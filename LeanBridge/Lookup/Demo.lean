import Mathlib
import ProofWidgets.Component.HtmlDisplay

-- https://www.lmfdb.org/api/nf_fields/?_format=json&_offset=0

open Lean Elab Tactic Meta



/-- Build the request body for an LMFDB `/sql` call. -/
def sqlRequestBody (sql : String) (limit : Nat := 1000) : Json :=
  .mkObj [
    ("sql", toJson sql),
    ("limit", toJson limit)
  ]

/-- Run a SQL query against the LMFDB `/sql` endpoint and return the decoded result. -/
def runSql (sql : String) : MetaM Json := do
  let sqlUrl := "https://mcp.lmfdb.org/sql"
  let curlArgs := #[
    "-sS",
    "-X", "POST", sqlUrl,
    "-H", "Content-Type: application/json",
    "-d", (sqlRequestBody sql).compress
  ]
  let out ← IO.Process.output { cmd := "curl", args := curlArgs }
  if out.exitCode != 0 then
    throwError s!"curl failed (exit {out.exitCode}): {out.stderr}"
  let .ok result := Json.parse out.stdout
    | throwError s!"failed to parse response:\n{out.stdout}"
  return result

-- #eval runSql "SELECT lmfdb_label, conductor, rank FROM ec_curvedata WHERE rank >= 4 AND conductor <= 1000 LIMIT 1"
-- #eval runSql "SELECT label, coeffs, degree FROM nf_fields WHERE degree = 2 LIMIT 1"

/-! ### The `lookup` tactic

`lookup` reads the local hypotheses and the goal, translates them into a SQL query
against LMFDB that searches for a *counterexample* (a database object satisfying all the
hypotheses but **violating** the goal), and reports it if one is found. -/

namespace Lookup

initialize registerTraceClass `lookup

/-! #### Literals -/

/-- Extract a natural-number literal from `e`, handling `@OfNat.ofNat _ n _`. -/
def getNatLit? (e : Expr) : Option Nat :=
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => n.rawNatLit?
  | _ => e.rawNatLit?

/-- Extract an integer literal, handling a leading negation `@Neg.neg _ _ n`. -/
def getIntLit? (e : Expr) : Option Int :=
  match e.getAppFnArgs with
  | (``Neg.neg, #[_, _, a]) => (getNatLit? a).map fun n => -(n : Int)
  | _ => (getNatLit? e).map Int.ofNat

/-! #### Comparison operators -/

/-- A comparison operator we know how to send to SQL. -/
inductive Cmp | eq | ne | le | lt | ge | gt
  deriving Inhabited, BEq

namespace Cmp

/-- The SQL spelling of the operator. -/
def toSql : Cmp → String
  | eq => "=" | ne => "<>" | le => "<=" | lt => "<" | ge => ">=" | gt => ">"

/-- The operator whose truth value is the logical negation of this one. -/
def negate : Cmp → Cmp
  | eq => ne | ne => eq | le => gt | lt => ge | ge => lt | gt => le

/-- The operator that holds after swapping the operands (equivalently, after negating both
sides of an order comparison). -/
def reverse : Cmp → Cmp
  | eq => eq | ne => ne | le => ge | lt => gt | ge => le | gt => lt

end Cmp

/-! #### Translating Lean expressions to SQL -/

/-- A scalar translated to SQL: its text, the quantities it references (recorded as
`(displayName, sqlExpr)` pairs so a counterexample's actual values can be reported), and the
LMFDB table it forces (a literal forces none). -/
structure Scalar where
  sql : String
  refs : Array (String × String) := #[]
  table : Option String := none

/-- Translate a scalar Lean expression (applied to the LMFDB object) into a SQL scalar: a
column expression tagged with its table, or a numeric literal. -/
def toSqlScalar (e : Expr) : Option Scalar :=
  match e.getAppFnArgs with
  | (``NumberField.classNumber, _) =>
      some { sql := "class_number", refs := #[("class number", "class_number")], table := "nf_fields" }
  | (``Module.finrank, args) =>
      -- `Module.finrank ℚ F` is the degree of a number field; `Module.finrank ℤ W.Point` is
      -- the rank of an elliptic curve's Mordell–Weil group.
      if h : 0 < args.size then
        if args[0].isConstOf ``Rat then
          some { sql := "degree", refs := #[("degree", "degree")], table := "nf_fields" }
        else if args[0].isConstOf ``Int then
          some { sql := "rank", refs := #[("rank", "rank")], table := "ec_curvedata" }
        else none
      else none
  | (``Nat.card, args) =>
      -- `Nat.card ↥(AddCommGroup.torsion W.Point)` is the size of the torsion subgroup.
      if args.any fun a => (a.find? (·.isConstOf ``AddCommGroup.torsion)).isSome then
        some { sql := "torsion", refs := #[("torsion", "torsion")], table := "ec_curvedata" }
      else none
  | (``abs, args) => args.back?.bind fun x =>
      -- `|NumberField.discr F|` is the absolute discriminant `disc_abs`.
      match x.getAppFnArgs with
      | (``NumberField.discr, _) =>
          some { sql := "disc_abs", refs := #[("|discriminant|", "disc_abs")], table := "nf_fields" }
      | _ => none
  | _ => (getIntLit? e).map fun n => { sql := toString n }

/-- Recognise the *signed* discriminant `NumberField.discr F`. -/
def isDiscr (e : Expr) : Bool :=
  match e.getAppFnArgs with
  | (``NumberField.discr, _) => true
  | _ => false

/-- LMFDB stores the signed discriminant split as `disc_sign * disc_abs`, so translating
`discr OP k` literally as `(disc_sign * disc_abs) OP k` cannot use the indices. Instead we
case-split on the sign into index-friendly comparisons on `disc_abs`:
`discr OP k  ⟺  (disc_sign = 1 ∧ disc_abs OP k) ∨ (disc_sign = -1 ∧ disc_abs revOP -k)`. -/
def discrCond (cmp : Cmp) (k : Int) : Scalar :=
  { sql := s!"((disc_sign = 1 AND disc_abs {cmp.toSql} {k}) OR \
              (disc_sign = -1 AND disc_abs {cmp.reverse.toSql} {-k}))",
    refs := #[("discriminant", "(disc_sign * disc_abs)")], table := "nf_fields" }

/-- Translate a comparison `cmp a b` into a SQL condition. -/
def toSqlCondCmp (cmp : Cmp) (a b : Expr) : Option Scalar :=
  -- Signed-discriminant comparisons against a literal get the index-friendly treatment.
  if isDiscr a then (getIntLit? b).map (discrCond cmp ·)
  else if isDiscr b then (getIntLit? a).map (discrCond cmp.reverse ·)
  else do
    let sa ← toSqlScalar a
    let sb ← toSqlScalar b
    return { sql := s!"{sa.sql} {cmp.toSql} {sb.sql}", refs := sa.refs ++ sb.refs,
             table := sa.table <|> sb.table }

/-- Match a comparison `Prop`, returning the operator and the two operands. -/
def matchCmp (e : Expr) : Option (Cmp × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Eq, #[_, a, b])       => some (.eq, a, b)
  | (``Ne, #[_, a, b])       => some (.ne, a, b)
  | (``LE.le, #[_, _, a, b]) => some (.le, a, b)
  | (``LT.lt, #[_, _, a, b]) => some (.lt, a, b)
  | (``GE.ge, #[_, _, a, b]) => some (.ge, a, b)
  | (``GT.gt, #[_, _, a, b]) => some (.gt, a, b)
  | _ => none

/-- The de Bruijn index of a bound variable, if `e` is one. -/
def bvarIdx? : Expr → Option Nat
  | .bvar n => some n
  | _ => none

/-- Recognise the commutativity predicate `∀ a b, a * b = b * a` (i.e. "the group is
abelian"), allowing for the two multiplications to have swapped operands. -/
def isAbelianPattern (e : Expr) : Bool := Id.run do
  let .forallE _ _ (.forallE _ _ body _) _ := e | return false
  let (``Eq, #[_, lhs, rhs]) := body.getAppFnArgs | return false
  let (``HMul.hMul, la) := lhs.getAppFnArgs | return false
  let (``HMul.hMul, ra) := rhs.getAppFnArgs | return false
  if la.size < 2 || ra.size < 2 then return false
  let some l1 := bvarIdx? la[la.size - 2]! | return false
  let some l2 := bvarIdx? la[la.size - 1]! | return false
  let some r1 := bvarIdx? ra[ra.size - 2]! | return false
  let some r2 := bvarIdx? ra[ra.size - 1]! | return false
  return l1 == r2 && l2 == r1 && l1 != l2

/-- Translate a boolean-valued property of the object into a SQL boolean-column comparison.
`positive := false` asks for the property to *fail* (`= 'f'`). -/
def toSqlPredicate (positive : Bool) (e : Expr) : Option Scalar :=
  let tf := if positive then "'t'" else "'f'"
  match e.getAppFnArgs with
  | (``IsSimpleGroup, _) =>
      some { sql := s!"simple = {tf}", refs := #[("simple", "simple")], table := "gps_groups" }
  | _ =>
      if isAbelianPattern e then
        some { sql := s!"abelian = {tf}", refs := #[("abelian", "abelian")], table := "gps_groups" }
      else none

/-- Translate a `Prop` into a SQL condition. `positive := false` translates its negation
instead; pushing the negation down to the operator / boolean value (rather than wrapping the
whole condition in SQL `NOT (...)`) keeps the query index-friendly. -/
partial def toCond (positive : Bool) (e : Expr) : Option Scalar :=
  match e.getAppFnArgs with
  | (``Not, #[p]) => toCond (!positive) p
  | _ =>
      match matchCmp e with
      | some (cmp, a, b) => toSqlCondCmp (if positive then cmp else cmp.negate) a b
      | none => toSqlPredicate positive e

/-- Translate a `Prop` into a SQL condition. -/
def toSqlCond (e : Expr) : Option Scalar := toCond true e

/-- Translate the *negation* of a `Prop` into a SQL condition (used for the goal). -/
def toSqlCondNeg (e : Expr) : Option Scalar := toCond false e

/-! #### Reading and rendering a result row -/

/-- The first returned row of an LMFDB `/sql` response, if any. -/
def firstRow? (j : Json) : Option Json :=
  match j.getObjVal? "rows" with
  | .ok (.arr rs) => rs[0]?
  | _ => none

/-- Read a (text-cast) field of a row as a string. -/
def rowStr (row : Json) (key : String) : String :=
  (row.getObjValAs? String key).toOption.getD "?"

/-- Pretty-print the integer monomial `c * x^e` (its sign is handled by the caller). -/
def monomial (c : Int) (e : Nat) : String :=
  if e == 0 then toString c.natAbs
  else
    let base := if e == 1 then "x" else s!"x^{e}"
    if c.natAbs == 1 then base else s!"{c.natAbs}*{base}"

/-- Format an LMFDB `coeffs` array (e.g. `{-1,-1,1}`, lowest degree first) as a polynomial
in `x`, highest degree first. -/
def formatPoly (coeffs : String) : String := Id.run do
  let stripped := (coeffs.replace "{" "").replace "}" ""
  let cs := (stripped.splitOn ",").filterMap String.toInt?
  let n := cs.length
  let mut out := ""
  for i in [0:n] do
    let e := n - 1 - i
    let c := cs[e]!
    if c == 0 then continue
    let term := monomial c e
    if out.isEmpty then
      out := if c < 0 then s!"-{term}" else term
    else
      out := out ++ (if c < 0 then s!" - {term}" else s!" + {term}")
  return if out.isEmpty then "0" else out

/-! #### LMFDB tables

Each supported object family corresponds to a table, knowing how to select its label and
descriptive data, render that data, and build a link to the LMFDB page. -/

/-- Per-table knowledge needed to query and report a counterexample. -/
structure TableInfo where
  /-- The SQL table name. -/
  table : String
  /-- The column holding the LMFDB label (selected `AS label`). -/
  labelCol : String
  /-- Extra SELECT fragments for the descriptive data (e.g. the defining polynomial). -/
  descSelects : Array String
  /-- Render the descriptive data of a result row as plain text. -/
  describe : Json → String
  /-- Build the LMFDB page URL from a label. -/
  url : String → String

/-- LMFDB elliptic-curve labels like `15.a2` live at `.../EllipticCurve/Q/15/a/2`. -/
def ecUrl (label : String) : String :=
  match label.splitOn "." with
  | [conductor, iso] =>
      let letters := iso.takeWhile Char.isAlpha
      let number := iso.dropWhile Char.isAlpha
      s!"https://www.lmfdb.org/EllipticCurve/Q/{conductor}/{letters}/{number}"
  | _ => s!"https://www.lmfdb.org/EllipticCurve/Q/{label}"

/-- Number fields. -/
def nfFields : TableInfo where
  table := "nf_fields"
  labelCol := "label"
  descSelects := #["coeffs::text AS coeffs"]
  describe row := s!"number field {rowStr row "label"}, with minimal polynomial \
    {formatPoly (rowStr row "coeffs")}"
  url label := s!"https://www.lmfdb.org/NumberField/{label}"

/-- Elliptic curves over `ℚ`. -/
def ecCurvedata : TableInfo where
  table := "ec_curvedata"
  labelCol := "lmfdb_label"
  descSelects := #["ainvs::text AS ainvs"]
  describe row := s!"elliptic curve {rowStr row "label"} with a-invariants {rowStr row "ainvs"}"
  url := ecUrl

/-- Finite groups. -/
def gpsGroups : TableInfo where
  table := "gps_groups"
  labelCol := "label"
  descSelects := #["tex_name::text AS tex_name"]
  describe row := s!"group {rowStr row "label"} ({rowStr row "tex_name"})"
  url label := s!"https://www.lmfdb.org/Groups/Abstract/{label}"

/-- The table configuration for a table name. -/
def tableInfo? : String → Option TableInfo
  | "nf_fields" => some nfFields
  | "ec_curvedata" => some ecCurvedata
  | "gps_groups" => some gpsGroups
  | _ => none

/-! #### Assembling the query and report -/

/-- Deduplicate referenced quantities by their SQL expression, preserving order. -/
def dedupRefs (refs : Array (String × String)) : Array (String × String) := Id.run do
  let mut seen : Array String := #[]
  let mut out : Array (String × String) := #[]
  for (name, expr) in refs do
    unless seen.contains expr do
      seen := seen.push expr
      out := out.push (name, expr)
  return out

/-- Build the counterexample query: the label, the descriptive data, and the actual values of
every referenced quantity (cast to text, since the endpoint cannot serialise bignum columns
directly). -/
def buildQuery (info : TableInfo) (conds : Array String) (items : Array (String × String)) :
    String := Id.run do
  let mut selects : Array String := #[s!"{info.labelCol} AS label"] ++ info.descSelects
  for i in [0:items.size] do
    selects := selects.push s!"({items[i]!.2})::text AS c{i}"
  let whereClause := String.intercalate " AND " conds.toList
  return s!"SELECT {String.intercalate ", " selects.toList} FROM {info.table} \
    WHERE {whereClause} LIMIT 1"

/-- The "name = value" strings for the referenced quantities of a result row. -/
def valueStrs (row : Json) (items : Array (String × String)) : Array String := Id.run do
  let mut out : Array String := #[]
  for i in [0:items.size] do
    out := out.push s!"{items[i]!.1} = {rowStr row s!"c{i}"}"
  return out

open ProofWidgets in
/-- Render a counterexample row as interactive HTML, including a clickable LMFDB link.
A bare or markdown URL in a `MessageData` is not linkified by the infoview, so we build an
actual `<a>` element and embed it via `MessageData.ofHtml`. -/
def reportHtml (info : TableInfo) (row : Json) (items : Array (String × String)) : Html :=
  let label := rowStr row "label"
  Html.element "div" #[] #[
    .text "lookup: the statement is FALSE — LMFDB has a counterexample.",
    .element "br" #[] #[],
    .text (info.describe row),
    .element "br" #[] #[],
    .text (", ".intercalate (valueStrs row items).toList),
    .element "br" #[] #[],
    .element "a" #[("href", toJson (info.url label))] #[.text s!"{label} on LMFDB"]
  ]

/-- A plain-text fallback for the counterexample, shown where HTML cannot render. -/
def reportAlt (info : TableInfo) (row : Json) (items : Array (String × String)) : String :=
  s!"lookup: the statement is FALSE — LMFDB has a counterexample.\n\
    {info.describe row}\n\
    {", ".intercalate (valueStrs row items).toList}\n\
    {info.url (rowStr row "label")}"

/-- Translate the hypotheses in context into SQL condition scalars. A hypothesis that *is* a
comparison but that we cannot translate is reported as a warning (and dropped), since silently
ignoring it would weaken any "no counterexample" conclusion. -/
def collectHypotheses : TacticM (Array Scalar) := do
  let mut out : Array Scalar := #[]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    match toSqlCond ty with
    | some s => out := out.push s
    | none =>
      if (matchCmp ty).isSome then
        logWarning m!"lookup: ignoring hypothesis `{ldecl.userName}` : {ty}\n\
          (couldn't translate it to a SQL condition, so the search ignores this constraint)."
  return out

elab "lookup" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    -- The negated goal is the final condition: we hunt for a row that breaks the goal.
    let some goalCond := toSqlCondNeg (← instantiateMVars (← goal.getType))
      | throwError "lookup: don't know how to translate the goal into a SQL query"
    let conditions := (← collectHypotheses).push goalCond
    -- Every condition must point at the same LMFDB table.
    let info ← match (conditions.filterMap (·.table)).toList.dedup with
      | [t] => match tableInfo? t with
        | some info => pure info
        | none => throwError "lookup: no table configuration for `{t}`"
      | [] => throwError "lookup: couldn't determine which LMFDB table the goal is about"
      | ts => throwError "lookup: the goal mixes multiple LMFDB object types {ts}"
    let conds := conditions.map (·.sql)
    let items := dedupRefs (conditions.foldl (fun acc s => acc ++ s.refs) #[])
    let query := buildQuery info conds items
    trace[lookup] "query:\n{query}"
    match firstRow? (← runSql query) with
    | none =>
      -- No counterexample in the database: report, but do *not* close the goal.
      logInfo m!"lookup: no counterexample found in LMFDB \
        (the statement is consistent with the database, but this is not a proof)."
    | some row =>
      throwError (← MessageData.ofHtml (reportHtml info row items) (reportAlt info row items))

end Lookup


/-
**Elliptic curves over Q:** `SELECT lmfdb_label, ainvs  FROM ec_curvedata WHERE...`
* [ec.torsion_subgroup](https://beta.lmfdb.org/knowledge/show/ec.torsion_subgroup) --  `torsion=4` or `torsion_structure='{2,2}'`
* [ec.discriminant](https://beta.lmfdb.org/knowledge/show/ec.discriminant) -- `absD=164025 AND signD=1`
* [ec.rank](https://beta.lmfdb.org/knowledge/show/ec.rank) / [ec.mordell_weil_group]([https://beta.lmfdb.org/knowledge/show/ec.mordell_weil_group) -- `rank=4`

**Dirichlet characters:** `SELECT label FROM char_dirichlet WHERE...`
* [character.dirichlet.primitive](https://beta.lmfdb.org/knowledge/show/character.dirichlet.primitive) -- `is_primitive='t'`
* [character.dirichlet.order](https://beta.lmfdb.org/knowledge/show/character.dirichlet.order) -- `order=4`
* [character.dirichlet.conductor](https://beta.lmfdb.org/knowledge/show/character.dirichlet.conductor) -- `conductor=4`

**Number fields:** `SELECT label, coeffs FROM nf_fields WHERE...`
* [nf.degree_mathlib_def](https://beta.lmfdb.org/knowledge/show/nf.degree_mathlib_def) -- `degree=6`
* [nf.ideal_class_group](https://beta.lmfdb.org/knowledge/show/nf.ideal_class_group) --  `class_group='{2,2}'`
* [nf.class_number](https://beta.lmfdb.org/knowledge/show/nf.class_number) -- `class_number=4`
* [nf.discriminant](https://beta.lmfdb.org/knowledge/show/nf.discriminant) -- `disc_abs=41 AND disc_sign=1`

*Example*: Every number field with class number 1 and degree 2 has absolute discriminant at most 163

**Groups:** `SELECT label, tex_name FROM gps_groups WHERE...`
* [group.simple](https://beta.lmfdb.org/knowledge/show/group.simple) -- `simple='t'`
* [group.abelian](https://beta.lmfdb.org/knowledge/show/group.abelian) -- `abelian='t'`

*Example*: Every simple group is nonabelian
-/

-- `ec_curvedata` = (W : WeierstrassCurve.Affine ℚ)
-- `torsion` = Nat.card (AddCommGroup.torsion W.Point)
-- `torsion_structure` ≈ AddCommGroup.torsion W.Point, but note that torsion_structure is the strucutre of the group as a product of cyclics
-- `rank` = Module.finrank ℤ W.Point

example {F : Type*} [Field F] [NumberField F]
    (hF : NumberField.classNumber F = 1) (hF : Module.finrank ℚ F = 2) :
    |NumberField.discr F| ≤ 163 := by
  lookup

-- Signed-discriminant queries are supported too (the DB stores `disc_sign * disc_abs`,
-- and `lookup` case-splits on the sign so the query stays index-friendly):
-- `NumberField.discr F ≥ -100` finds the counterexample `2.0.163.1` (discriminant -163),
-- while `NumberField.discr F ≥ -163` finds none.

-- A non-number-field example: `lookup` dispatches to the `ec_curvedata` table. This claim is
-- false — e.g. curve `117.a4` has a 4-torsion point yet positive rank — so `lookup` surfaces
-- it (with the curve's a-invariants and a link). The `≤ 20` version instead finds nothing.
example {W : WeierstrassCurve.Affine ℚ}
    (hW : 4 ≤ Nat.card (AddCommGroup.torsion W.Point)) :
    Module.finrank ℤ W.Point ≤ 0 := by
  lookup

-- A third object family: `lookup` dispatches boolean properties to `gps_groups`. "Every
-- simple group is nonabelian" is false — the cyclic groups of prime order are simple and
-- abelian — so `lookup` surfaces such a group.
example {G : Type*} [Group G] [IsSimpleGroup G] : ¬ ∀ a b : G, a * b = b * a := by
  lookup
