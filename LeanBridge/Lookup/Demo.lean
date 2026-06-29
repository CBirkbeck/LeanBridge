import Mathlib

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

/-- A scalar translated to SQL: its text plus the quantities it references, recorded as
`(displayName, sqlExpr)` pairs so a counterexample's actual values can be reported. -/
structure Scalar where
  sql : String
  refs : Array (String × String) := #[]

/-- Translate a scalar Lean expression (applied to the number field) into a SQL scalar over
`nf_fields`: a column expression or a numeric literal. -/
def toSqlScalar (e : Expr) : Option Scalar :=
  match e.getAppFnArgs with
  | (``NumberField.classNumber, _) =>
      some { sql := "class_number", refs := #[("class number", "class_number")] }
  | (``Module.finrank, args) =>
      -- `Module.finrank ℚ F` is the degree of the number field `F` over `ℚ`.
      if h : 0 < args.size then
        if args[0].isConstOf ``Rat then some { sql := "degree", refs := #[("degree", "degree")] }
        else none
      else none
  | (``abs, args) => args.back?.bind fun x =>
      -- `|NumberField.discr F|` is the absolute discriminant `disc_abs`.
      match x.getAppFnArgs with
      | (``NumberField.discr, _) => some { sql := "disc_abs", refs := #[("|discriminant|", "disc_abs")] }
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
    refs := #[("discriminant", "(disc_sign * disc_abs)")] }

/-- Translate a comparison `cmp a b` into a SQL condition. -/
def toSqlCondCmp (cmp : Cmp) (a b : Expr) : Option Scalar :=
  -- Signed-discriminant comparisons against a literal get the index-friendly treatment.
  if isDiscr a then (getIntLit? b).map (discrCond cmp ·)
  else if isDiscr b then (getIntLit? a).map (discrCond cmp.reverse ·)
  else do
    let sa ← toSqlScalar a
    let sb ← toSqlScalar b
    return { sql := s!"{sa.sql} {cmp.toSql} {sb.sql}", refs := sa.refs ++ sb.refs }

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

/-- Translate a `Prop` into a SQL condition. -/
def toSqlCond (e : Expr) : Option Scalar := do
  let (cmp, a, b) ← matchCmp e
  toSqlCondCmp cmp a b

/-- Translate the *negation* of a `Prop` into a SQL condition. Negating at the operator level
(rather than wrapping the whole thing in `NOT (...)`) keeps the query index-friendly. -/
def toSqlCondNeg (e : Expr) : Option Scalar := do
  let (cmp, a, b) ← matchCmp e
  toSqlCondCmp cmp.negate a b

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

/-- Build the counterexample query: `label`, the defining polynomial, and the actual values
of every referenced quantity (cast to text, since the endpoint cannot serialise bignum
columns directly). -/
def buildQuery (conds : Array String) (items : Array (String × String)) : String := Id.run do
  let mut selects : Array String := #["label", "coeffs::text AS coeffs"]
  for i in [0:items.size] do
    selects := selects.push s!"({items[i]!.2})::text AS c{i}"
  let whereClause := String.intercalate " AND " conds.toList
  return s!"SELECT {String.intercalate ", " selects.toList} FROM nf_fields WHERE {whereClause} LIMIT 1"

/-- Render a counterexample row as a message. -/
def reportRow (row : Json) (items : Array (String × String)) : MessageData := Id.run do
  let label := rowStr row "label"
  let mut vals : Array MessageData := #[]
  for i in [0:items.size] do
    vals := vals.push m!"{items[i]!.1} = {rowStr row s!"c{i}"}"
  return m!"lookup: the statement is FALSE — LMFDB has a counterexample.\n\
    number field {label}, with minimal polynomial {formatPoly (rowStr row "coeffs")}\n\
    {MessageData.joinSep vals.toList ", "}\n\
    https://www.lmfdb.org/NumberField/{label}"

/-- Translate the hypotheses in context into SQL conditions, collecting referenced
quantities. -/
def collectHypotheses : TacticM (Array String × Array (String × String)) := do
  let mut conds : Array String := #[]
  let mut refs : Array (String × String) := #[]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    if let some s := toSqlCond (← instantiateMVars ldecl.type) then
      conds := conds.push s.sql
      refs := refs ++ s.refs
  return (conds, refs)

elab "lookup" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let (hypConds, hypRefs) ← collectHypotheses
    -- The negated goal is the final condition: we hunt for a row that breaks the goal.
    let some goalCond := toSqlCondNeg (← instantiateMVars (← goal.getType))
      | throwError "lookup: don't know how to translate the goal into a SQL query"
    let conds := hypConds.push goalCond.sql
    let items := dedupRefs (hypRefs ++ goalCond.refs)
    let query := buildQuery conds items
    trace[lookup] "query:\n{query}"
    match firstRow? (← runSql query) with
    | none =>
      -- No counterexample in the database: report, but do *not* close the goal.
      logInfo m!"lookup: no counterexample found in LMFDB \
        (the statement is consistent with the database, but this is not a proof)."
    | some row => throwError reportRow row items

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

-- TEMP signed-discriminant test (FALSE: the disc = -163 field is a counterexample)
example {F : Type*} [Field F] [NumberField F]
    (h1 : NumberField.classNumber F = 1) (h2 : Module.finrank ℚ F = 2) :
    NumberField.discr F ≥ -100 := by
  lookup

-- TEMP signed-discriminant test (TRUE: -163 is the most negative, so no counterexample)
example {F : Type*} [Field F] [NumberField F]
    (h1 : NumberField.classNumber F = 1) (h2 : Module.finrank ℚ F = 2) :
    NumberField.discr F ≥ -163 := by
  lookup

-- example {W : WeierstrassCurve.Affine ℚ}
--     (hW : 4 ≤ Nat.card (AddCommGroup.torsion W.Point)) :
--     Module.finrank ℤ W.Point ≤ 20 := by
--   sorry
