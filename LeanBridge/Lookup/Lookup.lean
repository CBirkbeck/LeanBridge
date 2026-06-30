import Mathlib
import ProofWidgets.Component.HtmlDisplay

/-! # The `lookup` tactic

`lookup` reads the local hypotheses and the goal, translates them into a SQL query against
LMFDB that searches for a *counterexample* (a database object satisfying all the hypotheses but
**violating** the goal), and reports it if one is found. It never closes the goal: a hit shows
the statement is false, and a miss is only evidence (the database is not exhaustive).

To support a new object family, add a `TableInfo` to `tables`. To teach an existing family a
new column or property, add a recogniser to that table's `scalars`/`props`. -/

open Lean Elab Tactic Meta

namespace Lookup

initialize registerTraceClass `lookup

/-! #### Querying LMFDB -/

/-- Build the request body for an LMFDB `/sql` call. -/
def sqlRequestBody (sql : String) (limit : Nat := 1000) : Json :=
  .mkObj [("sql", toJson sql), ("limit", toJson limit)]

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

/-! #### Literals -/

/-- Extract a natural-number literal from `e`, handling `@OfNat.ofNat _ n _`. -/
def getNatLit? (e : Expr) : Option Nat :=
  match_expr e with
  | OfNat.ofNat _ n _ => n.rawNatLit?
  | _ => e.rawNatLit?

/-- Extract an integer literal, handling a leading negation `@Neg.neg _ _ n`. -/
def getIntLit? (e : Expr) : Option Int :=
  match_expr e with
  | Neg.neg _ _ a => (getNatLit? a).map fun n => -(n : Int)
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

/-! #### Translating Lean expressions to SQL

A `Column` is a quantity of an object (an SQL column expression plus a display name); a `Cond`
is a translated SQL boolean condition. The recognisers that map Lean expressions to columns
and conditions live *with each table* in the registry below, so adding a column or property to
a table is a local, one-line change. The generic plumbing here is table-agnostic. -/

/-- A scalar quantity of an object: an SQL column expression and a human-readable name. A
quantity stored split as `sign * |·|` records those two columns in `signed?`, so comparisons
against a literal can be made index-friendly. -/
structure Column where
  sql : String
  display : String
  signed? : Option (String × String) := none

/-- A translated SQL condition: the boolean SQL, the columns it references (as
`(displayName, selectExpr)` pairs, for reporting), and the LMFDB table it forces. -/
structure Cond where
  sql : String
  refs : Array (String × String) := #[]
  table : Option String := none

/-- Build a `Column`. -/
def col (sql display : String) (signed? : Option (String × String) := none) : Column :=
  { sql, display, signed? }

/-- A boolean-flag condition `column = 't'` (or `column = 'f'` when negated). -/
def boolCol (positive : Bool) (column : String) : Cond :=
  { sql := s!"{column} = {if positive then "'t'" else "'f'"}", refs := #[(column, column)] }

/-- Match a comparison `Prop`, returning the operator and the two operands. -/
def matchCmp (e : Expr) : Option (Cmp × Expr × Expr) :=
  match_expr e with
  | Eq _ a b => some (.eq, a, b)
  | Ne _ a b => some (.ne, a, b)
  | LE.le _ _ a b => some (.le, a, b)
  | LT.lt _ _ a b => some (.lt, a, b)
  | GE.ge _ _ a b => some (.ge, a, b)
  | GT.gt _ _ a b => some (.gt, a, b)
  | _ => none

/-- Whether `e` mentions the constant `n` anywhere. -/
def containsConst (e : Expr) (n : Name) : Bool := (e.find? (·.isConstOf n)).isSome

/-- Read a product of cyclic groups `ZMod n₁ × ⋯ × ZMod n_k` (with any `Multiplicative`
wrappers stripped) as its list of moduli, in the order written. -/
partial def cyclicFactors? (e : Expr) : Option (Array Nat) :=
  match_expr e with
  | ZMod n => (getNatLit? n).map (#[·])
  | Multiplicative a => cyclicFactors? a
  | Prod a b => do return (← cyclicFactors? a) ++ (← cyclicFactors? b)
  | _ => none

/-- LMFDB encodes the torsion structure as a brace array `{2,4}` and the ideal class group as
a JSON bracket array `[2, 2]`. -/
def fmtBraces (f : Array Nat) : String := "{" ++ ",".intercalate (f.toList.map toString) ++ "}"
def fmtBrackets (f : Array Nat) : String := "[" ++ ", ".intercalate (f.toList.map toString) ++ "]"

/-- The de Bruijn index of a bound variable, if `e` is one. -/
def bvarIdx? : Expr → Option Nat
  | .bvar n => some n
  | _ => none

/-- Recognise the commutativity predicate `∀ a b, a * b = b * a` ("the group is abelian"),
allowing the two multiplications to have swapped operands. -/
def isAbelianPattern (e : Expr) : Bool :=
  match e with
  | .forallE _ _ (.forallE _ _ body _) _ =>
    match_expr body with
    | Eq _ lhs rhs =>
      match_expr lhs with
      | HMul.hMul _ _ _ _ l1 l2 =>
        match_expr rhs with
        | HMul.hMul _ _ _ _ r1 r2 =>
          (bvarIdx? l1 == bvarIdx? r2) && (bvarIdx? l2 == bvarIdx? r1) &&
            (bvarIdx? l1).isSome && (bvarIdx? l1 != bvarIdx? l2)
        | _ => false
      | _ => false
    | _ => false
  | _ => false

/-- Translate an abelian-group-structure claim `lhs ≃ rhs` (with `rhs` a product of cyclics)
into an invariant-factor column comparison; `positive := false` negates it (`<>`). -/
def structCond (positive : Bool) (lhs rhs : Expr) (lhsConst : Name)
    (column display : String) (fmt : Array Nat → String) : Option Cond := do
  guard (containsConst lhs lhsConst)
  let factors ← cyclicFactors? rhs
  return { sql := s!"{column} {if positive then "=" else "<>"} '{fmt factors}'",
           refs := #[(display, column.replace "::text" "")] }

/-- Recognise an isomorphism `A ≃+ B` or `A ≃* B`, returning the equiv's head constant and the
two sides. -/
def matchEquiv (e : Expr) : Option (Name × Expr × Expr) :=
  match_expr e with
  | AddEquiv a b _ _ => some (``AddEquiv, a, b)
  | MulEquiv a b _ _ => some (``MulEquiv, a, b)
  | _ => none

/-! #### Declarative recognisers

Each table's columns and properties are described by *data* — `ScalarRule`/`PropRule` values.
All the `Expr`-matching metacode lives in the `match?` interpreters here, so teaching a table a
new column or property means adding a data constructor to its list (below), not writing a
matcher. -/

/-- How to recognise a scalar quantity of an object in a Lean expression. -/
inductive ScalarRule where
  /-- Head constant `c` applied to anything ↦ column `sql` (shown as `display`). -/
  | const (c : Name) (sql display : String)
  /-- `Module.finrank` over base ring `ring` ↦ column (e.g. `ℚ` for degree, `ℤ` for rank). -/
  | finrank (ring : Name) (sql display : String)
  /-- `Nat.card` of a type mentioning `inner` ↦ column (e.g. `AddCommGroup.torsion`). -/
  | cardOf (inner : Name) (sql display : String)
  /-- `|c …|` (absolute value of a `c`-headed term) ↦ column. -/
  | absOf (c : Name) (sql display : String)
  /-- Bare `c …` ↦ a signed quantity stored split as `signCol * absCol`. -/
  | signed (c : Name) (signCol absCol display : String)

/-- Interpret a `ScalarRule` as a recogniser `Expr → Option Column`. -/
def ScalarRule.match? : ScalarRule → Expr → Option Column
  | .const c sql display, e => if e.isAppOf c then some (col sql display) else none
  | .finrank ring sql display, e =>
      match_expr e with
      | Module.finrank r _ _ _ _ => if r.isConstOf ring then some (col sql display) else none
      | _ => none
  | .cardOf inner sql display, e =>
      match_expr e with
      | Nat.card g => if containsConst g inner then some (col sql display) else none
      | _ => none
  | .absOf c sql display, e =>
      match_expr e with
      | abs _ _ _ x => if x.isAppOf c then some (col sql display) else none
      | _ => none
  | .signed c signCol absCol display, e =>
      if e.isAppOf c then some (col s!"({signCol} * {absCol})" display (some (signCol, absCol)))
      else none

/-- How to recognise a boolean/structure property of an object. -/
inductive PropRule where
  /-- Head constant `c` ↦ boolean column `column` (`= 't'`, or `= 'f'` when negated). -/
  | flag (c : Name) (column : String)
  /-- The commutativity pattern `∀ a b, a * b = b * a` ↦ boolean column. -/
  | abelian (column : String)
  /-- An isomorphism `lhs ≃ (∏ ZMod nᵢ)` via `equiv` (``AddEquiv``/``MulEquiv``), with `lhs`
  mentioning `lhsConst`, compared against the invariant-factor `column`. `bracketed` chooses
  the JSON `[…]` encoding (ideal class group) over the array `{…}` encoding (torsion). -/
  | iso (equiv lhsConst : Name) (column display : String) (bracketed : Bool)

/-- Interpret a `PropRule` as a recogniser at a given polarity. -/
def PropRule.match? : PropRule → Bool → Expr → Option Cond
  | .flag c column, pos, e => if e.isAppOf c then some (boolCol pos column) else none
  | .abelian column, pos, e => if isAbelianPattern e then some (boolCol pos column) else none
  | .iso equiv lhsConst column display bracketed, pos, e => do
      let (h, a, b) ← matchEquiv e
      guard (h == equiv)
      structCond pos a b lhsConst column display (if bracketed then fmtBrackets else fmtBraces)

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
descriptive data, render that data, build a link to the LMFDB page, and recognise the Lean
expressions that map into its columns. -/

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
  /-- SQL `ORDER BY` clause picking the "smallest"/simplest counterexample. -/
  orderBy : String
  /-- Recognisers for scalar quantities of this object (used inside comparisons). To teach
  `lookup` a new column, add a `ScalarRule` here. -/
  scalars : Array ScalarRule := #[]
  /-- Recognisers for boolean/structure properties of this object at a given polarity. -/
  props : Array PropRule := #[]

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
  orderBy := "disc_abs"
  scalars := #[
    .const ``NumberField.classNumber "class_number" "class number",
    .finrank ``Rat "degree" "degree",
    -- `|discr F|` is `disc_abs`; the bare signed discriminant is split as `disc_sign·disc_abs`.
    .absOf ``NumberField.discr "disc_abs" "|discriminant|",
    .signed ``NumberField.discr "disc_sign" "disc_abs" "discriminant"]
  -- ideal class group structure: `ClassGroup (𝓞 F) ≃* Multiplicative (∏ ZMod nᵢ)`.
  props := #[.iso ``MulEquiv ``ClassGroup "class_group::text" "class group" true]

/-- Elliptic curves over `ℚ`. -/
def ecCurvedata : TableInfo where
  table := "ec_curvedata"
  labelCol := "lmfdb_label"
  descSelects := #["ainvs::text AS ainvs"]
  describe row := s!"elliptic curve {rowStr row "label"} with a-invariants {rowStr row "ainvs"}"
  url := ecUrl
  orderBy := "conductor"
  scalars := #[
    .finrank ``Int "rank" "rank",
    .cardOf ``AddCommGroup.torsion "torsion" "torsion"]
  -- torsion subgroup structure: `AddCommGroup.torsion W.Point ≃+ (∏ ZMod nᵢ)`.
  props := #[.iso ``AddEquiv ``AddCommGroup.torsion "torsion_structure" "torsion structure" false]

/-- Finite groups. -/
def gpsGroups : TableInfo where
  table := "gps_groups"
  labelCol := "label"
  descSelects := #["tex_name::text AS tex_name"]
  describe row := s!"group {rowStr row "label"} ({rowStr row "tex_name"})"
  url label := s!"https://www.lmfdb.org/Groups/Abstract/{label}"
  -- `order` is a SQL reserved word, so it must be quoted.
  orderBy := "\"order\""
  props := #[.flag ``IsSimpleGroup "simple", .abelian "abelian"]

/-- All supported object families. To support a new one, add its `TableInfo` here. -/
def tables : Array TableInfo := #[nfFields, ecCurvedata, gpsGroups]

/-- The table configuration for a table name. -/
def tableInfo? (name : String) : Option TableInfo := tables.find? (·.table == name)

/-! #### Dispatch: translating a `Prop` to a SQL condition -/

/-- Find the scalar column an expression denotes (trying every table's recognisers), together
with the table it belongs to. -/
def findScalar (e : Expr) : Option (Column × String) :=
  tables.findSome? fun t => (t.scalars.findSome? (·.match? e)).map (·, t.table)

/-- A column compared against an integer literal. A "signed" column stored as `sign * |·|` is
case-split on the sign, so the comparison hits the indexed absolute-value column rather than
the non-indexable product. -/
def colVsLit (c : Column) (table : String) (cmp : Cmp) (k : Int) : Cond :=
  match c.signed? with
  | some (signCol, absCol) =>
      { sql := s!"(({signCol} = 1 AND {absCol} {cmp.toSql} {k}) OR \
                  ({signCol} = -1 AND {absCol} {cmp.reverse.toSql} {-k}))",
        refs := #[(c.display, c.sql)], table := some table }
  | none =>
      { sql := s!"{c.sql} {cmp.toSql} {k}", refs := #[(c.display, c.sql)], table := some table }

/-- Translate a comparison `cmp a b` (column vs literal, or column vs column) into a `Cond`. -/
def toSqlCondCmp (cmp : Cmp) (a b : Expr) : Option Cond :=
  match findScalar a, findScalar b with
  | some (ca, ta), some (cb, _) =>
      some { sql := s!"{ca.sql} {cmp.toSql} {cb.sql}",
             refs := #[(ca.display, ca.sql), (cb.display, cb.sql)], table := some ta }
  | some (ca, ta), none => (getIntLit? b).map (colVsLit ca ta cmp)
  | none, some (cb, tb) => (getIntLit? a).map (colVsLit cb tb cmp.reverse)
  | none, none => none

/-- Translate a `Prop` into a SQL condition. `positive := false` translates its negation;
pushing the negation down to the operator / boolean value (rather than wrapping in SQL
`NOT (...)`) keeps the query index-friendly. `Not` flips the polarity; `Nonempty` is
transparent (an isomorphism *exists* iff the structures match). -/
partial def toCond (positive : Bool) (e : Expr) : Option Cond :=
  match_expr e with
  | Not p => toCond (!positive) p
  | Nonempty p => toCond positive p
  | _ =>
    match matchCmp e with
    | some (cmp, a, b) => toSqlCondCmp (if positive then cmp else cmp.negate) a b
    | none => tables.findSome? fun t =>
        (t.props.findSome? (·.match? positive e)).map fun c => { c with table := some t.table }

/-- Translate a `Prop` into a SQL condition. -/
def toSqlCond (e : Expr) : Option Cond := toCond true e

/-- Translate the *negation* of a `Prop` into a SQL condition (used for the goal). -/
def toSqlCondNeg (e : Expr) : Option Cond := toCond false e

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
    WHERE {whereClause} ORDER BY {info.orderBy} LIMIT 1"

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

/-- Translate the hypotheses in context into SQL conditions. A hypothesis that *is* a
comparison but that we cannot translate is reported as a warning (and dropped), since silently
ignoring it would weaken any "no counterexample" conclusion. -/
def collectHypotheses : TacticM (Array Cond) := do
  let mut out : Array Cond := #[]
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
