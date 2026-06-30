import LeanBridge.Lookup.Tables
import ProofWidgets.Component.HtmlDisplay

/-! # The `lookup` tactic

`lookup` reads the local hypotheses and the goal, translates them into a SQL query against
LMFDB that searches for a *counterexample* (a database object satisfying all the hypotheses but
**violating** the goal), and reports it if one is found. It never closes the goal: a hit shows
the statement is false, and a miss is only evidence (the database is not exhaustive).

The vocabulary lives in `LeanBridge.Lookup.Basic` and the table registry in
`LeanBridge.Lookup.Tables`; this file wires them into the query, the report, and the tactic. -/

open Lean Elab Tactic Meta

namespace Lookup

initialize registerTraceClass `lookup

/-! ## Querying LMFDB -/

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

/-! ## Dispatch: translating a `Prop` to a SQL condition -/

/-- Find the scalar column an expression denotes (trying every table's recognisers), together
with the table it belongs to. -/
def findScalar (e : Expr) : Option (Column × String) :=
  tables.findSome? fun t => (t.scalars.findSome? (· e)).map (·, t.table)

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
  | False => some { sql := if positive then "FALSE" else "TRUE" }
  | True => some { sql := if positive then "TRUE" else "FALSE" }
  | Not p => toCond (!positive) p
  | Nonempty p => toCond positive p
  | _ =>
    match matchCmp e with
    | some (cmp, a, b) => toSqlCondCmp (if positive then cmp else cmp.negate) a b
    | none => tables.findSome? fun t =>
        (t.props.findSome? (· positive e)).map fun c => { c with table := some t.table }

/-- Translate a `Prop` into a SQL condition. -/
def toSqlCond (e : Expr) : Option Cond := toCond true e

/-- Translate the *negation* of a `Prop` into a SQL condition (used for the goal). -/
def toSqlCondNeg (e : Expr) : Option Cond := toCond false e

/-! ## Assembling the query and report -/

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

/-! ## The tactic -/

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
