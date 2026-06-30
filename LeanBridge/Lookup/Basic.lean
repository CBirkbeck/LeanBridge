import Mathlib

/-! # `lookup` vocabulary

The table-agnostic building blocks shared by the rest of the tactic: the value types
(`Column`, `Cond`, `Cmp`), low-level `Expr` matchers, the recogniser combinators used to
describe a table's columns/properties, small result-row utilities, and the `TableInfo` record.

The concrete tables live in `LeanBridge.Lookup.Tables`; the tactic itself in
`LeanBridge.Lookup.Lookup`. -/

open Lean Meta

namespace Lookup

/-! ## Literals -/

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

/-! ## Comparison operators -/

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

/-! ## Columns and conditions -/

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

/-! ## Low-level `Expr` matchers -/

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

/-- Read a product of cyclic groups `ZMod n₁ × ⋯ × ZMod n_k` (with any `Multiplicative` or
`Additive` wrappers stripped) as its list of moduli, in the order written. -/
partial def cyclicFactors? (e : Expr) : Option (Array Nat) :=
  match_expr e with
  | ZMod n => (getNatLit? n).map (#[·])
  | Multiplicative a => cyclicFactors? a
  | Additive a => cyclicFactors? a
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

/-! ## Recogniser combinators

A column recogniser is a function `Expr → Option Column`; a property recogniser is
`Bool → Expr → Option Cond` (the `Bool` is the wanted polarity). A table lists these functions
directly; the helpers below build the common shapes, and anything unusual is just a lambda of
the same type. -/

/-- `headIs c "col" "name"`: matches any application of the constant `c` (e.g.
`NumberField.classNumber F`) to the column `col`, displayed as `name`. -/
def headIs (c : Name) (sql display : String) : Expr → Option Column :=
  fun e => if e.isAppOf c then some (col sql display) else none

/-- `finrankOver R "col" "name"`: matches `Module.finrank R _` (e.g. `R = ℚ` for a number
field's degree, `R = ℤ` for an elliptic curve's rank). -/
def finrankOver (R : Name) (sql display : String) : Expr → Option Column :=
  fun e => match_expr e with
    | Module.finrank r _ _ _ _ => if r.isConstOf R then some (col sql display) else none
    | _ => none

/-- `cardMentions c "col" "name"`: matches `Nat.card t` where the type `t` mentions `c`
(e.g. `Nat.card (AddCommGroup.torsion W.Point)`). -/
def cardMentions (c : Name) (sql display : String) : Expr → Option Column :=
  fun e => match_expr e with
    | Nat.card t => if containsConst t c then some (col sql display) else none
    | _ => none

/-- `absOf c "col" "name"`: matches `|x|` where `x` is an application of `c`
(e.g. `|NumberField.discr F|`). -/
def absOf (c : Name) (sql display : String) : Expr → Option Column :=
  fun e => match_expr e with
    | abs _ _ _ x => if x.isAppOf c then some (col sql display) else none
    | _ => none

/-- `signedValue c "signCol" "absCol" "name"`: matches an application of `c` whose value LMFDB
stores split as `signCol * absCol` (e.g. the signed discriminant). Recording the two columns
lets comparisons against a literal case-split on the sign and stay index-friendly. -/
def signedValue (c : Name) (signCol absCol display : String) : Expr → Option Column :=
  fun e => if e.isAppOf c then
    some (col s!"({signCol} * {absCol})" display (some (signCol, absCol))) else none

/-- `flagIs c "col"`: matches any application of `c` (e.g. `IsSimpleGroup G`) to the boolean
column `col` (`= 't'`, or `= 'f'` when negated). -/
def flagIs (c : Name) (column : String) : Bool → Expr → Option Cond :=
  fun pos e => if e.isAppOf c then some (boolCol pos column) else none

/-- `isAbelian "col"`: matches the commutativity statement `∀ a b, a * b = b * a` to the
boolean column `col`. -/
def isAbelian (column : String) : Bool → Expr → Option Cond :=
  fun pos e => if isAbelianPattern e then some (boolCol pos column) else none

/-- `isoStructure equiv c "col" "name" bracketed`: matches an isomorphism `lhs ≃ (∏ ZMod nᵢ)`
written with `equiv` (``AddEquiv`` or ``MulEquiv``) and `lhs` mentioning `c`, comparing the
invariant factors against `col`. `bracketed` selects the JSON `[…]` encoding (ideal class
group) over the array `{…}` encoding (torsion structure). -/
def isoStructure (equiv c : Name) (column display : String) (bracketed : Bool) :
    Bool → Expr → Option Cond :=
  fun pos e => do
    let (h, a, b) ← matchEquiv e
    guard (h == equiv)
    structCond pos a b c column display (if bracketed then fmtBrackets else fmtBraces)

/-! ## Result rows -/

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

/-! ## LMFDB tables -/

/-- Everything needed to query one LMFDB table and recognise the Lean expressions that map into
its columns. The concrete instances live in `LeanBridge.Lookup.Tables`. -/
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
  /-- Recognisers for scalar quantities of this object (used inside comparisons). Each is an
  `Expr → Option Column`; build them with `headIs`/`finrankOver`/… or write a lambda. -/
  scalars : Array (Expr → Option Column) := #[]
  /-- Recognisers for boolean/structure properties (the `Bool` is the wanted polarity). -/
  props : Array (Bool → Expr → Option Cond) := #[]

end Lookup
