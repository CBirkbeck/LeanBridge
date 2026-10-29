import LeanBridge.ForMathlib.NumberTheory.Hypergeometric.CuspIndex
import Mathlib.Data.Rat.Defs

/-!
# The labels of hypergeometric families and motives

The LMFDB labels the hypergeometric family `H(A, B)` and the hypergeometric motive `H(A, B, t)`
following the pattern of `H([3, 3], [2, 2, 4], -1/3)`, whose label is `A3.3_B2.2.4_t-1.3` and that
of whose family is `A3.3_B2.2.4`: the entries of `A` and of `B` in decimal, separated by dots, and
`t = a / b` in lowest terms with `b > 0`, written `a.b`. The entries are written in the order of the
cusp-indices, which are weakly increasing lists, as in the example. The labels are canonical: they
are functions of the defining parameters, with no database numbering.

## Main definitions

* `Hypergeometric.Parameters.label` (LMFDB `hgm.field.label`): the label of a family `H(A, B)`.
* `Hypergeometric.Parameters.motiveLabel` (LMFDB `hgm.field.label`): the label of a motive
  `H(A, B, t)`.
-/

namespace Hypergeometric

variable {d : ℕ} (c : CuspIndex d) (P : Parameters d) (t : ℚ)

/-- The entries of a cusp-index in decimal, in weakly increasing order and separated by dots, as in
`3.3` for `[3, 3]` and `2.2.4` for `[2, 2, 4]`. -/
def CuspIndex.labelEntries : String :=
  ".".intercalate (c.toList.map toString)

/-- The **label** (LMFDB `hgm.field.label`) of the hypergeometric family `H(A, B)` with defining
parameters `(A, B)`: `A` followed by the entries of `A`, then `_B` followed by the entries of `B`,
the entries in decimal, in weakly increasing order and separated by dots, as in `A3.3_B2.2.4` for
`H([3, 3], [2, 2, 4])`. -/
def Parameters.label : String :=
  "A" ++ P.A.labelEntries ++ "_B" ++ P.B.labelEntries

/-- The **label** (LMFDB `hgm.field.label`) of the hypergeometric motive `H(A, B, t)`: the label of
its family `H(A, B)`, then `_t` followed by `t = a / b` in lowest terms with `b > 0`, written `a.b`
in decimal, as in `A3.3_B2.2.4_t-1.3` for `H([3, 3], [2, 2, 4], -1/3)`. -/
def Parameters.motiveLabel : String :=
  P.label ++ "_t" ++ toString t.num ++ "." ++ toString t.den

end Hypergeometric
