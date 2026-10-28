import LeanBridge.ForMathlib.NumberTheory.Hypergeometric.Weight
import Mathlib.Algebra.Group.Nat.Even

/-!
# The type of a hypergeometric family and its Hodge vector at `t = 1`

A hypergeometric family `H(A, B)` of weight `w` is of orthogonal type if `w` is even and of
symplectic type if `w` is odd. At the special point `t = 1` the motive `H(A, B, 1)` loses one
dimension in its middle Hodge numbers: the middle Hodge number `h^{w/2, w/2}` drops by `1` if `w`
is even, and both middle Hodge numbers drop by `1` if `w` is odd.

As in `Hypergeometric.Weight`, these are the LMFDB's combinatorial recipes from the defining
parameters: hypergeometric motives, their motivic Galois groups and the Hodge numbers of the
motives `H(A, B, t)` are not formalised.

## Main definitions

* `Hypergeometric.Parameters.IsOrthogonalType`, `Hypergeometric.Parameters.IsSymplecticType`
  (LMFDB `hgm.type`).
* `Hypergeometric.Parameters.hodgeVectorAtOne` (LMFDB `hgm.hodge_vector`, `mot.hodgevector`): the
  Hodge vector of `H(A, B, 1)`.

## Main results

* `Hypergeometric.Parameters.isSymplecticType_iff_not_isOrthogonalType`: every family is of
  exactly one of the two types.
* `Hypergeometric.Parameters.length_hodgeVectorAtOne`: the Hodge vector at `t = 1` has as many
  entries as that of the family.
-/

namespace Hypergeometric.Parameters

variable {d : ℕ} (P : Parameters d)

/-- A hypergeometric family `H(A, B)` is of **orthogonal type** (LMFDB `hgm.type`) if its weight
`w` is even; then the motivic Galois group of its motives lies in a conformal orthogonal group,
which is not formalised. -/
def IsOrthogonalType : Prop :=
  Even P.weight

/-- A hypergeometric family `H(A, B)` is of **symplectic type** (LMFDB `hgm.type`) if its weight
`w` is odd; then the motivic Galois group of its motives lies in a conformal symplectic group,
which is not formalised. -/
def IsSymplecticType : Prop :=
  Odd P.weight

/-- **Every hypergeometric family is of exactly one type**: symplectic exactly when not
orthogonal. -/
lemma isSymplecticType_iff_not_isOrthogonalType : P.IsSymplecticType ↔ ¬P.IsOrthogonalType :=
  Nat.not_even_iff_odd.symm

/-- The **Hodge vector** `(h^{0,w}, …, h^{w,0})` of the motive `H(A, B, 1)` at the special point
`t = 1` (LMFDB `hgm.hodge_vector`, `mot.hodgevector`), from the Hodge vector of the family: the
middle entry `h^{w/2, w/2}` (the entry of index `i` with `2i = w`) drops by `1` if the weight `w`
is even, and the two middle entries (the entries of index `i` with `2i + 1 = w` or `2i = w + 1`)
drop by `1` if `w` is odd. For `t ≠ 0, 1` the motive `H(A, B, t)` has the Hodge vector of the
family, `Hypergeometric.Parameters.hodgeVector`. That the middle entries are positive, so that the
degree drops by `1` or `2`, is not proved here. -/
def hodgeVectorAtOne : List ℕ :=
  P.hodgeVector.mapIdx fun i h ↦
    if 2 * i = P.weight ∨ 2 * i + 1 = P.weight ∨ 2 * i = P.weight + 1 then h - 1 else h

/-- **The Hodge vector at `t = 1` has as many entries as that of the family.** -/
lemma length_hodgeVectorAtOne : P.hodgeVectorAtOne.length = P.hodgeVector.length :=
  List.length_mapIdx

end Hypergeometric.Parameters
