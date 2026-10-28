import LeanBridge.ForMathlib.GroupTheory.FiniteAbelian.AbelianInvariants
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The structure of the group of Dirichlet characters

The structure of the group of Dirichlet characters of modulus `q` is the list `[n₁, …, n_r]` of its
invariant factors: the unique list with `1 < n₁ ∣ n₂ ∣ ⋯ ∣ n_r` such that the group is isomorphic
to `C_{n₁} × ⋯ × C_{n_r}`, as computed by `AddCommGroup.smithAbelianInvariants`. It is the
structure of `(ℤ/qℤ)ˣ`, and its product is `φ(q)`.

## Main definitions

* `DirichletCharacter.groupStructure` (LMFDB `character.dirichlet.group.structure`): the structure
  of the group of Dirichlet characters of modulus `q`.

## Main results

* `DirichletCharacter.groupStructure_eq_iff`: the structure is the unique list `[n₁, …, n_r]` with
  `1 < n₁ ∣ n₂ ∣ ⋯ ∣ n_r` such that the group is isomorphic to `C_{n₁} × ⋯ × C_{n_r}`.
* `DirichletCharacter.groupStructure_eq`: it is the structure of `(ℤ/qℤ)ˣ`.
-/

namespace DirichletCharacter

variable (q : ℕ)

/-- The **structure** (LMFDB `character.dirichlet.group.structure`) of the group of Dirichlet
characters of modulus `q`: its invariant factors `[n₁, …, n_r]`, the unique list with
`1 < n₁ ∣ n₂ ∣ ⋯ ∣ n_r` such that the group is isomorphic to `C_{n₁} × ⋯ × C_{n_r}`
(`groupStructure_eq_iff`). It is also the structure of `(ℤ/qℤ)ˣ` (`groupStructure_eq`). The LMFDB
does not state `1 < n₁`, without which the list is not unique; for `q ≤ 2` the group is trivial
and the list is empty. -/
noncomputable def groupStructure : List ℕ :=
  AddCommGroup.smithAbelianInvariants <| Additive <| DirichletCharacter ℂ q

variable {q} in
/-- The structure of the group of Dirichlet characters of modulus `q` is the unique list
`[n₁, …, n_r]` with `1 < n₁ ∣ n₂ ∣ ⋯ ∣ n_r` such that the group is isomorphic to
`C_{n₁} × ⋯ × C_{n_r}`. -/
lemma groupStructure_eq_iff {L : List ℕ} : groupStructure q = L ↔ (∀ m ∈ L, 1 < m) ∧
    L.IsChain (· ∣ ·) ∧
      Nonempty (DirichletCharacter ℂ q ≃* Π i : Fin L.length, Multiplicative (ZMod L[i])) :=
  CommGroup.smithAbelianInvariants_additive_eq_iff

variable [NeZero q]

/-- The structure of the group of Dirichlet characters of modulus `q` is the structure of
`(ℤ/qℤ)ˣ`. -/
lemma groupStructure_eq :
    groupStructure q = AddCommGroup.smithAbelianInvariants (Additive (ZMod q)ˣ) :=
  AddCommGroup.smithAbelianInvariants_congr <| MulEquiv.toAdditive (mulEquiv_units ℂ q).some

lemma prod_groupStructure : (groupStructure q).prod = q.totient := by
  rw [groupStructure, AddCommGroup.prod_smithAbelianInvariants, Nat.card_congr Additive.toMul,
    card_eq_totient_of_hasEnoughRootsOfUnity]

end DirichletCharacter
