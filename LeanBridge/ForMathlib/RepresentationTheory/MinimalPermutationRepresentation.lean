import LeanBridge.ForMathlib.RepresentationTheory.PermutationContainer
import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Basic

/-!
# The smallest permutation representation containing a character

The LMFDB records, for an irreducible character of a finite group `G`, the smallest permutation
representation containing it, as a transitive group `nTt` (LMFDB
`group.representation.min_perm_rep`). Its degree `n` is the least index of a subgroup `H` of `G`
such that the permutation representation `k[G ⧸ H]` contains the representation `σ` affording the
character: LeanBridge's `Representation.minPermutationDegree` (LMFDB
`artin.permutation_container`), at which a transitive permutation representation is enough. The
transitive group is the image of `G` in the symmetric group on `G ⧸ H`, read through a numbering of
`G ⧸ H` by `{1, …, n}`, for a subgroup `H` of index `n` such that `k[G ⧸ H]` contains `σ`
(`Representation.IsMinPermutationContainer`); for an irreducible representation of a finite group
such subgroups exist (`Representation.exists_index_eq_minPermutationDegree`).

Several such subgroups `H` may give non-conjugate transitive groups. The knowl does not say which
the LMFDB records; for Artin representations it is one of least T-number (LMFDB
`artin.permutation_container`). The T-number `t` is a database numbering of the transitive groups
of degree `n` (LMFDB `gg.tnumber`), not formalised here. Tau Ceti's `TauCeti.TransitiveGroupLabel`
provides it in degrees at most five, which gives the labels `nTt` of the smallest permutation
representations containing `σ` in these degrees (`Representation.HasMinPermRepLabel`).

## Main definitions

* `Representation.IsMinPermutationContainer` (LMFDB `group.representation.min_perm_rep`): a
  subgroup `H` of least index such that `k[G ⧸ H]` contains `σ`.
* `Representation.HasMinPermRepLabel` (LMFDB `group.representation.min_perm_rep`): a smallest
  permutation representation containing `σ` is a transitive group with label `nTt`.

## Main results

* `Representation.HasMinPermRepLabel.degree_eq`: the degree `n` of a label `nTt` of a smallest
  permutation representation containing `σ` is the smallest degree.
-/

open MulAction TauCeti

namespace Representation

variable {k G W : Type*} [Field k] [Group G] [AddCommGroup W] [Module k W]
  (σ : Representation k G W) (H : Subgroup G) {n : ℕ} (j : TransitiveGroupIndex n)

/-- A subgroup `H` of `G` gives a **smallest permutation representation containing** `σ` (LMFDB
`group.representation.min_perm_rep`) if the permutation representation `k[G ⧸ H]` contains `σ` and
the index of `H` is the least degree `σ.minPermutationDegree` of a permutation representation
containing `σ`. The permutation representation is then the action of `G` on the `[G : H]` cosets
of `H`, a transitive permutation group of degree `[G : H]`, whose kernel is the normal core of
`H`. -/
def IsMinPermutationContainer : Prop :=
  H.index = σ.minPermutationDegree ∧ (ofMulAction k G (G ⧸ H)).Contains σ

/-- The transitive group with label `nT(j + 1)` (zero-based index `j`) is **a smallest permutation
representation containing** `σ` (LMFDB `group.representation.min_perm_rep`) if it is the image of
`G` in the symmetric group on `G ⧸ H`, read through a numbering of `G ⧸ H` by `Fin n`, for a
subgroup `H` giving a smallest permutation representation containing `σ`. The label is Tau Ceti's
`TransitiveGroupLabel`, which only exists in degrees at most five: the T-numbers of larger degrees
are a database numbering. Which of the possibly several such labels the LMFDB records is not
specified by the knowl. -/
def HasMinPermRepLabel : Prop :=
  ∃ (K : Subgroup G) (e : G ⧸ K ≃ Fin n), σ.IsMinPermutationContainer K ∧
    TransitiveGroupLabel j ((toPermHom G (G ⧸ K)).range.map e.permCongrHom.toMonoidHom)

variable {σ j} in
/-- **The degree `n` of the label `nT(j + 1)` of a smallest permutation representation containing
`σ` is the least degree of a permutation representation containing `σ`.** -/
lemma HasMinPermRepLabel.degree_eq (h : σ.HasMinPermRepLabel j) : n = σ.minPermutationDegree := by
  rcases h with ⟨K, e, ⟨hK, -⟩, -⟩
  rw [← hK, Subgroup.index, Nat.card_congr e, Nat.card_fin]

end Representation
