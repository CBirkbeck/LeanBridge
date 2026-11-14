import LeanBridge.ForMathlib.LinearAlgebra.Lattice.Sublattice
import Mathlib.Algebra.Order.Group.PiLex

/-!
# Normalized minimal vectors of an integral lattice

The minimal vectors of an integral lattice `L` (LMFDB `lattice.minimal_vector`), its nonzero vectors
whose norm is the minimum of `L`, come in pairs (LMFDB `lattice.normalized_minimal_vector`): with
`v`, the vector `-v` is a minimal vector, and `-v ≠ v`. The LMFDB lists one vector of each pair, the
normalized one: in the `ℤ`-basis of `L` in which the LMFDB stores its Gram matrix, a vector is
normalized if its first nonzero coordinate is positive. In the lexicographic order of the
coordinates this says that the vector is positive, so exactly one of `v` and `-v` is normalized when
`v ≠ 0`. Hence the minimal vectors are the normalized ones and their negatives, and the kissing
number of a positive definite lattice is twice the number of its normalized minimal vectors.

## Main definitions

* `TauCeti.IntegralLattice.IsNormalized` (LMFDB `lattice.normalized_minimal_vector`): the first
  nonzero coordinate is positive.

## Main results

* `TauCeti.IntegralLattice.neg_mem_minimalVectors_iff` (LMFDB `lattice.normalized_minimal_vector`):
  `-v` is a minimal vector exactly when `v` is.
* `TauCeti.IntegralLattice.neg_ne_self_of_mem_minimalVectors`: a minimal vector `v` differs from
  `-v`.
* `TauCeti.IntegralLattice.isNormalized_neg_iff`: exactly one of a nonzero vector and its negative
  is normalized.
* `TauCeti.IntegralLattice.kissingNumber_eq_two_mul_ncard`: the kissing number of a positive
  definite lattice is twice the number of its normalized minimal vectors.
-/

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V} {ι : Type*}
  [LinearOrder ι] (b : Module.Basis ι ℤ L) {x : L}

/-- **The minimal vectors come in pairs** (LMFDB `lattice.normalized_minimal_vector`): `-v` is a
minimal vector of an integral lattice exactly when `v` is. -/
lemma neg_mem_minimalVectors_iff : -x ∈ L.minimalVectors ↔ x ∈ L.minimalVectors := by
  rw [minimalVectors, Set.mem_sdiff, Set.mem_sdiff, neg_mem_vectorsOfNorm_iff,
    Set.mem_singleton_iff, Set.mem_singleton_iff, neg_eq_zero]

/-- **A minimal vector `v` differs from `-v`**: it is nonzero, and the lattice has no
`2`-torsion. -/
lemma neg_ne_self_of_mem_minimalVectors (hx : x ∈ L.minimalVectors) : -x ≠ x := fun h ↦ by
  have h₂ : (2 : ℚ) • (x : V) = 0 := by
    rw [two_smul]
    nth_rw 1 [← h]
    rw [Submodule.coe_neg, neg_add_cancel]
  exact ((L.mem_minimalVectors_iff x).mp hx).2 <|
    Subtype.ext ((smul_eq_zero.mp h₂).resolve_left two_ne_zero)

variable (x) in
/-- A vector `x` of an integral lattice `L` is **normalized** (LMFDB
`lattice.normalized_minimal_vector`) for a `ℤ`-basis `b` of `L` indexed by a linearly ordered type,
such as `Fin n` for the basis in which the LMFDB stores the Gram matrix of `L`, if its first nonzero
coordinate in `b` is positive. -/
def IsNormalized : Prop :=
  ∃ i, (∀ j < i, b.repr x j = 0) ∧ 0 < b.repr x i

lemma isNormalized_iff_pos_toLex : IsNormalized b x ↔ 0 < toLex ⇑(b.repr x) :=
  exists_congr fun _ ↦ and_congr (forall₂_congr fun _ _ ↦ eq_comm) Iff.rfl

variable [WellFoundedLT ι]

/-- **Exactly one of a nonzero vector and its negative is normalized**: in the lexicographic order
of the coordinates, a nonzero vector is either positive or negative. -/
lemma isNormalized_neg_iff (hx : x ≠ 0) : IsNormalized b (-x) ↔ ¬IsNormalized b x := by
  have h : toLex ⇑(b.repr x) ≠ 0 := fun h₀ ↦ hx <| b.repr.injective <| by
    rw [map_zero]
    exact DFunLike.coe_injective h₀
  rw [isNormalized_iff_pos_toLex, isNormalized_iff_pos_toLex, map_neg, Finsupp.coe_neg,
    toLex_neg, neg_pos]
  exact ⟨lt_asymm, fun h₁ ↦ (lt_or_gt_of_ne h).resolve_right h₁⟩

/-- **The kissing number of a positive definite lattice is twice the number of its normalized
minimal vectors**: the minimal vectors are the normalized ones and their negatives. -/
lemma kissingNumber_eq_two_mul_ncard (hL : L.IsPosDef) :
    L.kissingNumber = 2 * {x | x ∈ L.minimalVectors ∧ IsNormalized b x}.ncard := by
  have hfin : {x | x ∈ L.minimalVectors ∧ IsNormalized b x}.Finite :=
    ((hL.finite_vectorsOfNorm _).subset Set.sdiff_subset).subset fun _ hx ↦ hx.1
  have hunion : L.minimalVectors = {x | x ∈ L.minimalVectors ∧ IsNormalized b x} ∪
      Neg.neg '' {x | x ∈ L.minimalVectors ∧ IsNormalized b x} := by
    refine subset_antisymm (fun y hy ↦ ?_) (Set.union_subset (fun _ hy ↦ hy.1) ?_)
    · by_cases hn : IsNormalized b y
      · exact Or.inl ⟨hy, hn⟩
      · refine Or.inr ⟨-y, ⟨neg_mem_minimalVectors_iff.mpr hy, ?_⟩, neg_neg y⟩
        exact (isNormalized_neg_iff b ((L.mem_minimalVectors_iff y).mp hy).2).mpr hn
    · rintro _ ⟨y, hy, rfl⟩
      exact neg_mem_minimalVectors_iff.mpr hy.1
  have hdisj : Disjoint {x | x ∈ L.minimalVectors ∧ IsNormalized b x}
      (Neg.neg '' {x | x ∈ L.minimalVectors ∧ IsNormalized b x}) := by
    refine Set.disjoint_left.mpr fun y hy ↦ ?_
    rintro ⟨z, hz, rfl⟩
    exact (isNormalized_neg_iff b ((L.mem_minimalVectors_iff z).mp hz.1).2).mp hy.2 hz.2
  rw [L.kissingNumber_eq_ncard_minimalVectors]
  nth_rw 1 [hunion]
  rw [Set.ncard_union_eq hdisj hfin (hfin.image _), Set.ncard_image_of_injective _ neg_injective,
    two_mul]

end TauCeti.IntegralLattice
