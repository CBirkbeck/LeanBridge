import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Covolume
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Minimum

/-!
# Kissing numbers

The kissing number (LMFDB `lattice.kissing`) of a positive definite integral lattice `L` is its
number of vectors of minimal length, Tau Ceti's `TauCeti.IntegralLattice.kissingNumber`. It counts
`v` and `-v` alike, so that it is twice the number of normalised minimal vectors listed by the
LMFDB.

The lattice kissing number problem in dimension `n` is to find the lattices of rank `n` with the
largest kissing number: `TauCeti.IntegralLattice.latticeKissingNumber n` is that largest kissing
number, and `TauCeti.IntegralLattice.IsKissingOptimal` says that a lattice attains it. As in the
LMFDB, lattices are integral; every lattice of `ℝⁿ` can be deformed into a perfect one without
losing minimal vectors, and perfect lattices are similar to integral ones (Voronoi), so this is
also the classical lattice kissing number problem in `ℝⁿ`, but that is not formalised.

The general kissing number problem asks for the largest number of balls of `ℝⁿ` with disjoint
interiors that touch a fixed ball, all of the same radius: `EuclideanSpace.kissingNumber n`. A
positive definite lattice of rank `n` gives such a configuration, so its kissing number is at most
the kissing number of `ℝⁿ`; the inequality can be strict.

## Main definitions

* `TauCeti.IntegralLattice.latticeKissingNumber` (LMFDB `lattice.kissing`).
* `TauCeti.IntegralLattice.IsKissingOptimal` (LMFDB `lattice.kissing`).
* `EuclideanSpace.kissingNumber` (LMFDB `lattice.kissing`).

## Main results

* `TauCeti.IntegralLattice.kissingNumber_le_latticeKissingNumber`: the kissing number of a positive
  definite lattice of rank `n`, in any rational space, is at most the lattice kissing number in
  dimension `n`.
* `TauCeti.IntegralLattice.IsKissingOptimal.kissingNumber_le`: a lattice solving the lattice kissing
  number problem has a kissing number at least that of every positive definite lattice of the same
  rank.
* `TauCeti.IntegralLattice.kissingNumber_le_euclideanSpace_kissingNumber`: the kissing number of a
  positive definite lattice of rank `n` is at most the kissing number of `ℝⁿ`.
-/

open Module
open scoped InnerProductSpace

/-- The **kissing number** of `ℝⁿ` (LMFDB `lattice.kissing`, the general kissing number problem):
the largest number of balls of radius `1` of `ℝⁿ` with pairwise disjoint interiors that touch a
fixed ball of radius `1`, that is of points at distance `2` from the centre `0` of the fixed ball
and at distance at least `2` from each other; a supremum in `ℕ∞`. -/
noncomputable def EuclideanSpace.kissingNumber (n : ℕ) : ℕ∞ :=
  ⨆ (s : Finset (EuclideanSpace ℝ (Fin n))) (_ : ∀ x ∈ s, ‖x‖ = 2)
    (_ : (s : Set (EuclideanSpace ℝ (Fin n))).Pairwise fun x y ↦ 2 ≤ dist x y), (s.card : ℕ∞)

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- The **lattice kissing number** in dimension `n` (LMFDB `lattice.kissing`): the largest kissing
number of a positive definite integral lattice of rank `n`, a supremum in `ℕ∞`. It is taken over the
lattices of `ℚⁿ`, which is no restriction (`kissingNumber_le_latticeKissingNumber`). -/
noncomputable def latticeKissingNumber (n : ℕ) : ℕ∞ :=
  ⨆ (M : IntegralLattice (Fin n → ℚ)) (_ : M.IsPosDef), (M.kissingNumber : ℕ∞)

/-- A positive definite integral lattice `L` **solves the lattice kissing number problem** (LMFDB
`lattice.kissing`) in its dimension `n` if its kissing number is the largest kissing number of a
positive definite lattice of rank `n`. -/
def IsKissingOptimal : Prop :=
  L.IsPosDef ∧ latticeKissingNumber (finrank ℤ L) ≤ L.kissingNumber

variable {L}

/-- **The kissing number of a positive definite lattice of rank `n` is at most the lattice kissing
number in dimension `n`**, whatever rational space the lattice lies in. -/
lemma kissingNumber_le_latticeKissingNumber (hL : L.IsPosDef) :
    (L.kissingNumber : ℕ∞) ≤ latticeKissingNumber (finrank ℤ L) := by
  have : FiniteDimensional ℚ V := L.finiteDimensional
  let e : Isometry L (L.transport (finBasisOfFinrankEq ℚ V L.finrank_carrier.symm).equivFun) :=
    L.transportIsometry _
  exact e.kissingNumber_eq ▸ le_iSup₂_of_le (L.transport _) (e.isPosDef_iff.mp hL) le_rfl

/-- **A lattice solving the lattice kissing number problem has a kissing number at least that of
every positive definite lattice of the same rank.** -/
lemma IsKissingOptimal.kissingNumber_le (hL : L.IsKissingOptimal) {W : Type*} [AddCommGroup W]
    [Module ℚ W] {M : IntegralLattice W} (hM : M.IsPosDef) (hrank : finrank ℤ M = finrank ℤ L) :
    M.kissingNumber ≤ L.kissingNumber :=
  ENat.natCast_le_natCast.mp <| (kissingNumber_le_latticeKissingNumber hM).trans (hrank ▸ hL.2)

/-- **The kissing number of a positive definite lattice of rank `n` is at most the kissing number of
`ℝⁿ`**: rescaled to length `2` in a realization of the lattice in `ℝⁿ`, its minimal vectors are the
centres of balls of radius `1` touching the ball of radius `1` centred at `0`. -/
lemma kissingNumber_le_euclideanSpace_kissingNumber (hL : L.IsPosDef) :
    (L.kissingNumber : ℕ∞) ≤ EuclideanSpace.kissingNumber (finrank ℤ L) := by
  rcases subsingleton_or_nontrivial L with hL0 | hL0
  · simp
  rcases hL.exists_realization with ⟨φ, hφ, -⟩
  have hm : (0 : ℝ) < √(L.minimum : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hL.minimum_pos)
  have hc : 0 ≤ 2 / √(L.minimum : ℝ) := (div_pos two_pos hm).le
  have hφ' (x : L) : ‖φ x‖ = √(L.integralNorm x : ℝ) := by
    rw [integralNorm_apply, ← hφ, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hfin : (L.vectorsOfNorm L.minimum \ {0}).Finite := (hL.finite_vectorsOfNorm _).sdiff
  have hdist (x y : L) (hxy : x ≠ y) :
      2 ≤ dist ((2 / √(L.minimum : ℝ)) • φ x) ((2 / √(L.minimum : ℝ)) • φ y) := by
    rw [dist_eq_norm, ← smul_sub, ← map_sub, norm_smul_of_nonneg hc, hφ', div_mul_eq_mul_div,
      le_div_iff₀ hm]
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) zero_le_two
    exact_mod_cast hL.isPosSemidef.minimum_le_integralNorm (sub_ne_zero.mpr hxy)
  have hinj : Set.InjOn (fun x ↦ (2 / √(L.minimum : ℝ)) • φ x) hfin.toFinset :=
    fun x _ y _ hxy ↦ by_contra fun hne ↦
      (hdist x y hne).not_gt ((dist_eq_zero.mpr hxy).trans_lt two_pos)
  refine le_iSup₂_of_le (hfin.toFinset.image fun x ↦ (2 / √(L.minimum : ℝ)) • φ x) ?_
    (le_iSup_of_le ?_ ?_)
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    rw [hfin.mem_toFinset, Set.mem_sdiff, mem_vectorsOfNorm_natCast] at hx
    rw [norm_smul_of_nonneg hc, hφ', hx.1, Int.cast_natCast, div_mul_cancel₀ _ hm.ne']
  · rw [Finset.coe_image]
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ hne
    exact hdist x y fun h ↦ hne (h ▸ rfl)
  · rw [kissingNumber_def, Set.ncard_eq_toFinset_card _ hfin, Finset.card_image_of_injOn hinj]

end TauCeti.IntegralLattice
