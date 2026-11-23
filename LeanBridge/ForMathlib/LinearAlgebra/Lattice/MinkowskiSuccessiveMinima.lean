import LeanBridge.ForMathlib.LinearAlgebra.Lattice.RootSublattice
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Reduction

/-!
# Minkowski-reduced bases of lattices of rank at most four

The norms of the vectors of a Minkowski-reduced basis `b₀, …, b_{n-1}` of a positive semidefinite
integral lattice `L` are comparable to its successive minima, `λᵢ ≤ β(bᵢ, bᵢ) ≤ (i!)² λᵢ` (Tau
Ceti). When `n ≤ 4` they are equal: the diagonal entries of a Minkowski-reduced Gram matrix are the
successive minima of `L` (LMFDB `lattice.gram`, after van der Waerden). As in Tau Ceti and in
reduction theory, the successive minima are norms `β(v, v)`; LMFDB `lattice.successive_minima`
measures them through the unit ball, as lengths, whose squares these are.

Let `y` be a vector of norm at most `λᵢ` outside the span of `b₀, …, b_{i-1}`, and `m ≥ i` the
last index at which the coordinate `c` of `y` is nonzero. If `c = ±1`, then `b₀, …, b_{m-1}, y`
extends to a basis, so `β(b_m, b_m) ≤ β(y, y)`. Otherwise `y = c a` with
`a = b_m + ∑_{j<m} (y_j / c) b_j` in the rational span. Rounding the coefficients `-y_j / c` one at
a time, each step costing at most `β(b_j, b_j) / 4` (the better of the two nearest integers), turns
`a` into a lattice vector `v = b_m - ∑_{j<m} n_j b_j` with
`β(v, v) ≤ β(a, a) + ∑_{j<m} β(b_j, b_j) / 4`. As `m ≤ 3` and the norms of a reduced basis
increase, this is at most `β(a, a) + 3 β(b_m, b_m) / 4`, while reduction gives
`β(b_m, b_m) ≤ β(v, v)`. So `β(a, a) ≥ β(b_m, b_m) / 4` and
`β(y, y) = c² β(a, a) ≥ β(b_m, b_m)`. In both cases `β(bᵢ, bᵢ) ≤ β(b_m, b_m) ≤ β(y, y) ≤ λᵢ`.

Minkowski reduction is not unique. A basis of minimal vectors is reduced, and the root lattice `A₃`
has two bases of roots, the simple roots `α₀, α₁, α₂` and their partial sums
`α₀, α₀ + α₁, α₀ + α₁ + α₂`, whose Gram matrices `(2, -1, 0; -1, 2, -1; 0, -1, 2)` and
`(2, 1, 1; 1, 2, 1; 1, 1, 2)` differ; no signed permutation of a basis relates them, as only the
first has a zero entry.

## Main definitions

* `TauCeti.IntegralLattice.typeAThreePartialSumBasis`: the basis `α₀, α₀ + α₁, α₀ + α₁ + α₂` of
  `A₃`.

## Main results

* `TauCeti.IntegralLattice.IsMinkowskiReduced.integralNorm_eq_successiveMinimum` and
  `TauCeti.IntegralLattice.IsMinkowskiReduced.gramMatrix_apply_self_eq_successiveMinimum` (LMFDB
  `lattice.gram`): in rank at most `4`, the norms of the vectors of a Minkowski-reduced basis, the
  diagonal entries of its Gram matrix, are the successive minima.
* `TauCeti.IntegralLattice.isMinkowskiReduced_of_forall_integralNorm_eq_minimum`: a basis of minimal
  vectors is Minkowski reduced.
* `TauCeti.IntegralLattice.isMinkowskiReduced_typeASimpleRootBasis` and
  `TauCeti.IntegralLattice.isMinkowskiReduced_typeAThreePartialSumBasis` (LMFDB `lattice.gram`): two
  Minkowski-reduced bases of `A₃`.
* `TauCeti.IntegralLattice.gramMatrix_typeAThreePartialSumBasis` and
  `TauCeti.IntegralLattice.gramMatrix_typeAThreePartialSumBasis_ne` (LMFDB `lattice.gram`): their
  Gram matrices differ, so Minkowski reduction is not unique.

## References

* B. L. van der Waerden, *Die Reduktionstheorie der positiven quadratischen Formen*, Acta Math. 96
  (1956), 265–309.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 12, §1.
-/

open Module

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V} {n : ℕ}
  {b : Basis (Fin n) ℤ L}

lemma exists_norm_add_sub_intCast_smul_le (hL : L.IsPosSemidef) (a x : V) (t : ℚ) :
    ∃ k : ℤ, L.norm (a + (t - k) • x) ≤ L.norm a + L.norm x / 4 := by
  have hx : 0 ≤ L.norm x := L.norm_apply x ▸ L.isPosSemidef_iff.mp hL x
  have h (s : ℚ) : L.norm (a + s • x) = L.norm a + s ^ 2 * L.norm x + 2 * (s * L.form a x) := by
    rw [L.norm_add, L.norm_smul, map_smul, smul_eq_mul]
  have hf0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have hf1 : 0 < 1 - Int.fract t := sub_pos.mpr (Int.fract_lt_one t)
  by_cases h₀ : L.norm (a + Int.fract t • x) ≤ L.norm a + L.norm x / 4
  · exact ⟨⌊t⌋, h₀⟩
  refine ⟨⌊t⌋ + 1, ?_⟩
  rw [h] at h₀
  rw [Int.cast_add, Int.cast_one, ← sub_sub, ← Int.fract, h]
  nlinarith [mul_nonneg hx (sq_nonneg (Int.fract t - 1 / 2))]

lemma exists_norm_add_sum_sub_intCast_smul_le (hL : L.IsPosSemidef) {ι : Type*} (s : Finset ι)
    (x : ι → V) (t : ι → ℚ) (a : V) : ∃ k : ι → ℤ,
    L.norm (a + ∑ j ∈ s, (t j - k j) • x j) ≤ L.norm a + (∑ j ∈ s, L.norm (x j)) / 4 := by
  classical
  induction s using Finset.induction_on generalizing a with
  | empty => exact ⟨0, by simp⟩
  | insert j s hj ih =>
    rcases exists_norm_add_sub_intCast_smul_le hL a (x j) (t j) with ⟨kj, hkj⟩
    rcases ih (a + (t j - kj) • x j) with ⟨k, hk⟩
    refine ⟨Function.update k j kj, ?_⟩
    have hs : ∑ i ∈ s, (t i - Function.update k j kj i) • x i = ∑ i ∈ s, (t i - k i) • x i :=
      Finset.sum_congr rfl fun i hi ↦ by
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Function.update_self, hs, ← add_assoc]
    linarith

/-- **A basis of minimal vectors is Minkowski reduced**: if every vector of the basis `b` of a
positive semidefinite lattice has norm the minimum, it has least norm among all candidates. -/
lemma isMinkowskiReduced_of_forall_integralNorm_eq_minimum (hL : L.IsPosSemidef)
    (hb : ∀ i, L.integralNorm (b i) = L.minimum) : L.IsMinkowskiReduced b :=
  fun i e _ ↦ (hb i).trans_le (hL.minimum_le_integralNorm (e.ne_zero i))

namespace IsMinkowskiReduced

variable {e : Basis (Fin (finrank ℤ L)) ℤ L} (i : Fin (finrank ℤ L))

lemma integralNorm_le_of_coord_eq_zero (hL : L.IsPosSemidef) (hb : L.IsMinkowskiReduced b)
    {m : Fin n} (hm : (m : ℕ) ≤ 3) {y : L} (hy : ∀ j, m < j → b.coord j y = 0)
    (hc : b.coord m y ≠ 0) : L.integralNorm (b m) ≤ L.integralNorm y := by
  classical
  have hsum : y = b.coord m y • b m + ∑ j ∈ Finset.Iio m, b.coord j y • b j := by
    have h : ∑ j ∈ insert m (Finset.Iio m), b.coord j y • b j =
        b.coord m y • b m + ∑ j ∈ Finset.Iio m, b.coord j y • b j :=
      Finset.sum_insert Finset.notMem_Iio_self
    rw [Finset.Iio_insert] at h
    rw [← h, Finset.sum_subset (Finset.subset_univ _) fun j _ hj ↦ by
      rw [hy j (not_le.mp (Finset.mem_Iic.not.mp hj)), zero_smul]]
    exact (b.sum_repr y).symm
  by_cases hc1 : b.coord m y ^ 2 = 1
  · refine hb.integralNorm_le_of_apply_eq_one (f := b.coord m y • b.coord m) (fun j hj ↦ ?_) ?_
    · simp [hj.ne]
    · rw [LinearMap.smul_apply, smul_eq_mul, ← sq, hc1]
  have hc4 : (4 : ℚ) ≤ (b.coord m y : ℚ) ^ 2 := by
    have h1 : b.coord m y ≠ 1 := fun h ↦ hc1 (by rw [h, one_pow])
    have h2 : b.coord m y ≠ -1 := fun h ↦ hc1 (by rw [h]; norm_num)
    have h4 : (4 : ℤ) ≤ b.coord m y ^ 2 := by
      rcases (by omega : b.coord m y ≤ -2 ∨ 2 ≤ b.coord m y) with h | h <;> nlinarith
    exact_mod_cast h4
  have hc0 : (b.coord m y : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hnorm (z : L) : 0 ≤ L.norm z := L.norm_apply z ▸ L.isPosSemidef_iff.mp hL z
  -- `y = c • a` with `a = b m + ∑_{j < m} (y_j / c) • b j` in the rational span
  let a : V := (b m : V) + ∑ j ∈ Finset.Iio m, ((b.coord j y : ℚ) / b.coord m y) • (b j : V)
  have hya : (y : V) = (b.coord m y : ℚ) • a := by
    conv_lhs => rw [hsum]
    simp only [a, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul_of_tower, smul_add,
      Finset.smul_sum, smul_smul, mul_div_cancel₀ _ hc0, Int.cast_smul_eq_zsmul]
  rcases exists_norm_add_sum_sub_intCast_smul_le hL (Finset.Iio m) (fun j ↦ (b j : V))
    (fun j ↦ -((b.coord j y : ℚ) / b.coord m y)) a with ⟨k, hk⟩
  let w : L := ∑ j ∈ Finset.Iio m, (-k j) • b j
  have hw : b.coord m w = 0 := by
    simp only [w, map_sum, map_zsmul, Basis.coord_apply, Basis.repr_self]
    exact Finset.sum_eq_zero fun j hj ↦ by
      rw [Finsupp.single_eq_of_ne' (Finset.mem_Iio.mp hj).ne, smul_zero]
  have hv : a + ∑ j ∈ Finset.Iio m, (-((b.coord j y : ℚ) / b.coord m y) - k j) • (b j : V) =
      ((b m + w : L) : V) := by
    simp only [w, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul]
    rw [add_assoc, ← Finset.sum_add_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [← add_smul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_neg]
    congr 1
    ring1
  have hred : (L.integralNorm (b m) : ℚ) ≤ L.integralNorm (b m + w) :=
    Int.cast_le.mpr (hb.integralNorm_le_integralNorm_add m hw)
  have hsumle : ∑ j ∈ Finset.Iio m, L.norm (b j) ≤ 3 * L.norm (b m) := by
    have h : ∑ j ∈ Finset.Iio m, L.norm (b j) ≤ (Finset.Iio m).card • L.norm (b m) :=
      Finset.sum_le_card_nsmul (Finset.Iio m) (fun j ↦ L.norm (b j)) (L.norm (b m)) fun j hj ↦ by
        rw [← L.integralNorm_cast, ← L.integralNorm_cast]
        exact_mod_cast hb.monotone_integralNorm (Finset.mem_Iio.mp hj).le
    rw [nsmul_eq_mul, Fin.card_Iio] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) (hnorm (b m)))
  rw [L.integralNorm_cast, L.integralNorm_cast, ← hv] at hred
  have hyn : (L.integralNorm y : ℚ) = (b.coord m y : ℚ) ^ 2 * L.norm a := by
    rw [L.integralNorm_cast, hya, L.norm_smul]
  have ha : L.norm (b m) / 4 ≤ L.norm a := by
    linarith
  have hca : 4 * L.norm a ≤ (b.coord m y : ℚ) ^ 2 * L.norm a :=
    mul_le_mul_of_nonneg_right hc4 ((div_nonneg (hnorm (b m)) zero_le_four).trans ha)
  have hq : (L.integralNorm (b m) : ℚ) ≤ L.integralNorm y := by
    rw [hyn, L.integralNorm_cast]
    linarith
  exact_mod_cast hq

/-- **In rank at most four, a Minkowski-reduced basis attains the successive minima** (van der
Waerden): the `i`-th vector of a Minkowski-reduced basis of a positive semidefinite lattice of rank
at most `4` has norm the `i`-th successive minimum. -/
lemma integralNorm_eq_successiveMinimum (hL : L.IsPosSemidef) (hn : finrank ℤ L ≤ 4)
    (he : L.IsMinkowskiReduced e) : L.integralNorm (e i) = L.successiveMinimum i := by
  classical
  refine le_antisymm ?_ (he.successiveMinimum_le_integralNorm (hL.integralNorm_nonneg _))
  rcases L.exists_integralNorm_le_successiveMinimum_not_mem_span i
    fun j ↦ e (Fin.castLE i.isLt.le j) with ⟨y, hyl, hyspan⟩
  have hspan : ∀ x : L, (∀ j, i ≤ j → e.coord j x = 0) →
      (x : V) ∈ Submodule.span ℚ (Set.range fun j ↦ (e (Fin.castLE i.isLt.le j) : V)) := by
    intro x hx
    rw [← e.sum_repr x, Submodule.coe_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [Submodule.coe_smul_of_tower]
    rcases lt_or_ge j i with hj | hj
    · have hmem : (e j : V) ∈ Set.range fun k : Fin i ↦ (e (Fin.castLE i.isLt.le k) : V) :=
        ⟨⟨j, hj⟩, by simp⟩
      exact zsmul_mem (Submodule.subset_span hmem) _
    · rw [← e.coord_apply, hx j hj, zero_smul]
      exact zero_mem _
  have hne : (e.repr y).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h
    exact hyspan (hspan y fun j _ ↦ by rw [e.coord_apply, h, Finsupp.zero_apply])
  have hm (j : Fin (finrank ℤ L)) (hj : (e.repr y).support.max' hne < j) : e.coord j y = 0 := by
    by_contra h
    exact (Finset.le_max' _ j (Finsupp.mem_support_iff.mpr h)).not_gt hj
  have him : i ≤ (e.repr y).support.max' hne := by
    by_contra! h
    exact hyspan (hspan y fun j hj ↦ hm j (h.trans_le hj))
  have hle : L.integralNorm (e ((e.repr y).support.max' hne)) ≤ L.integralNorm y :=
    he.integralNorm_le_of_coord_eq_zero hL (by omega) hm
      (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hne))
  exact (he.monotone_integralNorm him).trans (hle.trans (by exact_mod_cast hyl))

/-- **In rank at most four, the diagonal entries of a Minkowski-reduced Gram matrix are the
successive minima** (LMFDB `lattice.gram`, van der Waerden). -/
lemma gramMatrix_apply_self_eq_successiveMinimum (hL : L.IsPosSemidef) (hn : finrank ℤ L ≤ 4)
    (he : L.IsMinkowskiReduced e) : L.gramMatrix e i i = L.successiveMinimum i := by
  rw [gramMatrix_apply, ← integralNorm_apply, he.integralNorm_eq_successiveMinimum i hL hn]

end IsMinkowskiReduced

/-- **The simple roots of `Aₙ` form a Minkowski-reduced basis** (LMFDB `lattice.gram`): they are
roots, of norm `2`, the minimum of `Aₙ`. -/
lemma isMinkowskiReduced_typeASimpleRootBasis (k : ℕ) :
    (typeARootLattice k).IsMinkowskiReduced (typeASimpleRootBasis k) :=
  isMinkowskiReduced_of_forall_integralNorm_eq_minimum (isPosDef_typeARootLattice k).isPosSemidef
    fun i ↦ by
      rw [integralNorm_typeASimpleRootBasis k i, minimum_typeARootLattice k i.pos.ne']
      rfl

/-- The basis `α₀, α₀ + α₁, α₀ + α₁ + α₂` of the root lattice `A₃` (`typeARootLattice 3`) of the
partial sums of its simple roots `αᵢ` (`TauCeti.IntegralLattice.typeASimpleRootBasis`). -/
noncomputable def typeAThreePartialSumBasis : Basis (Fin 3) ℤ (typeARootLattice 3) :=
  (typeASimpleRootBasis 3).map <| Matrix.toLinearEquiv (typeASimpleRootBasis 3)
    !![1, 1, 1; 0, 1, 1; 0, 0, 1] (by simp [Matrix.det_fin_three])

lemma typeAThreePartialSumBasis_apply (i : Fin 3) : typeAThreePartialSumBasis i = ∑ j,
    (!![1, 1, 1; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ) j i • typeASimpleRootBasis 3 j := by
  rw [typeAThreePartialSumBasis, Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self]

/-- **The Gram matrix of the basis of partial sums of the simple roots of `A₃`** is
`(2, 1, 1; 1, 2, 1; 1, 1, 2)`. -/
lemma gramMatrix_typeAThreePartialSumBasis :
    (typeARootLattice 3).gramMatrix typeAThreePartialSumBasis = !![2, 1, 1; 1, 2, 1; 1, 1, 2] := by
  have h (i j : Fin 3) : (typeARootLattice 3).integralForm (typeASimpleRootBasis 3 i)
      (typeASimpleRootBasis 3 j) = CartanMatrix.A 3 i j := by
    rw [← gramMatrix_apply, gramMatrix_typeASimpleRootBasis]
  ext i j
  rw [gramMatrix_apply, typeAThreePartialSumBasis_apply, typeAThreePartialSumBasis_apply]
  simp only [Fin.sum_univ_three, map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, h]
  fin_cases i <;> fin_cases j <;> decide

/-- **The partial sums of the simple roots of `A₃` form a Minkowski-reduced basis** (LMFDB
`lattice.gram`): they are roots, of norm `2`, the minimum of `A₃`. -/
lemma isMinkowskiReduced_typeAThreePartialSumBasis :
    (typeARootLattice 3).IsMinkowskiReduced typeAThreePartialSumBasis := by
  have h (i : Fin 3) : (typeARootLattice 3).integralNorm (typeAThreePartialSumBasis i) = 2 := by
    rw [integralNorm_apply, ← gramMatrix_apply, gramMatrix_typeAThreePartialSumBasis]
    fin_cases i <;> rfl
  refine isMinkowskiReduced_of_forall_integralNorm_eq_minimum
    (isPosDef_typeARootLattice 3).isPosSemidef fun i ↦ ?_
  rw [h i, minimum_typeARootLattice 3 three_ne_zero]
  rfl

/-- **Minkowski reduction is not unique** (LMFDB `lattice.gram`): the simple roots of `A₃` and their
partial sums are two Minkowski-reduced bases of `A₃` with different Gram matrices. -/
lemma gramMatrix_typeAThreePartialSumBasis_ne : (typeARootLattice 3).gramMatrix
    typeAThreePartialSumBasis ≠ (typeARootLattice 3).gramMatrix (typeASimpleRootBasis 3) := by
  rw [gramMatrix_typeAThreePartialSumBasis, gramMatrix_typeASimpleRootBasis]
  decide

end TauCeti.IntegralLattice
