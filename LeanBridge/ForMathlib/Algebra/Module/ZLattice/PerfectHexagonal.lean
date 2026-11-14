import LeanBridge.ForMathlib.Algebra.Module.ZLattice.Perfect

/-!
# The hexagonal lattice is perfect

The hexagonal lattice of `ℝ²`, spanned by `(1, 0)` and `(1 / 2, √3 / 2)`, has minimal norm `1`,
and its six minimal vectors `±(1, 0)`, `±(1 / 2, √3 / 2)` and `±(-1 / 2, √3 / 2)` give three
matrices `x xᵀ` that span the three-dimensional space of symmetric `2 × 2` real matrices. So it is
a perfect lattice (LMFDB `lattice.perfect`) of dimension `2`: the results about perfect lattices
are not vacuous.

## Main definitions

* `ZLattice.hexagonalLattice`: the hexagonal lattice of `ℝ²`.

## Main results

* `ZLattice.minimum_hexagonalLattice`: the shortest nonzero vectors of the hexagonal lattice have
  length `1`.
* `ZLattice.isPerfect_hexagonalLattice` (LMFDB `lattice.perfect`): the hexagonal lattice is
  perfect.
-/

open Matrix

namespace ZLattice

/-- The **hexagonal lattice** of `ℝ²`: the lattice spanned by `(1, 0)` and `(1 / 2, √3 / 2)`, the
root lattice `A₂` scaled to minimal norm `1`. -/
noncomputable def hexagonalLattice : Submodule ℤ (EuclideanSpace ℝ (Fin 2)) :=
  Submodule.span ℤ {!₂[1, 0], !₂[1 / 2, √3 / 2]}

variable (a b : ℤ)

lemma norm_sq_zsmul_add_zsmul_hexagonal :
    ‖a • (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) + b • !₂[1 / 2, √3 / 2]‖ ^ 2 = a ^ 2 + a * b +
      b ^ 2 := by
  have h3 : (√3 : ℝ) * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs]
  simp
  linear_combination (b ^ 2 / 4 : ℝ) * h3

lemma zsmul_add_zsmul_mem_hexagonalLattice :
    a • (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) + b • !₂[1 / 2, √3 / 2] ∈ hexagonalLattice :=
  Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩

lemma one_le_norm_of_mem_hexagonalLattice {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ hexagonalLattice)
    (hx₀ : x ≠ 0) : 1 ≤ ‖x‖ := by
  rcases Submodule.mem_span_pair.mp hx with ⟨a, b, rfl⟩
  have hab : 0 < a ^ 2 + a * b + b ^ 2 := by
    by_contra h
    have hb : b = 0 := by
      nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
    have ha : a = 0 := by
      nlinarith [sq_nonneg a]
    rw [ha, hb, zero_smul, zero_smul, add_zero] at hx₀
    exact hx₀ rfl
  rw [← one_le_sq_iff₀ (norm_nonneg _), norm_sq_zsmul_add_zsmul_hexagonal]
  exact_mod_cast hab

/-- **The shortest nonzero vectors of the hexagonal lattice have length `1`.** -/
lemma minimum_hexagonalLattice : minimum hexagonalLattice = 1 := by
  refine IsLeast.csInf_eq ⟨⟨!₂[1, 0], ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simpa using zsmul_add_zsmul_mem_hexagonalLattice 1 0
  · exact fun h ↦ one_ne_zero (congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) h)
  · exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp <| by
      simpa using norm_sq_zsmul_add_zsmul_hexagonal 1 0
  · rintro _ ⟨x, ⟨hx, hx₀⟩, rfl⟩
    exact one_le_norm_of_mem_hexagonalLattice hx hx₀

lemma zsmul_add_zsmul_mem_minimalVectors_hexagonalLattice (hab : a ^ 2 + a * b + b ^ 2 = 1) :
    a • (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) + b • !₂[1 / 2, √3 / 2] ∈
      minimalVectors hexagonalLattice := by
  have h1 : ‖a • (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) + b • !₂[1 / 2, √3 / 2]‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp <| by
      rw [norm_sq_zsmul_add_zsmul_hexagonal]
      exact_mod_cast hab
  refine ⟨zsmul_add_zsmul_mem_hexagonalLattice a b, fun h0 ↦ ?_,
    h1.trans minimum_hexagonalLattice.symm⟩
  rw [h0, norm_zero] at h1
  exact zero_ne_one h1

/-- **The hexagonal lattice is perfect** (LMFDB `lattice.perfect`): the matrices `x xᵀ` of its
minimal vectors `(1, 0)`, `(1 / 2, √3 / 2)` and `(-1 / 2, √3 / 2)` span the symmetric `2 × 2` real
matrices. -/
lemma isPerfect_hexagonalLattice : IsPerfect hexagonalLattice := by
  intro A hA
  have h3 : (√3 : ℝ) * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h10 : A 1 0 = A 0 1 := hA.apply 0 1
  have m1 : (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) ∈ minimalVectors hexagonalLattice := by
    simpa using zsmul_add_zsmul_mem_minimalVectors_hexagonalLattice 1 0 rfl
  have m2 : (!₂[1 / 2, √3 / 2] : EuclideanSpace ℝ (Fin 2)) ∈ minimalVectors hexagonalLattice := by
    simpa using zsmul_add_zsmul_mem_minimalVectors_hexagonalLattice 0 1 rfl
  have m3 : (!₂[-1 / 2, √3 / 2] : EuclideanSpace ℝ (Fin 2)) ∈ minimalVectors hexagonalLattice := by
    have e : (-1 : ℤ) • (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) + (1 : ℤ) • !₂[1 / 2, √3 / 2] =
        !₂[-1 / 2, √3 / 2] := by
      ext i
      fin_cases i
      · norm_num
      · simp
    exact e ▸ zsmul_add_zsmul_mem_minimalVectors_hexagonalLattice (-1) 1 rfl
  have hA' : A = (A 0 0 - A 1 1 / 3) • vecMulVec ![1, 0] ![1, 0] +
      (2 / 3 * A 1 1 + 2 * √3 / 3 * A 0 1) • vecMulVec ![1 / 2, √3 / 2] ![1 / 2, √3 / 2] +
      (2 / 3 * A 1 1 - 2 * √3 / 3 * A 0 1) • vecMulVec ![-1 / 2, √3 / 2] ![-1 / 2, √3 / 2] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp
      ring1
    · simp
      linear_combination (-(A 0 1) / 3) * h3
    · simp [h10]
      linear_combination (-(A 0 1) / 3) * h3
    · simp
      linear_combination (-(A 1 1) / 3) * h3
  rw [hA']
  exact Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, m1, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, m2, rfl⟩)))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, m3, rfl⟩))

end ZLattice
