import LeanBridge.ForMathlib.Algebra.Module.ZLattice.PerfectHexagonal
import LeanBridge.ForMathlib.Algebra.Module.ZLattice.Voronoi

/-!
# The hexagonal lattice is extreme

The hexagonal lattice of `ℝ²` (`ZLattice.hexagonalLattice`, spanned by `(1, 0)` and
`(1 / 2, √3 / 2)`) has exactly six minimal vectors, `±(1, 0)`, `±(1 / 2, √3 / 2)` and
`±(1 / 2, -√3 / 2)`: the vector `a (1, 0) + b (1 / 2, √3 / 2)` has squared length `a² + a b + b²`,
which equals `1` for exactly six pairs of integers `(a, b)`. Writing `A = ⟪v, (1, 0)⟫` and
`B = ⟪v, (1 / 2, √3 / 2)⟫`, the sum of the `⟪v, x⟫²` over the minimal vectors `x` is
`2 (A² + B² + (A - B)²) = 3 ⟪v, v⟫`, so the hexagonal lattice is strongly eutactic (LMFDB
`lattice.eutactic`). It is perfect (`ZLattice.isPerfect_hexagonalLattice`), so by Voronoi's theorem
it is extreme (LMFDB `lattice.extreme`): extreme lattices, and lattices that are both perfect and
eutactic, exist.

## Main results

* `ZLattice.isStronglyEutactic_hexagonalLattice` (LMFDB `lattice.eutactic`): the hexagonal lattice
  is strongly eutactic.
* `ZLattice.isExtreme_hexagonalLattice` (LMFDB `lattice.extreme`): the hexagonal lattice is
  extreme.
-/

open scoped InnerProductSpace

namespace ZLattice

lemma zsmul_add_zsmul_injective_hexagonal : Function.Injective fun p : ℤ × ℤ ↦
    p.1 • (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) + p.2 • !₂[1 / 2, √3 / 2] := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h0 : (a : ℝ) + b * 2⁻¹ = c + d * 2⁻¹ := by
    simpa using congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) h
  have h1 : b = d := by
    simpa using congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1) h
  rw [h1, add_left_inj] at h0
  rw [Int.cast_inj.mp h0, h1]

lemma mem_of_sq_add_mul_add_sq_eq_one {a b : ℤ} (h : a ^ 2 + a * b + b ^ 2 = 1) :
    (a, b) ∈ ({(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)} : Finset (ℤ × ℤ)) := by
  have hb1 : b ≤ 1 := by
    nlinarith [sq_nonneg (2 * a + b)]
  have hb2 : -1 ≤ b := by
    nlinarith [sq_nonneg (2 * a + b)]
  have ha1 : a ≤ 1 := by
    nlinarith [sq_nonneg (a + 2 * b)]
  have ha2 : -1 ≤ a := by
    nlinarith [sq_nonneg (a + 2 * b)]
  interval_cases a <;> interval_cases b <;> simp_all

lemma minimalVectors_hexagonalLattice : minimalVectors hexagonalLattice =
    (fun p : ℤ × ℤ ↦ p.1 • (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) + p.2 • !₂[1 / 2, √3 / 2]) ''
      ↑({(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)} : Finset (ℤ × ℤ)) := by
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · rcases Submodule.mem_span_pair.mp hx.1 with ⟨a, b, rfl⟩
    have h : ((a ^ 2 + a * b + b ^ 2 : ℤ) : ℝ) = 1 := by
      push_cast
      rw [← norm_sq_zsmul_add_zsmul_hexagonal, hx.2.2, minimum_hexagonalLattice, one_pow]
    exact ⟨(a, b), mem_of_sq_add_mul_add_sq_eq_one (Int.cast_eq_one.mp h), rfl⟩
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    refine zsmul_add_zsmul_mem_minimalVectors_hexagonalLattice a b ?_
    simp only [Finset.coe_insert, Finset.coe_singleton] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rfl

/-- **The hexagonal lattice is strongly eutactic** (LMFDB `lattice.eutactic`): for every `v ∈ ℝ²`,
`⟪v, v⟫ = (1 / 3) ∑ₓ ⟪v, x⟫²`, the sum ranging over its six minimal vectors `x`. -/
lemma isStronglyEutactic_hexagonalLattice : IsStronglyEutactic hexagonalLattice := by
  have h3 : (√3 : ℝ) * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  refine ⟨1 / 3, by norm_num, fun v ↦ ?_⟩
  have he1 : ⟪v, (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))⟫_ℝ = v 0 := by
    simp [PiLp.inner_apply]
  have he2 : ⟪v, (!₂[1 / 2, √3 / 2] : EuclideanSpace ℝ (Fin 2))⟫_ℝ = v 0 / 2 + √3 / 2 * v 1 := by
    simp [PiLp.inner_apply]
    ring1
  rw [real_inner_self_eq_norm_sq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs, minimalVectors_hexagonalLattice,
    finsum_mem_image zsmul_add_zsmul_injective_hexagonal.injOn, finsum_mem_coe_finset,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [one_smul, zero_smul, neg_smul, add_zero, zero_add, inner_add_right, inner_neg_right,
    he1, he2]
  linear_combination (-(v 1 ^ 2) / 3) * h3

/-- **The hexagonal lattice is extreme** (LMFDB `lattice.extreme`): it is perfect
(`ZLattice.isPerfect_hexagonalLattice`) and eutactic, hence extreme by Voronoi's theorem
(`ZLattice.IsPerfect.isExtreme`). -/
lemma isExtreme_hexagonalLattice : IsExtreme hexagonalLattice := by
  have hd : DiscreteTopology hexagonalLattice := isPerfect_hexagonalLattice.discreteTopology
  have hz : IsZLattice ℝ hexagonalLattice := isPerfect_hexagonalLattice.isZLattice
  exact isPerfect_hexagonalLattice.isExtreme isStronglyEutactic_hexagonalLattice.isEutactic

end ZLattice
