import TauCeti.NumberTheory.ArithmeticDirichletSeries.Perron.Basic

/-!
# The polar terms of Hecke's lemma

The constant term of an exponential sum gives its completed Dirichlet series simple poles at `0` and
at the weight `κ`. The contribution of these poles to the shift of a line of integration is computed
by Perron's formula for `y ^ (-s) / s`.

## Main results

* `ModularForm.tendsto_sub_integral_cpow_div`: the integrals of `y ^ (-s) / s` over two vertical
  lines on either side of `0`, truncated at height `T`, differ by a quantity tending to `2π`.
* `ModularForm.tendsto_sub_integral_cpow_div_sub`: the integrals of `y ^ (-s) / (x - s)` over two
  vertical lines on either side of `x`, truncated at height `T`, differ by a quantity tending to
  `-2π y ^ (-x)`.
-/

open Complex Filter Topology TauCeti

open scoped Real

namespace ModularForm

variable {x y a b : ℝ}

private lemma perronStep_add_inv (hy : 0 < y) : perronStep y⁻¹ + perronStep y = 1 := by
  rcases lt_trichotomy y 1 with h | rfl | h
  · rw [perronStep_of_one_lt ((one_lt_inv₀ hy).mpr h), perronStep_of_lt_one h, add_zero]
  · simp only [perronStep_one]
    norm_num
  · rw [perronStep_of_lt_one (inv_lt_one_of_one_lt₀ h), perronStep_of_one_lt h, zero_add]

/-- **The residue of `y ^ (-s) / s` at `0`**: for `a < 0 < b`, the integrals of `y ^ (-s) / s` over
the lines `Re s = b` and `Re s = a`, truncated at height `T`, differ by a quantity tending to
`2π`. -/
lemma tendsto_sub_integral_cpow_div (hy : 0 < y) (ha : a < 0) (hb : 0 < b) : Tendsto
    (fun T : ℝ ↦ (∫ t in -T..T, (y : ℂ) ^ (-((b : ℂ) + t * I)) / ((b : ℂ) + t * I)) -
      ∫ t in -T..T, (y : ℂ) ^ (-((a : ℂ) + t * I)) / ((a : ℂ) + t * I)) atTop
        (𝓝 ((2 * π : ℝ) : ℂ)) := by
  have h2pi : ((2 * π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have h1 : ∀ T : ℝ, ∫ t in -T..T, (y : ℂ) ^ (-((b : ℂ) + t * I)) / ((b : ℂ) + t * I) =
      ((2 * π : ℝ) : ℂ) * truncatedPerronKernel y⁻¹ b T := fun T ↦ by
    rw [truncatedPerronKernel_def, mul_inv_cancel_left₀ h2pi]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    have harg : (y : ℂ).arg ≠ π := by
      rw [arg_ofReal_of_nonneg hy.le]
      exact Real.pi_pos.ne
    simp only [perronIntegrand]
    rw [ofReal_inv, inv_cpow _ _ harg, cpow_neg]
  have h2 : ∀ T : ℝ, ∫ t in -T..T, (y : ℂ) ^ (-((a : ℂ) + t * I)) / ((a : ℂ) + t * I) =
      -(((2 * π : ℝ) : ℂ) * truncatedPerronKernel y (-a) T) := fun T ↦ by
    have e :
        ∫ t in -T..T, perronIntegrand y (-a) (-t) = ∫ t in -T..T, perronIntegrand y (-a) t := by
      rw [intervalIntegral.integral_comp_neg, neg_neg]
    rw [truncatedPerronKernel_def, mul_inv_cancel_left₀ h2pi, ← e, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    have e1 : -((a : ℂ) + t * I) = ((-a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
      push_cast
      ring1
    have e2 : (a : ℂ) + t * I = -(((-a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      push_cast
      ring1
    simp only [perronIntegrand]
    rw [e1, e2, div_neg]
  simp only [h1, h2]
  have hlim : Tendsto (fun T : ℝ ↦ ((2 * π : ℝ) : ℂ) *
      (truncatedPerronKernel y⁻¹ b T + truncatedPerronKernel y (-a) T)) atTop
        (𝓝 (((2 * π : ℝ) : ℂ) * (perronStep y⁻¹ + perronStep y))) :=
    ((tendsto_truncatedPerronKernel (inv_pos.mpr hy) hb).add
      (tendsto_truncatedPerronKernel hy (neg_pos.mpr ha))).const_mul _
  rw [perronStep_add_inv hy, mul_one] at hlim
  refine hlim.congr fun T ↦ ?_
  ring1

variable (x) in
private lemma integral_cpow_div_sub (hy : 0 < y) (w T : ℝ) : ∫ t in -T..T,
    (y : ℂ) ^ (-((w : ℂ) + t * I)) / ((x : ℂ) - ((w : ℂ) + t * I)) = -(y : ℂ) ^ (-(x : ℂ)) *
      ∫ t in -T..T, (y : ℂ) ^ (-(((w - x : ℝ) : ℂ) + t * I)) / (((w - x : ℝ) : ℂ) + t * I) := by
  have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  have e1 : -((w : ℂ) + t * I) = -(x : ℂ) + -(((w - x : ℝ) : ℂ) + t * I) := by
    push_cast
    ring1
  have e2 : (x : ℂ) - ((w : ℂ) + t * I) = -(((w - x : ℝ) : ℂ) + t * I) := by
    push_cast
    ring1
  rw [e1, cpow_add _ _ hyc, e2, div_neg]
  ring1

/-- **The residue of `y ^ (-s) / (x - s)` at `x`**: for `a < x < b`, the integrals of
`y ^ (-s) / (x - s)` over the lines `Re s = b` and `Re s = a`, truncated at height `T`, differ by a
quantity tending to `-2π y ^ (-x)`. -/
lemma tendsto_sub_integral_cpow_div_sub (hy : 0 < y) (ha : a < x) (hb : x < b) : Tendsto
    (fun T : ℝ ↦ (∫ t in -T..T, (y : ℂ) ^ (-((b : ℂ) + t * I)) / ((x : ℂ) - ((b : ℂ) + t * I))) -
      ∫ t in -T..T, (y : ℂ) ^ (-((a : ℂ) + t * I)) / ((x : ℂ) - ((a : ℂ) + t * I))) atTop
        (𝓝 (-(y : ℂ) ^ (-(x : ℂ)) * ((2 * π : ℝ) : ℂ))) := by
  refine ((tendsto_sub_integral_cpow_div hy (sub_neg.mpr ha) (sub_pos.mpr hb)).const_mul _).congr
    fun T ↦ ?_
  rw [mul_sub, integral_cpow_div_sub x hy b T, integral_cpow_div_sub x hy a T]

end ModularForm
