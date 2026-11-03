import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The integral of `y ^ (-3/2) e^{-A y - T / y}`

For `A, T > 0`, `∫₀^∞ y ^ (-3/2) e^{-A y - T / y} dy = √(π / T) e^{-2 √(A T)}`: this is the Bessel
function `K_{1/2}`, which is elementary. The proof is the substitution of Cauchy and Schlömilch:
`y = √(T / A) p²` gives `2 r ^ (-1/2) ∫₀^∞ p ^ (-2) e^{-c (p² + p ^ (-2))} dp`, with `c = √(A T)`,
the inversion `p ↦ 1 / p` shows that the factor `p ^ (-2)` may be replaced by `(1 + p ^ (-2)) / 2`,
and `t = p - 1 / p` then gives a Gaussian integral over `ℝ`.

## Main results

* `MeasureTheory.integrableOn_rpow_neg_mul_exp_neg_add_div`: the integrand is integrable.
* `MeasureTheory.integral_rpow_neg_mul_exp_neg_add_div`: the value of the integral.
-/

open Real Set MeasureTheory

namespace MeasureTheory

variable {A T c : ℝ}

private lemma exp_neg_div_le (hT : 0 < T) {y : ℝ} (hy : 0 < y) :
    rexp (-(T / y)) ≤ 2 / T ^ 2 * y ^ 2 := by
  rw [Real.exp_neg, inv_le_comm₀ (exp_pos _) (by positivity)]
  refine le_of_eq_of_le ?_ (Real.pow_div_factorial_le_exp (T / y) (div_pos hT hy).le 2)
  have e : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
  rw [e]
  field_simp

/-- The function `y ^ (-3/2) e^{-A y - T / y}` is integrable on `(0, ∞)` for `A, T > 0`. -/
lemma integrableOn_rpow_neg_mul_exp_neg_add_div (hA : 0 < A) (hT : 0 < T) :
    IntegrableOn (fun y : ℝ ↦ y ^ (-(3 / 2) : ℝ) * rexp (-(A * y) - T / y)) (Ioi 0) := by
  have hg : IntegrableOn (fun y : ℝ ↦ y ^ (1 / 2 : ℝ) * rexp (-(A * y))) (Ioi 0) := by
    simpa only [rpow_one, neg_mul] using integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1 / 2)
      (p := 1) (by norm_num) one_pos hA
  refine Integrable.mono' (hg.const_mul (2 / T ^ 2)) ?_ <|
    (ae_restrict_iff' measurableSet_Ioi).mpr <| .of_forall fun y hy ↦ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun y hy ↦ ContinuousAt.continuousWithinAt ?_)
      measurableSet_Ioi
    have hy' : y ≠ 0 := (mem_Ioi.mp hy).ne'
    exact (continuousAt_rpow_const y _ (Or.inl hy')).mul <| Real.continuous_exp.continuousAt.comp <|
      (by fun_prop (disch := assumption))
  · have hy0 : 0 < y := hy
    have e : rexp (-(A * y) - T / y) = rexp (-(A * y)) * rexp (-(T / y)) := by
      rw [← Real.exp_add]
      congr 1
    have e2 : y ^ (-(3 / 2) : ℝ) * y ^ 2 = y ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hy0]
      norm_num
    have h1 : 0 ≤ y ^ (-(3 / 2) : ℝ) * rexp (-(A * y)) := by positivity
    rw [Real.norm_of_nonneg (by positivity), e, ← mul_assoc, ← e2]
    refine (mul_le_mul_of_nonneg_left (exp_neg_div_le hT hy0) h1).trans_eq ?_
    ring1

private lemma injOn_sub_inv : InjOn (fun p : ℝ ↦ p - p⁻¹) (Ioi 0) := by
  intro p hp q hq h
  have hp0 : 0 < p := hp
  have hq0 : 0 < q := hq
  have h1 : (p - q) * (1 + (p * q)⁻¹) = 0 := by
    have h2 : p - p⁻¹ = q - q⁻¹ := h
    field_simp at h2 ⊢
    linear_combination h2
  rcases mul_eq_zero.mp h1 with h2 | h2
  · linarith
  · have h3 : 0 < (p * q)⁻¹ := by positivity
    linarith

private lemma image_sub_inv : (fun p : ℝ ↦ p - p⁻¹) '' Ioi 0 = univ := by
  refine eq_univ_of_forall fun t ↦ ?_
  have h1 : t ^ 2 + 4 ≥ 0 := by positivity
  have h2 : Real.sqrt (t ^ 2 + 4) ^ 2 = t ^ 2 + 4 := Real.sq_sqrt h1
  have h3 : |t| < Real.sqrt (t ^ 2 + 4) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg t) (by linarith)
  have h4 : 0 < (t + Real.sqrt (t ^ 2 + 4)) / 2 := by
    linarith [neg_abs_le t]
  refine ⟨(t + Real.sqrt (t ^ 2 + 4)) / 2, h4, ?_⟩
  have h5 : ((t + Real.sqrt (t ^ 2 + 4)) / 2)⁻¹ = (Real.sqrt (t ^ 2 + 4) - t) / 2 :=
    inv_eq_of_mul_eq_one_right (by linear_combination (1 / 4) * h2)
  simp only
  rw [h5]
  ring1

private lemma hasDerivWithinAt_sub_inv {p : ℝ} (hp : p ∈ Ioi (0 : ℝ)) :
    HasDerivWithinAt (fun p : ℝ ↦ p - p⁻¹) (1 + (p ^ 2)⁻¹) (Ioi 0) p := by
  have hp0 : p ≠ 0 := (mem_Ioi.mp hp).ne'
  rw [← sub_neg_eq_add]
  exact ((hasDerivAt_id' p).sub (hasDerivAt_inv hp0)).hasDerivWithinAt

private lemma sub_inv_sq {p : ℝ} (hp : 0 < p) : (p - p⁻¹) ^ 2 = p ^ 2 + (p ^ 2)⁻¹ - 2 := by
  field_simp
  ring1

private lemma integrableOn_gauss_sub_inv (hc : 0 < c) :
    IntegrableOn (fun p : ℝ ↦ (1 + (p ^ 2)⁻¹) * rexp (-c * (p - p⁻¹) ^ 2)) (Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ ↦ |1 + (x ^ 2)⁻¹| • rexp (-c * (x - x⁻¹) ^ 2)) (Ioi 0) :=
    (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun p hp ↦ hasDerivWithinAt_sub_inv hp) injOn_sub_inv (fun t : ℝ ↦ rexp (-c * t ^ 2))).mp
        (by rw [image_sub_inv, integrableOn_univ]; exact integrable_exp_neg_mul_sq hc)
  refine h.congr <| (ae_restrict_iff' measurableSet_Ioi).mpr <| .of_forall fun p hp ↦ ?_
  have hp0 : 0 < p := hp
  simp only [smul_eq_mul]
  rw [abs_of_pos (by positivity)]

private lemma integral_gauss_sub_inv :
    ∫ p in Ioi (0 : ℝ), (1 + (p ^ 2)⁻¹) * rexp (-c * (p - p⁻¹) ^ 2) = Real.sqrt (π / c) := by
  have h : ∫ x in (fun p : ℝ ↦ p - p⁻¹) '' Ioi 0, rexp (-c * x ^ 2) =
      ∫ x in Ioi (0 : ℝ), |1 + (x ^ 2)⁻¹| • rexp (-c * (x - x⁻¹) ^ 2) :=
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun p hp ↦ hasDerivWithinAt_sub_inv hp) injOn_sub_inv (fun t : ℝ ↦ rexp (-c * t ^ 2))
  rw [image_sub_inv, setIntegral_univ, integral_gaussian] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun p hp ↦ ?_
  have hp0 : 0 < p := hp
  simp only [smul_eq_mul]
  rw [abs_of_pos (by positivity)]

variable (c) in
/-- The function `e^{-c (p² + p ^ (-2))}`. -/
private noncomputable def gaussInv (p : ℝ) : ℝ :=
  rexp (-c * (p ^ 2 + (p ^ 2)⁻¹))

private lemma gauss_sub_inv_eq {p : ℝ} (hp : 0 < p) :
    rexp (-c * (p - p⁻¹) ^ 2) = rexp (2 * c) * gaussInv c p := by
  rw [gaussInv, ← Real.exp_add, sub_inv_sq hp]
  congr 1
  ring1

private lemma continuousOn_gaussInv : ContinuousOn (gaussInv c) (Ioi 0) := by
  refine fun p hp ↦ ContinuousAt.continuousWithinAt ?_
  have hp0 : p ≠ 0 := (mem_Ioi.mp hp).ne'
  unfold gaussInv
  fun_prop (disch := simp [hp0])

private lemma integrableOn_add_mul_gaussInv (hc : 0 < c) :
    IntegrableOn (fun p : ℝ ↦ (1 + (p ^ 2)⁻¹) * gaussInv c p) (Ioi 0) := by
  refine ((integrableOn_gauss_sub_inv hc).const_mul (rexp (-(2 * c)))).congr <|
    (ae_restrict_iff' measurableSet_Ioi).mpr <| .of_forall fun p hp ↦ ?_
  beta_reduce
  rw [gauss_sub_inv_eq hp]
  have e : rexp (-(2 * c)) * rexp (2 * c) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  linear_combination ((1 + (p ^ 2)⁻¹) * gaussInv c p) * e

private lemma integrableOn_gaussInv (hc : 0 < c) : IntegrableOn (gaussInv c) (Ioi 0) := by
  refine (integrableOn_add_mul_gaussInv hc).mono' (continuousOn_gaussInv.aestronglyMeasurable
    measurableSet_Ioi) <| (ae_restrict_iff' measurableSet_Ioi).mpr <| .of_forall fun p hp ↦ ?_
  have hp0 : 0 < p := hp
  have h1 : 0 < gaussInv c p := Real.exp_pos _
  rw [Real.norm_of_nonneg h1.le]
  have h2 : 0 < (p ^ 2)⁻¹ := by positivity
  nlinarith

private lemma integral_inv_sq_mul_gaussInv :
    ∫ p in Ioi (0 : ℝ), (p ^ 2)⁻¹ * gaussInv c p = ∫ p in Ioi (0 : ℝ), gaussInv c p := by
  rw [← integral_comp_rpow_Ioi (gaussInv c) (p := -1) (by norm_num)]
  refine setIntegral_congr_fun measurableSet_Ioi fun p hp ↦ ?_
  have hp0 : 0 < p := hp
  have e1 : p ^ (-1 - 1 : ℝ) = (p ^ 2)⁻¹ := by
    rw [show (-1 - 1 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hp0.le, Real.rpow_natCast]
  have e2 : gaussInv c (p ^ (-1 : ℝ)) = gaussInv c p := by
    rw [Real.rpow_neg_one, gaussInv, gaussInv, inv_pow, inv_inv, add_comm]
  simp only [smul_eq_mul]
  rw [e1, e2, abs_neg, abs_one, one_mul]

private lemma integral_gaussInv (hc : 0 < c) :
    ∫ p in Ioi (0 : ℝ), gaussInv c p = rexp (-(2 * c)) * Real.sqrt (π / c) / 2 := by
  have h1 : ∫ p in Ioi (0 : ℝ), (1 + (p ^ 2)⁻¹) * gaussInv c p =
      2 * ∫ p in Ioi (0 : ℝ), gaussInv c p := by
    have h2 : IntegrableOn (fun p : ℝ ↦ (p ^ 2)⁻¹ * gaussInv c p) (Ioi 0) := by
      refine ((integrableOn_add_mul_gaussInv hc).sub (integrableOn_gaussInv hc)).congr <|
        .of_forall fun p ↦ ?_
      simp only [Pi.sub_apply]
      ring1
    simp only [add_mul, one_mul]
    rw [integral_add (integrableOn_gaussInv hc) h2, integral_inv_sq_mul_gaussInv]
    ring1
  have h4 :
      ∫ p in Ioi (0 : ℝ), (1 + (p ^ 2)⁻¹) * gaussInv c p = rexp (-(2 * c)) * Real.sqrt (π / c) := by
    rw [← integral_gauss_sub_inv, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun p hp ↦ ?_
    have e : rexp (-(2 * c)) * rexp (2 * c) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [gauss_sub_inv_eq hp]
    linear_combination (-(1 + (p ^ 2)⁻¹) * gaussInv c p) * e
  linarith

/-- **The value of the integral**: for `A, T > 0`,
`∫₀^∞ y ^ (-3/2) e^{-A y - T / y} dy = √(π / T) e^{-2 √(A T)}`. -/
lemma integral_rpow_neg_mul_exp_neg_add_div (hA : 0 < A) (hT : 0 < T) : ∫ y in Ioi (0 : ℝ),
    y ^ (-(3 / 2) : ℝ) * rexp (-(A * y) - T / y) =
      Real.sqrt (π / T) * rexp (-(2 * Real.sqrt (A * T))) := by
  have hc : 0 < Real.sqrt (A * T) := Real.sqrt_pos.mpr (mul_pos hA hT)
  have hr : 0 < Real.sqrt (T / A) := Real.sqrt_pos.mpr (div_pos hT hA)
  have hrc : Real.sqrt (T / A) * Real.sqrt (A * T) = T := by
    rw [← Real.sqrt_mul (div_pos hT hA).le, div_mul_eq_mul_div, mul_comm T, mul_assoc,
      mul_div_cancel_left₀ _ hA.ne', Real.sqrt_mul_self hT.le]
  have hAr : A * Real.sqrt (T / A) = Real.sqrt (A * T) := by
    have h1 : Real.sqrt (A * T) ^ 2 = A * T := Real.sq_sqrt (mul_pos hA hT).le
    have h2 : Real.sqrt (T / A) * Real.sqrt (A * T) * A = T * A := by rw [hrc]
    refine mul_right_cancel₀ hc.ne' ?_
    rw [← sq, h1]
    linear_combination h2
  generalize Real.sqrt (T / A) = r at *
  generalize hC : Real.sqrt (A * T) = c at *
  have key : ∫ x in Ioi (0 : ℝ), 2 * r ^ (-(3 / 2) : ℝ) * ((x ^ 2)⁻¹ * gaussInv c x) =
      ∫ y in Ioi (0 : ℝ), (r * y) ^ (-(3 / 2) : ℝ) * rexp (-(A * (r * y)) - T / (r * y)) := by
    rw [← integral_comp_rpow_Ioi (fun y : ℝ ↦ (r * y) ^ (-(3 / 2) : ℝ) *
      rexp (-(A * (r * y)) - T / (r * y))) (p := 2) (by norm_num)]
    symm
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    have hx0 : 0 < x := hx
    have e1 : x ^ (2 : ℝ) = x ^ 2 := by
      exact_mod_cast Real.rpow_natCast x 2
    have e2 : x ^ ((2 : ℝ) - 1) = x := by
      rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    have e3 : (x ^ 2) ^ (-(3 / 2) : ℝ) = (x ^ 3)⁻¹ := by
      rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx0.le,
        show ((2 : ℕ) : ℝ) * (-(3 / 2)) = -(3 : ℕ) by norm_num, Real.rpow_neg hx0.le,
        Real.rpow_natCast]
    have e4 : -(A * (r * x ^ 2)) - T / (r * x ^ 2) = -c * (x ^ 2 + (x ^ 2)⁻¹) := by
      rw [← hrc]
      have h5 : A * r = c := hAr
      field_simp
      linear_combination (-(x ^ 4)) * h5
    rw [e1, e2, abs_of_pos two_pos, Real.mul_rpow hr.le (by positivity), e3, smul_eq_mul, e4,
      gaussInv]
    field_simp
  rw [integral_const_mul, integral_inv_sq_mul_gaussInv, integral_gaussInv hc,
    integral_comp_mul_left_Ioi (fun y : ℝ ↦ y ^ (-(3 / 2) : ℝ) * rexp (-(A * y) - T / y)) 0 hr,
    mul_zero, smul_eq_mul] at key
  have hrinv : r⁻¹ * r = 1 := inv_mul_cancel₀ hr.ne'
  have h6 : ∫ y in Ioi (0 : ℝ), y ^ (-(3 / 2) : ℝ) * rexp (-(A * y) - T / y) =
      r * (2 * r ^ (-(3 / 2) : ℝ) * (rexp (-(2 * c)) * Real.sqrt (π / c) / 2)) := by
    rw [key, ← mul_assoc, mul_comm r, hrinv, one_mul]
  have h7 : r * r ^ (-(3 / 2) : ℝ) = (Real.sqrt r)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hr.le, ← Real.rpow_one_add' hr.le (by norm_num)]
    norm_num
  have h8 : Real.sqrt (π / T) = Real.sqrt (π / c) * (Real.sqrt r)⁻¹ := by
    rw [← hrc, mul_comm r c, ← div_div, Real.sqrt_div (by positivity) r, div_eq_mul_inv]
  rw [h6, h8]
  linear_combination (rexp (-(2 * c)) * Real.sqrt (π / c)) * h7

end MeasureTheory
