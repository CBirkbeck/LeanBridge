import LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselK
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Derivative and recurrences of the `K`-Bessel function

For `x > 0`, the `K`-Bessel function `K_ν(x) = ½ ∫₀^∞ t^(ν - 1) e^(-(x/2)(t + 1/t)) dt`
(`Complex.besselK`, LMFDB `specialfunction.k_bessel`) is differentiable, with
`K_ν' = -(K_{ν - 1} + K_{ν + 1}) / 2` (differentiation under the integral sign), and satisfies the
recurrence `K_{ν - 1} - K_{ν + 1} = -(2ν / x) K_ν` (integration of the derivative of
`t^ν e^(-(x/2)(t + 1/t))` over `(0, ∞)`). Together they give `K_ν' = -K_{ν + 1} + (ν / x) K_ν =
-K_{ν - 1} - (ν / x) K_ν`, the modified Bessel equation `x² K_ν'' + x K_ν' - (x² + ν²) K_ν = 0`,
and the smoothness of `K_ν` on `(0, ∞)`.

## Main results

* `Complex.hasDerivAt_besselK`: `K_ν'(x) = -(K_{ν - 1}(x) + K_{ν + 1}(x)) / 2`.
* `Complex.besselK_sub_besselK`: `K_{ν - 1}(x) - K_{ν + 1}(x) = -(2ν / x) K_ν(x)`.
* `Complex.hasDerivAt_besselK_eq_add`: `K_ν'(x) = -K_{ν + 1}(x) + (ν / x) K_ν(x)`.
* `Complex.hasDerivAt_besselK_eq_sub`: `K_ν'(x) = -K_{ν - 1}(x) - (ν / x) K_ν(x)`.
* `Complex.besselK_ode`: the modified Bessel equation.
* `Complex.contDiffOn_besselK`: `K_ν` is smooth on `(0, ∞)`.
-/

open Filter MeasureTheory Real Set Topology

open scoped ContDiff

namespace Complex

variable (ν : ℂ) {x t : ℝ}

lemma besselKIntegrand_mul_add_inv (ht : 0 < t) : besselKIntegrand ν x t * ((t + t⁻¹ : ℝ) : ℂ) =
    besselKIntegrand (ν + 1) x t + besselKIntegrand (ν - 1) x t := by
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  simp only [besselKIntegrand, add_sub_cancel_right, cpow_sub _ _ ht', cpow_one]
  push_cast
  field_simp

variable (x t) in
lemma hasDerivAt_besselKIntegrand : HasDerivAt (fun x ↦ besselKIntegrand ν x t)
    (-(((t + t⁻¹) / 2 : ℝ) : ℂ) * besselKIntegrand ν x t) x := by
  have h : HasDerivAt (fun x : ℝ ↦ rexp (-(x / 2) * (t + t⁻¹)))
      (rexp (-(x / 2) * (t + t⁻¹)) * (-(1 / 2) * (t + t⁻¹))) x :=
    (((hasDerivAt_id x).div_const 2).neg.mul_const (t + t⁻¹)).exp.congr_deriv (by simp)
  refine (h.ofReal_comp.const_mul ((t : ℂ) ^ (ν - 1))).congr_deriv ?_
  rw [besselKIntegrand]
  push_cast
  ring1

lemma norm_besselKIntegrand_mul_le (ht : 0 < t) {x₀ : ℝ} (hx : x₀ / 2 < x) :
    ‖-(((t + t⁻¹) / 2 : ℝ) : ℂ) * besselKIntegrand ν x t‖ ≤
      (‖besselKIntegrand (ν + 1) (x₀ / 2) t‖ + ‖besselKIntegrand (ν - 1) (x₀ / 2) t‖) / 2 := by
  have hs : 0 < (t + t⁻¹) / 2 := by positivity
  have e₁ : t ^ ((ν + 1).re - 1) = t ^ (ν.re - 1) * t := by
    rw [← rpow_add_one ht.ne', add_re, one_re]
    congr 1
    ring1
  have e₂ : t ^ ((ν - 1).re - 1) = t ^ (ν.re - 1) * t⁻¹ := by
    rw [← rpow_neg_one, ← rpow_add ht, sub_re, one_re]
    congr 1
  have hE : rexp (-(x / 2) * (t + t⁻¹)) ≤ rexp (-(x₀ / 2 / 2) * (t + t⁻¹)) :=
    exp_le_exp.mpr <| mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rw [norm_mul, norm_neg, norm_real, Real.norm_of_nonneg hs.le, norm_besselKIntegrand _ ht,
    norm_besselKIntegrand _ ht, norm_besselKIntegrand _ ht, e₁, e₂]
  have e : (t ^ (ν.re - 1) * t * rexp (-(x₀ / 2 / 2) * (t + t⁻¹)) +
      t ^ (ν.re - 1) * t⁻¹ * rexp (-(x₀ / 2 / 2) * (t + t⁻¹))) / 2 =
        (t + t⁻¹) / 2 * (t ^ (ν.re - 1) * rexp (-(x₀ / 2 / 2) * (t + t⁻¹))) := by
    ring1
  rw [e]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE (by positivity)) hs.le

/-- **The derivative of the `K`-Bessel function**: `K_ν'(x) = -(K_{ν - 1}(x) + K_{ν + 1}(x)) / 2`
for `x > 0`, by differentiating under the integral sign. -/
lemma hasDerivAt_besselK (hx : 0 < x) :
    HasDerivAt (fun x ↦ besselK ν x) (-(besselK (ν - 1) x + besselK (ν + 1) x) / 2) x := by
  have hint (μ : ℂ) {x' : ℝ} (hx' : 0 < x') :
      Integrable (besselKIntegrand μ x') (volume.restrict (Ioi 0)) :=
    integrableOn_besselKIntegrand μ hx'
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ -(((t + t⁻¹) / 2 : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) :=
    (by fun_prop : Measurable fun t : ℝ ↦ -(((t + t⁻¹) / 2 : ℝ) : ℂ)).aestronglyMeasurable
  have key : HasDerivAt (fun x ↦ ∫ t in Ioi 0, besselKIntegrand ν x t)
      (∫ t in Ioi 0, -(((t + t⁻¹) / 2 : ℝ) : ℂ) * besselKIntegrand ν x t) x :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Ioi_mem_nhds (half_lt_self hx))
      ((eventually_gt_nhds hx).mono fun x' hx' ↦ (hint ν hx').aestronglyMeasurable)
      (hint ν hx) (hmeas.mul (hint ν hx).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).mpr <| .of_forall fun t ht x' hx' ↦
        norm_besselKIntegrand_mul_le ν ht hx')
      (((hint (ν + 1) (half_pos hx)).norm.add (hint (ν - 1) (half_pos hx)).norm).div_const 2)
      (.of_forall fun t x' _ ↦ hasDerivAt_besselKIntegrand ν x' t)).2
  refine (key.const_mul 2⁻¹).congr_deriv ?_
  have e : ∫ t in Ioi 0, -(((t + t⁻¹) / 2 : ℝ) : ℂ) * besselKIntegrand ν x t =
      -(2⁻¹ * ((∫ t in Ioi 0, besselKIntegrand (ν + 1) x t) +
        ∫ t in Ioi 0, besselKIntegrand (ν - 1) x t)) := by
    rw [← integral_add (hint _ hx) (hint _ hx), ← integral_const_mul, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [← besselKIntegrand_mul_add_inv ν ht]
    push_cast
    ring1
  rw [e, besselK, besselK]
  ring1

variable (x t) in
/-- The function `t ↦ t^ν e^(-(x/2)(t + 1/t))`, whose derivative gives the recurrence of the
`K`-Bessel functions. -/
private noncomputable def besselKPrimitive : ℂ :=
  (t : ℂ) ^ ν * (rexp (-(x / 2) * (t + t⁻¹)) : ℂ)

private lemma hasDerivAt_besselKPrimitive (ht : 0 < t) : HasDerivAt (besselKPrimitive ν x)
    (ν * besselKIntegrand ν x t -
      (x / 2 : ℂ) * (besselKIntegrand (ν + 1) x t - besselKIntegrand (ν - 1) x t)) t := by
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have h₁ : HasDerivAt (fun t : ℝ ↦ (t : ℂ) ^ ν) (ν * (t : ℂ) ^ (ν - 1) * 1) t :=
    ((hasDerivAt_id (t : ℂ)).cpow_const (ofReal_mem_slitPlane.mpr ht)).comp_ofReal
  have h₂ : HasDerivAt (fun t : ℝ ↦ rexp (-(x / 2) * (t + t⁻¹)))
      (rexp (-(x / 2) * (t + t⁻¹)) * (-(x / 2) * (1 + -(t ^ 2)⁻¹))) t :=
    (((hasDerivAt_id t).add (hasDerivAt_inv ht.ne')).const_mul (-(x / 2))).exp
  refine (h₁.mul h₂.ofReal_comp).congr_deriv ?_
  simp only [besselKIntegrand, add_sub_cancel_right, cpow_sub _ _ ht', cpow_one]
  push_cast
  field_simp
  ring1

private lemma norm_besselKPrimitive (ht : 0 < t) :
    ‖besselKPrimitive ν x t‖ = t ^ ν.re * rexp (-(x / 2) * (t + t⁻¹)) := by
  rw [besselKPrimitive, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_real,
    Real.norm_of_nonneg (exp_pos _).le]

private lemma tendsto_besselKPrimitive_atTop (hx : 0 < x) :
    Tendsto (besselKPrimitive ν x) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ν.re (x / 2)
    (half_pos hx))
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_besselKPrimitive ν ht]
  refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (rpow_nonneg ht.le _)
  nlinarith [inv_pos.mpr ht]

private lemma tendsto_besselKPrimitive_zero (hx : 0 < x) :
    Tendsto (besselKPrimitive ν x) (𝓝[>] 0) (𝓝 0) := by
  refine squeeze_zero_norm' ?_ ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-ν.re) (x / 2)
    (half_pos hx)).comp tendsto_inv_nhdsGT_zero)
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [norm_besselKPrimitive ν ht, Function.comp_apply, rpow_neg (inv_nonneg.mpr ht.le),
    inv_rpow ht.le, inv_inv]
  refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (rpow_nonneg ht.le _)
  nlinarith [inv_pos.mpr ht]

/-- **The recurrence of the `K`-Bessel functions**: `K_{ν - 1}(x) - K_{ν + 1}(x) = -(2ν / x) K_ν(x)`
for `x > 0`, by integrating the derivative of `t ↦ t^ν e^(-(x/2)(t + 1/t))` over `(0, ∞)`. -/
lemma besselK_sub_besselK (hx : 0 < x) :
    besselK (ν - 1) x - besselK (ν + 1) x = -(2 * ν / x) * besselK ν x := by
  have hint (μ : ℂ) : IntegrableOn (besselKIntegrand μ x) (Ioi 0) :=
    integrableOn_besselKIntegrand μ hx
  have hu' : IntegrableOn (fun t ↦ ν * besselKIntegrand ν x t -
      (x / 2 : ℂ) * (besselKIntegrand (ν + 1) x t - besselKIntegrand (ν - 1) x t)) (Ioi 0) :=
    ((hint ν).const_mul ν).sub (((hint (ν + 1)).sub (hint (ν - 1))).const_mul (x / 2 : ℂ))
  have h : ∫ t in Ioi 0, (ν * besselKIntegrand ν x t -
      (x / 2 : ℂ) * (besselKIntegrand (ν + 1) x t - besselKIntegrand (ν - 1) x t)) = 0 := by
    simpa only [mul_one, mul_zero, add_zero, sub_zero] using
      integral_Ioi_deriv_mul_eq_sub (u := besselKPrimitive ν x) (v := fun _ ↦ (1 : ℂ))
        (v' := fun _ ↦ 0) (a' := 0) (b' := 0) (fun t ht ↦ hasDerivAt_besselKPrimitive ν ht)
        (fun t _ ↦ hasDerivAt_const t 1) (by simpa [Pi.mul_def, Pi.add_def] using hu')
        (by simpa [Pi.mul_def] using tendsto_besselKPrimitive_zero ν hx)
        (by simpa [Pi.mul_def] using tendsto_besselKPrimitive_atTop ν hx)
  have hK (μ : ℂ) : ∫ t in Ioi 0, besselKIntegrand μ x t = 2 * besselK μ x := by
    rw [besselK]
    ring1
  rw [integral_sub (f := fun t ↦ ν * besselKIntegrand ν x t)
    (g := fun t ↦ (x / 2 : ℂ) * (besselKIntegrand (ν + 1) x t - besselKIntegrand (ν - 1) x t))
    ((hint ν).const_mul ν) (((hint (ν + 1)).sub (hint (ν - 1))).const_mul (x / 2 : ℂ)),
    integral_const_mul, integral_const_mul, integral_sub (hint _) (hint _), hK, hK, hK] at h
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  field_simp
  linear_combination h

/-- **The derivative of the `K`-Bessel function, lowering form**:
`K_ν'(x) = -K_{ν + 1}(x) + (ν / x) K_ν(x)` for `x > 0`. -/
lemma hasDerivAt_besselK_eq_add (hx : 0 < x) :
    HasDerivAt (fun x ↦ besselK ν x) (-besselK (ν + 1) x + ν / x * besselK ν x) x := by
  refine (hasDerivAt_besselK ν hx).congr_deriv ?_
  linear_combination (-1 / 2 : ℂ) * besselK_sub_besselK ν hx

/-- **The derivative of the `K`-Bessel function, raising form**:
`K_ν'(x) = -K_{ν - 1}(x) - (ν / x) K_ν(x)` for `x > 0`. -/
lemma hasDerivAt_besselK_eq_sub (hx : 0 < x) :
    HasDerivAt (fun x ↦ besselK ν x) (-besselK (ν - 1) x - ν / x * besselK ν x) x := by
  refine (hasDerivAt_besselK ν hx).congr_deriv ?_
  linear_combination (1 / 2 : ℂ) * besselK_sub_besselK ν hx

/-- **The modified Bessel equation** (LMFDB `specialfunction.k_bessel`):
`x² K_ν''(x) + x K_ν'(x) - (x² + ν²) K_ν(x) = 0` for `x > 0`. -/
lemma besselK_ode (hx : 0 < x) : (x : ℂ) ^ 2 * deriv (deriv fun x ↦ besselK ν x) x +
    x * deriv (fun x ↦ besselK ν x) x - ((x : ℂ) ^ 2 + ν ^ 2) * besselK ν x = 0 := by
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hd : deriv (fun x ↦ besselK ν x) =ᶠ[𝓝 x]
      fun y ↦ -besselK (ν + 1) y + ν / y * besselK ν y :=
    (eventually_gt_nhds hx).mono fun y hy ↦ (hasDerivAt_besselK_eq_add ν hy).deriv
  have h₁ : HasDerivAt (fun y : ℝ ↦ -besselK (ν + 1) y + ν / y * besselK ν y)
      (-(-besselK (ν + 1 - 1) x - (ν + 1) / x * besselK (ν + 1) x) +
        ((0 * x - ν * (1 : ℝ)) / (x : ℂ) ^ 2 * besselK ν x +
          ν / x * (-besselK (ν + 1) x + ν / x * besselK ν x))) x :=
    (hasDerivAt_besselK_eq_sub (ν + 1) hx).neg.add <|
      ((hasDerivAt_const x ν).div (hasDerivAt_id x).ofReal_comp hx').mul
        (hasDerivAt_besselK_eq_add ν hx)
  rw [hd.deriv_eq, h₁.deriv, (hasDerivAt_besselK_eq_add ν hx).deriv, add_sub_cancel_right,
    ofReal_one]
  field_simp
  ring1

private lemma contDiffOn_besselK_nat (n : ℕ) :
    ∀ ν : ℂ, ContDiffOn ℝ n (fun x ↦ besselK ν x) (Ioi 0) := by
  induction n with
  | zero =>
    exact fun ν ↦ contDiffOn_zero.mpr fun x hx ↦
      (hasDerivAt_besselK ν hx).continuousAt.continuousWithinAt
  | succ n ih =>
    intro ν
    refine (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).mpr ⟨fun x hx ↦
      (hasDerivAt_besselK ν hx).differentiableAt.differentiableWithinAt,
        fun h ↦ (WithTop.natCast_ne_top n h).elim, ?_⟩
    exact (((ih (ν - 1)).add (ih (ν + 1))).neg.div_const 2).congr fun x hx ↦
      (hasDerivAt_besselK ν hx).deriv

/-- **The `K`-Bessel function is smooth** on `(0, ∞)`. -/
lemma contDiffOn_besselK : ContDiffOn ℝ ∞ (fun x ↦ besselK ν x) (Ioi 0) :=
  contDiffOn_infty.mpr fun n ↦ contDiffOn_besselK_nat n ν

end Complex
