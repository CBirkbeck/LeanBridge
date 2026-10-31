import LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselKRecurrence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The decaying solution of the modified Bessel equation

For real `ν`, the modified Bessel equation `x² u'' + x u' - (x² + ν²) u = 0` on `(0, ∞)` has a
two-dimensional space of solutions, in which the `K`-Bessel function `K_ν` (`Complex.besselK`,
LMFDB `specialfunction.k_bessel`) is, up to a scalar, the only solution of at most polynomial growth
at `∞`: the other solutions grow exponentially, like the `I`-Bessel function. This is the scalar
part of the uniqueness of the Fourier–Bessel (Whittaker) functions of Bianchi modular forms. The
proof uses the Wronskian `x (u K_ν' - u' K_ν)`, which is constant along the solutions (Abel), and
the exponential decay of `K_ν` and `K_ν'`.

## Main results

* `Complex.norm_besselK_le`: `|K_ν(x)| ≤ e^{-(x-1)} · ½ ∫₀^∞ |t^(ν - 1) e^(-(t + 1/t)/2)| dt`
  (that is `e^{-(x-1)} K_{Re ν}(1)`) for `x ≥ 1`.
* `Complex.besselK_ofReal_ne_zero`: `K_ν(x) ≠ 0` for real `ν` and `x > 0`.
* `Complex.eq_div_mul_besselK_of_ode`: a solution of polynomial growth is `u(1) / K_ν(1) · K_ν`.
-/

open Filter MeasureTheory Real Set Topology

namespace Complex

variable (ν : ℂ) {x : ℝ}

/-- **The `K`-Bessel function decays exponentially**: for `x ≥ 1`,
`|K_ν(x)| ≤ e^{-(x-1)} · ½ ∫₀^∞ |t^(ν - 1) e^(-(t + 1/t)/2)| dt`, as `t + 1/t ≥ 2`. -/
lemma norm_besselK_le (hx : 1 ≤ x) :
    ‖besselK ν x‖ ≤ rexp (-(x - 1)) * (2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand ν 1 t‖) := by
  have hint : Integrable (fun t ↦ ‖besselKIntegrand ν 1 t‖) (volume.restrict (Ioi 0)) :=
    (integrableOn_besselKIntegrand ν one_pos).norm
  have h : ‖∫ t in Ioi 0, besselKIntegrand ν x t‖ ≤
      ∫ t in Ioi 0, rexp (-(x - 1)) * ‖besselKIntegrand ν 1 t‖ := by
    refine norm_integral_le_of_norm_le (hint.const_mul _) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t (ht : 0 < t) ↦ ?_)
    rw [norm_besselKIntegrand ν ht, norm_besselKIntegrand ν ht, ← mul_assoc,
      mul_comm (rexp _), mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (rpow_nonneg ht.le _)
    have h2 : 2 ≤ t + t⁻¹ := by
      have e : t + t⁻¹ - 2 = (t - 1) ^ 2 / t := by
        field_simp
        ring1
      have hq : 0 ≤ (t - 1) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
      linarith
    nlinarith
  rw [besselK, norm_mul, integral_const_mul] at *
  simp only [norm_inv, RCLike.norm_ofNat] at *
  nlinarith [norm_nonneg (∫ t in Ioi 0, besselKIntegrand ν x t), exp_pos (-(x - 1))]

/-- **The `K`-Bessel function of real order has no zero**: `K_r(x) ≠ 0` for real `r` and `x > 0`,
as the integrand of `K_r(x)` is positive. -/
lemma besselK_ofReal_ne_zero (r : ℝ) (hx : 0 < x) : besselK (r : ℂ) x ≠ 0 := by
  have h : ∀ t ∈ Ioi (0 : ℝ), besselKIntegrand (r : ℂ) x t =
      ((t ^ (r - 1) * rexp (-(x / 2) * (t + t⁻¹)) : ℝ) : ℂ) := by
    intro t ht
    rw [besselKIntegrand, ofReal_mul, ofReal_cpow (mem_Ioi.mp ht).le, ofReal_sub, ofReal_one]
  have hint : IntegrableOn (fun t : ℝ ↦ t ^ (r - 1) * rexp (-(x / 2) * (t + t⁻¹))) (Ioi 0) :=
    IntegrableOn.congr_fun (f := fun t ↦ ‖besselKIntegrand (r : ℂ) x t‖)
      (integrableOn_besselKIntegrand (r : ℂ) hx).norm
      (fun t ht ↦ by
        simp only
        rw [norm_besselKIntegrand _ (mem_Ioi.mp ht), ofReal_re]) measurableSet_Ioi
  have hpos : 0 < ∫ t in Ioi 0, t ^ (r - 1) * rexp (-(x / 2) * (t + t⁻¹)) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t (ht : 0 < t) ↦
        (mul_pos (rpow_pos_of_pos ht _) (exp_pos _)).le)) hint]
    have hs : Function.support (fun t : ℝ ↦ t ^ (r - 1) * rexp (-(x / 2) * (t + t⁻¹))) ∩ Ioi 0 =
        Ioi 0 :=
      inter_eq_right.mpr fun t (ht : 0 < t) ↦ (mul_pos (rpow_pos_of_pos ht _) (exp_pos _)).ne'
    rw [hs, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  rw [besselK, setIntegral_congr_fun measurableSet_Ioi h, integral_complex_ofReal]
  exact mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr hpos.ne')

lemma hasDerivAt_neg_besselK_add (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ -besselK (ν + 1) y + ν / y * besselK ν y)
      (besselK ν x + besselK (ν + 1) x / x + (ν ^ 2 - ν) / (x : ℂ) ^ 2 * besselK ν x) x := by
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  refine ((hasDerivAt_besselK_eq_sub (ν + 1) hx).neg.add <|
    ((hasDerivAt_const x ν).div (hasDerivAt_id x).ofReal_comp hx').mul
      (hasDerivAt_besselK_eq_add ν hx)).congr_deriv ?_
  simp only [add_sub_cancel_right, Pi.div_apply, id, ofReal_one]
  field_simp
  ring1

variable {u u' u'' : ℝ → ℂ}

/-- **The decaying solution of the modified Bessel equation is `K_ν`**: for real `ν`, a solution
`u` of `x² u'' + x u' - (x² + ν²) u = 0` on `(0, ∞)` which grows at most polynomially at `∞`,
with its derivative, is the multiple `u(1) / K_ν(1) · K_ν` of the `K`-Bessel function. The
Wronskian `x (u K_ν' - u' K_ν)` is constant (Abel) and tends to `0` at `∞` (`K_ν` and `K_ν'` decay
exponentially, `norm_besselK_le`), so it vanishes and `u / K_ν` is constant (`K_ν` has no zero,
`besselK_ofReal_ne_zero`). -/
lemma eq_div_mul_besselK_of_ode (r : ℝ) (hu : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    (hu' : ∀ x, 0 < x → HasDerivAt u' (u'' x) x)
    (hode : ∀ x : ℝ, 0 < x → (x : ℂ) ^ 2 * u'' x + x * u' x - ((x : ℂ) ^ 2 + (r : ℂ) ^ 2) * u x = 0)
    {C : ℝ} {N : ℕ} (hu₁ : ∀ x, 1 ≤ x → ‖u x‖ ≤ C * x ^ N)
    (hu₂ : ∀ x, 1 ≤ x → ‖u' x‖ ≤ C * x ^ N) (hx : 0 < x) :
    u x = u 1 / besselK r 1 * besselK r x := by
  have hK (y : ℝ) (hy : 0 < y) : HasDerivAt (fun y : ℝ ↦ besselK (r : ℂ) y)
      (-besselK ((r : ℂ) + 1) y + (r : ℂ) / y * besselK (r : ℂ) y) y :=
    hasDerivAt_besselK_eq_add r hy
  let W : ℝ → ℂ := fun y ↦ (y : ℂ) * (u y * (-besselK ((r : ℂ) + 1) y +
    (r : ℂ) / y * besselK (r : ℂ) y) - u' y * besselK (r : ℂ) y)
  have hW (y : ℝ) (hy : 0 < y) : HasDerivAt W 0 y := by
    have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
    refine ((hasDerivAt_id y).ofReal_comp.mul (((hu y hy).mul
      (hasDerivAt_neg_besselK_add r hy)).sub ((hu' y hy).mul (hK y hy)))).congr_deriv ?_
    refine mul_left_cancel₀ hy' ?_
    simp only [Pi.mul_apply, Pi.sub_apply, id, ofReal_one]
    field_simp
    linear_combination (-besselK (r : ℂ) y) * hode y hy
  have hconst (y : ℝ) (hy : 0 < y) : W y = W 1 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun z hz ↦ (hW z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hW z hz).deriv) hy (mem_Ioi.mpr one_pos)
  have hC : 0 ≤ C := by
    have h : ‖u 1‖ ≤ C * 1 ^ N := hu₁ 1 le_rfl
    rw [one_pow, mul_one] at h
    exact (norm_nonneg _).trans h
  have hB (μ : ℂ) : 0 ≤ 2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand μ 1 t‖ :=
    mul_nonneg (by norm_num) (integral_nonneg fun _ ↦ norm_nonneg _)
  have hbound (y : ℝ) (hy : 1 ≤ y) : ‖W y‖ ≤ C * ((2⁻¹ * ∫ t in Ioi 0,
      ‖besselKIntegrand ((r : ℂ) + 1) 1 t‖) + |r| * (2⁻¹ * ∫ t in Ioi 0,
        ‖besselKIntegrand (r : ℂ) 1 t‖) + 2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand (r : ℂ) 1 t‖) *
          rexp 1 * (y ^ (N + 1) * rexp (-y)) := by
    have hy₀ : 0 < y := by
      linarith
    have h₀ : ‖besselK (r : ℂ) y‖ ≤
        rexp (-(y - 1)) * (2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand (r : ℂ) 1 t‖) :=
      norm_besselK_le (r : ℂ) hy
    have h₁ : ‖besselK ((r : ℂ) + 1) y‖ ≤
        rexp (-(y - 1)) * (2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand ((r : ℂ) + 1) 1 t‖) :=
      norm_besselK_le ((r : ℂ) + 1) hy
    have hr : ‖(r : ℂ) / y‖ ≤ |r| := by
      rw [norm_div, norm_real, norm_real, Real.norm_of_nonneg hy₀.le, Real.norm_eq_abs]
      exact div_le_self (abs_nonneg r) hy
    have hd : ‖-besselK ((r : ℂ) + 1) y + (r : ℂ) / y * besselK (r : ℂ) y‖ ≤
        rexp (-(y - 1)) * ((2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand ((r : ℂ) + 1) 1 t‖) +
          |r| * (2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand (r : ℂ) 1 t‖)) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, norm_mul]
      nlinarith [mul_le_mul hr h₀ (norm_nonneg _) (abs_nonneg r)]
    have hW' : ‖W y‖ ≤ y * (C * y ^ N * (rexp (-(y - 1)) *
        ((2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand ((r : ℂ) + 1) 1 t‖) +
          |r| * (2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand (r : ℂ) 1 t‖))) + C * y ^ N *
            (rexp (-(y - 1)) * (2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand (r : ℂ) 1 t‖))) := by
      simp only [W]
      rw [norm_mul, norm_real, Real.norm_of_nonneg hy₀.le]
      refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) hy₀.le
      rw [norm_mul, norm_mul]
      gcongr
      · exact hu₁ y hy
      · exact hu₂ y hy
    have he : rexp (-(y - 1)) = rexp 1 * rexp (-y) := by
      rw [← Real.exp_add]
      congr 1
      ring1
    rw [he] at hW'
    refine hW'.trans (le_of_eq ?_)
    ring1
  have hlim : Tendsto W atTop (𝓝 0) := by
    refine squeeze_zero_norm' ((eventually_ge_atTop 1).mono hbound) ?_
    simpa using (tendsto_pow_mul_exp_neg_atTop_nhds_zero (N + 1)).const_mul
      (C * ((2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand ((r : ℂ) + 1) 1 t‖) +
        |r| * (2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand (r : ℂ) 1 t‖) +
          2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand (r : ℂ) 1 t‖) * rexp 1)
  have hW₁ : W 1 = 0 := tendsto_nhds_unique (tendsto_const_nhds.congr'
    ((eventually_gt_atTop 0).mono fun y hy ↦ (hconst y hy).symm)) hlim
  have hR (y : ℝ) (hy : 0 < y) : HasDerivAt (fun y ↦ u y / besselK (r : ℂ) y) 0 y := by
    have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
    have hWy : W y = 0 := (hconst y hy).trans hW₁
    have hw : u y * (-besselK ((r : ℂ) + 1) y + (r : ℂ) / y * besselK (r : ℂ) y) -
        u' y * besselK (r : ℂ) y = 0 :=
      (mul_eq_zero.mp hWy).resolve_left hy'
    refine ((hu y hy).div (hK y hy) (besselK_ofReal_ne_zero r hy)).congr_deriv ?_
    rw [div_eq_zero_iff]
    exact Or.inl (by linear_combination -hw)
  have hRc : u x / besselK (r : ℂ) x = u 1 / besselK (r : ℂ) 1 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun z hz ↦ (hR z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hR z hz).deriv) hx (mem_Ioi.mpr one_pos)
  rw [← hRc, div_mul_cancel₀ _ (besselK_ofReal_ne_zero r hx)]

end Complex
