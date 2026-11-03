import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Entire functions on vertical strips

Analytic facts behind Hecke's and Weil's converse theorems: the bound
`|Γ(s)| ≤ Γ(σ + 2) / (|s| |s + 1|)` for `σ = Re s > 0`, which needs no Stirling formula; the
upgrade, by Phragmén–Lindelöf, of a bound by `1 / |s - a + 1|` on the two edges of a strip to the
whole strip, for a function bounded on the strip; and the resulting comparison of the integrals over
two vertical lines.

## Main results

* `Complex.norm_Gamma_le_Gamma_re`: `|Γ(s)| ≤ Γ(Re s)` for `Re s > 0`.
* `Complex.norm_Gamma_le_div`: `|Γ(s)| ≤ Γ(Re s + 2) / (|s| |s + 1|)` for `Re s > 0`.
* `Complex.norm_mul_abs_im_le_of_strip`: the decay `1 / |t|` on a strip, from its edges.
* `Complex.tendsto_sub_intervalIntegral_vertical`: the shift of a vertical line of integration.
-/

open Asymptotics Complex Filter Topology Set MeasureTheory

open scoped Real

namespace Complex

variable {s : ℂ}

/-- **The Gamma function on a vertical line is largest on the real axis**: `|Γ(s)| ≤ Γ(Re s)` for
`Re s > 0`. -/
lemma norm_Gamma_le_Gamma_re (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Gamma_eq_integral hs, GammaIntegral, Real.Gamma_eq_integral hs]
  refine (norm_integral_le_integral_norm _).trans_eq (setIntegral_congr_fun measurableSet_Ioi ?_)
  intro x hx
  have hx' : (0 : ℝ) < x := hx
  simp only [norm_mul, norm_real, Real.norm_eq_abs, Real.abs_exp,
    norm_cpow_eq_rpow_re_of_pos hx', sub_re, one_re]

/-- **The decay of the Gamma function on a vertical line**, in the weak form that integrability
needs: `|Γ(s)| ≤ Γ(Re s + 2) / (|s| |s + 1|)` for `Re s > 0`. -/
lemma norm_Gamma_le_div (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma (s.re + 2) / (‖s‖ * ‖s + 1‖) := by
  have h0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  have h1 : s + 1 ≠ 0 := fun h ↦ by
    have h2 : (s + 1).re = 0 := by simp [h]
    simp only [add_re, one_re] at h2
    linarith
  have h2 : Gamma (s + 2) = (s + 1) * (s * Gamma s) := by
    have h3 : s + 2 = s + 1 + 1 := by ring1
    rw [h3, Gamma_add_one _ h1, Gamma_add_one _ h0]
  have h3 : ‖Gamma (s + 2)‖ ≤ Real.Gamma (s.re + 2) := by
    have h4 : ‖Gamma (s + 2)‖ ≤ Real.Gamma (s + 2).re :=
      norm_Gamma_le_Gamma_re (by simp only [add_re, re_ofNat]; linarith)
    simpa using h4
  rw [le_div_iff₀ (mul_pos (norm_pos_iff.mpr h0) (norm_pos_iff.mpr h1))]
  rw [h2, norm_mul, norm_mul] at h3
  linarith

variable {Λ H : ℂ → ℂ} {a b M C K : ℝ}

lemma integrable_vertical_of_decay {σ : ℝ} (hΛ : Continuous fun t : ℝ ↦ Λ (σ + t * I))
    (hdec : ∀ s : ℂ, s.re = σ → ‖Λ s‖ ≤ K / (1 + s.im ^ 2)) :
    Integrable fun t : ℝ ↦ Λ (σ + t * I) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul K) hΛ.aestronglyMeasurable
    (Eventually.of_forall fun t ↦ ?_)
  have h3 : ‖Λ (σ + t * I)‖ ≤ K / (1 + (σ + t * I : ℂ).im ^ 2) := hdec (σ + t * I) (by simp)
  simpa [div_eq_mul_inv] using h3

private lemma norm_sub_add_one_sq : ‖s - a + 1‖ ^ 2 = (s.re - a + 1) ^ 2 + s.im ^ 2 := by
  rw [← normSq_eq_norm_sq, normSq_apply]
  simp only [add_re, sub_re, ofReal_re, one_re, add_im, sub_im, ofReal_im, one_im]
  ring1

private lemma comp_bound (h1 : a ≤ s.re) (h2 : s.re ≤ b) :
    ‖s - a + 1‖ ^ 2 ≤ ((b - a + 1) ^ 2 + 1) * (1 + s.im ^ 2) := by
  have h4 : (s.re - a + 1) ^ 2 ≤ (b - a + 1) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  rw [norm_sub_add_one_sq]
  nlinarith [sq_nonneg s.im, sq_nonneg (b - a + 1)]

lemma norm_sub_add_one_mul_le {x : ℝ} (h1 : a ≤ s.re) (h2 : s.re ≤ b) (h0 : 0 ≤ x)
    (hx : x ≤ K / (1 + s.im ^ 2)) : ‖s - a + 1‖ * x ≤ ((b - a + 1) ^ 2 + 1) * K := by
  have h3 : ‖s - a + 1‖ ^ 2 ≤ ((b - a + 1) ^ 2 + 1) * (1 + s.im ^ 2) := comp_bound h1 h2
  have h4 : 1 + s.im ^ 2 ≤ ‖s - a + 1‖ ^ 2 := by
    rw [norm_sub_add_one_sq]
    nlinarith [sq_nonneg s.im]
  have h5 : 1 ≤ ‖s - a + 1‖ :=
    (one_le_sq_iff₀ (norm_nonneg _)).mp (by nlinarith [sq_nonneg s.im])
  have h6 : x * (1 + s.im ^ 2) ≤ K := (le_div_iff₀ (by positivity)).mp hx
  have h7 : ‖s - a + 1‖ ≤ ((b - a + 1) ^ 2 + 1) * (1 + s.im ^ 2) := by nlinarith
  refine (mul_le_mul_of_nonneg_right h7 h0).trans ?_
  have h8 : 0 ≤ (b - a + 1) ^ 2 + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h6 h8]

private lemma one_add_sq_le_norm_exp_exp {c : ℝ} (hc : 0 < c) (t : ℝ) :
    1 + t ^ 2 ≤ 2 * ‖Real.exp (1 / c * Real.exp (c * |t|))‖ := by
  have h1 : 1 + |t| + |t| ^ 2 / 2 ≤ Real.exp |t| := Real.quadratic_le_exp_of_nonneg (abs_nonneg t)
  have h2 : Real.exp |t| ≤ Real.exp (1 / c * Real.exp (c * |t|)) := by
    refine Real.exp_le_exp.mpr ?_
    have h3 : c * |t| + 1 ≤ Real.exp (c * |t|) := Real.add_one_le_exp (c * |t|)
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hc]
    nlinarith
  rw [sq_abs] at h1
  rw [Real.norm_eq_abs, Real.abs_exp]
  nlinarith [abs_nonneg t]

/-- **Phragmén–Lindelöf for the decay on a vertical strip**: if `Λ` is entire and bounded on the
strip `a ≤ Re s ≤ b` and `|s - a + 1| |Λ(s)| ≤ C` on its two edges, then `|Λ(s)| |Im s| ≤ C` on the
strip. -/
lemma norm_mul_abs_im_le_of_strip (hΛ : Differentiable ℂ Λ) (hab : a < b)
    (hM : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Λ s‖ ≤ M)
    (ha : ∀ s : ℂ, s.re = a → ‖s - a + 1‖ * ‖Λ s‖ ≤ C)
    (hb : ∀ s : ℂ, s.re = b → ‖s - a + 1‖ * ‖Λ s‖ ≤ C) (h1 : a ≤ s.re) (h2 : s.re ≤ b) :
    ‖Λ s‖ * |s.im| ≤ C := by
  have hdiff : Differentiable ℂ fun s : ℂ ↦ (s - a + 1) * Λ s := by fun_prop
  have hba : 0 < b - a := sub_pos.mpr hab
  have hc : 0 < π / (2 * (b - a)) := by positivity
  have hgrow : ∀ z : ℂ, z ∈ re ⁻¹' Ioo a b → ‖(z - a + 1) * Λ z‖ ≤ ((b - a + 1) ^ 2 + 2) * |M| * 2 *
      ‖Real.exp (1 / (π / (2 * (b - a))) * Real.exp (π / (2 * (b - a)) * |z.im|))‖ := fun z hz ↦ by
    have h3 : ‖z - a + 1‖ ^ 2 ≤ ((b - a + 1) ^ 2 + 1) * (1 + z.im ^ 2) := comp_bound hz.1.le hz.2.le
    have h4 : ‖z - a + 1‖ ≤ ((b - a + 1) ^ 2 + 2) * (1 + z.im ^ 2) := by
      nlinarith [sq_nonneg (‖z - a + 1‖ - 1), sq_nonneg z.im, sq_nonneg (b - a + 1)]
    have h5 : ‖Λ z‖ ≤ |M| := (hM z hz.1.le hz.2.le).trans (le_abs_self M)
    have h6 : 1 + z.im ^ 2 ≤
        2 * ‖Real.exp (1 / (π / (2 * (b - a))) * Real.exp (π / (2 * (b - a)) * |z.im|))‖ :=
      one_add_sq_le_norm_exp_exp hc z.im
    rw [norm_mul]
    refine (mul_le_mul h4 h5 (norm_nonneg _) (by positivity)).trans ?_
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h6 (by positivity))
      (abs_nonneg M)).trans_eq (by ring1)
  have h3 : ‖(s - a + 1) * Λ s‖ ≤ C :=
    PhragmenLindelof.vertical_strip (f := fun s : ℂ ↦ (s - a + 1) * Λ s) hdiff.diffContOnCl
      ⟨π / (2 * (b - a)), div_lt_div_of_pos_left Real.pi_pos hba (by linarith),
        1 / (π / (2 * (b - a))), IsBigO.of_bound _
          (eventually_inf_principal.mpr (Eventually.of_forall hgrow))⟩
      (fun z hz ↦ (norm_mul _ _).trans_le (ha z hz)) (fun z hz ↦ (norm_mul _ _).trans_le (hb z hz))
      h1 h2
  have h4 : |(s - a + 1).im| ≤ ‖s - a + 1‖ := abs_im_le_norm _
  have h5 : (s - a + 1).im = s.im := by simp
  rw [h5] at h4
  rw [norm_mul] at h3
  exact (mul_le_mul_of_nonneg_left h4 (norm_nonneg _)).trans (by rwa [mul_comm])

private lemma smul_sub_intervalIntegral_vertical (hH : Differentiable ℂ H) (T : ℝ) : I •
    ((∫ t : ℝ in -T..T, H (b + t * I)) - ∫ t : ℝ in -T..T, H (a + t * I)) =
      (∫ x : ℝ in a..b, H (x + T * I)) - ∫ x : ℝ in a..b, H (x + (-T : ℝ) * I) := by
  simp only [smul_sub]
  linear_combination (norm := skip)
    integral_boundary_rect_eq_zero_of_differentiableOn H ⟨a, -T⟩ ⟨b, T⟩ hH.differentiableOn
  ring1

/-- **The shift of a vertical line of integration.** If `H` is entire with `|H(s)| |Im s| ≤ C` on
the strip `a ≤ Re s ≤ b`, the integrals of `H` over the lines `Re s = a` and `Re s = b`, truncated
at height `T`, differ by a quantity tending to `0`. -/
lemma tendsto_sub_intervalIntegral_vertical (hH : Differentiable ℂ H) (hab : a ≤ b)
    (hdecay : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖H s‖ * |s.im| ≤ C) : Tendsto
      (fun T : ℝ ↦ (∫ t : ℝ in -T..T, H (b + t * I)) - ∫ t : ℝ in -T..T, H (a + t * I)) atTop
        (𝓝 0) := by
  have hhor : ∀ T : ℝ, T ≠ 0 → ‖∫ x : ℝ in a..b, H (x + T * I)‖ ≤ |C| / |T| * (b - a) := by
    intro T hT
    have h1 : ‖∫ x : ℝ in a..b, H (x + T * I)‖ ≤ |C| / |T| * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦ by
        rw [uIoc_of_le hab] at hx
        have h3 : ‖H (x + T * I)‖ * |(x + T * I : ℂ).im| ≤ C :=
          hdecay _ (by simpa using hx.1.le) (by simpa using hx.2)
        have h4 : (x + T * I : ℂ).im = T := by simp
        rw [h4] at h3
        exact (le_div_iff₀ (abs_pos.mpr hT)).mpr (h3.trans (le_abs_self C))
    rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at h1
  have hnorm : ∀ z : ℂ, ‖z‖ = ‖I • z‖ := fun z ↦ by
    rw [norm_smul, norm_I, one_mul]
  have hlim : Tendsto (fun T : ℝ ↦ 2 * (|C| / T * (b - a))) atTop (𝓝 0) := by
    simpa using ((tendsto_id.const_div_atTop |C|).mul_const (b - a)).const_mul 2
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with T hT
  have h1 : ‖∫ x : ℝ in a..b, H (x + T * I)‖ ≤ |C| / |T| * (b - a) := hhor T hT.ne'
  have h2 : ‖∫ x : ℝ in a..b, H (x + (-T : ℝ) * I)‖ ≤ |C| / |-T| * (b - a) :=
    hhor (-T) (neg_ne_zero.mpr hT.ne')
  rw [abs_neg] at h2
  rw [abs_of_pos hT] at h1 h2
  rw [hnorm, smul_sub_intervalIntegral_vertical hH]
  exact (norm_sub_le _ _).trans (by linarith)

end Complex
