import LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselK

/-!
# A lower bound for the `K`-Bessel function

For every order `ν ∈ ℂ`, the `K`-Bessel function (LMFDB `specialfunction.k_bessel`) decays exactly
exponentially, `K_ν(x) ~ √(π / 2x) e^{-x}` as `x → ∞`. This file proves the lower half of this in
the weak form `|K_ν(x)| ≥ e^{-2x}` for all large `x`; the upper bound `|K_ν(x)| ≤ C e^{-x}` is
`Complex.norm_besselK_le`.

In `K_ν(x) = ½ ∫₀^∞ t^{ν-1} e^{-(x/2)(t + 1/t)} dt` the mass concentrates near `t = 1` as `x` grows,
where `t^{ν-1}` is close to `1`. On an interval `[1 - δ, 1 + δ]` the real part of `t^{ν-1}` is at
least `1/2`, and the integrand is at least `½ e^{-x(1 + δ²/6)}` on `[1 - δ/2, 1 + δ/2]`, as
`t + 1/t ≤ 2 + δ²/3` there. Off `[1 - δ, 1 + δ]`, `t + 1/t ≥ 2 + 2δ²/3`, so the rest of the integral
is at most a constant times `e^{-x(1 + δ²/3)}`, which is negligible.

## Main results

* `Complex.eventually_exp_le_norm_besselK`: `e^{-2x} ≤ |K_ν(x)|` for all large `x`.
-/

open Filter MeasureTheory Real Set Topology

namespace Complex

variable (ν : ℂ) {t δ : ℝ}

private lemma two_add_le_add_inv (hδ₀ : 0 < δ) (hδ : δ ≤ 1 / 2) (ht : 0 < t) (htδ : δ < |t - 1|) :
    2 + 2 * δ ^ 2 / 3 ≤ t + t⁻¹ := by
  have e : t + t⁻¹ - (2 + 2 * δ ^ 2 / 3) = (t ^ 2 + 1 - (2 + 2 * δ ^ 2 / 3) * t) / t := by
    field_simp
  rw [← sub_nonneg, e]
  refine div_nonneg ?_ ht.le
  rcases lt_abs.mp htδ with h | h
  · have h1 : 0 ≤ t - 1 + δ - 2 * δ ^ 2 / 3 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h.le) h1,
      mul_nonneg (sq_nonneg δ) (by linarith : (0 : ℝ) ≤ 1 - 2 * δ)]
  · nlinarith [mul_nonneg (sq_nonneg δ) (by linarith : (0 : ℝ) ≤ 1 - t)]

private lemma add_inv_le_two_add (hδ : δ ≤ 1 / 2) (ht : |t - 1| ≤ δ / 2) :
    t + t⁻¹ ≤ 2 + δ ^ 2 / 3 := by
  rcases abs_le.mp ht with ⟨h1, h2⟩
  have ht0 : 0 < t := by linarith
  have e : 2 + δ ^ 2 / 3 - (t + t⁻¹) = ((2 + δ ^ 2 / 3) * t - t ^ 2 - 1) / t := by
    field_simp
    ring1
  rw [← sub_nonneg, e]
  refine div_nonneg ?_ ht0.le
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ δ / 2 - (t - 1))
    (by linarith : (0 : ℝ) ≤ δ / 2 + (t - 1)),
    mul_nonneg (sq_nonneg δ) (by linarith : (0 : ℝ) ≤ t - 3 / 4)]

/-- **The `K`-Bessel function is at least `e^{-2x}` at large `x`**: for every order `ν ∈ ℂ`,
`e^{-2x} ≤ |K_ν(x)|` for all large `x`. -/
lemma eventually_exp_le_norm_besselK : ∀ᶠ x in atTop, rexp (-(2 * x)) ≤ ‖besselK ν x‖ := by
  rcases Metric.continuousAt_iff.mp (continuousAt_ofReal_cpow_const 1 (ν - 1)
    (Or.inr one_ne_zero)) (1 / 2) (by norm_num) with ⟨ε, hε, hεc⟩
  set δ : ℝ := min (ε / 2) (1 / 2)
  have hδ₀ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδ₁ : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hre {t : ℝ} (ht : |t - 1| ≤ δ) : 1 / 2 ≤ ((t : ℂ) ^ (ν - 1)).re := by
    have h : dist ((t : ℂ) ^ (ν - 1)) (((1 : ℝ) : ℂ) ^ (ν - 1)) < 1 / 2 :=
      hεc (by rw [Real.dist_eq]; exact ht.trans_lt hδε)
    rw [ofReal_one, one_cpow, dist_eq] at h
    have h2 : |((t : ℂ) ^ (ν - 1) - 1).re| ≤ ‖(t : ℂ) ^ (ν - 1) - 1‖ := abs_re_le_norm _
    rw [sub_re, one_re] at h2
    linarith [(abs_le.mp (h2.trans h.le)).1]
  have hre₀ {t : ℝ} (ht : |t - 1| ≤ δ) : 0 ≤ ((t : ℂ) ^ (ν - 1)).re :=
    (hre ht).trans' (by norm_num)
  set c : ℝ := δ ^ 2 / 6 with hc_def
  have hc₀ : 0 < c := by positivity
  have hc₁ : 0 < 1 - c := by nlinarith
  set J : ℝ := ∫ t in Ioi 0, ‖besselKIntegrand ν 1 t‖
  have hI : Icc (1 - δ) (1 + δ) ⊆ Ioi (0 : ℝ) := fun t ht ↦ mem_Ioi.mpr (by linarith [ht.1])
  have hI' : Icc (1 - δ / 2) (1 + δ / 2) ⊆ Icc (1 - δ) (1 + δ) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hmain (x : ℝ) (hx : 1 ≤ x) :
      δ / 2 * rexp (-(x * (1 + c))) - J * rexp (-((x - 1) * (1 + 2 * c))) ≤ 2 * ‖besselK ν x‖ := by
    have hint : IntegrableOn (besselKIntegrand ν x) (Ioi 0) :=
      integrableOn_besselKIntegrand ν (by linarith)
    have hint1 : IntegrableOn (fun t ↦ ‖besselKIntegrand ν 1 t‖) (Ioi 0) :=
      (integrableOn_besselKIntegrand ν one_pos).norm
    have hre_int : IntegrableOn (fun t ↦ (besselKIntegrand ν x t).re) (Ioi 0) := by
      simpa only [RCLike.re_to_complex] using hint.re
    have h2K : 2 * ‖besselK ν x‖ = ‖∫ t in Ioi 0, besselKIntegrand ν x t‖ := by
      rw [besselK, norm_mul, norm_inv, RCLike.norm_ofNat, ← mul_assoc,
        mul_inv_cancel₀ two_ne_zero, one_mul]
    have hreK :
        (∫ t in Ioi 0, besselKIntegrand ν x t).re = ∫ t in Ioi 0, (besselKIntegrand ν x t).re := by
      simpa only [RCLike.re_to_complex] using (integral_re hint).symm
    rw [h2K]
    refine (re_le_norm _).trans' ?_
    rw [hreK, ← integral_inter_add_sdiff measurableSet_Icc hre_int, inter_eq_right.mpr hI]
    have hpart₁ : δ / 2 * rexp (-(x * (1 + c))) ≤
        ∫ t in Icc (1 - δ) (1 + δ), (besselKIntegrand ν x t).re := by
      have hnn :
          0 ≤ᵐ[volume.restrict (Icc (1 - δ) (1 + δ))] fun t ↦ (besselKIntegrand ν x t).re := by
        refine (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun t ht ↦ ?_)
        simp only [besselKIntegrand, re_mul_ofReal]
        exact mul_nonneg (hre₀ <| abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
          (exp_pos _).le
      refine (setIntegral_mono_set (hre_int.mono_set hI) hnn (Eventually.of_forall hI')).trans' ?_
      have hconst : ∫ _ in Icc (1 - δ / 2) (1 + δ / 2), (1 / 2 * rexp (-(x * (1 + c))) : ℝ) =
          δ / 2 * rexp (-(x * (1 + c))) := by
        rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul,
          max_eq_left (by linarith : (0 : ℝ) ≤ 1 + δ / 2 - (1 - δ / 2))]
        ring1
      rw [← hconst]
      refine setIntegral_mono_on (integrableOn_const (by simp)) (hre_int.mono_set (hI'.trans hI))
        measurableSet_Icc fun t ht ↦ ?_
      have h1 : |t - 1| ≤ δ / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have h1' : |t - 1| ≤ δ := h1.trans (by linarith)
      rw [besselKIntegrand, re_mul_ofReal]
      refine mul_le_mul (hre h1') (exp_le_exp.mpr ?_) (exp_pos _).le (hre₀ h1')
      have h2 : t + t⁻¹ ≤ 2 + δ ^ 2 / 3 := add_inv_le_two_add hδ₁ h1
      nlinarith
    have hpart₂ : -(J * rexp (-((x - 1) * (1 + 2 * c)))) ≤
        ∫ t in Ioi 0 \ Icc (1 - δ) (1 + δ), (besselKIntegrand ν x t).re := by
      have hsub : Ioi (0 : ℝ) \ Icc (1 - δ) (1 + δ) ⊆ Ioi 0 := sdiff_subset
      have hle : ∫ t in Ioi 0 \ Icc (1 - δ) (1 + δ), ‖besselKIntegrand ν 1 t‖ ≤ J :=
        setIntegral_mono_set hint1 ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall fun t _ ↦ norm_nonneg _)) (Eventually.of_forall hsub)
      have hmono : ∫ t in Ioi 0 \ Icc (1 - δ) (1 + δ),
          -(rexp (-((x - 1) * (1 + 2 * c))) * ‖besselKIntegrand ν 1 t‖) ≤
          ∫ t in Ioi 0 \ Icc (1 - δ) (1 + δ), (besselKIntegrand ν x t).re := by
        refine setIntegral_mono_on ((hint1.mono_set hsub).const_mul _).neg
          (hre_int.mono_set hsub) (measurableSet_Ioi.diff measurableSet_Icc) fun t ht ↦ ?_
        have ht0 : 0 < t := ht.1
        have htδ : δ < |t - 1| := by
          by_contra hcon
          rcases abs_le.mp (not_lt.mp hcon) with ⟨hl, hu⟩
          exact ht.2 ⟨by linarith, by linarith⟩
        have h2 : 2 + 2 * δ ^ 2 / 3 ≤ t + t⁻¹ := two_add_le_add_inv hδ₀ hδ₁ ht0 htδ
        refine (neg_le_of_abs_le (abs_re_le_norm _)).trans' ?_
        rw [neg_le_neg_iff, norm_besselKIntegrand ν ht0, norm_besselKIntegrand ν ht0, ← mul_assoc,
          mul_comm (rexp _) (t ^ _), mul_assoc, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (rpow_nonneg ht0.le _)
        nlinarith
      rw [integral_neg, integral_const_mul] at hmono
      nlinarith [exp_pos (-((x - 1) * (1 + 2 * c)))]
    linarith
  have h1 : Tendsto (fun x : ℝ ↦ rexp (-(c * x))) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc₀)
  have h2 : Tendsto (fun x : ℝ ↦ rexp (-((1 - c) * x))) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc₁)
  have hlim : Tendsto (fun x : ℝ ↦ J * rexp (1 + 2 * c) * rexp (-(c * x)) +
      2 * rexp (-((1 - c) * x))) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (h1.const_mul (J * rexp (1 + 2 * c))).add (h2.const_mul 2)
  filter_upwards [eventually_ge_atTop 1, hlim.eventually (gt_mem_nhds (half_pos hδ₀))]
    with x hx hlt
  have e1 : rexp (1 + 2 * c) * rexp (-(c * x)) * rexp (-(x * (1 + c))) =
      rexp (-((x - 1) * (1 + 2 * c))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring1
  have e2 : rexp (-((1 - c) * x)) * rexp (-(x * (1 + c))) = rexp (-(2 * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring1
  have key : J * rexp (-((x - 1) * (1 + 2 * c))) + 2 * rexp (-(2 * x)) <
      δ / 2 * rexp (-(x * (1 + c))) := by
    rw [← e1, ← e2]
    linarith [mul_lt_mul_of_pos_right hlt (exp_pos (-(x * (1 + c))))]
  linarith [hmain x hx]

end Complex
