import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.LSeries.HardyZ

/-!
# The Riemann–Siegel theta function

The Riemann–Siegel theta function is `θ(t) = arg Γ((2 i t + 1) / 4) - (log π / 2) t`, with the
continuous branch of the argument that vanishes at `t = 0`. It is the argument of
`Γ_ℝ(1 / 2 + i t)`, so that Hardy's Z-function `Z(t) = Λ(1 / 2 + i t) / |Γ_ℝ(1 / 2 + i t)|`
(Mathlib's `hardyZ`) is `exp (i θ(t)) ζ(1 / 2 + i t)`.

## Main definitions

* `riemannSiegelTheta` (LMFDB `lfunction.zfunction`): the Riemann–Siegel theta function.

## Main results

* `exp_riemannSiegelTheta_mul_I`: `exp (i θ(t)) = Γ_ℝ(1 / 2 + i t) / |Γ_ℝ(1 / 2 + i t)|`.
* `ofReal_hardyZ_eq_exp_mul_riemannZeta`: Hardy's Z-function is `exp (i θ(t)) ζ(1 / 2 + i t)`.
-/

open Complex
open scoped Real

namespace Complex

private lemma quarter_add_mul_I_ne_neg_natCast (u : ℝ) (m : ℕ) : (1 / 4 + u * I / 2 : ℂ) ≠ -m :=
  fun h ↦ by
    have h : (1 / 4 + u * I / 2 : ℂ).re = (-(m : ℂ)).re := congrArg re h
    norm_num at h
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

lemma continuousAt_digamma {z : ℂ} (hz : 0 < z.re) : ContinuousAt digamma z := by
  have hU : IsOpen {z : ℂ | 0 < z.re} :=
    continuous_re.isOpen_preimage _ isOpen_Ioi
  have hΓ : DifferentiableOn ℂ Gamma {z : ℂ | 0 < z.re} := fun z hz ↦
    (differentiableAt_Gamma z fun m h ↦ by
      have h : z.re = (-(m : ℂ)).re := congrArg re h
      simp only [neg_re, natCast_re] at h
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), hz.out]).differentiableWithinAt
  have hd : ContinuousAt (deriv Gamma) z :=
    ((hΓ.analyticOnNhd hU).deriv z hz).continuousAt
  exact hd.div ((hΓ.differentiableAt (hU.mem_nhds hz)).continuousAt) (Gamma_ne_zero_of_re_pos hz)

lemma hasDerivAt_Gammaℝ_half_add_mul_I (t : ℝ) : HasDerivAt (fun u : ℝ ↦ Gammaℝ (1 / 2 + u * I))
    (Gammaℝ (1 / 2 + t * I) * (I / 2 * (digamma (1 / 4 + t * I / 2) - log π))) t := by
  have hg : HasDerivAt (fun u : ℝ ↦ (1 / 4 + u * I / 2 : ℂ)) (I / 2) t := by
    simpa using (((hasDerivAt_id t).ofReal_comp.mul_const I).div_const 2).const_add (1 / 4 : ℂ)
  have hh : HasDerivAt (fun z ↦ (π : ℂ) ^ (-z) * Gamma z)
      ((π : ℂ) ^ (-(1 / 4 + t * I / 2)) * Gamma (1 / 4 + t * I / 2) *
        (digamma (1 / 4 + t * I / 2) - log π)) (1 / 4 + t * I / 2) := by
    convert ((hasDerivAt_neg _).const_cpow (c := (π : ℂ)) (Or.inl <| ofReal_ne_zero.mpr
      Real.pi_pos.ne')).fun_mul
        (differentiableAt_Gamma _ (quarter_add_mul_I_ne_neg_natCast t)).hasDerivAt using 1
    have hΓ : Gamma (1 / 4 + t * I / 2) ≠ 0 :=
      Gamma_ne_zero (quarter_add_mul_I_ne_neg_natCast t)
    rw [digamma_def, logDeriv_apply]
    generalize (1 / 4 + t * I / 2 : ℂ) = z at hΓ ⊢
    field_simp
    ring1
  convert hh.comp t hg using 1
  · ext u
    rw [Function.comp_apply, Gammaℝ_def]
    congr 2 <;> ring1
  · have hs : (1 / 2 + t * I : ℂ) / 2 = 1 / 4 + t * I / 2 := by
      ring1
    rw [Gammaℝ_def, neg_div, hs]
    ring1

lemma Gammaℝ_one_half : Gammaℝ (1 / 2) = ((π ^ (-(1 / 4) : ℝ) * Real.Gamma (1 / 4) : ℝ) : ℂ) := by
  rw [Gammaℝ_def, ofReal_mul, ofReal_cpow Real.pi_pos.le, ← Gamma_ofReal]
  norm_num

end Complex

/-- The **Riemann–Siegel theta function** (LMFDB `lfunction.zfunction`)
`θ(t) = arg Γ((2 i t + 1) / 4) - (log π / 2) t`, with the continuous branch of
`arg Γ(1 / 4 + i t / 2)` that vanishes at `t = 0` (where `Γ(1 / 4) > 0`). As Mathlib has no
continuous logarithm of `Γ`, the branch is written as the integral of its derivative
`re ψ(1 / 4 + i u / 2) / 2`, where `ψ = Γ' / Γ` is the digamma function;
`exp_riemannSiegelTheta_mul_I` shows that `exp (i θ(t))` is
`Γ_ℝ(1 / 2 + i t) / |Γ_ℝ(1 / 2 + i t)|`, so that `θ(t)` is an argument of
`π ^ (-i t / 2) Γ(1 / 4 + i t / 2)`. -/
noncomputable def riemannSiegelTheta (t : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..t, (digamma (1 / 4 + u * I / 2)).re) / 2 - t * Real.log π / 2

/-- `exp (i θ(t))` is the unit complex number `Γ_ℝ(1 / 2 + i t) / |Γ_ℝ(1 / 2 + i t)|`, so `θ(t)` is
an argument of `Γ_ℝ(1 / 2 + i t) = π ^ (-1 / 4) π ^ (-i t / 2) Γ(1 / 4 + i t / 2)`. -/
lemma exp_riemannSiegelTheta_mul_I (t : ℝ) :
    cexp (riemannSiegelTheta t * I) = Gammaℝ (1 / 2 + t * I) / ‖Gammaℝ (1 / 2 + t * I)‖ := by
  let f : ℝ → ℂ := fun u ↦ I / 2 * (digamma (1 / 4 + u * I / 2) - log π)
  have hψ : Continuous fun u : ℝ ↦ digamma (1 / 4 + u * I / 2) :=
    continuous_iff_continuousAt.mpr fun u ↦ (continuousAt_digamma <| by norm_num).comp
      (by fun_prop)
  have hf : Continuous f :=
    continuous_const.mul <| hψ.sub continuous_const
  let ρ : ℝ → ℂ := fun t ↦ ∫ u in (0 : ℝ)..t, f u
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ ↦ Gammaℝ (1 / 2 + u * I) * cexp (-ρ u)) 0 u := by
    convert (hasDerivAt_Gammaℝ_half_add_mul_I u).mul
      ((hf.integral_hasStrictDerivAt 0 u).hasDerivAt.neg.cexp) using 1
    ring1
  have hc : Gammaℝ (1 / 2 + t * I) * cexp (-ρ t) = Gammaℝ (1 / 2) := by
    simpa [ρ] using is_const_of_deriv_eq_zero (fun u ↦ (hd u).differentiableAt)
      (fun u ↦ (hd u).deriv) t 0
  have hG : Gammaℝ (1 / 2 + t * I) = Gammaℝ (1 / 2) * cexp (ρ t) := by
    rw [← hc, mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
  have hρ : cexp (ρ t) = Real.exp (ρ t).re * cexp ((ρ t).im * I) := by
    rw [ofReal_exp, ← exp_add, re_add_im]
  have him : (ρ t).im = riemannSiegelTheta t := by
    have h : ∫ u in (0 : ℝ)..t, (f u).im = (ρ t).im :=
      intervalIntegral.intervalIntegral_im (hf.intervalIntegrable 0 t)
    have hfu (u : ℝ) : (f u).im = (digamma (1 / 4 + u * I / 2)).re / 2 - Real.log π / 2 := by
      simp [f, log_ofReal_re]
      ring1
    have hψ' : Continuous fun u : ℝ ↦ (digamma (1 / 4 + u * I / 2)).re / 2 :=
      (continuous_re.comp hψ).div_const 2
    rw [← h, riemannSiegelTheta, intervalIntegral.integral_congr fun u _ ↦ hfu u,
      intervalIntegral.integral_sub (hψ'.intervalIntegrable 0 t) intervalIntegrable_const,
      intervalIntegral.integral_div, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
      mul_div_assoc]
  have hpos : 0 < π ^ (-(1 / 4) : ℝ) * Real.Gamma (1 / 4) := by
    positivity
  rw [hG, hρ, him, Gammaℝ_one_half, norm_mul, norm_mul, norm_real, norm_real,
    norm_exp_ofReal_mul_I, Real.norm_of_nonneg hpos.le, Real.norm_of_nonneg (Real.exp_pos _).le]
  push_cast
  field_simp
  exact (div_self <| ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos <| by norm_num).ne').symm

@[simp]
lemma riemannSiegelTheta_zero : riemannSiegelTheta 0 = 0 := by
  simp [riemannSiegelTheta]

/-- Hardy's Z-function is `Z(t) = exp (i θ(t)) ζ(1 / 2 + i t)`, where `θ` is the Riemann–Siegel
theta function. -/
lemma ofReal_hardyZ_eq_exp_mul_riemannZeta (t : ℝ) :
    (hardyZ t : ℂ) = cexp (riemannSiegelTheta t * I) * riemannZeta (1 / 2 + t * I) := by
  have hs : (1 / 2 + t * I : ℂ) ≠ 0 :=
    ne_of_apply_ne re <| by norm_num
  have hΓ : Gammaℝ (1 / 2 + t * I) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos <| by norm_num
  rw [ofReal_hardyZ, exp_riemannSiegelTheta_mul_I, riemannZeta_def_of_ne_zero hs]
  generalize (1 / 2 + t * I : ℂ) = s at hΓ ⊢
  field_simp
