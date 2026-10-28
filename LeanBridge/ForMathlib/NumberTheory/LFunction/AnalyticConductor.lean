import LeanBridge.ForMathlib.NumberTheory.LFunction.Basic
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Analytic.AnalyticConductor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The analytic conductor of an analytic L-function

The analytic conductor of an analytic L-function with gamma factor `L_∞(s)` and conductor `N` is
the positive real number `exp (2 re (L_∞'(1 / 2) / L_∞(1 / 2))) N`.

## Main definitions

* `AnalyticLFunction.SelbergData.analyticConductor` and `AnalyticLFunction.analyticConductor`
  (LMFDB `lfunction.analytic_conductor`): the analytic conductor of a functional equation and of an
  analytic L-function.

## Main results

* `AnalyticLFunction.SelbergData.analyticConductor_pos`: the analytic conductor is positive.
* `AnalyticLFunction.SelbergData.analyticConductor_eq_analyticConductorLMFDB`: for the gamma factor
  `Γ_ℂ(s + (k - 1) / 2)` of a newform of weight `k`, the analytic conductor is the analytic
  conductor `N (exp (ψ (k / 2)) / (2π))²` of a newform of level `N` and weight `k`.
-/

open Complex HeckeRing.GL2
open scoped Real

namespace AnalyticLFunction.SelbergData

variable (D : SelbergData) {k : ℤ}

/-- The **analytic conductor** (LMFDB `lfunction.analytic_conductor`)
`exp (2 re (L_∞'(1 / 2) / L_∞(1 / 2))) N` of a functional equation with gamma factor `L_∞(s)` and
conductor `N`. -/
noncomputable def analyticConductor : ℝ :=
  Real.exp (2 * (logDeriv D.gammaFactor (1 / 2)).re) * D.conductor

/-- The analytic conductor is positive. -/
lemma analyticConductor_pos : 0 < D.analyticConductor :=
  mul_pos (Real.exp_pos _) <| Nat.cast_pos.mpr D.conductor_pos

lemma logDeriv_gammaFactor (hk : 0 < k) (hμ : D.μ = 0) (hν : D.ν = {((k : ℂ) - 1) / 2}) :
    logDeriv D.gammaFactor (1 / 2) = digamma (k / 2) - log (2 * π) := by
  have hg : D.gammaFactor = fun s ↦ 2 * (2 * π) ^ (-(s + ((k : ℂ) - 1) / 2)) *
      Gamma (s + ((k : ℂ) - 1) / 2) :=
    funext fun s ↦ by simp [gammaFactor, hμ, hν, Gammaℂ_def]
  have hs : (1 / 2 : ℂ) + ((k : ℂ) - 1) / 2 = k / 2 := by
    ring1
  have hm (m : ℕ) : (k : ℂ) / 2 ≠ -m := fun h ↦ by
    have h : ((k : ℂ) / 2).re = (-(m : ℂ)).re := congrArg re h
    norm_num at h
    linarith [(Int.cast_pos (R := ℝ)).mpr hk, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hπ : (2 * π : ℂ) ≠ 0 := by
    exact_mod_cast Real.two_pi_pos.ne'
  have hd : HasDerivAt (fun s ↦ s + ((k : ℂ) - 1) / 2) 1 (1 / 2) :=
    (hasDerivAt_id _).add_const _
  have h₁ : HasDerivAt (fun s ↦ (2 * π : ℂ) ^ (-(s + ((k : ℂ) - 1) / 2)))
      ((2 * π : ℂ) ^ (-(1 / 2 + ((k : ℂ) - 1) / 2)) * log (2 * π) * -1) (1 / 2) :=
    hd.neg.const_cpow (Or.inl hπ)
  have h₂ : HasDerivAt (fun s ↦ Gamma (s + ((k : ℂ) - 1) / 2))
      (deriv Gamma (1 / 2 + ((k : ℂ) - 1) / 2) * 1) (1 / 2) :=
    (differentiableAt_Gamma _ (hs ▸ hm)).hasDerivAt.comp (1 / 2 : ℂ) hd
  rw [hg, logDeriv_apply, ((h₁.const_mul 2).fun_mul h₂).deriv, digamma_def, logDeriv_apply, hs]
  field_simp [Gamma_ne_zero hm]
  ring1

/-- For the gamma factor `Γ_ℂ(s + (k - 1) / 2)` of a newform of weight `k`, the analytic conductor
is the analytic conductor `N (exp (ψ (k / 2)) / (2π))²` of a newform of level `N` and weight `k`. -/
lemma analyticConductor_eq_analyticConductorLMFDB (hk : 0 < k) (hμ : D.μ = 0)
    (hν : D.ν = {((k : ℂ) - 1) / 2}) :
    D.analyticConductor = Newform.analyticConductorLMFDB D.conductor k := by
  rw [analyticConductor, D.logDeriv_gammaFactor hk hμ hν, Newform.analyticConductorLMFDB, sub_re,
    ← ofReal_ofNat, ← ofReal_mul, log_ofReal_re, two_mul, Real.exp_add, Real.exp_sub,
    Real.exp_log Real.two_pi_pos]
  ring1

end AnalyticLFunction.SelbergData

namespace AnalyticLFunction

variable (L : AnalyticLFunction)

/-- The **analytic conductor** (LMFDB `lfunction.analytic_conductor`)
`exp (2 re (L_∞'(1 / 2) / L_∞(1 / 2))) N` of an analytic L-function with gamma factor `L_∞(s)`
(`AnalyticLFunction.SelbergData.gammaFactor`, LMFDB `lfunction.infinity_factor`) and conductor `N`.
-/
noncomputable def analyticConductor : ℝ :=
  L.selbergData.analyticConductor

lemma analyticConductor_pos : 0 < L.analyticConductor :=
  L.selbergData.analyticConductor_pos

end AnalyticLFunction
