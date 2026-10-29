import LeanBridge.ForMathlib.NumberTheory.ModularForms.Analytic.AnalyticConductor
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# The quantity `N k²` of a classical modular form

The LMFDB sorts and searches classical modular forms, and spaces of modular forms, of level `N` and
weight `k` by the integer `N k²` (LMFDB `cmf.nk2`). As `k → ∞` it is proportional to the analytic
conductor `N (exp (ψ (k / 2)) / (2π))²` (LMFDB `cmf.analytic_conductor`), where `ψ = Γ' / Γ` is
the digamma function: their ratio tends to `1 / (16 π²)`. This follows from the bounds
`log x - 1 / x ≤ ψ(x) ≤ log x` for `x > 0`, which come from the convexity of `log Γ` on `(0, ∞)`
(the Bohr–Mollerup theorem) and the functional equation `ψ(x + 1) = ψ(x) + 1 / x`.

## Main definitions

* `HeckeRing.GL2.Newform.levelMulWeightSq` (LMFDB `cmf.nk2`): the integer `N k²`.

## Main results

* `Complex.re_digamma_le_log`, `Complex.log_sub_inv_le_re_digamma`: the bounds
  `log x - 1 / x ≤ ψ(x) ≤ log x` for `x > 0`.
* `HeckeRing.GL2.Newform.tendsto_analyticConductorLMFDB_div_levelMulWeightSq`: the analytic
  conductor divided by `N k²` tends to `1 / (16 π²)` as `k → ∞`.
-/

open Filter Set

open scoped Real Topology

namespace Complex

variable {x : ℝ}

lemma ofReal_ne_neg_natCast_of_pos (hx : 0 < x) (m : ℕ) : (x : ℂ) ≠ -m := fun h ↦ by
  have hm : x = -m := by
    simpa using congrArg re h
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

lemma hasDerivAt_log_Gamma (hx : 0 < x) :
    HasDerivAt (Real.log ∘ Real.Gamma) (digamma x).re x := by
  have h : HasDerivAt Real.Gamma (deriv Gamma x).re x := by
    simpa [Gamma_ofReal] using
      (differentiableAt_Gamma x (ofReal_ne_neg_natCast_of_pos hx)).hasDerivAt.real_of_complex
  rw [digamma_def, logDeriv_apply, Gamma_ofReal, div_ofReal_re]
  exact h.log (Real.Gamma_pos_of_pos hx).ne'

/-- **The digamma function is at most the logarithm**: `ψ(x) ≤ log x` for `x > 0`. -/
lemma re_digamma_le_log (hx : 0 < x) : (digamma x).re ≤ Real.log x := by
  have h : (digamma x).re ≤ slope (Real.log ∘ Real.Gamma) x (x + 1) :=
    Real.convexOn_log_Gamma.le_slope_of_hasDerivAt (mem_Ioi.mpr hx)
      (mem_Ioi.mpr (by linarith : 0 < x + 1)) (lt_add_one x) (hasDerivAt_log_Gamma hx)
  rwa [slope_def_field, Function.comp_apply, Function.comp_apply, Real.Gamma_add_one hx.ne',
    Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne', add_sub_cancel_right, add_sub_cancel_left,
    div_one] at h

/-- **The digamma function is at least the logarithm minus the inverse**: `log x - 1 / x ≤ ψ(x)`
for `x > 0`. -/
lemma log_sub_inv_le_re_digamma (hx : 0 < x) : Real.log x - x⁻¹ ≤ (digamma x).re := by
  have hx₁ : 0 < x + 1 := by
    linarith
  have h : slope (Real.log ∘ Real.Gamma) x (x + 1) ≤ (digamma (x + 1 : ℝ)).re :=
    Real.convexOn_log_Gamma.slope_le_of_hasDerivAt (mem_Ioi.mpr hx) (mem_Ioi.mpr hx₁)
      (lt_add_one x) (hasDerivAt_log_Gamma hx₁)
  rw [slope_def_field, Function.comp_apply, Function.comp_apply, Real.Gamma_add_one hx.ne',
    Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne', add_sub_cancel_right, add_sub_cancel_left,
    div_one, ofReal_add, ofReal_one, digamma_apply_add_one _ (ofReal_ne_neg_natCast_of_pos hx),
    add_re, ← ofReal_inv, ofReal_re] at h
  linarith

lemma tendsto_re_digamma_sub_log :
    Tendsto (fun x : ℝ ↦ (digamma x).re - Real.log x) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun x ↦ -x⁻¹)
    (by simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).neg) tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    linarith [log_sub_inv_le_re_digamma hx]
  · filter_upwards [eventually_gt_atTop 0] with x hx
    linarith [re_digamma_le_log hx]

end Complex

namespace HeckeRing.GL2.Newform

variable (N : ℕ) (k : ℤ)

/-- The integer **`N k²`** (LMFDB `cmf.nk2`) of a classical modular form, or of a space of modular
forms, of level `N` and weight `k`: the level times the square of the weight. Like the analytic
conductor `analyticConductorLMFDB`, to which it is asymptotically proportional as `k → ∞`
(`tendsto_analyticConductorLMFDB_div_levelMulWeightSq`), it depends only on `N` and `k`, which are
therefore its only arguments. -/
def levelMulWeightSq : ℤ :=
  N * k ^ 2

variable {N} in
/-- **`N k²` is asymptotically proportional to the analytic conductor**: as `k → ∞`, the analytic
conductor `N (exp (ψ (k / 2)) / (2π))²` divided by `N k²` tends to `1 / (16 π²)`. -/
lemma tendsto_analyticConductorLMFDB_div_levelMulWeightSq [NeZero N] :
    Tendsto (fun k : ℤ ↦ analyticConductorLMFDB N k / levelMulWeightSq N k) atTop
      (𝓝 (1 / (16 * π ^ 2))) := by
  have htend : Tendsto (fun k : ℤ ↦ (k : ℝ) / 2) atTop atTop :=
    tendsto_intCast_atTop_atTop.atTop_div_const two_pos
  rw [← one_pow 2, ← Real.exp_zero]
  refine (((Complex.tendsto_re_digamma_sub_log.comp htend).rexp.pow 2).div_const _).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk₂ : (0 : ℝ) < k / 2 := by
    positivity
  have hN : (N : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [Function.comp_apply, Real.exp_sub, Real.exp_log hk₂, analyticConductorLMFDB,
    levelMulWeightSq]
  push_cast
  field_simp
  ring1

end HeckeRing.GL2.Newform
