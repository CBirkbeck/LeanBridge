import Mathlib.Algebra.CubicDiscriminant
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# The complex period of a Weierstrass curve over `ℂ`

Let `W` be a Weierstrass curve over `ℂ` and `ω = dx / (2y + a₁x + a₃)` its invariant differential.
For a complex place `v` of a number field, the local factor of the global period (LMFDB
`ec.period`) is `Ω_v = |∫_{E(ℂ)} ω ∧ ω̄|`, twice the covolume of the period lattice `Λ` of `ω`
(LMFDB `ec.q.period_lattice`). On the curve, `(2y + a₁x + a₃)² = Ψ₂Sq(x)`, where

  `Ψ₂Sq(x) = 4x³ + b₂x² + 2b₄x + b₆`

is Mathlib's `WeierstrassCurve.Ψ₂Sq`. The `x`-coordinate exhibits `E(ℂ)` as a double cover of
`ℂ`, and the density of `|ω ∧ ω̄|` is `2 dA(x) / |Ψ₂Sq(x)|`, where `dA` is the Lebesgue measure on
`ℂ`. Equivalently, under the uniformisation `ℂ/Λ ≅ E(ℂ)`, `x = ℘(z) - b₂/12` and
`2y + a₁x + a₃ = ℘'(z)`, so `dA(x) = |Ψ₂Sq(x)| dA(z)` on each of the two sheets. Hence

  `covol(Λ) = 2 ∫_ℂ dA(x) / |Ψ₂Sq(x)|` and `Ω_v = |∫_{E(ℂ)} ω ∧ ω̄| = 4 ∫_ℂ dA(x) / |Ψ₂Sq(x)|`.

This file defines these quantities by the explicit integral, as Tau Ceti's
`WeierstrassCurve.realPeriod` does for a real place; the period lattice itself, which needs the
uniformisation of `E(ℂ)`, is not formalised. The integral is a Lebesgue integral of a nonnegative
function, with values in `ℝ≥0∞`. So that a divergent integral cannot silently read as `0`, its
finiteness is a theorem: the three roots `e₁, e₂, e₃` of `Ψ₂Sq` are distinct on an elliptic curve
and `|Ψ₂Sq(x)| = 4 |x - e₁| |x - e₂| |x - e₃|`, so near a root the integrand is at most a constant
times `|x - eᵢ|⁻¹`, which is integrable in dimension two, and far from the roots it is at most a
constant times `(1 + |x|)⁻³`, which is integrable at infinity.

Under a change of variables `C = (u, r, s, t)` the invariant differential becomes `u ω`, its
period lattice `u Λ`, and correspondingly the covolume and the complex period are multiplied by
`|u|²`.

## Main definitions

* `WeierstrassCurve.complexPeriodLIntegral`: the integral `∫_ℂ dA(x) / |Ψ₂Sq(x)|` in `ℝ≥0∞`.
* `WeierstrassCurve.periodCovolume`: the covolume `2 ∫_ℂ dA(x) / |Ψ₂Sq(x)|` of the period lattice
  (LMFDB `ec.q.period_lattice`).
* `WeierstrassCurve.complexPeriod`: the period `Ω = |∫_{E(ℂ)} ω ∧ ω̄|` at a complex place
  (LMFDB `ec.period`).

## Main results

* `WeierstrassCurve.complexPeriodLIntegral_pos`: the integral is positive.
* `WeierstrassCurve.complexPeriodLIntegral_lt_top`: the integral is finite on an elliptic curve.
* `WeierstrassCurve.periodCovolume_pos` and `WeierstrassCurve.complexPeriod_pos`: the covolume
  and the complex period of an elliptic curve are positive.
* `WeierstrassCurve.complexPeriodLIntegral_variableChange`,
  `WeierstrassCurve.periodCovolume_variableChange` and
  `WeierstrassCurve.complexPeriod_variableChange`: a change of variables multiplies them by
  `|u|²`.
* `WeierstrassCurve.complexPeriodLIntegral_map_conj` and `WeierstrassCurve.complexPeriod_map_conj`:
  they are invariant under complex conjugation of the coefficients.
-/

open MeasureTheory Polynomial
open scoped ComplexConjugate ENNReal

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℂ) (C : VariableChange ℂ) {e₁ e₂ e₃ : ℂ}

/-- The integral `∫_ℂ dA(x) / |Ψ₂Sq(x)|` of a Weierstrass curve over `ℂ`, where
`Ψ₂Sq(x) = 4x³ + b₂x² + 2b₄x + b₆` is the square of `2y + a₁x + a₃` on the curve and `dA` is the
Lebesgue measure on `ℂ`, as a value in `ℝ≥0∞`. It is finite for an elliptic curve
(`WeierstrassCurve.complexPeriodLIntegral_lt_top`), and it is half the covolume of the period
lattice of the invariant differential. -/
noncomputable def complexPeriodLIntegral : ℝ≥0∞ :=
  ∫⁻ x, ‖W.Ψ₂Sq.eval x‖ₑ⁻¹

/-- The **covolume of the period lattice** `Λ` (LMFDB `ec.q.period_lattice`) of the invariant
differential `ω = dx / (2y + a₁x + a₃)` of a Weierstrass curve over `ℂ`, the area of a fundamental
parallelogram of `Λ`, defined as the area `∫_{E(ℂ)} (i/2) ω ∧ ω̄` of `E(ℂ) ≅ ℂ/Λ` computed in the
`x`-coordinate: `2 ∫_ℂ dA(x) / |Ψ₂Sq(x)|`, the factor `2` counting the two points of `E(ℂ)` over
each `x`. It is `0` when the integral diverges, which does not happen on an elliptic curve. -/
noncomputable def periodCovolume : ℝ :=
  2 * W.complexPeriodLIntegral.toReal

/-- The **complex period** `Ω(W) = |∫_{E(ℂ)} ω ∧ ω̄|` (LMFDB `ec.period`) of a Weierstrass curve
over `ℂ`, the local factor of the global period at a complex place: twice the covolume of the
period lattice, `4 ∫_ℂ dA(x) / |Ψ₂Sq(x)|`. -/
noncomputable def complexPeriod : ℝ :=
  2 * W.periodCovolume

private lemma measurable_integrand : Measurable fun x : ℂ ↦ ‖W.Ψ₂Sq.eval x‖ₑ⁻¹ :=
  W.Ψ₂Sq.continuous.measurable.enorm.inv

/-- **The integral of the complex period is positive**, for every Weierstrass curve over `ℂ`: its
integrand is positive everywhere. -/
lemma complexPeriodLIntegral_pos : 0 < W.complexPeriodLIntegral := by
  rw [complexPeriodLIntegral, lintegral_pos_iff_support W.measurable_integrand]
  simp [Function.support]

private lemma exists_enorm_sub_inv_mul_le (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ z : ℂ, ‖z - e₁‖ₑ⁻¹ * ‖z - e₂‖ₑ⁻¹ * ‖z - e₃‖ₑ⁻¹ ≤ K *
    (‖z - e₁‖ₑ⁻¹ + ‖z - e₂‖ₑ⁻¹ + ‖z - e₃‖ₑ⁻¹) := by
  let δ : ℝ := min (min ‖e₁ - e₂‖ ‖e₁ - e₃‖) ‖e₂ - e₃‖
  have hδ : 0 < δ :=
    lt_min (lt_min (norm_sub_pos_iff.mpr h₁₂) (norm_sub_pos_iff.mpr h₁₃)) (norm_sub_pos_iff.mpr h₂₃)
  let k : ℝ≥0∞ := (ENNReal.ofReal (δ / 2))⁻¹
  have hk : k ≠ ∞ := by simp [k, hδ]
  -- a point at distance at least `δ / 2` contributes a factor at most `k`
  have far {z e : ℂ} (h : δ / 2 ≤ ‖z - e‖) : ‖z - e‖ₑ⁻¹ ≤ k :=
    ENNReal.inv_le_inv.mpr (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal h)
  -- no point is within `δ / 2` of two of the `eᵢ`
  have near {z a b : ℂ} (hab : δ ≤ ‖a - b‖) : δ / 2 ≤ ‖z - a‖ ∨ δ / 2 ≤ ‖z - b‖ := by
    by_contra! h
    linarith [norm_sub_le_norm_sub_add_norm_sub a z b, norm_sub_rev z a]
  have hδ₁₂ : δ ≤ ‖e₁ - e₂‖ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ₁₃ : δ ≤ ‖e₁ - e₃‖ := (min_le_left _ _).trans (min_le_right _ _)
  have hδ₂₃ : δ ≤ ‖e₂ - e₃‖ := min_le_right _ _
  refine ⟨k * k, ENNReal.mul_ne_top hk hk, fun z ↦ ?_⟩
  by_cases f₁ : δ / 2 ≤ ‖z - e₁‖
  · by_cases f₂ : δ / 2 ≤ ‖z - e₂‖
    · exact (mul_le_mul_left (mul_le_mul' (far f₁) (far f₂)) _).trans
        (mul_le_mul_right le_add_self _)
    · have f₃ : δ / 2 ≤ ‖z - e₃‖ := (near hδ₂₃).resolve_left f₂
      refine (mul_le_mul' (mul_le_mul_left (far f₁) _) (far f₃)).trans ?_
      rw [mul_right_comm]
      exact mul_le_mul_right (le_add_self.trans le_self_add) _
  · have f₂ : δ / 2 ≤ ‖z - e₂‖ := (near hδ₁₂).resolve_left f₁
    have f₃ : δ / 2 ≤ ‖z - e₃‖ := (near hδ₁₃).resolve_left f₁
    refine (mul_le_mul' (mul_le_mul_right (far f₂) _) (far f₃)).trans ?_
    rw [mul_assoc, mul_comm]
    exact mul_le_mul_right (le_self_add.trans le_self_add) _

private lemma enorm_eval_Ψ₂Sq_inv_le
    (hfac : ∀ x : ℂ, ‖W.Ψ₂Sq.eval x‖ = 4 * (‖x - e₁‖ * ‖x - e₂‖ * ‖x - e₃‖)) (x : ℂ) :
    ‖W.Ψ₂Sq.eval x‖ₑ⁻¹ ≤ ‖x - e₁‖ₑ⁻¹ * ‖x - e₂‖ₑ⁻¹ * ‖x - e₃‖ₑ⁻¹ := by
  rw [← ENNReal.mul_inv (Or.inr enorm_ne_top) (Or.inl enorm_ne_top),
    ← ENNReal.mul_inv (Or.inr enorm_ne_top) (Or.inl (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top))]
  refine ENNReal.inv_le_inv.mpr ?_
  simp only [← ofReal_norm]
  rw [hfac x, ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left (by positivity) (by norm_num))

private lemma setLIntegral_closedBall_lt_top (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃)
    (hfac : ∀ x : ℂ, ‖W.Ψ₂Sq.eval x‖ = 4 * (‖x - e₁‖ * ‖x - e₂‖ * ‖x - e₃‖)) {R : ℝ} (hR : 0 ≤ R) :
    ∫⁻ x in Metric.closedBall 0 R, ‖W.Ψ₂Sq.eval x‖ₑ⁻¹ < ∞ := by
  rcases exists_enorm_sub_inv_mul_le h₁₂ h₁₃ h₂₃ with ⟨K, hK, hle⟩
  have hfin (e : ℂ) : ∫⁻ x in Metric.closedBall 0 R, ‖x - e‖ₑ⁻¹ < ∞ := by
    have hsub : Metric.closedBall (0 : ℂ) R ⊆ Metric.closedBall e (R + ‖e‖) := fun x hx ↦ by
      rw [mem_closedBall_zero_iff] at hx
      rw [Metric.mem_closedBall, dist_eq_norm]
      linarith [norm_sub_le x e]
    simp_rw [enorm_sub_rev _ e, ← ENNReal.rpow_neg_one]
    refine (lintegral_mono_set hsub).trans_lt ?_
    rw [TauCeti.setLIntegral_closedBall_enorm_sub_rpow (by norm_num) (by positivity) e]
    exact ENNReal.ofReal_lt_top
  have hmeas (e : ℂ) : Measurable fun x : ℂ ↦ ‖x - e‖ₑ⁻¹ := by
    fun_prop
  refine (lintegral_mono fun x ↦ (W.enorm_eval_Ψ₂Sq_inv_le hfac x).trans (hle x)).trans_lt ?_
  rw [lintegral_const_mul' _ _ hK, lintegral_add_left (f := fun x : ℂ ↦ ‖x - e₁‖ₑ⁻¹ + ‖x - e₂‖ₑ⁻¹)
    ((hmeas e₁).add (hmeas e₂)), lintegral_add_left (hmeas e₁)]
  exact ENNReal.mul_lt_top hK.lt_top
    (ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hfin e₁, hfin e₂⟩, hfin e₃⟩)

private lemma setLIntegral_compl_closedBall_lt_top
    (hfac : ∀ x : ℂ, ‖W.Ψ₂Sq.eval x‖ = 4 * (‖x - e₁‖ * ‖x - e₂‖ * ‖x - e₃‖)) :
    ∫⁻ x in (Metric.closedBall 0 (2 * (‖e₁‖ + ‖e₂‖ + ‖e₃‖) + 1))ᶜ, ‖W.Ψ₂Sq.eval x‖ₑ⁻¹ < ∞ := by
  have hpt (x : ℂ) (hx : x ∈ (Metric.closedBall 0 (2 * (‖e₁‖ + ‖e₂‖ + ‖e₃‖) + 1))ᶜ) :
      ‖W.Ψ₂Sq.eval x‖ₑ⁻¹ ≤ ENNReal.ofReal 2 * ENNReal.ofReal ((1 + ‖x‖) ^ (-3 : ℝ)) := by
    rw [Set.mem_compl_iff, mem_closedBall_zero_iff, not_le] at hx
    -- each `‖x - eᵢ‖` is at least `(1 + ‖x‖) / 2`
    have hfar (e : ℂ) (he : 2 * ‖e‖ + 1 ≤ 2 * (‖e₁‖ + ‖e₂‖ + ‖e₃‖) + 1) :
        (1 + ‖x‖) / 2 ≤ ‖x - e‖ := by
      linarith [norm_sub_norm_le x e]
    have h₁ : (1 + ‖x‖) / 2 ≤ ‖x - e₁‖ := hfar e₁ (by linarith [norm_nonneg e₂, norm_nonneg e₃])
    have h₂ : (1 + ‖x‖) / 2 ≤ ‖x - e₂‖ := hfar e₂ (by linarith [norm_nonneg e₁, norm_nonneg e₃])
    have h₃ : (1 + ‖x‖) / 2 ≤ ‖x - e₃‖ := hfar e₃ (by linarith [norm_nonneg e₁, norm_nonneg e₂])
    have hy : 0 < (1 + ‖x‖) / 2 := by positivity
    have hΨ : (1 + ‖x‖) ^ 3 / 2 ≤ ‖W.Ψ₂Sq.eval x‖ := by
      rw [hfac x]
      nlinarith [mul_le_mul (mul_le_mul h₁ h₂ hy.le (hy.le.trans h₁)) h₃ hy.le
        (mul_nonneg (hy.le.trans h₁) (hy.le.trans h₂))]
    have hpos : 0 < ‖W.Ψ₂Sq.eval x‖ := (by positivity : (0 : ℝ) < (1 + ‖x‖) ^ 3 / 2).trans_le hΨ
    rw [← ofReal_norm, ← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_mul zero_le_two]
    refine ENNReal.ofReal_le_ofReal ((inv_anti₀ (by positivity) hΨ).trans_eq ?_)
    rw [inv_div, div_eq_mul_inv, Real.rpow_neg (by positivity)]
    norm_cast
  refine (setLIntegral_mono' Metric.isClosed_closedBall.measurableSet.compl hpt).trans_lt
    ((setLIntegral_le_lintegral _ _).trans_lt ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (finite_integral_one_add_norm (by norm_num))

private lemma map_volume_mul_left {a : ℂ} (ha : a ≠ 0) :
    Measure.map (a * ·) (volume : Measure ℂ) = (‖a‖ₑ ^ 2)⁻¹ • volume := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ a) = ‖a‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  have hmap : Measure.map (LinearMap.mulLeft ℝ a) (volume : Measure ℂ) =
      ENNReal.ofReal |(LinearMap.det (LinearMap.mulLeft ℝ a))⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; positivity)
  rw [hdet, abs_inv, abs_pow, abs_norm, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow (norm_nonneg a), ofReal_norm] at hmap
  exact hmap

/-- **Under a change of variables `C = (u, r, s, t)` the integral of the complex period scales by
`|u|²`**, as the invariant differential becomes `u ω`. -/
@[simp]
lemma complexPeriodLIntegral_variableChange :
    (C • W).complexPeriodLIntegral = ‖(C.u : ℂ)‖ₑ ^ 2 * W.complexPeriodLIntegral := by
  have hu2 : (C.u : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 C.u.ne_zero
  -- the integrand of `C • W` at `x` is `|u|⁶` times that of `W` at `u² x + r`
  have hpt (x : ℂ) : ‖(C • W).Ψ₂Sq.eval x‖ₑ⁻¹ = ‖(C.u : ℂ)‖ₑ ^ 6 *
      ‖W.Ψ₂Sq.eval ((C.u : ℂ) ^ 2 * (x + C.r / (C.u : ℂ) ^ 2))‖ₑ⁻¹ := by
    rw [eval_variableChange_Ψ₂Sq, mul_add, mul_div_cancel₀ _ hu2, enorm_mul,
      ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), enorm_pow, Units.val_inv_eq_inv_val,
      enorm_inv C.u.ne_zero, ENNReal.inv_pow, inv_inv]
  -- translation invariance removes the shift by `r / u²`
  have htrans : ∫⁻ x, ‖W.Ψ₂Sq.eval ((C.u : ℂ) ^ 2 * (x + C.r / (C.u : ℂ) ^ 2))‖ₑ⁻¹ =
      ∫⁻ x, ‖W.Ψ₂Sq.eval ((C.u : ℂ) ^ 2 * x)‖ₑ⁻¹ :=
    lintegral_add_right_eq_self (fun y ↦ ‖W.Ψ₂Sq.eval ((C.u : ℂ) ^ 2 * y)‖ₑ⁻¹) _
  -- dilation by `u²` scales the integral by `|u|⁻⁴`
  have hdil : ∫⁻ x, ‖W.Ψ₂Sq.eval ((C.u : ℂ) ^ 2 * x)‖ₑ⁻¹ = (‖(C.u : ℂ) ^ 2‖ₑ ^ 2)⁻¹ *
      ∫⁻ x, ‖W.Ψ₂Sq.eval x‖ₑ⁻¹ := by
    rw [← smul_eq_mul (‖(C.u : ℂ) ^ 2‖ₑ ^ 2)⁻¹, ← lintegral_smul_measure,
      ← map_volume_mul_left hu2]
    exact ((measurableEmbedding_mulLeft₀ hu2).lintegral_map fun y ↦ ‖W.Ψ₂Sq.eval y‖ₑ⁻¹).symm
  have hconst : ‖(C.u : ℂ)‖ₑ ^ 6 * (‖(C.u : ℂ) ^ 2‖ₑ ^ 2)⁻¹ = ‖(C.u : ℂ)‖ₑ ^ 2 := by
    rw [enorm_pow, ← pow_mul, ← div_eq_mul_inv, eq_comm, ENNReal.eq_div_iff (by simp) (by simp),
      ← pow_add]
  rw [complexPeriodLIntegral, complexPeriodLIntegral]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ (by simp), htrans, hdil, ← mul_assoc, hconst]

/-- **The covolume of the period lattice scales by `|u|²` under a change of variables**
`C = (u, r, s, t)`, the period lattice of `u ω` being `u Λ`. -/
@[simp]
lemma periodCovolume_variableChange :
    (C • W).periodCovolume = ‖(C.u : ℂ)‖ ^ 2 * W.periodCovolume := by
  rw [periodCovolume, periodCovolume, complexPeriodLIntegral_variableChange, ENNReal.toReal_mul,
    ENNReal.toReal_pow, toReal_enorm]
  ring1

/-- **The complex period scales by `|u|²` under a change of variables** `C = (u, r, s, t)`. -/
@[simp]
lemma complexPeriod_variableChange : (C • W).complexPeriod = ‖(C.u : ℂ)‖ ^ 2 * W.complexPeriod := by
  rw [complexPeriod, complexPeriod, periodCovolume_variableChange]
  ring1

/-- **The integral of the complex period is invariant under complex conjugation of the
coefficients**, as complex conjugation preserves the Lebesgue measure of `ℂ`. -/
@[simp]
lemma complexPeriodLIntegral_map_conj :
    (W.map conj).complexPeriodLIntegral = W.complexPeriodLIntegral := by
  have hpt (x : ℂ) : ‖(W.map conj).Ψ₂Sq.eval x‖ₑ⁻¹ = ‖W.Ψ₂Sq.eval (conj x)‖ₑ⁻¹ := by
    rw [map_Ψ₂Sq, eval_map, ← Complex.conj_conj x, eval₂_at_apply, Complex.conj_conj]
    simp
  rw [complexPeriodLIntegral, complexPeriodLIntegral]
  simp_rw [hpt]
  exact Complex.conjLIE.measurePreserving.lintegral_comp_emb
    Complex.conjLIE.toHomeomorph.measurableEmbedding fun x ↦ ‖W.Ψ₂Sq.eval x‖ₑ⁻¹

/-- **The complex period is invariant under complex conjugation of the coefficients**, so that the
local period at a complex place does not depend on which of its two conjugate embeddings is
used. -/
@[simp]
lemma complexPeriod_map_conj : (W.map conj).complexPeriod = W.complexPeriod := by
  rw [complexPeriod, complexPeriod, periodCovolume, periodCovolume, complexPeriodLIntegral_map_conj]

variable [W.IsElliptic]

private lemma exists_norm_eval_Ψ₂Sq_eq : ∃ e₁ e₂ e₃ : ℂ, e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ ∧ ∀ x : ℂ,
    ‖W.Ψ₂Sq.eval x‖ = 4 * (‖x - e₁‖ * ‖x - e₂‖ * ‖x - e₃‖) := by
  have ha : W.twoTorsionPolynomial.a ≠ 0 := by norm_num [twoTorsionPolynomial]
  rcases (Cubic.splits_iff_roots_eq_three (φ := RingHom.id ℂ) ha).mp (IsAlgClosed.splits _) with
    ⟨e₁, e₂, e₃, h3⟩
  have hdisc : 16 * W.Δ = (W.twoTorsionPolynomial.a * W.twoTorsionPolynomial.a * (e₁ - e₂) *
      (e₁ - e₃) * (e₂ - e₃)) ^ 2 := by
    rw [← twoTorsionPolynomial_discr]
    exact Cubic.discr_eq_prod_three_roots ha h3
  have hne : 16 * W.Δ ≠ 0 := mul_ne_zero (by norm_num) W.isUnit_Δ.ne_zero
  rw [hdisc, pow_ne_zero_iff two_ne_zero] at hne
  simp only [mul_ne_zero_iff, sub_ne_zero] at hne
  rcases hne with ⟨⟨⟨-, h₁₂⟩, h₁₃⟩, h₂₃⟩
  refine ⟨e₁, e₂, e₃, h₁₂, h₁₃, h₂₃, fun x ↦ ?_⟩
  have hx : W.twoTorsionPolynomial.toPoly.eval x =
      (C W.twoTorsionPolynomial.a * (X - C e₁) * (X - C e₂) * (X - C e₃)).eval x := by
    simpa [Cubic.map_toPoly] using congrArg (eval x) (Cubic.eq_prod_three_roots ha h3)
  rw [Ψ₂Sq_eq, hx]
  simp [twoTorsionPolynomial, mul_assoc]

/-- **The integral of the complex period of an elliptic curve is finite.** -/
lemma complexPeriodLIntegral_lt_top : W.complexPeriodLIntegral < ∞ := by
  rcases W.exists_norm_eval_Ψ₂Sq_eq with ⟨e₁, e₂, e₃, h₁₂, h₁₃, h₂₃, hfac⟩
  rw [complexPeriodLIntegral, ← lintegral_add_compl _ (Metric.isClosed_closedBall (x := (0 : ℂ))
    (ε := 2 * (‖e₁‖ + ‖e₂‖ + ‖e₃‖) + 1)).measurableSet]
  exact ENNReal.add_lt_top.mpr ⟨W.setLIntegral_closedBall_lt_top h₁₂ h₁₃ h₂₃ hfac (by positivity),
    W.setLIntegral_compl_closedBall_lt_top hfac⟩

lemma ofReal_periodCovolume : ENNReal.ofReal W.periodCovolume = 2 * W.complexPeriodLIntegral := by
  rw [periodCovolume, ENNReal.ofReal_mul zero_le_two,
    ENNReal.ofReal_toReal W.complexPeriodLIntegral_lt_top.ne, ENNReal.ofReal_ofNat]

/-- **The covolume of the period lattice of an elliptic curve is positive.** -/
lemma periodCovolume_pos : 0 < W.periodCovolume :=
  mul_pos two_pos <| ENNReal.toReal_pos W.complexPeriodLIntegral_pos.ne'
    W.complexPeriodLIntegral_lt_top.ne

/-- **The complex period of an elliptic curve is positive.** -/
lemma complexPeriod_pos : 0 < W.complexPeriod :=
  mul_pos two_pos W.periodCovolume_pos

end WeierstrassCurve
