import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The `K`-Bessel function

For `x > 0` and `ν ∈ ℂ`, the `K`-Bessel function (the modified Bessel function of the second
kind) is `K_ν(x) = ½ ∫₀^∞ t^(ν - 1) e^(-(x/2)(t + 1/t)) dt`.

## Main definitions

* `Complex.besselK` (LMFDB `specialfunction.k_bessel`).

## Main results

* `Complex.integrableOn_besselKIntegrand`: the defining integral converges for every `ν ∈ ℂ` and
  `x > 0`.
* `Complex.besselK_neg`: `K_{-ν}(x) = K_ν(x)`.
* `Complex.conj_besselK_I_mul`: `K_{ir}(x)` is real for real `r`, as in the Fourier expansions of
  Maass forms.
-/

open MeasureTheory Real Set
open scoped ComplexConjugate Nat

namespace Complex

variable (ν : ℂ) (x : ℝ) (m : ℕ) {t : ℝ}

variable (t) in
/-- The integrand `t ↦ t^(ν - 1) e^(-(x/2)(t + 1/t))` of the `K`-Bessel function `K_ν(x)`. -/
noncomputable def besselKIntegrand : ℂ :=
  (t : ℂ) ^ (ν - 1) * (rexp (-(x / 2) * (t + t⁻¹)) : ℂ)

/-- The **`K`-Bessel function** (LMFDB `specialfunction.k_bessel`)
`K_ν(x) = ½ ∫₀^∞ t^(ν - 1) e^(-(x/2)(t + 1/t)) dt` of order `ν ∈ ℂ` at `x ∈ ℝ`; the integral
converges for `x > 0` (`integrableOn_besselKIntegrand`), where the LMFDB defines it. -/
noncomputable def besselK : ℂ :=
  2⁻¹ * ∫ t in Ioi 0, besselKIntegrand ν x t

variable {x} in
lemma norm_besselKIntegrand (ht : 0 < t) :
    ‖besselKIntegrand ν x t‖ = t ^ (ν.re - 1) * rexp (-(x / 2) * (t + t⁻¹)) := by
  rw [besselKIntegrand, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re, norm_real,
    norm_of_nonneg (exp_pos _).le]

private lemma exp_neg_div_le {a : ℝ} (ha : 0 < a) (ht : 0 < t) :
    rexp (-(a / t)) ≤ m ! / a ^ m * t ^ m := by
  rw [Real.exp_neg, inv_le_comm₀ (exp_pos _) (by positivity)]
  refine le_of_eq_of_le ?_ (Real.pow_div_factorial_le_exp _ (div_pos ha ht).le m)
  rw [div_pow]
  field_simp

variable {x} in
private lemma norm_besselKIntegrand_le (hx : 0 < x) (ht : 0 < t) :
    ‖besselKIntegrand ν x t‖ ≤ m ! / (x / 2) ^ m * (t ^ (ν.re - 1 + m) * rexp (-(x / 2) * t)) := by
  have h : rexp (-(x / 2) * (t + t⁻¹)) = rexp (-(x / 2) * t) * rexp (-(x / 2 / t)) :=
    (congrArg rexp (by ring1)).trans <| Real.exp_add _ _
  rw [norm_besselKIntegrand ν ht, h, rpow_add ht, rpow_natCast]
  refine (le_of_eq_of_le ?_ <| mul_le_mul_of_nonneg_left (exp_neg_div_le m (half_pos hx) ht) <|
    mul_nonneg (rpow_nonneg ht.le (ν.re - 1)) (exp_pos (-(x / 2) * t)).le).trans_eq ?_ <;> ring1

variable {x} in
/-- **The defining integral of `K_ν(x)` converges** for every `ν ∈ ℂ` and `x > 0`: near `0` the
factor `e^(-x/(2t))` beats every power of `t`, and near `∞` the factor `e^(-xt/2)` does. -/
lemma integrableOn_besselKIntegrand (hx : 0 < x) : IntegrableOn (besselKIntegrand ν x) (Ioi 0) := by
  have hm : -1 < ν.re - 1 + (⌈-ν.re⌉₊ + 1 : ℕ) := by
    push_cast
    linarith [Nat.le_ceil (-ν.re)]
  have hg :
      IntegrableOn (fun t ↦ t ^ (ν.re - 1 + (⌈-ν.re⌉₊ + 1 : ℕ)) * rexp (-(x / 2) * t)) (Ioi 0) := by
    simpa only [rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow hm one_pos (half_pos hx)
  refine Integrable.mono' (hg.const_mul _) ?_ <| (ae_restrict_iff' measurableSet_Ioi).mpr <|
    .of_forall fun t ht ↦ norm_besselKIntegrand_le ν _ hx ht
  refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ContinuousAt.continuousWithinAt ?_)
    measurableSet_Ioi
  have ht : t ≠ 0 := (mem_Ioi.mp ht).ne'
  refine (continuousAt_ofReal_cpow_const t (ν - 1) (Or.inr ht)).mul ?_
  fun_prop (disch := assumption)

/-- **`K_{-ν}(x) = K_ν(x)`**, by the substitution `t ↦ 1/t` in the defining integral. -/
lemma besselK_neg : besselK (-ν) x = besselK ν x := by
  rw [besselK, besselK,
    ← integral_comp_rpow_Ioi (besselKIntegrand ν x) (neg_ne_zero.mpr one_ne_zero)]
  refine congrArg _ <| setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  have ht : 0 < t := ht
  rw [besselKIntegrand, besselKIntegrand, abs_neg, abs_one, one_mul, rpow_neg_one, inv_inv,
    add_comm t⁻¹, real_smul, ofReal_cpow ht.le, ofReal_inv, inv_cpow _ _ (by
      rw [arg_ofReal_of_nonneg ht.le]
      exact pi_ne_zero.symm), ← cpow_neg, ← mul_assoc, ← cpow_add _ _ (ofReal_ne_zero.mpr ht.ne')]
  push_cast
  congr 2
  ring1

lemma conj_besselK : conj (besselK ν x) = besselK (conj ν) x := by
  rw [besselK, besselK, map_mul, ← integral_conj, map_inv₀, map_ofNat]
  refine congrArg _ <| setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  have h : conj ν - 1 = conj (ν - 1) := by rw [map_sub, map_one]
  rw [besselKIntegrand, besselKIntegrand, map_mul, h, cpow_conj _ _ (by
    rw [arg_ofReal_of_nonneg (mem_Ioi.mp ht).le]
    exact pi_ne_zero.symm), conj_ofReal, conj_ofReal]

/-- **`K_{ir}(x)` is real** for real `r`: it is its own complex conjugate, by `besselK_neg`. -/
lemma conj_besselK_I_mul (r : ℝ) : conj (besselK (I * r) x) = besselK (I * r) x := by
  rw [conj_besselK, map_mul, conj_I, conj_ofReal, neg_mul, besselK_neg]

end Complex
