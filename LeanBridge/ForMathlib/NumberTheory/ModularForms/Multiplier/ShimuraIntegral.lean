import LeanBridge.ForMathlib.Analysis.SpecialFunctions.ExpAddInvIntegral
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraKernel
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The integral behind the Fourier coefficients of the Shimura lift

Let `v, n > 0` and `b` be a nonzero integer. For `l ≥ 0` let

`J_l = ∫₀^∞ y ^ (-3/2) e^{-4 π b² y - π v² n² / (4 y)}
  G_l(-i v b y + i v² n / 4, v² y / (16 π)) dy`,

where `G_l(α, β)` is the coefficient of `s ^ l` in `exp(α s + β s²)`. Then `J_l = 0` for `b > 0` and
`l ≥ 1`, while `J_l = (2 / (v n)) e^{-2 π v n |b|} (i v² n / 2) ^ l / l!` for `b < 0`. This is what
makes the theta lift holomorphic in `w` when `l ≥ 1`, and what produces the factor `n ^ (l - 1)` of
the Shimura lift.

The proof computes the generating function: at `s = i τ`, `τ` real and small, the sum over `l` of
the integrands is `exp(-v² n τ / 4)` times the integrand
`y ^ (-3/2) e^{-4 π (b - v τ / 8 π)² y - π v² n² / (4 y)}` of `K_{1/2}`, which is known in closed
form (`MeasureTheory.integral_rpow_neg_mul_exp_neg_add_div`).

## Main results

* `ModularForm.integral_mul_gaussCoeff_of_pos`: `J_l = 0` for `b > 0` and `l ≥ 1`.
* `ModularForm.integral_mul_gaussCoeff_of_neg`: the value of `J_l` for `b < 0`.
-/

open Complex MeasureTheory Set

open scoped Real Nat

namespace ModularForm

variable {v n : ℝ} {b : ℤ} (l : ℕ)

lemma continuous_gaussCoeff : Continuous fun p : ℂ × ℂ ↦ gaussCoeff l p.1 p.2 := by
  unfold gaussCoeff
  fun_prop

variable (v n b) in
/-- The weight `y ^ (-3/2) e^{-4 π b² y - π v² n² / (4 y)}`. -/
private noncomputable def intWeight (y : ℝ) : ℝ :=
  y ^ (-(3 / 2) : ℝ) * Real.exp (-(4 * π * (b : ℝ) ^ 2 * y) - π * v ^ 2 * n ^ 2 / 4 / y)

variable (v n b) in
private noncomputable def intAlpha (y : ℝ) : ℂ :=
  -I * v * b * y + I * (v : ℂ) ^ 2 * n / 4

variable (v) in
private noncomputable def intBeta (y : ℝ) : ℝ :=
  v ^ 2 * y / (16 * π)

variable (v n b) in
private noncomputable def intF (y : ℝ) : ℂ :=
  (intWeight v n b y : ℂ) * gaussCoeff l (intAlpha v n b y) (intBeta v y)

private lemma continuousOn_intF : ContinuousOn (intF v n b l) (Ioi 0) := by
  refine fun y hy ↦ ContinuousAt.continuousWithinAt ?_
  have hy' : y ≠ 0 := (mem_Ioi.mp hy).ne'
  have h1 : ContinuousAt (intWeight v n b) y := by
    refine (Real.continuousAt_rpow_const y _ (Or.inl hy')).mul ?_
    exact Real.continuous_exp.continuousAt.comp (by fun_prop (disch := assumption))
  have h2 : ContinuousAt (fun y : ℝ ↦ gaussCoeff l (intAlpha v n b y) (intBeta v y)) y := by
    refine (continuous_gaussCoeff l).continuousAt.comp (f := fun y : ℝ ↦
      (intAlpha v n b y, ((intBeta v y : ℝ) : ℂ))) ?_
    refine ContinuousAt.prodMk ?_ ?_
    · unfold intAlpha
      fun_prop
    · unfold intBeta
      fun_prop
  exact (continuous_ofReal.continuousAt.comp h1).mul h2

private lemma norm_intAlpha_le {y : ℝ} (hv : 0 < v) (hn : 0 < n) (hy : 0 < y) :
    ‖intAlpha v n b y‖ ≤ v * |(b : ℝ)| * y + v ^ 2 * n / 4 := by
  have h1 : ‖-I * (v : ℂ) * (b : ℂ) * (y : ℂ)‖ = v * |(b : ℝ)| * y := by
    simp [abs_of_pos hv, abs_of_pos hy]
  have h2 : ‖I * (v : ℂ) ^ 2 * (n : ℂ) / 4‖ = v ^ 2 * n / 4 := by
    simp [abs_of_pos hn]
  rw [intAlpha, ← h1, ← h2]
  exact norm_add_le _ _

variable (v n b) in
/-- The exponent `B` of the majorant at `s = i τ`. -/
private noncomputable def majExp (τ : ℝ) : ℝ :=
  4 * π * (b : ℝ) ^ 2 - 2 * |τ| * v * |(b : ℝ)| - τ ^ 2 * v ^ 2 / (4 * π)

private lemma one_le_abs_cast (hb : b ≠ 0) : (1 : ℝ) ≤ |(b : ℝ)| := by
  exact_mod_cast Int.one_le_abs hb

private lemma majExp_pos (hb : b ≠ 0) {τ : ℝ} (hv : 0 < v) (hτ : |τ| < 1 / v) :
    0 < majExp v b τ := by
  have hp : 3 < π := Real.pi_gt_three
  have h1 : (1 : ℝ) ≤ |(b : ℝ)| := one_le_abs_cast hb
  have h2 : |τ| * v < 1 := by
    rwa [lt_div_iff₀ hv] at hτ
  have h3 : 0 ≤ |τ| * v := by positivity
  have h4 : (b : ℝ) ^ 2 = |(b : ℝ)| ^ 2 := (sq_abs _).symm
  have h5 : τ ^ 2 * v ^ 2 / (4 * π) ≤ 1 := by
    have e : τ ^ 2 * v ^ 2 = (|τ| * v) ^ 2 := by
      rw [mul_pow, sq_abs]
    rw [e, div_le_one (by positivity)]
    nlinarith
  rw [majExp, h4]
  nlinarith

variable (v n b) in
/-- The majorant of the `l`-th term of the series in `l` at `s = i τ`. -/
private noncomputable def intMaj (τ y : ℝ) : ℝ :=
  Real.exp (|τ| * v ^ 2 * n / 2) *
    (y ^ (-(3 / 2) : ℝ) * Real.exp (-(majExp v b τ * y) - π * v ^ 2 * n ^ 2 / 4 / y))

private lemma integrableOn_intMaj (hb : b ≠ 0) {τ : ℝ} (hv : 0 < v) (hn : 0 < n)
    (hτ : |τ| < 1 / v) : IntegrableOn (intMaj v n b τ) (Ioi 0) := by
  have hp : 0 < π := Real.pi_pos
  exact (integrableOn_rpow_neg_mul_exp_neg_add_div (majExp_pos hb hv hτ)
    (by positivity)).const_mul _

private lemma norm_intF_mul_le {τ y : ℝ} (hv : 0 < v) (hn : 0 < n) (hy : 0 < y) :
    ‖intF v n b l y * (I * τ) ^ l‖ ≤ (1 / 2) ^ l * intMaj v n b τ y := by
  have hp : 0 < π := Real.pi_pos
  have hr : (0 : ℝ) ≤ 2 * |τ| := by positivity
  have h1 : ‖gaussCoeff l (intAlpha v n b y) (intBeta v y)‖ * (2 * |τ|) ^ l ≤
      Real.exp (‖intAlpha v n b y‖ * (2 * |τ|) + ‖(intBeta v y : ℂ)‖ * (2 * |τ|) ^ 2) :=
    norm_gaussCoeff_mul_pow_le l (intAlpha v n b y) (intBeta v y : ℂ) hr
  have hβ : ‖((intBeta v y : ℝ) : ℂ)‖ = intBeta v y := by
    rw [norm_real, Real.norm_of_nonneg]
    rw [intBeta]
    positivity
  rw [hβ] at h1
  have h2 : ‖intF v n b l y * (I * τ) ^ l‖ = (1 / 2) ^ l * (intWeight v n b y *
      (‖gaussCoeff l (intAlpha v n b y) (intBeta v y)‖ * (2 * |τ|) ^ l)) := by
    have e : ‖(I * (τ : ℂ)) ^ l‖ = |τ| ^ l := by
      rw [norm_pow, norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]
    have hw : 0 ≤ intWeight v n b y := by
      rw [intWeight]
      positivity
    rw [intF, norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hw, e, mul_pow]
    have e2 : (1 / 2 : ℝ) ^ l * 2 ^ l = 1 := by
      rw [← mul_pow]
      norm_num
    linear_combination (-(intWeight v n b y * ‖gaussCoeff l (intAlpha v n b y) (intBeta v y)‖ *
      |τ| ^ l)) * e2
  rw [h2]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (mul_le_mul_of_nonneg_left h1 (by rw [intWeight]; positivity)).trans ?_
  have h4 : ‖intAlpha v n b y‖ * (2 * |τ|) ≤ (v * |(b : ℝ)| * y + v ^ 2 * n / 4) * (2 * |τ|) :=
    mul_le_mul_of_nonneg_right (norm_intAlpha_le (b := b) hv hn hy) hr
  rw [intWeight, intMaj, mul_left_comm (Real.exp _), mul_assoc, ← Real.exp_add, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  rw [majExp, intBeta]
  have e : (2 * |τ|) ^ 2 = 4 * τ ^ 2 := by
    rw [mul_pow, sq_abs]
    norm_num
  rw [e]
  have e2 : v ^ 2 * y / (16 * π) * (4 * τ ^ 2) = τ ^ 2 * v ^ 2 / (4 * π) * y := by
    field_simp
    norm_num
  rw [e2]
  nlinarith

private lemma integrable_intF_mul (hb : b ≠ 0) {τ : ℝ} (hv : 0 < v) (hn : 0 < n)
    (hτ : |τ| < 1 / v) : IntegrableOn (fun y ↦ intF v n b l y * (I * τ) ^ l) (Ioi 0) := by
  refine ((integrableOn_intMaj hb hv hn hτ).const_mul ((1 / 2) ^ l)).mono' ?_ <|
    (ae_restrict_iff' measurableSet_Ioi).mpr <| .of_forall fun y hy ↦ norm_intF_mul_le l hv hn hy
  exact ((continuousOn_intF l).mul continuousOn_const).aestronglyMeasurable measurableSet_Ioi

private lemma hasSum_integral_intF (hb : b ≠ 0) {τ : ℝ} (hv : 0 < v) (hn : 0 < n)
    (hτ : |τ| < 1 / v) : HasSum (fun l ↦ (∫ y in Ioi (0 : ℝ), intF v n b l y) * (I * τ) ^ l)
      (∫ y in Ioi (0 : ℝ), ∑' l, intF v n b l y * (I * τ) ^ l) := by
  have hsum : Summable fun l ↦ ∫ y in Ioi (0 : ℝ), ‖intF v n b l y * (I * τ) ^ l‖ := by
    have hg : Summable fun l : ℕ ↦ (1 / 2 : ℝ) ^ l * ∫ y in Ioi (0 : ℝ), intMaj v n b τ y :=
      summable_geometric_two.mul_right _
    refine Summable.of_nonneg_of_le (fun l ↦ integral_nonneg fun y ↦ norm_nonneg _) (fun l ↦ ?_) hg
    rw [← integral_const_mul]
    refine setIntegral_mono_on (integrable_intF_mul l hb hv hn hτ).norm
      ((integrableOn_intMaj hb hv hn hτ).const_mul _) measurableSet_Ioi fun y hy ↦ ?_
    exact norm_intF_mul_le l hv hn hy
  simpa only [integral_mul_const] using hasSum_integral_of_summable_integral_norm
    (fun l ↦ integrable_intF_mul l hb hv hn hτ) hsum

private lemma tsum_intF_mul (y τ : ℝ) : ∑' l, intF v n b l y * (I * τ) ^ l =
    ((intWeight v n b y * Real.exp (v * b * τ * y - v ^ 2 * n * τ / 4 -
      v ^ 2 * y / (16 * π) * τ ^ 2) : ℝ) : ℂ) := by
  have e : (fun l ↦ (intWeight v n b y : ℂ) * (gaussCoeff l (intAlpha v n b y) (intBeta v y) *
      (I * τ) ^ l)) = fun l ↦ intF v n b l y * (I * τ) ^ l := by
    funext l
    rw [intF, mul_assoc]
  rw [← e, ((hasSum_gaussCoeff_mul_pow (intAlpha v n b y) (intBeta v y : ℂ) (I * τ)).mul_left
    (intWeight v n b y : ℂ)).tsum_eq]
  push_cast
  congr 2
  simp only [intAlpha, intBeta]
  push_cast
  linear_combination
    (-(v : ℂ) * b * τ * y + (v : ℂ) ^ 2 * n * τ / 4 + (v : ℂ) ^ 2 * y / (16 * π) * τ ^ 2) * I_sq

private lemma integral_tsum_intF_mul (hb : b ≠ 0) {τ : ℝ} (hv : 0 < v) (hn : 0 < n)
    (hτ : |τ| < 1 / v) : ∫ y in Ioi (0 : ℝ), ∑' l, intF v n b l y * (I * τ) ^ l =
      ((Real.exp (-(v ^ 2 * n * τ / 4)) * (2 / (v * n) *
        Real.exp (-(2 * π * v * n * |(b : ℝ) - v * τ / (8 * π)|))) : ℝ) : ℂ) := by
  have hp : 0 < π := Real.pi_pos
  have hT : 0 < π * v ^ 2 * n ^ 2 / 4 := by positivity
  have hD : 0 < |(b : ℝ) - v * τ / (8 * π)| := by
    refine abs_pos.mpr fun h0 ↦ ?_
    have h1 : (1 : ℝ) ≤ |(b : ℝ)| := one_le_abs_cast hb
    have h2 : |τ| * v < 1 := by
      rwa [lt_div_iff₀ hv] at hτ
    have h3 : (b : ℝ) = v * τ / (8 * π) := by linarith
    have h4 : |v * τ / (8 * π)| ≤ |τ| * v := by
      have hp3 : 3 < π := Real.pi_gt_three
      rw [abs_div, abs_mul, abs_of_pos hv, abs_of_pos (by positivity : (0 : ℝ) < 8 * π), mul_comm v]
      exact div_le_self (by positivity) (by nlinarith)
    rw [h3] at h1
    linarith
  have hA : 0 < 4 * π * ((b : ℝ) - v * τ / (8 * π)) ^ 2 := by
    have h : 0 < |(b : ℝ) - v * τ / (8 * π)| ^ 2 := sq_pos_of_pos hD
    rw [sq_abs] at h
    positivity
  simp_rw [tsum_intF_mul]
  rw [integral_complex_ofReal]
  congr 1
  have h1 : ∀ y ∈ Ioi (0 : ℝ), intWeight v n b y * Real.exp (v * b * τ * y - v ^ 2 * n * τ / 4 -
      v ^ 2 * y / (16 * π) * τ ^ 2) = Real.exp (-(v ^ 2 * n * τ / 4)) * (y ^ (-(3 / 2) : ℝ) *
        Real.exp (-(4 * π * ((b : ℝ) - v * τ / (8 * π)) ^ 2 * y) - π * v ^ 2 * n ^ 2 / 4 / y)) := by
    intro y hy
    have hy0 : y ≠ 0 := (mem_Ioi.mp hy).ne'
    rw [intWeight, mul_assoc, mul_left_comm (Real.exp _), ← Real.exp_add, ← Real.exp_add]
    congr 2
    field_simp
    ring1
  rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_const_mul,
    integral_rpow_neg_mul_exp_neg_add_div hA hT]
  have h2 : Real.sqrt (π / (π * v ^ 2 * n ^ 2 / 4)) = 2 / (v * n) := by
    have e : π / (π * v ^ 2 * n ^ 2 / 4) = (2 / (v * n)) ^ 2 := by
      field_simp
      norm_num
    rw [e, Real.sqrt_sq (by positivity)]
  have h3 : Real.sqrt (4 * π * ((b : ℝ) - v * τ / (8 * π)) ^ 2 * (π * v ^ 2 * n ^ 2 / 4)) =
      π * v * n * |(b : ℝ) - v * τ / (8 * π)| := by
    have e : 4 * π * ((b : ℝ) - v * τ / (8 * π)) ^ 2 * (π * v ^ 2 * n ^ 2 / 4) =
        (π * v * n * |(b : ℝ) - v * τ / (8 * π)|) ^ 2 := by
      rw [mul_pow, sq_abs]
      ring1
    rw [e, Real.sqrt_sq (by positivity)]
  rw [h2, h3]
  congr 3
  ring1

private lemma coeff_eq_of_hasSum {J R : ℕ → ℂ} {K : ℝ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hJ : ∀ τ : ℝ, |τ| < ε → HasSum (fun l ↦ J l * (I * τ) ^ l) (K τ))
    (hR : ∀ τ : ℝ, |τ| < ε → HasSum (fun l ↦ R l * (I * τ) ^ l) (K τ)) : J l = R l := by
  have h : (fun l ↦ (J l - R l) * I ^ l) = 0 := eq_zero_of_hasSum_ofReal hε fun τ hτ ↦ by
    have h1 : HasSum (fun l ↦ J l * (I * τ) ^ l - R l * (I * τ) ^ l) (K τ - K τ) :=
      (hJ τ hτ).sub (hR τ hτ)
    rw [sub_self] at h1
    convert h1 using 2 with l
    rw [mul_pow]
    ring1
  have h2 : (J l - R l) * I ^ l = (0 : ℕ → ℂ) l := congrFun h l
  simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', I_ne_zero, false_and, or_false] at h2
  exact sub_eq_zero.mp h2

/-- **The integral `J_l` vanishes for `b > 0` and `l ≥ 1`.** -/
lemma integral_mul_gaussCoeff_of_pos (hb : 0 < b) (hv : 0 < v) (hn : 0 < n) (hl : l ≠ 0) :
    ∫ y in Ioi (0 : ℝ), ((y ^ (-(3 / 2) : ℝ) * Real.exp (-(4 * π * (b : ℝ) ^ 2 * y) -
      π * v ^ 2 * n ^ 2 / 4 / y) : ℝ) : ℂ) * gaussCoeff l (-I * v * b * y + I * (v : ℂ) ^ 2 * n / 4)
        ((v ^ 2 * y / (16 * π) : ℝ) : ℂ) = 0 := by
  have hb0 : b ≠ 0 := hb.ne'
  have hp : 3 < π := Real.pi_gt_three
  refine (coeff_eq_of_hasSum l (ε := 1 / v) (J := fun l ↦ ∫ y in Ioi (0 : ℝ), intF v n b l y)
    (R := fun l ↦ if l = 0 then ((2 / (v * n) * Real.exp (-(2 * π * v * n * b)) : ℝ) : ℂ) else 0)
    (K := fun _ ↦ ((2 / (v * n) * Real.exp (-(2 * π * v * n * b)) : ℝ) : ℂ)) (by positivity)
    (fun τ hτ ↦ ?_) (fun τ _ ↦ ?_)).trans (by simp [hl])
  · have h : HasSum (fun l ↦ (∫ y in Ioi (0 : ℝ), intF v n b l y) * (I * τ) ^ l)
        (∫ y in Ioi (0 : ℝ), ∑' l, intF v n b l y * (I * τ) ^ l) :=
      hasSum_integral_intF hb0 hv hn hτ
    rw [integral_tsum_intF_mul hb0 hv hn hτ] at h
    have h1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    have h2 : |τ| * v < 1 := by
      rwa [lt_div_iff₀ hv] at hτ
    have h3 : v * τ / (8 * π) < 1 := by
      have h4 : v * τ ≤ |τ| * v := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (le_abs_self τ) hv.le
      rw [div_lt_one (by positivity)]
      linarith
    have h5 : |(b : ℝ) - v * τ / (8 * π)| = (b : ℝ) - v * τ / (8 * π) :=
      abs_of_pos (by linarith)
    have e : Real.exp (-(v ^ 2 * n * τ / 4)) * (2 / (v * n) *
        Real.exp (-(2 * π * v * n * |(b : ℝ) - v * τ / (8 * π)|))) =
          2 / (v * n) * Real.exp (-(2 * π * v * n * b)) := by
      rw [h5, mul_left_comm, ← Real.exp_add]
      congr 2
      field_simp
      ring1
    rwa [e] at h
  · convert hasSum_ite_eq (0 : ℕ) ((2 / (v * n) * Real.exp (-(2 * π * v * n * b)) : ℝ) : ℂ)
      using 2 with l
    split_ifs with h0
    · rw [h0]
      simp
    · simp

/-- **The value of the integral `J_l` for `b < 0`**: it is
`(2 / (v n)) e^{-2 π v n |b|} (i v² n / 2) ^ l / l!`. -/
lemma integral_mul_gaussCoeff_of_neg (hb : b < 0) (hv : 0 < v) (hn : 0 < n) : ∫ y in Ioi (0 : ℝ),
    ((y ^ (-(3 / 2) : ℝ) * Real.exp (-(4 * π * (b : ℝ) ^ 2 * y) -
      π * v ^ 2 * n ^ 2 / 4 / y) : ℝ) : ℂ) * gaussCoeff l (-I * v * b * y + I * (v : ℂ) ^ 2 * n / 4)
        ((v ^ 2 * y / (16 * π) : ℝ) : ℂ) =
          ((2 / (v * n) * Real.exp (-(2 * π * v * n * |(b : ℝ)|)) : ℝ) : ℂ) *
            ((I * (v : ℂ) ^ 2 * n / 2) ^ l / (l ! : ℂ)) := by
  have hb0 : b ≠ 0 := hb.ne
  have hp : 3 < π := Real.pi_gt_three
  refine coeff_eq_of_hasSum l (ε := 1 / v) (J := fun l ↦ ∫ y in Ioi (0 : ℝ), intF v n b l y)
    (R := fun l ↦ ((2 / (v * n) * Real.exp (-(2 * π * v * n * |(b : ℝ)|)) : ℝ) : ℂ) *
      ((I * (v : ℂ) ^ 2 * n / 2) ^ l / (l ! : ℂ)))
    (K := fun τ ↦ ((2 / (v * n) * Real.exp (-(2 * π * v * n * |(b : ℝ)|)) *
      Real.exp (-(v ^ 2 * n * τ / 2)) : ℝ) : ℂ)) (by positivity) (fun τ hτ ↦ ?_) (fun τ _ ↦ ?_)
  · have h : HasSum (fun l ↦ (∫ y in Ioi (0 : ℝ), intF v n b l y) * (I * τ) ^ l)
        (∫ y in Ioi (0 : ℝ), ∑' l, intF v n b l y * (I * τ) ^ l) :=
      hasSum_integral_intF hb0 hv hn hτ
    rw [integral_tsum_intF_mul hb0 hv hn hτ] at h
    have h1 : (b : ℝ) ≤ -1 := by
      have h2 : b ≤ -1 := by omega
      exact_mod_cast h2
    have h2 : |τ| * v < 1 := by
      rwa [lt_div_iff₀ hv] at hτ
    have h3 : -(v * τ / (8 * π)) < 1 := by
      have h4 : -(v * τ) ≤ |τ| * v := by
        linarith [mul_le_mul_of_nonneg_right (neg_le_abs τ) hv.le]
      rw [← neg_div, div_lt_one (by positivity)]
      linarith
    have h5 : |(b : ℝ) - v * τ / (8 * π)| = |(b : ℝ)| + v * τ / (8 * π) := by
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
      ring1
    have e : Real.exp (-(v ^ 2 * n * τ / 4)) * (2 / (v * n) *
        Real.exp (-(2 * π * v * n * |(b : ℝ) - v * τ / (8 * π)|))) =
          2 / (v * n) * Real.exp (-(2 * π * v * n * |(b : ℝ)|)) *
            Real.exp (-(v ^ 2 * n * τ / 2)) := by
      have h6 : Real.exp (-(v ^ 2 * n * τ / 4)) *
          Real.exp (-(2 * π * v * n * |(b : ℝ) - v * τ / (8 * π)|)) =
            Real.exp (-(2 * π * v * n * |(b : ℝ)|)) * Real.exp (-(v ^ 2 * n * τ / 2)) := by
        rw [h5, ← Real.exp_add, ← Real.exp_add]
        congr 1
        field_simp
        ring1
      linear_combination (2 / (v * n)) * h6
    rwa [e] at h
  · have h1 : HasSum (fun l : ℕ ↦ (I * (v : ℂ) ^ 2 * n / 2 * (I * τ)) ^ l / (l ! : ℂ))
        (cexp (I * (v : ℂ) ^ 2 * n / 2 * (I * τ))) := by
      rw [Complex.exp_eq_exp_ℂ]
      exact NormedSpace.expSeries_div_hasSum_exp _
    have e1 :
        cexp (I * (v : ℂ) ^ 2 * n / 2 * (I * τ)) = ((Real.exp (-(v ^ 2 * n * τ / 2)) : ℝ) : ℂ) := by
      push_cast
      congr 1
      linear_combination ((v : ℂ) ^ 2 * n * τ / 2) * I_sq
    rw [e1] at h1
    convert h1.mul_left ((2 / (v * n) * Real.exp (-(2 * π * v * n * |(b : ℝ)|)) : ℝ) : ℂ)
      using 2 with l
    · rw [mul_pow]
      ring1
    · push_cast
      rfl

end ModularForm
