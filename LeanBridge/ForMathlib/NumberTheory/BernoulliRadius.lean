import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ZetaValues

/-!
# The radius of convergence of the Bernoulli series

The Bernoulli numbers `Bₙ` (LMFDB `af.bernoulli_numbers`, Mathlib's `bernoulli`, with
`B₁ = -1/2`) are the coefficients of the formal power series
`T / (e^T - 1) = ∑ Bₙ Tⁿ / n!` (Mathlib's `bernoulliPowerSeries` and
`bernoulliPowerSeries_mul_exp_sub_one`). This power series has radius of convergence `2π`
(`radius_bernoulliSeries`). Indeed `B₂ₖ` is given by `ζ(2k)` (Mathlib's `hasSum_zeta_nat`):
`|B₂ₖ| / (2k)! = 2 ζ(2k) / (2π)^{2k}` for `k ≥ 1`, with `1 ≤ ζ(2k) ≤ ζ(2) = π² / 6 ≤ 2`, while
`B₁ = -1/2` and `Bₙ = 0` for odd `n ≥ 3`. So `|Bₙ / n!| rⁿ` is bounded for `r < 2π` and unbounded
for `r > 2π`.

## Main definitions

* `bernoulliSeries` (LMFDB `af.bernoulli_numbers`): the power series `∑ Bₙ Tⁿ / n!` over `ℂ`, as
  a formal multilinear series.

## Main results

* `radius_bernoulliSeries` (LMFDB `af.bernoulli_numbers`): the power series `∑ Bₙ Tⁿ / n!` has
  radius of convergence `2π`.
-/

open FormalMultilinearSeries NNReal Real

open scoped Nat

/-- The power series `∑ Bₙ Tⁿ / n!` (LMFDB `af.bernoulli_numbers`) over `ℂ`, as a formal
multilinear series: its coefficients are those of Mathlib's `bernoulliPowerSeries ℂ`, the formal
power series of `T / (e^T - 1)`. -/
noncomputable def bernoulliSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  ofScalars ℂ fun n ↦ PowerSeries.coeff n (bernoulliPowerSeries ℂ)

lemma norm_bernoulliSeries (n : ℕ) : ‖bernoulliSeries n‖ = |((bernoulli n / n ! : ℚ) : ℝ)| := by
  rw [bernoulliSeries, ofScalars_norm, bernoulliPowerSeries, PowerSeries.coeff_mk, eq_ratCast,
    Complex.norm_ratCast]

variable {k : ℕ}

lemma one_le_bernoulli_zeta_formula (hk : k ≠ 0) :
    1 ≤ (-1 : ℝ) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k) / (2 * k)! := by
  simpa using le_hasSum (hasSum_zeta_nat hk) 1 fun j _ ↦ by positivity

lemma bernoulli_zeta_formula_le_two (hk : k ≠ 0) :
    (-1 : ℝ) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k) / (2 * k)! ≤ 2 := by
  refine (hasSum_le (fun n ↦ ?_) (hasSum_zeta_nat hk) hasSum_zeta_two).trans ?_
  · rcases n.eq_zero_or_pos with rfl | hn
    · simp [hk]
    · exact one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (by exact_mod_cast hn) (by omega))
  · nlinarith [pi_lt_d2, Real.pi_pos]

lemma abs_bernoulli_div_factorial_mul_two_pi_pow (hk : k ≠ 0) :
    |((bernoulli (2 * k) / (2 * k)! : ℚ) : ℝ)| * (2 * π) ^ (2 * k) =
      2 * ((-1 : ℝ) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k) / (2 * k)!) := by
  have h₁ : (0 : ℝ) < 2 ^ (2 * k - 1) * π ^ (2 * k) := by
    positivity
  have hc : (2 * π) ^ (2 * k) = 2 * (2 ^ (2 * k - 1) * π ^ (2 * k)) := by
    rw [mul_pow, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]
  have hT : (-1 : ℝ) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k) / (2 * k)! =
      2 ^ (2 * k - 1) * π ^ (2 * k) *
          ((-1) ^ (k + 1) * ((bernoulli (2 * k) / (2 * k)! : ℚ) : ℝ)) := by
    push_cast
    ring1
  rw [hc, ← abs_of_pos (zero_lt_one.trans_le (one_le_bernoulli_zeta_formula hk)), hT, abs_mul,
    abs_mul ((-1 : ℝ) ^ (k + 1)), abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos h₁]
  ring1

lemma norm_bernoulliSeries_mul_pow_le {r : ℝ≥0} (hr : (r : ℝ) < 2 * π) (n : ℕ) :
    ‖bernoulliSeries n‖ * (r : ℝ) ^ n ≤ 4 := by
  rw [norm_bernoulliSeries]
  rcases n.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rcases eq_or_ne k 0 with rfl | hk
    · norm_num
    · rw [← two_mul]
      have h₁ : (r : ℝ) ^ (2 * k) ≤ (2 * π) ^ (2 * k) := pow_le_pow_left₀ r.2 hr.le _
      refine (mul_le_mul_of_nonneg_left h₁ (abs_nonneg _)).trans ?_
      rw [abs_bernoulli_div_factorial_mul_two_pi_pow hk]
      linarith [bernoulli_zeta_formula_le_two hk]
  · rcases eq_or_ne k 0 with rfl | hk
    · norm_num
      nlinarith [pi_lt_d2, r.2]
    · rw [bernoulli_eq_zero_of_odd ⟨k, rfl⟩ (by omega)]
      norm_num

/-- **The power series `∑ Bₙ Tⁿ / n!` of `T / (e^T - 1)` has radius of convergence `2π`** (LMFDB
`af.bernoulli_numbers`): `|B₂ₖ| / (2k)! = 2 ζ(2k) / (2π)^{2k}` with `1 ≤ ζ(2k) ≤ 2` for `k ≥ 1`,
and the odd Bernoulli numbers vanish beyond `B₁`. -/
lemma radius_bernoulliSeries : bernoulliSeries.radius = ENNReal.ofReal (2 * π) := by
  refine le_antisymm ?_ (ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_)
  · by_contra! h
    rcases ENNReal.lt_iff_exists_nnreal_btwn.mp h with ⟨r, hr₁, hr₂⟩
    rcases bernoulliSeries.norm_mul_pow_le_of_lt_radius hr₂ with ⟨C, -, hC⟩
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff'] at hr₁
    have hq : 1 < ((r : ℝ) / (2 * π)) ^ 2 :=
      one_lt_pow₀ ((one_lt_div (by positivity)).mpr hr₁.1) two_ne_zero
    rcases pow_unbounded_of_one_lt (C / 2) hq with ⟨k, hk⟩
    have h₁ : ‖bernoulliSeries (2 * (k + 1))‖ * (r : ℝ) ^ (2 * (k + 1)) ≤ C := hC (2 * (k + 1))
    have h₂ : (((r : ℝ) / (2 * π)) ^ 2) ^ k ≤ (((r : ℝ) / (2 * π)) ^ 2) ^ (k + 1) :=
      pow_le_pow_right₀ hq.le k.le_succ
    have h₃ : |((bernoulli (2 * (k + 1)) / (2 * (k + 1))! : ℚ) : ℝ)| * (r : ℝ) ^ (2 * (k + 1)) =
        |((bernoulli (2 * (k + 1)) / (2 * (k + 1))! : ℚ) : ℝ)| * (2 * π) ^ (2 * (k + 1)) *
            (((r : ℝ) / (2 * π)) ^ 2) ^ (k + 1) := by
      rw [← pow_mul, div_pow, mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ (by positivity)]
    rw [norm_bernoulliSeries, h₃, abs_bernoulli_div_factorial_mul_two_pi_pow k.succ_ne_zero] at h₁
    have h₄ : (0 : ℝ) ≤ (((r : ℝ) / (2 * π)) ^ 2) ^ (k + 1) := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_right (one_le_bernoulli_zeta_formula k.succ_ne_zero) h₄]
  · rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hr
    exact bernoulliSeries.le_radius_of_bound 4 (norm_bernoulliSeries_mul_pow_le hr)
