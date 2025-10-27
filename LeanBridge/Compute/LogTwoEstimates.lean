/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Estimates on log base 2 of rationals by iterative squaring

This file was ported from https://github.com/b-mehta/exponential-ramsey/blob/main/src/log2_estimates.lean
The idea for the calculation is https://en.wikipedia.org/wiki/Binary_logarithm#Iterative_approximation
-/

noncomputable section

open Real

lemma logb_zpow {b x : ℝ} (m : ℤ) : logb b (x ^ m) = m * logb b x := by
  rw [logb, log_zpow, mul_div_assoc, logb]

lemma logb_div_base' {b x : ℝ} (hb : 0 < b) (hb' : b ≠ 1) (hx : x ≠ 0) :
    logb b (x / b) = logb b x - 1 := by
  rw [logb_div hx hb.ne', Real.logb_self_eq_one_iff.2]
  grind

/-- the form of goal which is used to prove log2 estimates -/
def log_base2_goal (x₁ x₂ a₁ a₂ : ℝ) : Prop :=
  0 < x₁ → x₁ ≤ x₂ → a₁ < logb 2 x₁ ∧ logb 2 x₂ < a₂

lemma log_base2_square {x₁ x₂ a₁ a₂ : ℝ} (h : log_base2_goal (x₁ ^ 2) (x₂ ^ 2) (2 * a₁) (2 * a₂)) :
    log_base2_goal x₁ x₂ a₁ a₂ := fun hx₁ hx₂ ↦ by
  simpa [logb_pow] using h (pow_pos hx₁ _) (pow_le_pow_left₀ hx₁.le hx₂ _)

-- TODO: change logb_le_logb_of_le to be consistent with log_le_log
-- TODO: change logb_le_logb_of_le to have 1 ≤ b
lemma log_base2_weaken {x₁ x₂ a₁ a₂ : ℝ} (x₃ x₄ : ℝ) (h : log_base2_goal x₃ x₄ a₁ a₂)
    (h₁ : x₃ ≤ x₁) (h₂ : x₂ ≤ x₄) (h₃ : 0 < x₃) :
    log_base2_goal x₁ x₂ a₁ a₂ := by
  intros hx₁ hx₂
  have t := h h₃ (h₁.trans (hx₂.trans h₂))
  exact ⟨t.1.trans_le (logb_le_logb_of_le one_lt_two h₃ h₁),
         t.2.trans_le' (logb_le_logb_of_le one_lt_two (hx₁.trans_le hx₂) h₂)⟩

lemma log_base2_half {x₁ x₂ a₁ a₂ : ℝ}
    (h : log_base2_goal (x₁ / 2) (x₂ / 2) (a₁ - 1) (a₂ - 1)) :
    log_base2_goal x₁ x₂ a₁ a₂ := fun hx₁ hx₂ ↦ by
  simpa [logb_div_base', hx₁.ne', show (2 : ℝ) ≠ 1 by norm_num, (hx₁.trans_le hx₂).ne'] using
    h (half_pos hx₁) (div_le_div_of_nonneg_right hx₂ zero_le_two)

lemma log_base2_scale {x₁ x₂ a₁ a₂ : ℝ} (m : ℤ)
    (h : log_base2_goal (x₁ * 2 ^ m) (x₂ * 2 ^ m) (a₁ + m) (a₂ + m)) :
  log_base2_goal x₁ x₂ a₁ a₂ := by
  intro hx₁ hx₂
  have i : 0 < (2 : ℝ)^m := zpow_pos zero_lt_two _
  have := h (mul_pos hx₁ i) (mul_le_mul_of_nonneg_right hx₂ i.le)
  simpa [logb_mul hx₁.ne' i.ne', logb_mul (hx₁.trans_le hx₂).ne' i.ne', logb_zpow,
    logb_self_eq_one_iff.2] using this

lemma log_base2_start {x₁ x₂ a₁ a₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : x₁ ≤ x₂)
    (h : log_base2_goal x₁ x₂ a₁ a₂) : a₁ < logb 2 x₁ ∧ logb 2 x₂ < a₂ :=
  h hx₁ hx₂

lemma log_base2_end {x₁ x₂ a₁ a₂ : ℝ} (hx₁ : 1 < x₁) (hx₂ : x₂ < 2) (ha₁ : a₁ ≤ 0) (ha₂ : 1 ≤ a₂) :
  log_base2_goal x₁ x₂ a₁ a₂ := by
  rintro - h
  refine ⟨ha₁.trans_lt (div_pos (log_pos hx₁) (log_pos one_lt_two)), lt_of_lt_of_le ?_ ha₂⟩
  rw [logb, div_lt_one (log_pos one_lt_two)]
  exact log_lt_log ((zero_le_one.trans_lt hx₁).trans_le h) hx₂

noncomputable def x_value2 : ℝ := 1 / (2 - 0.817)
lemma x_value2_eq : x_value2 = 1000 / 1183 := by norm_num [x_value2]

lemma logb_approx_second : -0.24246 < logb 2 x_value2 ∧ logb 2 x_value2 < -0.242435 := by
  rw [x_value2_eq]
  refine log_base2_start (by norm_num1) le_rfl ?_
  refine log_base2_scale 1 ?_
  rw [Int.cast_one]
  norm_num1
  refine log_base2_square ?_
  refine log_base2_half ?_
  refine log_base2_weaken 1.429093 1.429094 ?_ (by norm_num1) (by norm_num1) (by norm_num1)
  refine log_base2_square ?_
  refine log_base2_half ?_
  refine log_base2_weaken 1.021153 1.021155 ?_ (by norm_num1) (by norm_num1) (by norm_num1)
  refine log_base2_square ?_
  refine log_base2_weaken 1.042753 1.042758 ?_ (by norm_num1) (by norm_num1) (by norm_num1)
  refine log_base2_square ?_
  refine log_base2_weaken 1.087333 1.087345 ?_ (by norm_num1) (by norm_num1) (by norm_num1)
  refine log_base2_square ?_
  refine log_base2_weaken 1.182293 1.182320 ?_ (by norm_num1) (by norm_num1) (by norm_num1)
  refine log_base2_square ?_
  refine log_base2_weaken 1.397816 1.397890 ?_ (by norm_num1) (by norm_num1) (by norm_num1)
  refine log_base2_square ?_
  refine log_base2_weaken 1.95388 1.95410 ?_ (by norm_num1) (by norm_num1) (by norm_num1)
  refine log_base2_square ?_
  refine log_base2_half ?_
  refine log_base2_weaken 1.90882 1.90926 ?_ (by norm_num1) (by norm_num1) (by norm_num1)
  refine log_base2_square ?_
  refine log_base2_half ?_
  refine log_base2_weaken 1.82179 1.82264 ?_ (by norm_num1) (by norm_num1) (by norm_num1)
  refine log_base2_square ?_
  refine log_base2_half ?_
  refine log_base2_weaken 1.65945 1.66101 ?_ (by norm_num1) (by norm_num1) (by norm_num1)
  refine log_base2_square ?_
  refine log_base2_half ?_
  refine log_base2_weaken 1.37688 1.37948 ?_ (by norm_num1) (by norm_num1) (by norm_num1)
  refine log_base2_square ?_
  refine log_base2_weaken 1.8957 1.90297 ?_ (by norm_num1) (by norm_num1) (by norm_num1)
  refine log_base2_square ?_
  refine log_base2_half ?_
  refine log_base2_weaken 1.7968 1.8107 ?_ (by norm_num1) (by norm_num1) (by norm_num1)
  refine log_base2_square ?_
  refine log_base2_half ?_
  refine log_base2_weaken 1.614 1.640 ?_ (by norm_num1) (by norm_num1) (by norm_num1)
  refine log_base2_square ?_
  refine log_base2_half ?_
  refine log_base2_weaken 1.30 1.35 ?_ (by norm_num1) (by norm_num1) (by norm_num1)
  refine log_base2_square ?_
  refine log_base2_weaken 1.5 1.9 ?_ (by norm_num1) (by norm_num1) (by norm_num1)
  refine log_base2_square ?_
  refine log_base2_half ?_
  norm_num1
  exact log_base2_end (by norm_num1) (by norm_num1) (by norm_num1) (by norm_num1)
end
