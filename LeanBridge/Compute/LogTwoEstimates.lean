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

section

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

section

variable {x₁ x₂ a₁ a₂ : ℚ}

def goalShape (x₁ x₂ a₁ a₂ : ℚ) : Prop :=
  0 < x₁ → x₁ ≤ x₂ → a₁ < logb 2 x₁ ∧ logb 2 x₂ < a₂

lemma goalShape_imp (h₁ : 0 < x₁) (h₂ : x₁ ≤ x₂) (h : goalShape x₁ x₂ a₁ a₂) :
    ∀ x : ℝ, x ∈ Set.Icc (x₁ : ℝ) x₂ → logb 2 x ∈ Set.Ioo (a₁ : ℝ) a₂ := by
  intro x hx
  have := h h₁ h₂
  simp only [Set.mem_Ioo]
  simp only [Set.mem_Icc] at hx
  have : 0 < x := hx.1.trans_lt' (by norm_cast)
  have : logb 2 x ≤ logb 2 x₂ := logb_le_logb_of_le one_lt_two this hx.2
  have := logb_le_logb_of_le one_lt_two (by positivity) hx.1
  grind

lemma goalShape_scale (m : ℕ)
    (h : goalShape (x₁ ^ (2 ^ m)) (x₂ ^ (2 ^ m)) (2 ^ m * a₁) (2 ^ m * a₂)) :
    goalShape x₁ x₂ a₁ a₂ := by
  intro hx₁ hx₂
  simpa [logb_pow] using h (by positivity) (by gcongr)

lemma goalShape_shift (m : ℤ) (h : goalShape (x₁ * 2 ^ m) (x₂ * 2 ^ m) (a₁ + m) (a₂ + m)) :
    goalShape x₁ x₂ a₁ a₂ := by
  intro hx₁ hx₂
  have h₁ : (0 : ℝ) < x₁ := by norm_cast
  have h₂ : (0 : ℝ) < x₂ := by norm_cast; order
  have h₃ : (2 : ℝ) ^ m ≠ 0 := by positivity
  simpa [logb_mul, ne_of_gt, h₁, h₂, h₃, logb_zpow] using h (by positivity) (by gcongr)

lemma goalShape_trivial (hx₁ : 1 < x₁) (hx₂ : x₂ < 2) (ha₁ : a₁ ≤ 0) (ha₂ : 1 ≤ a₂) :
    goalShape x₁ x₂ a₁ a₂ := by
  intro hx₁' hx₂'
  replace hx₁ : 0 < logb 2 x₁ := logb_pos one_lt_two (by norm_cast)
  replace hx₂ : logb 2 x₂ < 1 := by
    simpa using logb_lt_logb (y := 2) one_lt_two (by norm_cast; order) (by norm_cast)
  exact ⟨hx₁.trans_le' (by norm_cast), hx₂.trans_le (by norm_cast)⟩

lemma goalShape_weaken (x₁' x₂' : ℚ) (h₁ : x₁' ≤ x₁) (h₂ : x₂ ≤ x₂') (h₃ : 0 < x₁')
    (h : goalShape x₁' x₂' a₁ a₂) :
    goalShape x₁ x₂ a₁ a₂ := by
  intro hx₁ hx₂
  have := h h₃ (by order)
  have : logb 2 x₁' ≤ logb 2 x₁ :=
    logb_le_logb_of_le one_lt_two (by norm_cast) (by norm_cast)
  have : logb 2 x₂ ≤ logb 2 x₂' :=
    logb_le_logb_of_le one_lt_two (by norm_cast; order) (by norm_cast)
  grind

lemma logb_approx_second' : -0.242451 < logb 2 x_value2 ∧ logb 2 x_value2 < -0.242450 := by
  suffices goalShape (1000 / 1183) (1000 / 1183) (-0.242451) (-0.242450) by
    have := goalShape_imp (by norm_num1) (by norm_num1) this x_value2 (by norm_num [x_value2_eq])
    simpa using this
  apply goalShape_shift 1
  norm_num1
  apply goalShape_weaken 1.69061707 1.69061708 (by norm_num1) (by norm_num1) (by norm_num1)
  apply goalShape_scale 1
  apply goalShape_shift (-1)
  apply goalShape_weaken 1.42909303 1.42909306 (by norm_num1) (by norm_num1) (by norm_num1)
  apply goalShape_scale 1
  apply goalShape_shift (-1)
  apply goalShape_weaken 1.02115344 1.02115349 (by norm_num1) (by norm_num1) (by norm_num1)
  apply goalShape_scale 6
  apply goalShape_shift (-1)
  apply goalShape_weaken 1.90894891 1.90895490 (by norm_num1) (by norm_num1) (by norm_num1)
  apply goalShape_scale 1
  apply goalShape_shift (-1)
  apply goalShape_weaken 1.82204297 1.82205441 (by norm_num1) (by norm_num1) (by norm_num1)
  apply goalShape_scale 1
  apply goalShape_shift (-1)
  apply goalShape_weaken 1.65992029 1.65994114 (by norm_num1) (by norm_num1) (by norm_num1)
  apply goalShape_scale 1
  apply goalShape_shift (-1)
  apply goalShape_weaken 1.37766768 1.37770230 (by norm_num1) (by norm_num1) (by norm_num1)
  apply goalShape_scale 2
  apply goalShape_shift (-1)
  apply goalShape_weaken 1.80114171 1.80132277 (by norm_num1) (by norm_num1) (by norm_num1)
  apply goalShape_scale 1
  apply goalShape_shift (-1)
  apply goalShape_weaken 1.62205572 1.62238187 (by norm_num1) (by norm_num1) (by norm_num1)
  apply goalShape_scale 1
  apply goalShape_shift (-1)
  apply goalShape_weaken 1.31553237 1.31606147 (by norm_num1) (by norm_num1) (by norm_num1)
  apply goalShape_scale 2
  apply goalShape_shift (-1)
  apply goalShape_weaken 1.49753216 1.49994282 (by norm_num1) (by norm_num1) (by norm_num1)
  apply goalShape_scale 1
  apply goalShape_shift (-1)
  apply goalShape_weaken 1.12130128 1.12491424 (by norm_num1) (by norm_num1) (by norm_num1)
  apply goalShape_scale 3
  apply goalShape_shift (-1)
  apply goalShape_weaken 1.24953535 1.28211010 (by norm_num1) (by norm_num1) (by norm_num1)
  apply goalShape_scale 2
  apply goalShape_shift (-1)
  apply goalShape_weaken 1.21888909 1.35104959 (by norm_num1) (by norm_num1) (by norm_num1)
  apply goalShape_scale 2
  apply goalShape_shift (-1)
  apply goalShape_weaken 1.10363829 1.66592393 (by norm_num1) (by norm_num1) (by norm_num1)
  apply goalShape_trivial (by norm_num1) (by norm_num1) (by norm_num1) (by norm_num1)

end
