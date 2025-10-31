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
  norm_num1
  apply goalShape_shift 1
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

section

def logGoalShape (x₁a x₁b x₂a x₂b : ℕ) (a₁a : ℤ) (a₁b : ℕ) (a₂a : ℤ) (a₂b : ℕ) : Prop :=
    0 < x₁a → 0 < x₁b → (x₁a / x₁b : ℚ) ≤ x₂a / x₂b → 0 < a₁b → 0 < a₂b →
      a₁a / a₁b < logb 2 (x₁a / x₁b) ∧ logb 2 (x₂a / x₂b) < a₂a / a₂b

variable (x₁a x₁b x₂a x₂b : ℕ) (a₁a : ℤ) (a₁b : ℕ) (a₂a : ℤ) (a₂b : ℕ)

lemma logGoalShape_real
    (x₁ x₂ a₁ a₂ : ℝ)
    (ha₁ : a₁ ≤ a₁a / a₁b) (ha₂ : a₂a / a₂b ≤ a₂)
    (hx₁ : x₁a / x₁b ≤ x₁) (hx₂ : x₂ ≤ x₂a / x₂b)
    (hx : x₁ ≤ x₂)
    (hx₁a : 0 < x₁a)
    (hx₁b : 0 < x₁b)
    (ha₁b : 0 < a₁b)
    (ha₂b : 0 < a₂b)
    (h : logGoalShape x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b) :
    a₁ < logb 2 x₁ ∧ logb 2 x₂ < a₂ := by
  rw [logGoalShape] at h
  have hR : (x₁a / x₁b : ℝ) ≤ x₂a / x₂b := hx₁.trans (hx.trans hx₂)
  have hQ : (x₁a / x₁b : ℚ) ≤ x₂a / x₂b := (Rat.cast_le (K := ℝ)).1 (by simpa using hR)
  specialize h (by positivity) (by positivity) hQ (by simpa using ha₁b)
    (by simpa using ha₂b)
  have h₁ : logb 2 (x₁a / x₁b) ≤ logb 2 x₁ := (logb_le_logb_of_le one_lt_two (by positivity) hx₁)
  have h₂ : logb 2 x₂ ≤ logb 2 (x₂a / x₂b) := by
    apply logb_le_logb_of_le one_lt_two _ hx₂
    grw [← hx, ← hx₁]
    positivity
  exact ⟨h₁.trans_lt' (h.1.trans_le' (mod_cast ha₁)), h₂.trans_lt (h.2.trans_le (mod_cast ha₂))⟩

lemma logGoalShape_imp
    (x₁ x₂ a₁ a₂ : ℚ)
    (ha₁ : a₁ ≤ a₁a / a₁b) (ha₂ : a₂a / a₂b ≤ a₂)
    (hx₁ : x₁a / x₁b ≤ x₁) (hx₂ : x₂ ≤ x₂a / x₂b)
    (hx : x₁ ≤ x₂)
    (hx₁a : (0).blt x₁a)
    (hx₁b : (0).blt x₁b)
    (ha₁b : (0).blt a₁b)
    (ha₂b : (0).blt a₂b)
    (h : logGoalShape x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b) :
    a₁ < logb 2 x₁ ∧ logb 2 x₂ < a₂ := by
  simp only [Nat.blt_eq] at hx₁a hx₁b ha₁b ha₂b
  refine logGoalShape_real _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ (mod_cast hx) hx₁a hx₁b ha₁b ha₂b h
  · grw [ha₁]; simp
  · grw [← ha₂]; simp
  · grw [← hx₁]; simp
  · grw [hx₂]; simp

lemma logGoalShape_imp''
    (x₁ x₂ a₁ a₂ : ℝ)
    (ha₁ : a₁ = a₁a / a₁b) (ha₂ : a₂ = a₂a / a₂b)
    (hx₁ : x₁ = x₁a / x₁b) (hx₂ : x₂ = x₂a / x₂b)
    (hx : (x₁a.mul x₂b).ble (x₂a.mul x₁b))
    (hx₁a : (0).blt x₁a)
    (hx₁b : (0).blt x₁b)
    (hx₂b : (0).blt x₂b)
    (ha₁b : (0).blt a₁b)
    (ha₂b : (0).blt a₂b)
    (h : logGoalShape x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b) :
    a₁ < logb 2 x₁ ∧ logb 2 x₂ < a₂ := by
  simp only [Nat.blt_eq, Nat.mul_eq, Nat.ble_eq] at hx₁a hx₁b hx₂b ha₁b ha₂b hx
  refine logGoalShape_real _ _ _ _ _ _ _ _ _ _ _ _
    ha₁.le ha₂.ge hx₁.ge hx₂.le ?_ hx₁a hx₁b ha₁b ha₂b h
  rw [hx₁, hx₂, div_le_div_iff₀ (by positivity) (by positivity)]
  exact mod_cast hx

lemma logGoalShape_scale (m : ℕ)
    (h : logGoalShape (x₁a ^ (2 ^ m)) (x₁b ^ (2 ^ m)) (x₂a ^ (2 ^ m)) (x₂b ^ (2 ^ m))
      (2 ^ m * a₁a) a₁b (2 ^ m * a₂a) a₂b) :
    logGoalShape x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b := by
  intro hx₁a hx₁b hx₂
  have := h (by positivity) (by positivity)
    (by simp only [Nat.cast_pow, ← div_pow]; gcongr)
  simpa [← div_pow, logb_pow, mul_div_assoc] using this

lemma logGoalShape_shift_pos (m : ℕ)
    (h : logGoalShape (x₁a * 2 ^ m) x₁b (x₂a * 2 ^ m) x₂b (a₁a + m * a₁b) a₁b (a₂a + m * a₂b) a₂b) :
    logGoalShape x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b := by
  intro hx₁a hx₁b hx₂ ha₁b ha₂b
  have h₂ : (↑(x₁a * 2 ^ m) : ℚ) / ↑x₁b ≤ ↑(x₂a * 2 ^ m) / ↑x₂b := by
    rw [Nat.cast_mul, Nat.cast_mul, mul_comm, mul_comm (x₂a : ℚ), mul_div_assoc, mul_div_assoc]
    gcongr
  have := h (by positivity) (by positivity) h₂ ha₁b ha₂b
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat] at this
  rwa [← div_add' _ _ _ (by positivity), ← div_add' _ _ _ (by positivity), mul_comm (x₁a : ℝ),
    mul_comm (x₂a : ℝ), mul_div_assoc, mul_div_assoc, logb_mul (by simp) (by positivity),
    logb_mul (by simp), logb_pow, logb_self_eq_one one_lt_two, mul_one, add_comm (m : ℝ),
    add_comm (m : ℝ), add_lt_add_iff_right, add_lt_add_iff_right] at this
  intro h
  have : (x₂a / x₂b : ℚ) = 0 := by simpa using h
  rw [this] at hx₂
  have : 0 < (x₁a / x₁b : ℚ) := by positivity
  exact this.not_ge hx₂

lemma logGoalShape_shift_neg (m : ℕ)
    (h : logGoalShape x₁a (x₁b * 2 ^ m) x₂a (x₂b * 2 ^ m) (a₁a - m * a₁b) a₁b (a₂a - m * a₂b) a₂b) :
    logGoalShape x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b := by
  intro hx₁a hx₁b hx₂ ha₁b ha₂b
  have h₂ : (↑x₁a / ↑(x₁b * 2 ^ m) : ℚ) ≤ ↑x₂a / ↑(x₂b * 2 ^ m) := by
    rw [Nat.cast_mul, Nat.cast_mul, div_mul_eq_div_div, div_mul_eq_div_div]
    gcongr
  have := h (by positivity) (by positivity) h₂ ha₁b ha₂b
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat] at this
  rwa [mul_comm (m : ℝ), mul_comm (m : ℝ), ← div_sub' (by positivity), ← div_sub' (by positivity),
    div_mul_eq_div_div, div_mul_eq_div_div, logb_div (by positivity) (pow_ne_zero _ two_ne_zero),
    logb_div _ (pow_ne_zero _ two_ne_zero), logb_pow, logb_self_eq_one one_lt_two, mul_one,
    sub_lt_sub_iff_right, sub_lt_sub_iff_right] at this
  intro h
  have : (x₂a / x₂b : ℚ) = 0 := by simpa using h
  rw [this] at hx₂
  have : 0 < (x₁a / x₁b : ℚ) := by positivity
  exact this.not_ge hx₂

lemma logGoalShape_trivial (hx₁ : x₁b.blt x₁a) (hx₂ : x₂a.blt (Nat.mul 2 x₂b))
    (ha₁ : a₁a.ble' (Int.ofNat Nat.zero)) (ha₂ : (Int.ofNat a₂b).ble' a₂a) :
    logGoalShape x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b := by
  intro hx₁a hx₁b hx ha₁b ha₂b
  simp only [Nat.zero_eq, Int.ofNat_eq_coe, CharP.cast_eq_zero, Int.ble'_eq_true] at ha₁ ha₂
  have h₁ : (a₁a / a₁b : ℚ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (mod_cast ha₁) (by positivity)
  have h₂ : 0 < logb 2 (x₁a / x₁b) := by
    apply logb_pos one_lt_two
    rw [one_lt_div₀]
    · simpa using hx₁
    · exact mod_cast hx₁b
  have h₃ : (0 : ℚ) < x₁a / x₁b := by positivity
  have h₄ : logb 2 (x₂a / x₂b) < 1 := by
    rw [logb_lt_iff_lt_rpow one_lt_two, rpow_one, div_lt_iff₀]
    · norm_cast
      simpa using hx₂
    · by_contra!
      have : x₂b = 0 := by simpa using this
      simp only [this, CharP.cast_eq_zero, div_zero] at hx
      exact h₃.not_ge hx
    have : (0 : ℚ) < x₂a / x₂b := h₃.trans_le hx
    rw [← Rat.cast_lt (K := ℝ)] at this
    simpa using this
  have h₅ : (1 : ℝ) ≤ a₂a / a₂b := by
    rw [one_le_div₀]
    · exact mod_cast ha₂
    simpa
  exact ⟨h₂.trans_le' (mod_cast h₁), h₄.trans_le h₅⟩

lemma logGoalShape_weaken (x₁a' x₁b' x₂a' x₂b' : ℕ)
    (h₁ : (x₁a'.mul x₁b).ble (x₁a.mul x₁b')) (h₂ : (x₂a.mul x₂b').ble (x₂a'.mul x₂b))
    (hx₁a' : Nat.blt 0 x₁a') (hx₂b' : Nat.blt 0 x₂b')
    (h : logGoalShape x₁a' x₁b' x₂a' x₂b' a₁a a₁b a₂a a₂b) :
    logGoalShape x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b := by
  intro hx₁a hx₁b hx ha₁b ha₂b
  simp only [Nat.mul_eq, Nat.ble_eq, Nat.blt_eq] at h₁ h₂ hx₁a' hx₂b'
  have : 0 < x₁b' := by
    by_contra!
    simp only [nonpos_iff_eq_zero] at this
    simp only [this, mul_zero, nonpos_iff_eq_zero, mul_eq_zero] at h₁
    grind
  have h₁' : (x₁a' / x₁b' : ℚ) ≤ x₁a / x₁b := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mod_cast h₁
  have h₂' : (x₂a / x₂b : ℚ) ≤ x₂a' / x₂b' := by
    obtain rfl | h' := eq_or_ne x₂b 0
    · simp only [CharP.cast_eq_zero, div_zero]; positivity
    rw [div_le_div_iff₀ (by positivity)]
    · exact mod_cast h₂
    positivity
  have := h hx₁a' this (h₁'.trans (h₂'.trans' hx)) ha₁b ha₂b
  refine ⟨this.1.trans_le (logb_le_logb_of_le one_lt_two (by positivity)
    (by simpa using (Rat.cast_le (K := ℝ)).2 h₁')), this.2.trans_le'
      (logb_le_logb_of_le one_lt_two ?_ (by simpa using (Rat.cast_le (K := ℝ)).2 h₂'))⟩
  by_contra! h
  have : (x₂a / x₂b : ℝ) = 0 := le_antisymm h (by positivity)
  have : (x₂a / x₂b : ℚ) = 0 := by simpa using this
  rw [this] at hx
  have : 0 < (x₁a / x₁b : ℚ) := by positivity
  exact this.not_ge hx

lemma logb_approx_second'' :
    -24245009 / 100000000 < logb 2 (1000 / 1183) ∧ logb 2 (1000 / 1183) < -24245005 / 100000000 := by
  suffices logGoalShape 1000 1183 1000 1183 (-24245009) 100000000 (-24245005) 100000000 by
    have := logGoalShape_imp _ _ _ _ _ _ _ _ (1000 / 1183) (1000 / 1183) (-24245009 / 100000000)
      (-24245005 / 100000000) (by norm_num1) (by norm_num1) (by norm_num1) (by norm_num1) (by simp)
      rfl rfl rfl rfl this
    simpa using this
  refine logGoalShape_shift_pos _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_scale _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_shift_neg _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_scale _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_shift_neg _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_weaken _ _ _ _ _ _ _ _
    9418478353660960986 9223372036854775808 9418478353660960987 9223372036854775808
    rfl rfl rfl rfl ?_
  refine logGoalShape_scale _ _ _ _ _ _ _ _ 6 ?_
  refine logGoalShape_shift_neg _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_weaken _ _ _ _ _ _ _ _
    17606978297203486162 9223372036854775808 17606978297203486283 9223372036854775808
    rfl rfl rfl rfl ?_
  refine logGoalShape_scale _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_shift_neg _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_scale _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_shift_neg _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_scale _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_shift_neg _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_scale _ _ _ _ _ _ _ _ 2 ?_
  refine logGoalShape_shift_neg _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_weaken _ _ _ _ _ _ _ _
    16613575871599151527 9223372036854775808 16613575871599155181 9223372036854775808
    rfl rfl rfl rfl ?_
  refine logGoalShape_scale _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_shift_neg _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_scale _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_shift_neg _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_scale _ _ _ _ _ _ _ _ 2 ?_
  refine logGoalShape_shift_neg _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_scale _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_shift_neg _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_weaken _ _ _ _ _ _ _ _
    10361637590695982181 9223372036854775808 10361637590696055108 9223372036854775808
    rfl rfl rfl rfl ?_
  refine logGoalShape_scale _ _ _ _ _ _ _ _ 3 ?_
  refine logGoalShape_shift_neg _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_scale _ _ _ _ _ _ _ _ 2 ?_
  refine logGoalShape_shift_neg _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_scale _ _ _ _ _ _ _ _ 2 ?_
  refine logGoalShape_shift_neg _ _ _ _ _ _ _ _ 1 ?_
  refine logGoalShape_trivial _ _ _ _ _ _ _ _ rfl rfl rfl rfl

lemma logGoalShape_shift_pos'
    (x₁a' x₂a' : ℕ)
    (a₁a' a₂a' : ℤ)
    (m : ℕ)
    (hx₁a' : x₁a'.beq (x₁a.mul (Nat.pow 2 m)))
    (hx₂a' : x₂a'.beq (x₂a.mul (Nat.pow 2 m)))
    (ha₁a' : a₁a'.beq' (a₁a.add (Int.ofNat (m.mul a₁b))))
    (ha₂a' : a₂a'.beq' (a₂a.add (Int.ofNat (m.mul a₂b))))
    (h : logGoalShape x₁a' x₁b x₂a' x₂b a₁a' a₁b a₂a' a₂b) :
    logGoalShape x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b := by
  simp only [Nat.pow_eq, Nat.mul_eq, Nat.beq_eq, Int.ofNat_eq_coe, Nat.cast_mul, Int.add_def,
    Int.beq'_eq] at hx₁a' hx₂a' ha₁a' ha₂a'
  subst hx₁a' hx₂a' ha₁a' ha₂a'
  exact logGoalShape_shift_pos x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b m h

lemma logGoalShape_shift_neg'
    (x₁b' x₂b' : ℕ)
    (a₁a' a₂a' : ℤ)
    (m : ℕ)
    (hx₁b' : x₁b'.beq (x₁b.mul (Nat.pow 2 m)))
    (hx₂b' : x₂b'.beq (x₂b.mul (Nat.pow 2 m)))
    (ha₁a' : a₁a'.beq' (a₁a.sub (Int.ofNat (m.mul a₁b))))
    (ha₂a' : a₂a'.beq' (a₂a.sub (Int.ofNat (m.mul a₂b))))
    (h : logGoalShape x₁a x₁b' x₂a x₂b' a₁a' a₁b a₂a' a₂b) :
    logGoalShape x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b := by
  simp only [Nat.pow_eq, Nat.mul_eq, Nat.beq_eq, Int.ofNat_eq_coe, Nat.cast_mul,
    Int.beq'_eq] at hx₁b' hx₂b' ha₁a' ha₂a'
  subst hx₁b' hx₂b' ha₁a' ha₂a'
  exact logGoalShape_shift_neg x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b m h

lemma logGoalShape_scale'
    (x₁a' x₁b' x₂a' x₂b' : ℕ)
    (a₁a' a₂a' : ℤ)
    (m : ℕ)
    (hx₁a' : x₁a'.beq (x₁a.pow (Nat.pow 2 m)))
    (hx₁b' : x₁b'.beq (x₁b.pow (Nat.pow 2 m)))
    (hx₂a' : x₂a'.beq (x₂a.pow (Nat.pow 2 m)))
    (hx₂b' : x₂b'.beq (x₂b.pow (Nat.pow 2 m)))
    (ha₁a' : a₁a'.beq' (Int.mul (Int.ofNat (Nat.pow 2 m)) a₁a))
    (ha₂a' : a₂a'.beq' (Int.mul (Int.ofNat (Nat.pow 2 m)) a₂a))
    (h : logGoalShape x₁a' x₁b' x₂a' x₂b' a₁a' a₁b a₂a' a₂b) :
    logGoalShape x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b := by
  simp only [Nat.pow_eq, Nat.beq_eq, Int.ofNat_eq_coe, Nat.cast_pow, Nat.cast_ofNat, Int.mul_def,
    Int.beq'_eq] at hx₁a' hx₁b' hx₂a' hx₂b' ha₁a' ha₂a'
  subst hx₁a' hx₁b' hx₂a' hx₂b' ha₁a' ha₂a'
  exact logGoalShape_scale x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b m h

end

section

open Lean Expr Elab Meta Tactic Qq

def mkRatDiv (a b : Expr) : Expr :=
  mkApp6 (mkConst ``HDiv.hDiv [0, 0, 0]) (mkConst ``Rat) (mkConst ``Rat) (mkConst ``Rat)
    (mkApp2 (mkConst ``instHDiv) (mkConst ``Rat) (mkConst ``Rat.instDiv)) a b

def cleanup_rat (e : Q(ℝ)) : MetaM ((ℤ × ℕ) × (a : Q(ℤ)) × (b : Q(ℕ)) × Q($e = $a / $b)) := do
  let ⟨q, a, b, pf⟩ ← Mathlib.Meta.NormNum.deriveRat e q(Real.instDivisionRing)
  let pf' : Q($e = $a / $b) := q(($pf).to_raw_eq)
  return ⟨(q.num, q.den), a, b, pf'⟩

-- given an expression `logb 2 x`, where `x` can be normalized to a positive rational `xa / xb`,
-- return `((xa, xb), x, pf)` where `pf : x = xa / xb`
def unpack_log (e : Expr) : MetaM ((ℕ × ℕ) × Expr × Expr) :=
  match_expr e with
  | Real.logb b x => do
    let some b := b.nat?
      | throwError "unexpected expression in base"
    unless b == 2 do
      throwError "only base 2 supported"
    let ⟨(a, b), _, _, pf⟩ ← cleanup_rat x
    if a ≤ 0 then
      throwError "log of nonpositive number"
    return ((a.natAbs, b), x, pf)
  | _ => throwError "expected log"

-- given an expression `a < logb 2 x` where `a` and `x` can be normalised to rationals `aa / ab` and
-- `xa / xb` respectively, return `(((xa, xb), x, pf_x), ((aa, ab), a, pf_a))`
-- where `pf_a : a = aa / ab` and `pf_x : x = xa / xb`
def unpack_lt_log (e : Expr) : MetaM (((ℕ × ℕ) × Expr × Expr) × ((ℤ × ℕ) × Expr × Expr)) :=
  match_expr e with
  | LT.lt _ _ lhs rhs => do
    let ⟨(aa, ab), _, _, pf_a⟩ ← cleanup_rat lhs
    let ((xa, xb), x, pf_x) ← unpack_log rhs
    return (((xa, xb), x, pf_x), ((aa, ab), lhs, pf_a))
  | _ => throwError "expected _ < _"

-- given an expression `logb 2 x < a` where `a` and `x` can be normalised to rationals `aa / ab` and
-- `xa / xb` respectively, return `(((xa, xb), x, pf_x), ((aa, ab), a, pf_a))` where
-- `pf_a : a = aa / ab` and `pf_x : x = xa / xb`
def unpack_log_lt (e : Expr) : MetaM (((ℕ × ℕ) × Expr × Expr) × ((ℤ × ℕ) × Expr × Expr)) :=
  match_expr e with
  | LT.lt _ _ lhs rhs => do
    let ((xa, xb), x, pf_x) ← unpack_log lhs
    let ⟨(aa, ab), _, _, pf_a⟩ ← cleanup_rat rhs
    return (((xa, xb), x, pf_x), ((aa, ab), rhs, pf_a))
  | _ => throwError "expected _ < _"

def unpack_goal (e : Expr) :
    MetaM ((((ℕ × ℕ) × Expr × Expr) × ((ℕ × ℕ) × Expr × Expr)) × (((ℤ × ℕ) × Expr × Expr) × ((ℤ × ℕ) × Expr × Expr))) :=
  match_expr e with
  | And lhs rhs => do
    let (x₁, a₁) ← unpack_lt_log lhs
    let (x₂, a₂) ← unpack_log_lt rhs
    return ((x₁, x₂), (a₁, a₂))
  | _ => throwError "unexpected goal shape"

def mkLogGoalShapeExpr (x₁a x₁b x₂a x₂b : ℕ) (a₁a : ℤ) (a₁b : ℕ) (a₂a : ℤ) (a₂b : ℕ) :
    Expr :=
  mkApp8 (mkConst ``logGoalShape)
    (mkNatLit x₁a) (mkNatLit x₁b) (mkNatLit x₂a) (mkNatLit x₂b)
    (mkIntLit a₁a) (mkNatLit a₁b) (mkIntLit a₂a) (mkNatLit a₂b)

/--
compute ⌊log₂(a/b)⌋ for positive naturals a, b
warning! does not terminate for a = 0, but this function will only be called for
positive rationals
-/
partial def floorLog2 (a b : ℕ) : ℤ :=
  if a = 0 ∨ b = 0 then unreachable! else
  if b ≤ a then
    if a < 2 * b then 0
    else floorLog2 a (2 * b) + 1
  else
    floorLog2 (2 * a) b - 1

/--
Finds the least m such that 2 ≤ (a/b)^(2^m)

Warning! does not terminate if a ≤ b
-/
def countSquares (a b : ℕ) : ℕ × ℕ × ℕ := if a ≤ b then unreachable! else go 0 a b where
  go (n : ℕ) (a b : ℕ) : ℕ × ℕ × ℕ := if 2 * b ≤ a then (n, a, b) else go (n + 1) (a * a) (b * b)
  partial_fixpoint

partial def prove_logGoalShape (x₁a x₁b x₂a x₂b : ℕ) (a₁a : ℤ) (a₁b : ℕ) (a₂a : ℤ) (a₂b : ℕ)
    (cut : List String) :
    MetaM Expr := do
  if cut.length > 500 then
    throwError "too deep {cut}"
  if Nat.gcd x₁a x₁b ≠ 1 ∨ Nat.gcd x₂a x₂b ≠ 1 then
    let x₁g := Nat.gcd x₁a x₁b
    let x₂g := Nat.gcd x₂a x₂b
    let x₁a' := x₁a / x₁g
    let x₁b' := x₁b / x₁g
    let x₂a' := x₂a / x₂g
    let x₂b' := x₂b / x₂g
    let pf ← prove_logGoalShape x₁a' x₁b' x₂a' x₂b' a₁a a₁b a₂a a₂b ("cancel" :: cut)
    let pf₁ := mkApp8 (mkConst ``logGoalShape_weaken)
      (mkNatLit x₁a) (mkNatLit x₁b) (mkNatLit x₂a) (mkNatLit x₂b)
      (mkIntLit a₁a) (mkNatLit a₁b) (mkIntLit a₂a) (mkNatLit a₂b)
    let pf₂ := mkApp9 pf₁
      (mkNatLit x₁a') (mkNatLit x₁b') (mkNatLit x₂a') (mkNatLit x₂b')
      reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue pf
    return pf₂
  if x₁b > 2 ^ 64 ∨ x₂b > 2 ^ 64 then
    let x₁a' : ℕ := Int.natAbs (Rat.floor (x₁a / x₁b * 2 ^ 63 : ℚ))
    let x₂a' : ℕ := Int.natAbs (Rat.ceil (x₂a / x₂b * 2 ^ 63 : ℚ))
    let x₁b' : ℕ := 2 ^ 63
    let x₂b' : ℕ := 2 ^ 63
    let pf ← prove_logGoalShape x₁a' x₁b' x₂a' x₂b' a₁a a₁b a₂a a₂b ("weaken" :: cut)
    let pf₁ := mkApp8 (mkConst ``logGoalShape_weaken)
      (mkNatLit x₁a) (mkNatLit x₁b) (mkNatLit x₂a) (mkNatLit x₂b)
      (mkIntLit a₁a) (mkNatLit a₁b) (mkIntLit a₂a) (mkNatLit a₂b)
    let pf₂ := mkApp9 pf₁
      (mkNatLit x₁a') (mkNatLit x₁b') (mkNatLit x₂a') (mkNatLit x₂b')
      reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue pf
    return pf₂
  let n₁ := floorLog2 x₁a x₁b
  let n₂ := floorLog2 x₂a x₂b
  unless n₁ = n₂ do throwError "bounds not satified"
  -- let pf ← mkSorry (mkLogGoalShapeExpr x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b) false
  if n₁ = 0 then
    if a₂a ≤ 0 then throwError "upper inequality fails"
    if a₁a ≥ a₁b then throwError "lower inequality fails"
    if a₁a ≤ 0 ∧ a₂b ≤ a₂a then
      let pf₁ := mkApp8 (mkConst ``logGoalShape_trivial)
        (mkNatLit x₁a) (mkNatLit x₁b) (mkNatLit x₂a) (mkNatLit x₂b)
        (mkIntLit a₁a) (mkNatLit a₁b) (mkIntLit a₂a) (mkNatLit a₂b)
      return mkApp4 pf₁ reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue
    else
      let (m₁, x₁a', x₁b') := countSquares x₁a x₁b
      let (m₂, x₂a', x₂b') := countSquares x₂a x₂b
      unless m₁ = m₂ do throwError "exponent bounds not satified {cut}"
      let a₁a' : ℤ := a₁a * 2 ^ m₁
      let a₂a' : ℤ := a₂a * 2 ^ m₁
      let pf₁ := mkApp8 (mkConst ``logGoalShape_scale')
        (mkNatLit x₁a) (mkNatLit x₁b) (mkNatLit x₂a) (mkNatLit x₂b)
        (mkIntLit a₁a) (mkNatLit a₁b) (mkIntLit a₂a) (mkNatLit a₂b)
      let pf₂ := mkApp7 pf₁ (mkNatLit x₁a') (mkNatLit x₁b') (mkNatLit x₂a') (mkNatLit x₂b')
        (mkIntLit a₁a') (mkIntLit a₂a') (mkNatLit m₁)
      let pf₃ := mkApp7 pf₂
        reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue
      let pf ← prove_logGoalShape x₁a' x₁b' x₂a' x₂b' a₁a' a₁b a₂a' a₂b (s!"scale {m₁}" :: cut)
      return pf₃ pf
  else
    if n₁ > 0 then
      let m := n₁.natAbs
      let x₁b' : ℕ := x₁b * 2 ^ m
      let x₂b' : ℕ := x₂b * 2 ^ m
      let a₁a' : ℤ := a₁a - m * a₁b
      let a₂a' : ℤ := a₂a - m * a₂b
      let pf₁ := mkApp8 (mkConst ``logGoalShape_shift_neg')
        (mkNatLit x₁a) (mkNatLit x₁b) (mkNatLit x₂a) (mkNatLit x₂b)
        (mkIntLit a₁a) (mkNatLit a₁b) (mkIntLit a₂a) (mkNatLit a₂b)
      let pf₂ := mkApp9 pf₁
        (mkNatLit x₁b') (mkNatLit x₂b') (mkIntLit a₁a') (mkIntLit a₂a') (mkNatLit m)
        reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue
      let pf₃ ← prove_logGoalShape x₁a x₁b' x₂a x₂b' a₁a' a₁b a₂a' a₂b (s!"neg {m}" :: cut)
      return mkApp pf₂ pf₃
    else
      let m := n₁.natAbs
      let x₁a' : ℕ := x₁a * 2 ^ m
      let x₂a' : ℕ := x₂a * 2 ^ m
      let a₁a' : ℤ := a₁a + m * a₁b
      let a₂a' : ℤ := a₂a + m * a₂b
      let pf₁ := mkApp8 (mkConst ``logGoalShape_shift_pos')
        (mkNatLit x₁a) (mkNatLit x₁b) (mkNatLit x₂a) (mkNatLit x₂b)
        (mkIntLit a₁a) (mkNatLit a₁b) (mkIntLit a₂a) (mkNatLit a₂b)
      let pf₂ := mkApp9 pf₁
        (mkNatLit x₁a') (mkNatLit x₂a') (mkIntLit a₁a') (mkIntLit a₂a') (mkNatLit m)
        reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue
      let pf₃ ← prove_logGoalShape x₁a' x₁b x₂a' x₂b a₁a' a₁b a₂a' a₂b (s!"pos {m}" :: cut)
      return mkApp pf₂ pf₃

elab "prove_goalShape" : tactic => do
  let g ← getMainGoal
  let t ← g.getType
  let ((((x₁a, x₁b), x₁, pfx₁), ((x₂a, x₂b), x₂, pfx₂)),
       (((a₁a, a₁b), a₁, pfa₁), ((a₂a, a₂b), a₂, pfa₂))) ← unpack_goal t
  let i ← mkFreshExprMVar (some (mkLogGoalShapeExpr x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b))
  let pf₁ := mkApp8 (mkConst ``logGoalShape_imp'') (mkNatLit x₁a) (mkNatLit x₁b)
    (mkNatLit x₂a) (mkNatLit x₂b) (mkIntLit a₁a) (mkNatLit a₁b) (mkIntLit a₂a) (mkNatLit a₂b)
  let pf₂ := mkApp8 pf₁ x₁ x₂ a₁ a₂ pfa₁ pfa₂ pfx₁ pfx₂
  let pf₃ := mkApp7 pf₂ reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue
    reflBoolTrue i
  replaceMainGoal [i.mvarId!]
  g.assign pf₃

elab "test_logGoalShape" : tactic => liftMetaFinishingTactic fun g ↦ do
  let e : Q(Prop) ← g.getType
  match e with
  | ~q(logGoalShape $x₁a $x₁b $x₂a $x₂b $a₁a $a₁b $a₂a $a₂b) =>
    let some x₁a := x₁a.nat? | throwError "unexpected x₁a"
    let some x₁b := x₁b.nat? | throwError "unexpected x₁b"
    let some x₂a := x₂a.nat? | throwError "unexpected x₂a"
    let some x₂b := x₂b.nat? | throwError "unexpected x₂b"
    let some a₁a := a₁a.int? | throwError "unexpected a₁a"
    let some a₁b := a₁b.nat? | throwError "unexpected a₁b"
    let some a₂a := a₂a.int? | throwError "unexpected a₂a"
    let some a₂b := a₂b.nat? | throwError "unexpected a₂b"
    let pf ← prove_logGoalShape x₁a x₁b x₂a x₂b a₁a a₁b a₂a a₂b []
    g.assign pf
  | _ => throwError "unexpected goal shape"

example : -0.242450073677701384625 < logb 2 (1000 / 1183) ∧ logb 2 (1000 / 1183) < -0.242450073677701384624 := by
  prove_goalShape
  show_term test_logGoalShape

example : 0.1 < logb 2 1.414 ∧ logb 2 1.415 < 0.99 := by
  prove_goalShape
  test_logGoalShape

end
