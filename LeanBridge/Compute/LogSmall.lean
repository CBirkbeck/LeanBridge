/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import LeanBridge.Compute.Interval
import Mathlib

/-!
# Estimates on natural log of rationals close to 1
-/

open Filter
open Topology BigOperators
open Finset hiding Icc Ioo
open Set

namespace Real

set_option linter.unusedSimpArgs false in
lemma artanh_partial_series_bound_aux {y : ℝ} (n : ℕ) (hy₁ : -1 < y) (hy₂ : y < 1) :
    HasDerivAt
      (fun (x : ℝ) ↦ (∑ i ∈ range n, x^(2*i+1)/(2*i+1)) - 1/2 * log ((1+x)/(1-x)))
      (- (y ^ 2) ^ n / (1 - y^2)) y := by
  apply ((HasDerivAt.fun_sum fun i hi ↦ (hasDerivAt_pow _ _).div_const _).sub
      (((((hasDerivAt_id _).const_add _).div ((hasDerivAt_id _).const_sub _) _).log
        _).const_mul _)).congr_deriv ?_
  · grind
  · simp only [id_eq, div_ne_zero_iff, Pi.div_apply]; grind
  have : (∑ i ∈ range n, (2*i+1) * y ^ (2*i) / (2*i+1)) = (∑ i ∈ range n, (y^2) ^ i) := by
    congr with i
    simp [field, mul_comm, ← pow_mul]
  have hy₃ : y ^ 2 ≠ 1 := by simp [hy₁.ne', hy₂.ne]
  have hy₄ : (1 - y) * (1 + y) = 1 - y ^ 2 := by ring
  simp [this, field, geom_sum_eq hy₃, hy₄, sub_ne_zero_of_ne, hy₃.symm]
  ring

set_option linter.unusedSimpArgs false in
lemma artanh_partial_series_bound_aux' {y : ℝ} (n : ℕ) (hy₁ : -1 < y) (hy₂ : y < 1) :
    HasDerivAt
      (fun x ↦ 1 / 2 * log ((1 + x) / (1 - x)) - (∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1)))
      ((y ^ 2) ^ n / (1 - y ^ 2)) y := by
  apply ((((((hasDerivAt_id _).const_add _).div ((hasDerivAt_id _).const_sub _) _).log
          _).const_mul _).sub (HasDerivAt.fun_sum fun i hi ↦ (hasDerivAt_pow _ _).div_const _))
        |>.congr_deriv ?_
  · grind
  · simp only [id_eq, div_ne_zero_iff, Pi.div_apply]; grind
  have : (∑ i ∈ range n, (2*i+1) * y ^ (2*i) / (2*i+1)) = (∑ i ∈ range n, (y^2) ^ i) := by
    congr with i
    simp [field, mul_comm, ← pow_mul]
  have hy₃ : y ^ 2 ≠ 1 := by simp [hy₁.ne', hy₂.ne]
  have hy₄ : (1 - y) * (1 + y) = 1 - y ^ 2 := by ring
  simp [this, field, geom_sum_eq hy₃, hy₄, sub_ne_zero_of_ne, hy₃.symm]
  ring


lemma artanh_partial_series_symmetric_bound {x : ℝ} (h : |x| < 1) (n : ℕ) :
    |((∑ i ∈ range n, x^(2*i+1)/(2*i+1)) - 1/2 * log ((1+x)/(1-x)))| ≤
      |x|^(2*n+1) / (1 - x^2) := by
  let F : ℝ → ℝ := fun x ↦ (∑ i ∈ range n, x^(2*i+1)/(2*i+1)) - 1/2 * log ((1+x)/(1-x))
  let F' (y : ℝ) : ℝ := (- (y ^ 2) ^ n / (1 - y ^ 2))
  have hI : Icc (-|x|) |x| ⊆ Ioo (-1 : ℝ) 1 := Icc_subset_Ioo (by simp [h]) h
  have A : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt F (F' y) y := by
    intros y hy
    apply artanh_partial_series_bound_aux n hy.1 hy.2
  have B : ∀ y ∈ Set.Icc (-|x|) |x|, ‖F' y‖ ≤ |x| ^ (2 * n) / (1 - x ^ 2) := fun y hy ↦ by
    have : y ^ 2 ≤ x ^ 2 := sq_le_sq.2 (abs_le.2 hy)
    calc
    ‖F' y‖ = (y ^ 2) ^ n / |1 - y ^ 2| := by simp [F']
    _ = (y ^ 2) ^ n / (1 - y ^ 2) := by rw [abs_of_pos (by simpa [abs_lt] using hI hy)]
    _ ≤ (x ^ 2) ^ n / (1 - x ^ 2) := by gcongr ?_ ^ n / (1 - ?_); simpa [abs_lt] using h
    _ ≤ |x| ^ (2 * n) / (1 - x ^ 2) := by simp [pow_mul]
  have C : ‖F x - F 0‖ ≤ |x|^(2*n) / (1 - x^2) * ‖x - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy ↦ (A _ (hI hy)).hasDerivWithinAt) B
      (convex_Icc (-|x|) |x|) (by simp) (by simp [le_abs_self, neg_le, neg_le_abs x])
  simpa [F, pow_succ, div_mul_eq_mul_div, mul_assoc] using C

lemma artanh_partial_series_lower_bound {x : ℝ} (h₀ : 0 ≤ x) (h : x < 1) (n : ℕ) :
    ∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1) ≤ 1 / 2 * log ((1 + x) / (1 - x)) := by
  let F (x : ℝ) : ℝ :=
    1 / 2 * log ((1 + x) / (1 - x)) - (∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1))
  let F' (y : ℝ) : ℝ := (y ^ 2) ^ n / (1 - y ^ 2)
  have A : ∀ y ∈ Icc 0 x, HasDerivAt F (F' y) y := by
    intro y hy
    exact artanh_partial_series_bound_aux' _ (by grind) (by grind)
  suffices 0 ≤ F x by linear_combination this
  suffices MonotoneOn F (Icc 0 x) by simpa [F] using this ⟨le_rfl, h₀⟩ ⟨h₀, le_rfl⟩ h₀
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
    (fun y hy ↦ (A y hy).continuousAt.continuousWithinAt)
    (fun y hy ↦ (A y (interior_subset hy)).hasDerivWithinAt) ?_
  intro y hy
  simp only [interior_Icc, Set.mem_Ioo] at hy
  simp only [F']
  have : 0 ≤ 1 - y ^ 2 := by calc
    0 ≤ 1 - x ^ 2 := by simp [abs_of_nonneg h₀, h.le]
    _ ≤ 1 - y ^ 2 := sub_le_sub_left (pow_le_pow_left₀ hy.1.le hy.2.le 2) 1
  positivity

lemma special_log {k : ℕ} (hk : k ≠ 0) :
    ((1 + (2 * k + 1 : ℝ)⁻¹) / (1 - (2 * k + 1 : ℝ)⁻¹)) = ((k + 1) / k) := by
  simp [field]
  ring

lemma log_bounds (k n : ℕ) (t : ℝ) (hk : k ≠ 0) (hn : n ≠ 0) (x : ℝ) (y : ℕ)
    (ht : t = (k + 1) / k)
    (hx : x = ∑ i ∈ range n, (2 * k + 1 : ℝ)⁻¹ ^ (2 * i + 1) / (2 * i + 1))
    (hy : y = ((2 * k + 1) ^ 2 - 1) * (2 * k + 1) ^ (2 * n - 1)) :
    2 * x ≤ log t ∧ log t ≤ 2 * (x + (y : ℝ)⁻¹) := by
  subst ht
  have hk' : (2 * k + 1 : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by simp; omega)
  have hk'' : 0 < (2 * k + 1 : ℝ)⁻¹ := by simp; positivity
  have hu := artanh_partial_series_symmetric_bound (x := (2 * k + 1 : ℝ)⁻¹)
    (by rwa [abs_of_pos hk'']) n
  have hl := artanh_partial_series_lower_bound (x := (2 * k + 1 : ℝ)⁻¹) (by positivity) hk' n
  rw [← hx, special_log hk] at hl hu
  constructor
  · linear_combination 2 * hl
  rw [abs_of_nonpos (by linear_combination hl), neg_sub, one_div_mul_eq_div, div_sub' two_ne_zero,
    div_le_iff₀ zero_lt_two, sub_le_iff_le_add'] at hu
  grw [hu, mul_add, add_le_add_iff_left, mul_comm, mul_le_mul_iff_right₀ two_pos, abs_of_pos hk'']
  rw [inv_pow]
  apply le_of_eq
  simp [inv_pow, hy, mul_inv_rev, field, ← pow_add]
  congr! 2
  grind

lemma log_16_15 :
    log (16 / 15) ∈ Set.Icc
      0.06453852113757117167292391568399292812
      0.06453852113757117167292391568399292813 := by
  have := log_bounds 15 13 (16 / 15) (by norm_num) (by norm_num) _ _ (by norm_num) rfl rfl
  apply interval_end this (by norm_num) (by norm_num)

lemma log_81_80 :
    log (81 / 80) ∈ Set.Icc
      0.01242251999855715331129312863120890676
      0.01242251999855715331129312863120890677 := by
  have := log_bounds 80 9 (81 / 80) (by norm_num) (by norm_num) _ _ (by norm_num) rfl rfl
  apply interval_end this (by norm_num) (by norm_num)

lemma log_25_24 :
    log (25 / 24) ∈ Set.Icc
      0.040821994520255129554577065155319870177
      0.040821994520255129554577065155319870180 := by
  have := log_bounds 24 11 (25 / 24) (by norm_num) (by norm_num) _ _ (by norm_num) rfl rfl
  apply interval_end this (by norm_num) (by norm_num)

lemma log_2 :
    log 2 ∈ Set.Icc
      0.693147180559945309417232121458176568
      0.693147180559945309417232121458176569 := by
  have : log 2 = 7 * log (16 / 15) + 3 * log (81 / 80) + 5 * log (25 / 24) := by
    have : (2 : ℝ) = (16 / 15) ^ 7 * (81 / 80) ^ 3 * (25 / 24) ^ 5 := by norm_num
    rw [this, log_mul (by simp) (by simp), log_mul (by simp) (by simp),
      log_pow, log_pow, log_pow]
    simp
  rw [this]
  refine interval_end (add_interval (add_interval
    (mul_interval const_interval log_16_15 (by norm_num1) (by norm_num1))
    (mul_interval const_interval log_81_80 (by norm_num1) (by norm_num1)))
    (mul_interval const_interval log_25_24 (by norm_num1) (by norm_num1))) ?_ ?_
  · norm_num1
  · norm_num1
