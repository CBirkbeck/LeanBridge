/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Estimates on natural log of rationals close to 1
-/

open Filter
open Topology BigOperators
open Finset hiding Icc Ioo
open Set

namespace Real

section artanh

set_option linter.unusedSimpArgs false in
lemma artanh_partial_series_bound_aux' {y : ℝ} (n : ℕ) (hy₁ : -1 < y) (hy₂ : y < 1) :
    HasDerivAt
      (fun x ↦ 1 / 2 * log ((1 + x) / (1 - x)) - (∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1)))
      ((y ^ 2) ^ n / (1 - y ^ 2)) y := by
  refine ((((((hasDerivAt_id _).const_add _).div ((hasDerivAt_id _).const_sub _) (by grind)).log
          ?_).const_mul _).sub (HasDerivAt.fun_sum fun i hi ↦ (hasDerivAt_pow _ _).div_const _))
        |>.congr_deriv ?_
  · simp only [id_eq, div_ne_zero_iff, Pi.div_apply]; grind
  have : (∑ i ∈ range n, (2*i+1) * y ^ (2*i) / (2*i+1)) = (∑ i ∈ range n, (y^2) ^ i) := by
    congr with i
    simp [field, mul_comm, ← pow_mul]
  have hy₃ : y ^ 2 ≠ 1 := by simp [hy₁.ne', hy₂.ne]
  have hy₄ : (1 - y) * (1 + y) = 1 - y ^ 2 := by ring
  simp [this, field, geom_sum_eq hy₃, hy₄, sub_ne_zero_of_ne, hy₃.symm]
  ring

lemma artanh_partial_series_symmetric_bound {x : ℝ} (h : |x| < 1) (n : ℕ) :
    |∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1) - 1 / 2 * log ((1 + x) / (1 - x))| ≤
      |x| ^ (2 * n + 1) / (1 - x ^ 2) := by
  let F (x : ℝ) : ℝ :=
    1 / 2 * log ((1 + x) / (1 - x)) - (∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1))
  let F' (y : ℝ) : ℝ := (y ^ 2) ^ n / (1 - y ^ 2)
  have hI : Icc (-|x|) |x| ⊆ Ioo (-1 : ℝ) 1 := Icc_subset_Ioo (by simp [h]) h
  have A : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt F (F' y) y := by
    intro y hy
    exact artanh_partial_series_bound_aux' _ (by grind) (by grind)
  have B : ∀ y ∈ Set.Icc (-|x|) |x|, ‖F' y‖ ≤ |x| ^ (2 * n) / (1 - x ^ 2) := fun y hy ↦ by
    have : y ^ 2 ≤ x ^ 2 := sq_le_sq.2 (abs_le.2 hy)
    calc
    ‖F' y‖ = (y ^ 2) ^ n / |1 - y ^ 2| := by simp [F']
    _ = (y ^ 2) ^ n / (1 - y ^ 2) := by rw [abs_of_pos (by simpa [abs_lt] using hI hy)]
    _ ≤ (x ^ 2) ^ n / (1 - x ^ 2) := by gcongr ?_ ^ n / (1 - ?_); simpa [abs_lt] using h
    _ ≤ |x| ^ (2 * n) / (1 - x ^ 2) := by simp [pow_mul]
  have C : ‖F x - F 0‖ ≤ |x| ^ (2 * n) / (1 - x^2) * ‖x - 0‖ :=
    (convex_Icc (-|x|) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy ↦ (A _ (hI hy)).hasDerivWithinAt) B
      (by simp) (by simp [le_abs_self, neg_le, neg_le_abs x])
  simpa [F, abs_sub_comm, pow_succ, div_mul_eq_mul_div] using C

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

end artanh

-- section sin

-- lemma iteratedDerivWithin_sin_zero {k : ℕ} :
--     iteratedDeriv k sin 0 = if Even k then 0 else (-1) ^ (k / 2) := by
--   obtain ⟨i, rfl | rfl⟩ := k.even_or_odd'
--   · rw [iteratedDeriv_even_sin]
--     simp
--   · rw [iteratedDeriv_odd_sin]
--     simp
--     congr! 1
--     grind

-- lemma taylorWithinEval_sin {k : ℕ} {a b x : ℝ} :
--     taylorWithinEval sin (2 * k) (Set.Icc a b) 0 x =
--       ∑ i ∈ Finset.range k, sorry := by
--   rw [taylor_within_apply]
--   refine (Finset.sum_bij_ne_zero (fun i _ _ ↦ 2 * i + 1) (fun i hi _ ↦ by simpa using hi) (by simp)
--     ?_ ?_).symm
--   · intro j hj hj'
--     simp only [Finset.mem_range] at hj
--     simp [sub_zero, smul_eq_mul, ne_eq, mul_eq_zero, inv_eq_zero, Nat.cast_eq_zero,
--       pow_eq_zero_iff', not_or, not_and, Decidable.not_not, iteratedDerivWithin_sin_zero] at hj'

--   -- · intro i
--   --   simp only [coe_range, Set.mem_Iio, Set.mem_image]
--   --   intro hi


-- lemma sin_partial_series_bound {x : ℝ} {n : ℕ} :
--     |sin x - ∑ i ∈ Finset.range n, ((-1) ^ i * x ^ (2 * i + 1)) / (2 * i + 1).factorial| ≤
--       x ^ (2 * n + 1) / (2 * n + 1).factorial := by
--   sorry

-- end sin
