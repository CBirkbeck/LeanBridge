import LeanBridge.Compute.LogTwoEstimatesAgain
import LeanBridge.Compute.LogSmall

open Real

theorem bound_sqrt_5 :
    √(5 : ℝ) ∈ Set.Icc
      2.2360679774997896964091736687312762
      2.2360679774997896964091736687312763 :=
  ⟨Real.le_sqrt_of_sq_le (by norm_num), (Real.sqrt_le_left (by norm_num)).2 (by norm_num)⟩

noncomputable def φ : ℝ := (1 + √5) / 2

theorem bound_φ :
    φ ∈ Set.Icc
      1.6180339887498948482045868343656381
      1.6180339887498948482045868343656382 := by
  rw [φ, div_eq_mul_inv]
  apply interval_end (mul_interval (add_interval const_interval bound_sqrt_5) const_interval
    (by norm_num1) (by simp))
  · norm_num
  · norm_num

theorem bound_logb_φ :
    logb 2 φ ∈ Set.Icc
      0.694241913630617301738790266898595
      0.694241913630617301738790266898596 := by
  apply Tactic.LtLogGoal.finish (by norm_num1) _ _ _ bound_φ
  · bound_log
  · bound_log

theorem bound_log_φ :
    log φ ∈ Set.Icc
      0.48121182505960344749775891342436
      0.48121182505960344749775891342437 := by
  have : log φ = logb 2 φ * log 2 := by
    rw [logb, div_mul_cancel₀]
    norm_num
  rw [this]
  refine interval_end (mul_interval bound_logb_φ log_2 (by norm_num1) (by norm_num1))
    (by norm_num1) (by norm_num1)
