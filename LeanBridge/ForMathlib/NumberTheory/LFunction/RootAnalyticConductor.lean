import LeanBridge.ForMathlib.NumberTheory.LFunction.AnalyticConductor

/-!
# The root analytic conductor of an analytic L-function

The root analytic conductor of an analytic L-function of degree `d` is the `d`-th root `A ^ (1 / d)`
of its analytic conductor `A`, the analogue for L-functions of the root discriminant of a number
field.

## Main definitions

* `AnalyticLFunction.rootAnalyticConductor` (LMFDB `lfunction.root_analytic_conductor`).

## Main results

* `AnalyticLFunction.rootAnalyticConductor_pow_degree`: for an L-function of positive degree `d`,
  the `d`-th power of the root analytic conductor is the analytic conductor.
-/

namespace AnalyticLFunction

variable (L : AnalyticLFunction)

/-- The **root analytic conductor** `α = A ^ (1 / d)` (LMFDB `lfunction.root_analytic_conductor`) of
an analytic L-function of degree `d` (LMFDB `lfunction.degree`) and analytic conductor `A` (LMFDB
`lfunction.analytic_conductor`), the positive real `d`-th root of `A`. -/
noncomputable def rootAnalyticConductor : ℝ :=
  L.analyticConductor ^ (1 / L.degree : ℝ)

lemma rootAnalyticConductor_pos : 0 < L.rootAnalyticConductor :=
  Real.rpow_pos_of_pos L.analyticConductor_pos _

/-- **The root analytic conductor is a `d`-th root of the analytic conductor.** -/
lemma rootAnalyticConductor_pow_degree (hL : L.degree ≠ 0) :
    L.rootAnalyticConductor ^ L.degree = L.analyticConductor := by
  rw [rootAnalyticConductor, ← Real.rpow_mul_natCast L.analyticConductor_pos.le, one_div,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hL), Real.rpow_one]

end AnalyticLFunction
