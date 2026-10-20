import LeanBridge.ForMathlib.NumberTheory.LFunction.Basic
import Mathlib.Analysis.Meromorphic.Order

/-!
# The Riemann hypothesis for analytic L-functions

The Riemann hypothesis for an analytic L-function asserts that its zeros `ρ` with `re ρ > 0` lie
on the critical line `re ρ = 1 / 2` (in the analytic normalisation); the condition `re ρ > 0`
excludes the trivial zeros. The generalized Riemann hypothesis asserts it for every analytic
L-function.

## Main definitions

* `AnalyticLFunction.zeros` (LMFDB `lfunction.zeros`): the zeros of an analytic L-function.
* `AnalyticLFunction.RiemannHypothesis` (LMFDB `lfunction.rh`): the Riemann hypothesis for an
  analytic L-function.
* `GeneralizedRiemannHypothesis` (LMFDB `lfunction.rh`): the Riemann hypothesis for every
  analytic L-function.

## Main results

* `AnalyticLFunction.mem_zeros_iff`: away from `s = 1`, the zeros of an analytic L-function are
  the points where its continuation vanishes.
-/

namespace AnalyticLFunction

variable (L : AnalyticLFunction) {ρ : ℂ}

/-- The **zeros** (LMFDB `lfunction.zeros`) of an analytic L-function: the points where its
continuation, a meromorphic function on `ℂ`, has positive order. Away from the only possible pole
`s = 1` they are the points where the continuation vanishes (`mem_zeros_iff`); using the order
makes the junk value at a pole irrelevant. -/
noncomputable def zeros : Set ℂ :=
  {ρ | 0 < meromorphicOrderAt L.toFun ρ}

/-- Away from `s = 1`, the zeros of an analytic L-function are the points where its continuation
vanishes. -/
lemma mem_zeros_iff (hρ : ρ ≠ 1) : ρ ∈ L.zeros ↔ L.toFun ρ = 0 := by
  have hf : AnalyticAt ℂ L.toFun ρ :=
    L.analyticOnNhd_toFun ρ hρ
  rw [zeros, Set.mem_ofPred_eq, hf.meromorphicOrderAt_eq, ← hf.analyticOrderAt_ne_zero]
  cases analyticOrderAt L.toFun ρ <;> simp [pos_iff_ne_zero]

/-- The **Riemann hypothesis** (LMFDB `lfunction.rh`) for an analytic L-function: its zeros `ρ`
with `re ρ > 0` lie on the critical line `re ρ = 1 / 2`. -/
def RiemannHypothesis : Prop :=
  ∀ ρ ∈ L.zeros, 0 < ρ.re → ρ.re = 1 / 2

end AnalyticLFunction

/-- The **generalized Riemann hypothesis** (LMFDB `lfunction.rh`): every analytic L-function
satisfies the Riemann hypothesis, that is, all of its zeros `ρ` with `re ρ > 0` satisfy
`re ρ = 1 / 2`. -/
def GeneralizedRiemannHypothesis : Prop :=
  ∀ L : AnalyticLFunction, L.RiemannHypothesis
