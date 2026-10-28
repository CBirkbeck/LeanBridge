import LeanBridge.ForMathlib.NumberTheory.LFunction.AnalyticRank
import LeanBridge.ForMathlib.NumberTheory.LFunction.CriticalStrip

/-!
# The central point of an analytic L-function

The functional equation `Λ(s) = ε conj (Λ (1 - conj s))` of an analytic L-function in its analytic
normalisation relates `s` and `1 - conj s`, which on the real axis is `s ↦ 1 - s`. Its fixed point
`s = 1 / 2` is the central point, the point of the critical line `re s = 1 / 2` on the real axis. In
the arithmetic normalisation of weight `w` the functional equation relates `s` and `1 + w - conj s`,
and the central point is `(w + 1) / 2`.

## Main definitions

* `AnalyticLFunction.centralPoint` and `AnalyticLFunction.arithmeticCentralPoint` (LMFDB
  `lfunction.central_point`): the central point in the analytic normalisation and in the arithmetic
  normalisation of weight `w`.

## Main results

* `AnalyticLFunction.criticalLine_inter_im_eq_zero` and
  `AnalyticLFunction.arithmeticCriticalLine_inter_im_eq_zero`: the central point is the point of the
  critical line on the real axis, in both normalisations.
* `AnalyticLFunction.one_sub_eq_self_iff` and `AnalyticLFunction.add_sub_eq_self_iff`: the central
  point is the fixed point of the functional equation, in both normalisations.
* `AnalyticLFunction.analyticRank_eq_analyticOrderNatAt_centralPoint`: the analytic rank is the
  order of vanishing at the central point.
-/

open Complex Set

namespace AnalyticLFunction

variable (L : AnalyticLFunction) (w : ℕ) {s : ℂ}

/-- The **central point** (LMFDB `lfunction.central_point`) `s = 1 / 2` of an analytic L-function in
its analytic normalisation: the point of the critical line on the real axis
(`criticalLine_inter_im_eq_zero`), equivalently the fixed point of the functional equation, which
relates `s` and `1 - conj s` (`one_sub_eq_self_iff`). It is the same point for every analytic
L-function. -/
noncomputable def centralPoint : ℂ :=
  1 / 2

/-- The **central point** (LMFDB `lfunction.central_point`) `s = (w + 1) / 2` of an analytic
L-function in its arithmetic normalisation of weight `w` (for the LMFDB, its motivic weight): the
point of the critical line `re s = (1 + w) / 2` on the real axis
(`arithmeticCriticalLine_inter_im_eq_zero`), equivalently the fixed point of the functional
equation, which relates `s` and `1 + w - conj s` (`add_sub_eq_self_iff`). It is the translate of
`centralPoint` by `w / 2`. -/
noncomputable def arithmeticCentralPoint : ℂ :=
  (w + 1) / 2

@[simp]
lemma centralPoint_re : centralPoint.re = 1 / 2 := by
  norm_num [centralPoint]

@[simp]
lemma centralPoint_im : centralPoint.im = 0 := by
  norm_num [centralPoint]

@[simp]
lemma arithmeticCentralPoint_re : (arithmeticCentralPoint w).re = (1 + w) / 2 := by
  norm_num [arithmeticCentralPoint, add_comm]

@[simp]
lemma arithmeticCentralPoint_im : (arithmeticCentralPoint w).im = 0 := by
  norm_num [arithmeticCentralPoint]

lemma arithmeticCentralPoint_sub : arithmeticCentralPoint w - w / 2 = centralPoint := by
  rw [arithmeticCentralPoint, centralPoint]
  ring1

@[simp]
lemma arithmeticCentralPoint_zero : arithmeticCentralPoint 0 = centralPoint := by
  simpa using arithmeticCentralPoint_sub 0

lemma centralPoint_mem_criticalLine : centralPoint ∈ criticalLine := by
  simp

lemma arithmeticCentralPoint_mem_arithmeticCriticalLine :
    arithmeticCentralPoint w ∈ arithmeticCriticalLine w := by
  simp

/-- The central point is the point of the critical line on the real axis. -/
lemma criticalLine_inter_im_eq_zero : criticalLine ∩ im ⁻¹' {0} = {centralPoint} := by
  ext s
  simp [Complex.ext_iff]

/-- In the arithmetic normalisation of weight `w`, the central point is the point of the critical
line on the real axis. -/
lemma arithmeticCriticalLine_inter_im_eq_zero :
    arithmeticCriticalLine w ∩ im ⁻¹' {0} = {arithmeticCentralPoint w} := by
  ext s
  simp [Complex.ext_iff]

/-- The central point is the fixed point of the functional equation, which relates `s` and
`1 - conj s`, or `1 - s` on the real axis. -/
lemma one_sub_eq_self_iff : 1 - s = s ↔ s = centralPoint := by
  rw [centralPoint]
  grind

/-- In the arithmetic normalisation of weight `w`, the central point is the fixed point of the
functional equation, which relates `s` and `1 + w - conj s`, or `1 + w - s` on the real axis. -/
lemma add_sub_eq_self_iff : 1 + w - s = s ↔ s = arithmeticCentralPoint w := by
  rw [arithmeticCentralPoint]
  grind

/-- The analytic rank of an analytic L-function is the order of vanishing at its central point. -/
lemma analyticRank_eq_analyticOrderNatAt_centralPoint :
    L.analyticRank = analyticOrderNatAt L.toFun centralPoint :=
  rfl

end AnalyticLFunction
