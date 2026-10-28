import LeanBridge.ForMathlib.NumberTheory.LFunction.CentralPoint

/-!
# The lowest zero of an analytic L-function

The lowest zero of an analytic L-function is the least `γ > 0` such that `L(1 / 2 + i γ) = 0`.
The continuation of an analytic L-function is holomorphic on the connected set `ℂ \ {1}` and does
not vanish identically, so its zeros are isolated there; hence the infimum of these `γ` is attained
whenever there is one, even when `L(1 / 2) = 0`.

## Main definitions

* `AnalyticLFunction.lowestZero` (LMFDB `lfunction.zeros`): the lowest zero of an analytic
  L-function.

## Main results

* `AnalyticLFunction.eventually_toFun_ne_zero`: the zeros of an analytic L-function are isolated.
* `AnalyticLFunction.lowestZero_pos`,
  `AnalyticLFunction.centralPoint_add_lowestZero_mul_I_mem_zeros` and
  `AnalyticLFunction.lowestZero_le`: when the L-function has a zero `1 / 2 + i γ` with `γ > 0`, the
  lowest zero is the least such `γ`.
-/

open Complex Filter Set
open scoped Topology

namespace AnalyticLFunction

variable (L : AnalyticLFunction) {z : ℂ} {γ : ℝ}

/-- The zeros of an analytic L-function are isolated: away from `s = 1`, it does not vanish on a
punctured neighbourhood of any point. -/
lemma eventually_toFun_ne_zero (hz : z ≠ 1) : ∀ᶠ s in 𝓝[≠] z, L.toFun s ≠ 0 := by
  refine (L.analyticOnNhd_toFun z hz).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    fun h ↦ ?_
  rcases L.exists_toFun_ne_zero with ⟨x, hx, hL⟩
  refine hL <| L.analyticOnNhd_toFun.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected hz h ?_
  simpa using (ofReal_ne_one.mpr hx.ne')

/-- The **lowest zero** (LMFDB `lfunction.zeros`) of an analytic L-function: the least `γ > 0` such
that `L(1 / 2 + i γ) = 0`. It is a positive real number even when `L(1 / 2) = 0`; the infimum is
attained when there is such a `γ` (`centralPoint_add_lowestZero_mul_I_mem_zeros`), since the zeros
are isolated. When there is none, it takes the junk value `0`. -/
noncomputable def lowestZero : ℝ :=
  sInf {γ : ℝ | 0 < γ ∧ centralPoint + γ * I ∈ L.zeros}

lemma lowestZero_mem (h : ∃ γ : ℝ, 0 < γ ∧ centralPoint + γ * I ∈ L.zeros) :
    L.lowestZero ∈ {γ : ℝ | 0 < γ ∧ centralPoint + γ * I ∈ L.zeros} := by
  by_contra hc
  have hb : BddBelow {γ : ℝ | 0 < γ ∧ centralPoint + γ * I ∈ L.zeros} :=
    ⟨0, fun γ hγ ↦ hγ.1.le⟩
  have hne (γ : ℝ) : centralPoint + γ * I ≠ 1 :=
    ne_of_apply_ne re <| by norm_num
  have hfr : ∃ᶠ γ : ℝ in 𝓝[≠] L.lowestZero, L.toFun (centralPoint + γ * I) = 0 :=
    (frequently_nhdsWithin_iff.mpr <| (mem_closure_iff_frequently.mp <| csInf_mem_closure
      (s := {γ : ℝ | 0 < γ ∧ centralPoint + γ * I ∈ L.zeros}) h hb).mono
        fun γ hγ ↦ ⟨hγ, fun hγc : γ = L.lowestZero ↦ hc <| hγc ▸ hγ⟩).mono
          fun γ hγ ↦ (L.mem_zeros_iff (hne γ)).mp hγ.2
  have ht : Tendsto (fun γ : ℝ ↦ centralPoint + γ * I) (𝓝[≠] L.lowestZero)
      (𝓝[≠] (centralPoint + L.lowestZero * I)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((continuous_const.add (continuous_ofReal.mul continuous_const)).tendsto _ |>.mono_left
        nhdsWithin_le_nhds) <| eventually_nhdsWithin_of_forall fun γ hγ h ↦ hγ <| by
        simpa using congrArg im h
  exact ((ht.frequently (p := fun s ↦ L.toFun s = 0) hfr).and_eventually
    (L.eventually_toFun_ne_zero (hne _))).exists.elim fun _ hs ↦ hs.2 hs.1

/-- When an analytic L-function has a zero `1 / 2 + i γ` with `γ > 0`, its lowest zero is positive.
-/
lemma lowestZero_pos (h : ∃ γ : ℝ, 0 < γ ∧ centralPoint + γ * I ∈ L.zeros) : 0 < L.lowestZero :=
  (L.lowestZero_mem h).1

/-- When an analytic L-function has a zero `1 / 2 + i γ` with `γ > 0`, its lowest zero `γ₀` gives a
zero `1 / 2 + i γ₀`. -/
lemma centralPoint_add_lowestZero_mul_I_mem_zeros
    (h : ∃ γ : ℝ, 0 < γ ∧ centralPoint + γ * I ∈ L.zeros) :
    centralPoint + L.lowestZero * I ∈ L.zeros :=
  (L.lowestZero_mem h).2

/-- The lowest zero is at most every `γ > 0` with `L(1 / 2 + i γ) = 0`. -/
lemma lowestZero_le (hγ : 0 < γ) (h : centralPoint + γ * I ∈ L.zeros) : L.lowestZero ≤ γ :=
  csInf_le ⟨0, fun _ hγ ↦ hγ.1.le⟩ ⟨hγ, h⟩

lemma lowestZero_eq_zero (h : ¬∃ γ : ℝ, 0 < γ ∧ centralPoint + γ * I ∈ L.zeros) :
    L.lowestZero = 0 := by
  rw [lowestZero, (not_nonempty_iff_eq_empty (s := {γ : ℝ | 0 < γ ∧ _})).mp h, Real.sInf_empty]

end AnalyticLFunction
