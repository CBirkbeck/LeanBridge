import LeanBridge.ForMathlib.NumberTheory.LFunction.CriticalStrip
import LeanBridge.ForMathlib.NumberTheory.LFunction.TrivialZeroOrder

/-!
# Under the Riemann hypothesis the nontrivial zeros lie on the critical line

The Riemann hypothesis for an analytic L-function `L` (LMFDB `lfunction.rh`) constrains its zeros
`ρ` with `re ρ > 0`. Its nontrivial zeros (LMFDB `lfunction.trivial_zero`) are the zeros that are
not at poles of the gamma factor `L_∞`, and a priori they may have `re ρ ≤ 0`. The functional
equation rules this out. At a zero `ρ` of `L` that is not a pole of `L_∞`, the completed L-function
`Λ(s) = N ^ (s / 2) L_∞(s) L(s)` has positive order, also when `ρ` is `0` or `1`, where the value of
`Λ` carries no information. The functional equation `Λ(s) = ε conj (Λ (1 - conj s))` then gives `Λ`
positive order at the reflection `1 - conj ρ` of `ρ` in the critical line, and the order of `L` at
any point is at least that of `Λ`, since `1 / L_∞` is entire. So `1 - conj ρ` is a zero of `L`. If
`re ρ ≤ 0`, it is a zero of real part at least `1`, which the Riemann hypothesis forbids.

Conversely, a zero with positive real part is not at a pole of the gamma factor, so the Riemann
hypothesis is equivalent to the statement that every nontrivial zero lies on the critical line.

## Main results

* `AnalyticLFunction.one_sub_conj_mem_zeros`: the reflection of a nontrivial zero in the critical
  line is a zero.
* `AnalyticLFunction.RiemannHypothesis.zeros_diff_trivialZeros_subset_criticalLine` (LMFDB
  `lfunction.zeros`): under the Riemann hypothesis, every nontrivial zero lies on the critical
  line `re s = 1 / 2`.
* `AnalyticLFunction.riemannHypothesis_iff_zeros_diff_trivialZeros_subset_criticalLine` (LMFDB
  `lfunction.zeros`): the Riemann hypothesis holds if and only if every nontrivial zero lies on the
  critical line.
* `AnalyticLFunction.RiemannHypothesis.mem_arithmeticCriticalLine` (LMFDB `lfunction.zeros`): in
  the arithmetic normalisation of weight `w`, under the Riemann hypothesis every nontrivial zero
  lies on the critical line `re s = (1 + w) / 2`.
* `generalizedRiemannHypothesis_iff_zeros_diff_trivialZeros_subset_criticalLine` (LMFDB
  `lfunction.zeros`): the generalized Riemann hypothesis holds if and only if every nontrivial zero
  of every analytic L-function lies on the critical line.
-/

open Complex Filter Set

open scoped ComplexConjugate Topology

namespace AnalyticLFunction

variable (L : AnalyticLFunction) {w : ℕ} {s ρ : ℂ}

variable (s) in
lemma tendsto_one_sub_conj_nhdsNE :
    Tendsto (fun z : ℂ ↦ 1 - conj z) (𝓝[≠] (1 - conj s)) (𝓝[≠] s) := by
  have hc : Continuous fun z : ℂ ↦ 1 - conj z :=
    continuous_const.sub continuous_conj
  have h : Tendsto (fun z : ℂ ↦ 1 - conj z) (𝓝 (1 - conj s)) (𝓝 s) := by
    simpa using hc.tendsto (1 - conj s)
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (h.mono_left nhdsWithin_le_nhds) <| eventually_nhdsWithin_of_forall fun z hz hzs ↦ hz ?_
  simp [← mem_singleton_iff.mp hzs]

lemma meromorphicOrderAt_completed_one_sub_conj_pos (h : 0 < meromorphicOrderAt L.completed s) :
    0 < meromorphicOrderAt L.completed (1 - conj s) := by
  rw [← tendsto_zero_iff_meromorphicOrderAt_pos (L.meromorphicAt_completed _)] at h ⊢
  have h' :
      Tendsto (fun z ↦ L.sign * conj (L.completed (1 - conj z))) (𝓝[≠] (1 - conj s)) (𝓝 0) := by
    simpa using ((continuous_conj.tendsto _).comp
      (h.comp (tendsto_one_sub_conj_nhdsNE s))).const_mul L.sign
  refine h'.congr' ?_
  filter_upwards [nhdsNE_le_cofinite _ (eventually_cofinite_ne 0),
    nhdsNE_le_cofinite _ (eventually_cofinite_ne 1)] with z hz₀ hz₁
  exact (L.completed_eq_sign_mul_conj hz₀ hz₁).symm

/-- **The reflection of a nontrivial zero in the critical line is a zero**: if `ρ` is a zero of an
analytic L-function that is not at a pole of its gamma factor, then `1 - conj ρ` is a zero, by the
functional equation. -/
lemma one_sub_conj_mem_zeros (hρ : ρ ∈ L.zeros \ L.trivialZeros) : 1 - conj ρ ∈ L.zeros := by
  have hγ : meromorphicOrderAt (fun z ↦ (L.selbergData.gammaFactor z)⁻¹) ρ = 0 :=
    L.selbergData.analyticAt_inv_gammaFactor.meromorphicOrderAt_nonneg.antisymm' <| not_lt.mp
      fun h ↦ hρ.2 ⟨hρ.1, L.selbergData.meromorphicOrderAt_inv_gammaFactor_pos_iff.mp h⟩
  have hΛ : 0 < meromorphicOrderAt L.completed ρ := by
    simpa [zeros, L.meromorphicOrderAt_toFun ρ, hγ] using hρ.1
  rw [zeros, mem_ofPred_eq, L.meromorphicOrderAt_toFun]
  exact add_pos_of_pos_of_nonneg (L.meromorphicOrderAt_completed_one_sub_conj_pos hΛ)
    L.selbergData.analyticAt_inv_gammaFactor.meromorphicOrderAt_nonneg

variable {L} in
/-- **Under the Riemann hypothesis, every nontrivial zero lies on the critical line** (LMFDB
`lfunction.zeros`): if the zeros `ρ` with `re ρ > 0` of an analytic L-function satisfy
`re ρ = 1 / 2`, then so does every zero that is not a trivial zero, that is, not at a pole of the
gamma factor (LMFDB `lfunction.trivial_zero`). A nontrivial zero with `re ρ ≤ 0` would be reflected
by the functional equation to a zero of real part at least `1`. -/
lemma RiemannHypothesis.zeros_diff_trivialZeros_subset_criticalLine (h : L.RiemannHypothesis) :
    L.zeros \ L.trivialZeros ⊆ criticalLine := by
  intro ρ hρ
  rcases lt_or_ge 0 ρ.re with hre | hre
  · exact h ρ hρ.1 hre
  · have h' : (1 - conj ρ).re = 1 / 2 :=
      h _ (L.one_sub_conj_mem_zeros hρ) (by simpa using hre.trans_lt one_pos)
    rw [mem_criticalLine]
    simp at h'
    linarith

/-- **The Riemann hypothesis says that the nontrivial zeros lie on the critical line** (LMFDB
`lfunction.zeros`): an analytic L-function satisfies the Riemann hypothesis (LMFDB `lfunction.rh`),
which constrains its zeros with positive real part, if and only if every zero that is not at a pole
of its gamma factor lies on the critical line `re s = 1 / 2`. -/
lemma riemannHypothesis_iff_zeros_diff_trivialZeros_subset_criticalLine :
    L.RiemannHypothesis ↔ L.zeros \ L.trivialZeros ⊆ criticalLine :=
  ⟨fun h ↦ h.zeros_diff_trivialZeros_subset_criticalLine, fun h _ hρ hre ↦
    h ⟨hρ, fun hρt ↦ L.selbergData.notMem_gammaPoles_of_re_pos hre hρt.2⟩⟩

variable {L} in
/-- **In the arithmetic normalisation, under the Riemann hypothesis every nontrivial zero lies on
the critical line** (LMFDB `lfunction.zeros`): the nontrivial zeros of the arithmetic normalisation
`s ↦ L(s - w / 2)` of weight `w`, the `s` with `s - w / 2` a nontrivial zero of `L`, satisfy
`re s = (1 + w) / 2`. -/
lemma RiemannHypothesis.mem_arithmeticCriticalLine (h : L.RiemannHypothesis)
    (hs : s - w / 2 ∈ L.zeros \ L.trivialZeros) : s ∈ arithmeticCriticalLine w :=
  sub_mem_criticalLine_iff.mp <| h.zeros_diff_trivialZeros_subset_criticalLine hs

end AnalyticLFunction

/-- **The generalized Riemann hypothesis says that the nontrivial zeros of every analytic
L-function lie on the critical line** (LMFDB `lfunction.zeros`, `lfunction.rh`). -/
lemma generalizedRiemannHypothesis_iff_zeros_diff_trivialZeros_subset_criticalLine :
    GeneralizedRiemannHypothesis ↔
      ∀ L : AnalyticLFunction, L.zeros \ L.trivialZeros ⊆ AnalyticLFunction.criticalLine :=
  forall_congr' fun L ↦ L.riemannHypothesis_iff_zeros_diff_trivialZeros_subset_criticalLine
