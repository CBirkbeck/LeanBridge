import LeanBridge.ForMathlib.NumberTheory.LFunction.Completed
import LeanBridge.ForMathlib.NumberTheory.LFunction.RiemannZeta

/-!
# The trivial zeros required by the functional equation

Let `L` be an analytic L-function of conductor `N`, with gamma factor
`L_∞(s) = ∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ)` and completed L-function `Λ(s) = N ^ (s / 2) L_∞(s) L(s)`.
The function `1 / L_∞` is entire and vanishes exactly at the points of
`AnalyticLFunction.SelbergData.gammaPoles`, which are therefore the poles of the gamma factor. Away
from them and from `s = 0, 1`, `L(s) = N ^ (-s / 2) Λ(s) / L_∞(s)`, so the orders at any `s` satisfy
`ord_s L = ord_s Λ + ord_s (1 / L_∞)`. The completed L-function has no poles except possibly at
`s = 0` and `s = 1`, and `1` is not a pole of `L_∞`. So `L` vanishes at every pole `s ≠ 0` of its
gamma factor, to at least the order of the pole, and also at `s = 0` when `0` is a pole of `L_∞` at
which `Λ` has no pole: the functional equation requires the trivial zeros (LMFDB
`lfunction.trivial_zero`). The exception is genuine: the gamma factor `Γ_ℝ(s)` of the Riemann zeta
function has a pole at `0`, where `Λ(s)` has one too and `ζ(0) = -1 / 2`. To the right of the
critical strip, `L` has no zeros (`AnalyticLFunction.toFun_ne_zero`) and no poles.

## Main results

* `AnalyticLFunction.SelbergData.meromorphicOrderAt_gammaFactor_neg_iff`: the poles of the gamma
  factor are the points of `gammaPoles`.
* `AnalyticLFunction.meromorphicOrderAt_toFun` (LMFDB `lfunction.trivial_zero`): the order of `L` is
  the order of `Λ` plus the order of `1 / L_∞`.
* `AnalyticLFunction.mem_trivialZeros_of_mem_gammaPoles` (LMFDB `lfunction.trivial_zero`): a pole of
  the gamma factor at which `Λ` has no pole is a trivial zero.
* `AnalyticLFunction.gammaPoles_diff_zero_subset_trivialZeros` (LMFDB `lfunction.trivial_zero`):
  every pole `s ≠ 0` of the gamma factor is a trivial zero.
* `AnalyticLFunction.zero_notMem_trivialZeros_zeta`: the pole `s = 0` of the gamma factor of the
  Riemann zeta function is not a zero.
-/

open Complex Filter Set

open scoped Topology

namespace AnalyticLFunction.SelbergData

variable (D : SelbergData) {s : ℂ}

lemma analyticAt_inv_gammaFactor : AnalyticAt ℂ (fun z ↦ (D.gammaFactor z)⁻¹) s :=
  D.differentiable_inv_gammaFactor.analyticAt s

lemma analyticOrderAt_inv_gammaFactor_ne_top :
    analyticOrderAt (fun z ↦ (D.gammaFactor z)⁻¹) s ≠ ⊤ := by
  refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    (fun z _ ↦ D.analyticAt_inv_gammaFactor) isPreconnected_univ (mem_univ 1) (mem_univ s) ?_
  rw [D.analyticAt_inv_gammaFactor.analyticOrderAt_eq_zero.mpr
    (inv_ne_zero (D.gammaFactor_ne_zero (by norm_num)))]
  exact ENat.zero_ne_top

lemma meromorphicOrderAt_inv_gammaFactor_pos_iff :
    0 < meromorphicOrderAt (fun z ↦ (D.gammaFactor z)⁻¹) s ↔ s ∈ D.gammaPoles := by
  rcases ENat.ne_top_iff_exists.mp D.analyticOrderAt_inv_gammaFactor_ne_top with ⟨n, hn⟩
  rw [← D.gammaFactor_eq_zero_iff, ← inv_eq_zero,
    ← D.analyticAt_inv_gammaFactor.analyticOrderAt_ne_zero,
    D.analyticAt_inv_gammaFactor.meromorphicOrderAt_eq, ← hn]
  simp [pos_iff_ne_zero]

lemma meromorphicOrderAt_inv_gammaFactor_ne_top :
    meromorphicOrderAt (fun z ↦ (D.gammaFactor z)⁻¹) s ≠ ⊤ := by
  rcases ENat.ne_top_iff_exists.mp (D.analyticOrderAt_inv_gammaFactor_ne_top (s := s)) with
    ⟨n, hn⟩
  simp [D.analyticAt_inv_gammaFactor.meromorphicOrderAt_eq, ← hn]

/-- **The poles of the gamma factor are the points of `gammaPoles`**: `L_∞(s)` has a pole exactly
at the points `-μⱼ - 2n` and `-νₖ - n`, `n ∈ ℕ`. -/
lemma meromorphicOrderAt_gammaFactor_neg_iff :
    meromorphicOrderAt D.gammaFactor s < 0 ↔ s ∈ D.gammaPoles := by
  have h : D.gammaFactor = (fun z ↦ (D.gammaFactor z)⁻¹)⁻¹ :=
    funext fun z ↦ (inv_inv _).symm
  rcases WithTop.ne_top_iff_exists.mp D.meromorphicOrderAt_inv_gammaFactor_ne_top with ⟨a, ha⟩
  rw [h, meromorphicOrderAt_inv, ← D.meromorphicOrderAt_inv_gammaFactor_pos_iff, ← ha]
  norm_cast
  omega

end AnalyticLFunction.SelbergData

namespace AnalyticLFunction

variable (L : AnalyticLFunction) {s : ℂ}

variable (s) in
private lemma eventually_ne_nhdsNE (a : ℂ) : ∀ᶠ z in 𝓝[≠] s, z ≠ a := by
  rcases eq_or_ne s a with rfl | h
  · exact self_mem_nhdsWithin
  · exact eventually_ne_nhdsWithin h

variable (s) in
lemma eventually_notMem_gammaPoles : ∀ᶠ z in 𝓝[≠] s, z ∉ L.selbergData.gammaPoles := by
  rcases L.selbergData.analyticAt_inv_gammaFactor.eventually_eq_zero_or_eventually_ne_zero
    (z₀ := s) with h | h
  · exact absurd (analyticOrderAt_eq_top.mpr h)
      L.selbergData.analyticOrderAt_inv_gammaFactor_ne_top
  · exact h.mono fun z hz hzp ↦
      hz (inv_eq_zero.mpr (L.selbergData.gammaFactor_eq_zero_iff.mpr hzp))

variable (s) in
lemma eventuallyEq_completed : L.completed =ᶠ[𝓝[≠] s]
    fun z ↦ (L.conductor : ℂ) ^ (z / 2) * L.selbergData.gammaFactor z * L.toFun z := by
  filter_upwards [L.eventually_notMem_gammaPoles s, eventually_ne_nhdsNE s 0,
    eventually_ne_nhdsNE s 1] with z hz hz₀ hz₁
  exact L.completed_eq_of_notMem_gammaPoles hz hz₀ hz₁

variable (s) in
lemma meromorphicAt_completed : MeromorphicAt L.completed s := by
  refine MeromorphicAt.congr ?_ (L.eventuallyEq_completed s).symm
  have hγ : MeromorphicAt L.selbergData.gammaFactor s :=
    MeromorphicAt.inv_iff.mp L.selbergData.analyticAt_inv_gammaFactor.meromorphicAt
  exact (L.analyticAt_conductor_cpow.meromorphicAt.mul hγ).mul (L.meromorphicAt_toFun' s)

variable (s) in
/-- **The functional equation determines the order of `L` from those of `Λ` and of `L_∞`** (LMFDB
`lfunction.trivial_zero`): at every `s`, the order of `L` is the order of the completed L-function
`Λ` plus the order of the entire function `1 / L_∞`, that is minus the order of the gamma factor. -/
lemma meromorphicOrderAt_toFun : meromorphicOrderAt L.toFun s = meromorphicOrderAt L.completed s +
    meromorphicOrderAt (fun z ↦ (L.selbergData.gammaFactor z)⁻¹) s := by
  have heq : L.toFun =ᶠ[𝓝[≠] s] (fun z : ℂ ↦ ((L.conductor : ℂ) ^ (z / 2))⁻¹) *
      (L.completed * fun z ↦ (L.selbergData.gammaFactor z)⁻¹) := by
    filter_upwards [L.eventually_notMem_gammaPoles s, eventually_ne_nhdsNE s 0,
      eventually_ne_nhdsNE s 1] with z hz hz₀ hz₁
    have hγ : L.selbergData.gammaFactor z ≠ 0 :=
      mt L.selbergData.gammaFactor_eq_zero_iff.mp hz
    have hN : (L.conductor : ℂ) ^ (z / 2) ≠ 0 :=
      L.conductor_cpow_ne_zero z
    rw [Pi.mul_apply, Pi.mul_apply, L.completed_eq_of_notMem_gammaPoles hz hz₀ hz₁]
    field_simp
  rw [meromorphicOrderAt_congr heq, meromorphicOrderAt_mul_of_ne_zero
    (L.analyticAt_conductor_cpow.fun_inv (L.conductor_cpow_ne_zero s))
    (inv_ne_zero (L.conductor_cpow_ne_zero s)), meromorphicOrderAt_mul
    (L.meromorphicAt_completed s) L.selbergData.analyticAt_inv_gammaFactor.meromorphicAt]

/-- **A pole of the gamma factor at which `Λ` has no pole is a trivial zero** (LMFDB
`lfunction.trivial_zero`). By `meromorphicOrderAt_toFun`, `L` vanishes there to at least the order
of the pole. -/
lemma mem_trivialZeros_of_mem_gammaPoles (hs : s ∈ L.selbergData.gammaPoles)
    (hΛ : 0 ≤ meromorphicOrderAt L.completed s) : s ∈ L.trivialZeros := by
  refine ⟨?_, hs⟩
  rw [zeros, mem_ofPred_eq, L.meromorphicOrderAt_toFun s]
  exact lt_add_of_nonneg_of_lt hΛ
    (L.selbergData.meromorphicOrderAt_inv_gammaFactor_pos_iff.mpr hs)

/-- **Every pole `s ≠ 0` of the gamma factor is a trivial zero** (LMFDB `lfunction.trivial_zero`):
the completed L-function is holomorphic there. -/
lemma gammaPoles_diff_zero_subset_trivialZeros :
    L.selbergData.gammaPoles \ {0} ⊆ L.trivialZeros := by
  rintro s ⟨hs, hs₀⟩
  have hs₁ : s ≠ 1 := by
    rintro rfl
    exact L.selbergData.notMem_gammaPoles_of_re_pos (by norm_num) hs
  refine L.mem_trivialZeros_of_mem_gammaPoles hs (AnalyticAt.meromorphicOrderAt_nonneg ?_)
  exact L.differentiableOn_completed.analyticAt <| (toFinite {0, 1}).isClosed.isOpen_compl.mem_nhds
    (by simp_all)

/-- **The pole `s = 0` of the gamma factor `Γ_ℝ(s)` of the Riemann zeta function is not a zero**:
`ζ(0) = -1 / 2`, so the hypothesis of `mem_trivialZeros_of_mem_gammaPoles` that `Λ` has no pole
cannot be dropped. -/
lemma zero_notMem_trivialZeros_zeta : (0 : ℂ) ∉ zeta.trivialZeros := fun h ↦ by
  have h₀ : riemannZeta 0 = 0 :=
    (zeta.mem_zeros_iff zero_ne_one).mp h.1
  rw [riemannZeta_zero] at h₀
  norm_num at h₀

end AnalyticLFunction
