import LeanBridge.ForMathlib.NumberTheory.LFunction.AnalyticRank
import LeanBridge.ForMathlib.NumberTheory.LFunction.ZFunction
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The parity of the analytic rank of a self-dual L-function

An analytic L-function `L(s) = ∑ aₙ n^{-s}` is self-dual (LMFDB `lfunction.self-dual`) if its
Dirichlet coefficients `aₙ` are real. Then `L(conj s) = conj L(s)`, first for `re s > 1` and then
on `ℂ ∖ {1}` by the identity theorem. If moreover its gamma factor is real at the central point
`s = 1 / 2`, as for real spectral parameters, then comparing the leading terms at `s = 1 / 2` of
both sides of the functional equation `Λ(s) = ε conj (Λ (1 - conj s))`, with
`Λ(s) = N ^ (s / 2) L_∞(s) L(s)` and `L(1 / 2 + t) ∼ c tʳ`, gives `ε = (-1)ʳ`: the sign of the
functional equation (LMFDB `lfunction.sign`) determines the parity of the analytic rank `r` (LMFDB
`lfunction.analytic_rank`), as LMFDB `mf.bianchi.sign` and `mf.bianchi.anr` state for the
L-functions of Bianchi newforms.

## Main results

* `AnalyticLFunction.conj_toFun_conj`: the continuation of a self-dual L-function satisfies
  `L(conj s) = conj L(s)`.
* `AnalyticLFunction.sign_eq_neg_one_pow_analyticRank` (LMFDB `mf.bianchi.anr`, `lfunction.sign`):
  the sign of a self-dual L-function whose gamma factor is real at the central point is `(-1)ʳ`,
  where `r` is its analytic rank.
-/

open Complex Filter Set

open scoped ComplexConjugate Topology

lemma Complex.conj_natCast_cpow_conj (n : ℕ) (s : ℂ) : conj ((n : ℂ) ^ conj s) = (n : ℂ) ^ s := by
  rw [cpow_conj _ _ (by simpa using Real.pi_ne_zero.symm), conj_conj, conj_natCast]

namespace AnalyticLFunction

variable (L : AnalyticLFunction) {s : ℂ}

lemma conj_LSeries_conj (hL : ∀ n ≠ 0, conj (L.coeff n) = L.coeff n) :
    conj (LSeries L.coeff (conj s)) = LSeries L.coeff s := by
  rw [LSeries, conj_tsum]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀, hL n hn,
      conj_natCast_cpow_conj]

/-- **The continuation of a self-dual L-function satisfies `L(conj s) = conj L(s)`**: if the
Dirichlet coefficients are real, then `conj L(conj s) = L(s)` for `re s > 1`, hence for every
`s ≠ 1` by the identity theorem. -/
lemma conj_toFun_conj (hL : ∀ n ≠ 0, conj (L.coeff n) = L.coeff n) (hs : s ≠ 1) :
    conj (L.toFun (conj s)) = L.toFun s := by
  have hg : AnalyticOnNhd ℂ (conj ∘ L.toFun ∘ conj) {1}ᶜ := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) isOpen_compl_singleton
    have hz' : conj z ≠ 1 := fun h ↦ hz <| mem_singleton_iff.mpr <| by
      rw [← conj_conj z, h, map_one]
    have hd : DifferentiableAt ℂ L.toFun (conj z) :=
      (L.differentiableOn_toFun (conj z) hz').differentiableAt (isOpen_compl_singleton.mem_nhds hz')
    simpa using hd.conj_conj.differentiableWithinAt
  have h₂ : (conj ∘ L.toFun ∘ conj) =ᶠ[𝓝 2] L.toFun := by
    filter_upwards [(continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (by norm_num : (2 : ℂ) ∈ re ⁻¹' Ioi 1)] with z hz
    have hz' : 1 < (conj z).re := by
      simpa using hz
    rw [Function.comp_apply, Function.comp_apply, L.toFun_eq_LSeries hz', L.toFun_eq_LSeries hz,
      L.conj_LSeries_conj hL]
  exact hg.eqOn_of_preconnected_of_eventuallyEq L.analyticOnNhd_toFun
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected (by norm_num) h₂ hs

/-- **The sign determines the parity of the analytic rank** (LMFDB `mf.bianchi.anr`,
`lfunction.sign`): for a self-dual L-function (real Dirichlet coefficients, LMFDB
`lfunction.self-dual`) whose gamma factor is real at the central point `s = 1 / 2`, the sign of the
functional equation is `(-1)ʳ`, where `r` is the analytic rank. -/
lemma sign_eq_neg_one_pow_analyticRank (hL : ∀ n ≠ 0, conj (L.coeff n) = L.coeff n)
    (hγ : conj (L.selbergData.gammaFactor (1 / 2)) = L.selbergData.gammaFactor (1 / 2)) :
    L.sign = (-1) ^ L.analyticRank := by
  rcases (L.analyticAt_toFun (s := 1 / 2) (by norm_num)).analyticOrderAt_eq_natCast.mp
    L.natCast_analyticRank.symm with ⟨m, hm, hm0, hℓ⟩
  have hG : ContinuousAt L.completingFactor (1 / 2) :=
    (L.differentiableAt_completingFactor (by norm_num)).continuousAt
  have hc : conj (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  have hfe : ∀ᶠ z in 𝓝[≠] (1 / 2), L.completingFactor z * m z = L.sign *
      (conj (L.completingFactor (1 - conj z)) * ((-1) ^ L.analyticRank * m (1 - z))) := by
    have h₁ : Tendsto (fun z : ℂ ↦ 1 - z) (𝓝 (1 / 2)) (𝓝 (1 / 2)) :=
      (continuous_const.sub continuous_id).tendsto' _ _ (by norm_num)
    filter_upwards [nhdsWithin_le_nhds hℓ, nhdsWithin_le_nhds (h₁.eventually hℓ),
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (1 / 2 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)),
      self_mem_nhdsWithin] with z hℓ₁ hℓ₂ hz hz'
    have hre : |z.re - 1 / 2| < 1 / 2 := by
      simpa using (abs_re_le_norm (z - 1 / 2)).trans_lt (by simpa [dist_eq] using hz)
    rw [abs_lt] at hre
    have hz0 : z ≠ 0 := fun h ↦ by
      norm_num [h] at hre
    have hz1 : z ≠ 1 := fun h ↦ by
      norm_num [h] at hre
    have hL' : conj (L.toFun (1 - conj z)) = L.toFun (1 - z) := by
      have h : conj (L.toFun (conj (1 - z))) = L.toFun (1 - z) :=
        L.conj_toFun_conj hL fun h ↦ hz0 (by linear_combination -h)
      rwa [map_sub, map_one] at h
    have hre₁ : 0 < (1 - conj z).re := by
      simp only [sub_re, one_re, conj_re]
      linarith
    have h : L.completed z = L.selbergData.sign * conj (L.completed (1 - conj z)) :=
      L.completed_eq_sign_mul_conj hz0 hz1
    rw [L.completed_eq_of_re_pos (by linarith) hz1, L.completed_eq_of_re_pos hre₁
      fun h ↦ hz0 (by simpa using h), map_mul, hL', hℓ₁, hℓ₂, smul_eq_mul, smul_eq_mul,
      (by ring1 : 1 - z - 1 / 2 = -1 * (z - 1 / 2)), mul_pow] at h
    refine mul_left_cancel₀ (pow_ne_zero L.analyticRank (sub_ne_zero.mpr hz')) ?_
    rw [sign]
    linear_combination h
  have hcN :
      conj ((L.conductor : ℂ) ^ ((1 / 2 : ℂ) / 2)) = (L.conductor : ℂ) ^ ((1 / 2 : ℂ) / 2) := by
    have h :
        conj ((L.conductor : ℂ) ^ conj ((1 / 2 : ℂ) / 2)) = (L.conductor : ℂ) ^ ((1 / 2 : ℂ) / 2) :=
      conj_natCast_cpow_conj L.conductor _
    rwa [map_div₀, hc, map_ofNat] at h
  have hB : ContinuousAt (fun z ↦ L.sign * (conj (L.completingFactor (1 - conj z)) *
      ((-1) ^ L.analyticRank * m (1 - z)))) (1 / 2) := by
    have h₁ : ContinuousAt (fun z ↦ L.completingFactor (1 - conj z)) (1 / 2) :=
      hG.comp_of_eq (continuous_const.sub continuous_conj).continuousAt <| by
        rw [hc]
        norm_num
    have h₂ : ContinuousAt (fun z ↦ m (1 - z)) (1 / 2) :=
      hm.continuousAt.comp_of_eq (continuous_const.sub continuous_id).continuousAt (by norm_num)
    exact continuousAt_const.mul ((continuous_conj.continuousAt.comp h₁).mul
      (continuousAt_const.mul h₂))
  have hlim : L.completingFactor (1 / 2) * m (1 / 2) = L.sign *
      (conj (L.completingFactor (1 - conj (1 / 2))) * ((-1) ^ L.analyticRank * m (1 - 1 / 2))) :=
    tendsto_nhds_unique ((hG.mul hm.continuousAt).tendsto.mono_left nhdsWithin_le_nhds)
      ((hB.tendsto.mono_left nhdsWithin_le_nhds).congr' (hfe.mono fun z h ↦ h.symm))
  rw [hc, sub_half, completingFactor, map_mul, hcN, hγ] at hlim
  have h₁ : 1 = L.sign * (-1) ^ L.analyticRank := mul_right_cancel₀
    (mul_ne_zero (L.completingFactor_ne_zero (s := 1 / 2) (by norm_num)) hm0) <| by
      rw [completingFactor]
      linear_combination hlim
  have h₂ : ((-1 : ℂ) ^ L.analyticRank) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  linear_combination (-(-1 : ℂ) ^ L.analyticRank) * h₁ + (-L.sign) * h₂

end AnalyticLFunction
