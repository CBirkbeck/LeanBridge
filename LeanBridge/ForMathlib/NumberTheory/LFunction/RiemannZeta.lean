import LeanBridge.ForMathlib.NumberTheory.LFunction.RiemannHypothesis
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The Riemann zeta function as an analytic L-function

The Riemann zeta function `ζ(s) = ∑ n ^ (-s)` is the analytic L-function of degree `1` and
conductor `1` with Euler factors `(1 - p ^ (-s))⁻¹`, spectral parameter `μ = 0` and sign `1`: its
completion is `Λ(s) = Γ_ℝ(s) ζ(s)`, which satisfies `Λ(s) = Λ(1 - s)`. Its Riemann hypothesis in
the sense of the LMFDB is Mathlib's `RiemannHypothesis`.

## Main definitions

* `AnalyticLFunction.zeta` (LMFDB `lfunction.riemann`): the Riemann zeta function as an analytic
  L-function.

## Main results

* `riemannZeta_eq_zero_iff_of_re_nonpos`: in the half-plane `re s ≤ 0`, the zeros of `ζ` are its
  trivial zeros `-2 (n + 1)`.
* `riemannHypothesis_iff_zeta`: Mathlib's `RiemannHypothesis` is the Riemann hypothesis for the
  analytic L-function `AnalyticLFunction.zeta`.
-/

open Complex Set
open scoped ComplexConjugate Polynomial Real

namespace AnalyticLFunction

/-- The **Riemann zeta function** (LMFDB `lfunction.riemann`) as an analytic L-function: the
Dirichlet series `∑ n ^ (-s)`, with Euler factors `(1 - p ^ (-s))⁻¹`, continued by `riemannZeta`
and completed by `completedRiemannZeta`, with Selberg data `(1, 1, (0 : ), 1)`. -/
noncomputable def zeta : AnalyticLFunction where
  coeff := 1
  toFun := riemannZeta
  completed := completedRiemannZeta
  selbergData :=
    { conductor := 1
      μ := {0}
      ν := 0
      sign := 1
      conductor_pos := one_pos
      re_eq_zero_or_one_of_mem_μ x hx := .inl <| by simp_all
      exists_two_mul_re_eq_of_mem_ν x hx := absurd hx (Multiset.notMem_zero x)
      im_sum_add_two_mul_sum := by simp }
  coeff_one := rfl
  coeff_mul_of_coprime _ := (mul_one 1).symm
  exists_eulerFactor p hp := by
    have hF : (1 - Polynomial.X : ℂ[X]).natDegree = 1 := by
      rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt] <;> simp
    refine ⟨1 - Polynomial.X, ?_, ?_, ?_⟩
    · simp [hF, SelbergData.degree]
    · simp [hF, SelbergData.degree, hp.ne_one]
    · rw [mul_comm, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X]
      exact PowerSeries.mk_one_mul_one_sub_eq_one ℂ
  LSeriesSummable_coeff hs := LSeriesSummable_one_iff.mpr hs
  toFun_eq_LSeries hs := (LSeries_one_eq_riemannZeta hs).symm
  differentiableOn_toFun s hs := (differentiableAt_riemannZeta hs).differentiableWithinAt
  meromorphicAt_toFun := by
    refine (((analyticAt_id.sub (analyticAt_const (v := 1))).meromorphicAt.inv).mul
      (differentiable_riemannZeta₁.analyticAt 1).meromorphicAt).congr ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (riemannZeta_eq_inv_sub_mul hs).symm
  completed_eq {s} hs := by
    have h₀ : s ≠ 0 := by
      rintro rfl
      norm_num at hs
    have hΓ : Gammaℝ s ≠ 0 :=
      Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs)
    simp [SelbergData.gammaFactor, riemannZeta_def_of_ne_zero h₀]
    field_simp
  differentiableOn_completed s hs := by
    simp only [mem_compl_iff, mem_insert_iff, not_or] at hs
    exact (differentiableAt_completedZeta hs.1 hs.2).differentiableWithinAt
  completed_eq_sign_mul_conj _ _ := by
    rw [completedRiemannZeta_one_sub, completedRiemannZeta_conj, conj_conj, one_mul]

@[simp]
lemma zeta_toFun : zeta.toFun = riemannZeta :=
  rfl

@[simp]
lemma zeta_completed : zeta.completed = completedRiemannZeta :=
  rfl

@[simp]
lemma degree_zeta : zeta.degree = 1 :=
  rfl

@[simp]
lemma conductor_zeta : zeta.conductor = 1 :=
  rfl

@[simp]
lemma sign_zeta : zeta.sign = 1 :=
  rfl

lemma one_notMem_zeros_zeta : 1 ∉ zeta.zeros := by
  have hm : MeromorphicAt riemannZeta 1 :=
    zeta.meromorphicAt_toFun
  have h : meromorphicOrderAt riemannZeta 1 = (-1 : ℤ) := by
    rw [meromorphicOrderAt_eq_int_iff hm]
    refine ⟨riemannZeta₁, differentiable_riemannZeta₁.analyticAt 1, by simp, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [riemannZeta_eq_inv_sub_mul hs, zpow_neg_one, smul_eq_mul]
  simp [zeros, h]

end AnalyticLFunction

/-- In the half-plane `re s ≤ 0`, the zeros of the Riemann zeta function are its trivial zeros
`-2 (n + 1)`. -/
lemma riemannZeta_eq_zero_iff_of_re_nonpos {s : ℂ} (hre : s.re ≤ 0) :
    riemannZeta s = 0 ↔ ∃ n : ℕ, s = -2 * (n + 1) := by
  refine ⟨fun hs ↦ ?_, fun ⟨n, hn⟩ ↦ hn ▸ riemannZeta_neg_two_mul_nat_add_one n⟩
  have h₀ : s ≠ 0 := by
    rintro rfl
    norm_num [riemannZeta_zero] at hs
  have hre₁ : 1 ≤ (1 - s).re := by
    rw [sub_re, one_re]
    linarith
  have hn (n : ℕ) : 1 - s ≠ -n := by
    intro hn
    have h : (1 - s).re = (-n : ℂ).re :=
      congrArg re hn
    simp only [neg_re, natCast_re] at h
    linarith [n.cast_nonneg (α := ℝ)]
  have hπ : (π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcos : cos (π * (1 - s) / 2) = 0 := by
    simpa [hs, Gamma_ne_zero_of_re_pos (by linarith : 0 < (1 - s).re),
      riemannZeta_ne_zero_of_one_le_re hre₁] using
      (riemannZeta_one_sub hn (by simpa using h₀)).symm
  rcases cos_eq_zero_iff.mp hcos with ⟨k, hk⟩
  have hsk : s = -2 * k := by
    linear_combination -(mul_left_cancel₀ hπ (by linear_combination 2 * hk) : 1 - s = 2 * k + 1)
  have hk₀ : 0 < k := by
    rcases lt_trichotomy k 0 with hk' | rfl | hk'
    · have h : s.re = (-2 * k : ℂ).re :=
        congrArg re hsk
      simp at h
      linarith [(Int.cast_lt_zero.mpr hk' : (k : ℝ) < 0)]
    · simp [hsk] at h₀
    · exact hk'
  lift k to ℕ using hk₀.le
  rcases Nat.exists_eq_succ_of_ne_zero (by exact_mod_cast hk₀.ne' : k ≠ 0) with ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  rw [hsk]
  push_cast
  ring1

/-- Mathlib's `RiemannHypothesis` is the Riemann hypothesis (LMFDB `lfunction.rh`) for the Riemann
zeta function as an analytic L-function. -/
lemma riemannHypothesis_iff_zeta :
    RiemannHypothesis ↔ AnalyticLFunction.zeta.RiemannHypothesis := by
  refine ⟨fun h ρ hρ hre ↦ ?_, fun h s hs htriv h₁ ↦ ?_⟩
  · have h₁ : ρ ≠ 1 :=
      ne_of_mem_of_not_mem hρ AnalyticLFunction.one_notMem_zeros_zeta
    refine h ρ ((AnalyticLFunction.zeta.mem_zeros_iff h₁).mp hρ) ?_ h₁
    rintro ⟨n, rfl⟩
    simp at hre
    linarith [n.cast_nonneg (α := ℝ)]
  · rcases lt_or_ge 0 s.re with hre | hre
    · exact h s ((AnalyticLFunction.zeta.mem_zeros_iff h₁).mpr hs) hre
    · exact absurd ((riemannZeta_eq_zero_iff_of_re_nonpos hre).mp hs) htriv
