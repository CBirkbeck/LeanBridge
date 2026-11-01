import LeanBridge.ForMathlib.Analysis.Fourier.PeriodicFourierSeries
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Fourier series of smooth functions on a two-dimensional torus

A smooth function `G : ℝ × ℝ → ℂ` of period `1` in each variable is the sum of its Fourier series
`G(x, y) = ∑_{(m, n) ∈ ℤ²} c_{m,n} e^{2πi(mx + ny)}`,
`c_{m,n} = ∫_0^1 ∫_0^1 e^{-2πi(ms + nt)} G(s, t) dt ds`, which converges absolutely
(`hasSum_fourierSeries_prod_of_contDiff`). Integrating by parts twice in each variable, the
coefficients of `G`, `∂_t² G`, `∂_s² G` and `∂_s² ∂_t² G` (the periodic boundary terms cancel) give
`|c_{m,n}| ≤ C u(m) u(n)` with `u(0) = 1` and `u(k) = 1 / k²` otherwise, which is summable over
`ℤ²`. The series in `t` converges to `G(s, ·)` for each `s` (the one-dimensional `C²` case,
`hasSum_fourierCoeffOn_of_periodic`), and the series in `s` of its coefficients, continuous periodic
functions with summable Fourier coefficients, converges to them, so the double series, summable,
converges to `G`.

Transported along an `ℝ`-basis `(b₀, b₁)` of `ℂ`, this is Fourier inversion on the torus `ℂ / Λ`,
`Λ = ℤ b₀ + ℤ b₁`: a smooth `Λ`-periodic `h : ℂ → ℂ` is the sum over the frequencies `ν ∈ ℂ` with
`ψ(νl) = 1` on `Λ`, `ψ(z) = e^{2πi(z + z̄)}`, of `ψ(νx) vol(P)⁻¹ ∫_P ψ(-νt) h(t) dt`, where `P` is
the fundamental parallelogram of `Λ` (`hasSum_fourierSeries_zlattice_of_contDiff`): every such `ν`
is the dual frequency of a unique `(m, n) ∈ ℤ²`, `ν x + conj(ν x) = m s + n t` for
`x = s b₀ + t b₁`, and the integral over `P` is `vol(P)` times the integral over the unit square
(`inv_mul_setIntegral_fundamentalDomain`, the change of variables `(s, t) ↦ s b₀ + t b₁`).

## Main results

* `hasSum_fourierSeries_prod_of_contDiff`: Fourier inversion for smooth functions on `ℝ² / ℤ²`.
* `inv_mul_setIntegral_fundamentalDomain`: the normalised integral over the fundamental
  parallelogram of a lattice of `ℂ` is the integral over the unit square.
* `hasSum_fourierSeries_zlattice_of_contDiff`: Fourier inversion for smooth functions on `ℂ / Λ`.
-/

open Complex Function MeasureTheory Module Real Set

open scoped ComplexConjugate ContDiff

variable (B : Basis (Fin 2) ℝ ℂ) {g g' : ℝ → ℂ} {G H : ℝ × ℝ → ℂ} {f : ℂ → ℂ} {m n : ℤ} {M : ℝ}
  {ν ν' : ℂ} (x y : ℝ) (z : ℂ)

private lemma fourierCoeffOn_zero_one_eq : fourierCoeffOn (lt_add_of_pos_right 0 one_pos) g n =
    ∫ t in (0 : ℝ)..1, cexp (-(2 * π * I * n * t)) * g t := by
  rw [fourierCoeffOn_eq_integral]
  simp only [fourier_coe_apply]
  norm_num

private lemma intervalIntegral_cexp_mul_eq (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g')
    (hp : Periodic g 1) (hn : n ≠ 0) : ∫ t in (0 : ℝ)..1, cexp (-(2 * π * I * n * t)) * g t =
      1 / (2 * π * I * n) * ∫ t in (0 : ℝ)..1, cexp (-(2 * π * I * n * t)) * g' t := by
  have hT : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  rw [← fourierCoeffOn_zero_one_eq, ← fourierCoeffOn_zero_one_eq]
  simpa using fourierCoeffOn_eq_mul_fourierCoeffOn_deriv hg hg' hp hn

private lemma norm_intervalIntegral_cexp_mul_le (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖g t‖ ≤ M) :
    ‖∫ t in (0 : ℝ)..1, cexp (-(2 * π * I * n * t)) * g t‖ ≤ M := by
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := M) fun t ht ↦ ?_).trans_eq
    (by simp)
  rw [uIoc_of_le zero_le_one] at ht
  rw [norm_mul, norm_exp]
  simpa using hM t (Ioc_subset_Icc_self ht)

variable (H) in
/-- `H : ℝ × ℝ → ℂ` is smooth and of period `1` in each variable. -/
private structure IsSmoothBiperiodic : Prop where
  contDiff : ContDiff ℝ ∞ H
  add_fst (p : ℝ × ℝ) : H (p + (1, 0)) = H p
  add_snd (p : ℝ × ℝ) : H (p + (0, 1)) = H p

private lemma IsSmoothBiperiodic.fderiv (h : IsSmoothBiperiodic H) (v : ℝ × ℝ) :
    IsSmoothBiperiodic fun p ↦ fderiv ℝ H p v where
  contDiff := (contDiff_infty_iff_fderiv.mp h.contDiff).2.clm_apply contDiff_const
  add_fst p := by
    rw [← fderiv_comp_add_right, funext h.add_fst]
  add_snd p := by
    rw [← fderiv_comp_add_right, funext h.add_snd]

private lemma IsSmoothBiperiodic.differentiable (h : IsSmoothBiperiodic H) : Differentiable ℝ H :=
  (contDiff_infty_iff_fderiv.mp h.contDiff).1

private lemma IsSmoothBiperiodic.apply_add_one_fst (h : IsSmoothBiperiodic H) :
    H (x + 1, y) = H (x, y) := by
  simpa using h.add_fst (x, y)

private lemma IsSmoothBiperiodic.periodic_fst (h : IsSmoothBiperiodic H) :
    Periodic (fun s ↦ H (s, y)) 1 :=
  fun s ↦ h.apply_add_one_fst s y

private lemma IsSmoothBiperiodic.periodic_snd (h : IsSmoothBiperiodic H) :
    Periodic (fun t ↦ H (x, t)) 1 :=
  fun t ↦ by simpa using h.add_snd (x, t)

private lemma hasDerivAt_snd_of_differentiable (h : Differentiable ℝ H) :
    HasDerivAt (fun t ↦ H (x, t)) (fderiv ℝ H (x, y) (0, 1)) y :=
  (h (x, y)).hasFDerivAt.comp_hasDerivAt y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))

private lemma hasDerivAt_fst_of_differentiable (h : Differentiable ℝ H) :
    HasDerivAt (fun s ↦ H (s, y)) (fderiv ℝ H (x, y) (1, 0)) x :=
  (h (x, y)).hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

variable (H m n) in
/-- The Fourier coefficient `c_{m,n} = ∫_0^1 ∫_0^1 e^{-2πi(ms + nt)} H(s, t) dt ds`. -/
private noncomputable def doubleCoeff : ℂ :=
  ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, cexp (-(2 * π * I * (m * s + n * t))) * H (s, t)

variable (H n) in
/-- The Fourier coefficient `∫_0^1 e^{-2πint} H(x, t) dt` in the second variable. -/
private noncomputable def sndCoeff : ℂ :=
  ∫ t in (0 : ℝ)..1, cexp (-(2 * π * I * n * t)) * H (x, t)

private lemma doubleCoeff_eq_snd :
    doubleCoeff H m n = ∫ s in (0 : ℝ)..1, cexp (-(2 * π * I * m * s)) * sndCoeff H n s := by
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  rw [sndCoeff, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring1

private lemma doubleCoeff_eq_fst (hH : Continuous H) : doubleCoeff H m n =
    ∫ t in (0 : ℝ)..1, cexp (-(2 * π * I * n * t)) *
      ∫ s in (0 : ℝ)..1, cexp (-(2 * π * I * m * s)) * H (s, t) := by
  rw [doubleCoeff, intervalIntegral_intervalIntegral_swap]
  · refine intervalIntegral.integral_congr fun t _ ↦ ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    ring1
  · rw [uIoc_of_le zero_le_one]
    exact ((by fun_prop : Continuous _).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
        (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

private lemma doubleCoeff_eq_snd_deriv (hH : IsSmoothBiperiodic H) (hn : n ≠ 0) :
    doubleCoeff H m n = 1 / (2 * π * I * n) * (1 / (2 * π * I * n) *
      doubleCoeff (fun p ↦ fderiv ℝ (fun q ↦ fderiv ℝ H q (0, 1)) p (0, 1)) m n) := by
  have h₁ : IsSmoothBiperiodic fun q ↦ fderiv ℝ H q (0, 1) :=
    hH.fderiv (0, 1)
  have h₂ : IsSmoothBiperiodic fun p ↦ fderiv ℝ (fun q ↦ fderiv ℝ H q (0, 1)) p (0, 1) :=
    h₁.fderiv (0, 1)
  rw [doubleCoeff_eq_snd, doubleCoeff_eq_snd, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  simp only [sndCoeff]
  rw [intervalIntegral_cexp_mul_eq (hasDerivAt_snd_of_differentiable s · hH.differentiable)
    (h₁.contDiff.continuous.comp (by fun_prop)) (hH.periodic_snd s) hn,
    intervalIntegral_cexp_mul_eq (hasDerivAt_snd_of_differentiable s · h₁.differentiable)
    (h₂.contDiff.continuous.comp (by fun_prop)) (h₁.periodic_snd s) hn]
  ring1

private lemma doubleCoeff_eq_fst_deriv (hH : IsSmoothBiperiodic H) (hm : m ≠ 0) :
    doubleCoeff H m n = 1 / (2 * π * I * m) * (1 / (2 * π * I * m) *
      doubleCoeff (fun p ↦ fderiv ℝ (fun q ↦ fderiv ℝ H q (1, 0)) p (1, 0)) m n) := by
  have h₁ : IsSmoothBiperiodic fun q ↦ fderiv ℝ H q (1, 0) :=
    hH.fderiv (1, 0)
  have h₂ : IsSmoothBiperiodic fun p ↦ fderiv ℝ (fun q ↦ fderiv ℝ H q (1, 0)) p (1, 0) :=
    h₁.fderiv (1, 0)
  rw [doubleCoeff_eq_fst hH.contDiff.continuous, doubleCoeff_eq_fst h₂.contDiff.continuous,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [intervalIntegral_cexp_mul_eq (hasDerivAt_fst_of_differentiable · t hH.differentiable)
    (h₁.contDiff.continuous.comp (by fun_prop)) (hH.periodic_fst t) hm,
    intervalIntegral_cexp_mul_eq (hasDerivAt_fst_of_differentiable · t h₁.differentiable)
    (h₂.contDiff.continuous.comp (by fun_prop)) (h₁.periodic_fst t) hm]
  ring1

variable (m n) in
private lemma norm_doubleCoeff_le (hM : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖H p‖ ≤ M) :
    ‖doubleCoeff H m n‖ ≤ M := by
  rw [doubleCoeff_eq_snd]
  exact norm_intervalIntegral_cexp_mul_le fun s hs ↦
    norm_intervalIntegral_cexp_mul_le fun t ht ↦ hM (s, t) ⟨hs, ht⟩

private lemma norm_inv_two_pi_I_mul_le (hn : n ≠ 0) :
    ‖1 / (2 * π * I * n) * (1 / (2 * π * I * n) * z)‖ ≤ 1 / (n : ℝ) ^ 2 * ‖z‖ := by
  have hk : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hn)
  have hn' : ‖1 / (2 * π * I * n)‖ = 1 / (2 * π * |(n : ℝ)|) := by
    simp [abs_of_pos pi_pos]
  rw [norm_mul, norm_mul, hn', ← mul_assoc, ← sq_abs (n : ℝ)]
  gcongr
  rw [div_mul_div_comm, one_mul]
  gcongr
  have h2 : |(n : ℝ)| ≤ 2 * π * |(n : ℝ)| := le_mul_of_one_le_left hk.le (by linarith [two_le_pi])
  rw [sq]
  exact mul_le_mul h2 h2 hk.le (by positivity)

private lemma exists_norm_le_of_continuous (h : Continuous H) :
    ∃ M, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖H p‖ ≤ M :=
  (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn h.continuousOn

private lemma summable_doubleCoeff (hG : IsSmoothBiperiodic G) :
    Summable fun q : ℤ × ℤ ↦ doubleCoeff G q.1 q.2 := by
  let u : ℤ → ℝ := update (fun k : ℤ ↦ 1 / (k : ℝ) ^ 2) 0 1
  have hu : Summable u := (Real.summable_one_div_int_pow.mpr one_lt_two).update 0 1
  have hu₀ : 0 ≤ u := fun k ↦ by
    by_cases hk : k = 0
    · simp [u, hk]
    · simp only [u, update_of_ne hk]
      positivity
  have h₂ : IsSmoothBiperiodic fun p ↦ fderiv ℝ (fun q ↦ fderiv ℝ G q (0, 1)) p (0, 1) :=
    (hG.fderiv (0, 1)).fderiv (0, 1)
  have h₁ : IsSmoothBiperiodic fun p ↦ fderiv ℝ (fun q ↦ fderiv ℝ G q (1, 0)) p (1, 0) :=
    (hG.fderiv (1, 0)).fderiv (1, 0)
  have h₃ : IsSmoothBiperiodic fun p ↦ fderiv ℝ (fun q ↦ fderiv ℝ
      (fun p ↦ fderiv ℝ (fun q ↦ fderiv ℝ G q (0, 1)) p (0, 1)) q (1, 0)) p (1, 0) :=
    (h₂.fderiv (1, 0)).fderiv (1, 0)
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩
  rcases exists_norm_le_of_continuous hG.contDiff.continuous with ⟨M₀, hM₀⟩
  rcases exists_norm_le_of_continuous h₁.contDiff.continuous with ⟨M₁, hM₁⟩
  rcases exists_norm_le_of_continuous h₂.contDiff.continuous with ⟨M₂, hM₂⟩
  rcases exists_norm_le_of_continuous h₃.contDiff.continuous with ⟨M₃, hM₃⟩
  have hM₀' : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ _ h0)
  have hM₁' : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ _ h0)
  have hM₂' : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ _ h0)
  have hM₃' : 0 ≤ M₃ := (norm_nonneg _).trans (hM₃ _ h0)
  refine .of_norm_bounded ((hu.mul_of_nonneg hu hu₀ hu₀).mul_left (M₀ + M₁ + M₂ + M₃)) ?_
  rintro ⟨m, n⟩
  by_cases hm : m = 0 <;> by_cases hn : n = 0
  · subst hm hn
    simp only [u, update_self]
    linarith [norm_doubleCoeff_le 0 0 hM₀]
  · subst hm
    simp only [u, update_self, update_of_ne hn, one_mul]
    rw [doubleCoeff_eq_snd_deriv hG hn]
    refine (norm_inv_two_pi_I_mul_le _ hn).trans ?_
    rw [mul_comm (M₀ + M₁ + M₂ + M₃)]
    gcongr
    linarith [norm_doubleCoeff_le 0 n hM₂]
  · subst hn
    simp only [u, update_self, update_of_ne hm, mul_one]
    rw [doubleCoeff_eq_fst_deriv hG hm]
    refine (norm_inv_two_pi_I_mul_le _ hm).trans ?_
    rw [mul_comm (M₀ + M₁ + M₂ + M₃)]
    gcongr
    linarith [norm_doubleCoeff_le m 0 hM₁]
  · simp only [u, update_of_ne hm, update_of_ne hn]
    rw [doubleCoeff_eq_snd_deriv hG hn, doubleCoeff_eq_fst_deriv h₂ hm]
    refine (norm_inv_two_pi_I_mul_le _ hn).trans <| (mul_le_mul_of_nonneg_left
      ((norm_inv_two_pi_I_mul_le _ hm).trans (mul_le_mul_of_nonneg_left
        (norm_doubleCoeff_le m n hM₃) (by positivity))) (by positivity)).trans ?_
    have hK : M₃ ≤ M₀ + M₁ + M₂ + M₃ := by
      linarith
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK (by positivity))
      (by positivity)).trans_eq (by ring1)

private lemma hasSum_fourierCoeffOn_of_summable {T : ℝ} [hT : Fact (0 < T)] (hg : Continuous g)
    (hp : Periodic g T) (hs : Summable (fourierCoeffOn (lt_add_of_pos_right 0 hT.out) g)) :
    HasSum (fun n : ℤ ↦ fourierCoeffOn (lt_add_of_pos_right 0 hT.out) g n •
      fourier n (x : AddCircle T)) (g x) := by
  have hcont : Continuous (AddCircle.liftIco T 0 g) :=
    AddCircle.liftIco_continuous (hp 0).symm hg.continuousOn
  have hF :
      fourierCoeff (AddCircle.liftIco T 0 g) = fourierCoeffOn (lt_add_of_pos_right 0 hT.out) g :=
    funext fun n ↦ fourierCoeff_liftIco_eq g n
  have h0 : Summable (fourierCoeff (⟨_, hcont⟩ : C(AddCircle T, ℂ))) := by
    rw [ContinuousMap.coe_mk, hF]
    exact hs
  have h : HasSum (fun n ↦ fourierCoeff (⟨_, hcont⟩ : C(AddCircle T, ℂ)) n •
      fourier n (x : AddCircle T)) ((⟨_, hcont⟩ : C(AddCircle T, ℂ)) x) :=
    has_pointwise_sum_fourier_series_of_summable h0 x
  rw [ContinuousMap.coe_mk, hF] at h
  convert h using 1
  have hy : toIcoMod hT.out 0 x = x - toIcoDiv hT.out 0 x • T := by
    rw [← self_sub_toIcoMod, sub_sub_cancel]
  have hcoe : ((toIcoMod hT.out 0 x : ℝ) : AddCircle T) = (x : AddCircle T) := by
    rw [hy, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_zsmul, AddCircle.coe_period, smul_zero,
      sub_zero]
  rw [← hcoe, AddCircle.liftIco_coe_apply (toIcoMod_mem_Ico hT.out 0 x), hy, hp.sub_zsmul_eq]

private lemma hasSum_doubleCoeff (hG : IsSmoothBiperiodic G) : HasSum (fun q : ℤ × ℤ ↦
    doubleCoeff G q.1 q.2 * cexp (2 * π * I * (q.1 * x + q.2 * y))) (G (x, y)) := by
  have hT : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hGc : Continuous G := hG.contDiff.continuous
  have ha (n : ℤ) : Continuous (sndCoeff G n) := by
    have h : Continuous fun p : ℝ × ℝ ↦ cexp (-(2 * π * I * n * p.2)) * G (p.1, p.2) := by
      fun_prop
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h 0 1
  have hap (n : ℤ) : Periodic (sndCoeff G n) 1 := fun s ↦
    intervalIntegral.integral_congr fun t _ ↦ by
      rw [hG.apply_add_one_fst]
  have hc (m n : ℤ) :
      fourierCoeffOn (lt_add_of_pos_right 0 one_pos) (sndCoeff G n) m = doubleCoeff G m n := by
    rw [fourierCoeffOn_zero_one_eq, doubleCoeff_eq_snd]
  have hS : Summable fun q : ℤ × ℤ ↦ doubleCoeff G q.2 q.1 :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mpr (summable_doubleCoeff hG)
  have h₃ (n : ℤ) :
      HasSum (fun m : ℤ ↦ doubleCoeff G m n * cexp (2 * π * I * m * x)) (sndCoeff G n x) := by
    have hs : Summable (fourierCoeffOn (lt_add_of_pos_right 0 one_pos) (sndCoeff G n)) := by
      rw [funext fun m ↦ hc m n]
      exact hS.prod_factor n
    simpa only [hc, fourier_coe_apply, smul_eq_mul, ofReal_one, div_one] using
      hasSum_fourierCoeffOn_of_summable x (ha n) (hap n) hs
  have h₄ : HasSum (fun n : ℤ ↦ sndCoeff G n x * cexp (2 * π * I * n * y)) (G (x, y)) := by
    simpa only [fourierCoeffOn_zero_one_eq, fourier_coe_apply, smul_eq_mul, ofReal_one, div_one,
      sndCoeff] using hasSum_fourierCoeffOn_of_periodic
        (hasDerivAt_snd_of_differentiable x · hG.differentiable)
        (hasDerivAt_snd_of_differentiable x · (hG.fderiv (0, 1)).differentiable)
        (((hG.fderiv (0, 1)).fderiv (0, 1)).contDiff.continuous.comp (by fun_prop))
        (hG.periodic_snd x) y
  have hf :
      Summable fun q : ℤ × ℤ ↦ doubleCoeff G q.1 q.2 * cexp (2 * π * I * (q.1 * x + q.2 * y)) :=
    (summable_doubleCoeff hG).norm.of_norm_bounded fun q ↦ by
      rw [norm_mul, norm_exp]
      simp
  have h₅ : HasSum (fun n : ℤ ↦ sndCoeff G n x * cexp (2 * π * I * n * y))
      (∑' q : ℤ × ℤ, doubleCoeff G q.1 q.2 * cexp (2 * π * I * (q.1 * x + q.2 * y))) :=
    ((Equiv.prodComm ℤ ℤ).hasSum_iff.mpr hf.hasSum).prod_fiberwise fun n ↦ by
      convert (h₃ n).mul_right (cexp (2 * π * I * n * y)) using 1
      funext m
      simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      rw [mul_assoc (doubleCoeff G m n), ← Complex.exp_add]
      congr 2
      ring1
  rw [h₄.unique h₅]
  exact hf.hasSum

/-- **Fourier inversion on the two-dimensional torus `ℝ² / ℤ²`**: a smooth function
`G : ℝ × ℝ → ℂ` of period `1` in each variable is the sum of its Fourier series,
`G(x, y) = ∑_{(m, n) ∈ ℤ²} c_{m,n} e^{2πi(mx + ny)}` with
`c_{m,n} = ∫_0^1 ∫_0^1 e^{-2πi(ms + nt)} G(s, t) dt ds`, the series converging absolutely. -/
lemma hasSum_fourierSeries_prod_of_contDiff (hG : ContDiff ℝ ∞ G) (h₁ : ∀ p, G (p + (1, 0)) = G p)
    (h₂ : ∀ p, G (p + (0, 1)) = G p) : HasSum (fun q : ℤ × ℤ ↦ (∫ s in (0 : ℝ)..1,
      ∫ t in (0 : ℝ)..1, cexp (-(2 * π * I * (q.1 * s + q.2 * t))) * G (s, t)) *
        cexp (2 * π * I * (q.1 * x + q.2 * y))) (G (x, y)) :=
  hasSum_doubleCoeff x y ⟨hG, h₁, h₂⟩

private lemma repr_smul_add_smul_zero : B.repr (x • B 0 + y • B 1) 0 = x := by
  rw [map_add, B.repr.map_smul, B.repr.map_smul, B.repr_self, B.repr_self]
  simp

private lemma repr_smul_add_smul_one : B.repr (x • B 0 + y • B 1) 1 = y := by
  rw [map_add, B.repr.map_smul, B.repr.map_smul, B.repr_self, B.repr_self]
  simp

private lemma repr_smul_add_repr_smul : B.repr z 0 • B 0 + B.repr z 1 • B 1 = z := by
  simpa [Fin.sum_univ_two] using B.sum_repr z

private lemma setIntegral_Ico_zero_one_eq : ∫ s in Ico (0 : ℝ) 1, g s = ∫ s in (0 : ℝ)..1, g s := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ico_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]

/-- **The integral over the fundamental parallelogram**: for an `ℝ`-basis `(b₀, b₁)` of `ℂ` and a
continuous `k : ℂ → ℂ`, the integral of `k` over the fundamental parallelogram `P` of the lattice
`ℤ b₀ + ℤ b₁`, divided by `vol(P)`, is `∫_0^1 ∫_0^1 k(s b₀ + t b₁) dt ds` (change of variables
along the linear map `s + ti ↦ s b₀ + t b₁`). -/
lemma inv_mul_setIntegral_fundamentalDomain {k : ℂ → ℂ} (hk : Continuous k) :
    (volume.real (ZSpan.fundamentalDomain B) : ℂ)⁻¹ * ∫ x in ZSpan.fundamentalDomain B, k x =
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, k (s • B 0 + t • B 1) := by
  let L : ℂ →L[ℝ] ℂ := reCLM.smulRight (B 0) + imCLM.smulRight (B 1)
  have hL (z : ℂ) : L z = z.re • B 0 + z.im • B 1 :=
    rfl
  let Q : Set ℂ := measurableEquivRealProd ⁻¹' (Ico 0 1 ×ˢ Ico 0 1)
  have hQ : MeasurableSet Q :=
    measurableEquivRealProd.measurable (measurableSet_Ico.prod measurableSet_Ico)
  have hinj : InjOn L Q := fun z _ w _ h ↦ by
    have h0 : B.repr (L z) 0 = B.repr (L w) 0 :=
      congrArg (B.repr · 0) h
    have h1 : B.repr (L z) 1 = B.repr (L w) 1 :=
      congrArg (B.repr · 1) h
    rw [hL, hL, repr_smul_add_smul_zero, repr_smul_add_smul_zero] at h0
    rw [hL, hL, repr_smul_add_smul_one, repr_smul_add_smul_one] at h1
    exact Complex.ext h0 h1
  have himage : L '' Q = ZSpan.fundamentalDomain B := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [ZSpan.mem_fundamentalDomain, Fin.forall_fin_two, hL, repr_smul_add_smul_zero,
        repr_smul_add_smul_one]
      exact hz
    · intro hx
      refine ⟨⟨B.repr x 0, B.repr x 1⟩, ⟨hx 0, hx 1⟩, ?_⟩
      rw [hL]
      exact repr_smul_add_repr_smul B x
  have hJ : ∫ x in L '' Q, k x = ∫ x in Q, |L.det| • k (L x) :=
    integral_image_eq_integral_abs_det_fderiv_smul volume hQ
      (fun z _ ↦ L.hasFDerivAt.hasFDerivWithinAt) hinj k
  have hvol : volume (L '' Q) = ENNReal.ofReal |LinearMap.det (L : ℂ →ₗ[ℝ] ℂ)| * volume Q :=
    Measure.addHaar_image_linearMap volume (L : ℂ →ₗ[ℝ] ℂ) Q
  have hQ1 : volume Q = 1 := by
    rw [volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet, Measure.volume_eq_prod,
      Measure.prod_prod, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, one_mul]
  have hint (f : ℂ → ℂ) (hf : Continuous f) :
      ∫ z in Q, f z = ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, f ⟨s, t⟩ := by
    have h : ∫ z in Q, f (measurableEquivRealProd.symm (measurableEquivRealProd z)) =
        ∫ p in Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1, f (measurableEquivRealProd.symm p) :=
      volume_preserving_equiv_real_prod.setIntegral_preimage_emb
        measurableEquivRealProd.measurableEmbedding (fun p ↦ f (measurableEquivRealProd.symm p)) _
    simp only [MeasurableEquiv.symm_apply_apply] at h
    rw [h, Measure.volume_eq_prod, setIntegral_prod, setIntegral_Ico_zero_one_eq]
    · refine intervalIntegral.integral_congr fun s _ ↦ ?_
      rw [setIntegral_Ico_zero_one_eq]
      rfl
    · exact ((hf.comp equivRealProdCLM.symm.continuous).continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)).mono_set
          (prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)
  have hdet : volume.real (ZSpan.fundamentalDomain B) = |LinearMap.det (L : ℂ →ₗ[ℝ] ℂ)| := by
    rw [measureReal_def, ← himage, hvol, hQ1, mul_one, ENNReal.toReal_ofReal (abs_nonneg _)]
  have hne : ((|LinearMap.det (L : ℂ →ₗ[ℝ] ℂ)| : ℝ) : ℂ) ≠ 0 := by
    have h : volume (ZSpan.fundamentalDomain B) ≠ 0 :=
      ZSpan.measure_fundamentalDomain_ne_zero B
    rw [← himage, hvol, hQ1, mul_one, Ne, ENNReal.ofReal_eq_zero, not_le] at h
    exact_mod_cast h.ne'
  rw [hdet, ← himage, hJ, integral_smul, real_smul, inv_mul_cancel_left₀ hne]
  exact hint _ (hk.comp L.continuous)

variable (m n) in
/-- The frequency `ν ∈ ℂ` dual to `(m, n) ∈ ℤ²` for the basis `(b₀, b₁)`:
`ν x + conj(ν x) = m s + n t` for `x = s b₀ + t b₁`. -/
private noncomputable def dualFrequency : ℂ :=
  ((m * B.repr 1 0 + n * B.repr 1 1 : ℝ) - (m * B.repr I 0 + n * B.repr I 1 : ℝ) * I) / 2

variable (m n) in
private lemma dualFrequency_mul_add_conj : dualFrequency B m n * z +
    conj (dualFrequency B m n * z) = (m * B.repr z 0 + n * B.repr z 1 : ℝ) := by
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    apply Complex.ext <;> simp
  have hr (i : Fin 2) : B.repr z i = z.re * B.repr 1 i + z.im * B.repr I i := by
    conv_lhs => rw [hz]
    rw [map_add, B.repr.map_smul, B.repr.map_smul]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [add_conj, hr 0, hr 1]
  congr 1
  simp only [dualFrequency, ofReal_add, ofReal_mul, ofReal_intCast, mul_re, div_ofNat_re, sub_re,
    add_re, intCast_re, ofReal_re, intCast_im, ofReal_im, I_re, add_im, mul_im, I_im, div_ofNat_im,
    sub_im]
  ring1

private lemma eq_of_mul_add_conj (h : ∀ i, ν * B i + conj (ν * B i) = ν' * B i + conj (ν' * B i)) :
    ν = ν' := by
  have key (z : ℂ) : ν * z + conj (ν * z) = ν' * z + conj (ν' * z) := by
    rw [← repr_smul_add_repr_smul B z]
    have h0 : ν * B 0 + conj (ν * B 0) = ν' * B 0 + conj (ν' * B 0) := h 0
    have h1 : ν * B 1 + conj (ν * B 1) = ν' * B 1 + conj (ν' * B 1) := h 1
    simp only [real_smul, map_add, map_mul, conj_ofReal] at h0 h1 ⊢
    linear_combination (B.repr z 0 : ℂ) * h0 + (B.repr z 1 : ℂ) * h1
  have h1 : ν * 1 + conj (ν * 1) = ν' * 1 + conj (ν' * 1) := key 1
  have hI : ν * I + conj (ν * I) = ν' * I + conj (ν' * I) := key I
  simp only [add_conj, mul_one, ofReal_inj, mul_re, I_re, I_im] at h1 hI
  apply Complex.ext <;> linarith

variable (m n) in
private lemma dualFrequency_mem {l : ℂ} (hl : l ∈ Submodule.span ℤ (range B)) :
    cexp (2 * π * I * (dualFrequency B m n * l + conj (dualFrequency B m n * l))) = 1 := by
  rcases (B.mem_span_iff_repr_mem ℤ l).mp hl 0 with ⟨k₀, hk₀⟩
  rcases (B.mem_span_iff_repr_mem ℤ l).mp hl 1 with ⟨k₁, hk₁⟩
  rw [dualFrequency_mul_add_conj, ← hk₀, ← hk₁]
  simp only [algebraMap_int_eq, Int.coe_castRingHom]
  rw [mul_comm]
  exact_mod_cast exp_int_mul_two_pi_mul_I (m * k₀ + n * k₁)

variable (m n) in
private lemma dualFrequency_mul_add_conj_zero :
    dualFrequency B m n * B 0 + conj (dualFrequency B m n * B 0) = m := by
  rw [dualFrequency_mul_add_conj, B.repr_self]
  simp

variable (m n) in
private lemma dualFrequency_mul_add_conj_one :
    dualFrequency B m n * B 1 + conj (dualFrequency B m n * B 1) = n := by
  rw [dualFrequency_mul_add_conj, B.repr_self]
  simp

private lemma exists_intCast_of_forall_cexp_eq_one
    (hν : ∀ l ∈ Submodule.span ℤ (range B), cexp (2 * π * I * (ν * l + conj (ν * l))) = 1)
    (i : Fin 2) : ∃ k : ℤ, ν * B i + conj (ν * B i) = k := by
  rcases exp_eq_one_iff.mp (hν (B i) (Submodule.subset_span ⟨i, rfl⟩)) with ⟨k, hk⟩
  refine ⟨k, mul_left_cancel₀ two_pi_I_ne_zero ?_⟩
  rw [hk]
  ring1

/-- The bijection `(m, n) ↦ ν` from `ℤ²` onto the frequencies `ν ∈ ℂ` with `ψ(νl) = 1` on the
lattice spanned by `(b₀, b₁)`. -/
private noncomputable def dualFrequencyEquiv : ℤ × ℤ ≃ {ν : ℂ // ∀ l ∈ Submodule.span ℤ (range B),
    cexp (2 * π * I * (ν * l + conj (ν * l))) = 1} :=
  Equiv.ofBijective (fun q ↦ ⟨dualFrequency B q.1 q.2, fun _ ↦ dualFrequency_mem B q.1 q.2⟩)
    ⟨fun q q' h ↦ by
      have h' : dualFrequency B q.1 q.2 = dualFrequency B q'.1 q'.2 :=
        congrArg Subtype.val h
      have h0 : dualFrequency B q.1 q.2 * B 0 + conj (dualFrequency B q.1 q.2 * B 0) = q.1 :=
        dualFrequency_mul_add_conj_zero B q.1 q.2
      have h1 : dualFrequency B q.1 q.2 * B 1 + conj (dualFrequency B q.1 q.2 * B 1) = q.2 :=
        dualFrequency_mul_add_conj_one B q.1 q.2
      rw [h', dualFrequency_mul_add_conj_zero] at h0
      rw [h', dualFrequency_mul_add_conj_one] at h1
      exact Prod.ext (by exact_mod_cast h0.symm) (by exact_mod_cast h1.symm), fun ν ↦ by
      rcases exists_intCast_of_forall_cexp_eq_one B ν.2 0 with ⟨k₀, hk₀⟩
      rcases exists_intCast_of_forall_cexp_eq_one B ν.2 1 with ⟨k₁, hk₁⟩
      refine ⟨(k₀, k₁), Subtype.ext (eq_of_mul_add_conj B fun i ↦ ?_)⟩
      fin_cases i
      · exact (dualFrequency_mul_add_conj_zero B k₀ k₁).trans hk₀.symm
      · exact (dualFrequency_mul_add_conj_one B k₀ k₁).trans hk₁.symm⟩

private lemma dualFrequencyEquiv_apply (q : ℤ × ℤ) :
    (dualFrequencyEquiv B q : ℂ) = dualFrequency B q.1 q.2 :=
  rfl

private lemma hasSum_fourierSeries_finTwo (hf : ContDiff ℝ ∞ f)
    (hper : ∀ l ∈ Submodule.span ℤ (range B), ∀ w, f (l + w) = f w) :
    HasSum (fun ν : {ν : ℂ // ∀ l ∈ Submodule.span ℤ (range B),
      cexp (2 * π * I * (ν * l + conj (ν * l))) = 1} ↦
        cexp (2 * π * I * (ν.1 * z + conj (ν.1 * z))) *
          ((volume.real (ZSpan.fundamentalDomain B) : ℂ)⁻¹ * ∫ t in ZSpan.fundamentalDomain B,
            cexp (-(2 * π * I * (ν.1 * t + conj (ν.1 * t)))) * f t)) (f z) := by
  let G : ℝ × ℝ → ℂ := fun p ↦ f (p.1 • B 0 + p.2 • B 1)
  have hG : IsSmoothBiperiodic G := by
    refine ⟨hf.comp (by fun_prop), fun p ↦ ?_, fun p ↦ ?_⟩
    · have e : (p + (1, 0)).1 • B 0 + (p + (1, 0)).2 • B 1 = B 0 + (p.1 • B 0 + p.2 • B 1) := by
        simp only [Prod.fst_add, Prod.snd_add, add_zero, add_smul, one_smul]
        abel
      simp only [G, e]
      exact hper _ (Submodule.subset_span ⟨0, rfl⟩) _
    · have e : (p + (0, 1)).1 • B 0 + (p + (0, 1)).2 • B 1 = B 1 + (p.1 • B 0 + p.2 • B 1) := by
        simp only [Prod.fst_add, Prod.snd_add, add_zero, add_smul, one_smul]
        abel
      simp only [G, e]
      exact hper _ (Submodule.subset_span ⟨1, rfl⟩) _
  have hz : G (B.repr z 0, B.repr z 1) = f z := by
    simp only [G, repr_smul_add_repr_smul]
  have hsum : HasSum (fun q : ℤ × ℤ ↦ doubleCoeff G q.1 q.2 *
      cexp (2 * π * I * (q.1 * B.repr z 0 + q.2 * B.repr z 1))) (f z) :=
    hz ▸ hasSum_doubleCoeff (B.repr z 0) (B.repr z 1) hG
  have hc : Continuous f := hf.continuous
  refine (dualFrequencyEquiv B).hasSum_iff.mp (hsum.congr_fun fun q ↦ ?_)
  simp only [Function.comp_apply, dualFrequencyEquiv_apply]
  rw [dualFrequency_mul_add_conj, inv_mul_setIntegral_fundamentalDomain B (by fun_prop), mul_comm]
  congr 1
  · refine intervalIntegral.integral_congr fun s _ ↦ intervalIntegral.integral_congr fun t _ ↦ ?_
    simp only [dualFrequency_mul_add_conj, repr_smul_add_smul_zero, repr_smul_add_smul_one]
    norm_cast
  · norm_cast

/-- **Fourier inversion on a two-dimensional torus `ℂ / Λ`**: let `Λ` be the lattice of `ℂ` spanned
over `ℤ` by an `ℝ`-basis `b` of `ℂ` and `P` its fundamental parallelogram. A smooth `Λ`-periodic
function `f : ℂ → ℂ` is the sum of its Fourier series
`f(z) = ∑_ν ψ(νz) vol(P)⁻¹ ∫_P ψ(-νt) f(t) dt`, `ψ(w) = e^{2πi(w + w̄)}`, over the frequencies
`ν ∈ ℂ` with `ψ(νl) = 1` for all `l ∈ Λ` (the characters of `ℂ / Λ`), the series converging
absolutely. -/
lemma hasSum_fourierSeries_zlattice_of_contDiff {ι : Type*} [Fintype ι] (b : Basis ι ℝ ℂ)
    (hf : ContDiff ℝ ∞ f) (hper : ∀ l ∈ Submodule.span ℤ (range b), ∀ w, f (l + w) = f w) :
    HasSum (fun ν : {ν : ℂ // ∀ l ∈ Submodule.span ℤ (range b),
      cexp (2 * π * I * (ν * l + conj (ν * l))) = 1} ↦
        cexp (2 * π * I * (ν.1 * z + conj (ν.1 * z))) *
          ((volume.real (ZSpan.fundamentalDomain b) : ℂ)⁻¹ * ∫ t in ZSpan.fundamentalDomain b,
            cexp (-(2 * π * I * (ν.1 * t + conj (ν.1 * t)))) * f t)) (f z) := by
  let e : ι ≃ Fin 2 :=
    Fintype.equivFinOfCardEq (by rw [← finrank_eq_card_basis b, Complex.finrank_real_complex])
  rw [← b.range_reindex e, ← ZSpan.fundamentalDomain_reindex b e]
  exact hasSum_fourierSeries_finTwo (b.reindex e) z hf (by rwa [Basis.range_reindex])
