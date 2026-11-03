import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Fourier series of periodic `C²` functions

A function `g : ℝ → ℂ` of period `T > 0`, twice differentiable with a continuous second derivative
(then `g'` is also of period `T`), is the sum of its Fourier series
`g(x) = ∑_{n ∈ ℤ} c_n(g) e^{2πinx/T}`, `c_n(g) = (1/T) ∫_0^T g(t) e^{-2πint/T} dt`, which converges
absolutely: integrating by parts twice, `c_n(g) = -(T / 2πn)² c_n(g'')` for `n ≠ 0`, and
`|c_n(g'')|` is bounded. This is the expansion in `x` of a smooth function `f(x + iy)` on the upper
half-plane invariant under `z ↦ z + 1`, the first step towards the Fourier expansion of a Maass form
(LMFDB `mf.maass.mwf.fourierexpansion`, `mf.maass.mwf.coefficients`).

## Main results

* `hasSum_fourierCoeffOn_of_periodic`: the Fourier series of a periodic `C²` function converges to
  it, absolutely (`summable_fourierCoeffOn_of_periodic`).
-/

open Complex Function MeasureTheory Real Set

variable {T M : ℝ} [hT : Fact (0 < T)] {g g' g'' : ℝ → ℂ} {n : ℤ}

variable (n) in
lemma intervalIntegral_exp_two_pi_I_mul :
    ∫ x in (0 : ℝ)..1, cexp (2 * π * I * n * x) = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · simp [hn]
  · have hc : 2 * π * I * n ≠ 0 := by
      simp [hn, Real.pi_ne_zero]
    rw [integral_exp_mul_complex hc]
    have h1 : cexp (2 * π * I * n) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨n, by ring1⟩
    simp [h1]

variable (g n) in
lemma fourierCoeffOn_eq_integral_exp : fourierCoeffOn (lt_add_of_pos_right 0 one_pos) g n =
    ∫ t in (0 : ℝ)..1, cexp (-(2 * π * I * n) * t) * g t := by
  rw [fourierCoeffOn_eq_integral]
  simp only [zero_add, sub_zero, div_one, one_smul]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [fourier_coe_apply]
  congr 2
  push_cast
  ring1

variable (n) in
lemma norm_integral_exp_mul_le (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖g t‖ ≤ M) :
    ‖∫ t in (0 : ℝ)..1, cexp (-(2 * π * I * n) * t) * g t‖ ≤ M := by
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := M) fun t ht ↦ ?_).trans_eq
    (by simp)
  rw [uIoc_of_le zero_le_one] at ht
  rw [norm_mul, norm_exp]
  simpa using hM t (Ioc_subset_Icc_self ht)

lemma fourierCoeffOn_eq_mul_fourierCoeffOn_deriv (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : Continuous g') (hp : Periodic g T) (hn : n ≠ 0) :
    fourierCoeffOn (lt_add_of_pos_right 0 hT.out) g n =
      T / (2 * π * I * n) * fourierCoeffOn (lt_add_of_pos_right 0 hT.out) g' n := by
  rw [fourierCoeffOn_of_hasDerivAt _ hn (fun x _ ↦ hg x) (hg'.intervalIntegrable _ _), hp 0]
  push_cast
  field_simp
  ring1

variable (g'' n) in
lemma norm_fourierCoeffOn_le : ‖fourierCoeffOn (lt_add_of_pos_right 0 hT.out) g'' n‖ ≤
    1 / T * ∫ x in (0 : ℝ)..0 + T, ‖g'' x‖ := by
  have h1 : ‖1 / (0 + T - 0)‖ = 1 / T := by
    rw [zero_add, sub_zero, norm_div, norm_one, Real.norm_of_nonneg hT.out.le]
  rw [fourierCoeffOn_eq_integral, norm_smul, h1]
  refine mul_le_mul_of_nonneg_left ((intervalIntegral.norm_integral_le_integral_norm
    (le_add_of_nonneg_right hT.out.le)).trans_eq <|
      intervalIntegral.integral_congr fun x _ ↦ ?_) (one_div_nonneg.mpr hT.out.le)
  rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]

/-- **The Fourier coefficients of a periodic `C²` function are summable**: for `g` twice
differentiable with a continuous second derivative and of period `T > 0` (then so is `g'`),
`|c_n(g)| ≤ C / n²` for `n ≠ 0`. -/
lemma summable_fourierCoeffOn_of_periodic (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x) (hc : Continuous g'') (hp : Periodic g T) :
    Summable (fourierCoeffOn (lt_add_of_pos_right 0 hT.out) g) := by
  have hp' : Periodic g' T := fun x ↦
    ((hg (x + T)).comp_add_const x T).unique <| (hg x).congr_of_eventuallyEq <| .of_forall hp
  refine Summable.of_norm_bounded_eventually (g := fun n : ℤ ↦ T ^ 2 / (4 * π ^ 2) *
    (1 / T * ∫ x in (0 : ℝ)..0 + T, ‖g'' x‖) * (1 / (n : ℝ) ^ 2))
    ((Real.summable_one_div_int_pow.mpr one_lt_two).mul_left _) ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
  rw [fourierCoeffOn_eq_mul_fourierCoeffOn_deriv hg (continuous_iff_continuousAt.mpr fun x ↦
    (hg' x).continuousAt) hp hn, fourierCoeffOn_eq_mul_fourierCoeffOn_deriv hg' hc hp' hn]
  have hb : ‖fourierCoeffOn (lt_add_of_pos_right 0 hT.out) g'' n‖ ≤
      1 / T * ∫ x in (0 : ℝ)..0 + T, ‖g'' x‖ :=
    norm_fourierCoeffOn_le g'' n
  have hnorm : ‖(T : ℂ) / (2 * π * I * n)‖ = T / (2 * π * |(n : ℝ)|) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_real, norm_real, norm_I, norm_intCast,
      Real.norm_of_nonneg hT.out.le, Real.norm_of_nonneg pi_pos.le, RCLike.norm_ofNat, mul_one]
  have e : T / (2 * π * |(n : ℝ)|) * (T / (2 * π * |(n : ℝ)|) *
      ‖fourierCoeffOn (lt_add_of_pos_right 0 hT.out) g'' n‖) = T ^ 2 / (4 * π ^ 2) *
        ‖fourierCoeffOn (lt_add_of_pos_right 0 hT.out) g'' n‖ * (1 / (n : ℝ) ^ 2) := by
    rw [← sq_abs (n : ℝ)]
    field_simp
    ring1
  rw [norm_mul, norm_mul, hnorm, e]
  gcongr

lemma hasSum_fourierCoeffOn_of_summable (hg : Continuous g) (hp : Periodic g T)
    (hs : Summable (fourierCoeffOn (lt_add_of_pos_right 0 hT.out) g)) (x : ℝ) :
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

/-- **The Fourier series of a periodic `C²` function converges to it**: for `g` twice
differentiable on `ℝ` with a continuous second derivative and of period `T > 0`,
`g(x) = ∑_{n ∈ ℤ} c_n(g) e^{2πinx/T}` with `c_n(g) = (1/T) ∫_0^T g(t) e^{-2πint/T} dt`, the series
converging absolutely (`summable_fourierCoeffOn_of_periodic`). -/
lemma hasSum_fourierCoeffOn_of_periodic (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x) (hc : Continuous g'') (hp : Periodic g T) (x : ℝ) :
    HasSum (fun n : ℤ ↦ fourierCoeffOn (lt_add_of_pos_right 0 hT.out) g n •
      fourier n (x : AddCircle T)) (g x) :=
  hasSum_fourierCoeffOn_of_summable (continuous_iff_continuousAt.mpr fun x ↦ (hg x).continuousAt)
    hp (summable_fourierCoeffOn_of_periodic hg hg' hc hp) x
