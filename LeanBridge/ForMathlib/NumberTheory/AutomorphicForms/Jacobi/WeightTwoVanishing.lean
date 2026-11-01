import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Jacobi.WeightTwo
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The vanishing of Jacobi forms of weight 2 and index 1

For a Jacobi form `φ ∈ J_{k,1}` with Fourier coefficients `c(n, r)` the second derivative
`g(τ) = ∂²φ/∂z²(τ, 0)` is the `q`-series `∑_{n, r} c(n, r) (2πir)² qⁿ`: the Fourier expansion of
`φ` converges absolutely at every point of `ℍ × ℂ`, which bounds it uniformly on the strips
`|Im z| ≤ δ`, so that it can be differentiated termwise in `z`. Differentiating the transformation
law `φ(γτ, z/(cτ + d)) = (cτ + d)^k e^{2πicz²/(cτ + d)} φ(τ, z)` twice at `z = 0` gives
`(cτ + d)^{-2} g(γτ) = (cτ + d)^k (g(τ) + 4πic/(cτ + d) φ(τ, 0))`, so that `g` is a modular form of
weight `k + 2` on `SL(2, ℤ)` as soon as `φ(τ, 0) = 0`; it vanishes at `∞`, its `q`-series having
no constant term (`c(0, r) = 0` for `r ≠ 0`). For `k = 2`, `φ(τ, 0)` is a modular form of weight
`2`, hence `0`, so `g` is a cusp form of weight `4`, hence `0`, and `∑_r r² c(n, r) = 0` for every
`n`. With the vanishing of `∑_r c(n, r)` this forces `c = 0`
(`ModularForm.jacobiCoeff_eq_zero_of_tsum_eq_zero`): `J_{2,1} = 0` (Eichler and Zagier,
Theorem 3.5).

## Main definitions

* `ModularForm.jacobiSecondDeriv`: the second derivative `∂²φ/∂z²(τ, 0)`.
* `ModularForm.jacobiSecondDerivCuspForm`: the cusp form `τ ↦ ∂²φ/∂z²(τ, 0)` of weight `k + 2` of
  a Jacobi form `φ ∈ J_{k,1}` with `φ(τ, 0) = 0`.

## Main results

* `ModularForm.hasSum_jacobiSecondDeriv`: `∂²φ/∂z²(τ, 0) = ∑_{n, r} c(n, r) (2πir)² qⁿ`.
* `ModularForm.jacobiSecondDeriv_smul`: the transformation law of weight `k + 2` of
  `∂²φ/∂z²(τ, 0)` when `φ(τ, 0) = 0`.
* `ModularForm.tsum_sq_mul_jacobiCoeff_eq_zero_of_apply_zero`: `∑_r r² c(n, r) = 0` for
  `φ ∈ J_{k,1}`, `k < 10`, with `φ(τ, 0) = 0`.
* `ModularForm.tsum_sq_mul_jacobiCoeff_eq_zero`: `∑_r r² c(n, r) = 0` for `φ ∈ J_{2,1}`.
* `ModularForm.eq_zero_of_mem_jacobiFormSpace_two`: `J_{2,1} = 0`.
-/

open Complex Filter Real Topology

open UpperHalfPlane hiding I

open scoped Manifold MatrixGroups

namespace ModularForm

variable {k : ℤ} {N : ℕ} {φ : ℍ × ℂ → ℂ} {c : ℤ × ℤ → ℂ} {f : ℂ → ℂ} (p : ℤ × ℤ) (τ : ℍ)
    (γ : SL(2, ℤ)) (n : ℤ) {w : ℂ}

private lemma norm_jacobiFourierExp_eq (x : ℍ × ℂ) :
    ‖jacobiFourierExp p x‖ = rexp (-(2 * π * (p.1 * x.1.im + p.2 * x.2.im))) := by
  rw [jacobiFourierExp, Complex.norm_exp]
  congr 1
  simp

private lemma norm_jacobiFourierExp_le_add {δ : ℝ} (hw : |w.im| ≤ δ) : ‖jacobiFourierExp p (τ, w)‖ ≤
    ‖jacobiFourierExp p (τ, δ * I)‖ + ‖jacobiFourierExp p (τ, -δ * I)‖ := by
  norm_num [norm_jacobiFourierExp_eq]
  rcases le_total 0 (p.2 : ℝ) with h | h
  · refine (Real.exp_le_exp.mpr ?_).trans (le_add_of_nonneg_left (Real.exp_pos _).le)
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le h) (by linarith [abs_le.mp hw] : 0 ≤ w.im + δ)]
  · refine (Real.exp_le_exp.mpr ?_).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (neg_nonneg.mpr h))
      (by linarith [abs_le.mp hw] : 0 ≤ δ - w.im)]

lemma hasSum_deriv_of_hasSum_jacobiFourierExp
    (hf : ∀ w, HasSum (fun p ↦ c p * jacobiFourierExp p (τ, w)) (f w)) (z : ℂ) :
    HasSum (fun p ↦ c p * (2 * π * I * p.2) * jacobiFourierExp p (τ, z)) (deriv f z) := by
  have hd (p : ℤ × ℤ) (w : ℂ) : HasDerivAt (fun w ↦ c p * jacobiFourierExp p (τ, w))
      (c p * (2 * π * I * p.2) * jacobiFourierExp p (τ, w)) w := by
    refine (((((hasDerivAt_id w).const_mul (p.2 : ℂ)).const_add ((p.1 : ℂ) * τ)).const_mul
      (2 * π * I)).cexp.const_mul (c p)).congr_deriv ?_
    simp only [jacobiFourierExp, id]
    ring1
  have hU (p : ℤ × ℤ) (w : ℂ) (hw : w ∈ Metric.ball z 1) : ‖c p * jacobiFourierExp p (τ, w)‖ ≤
      ‖c p * jacobiFourierExp p (τ, (|z.im| + 1 : ℝ) * I)‖ +
        ‖c p * jacobiFourierExp p (τ, -(|z.im| + 1 : ℝ) * I)‖ := by
    rw [norm_mul, norm_mul, norm_mul, ← mul_add]
    refine mul_le_mul_of_nonneg_left (norm_jacobiFourierExp_le_add p τ ?_) (norm_nonneg _)
    rw [mem_ball_iff_norm] at hw
    linarith [abs_sub_abs_le_abs_sub w.im z.im, sub_im w z ▸ abs_im_le_norm (w - z)]
  have hs : Summable fun p ↦ ‖c p * jacobiFourierExp p (τ, (|z.im| + 1 : ℝ) * I)‖ +
      ‖c p * jacobiFourierExp p (τ, -(|z.im| + 1 : ℝ) * I)‖ :=
    (summable_norm_iff.mpr (hf _).summable).add (summable_norm_iff.mpr (hf _).summable)
  have h : HasSum (fun p ↦ deriv (fun w ↦ c p * jacobiFourierExp p (τ, w)) z)
      (deriv (fun w ↦ ∑' p, c p * jacobiFourierExp p (τ, w)) z) :=
    hasSum_deriv_of_summable_norm hs (fun p w _ ↦ (hd p w).differentiableAt.differentiableWithinAt)
      Metric.isOpen_ball hU (Metric.mem_ball_self one_pos)
  rw [funext fun w ↦ (hf w).tsum_eq] at h
  exact h.congr_fun fun p ↦ (hd p z).deriv.symm

variable (φ) in
/-- The **second derivative** `∂²φ/∂z²(τ, 0)` in `z` at `z = 0` of `φ : ℍ × ℂ → ℂ`, a function of
`τ`. For a Jacobi form `φ ∈ J_{k,1}` with `φ(τ, 0) = 0` it is a cusp form of weight `k + 2` on
`SL(2, ℤ)` (`ModularForm.jacobiSecondDerivCuspForm`). -/
noncomputable def jacobiSecondDeriv : ℂ :=
  deriv (deriv fun z ↦ φ (τ, z)) 0

/-- **The second derivative of a Jacobi form at `z = 0` as a `q`-series**: for `φ ∈ J_{k,N}` with
Fourier coefficients `c(n, r)`, `∂²φ/∂z²(τ, 0) = ∑_{n, r} c(n, r) (2πir)² e^{2πinτ}`, the Fourier
expansion being differentiated termwise. -/
lemma hasSum_jacobiSecondDeriv (hφ : φ ∈ jacobiFormSpace k N) : HasSum (fun p ↦
    jacobiCoeff φ p * (2 * π * I * p.2) * (2 * π * I * p.2) * jacobiFourierExp p (τ, 0))
      (jacobiSecondDeriv φ τ) :=
  hasSum_deriv_of_hasSum_jacobiFourierExp τ (hasSum_deriv_of_hasSum_jacobiFourierExp τ
    (fun w ↦ hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ (τ, w))) 0

private lemma differentiable_apply_mk (hφ : φ ∈ jacobiFormSpace k N) :
    Differentiable ℂ fun z ↦ φ (τ, z) :=
  mdifferentiable_iff_differentiable.mp <| hφ.1.comp <|
    mdifferentiable_const.prodMk mdifferentiable_id

/-- **The transformation law of `∂²φ/∂z²(τ, 0)`**: for a Jacobi form `φ ∈ J_{k,1}` with
`φ(τ, 0) = 0` for every `τ`, `g(τ) = ∂²φ/∂z²(τ, 0)` satisfies `g(γτ) = (cτ + d)^{k+2} g(τ)` for
every `γ = (a, b; c, d) ∈ SL(2, ℤ)`: differentiate
`φ(γτ, z/(cτ + d)) = (cτ + d)^k e^{2πicz²/(cτ + d)} φ(τ, z)` twice at `z = 0`, where the
derivative of the exponential and `φ(τ, 0)` vanish. -/
lemma jacobiSecondDeriv_smul (hφ : φ ∈ jacobiFormSpace k 1) (h0 : ∀ τ : ℍ, φ (τ, 0) = 0) :
    jacobiSecondDeriv φ (γ • τ) = denom γ τ ^ (k + 2) * jacobiSecondDeriv φ τ := by
  have hD : denom γ τ ≠ 0 := denom_ne_zero γ τ
  let E : ℂ → ℂ := fun z ↦ denom γ τ ^ k * cexp (2 * π * I * (1 : ℕ) * γ 1 0 * z ^ 2 / denom γ τ)
  have hlaw : (fun z ↦ φ (γ • τ, (denom γ τ)⁻¹ * z)) = fun z ↦ E z * φ (τ, z) := funext fun z ↦ by
    rw [inv_mul_eq_div]
    exact hφ.2.1 γ (τ, z)
  have hE : Differentiable ℂ E := by
    fun_prop
  have hE0 : HasDerivAt E 0 0 :=
    ((((hasDerivAt_pow 2 (0 : ℂ)).const_mul (2 * π * I * (1 : ℕ) * γ 1 0)).div_const
      (denom γ τ)).cexp.const_mul (denom γ τ ^ k)).congr_deriv (by simp)
  have h1 : deriv (deriv fun z ↦ φ (γ • τ, (denom γ τ)⁻¹ * z)) 0 =
      (denom γ τ)⁻¹ * ((denom γ τ)⁻¹ * jacobiSecondDeriv φ (γ • τ)) := by
    have hd : deriv (fun z ↦ φ (γ • τ, (denom γ τ)⁻¹ * z)) =
        fun z ↦ (denom γ τ)⁻¹ * deriv (fun z ↦ φ (γ • τ, z)) ((denom γ τ)⁻¹ * z) :=
      funext fun z ↦ deriv_comp_mul_left (denom γ τ)⁻¹ (fun z ↦ φ (γ • τ, z)) z
    rw [hd, deriv_const_mul_field']
    beta_reduce
    rw [deriv_comp_mul_left, mul_zero, smul_eq_mul]
    rfl
  have h2 : deriv (deriv fun z ↦ E z * φ (τ, z)) 0 = denom γ τ ^ k * jacobiSecondDeriv φ τ := by
    have hh : Differentiable ℂ fun z ↦ φ (τ, z) := differentiable_apply_mk τ hφ
    have hd : deriv (fun z ↦ E z * φ (τ, z)) =
        fun z ↦ deriv E z * φ (τ, z) + E z * deriv (fun z ↦ φ (τ, z)) z :=
      funext fun z ↦ deriv_fun_mul (hE z) (hh z)
    have ha : DifferentiableAt ℂ (fun z ↦ deriv E z * φ (τ, z)) 0 := (hE.deriv 0).mul (hh 0)
    have hb : DifferentiableAt ℂ (fun z ↦ E z * deriv (fun z ↦ φ (τ, z)) z) 0 :=
      (hE 0).mul (hh.deriv 0)
    rw [hd, deriv_fun_add ha hb, deriv_fun_mul (hE.deriv 0) (hh 0),
      deriv_fun_mul (hE 0) (hh.deriv 0), hE0.deriv, h0 τ]
    simp [E, jacobiSecondDeriv]
  rw [hlaw, h2] at h1
  rw [zpow_add₀ hD]
  field_simp at h1 ⊢
  exact h1.symm

variable {p} in
private lemma nonneg_of_jacobiCoeff_ne_zero (hφ : φ ∈ jacobiFormSpace k N)
    (hp : jacobiCoeff φ p ≠ 0) : 0 ≤ p.1 :=
  not_not.mp fun h ↦ hp <| jacobiCoeff_eq_zero_of_mem_jacobiFourierSupported hφ.2.2 fun h' ↦ h h'.1

variable {p} in
private lemma sq_le_of_jacobiCoeff_ne_zero (hφ : φ ∈ jacobiFormSpace k N)
    (hp : jacobiCoeff φ p ≠ 0) : p.2 ^ 2 ≤ 4 * p.1 * N :=
  not_not.mp fun h ↦ hp <| jacobiCoeff_eq_zero_of_mem_jacobiFourierSupported hφ.2.2 fun h' ↦ h h'.2

private lemma norm_cexp_mul_le {y : ℝ} (hp : 0 ≤ p.1) (hw : y ≤ w.im) :
    ‖cexp (2 * π * I * (p.1 * w))‖ ≤ rexp (-(2 * π * (p.1 * y))) := by
  have h : (2 * π * I * (p.1 * w)).re = -(2 * π * (p.1 * w.im)) := by
    simp
  rw [Complex.norm_exp, h]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (Int.cast_nonneg hp)) (sub_nonneg.mpr hw)]

lemma mdifferentiable_jacobiSecondDeriv (hφ : φ ∈ jacobiFormSpace k N) :
    MDiff (jacobiSecondDeriv φ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  let τ₀ : ℍ := ⟨(z.im / 2 : ℝ) * I, by simpa using half_pos hz.out⟩
  have hs : Summable fun p : ℤ × ℤ ↦ ‖jacobiCoeff φ p * (2 * π * I * p.2) * (2 * π * I * p.2) *
      jacobiFourierExp p (τ₀, 0)‖ :=
    summable_norm_iff.mpr (hasSum_jacobiSecondDeriv τ₀ hφ).summable
  have hU : IsOpen {w : ℂ | z.im / 2 < w.im} := isOpen_lt continuous_const continuous_im
  have hd : DifferentiableOn ℂ (fun w ↦ ∑' p : ℤ × ℤ, jacobiCoeff φ p * (2 * π * I * p.2) *
      (2 * π * I * p.2) * cexp (2 * π * I * (p.1 * w))) {w : ℂ | z.im / 2 < w.im} := by
    refine differentiableOn_tsum_of_summable_norm hs (fun p ↦ by fun_prop) hU fun p w hw ↦ ?_
    by_cases hc : jacobiCoeff φ p = 0
    · simp [hc]
    rw [norm_mul (jacobiCoeff φ p * _ * _), norm_mul (jacobiCoeff φ p * _ * _),
      norm_jacobiFourierExp_eq]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_cexp_mul_le p (nonneg_of_jacobiCoeff_ne_zero hφ hc) hw.le).trans_eq ?_
    simp [τ₀]
  have heq : Set.EqOn (jacobiSecondDeriv φ ∘ ofComplex) (fun w ↦ ∑' p : ℤ × ℤ, jacobiCoeff φ p *
      (2 * π * I * p.2) * (2 * π * I * p.2) * cexp (2 * π * I * (p.1 * w)))
      {w : ℂ | z.im / 2 < w.im} := fun w hw ↦ by
    have hw' : 0 < w.im := (half_pos hz.out).trans hw
    rw [Function.comp_apply, ofComplex_apply_of_im_pos hw',
      ← (hasSum_jacobiSecondDeriv _ hφ).tsum_eq]
    simp [jacobiFourierExp]
  exact ((hd.congr heq).differentiableAt (hU.mem_nhds (half_lt_self hz.out))).differentiableWithinAt

lemma isZeroAtImInfty_jacobiSecondDeriv (hφ : φ ∈ jacobiFormSpace k N) :
    IsZeroAtImInfty (jacobiSecondDeriv φ) := by
  have hs : Summable fun p : ℤ × ℤ ↦ ‖jacobiCoeff φ p * (2 * π * I * p.2) * (2 * π * I * p.2) *
      jacobiFourierExp p (UpperHalfPlane.I, 0)‖ :=
    summable_norm_iff.mpr (hasSum_jacobiSecondDeriv UpperHalfPlane.I hφ).summable
  have hab (p : ℤ × ℤ) : Tendsto (fun τ : ℍ ↦ jacobiCoeff φ p * (2 * π * I * p.2) *
      (2 * π * I * p.2) * jacobiFourierExp p (τ, 0)) atImInfty (𝓝 0) := by
    by_cases hc : jacobiCoeff φ p * (2 * π * I * p.2) * (2 * π * I * p.2) = 0
    · simp [hc]
    have hc0 : jacobiCoeff φ p ≠ 0 := fun h ↦ hc <| by simp [h]
    have hp2 : p.2 ≠ 0 := fun h ↦ hc <| by simp [h]
    have hp : p.2 ^ 2 ≤ 4 * p.1 * N := sq_le_of_jacobiCoeff_ne_zero hφ hc0
    have hp1 : (0 : ℝ) < p.1 := Int.cast_pos.mpr <| by
      nlinarith [nonneg_of_jacobiCoeff_ne_zero hφ hc0, sq_pos_iff.mpr hp2]
    have ht : Tendsto (fun τ : ℍ ↦ jacobiFourierExp p (τ, 0)) atImInfty (𝓝 0) := by
      refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
      simp only [norm_jacobiFourierExp_eq, zero_im, mul_zero, add_zero]
      refine Real.tendsto_exp_atBot.comp <| tendsto_neg_atTop_atBot.comp ?_
      exact (tendsto_comap.const_mul_atTop hp1).const_mul_atTop two_pi_pos
    simpa using ht.const_mul (jacobiCoeff φ p * (2 * π * I * p.2) * (2 * π * I * p.2))
  have hb : ∀ᶠ τ : ℍ in atImInfty, ∀ p : ℤ × ℤ, ‖jacobiCoeff φ p * (2 * π * I * p.2) *
      (2 * π * I * p.2) * jacobiFourierExp p (τ, 0)‖ ≤ ‖jacobiCoeff φ p * (2 * π * I * p.2) *
        (2 * π * I * p.2) * jacobiFourierExp p (UpperHalfPlane.I, 0)‖ := by
    refine (atImInfty_mem _).mpr ⟨1, fun τ hτ p ↦ ?_⟩
    by_cases hc : jacobiCoeff φ p = 0
    · simp [hc]
    rw [norm_mul (jacobiCoeff φ p * _ * _), norm_mul (jacobiCoeff φ p * _ * _)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simp only [norm_jacobiFourierExp_eq, UpperHalfPlane.I_im]
    have hp : (0 : ℝ) ≤ p.1 := Int.cast_nonneg <| nonneg_of_jacobiCoeff_ne_zero hφ hc
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hp) (sub_nonneg.mpr hτ)]
  simpa [IsZeroAtImInfty, ZeroAtFilter, fun τ ↦ (hasSum_jacobiSecondDeriv τ hφ).tsum_eq] using
    tendsto_tsum_of_dominated_convergence hs hab hb

private lemma slash_jacobiSecondDeriv (hφ : φ ∈ jacobiFormSpace k 1) (h0 : ∀ τ : ℍ, φ (τ, 0) = 0) :
    jacobiSecondDeriv φ ∣[k + 2] γ = jacobiSecondDeriv φ := by
  ext τ
  rw [SL_slash_apply, jacobiSecondDeriv_smul τ γ hφ h0, zpow_neg, mul_comm, ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ (denom_ne_zero _ τ)), one_mul]

/-- The **cusp form** `τ ↦ ∂²φ/∂z²(τ, 0)` of weight `k + 2` on `SL(2, ℤ)` of a Jacobi form
`φ ∈ J_{k,1}` with `φ(τ, 0) = 0` for every `τ`: it transforms with weight `k + 2`
(`ModularForm.jacobiSecondDeriv_smul`), it is holomorphic, and it vanishes at `∞`, as its
`q`-series `∑_{n, r} c(n, r) (2πir)² qⁿ` has no constant term. -/
noncomputable def jacobiSecondDerivCuspForm (hφ : φ ∈ jacobiFormSpace k 1)
    (h0 : ∀ τ : ℍ, φ (τ, 0) = 0) : CuspForm 𝒮ℒ (k + 2) where
  toFun := jacobiSecondDeriv φ
  slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ slash_jacobiSecondDeriv γ hφ h0
  holo' := mdifferentiable_jacobiSecondDeriv hφ
  zero_at_cusps' hc := (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr fun γ _ ↦
    (slash_jacobiSecondDeriv γ hφ h0).symm ▸ isZeroAtImInfty_jacobiSecondDeriv hφ

lemma tsum_eq_zero_of_hasSum_jacobiFourierExp
    (hc : ∀ τ : ℍ, HasSum (fun p ↦ c p * jacobiFourierExp p (τ, 0)) 0) :
    ∑' r : ℤ, c (n, r) = 0 := by
  have hd : (fun p : ℤ × ℤ ↦ if p.2 = 0 then ∑' r : ℤ, c (p.1, r) else 0) = 0 := by
    refine eq_zero_of_hasSum_jacobiFourierExp fun x ↦ ?_
    have he (p : ℤ × ℤ) : jacobiFourierExp p (x.1, 0) = jacobiFourierExp (p.1, 0) x := by
      simp [jacobiFourierExp]
    have h1 : HasSum (fun m : ℤ ↦ (∑' r : ℤ, c (m, r)) * jacobiFourierExp (m, 0) x) 0 := by
      refine (hc x.1).prod_fiberwise fun m ↦ ?_
      have hs : Summable fun r : ℤ ↦ c (m, r) * jacobiFourierExp (m, 0) x := by
        simpa only [he] using (hc x.1).summable.prod_factor m
      have hs' : Summable fun r : ℤ ↦ c (m, r) :=
        (summable_mul_right_iff (Complex.exp_ne_zero _)).mp hs
      simpa only [he] using hs'.hasSum.mul_right (jacobiFourierExp (m, 0) x)
    refine ((Prod.mk_left_injective (0 : ℤ)).hasSum_iff fun p hp ↦ ?_).mp ?_
    · have h0 : p.2 ≠ 0 := fun h0 ↦ hp ⟨p.1, Prod.ext rfl h0.symm⟩
      simp [h0]
    · simpa [Function.comp_def] using h1
  simpa using congrFun hd (n, 0)

/-- **The `z²`-coefficients of a Jacobi form vanishing at `z = 0`**: if `φ ∈ J_{k,1}`, `k < 10`,
satisfies `φ(τ, 0) = 0` for every `τ`, then `∑_r r² c(n, r) = 0` for every `n`, as
`∂²φ/∂z²(τ, 0) = -4π² ∑_n (∑_r r² c(n, r)) qⁿ` is a cusp form of weight `k + 2 < 12` on
`SL(2, ℤ)`, hence `0`. -/
lemma tsum_sq_mul_jacobiCoeff_eq_zero_of_apply_zero (hφ : φ ∈ jacobiFormSpace k 1)
    (h0 : ∀ τ : ℍ, φ (τ, 0) = 0) (hk : k < 10) :
    ∑' r : ℤ, (r : ℂ) ^ 2 * jacobiCoeff φ (n, r) = 0 := by
  have hF : jacobiSecondDerivCuspForm hφ h0 = 0 :=
    rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by omega)) _
  have hc (τ : ℍ) : HasSum (fun p : ℤ × ℤ ↦
      (2 * π * I) ^ 2 * ((p.2 : ℂ) ^ 2 * jacobiCoeff φ p) * jacobiFourierExp p (τ, 0)) 0 := by
    have hτ : jacobiSecondDeriv φ τ = 0 := congrArg (fun F : CuspForm 𝒮ℒ (k + 2) ↦ F τ) hF
    exact (hτ ▸ hasSum_jacobiSecondDeriv τ hφ).congr_fun fun p ↦ by ring1
  have h : ∑' r : ℤ, (2 * π * I) ^ 2 * ((r : ℂ) ^ 2 * jacobiCoeff φ (n, r)) = 0 :=
    tsum_eq_zero_of_hasSum_jacobiFourierExp n hc
  rw [tsum_mul_left] at h
  exact (mul_eq_zero.mp h).resolve_left (by simp)

/-- **The `z²`-coefficients of a Jacobi form of weight `2` and index `1` vanish**: for
`φ ∈ J_{2,1}`, `∑_r r² c(n, r) = 0` for every `n`, as `φ(τ, 0) = 0` (there are no nonzero modular
forms of weight `2` on `SL(2, ℤ)`) and there are no nonzero cusp forms of weight `4`. -/
lemma tsum_sq_mul_jacobiCoeff_eq_zero (hφ : φ ∈ jacobiFormSpace 2 1) :
    ∑' r : ℤ, (r : ℂ) ^ 2 * jacobiCoeff φ (n, r) = 0 :=
  tsum_sq_mul_jacobiCoeff_eq_zero_of_apply_zero n hφ (apply_zero_of_mem_jacobiFormSpace_two hφ)
    (by norm_num)

/-- **There are no nonzero Jacobi forms of weight `2` and index `1`** (Eichler and Zagier,
Theorem 3.5): `J_{2,1} = 0`. The Taylor coefficients `φ(τ, 0)` and `∂²φ/∂z²(τ, 0)` of
`φ ∈ J_{2,1}` at `z = 0` are a modular form of weight `2` and a cusp form of weight `4` on
`SL(2, ℤ)`, both `0`, and a Jacobi form of index `1` is determined by these two. -/
lemma eq_zero_of_mem_jacobiFormSpace_two (hφ : φ ∈ jacobiFormSpace 2 1) : φ = 0 :=
  eq_zero_of_mem_jacobiFormSpace_two_of_tsum_sq hφ fun n ↦ tsum_sq_mul_jacobiCoeff_eq_zero n hφ

end ModularForm
