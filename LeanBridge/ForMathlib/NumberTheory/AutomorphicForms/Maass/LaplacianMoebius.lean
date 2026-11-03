import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.HeckeSquareIntegrable
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# The hyperbolic Laplacian commutes with the Möbius action

The flat Laplacian `∂²/∂x² + ∂²/∂y²` is conformally invariant: for `g` holomorphic,
`(∂²/∂x² + ∂²/∂y²)(f ∘ g) = |g'|² ((∂²/∂x² + ∂²/∂y²) f) ∘ g`. For a Möbius transformation
`z ↦ (az + b)/(cz + d)` with `ad - bc > 0`, `y² |g'(z)|² = (Im g(z))²`, so that the hyperbolic
Laplacian `y² (∂²/∂x² + ∂²/∂y²)` of `UpperHalfPlane.hyperbolicLaplacian` commutes with `g`: this
extends `UpperHalfPlane.hyperbolicLaplacian_comp_affine` from real affine maps to all of
`GL(2, ℝ)⁺`.

So for `F` in `M(N, χ, λ)` (`UpperHalfPlane.maassSpace`) and `β ∈ GL(2, ℚ)⁺`, the function
`z ↦ F(βz)` is smooth with eigenvalue `λ` and square-integrable on every translate `σ 𝒟ᵒ`,
`σ ∈ SL(2, ℤ)`, of the open standard fundamental domain. Such functions form the complex vector
space `UpperHalfPlane.maassTileSpace`, whose `Γ₀(N)`-invariant elements lie in `M(N, 1, λ)`.

## Main definitions

* `UpperHalfPlane.maassTileSpace`: the smooth eigenfunctions of the Laplacian that are
  square-integrable on every translate of `𝒟ᵒ`.

## Main results

* `UpperHalfPlane.hyperbolicLaplacian_comp_of_analyticAt`: the conformal invariance of the
  hyperbolic Laplacian.
* `UpperHalfPlane.hyperbolicLaplacian_comp_smul`: the hyperbolic Laplacian commutes with
  `GL(2, ℝ)⁺`.
* `UpperHalfPlane.comp_smul_mem_maassTileSpace`: `F(βz)` lies in `maassTileSpace` for `F` in
  `M(N, χ, λ)` and `β ∈ GL(2, ℚ)⁺`.
* `UpperHalfPlane.mem_maassSpace_of_mem_maassTileSpace`: the `Γ₀(N)`-invariant elements of
  `maassTileSpace` lie in `M(N, 1, λ)`.
-/

open MeasureTheory CongruenceSubgroup ModularGroup TauCeti

open scoped ContDiff MatrixGroups Pointwise

namespace UpperHalfPlane

variable {f g : ℂ → ℂ} {z : ℂ} {b : GL (Fin 2) ℝ} {F H : ℍ → ℂ} {eigenvalue : ℂ} {N : ℕ}
  {χ : DirichletCharacter ℂ N} {n : WithTop ℕ∞}

lemma fderiv_fderiv_comp_apply_of_analyticAt (hf : ContDiffAt ℝ 2 f (g z)) (hg : AnalyticAt ℂ g z)
    (v : ℂ) : fderiv ℝ (fun w ↦ fderiv ℝ (f ∘ g) w v) z v =
      fderiv ℝ (fderiv ℝ f) (g z) (deriv g z * v) (deriv g z * v) +
        fderiv ℝ f (g z) (v * v * iteratedDeriv 2 g z) := by
  have hg' : ContDiffAt ℝ 2 g z := hg.contDiffAt.restrict_scalars ℝ
  have hd : fderiv ℝ g z v = deriv g z * v := by
    rw [hg.differentiableAt.fderiv_restrictScalars ℝ, ContinuousLinearMap.coe_restrictScalars',
      fderiv_eq_smul_deriv, smul_eq_mul, mul_comm]
  rw [fderiv_clm_apply_const_apply ((hf.comp z hg').hasFDerivAt_fderiv le_rfl).differentiableAt,
    fderiv_fderiv_comp_apply hf hg', hd, hg.contDiffAt.fderiv_fderiv_restrictScalars_apply,
    fderiv_fderiv_apply_eq_smul_iteratedDeriv, smul_eq_mul]

lemma bilinear_add_bilinear_mul_I (D : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (a : ℂ) : D a a +
    D (a * Complex.I) (a * Complex.I) = (Complex.normSq a : ℂ) *
      (D 1 1 + D Complex.I Complex.I) := by
  have ha : a = a.re • (1 : ℂ) + a.im • Complex.I := by
    simp
  have hI : a * Complex.I = a.re • Complex.I + (-a.im) • (1 : ℂ) := by
    apply Complex.ext <;> simp
  rw [hI, Complex.normSq_apply, ← Complex.real_smul]
  generalize a.re = s at *
  generalize a.im = t at *
  rw [ha]
  simp only [map_add, map_smul, add_apply, smul_apply]
  module

/-- **The hyperbolic Laplacian is conformally invariant**: for `f` twice continuously
differentiable at `g(z)` and `g` holomorphic at `z` with `y² |g'(z)|² = (Im g(z))²`, the hyperbolic
Laplacian of `f ∘ g` at `z` is the one of `f` at `g(z)`. -/
lemma hyperbolicLaplacian_comp_of_analyticAt (hf : ContDiffAt ℝ 2 f (g z)) (hg : AnalyticAt ℂ g z)
    (h : z.im ^ 2 * Complex.normSq (deriv g z) = (g z).im ^ 2) :
    hyperbolicLaplacian (f ∘ g) z = hyperbolicLaplacian f (g z) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) (g z) :=
    (hf.hasFDerivAt_fderiv le_rfl).differentiableAt
  have key : fderiv ℝ (fderiv ℝ f) (g z) (deriv g z) (deriv g z) +
      fderiv ℝ (fderiv ℝ f) (g z) (deriv g z * Complex.I) (deriv g z * Complex.I) =
        (Complex.normSq (deriv g z) : ℂ) * (fderiv ℝ (fderiv ℝ f) (g z) 1 1 +
          fderiv ℝ (fderiv ℝ f) (g z) Complex.I Complex.I) :=
    bilinear_add_bilinear_mul_I _ _
  simp only [hyperbolicLaplacian, fderiv_fderiv_comp_apply_of_analyticAt hf hg,
    fderiv_clm_apply_const_apply hdf, mul_one, Complex.I_mul_I, neg_mul, map_neg, ← h]
  push_cast
  linear_combination (z.im : ℂ) ^ 2 * key

lemma coe_ofComplex_of_im_pos (hz : 0 < z.im) : ((ofComplex z : ℍ) : ℂ) = z := by
  rw [ofComplex_apply_of_im_pos hz, coe_mk]

lemma comp_smul_eq_comp :
    (fun τ ↦ F (b • τ)) ∘ ofComplex = (F ∘ ofComplex) ∘ fun w ↦ ↑(b • ofComplex w) := by
  funext w
  simp only [Function.comp_apply, ofComplex_apply]

lemma analyticAt_coe_smul_ofComplex (hb : 0 < b.det.val) (hz : 0 < z.im) :
    AnalyticAt ℂ (fun w ↦ ↑(b • ofComplex w) : ℂ → ℂ) z := by
  simpa only [coe_ofComplex_of_im_pos hz] using (ofComplex z).analyticAt_smul hb

lemma im_sq_mul_normSq_deriv_coe_smul_ofComplex (hb : 0 < b.det.val) (hz : 0 < z.im) :
    z.im ^ 2 * Complex.normSq (deriv (fun w ↦ ↑(b • ofComplex w) : ℂ → ℂ) z) =
      ((b • ofComplex z : ℍ) : ℂ).im ^ 2 := by
  have hd : Complex.normSq (denom b z) ≠ 0 := normSq_denom_ne_zero b hz.ne'
  have h : deriv (fun w ↦ ↑(b • ofComplex w) : ℂ → ℂ) ((ofComplex z : ℍ) : ℂ) =
      (b.det.val : ℝ) / denom b (ofComplex z) ^ 2 := (ofComplex z).deriv_smul hb
  rw [coe_ofComplex_of_im_pos hz] at h
  rw [h, coe_smul_of_det_pos hb, coe_ofComplex_of_im_pos hz, moebius_im, map_div₀, map_pow,
    Complex.normSq_ofReal]
  field_simp

lemma contDiffOn_comp_smul (hb : 0 < b.det.val)
    (hF : ContDiffOn ℝ n (F ∘ ofComplex) {w | 0 < w.im}) :
    ContDiffOn ℝ n ((fun τ ↦ F (b • τ)) ∘ ofComplex) {w | 0 < w.im} := by
  rw [comp_smul_eq_comp]
  refine fun w hw ↦ ContDiffAt.contDiffWithinAt ?_
  exact (hF.contDiffAt <| isOpen_upperHalfPlaneSet.mem_nhds (b • ofComplex w).im_pos).comp w
    ((analyticAt_coe_smul_ofComplex hb hw).contDiffAt.restrict_scalars ℝ)

/-- **The hyperbolic Laplacian commutes with `GL(2, ℝ)⁺`**: for `b ∈ GL(2, ℝ)` with `det b > 0` and
`F` twice continuously differentiable on `ℍ`, the hyperbolic Laplacian of `z ↦ F(bz)` at `z` is the
one of `F` at `bz`. -/
lemma hyperbolicLaplacian_comp_smul (hb : 0 < b.det.val)
    (hF : ContDiffOn ℝ 2 (F ∘ ofComplex) {w | 0 < w.im}) (hz : 0 < z.im) :
    hyperbolicLaplacian ((fun τ ↦ F (b • τ)) ∘ ofComplex) z =
      hyperbolicLaplacian (F ∘ ofComplex) ↑(b • ofComplex z) := by
  rw [comp_smul_eq_comp]
  exact hyperbolicLaplacian_comp_of_analyticAt
    (hF.contDiffAt <| isOpen_upperHalfPlaneSet.mem_nhds (b • ofComplex z).im_pos)
    (analyticAt_coe_smul_ofComplex hb hz) (im_sq_mul_normSq_deriv_coe_smul_ofComplex hb hz)

variable (eigenvalue) in
/-- The complex vector space of **smooth eigenfunctions of the Laplacian that are square-integrable
on every translate of the standard domain**: the functions `H` on `ℍ` such that `H ∘ ofComplex` is
smooth on `ℍ`, `H` is square-integrable on `σ 𝒟ᵒ` for every `σ ∈ SL(2, ℤ)` and
`(Δ + λ) H = 0`. Its elements with a congruence invariance are Maass forms
(`mem_maassSpace_of_mem_maassTileSpace`), and it contains `F(βz)` for `F` a Maass form and
`β ∈ GL(2, ℚ)⁺` (`comp_smul_mem_maassTileSpace`). -/
noncomputable def maassTileSpace : Submodule ℂ (ℍ → ℂ) where
  carrier := {H | ContDiffOn ℝ ∞ (H ∘ ofComplex) {w | 0 < w.im} ∧
    (∀ σ : SL(2, ℤ), MemLp H 2 (volume.restrict (σ • fdo))) ∧
    ∀ w : ℂ, 0 < w.im → hyperbolicLaplacian (H ∘ ofComplex) w + eigenvalue * (H ∘ ofComplex) w = 0}
  add_mem' {H₁ H₂} hF hG := ⟨hF.1.add hG.1, fun σ ↦ (hF.2.1 σ).add (hG.2.1 σ), fun w hw ↦ by
    have h : hyperbolicLaplacian ((H₁ + H₂) ∘ ofComplex) w =
        hyperbolicLaplacian (H₁ ∘ ofComplex) w + hyperbolicLaplacian (H₂ ∘ ofComplex) w :=
      hyperbolicLaplacian_add (contDiffAt_two_of_contDiffOn hF.1 hw)
        (contDiffAt_two_of_contDiffOn hG.1 hw)
    have h0 : ((H₁ + H₂) ∘ ofComplex) w = (H₁ ∘ ofComplex) w + (H₂ ∘ ofComplex) w := rfl
    rw [h, h0]
    linear_combination hF.2.2 w hw + hG.2.2 w hw⟩
  zero_mem' := ⟨contDiffOn_const, fun σ ↦ MemLp.zero, fun w hw ↦ by
    simp [hyperbolicLaplacian]⟩
  smul_mem' c H hH := ⟨contDiffOn_const.mul hH.1, fun σ ↦ (hH.2.1 σ).const_mul c, fun w hw ↦ by
    have h :
        hyperbolicLaplacian ((c • H) ∘ ofComplex) w = c * hyperbolicLaplacian (H ∘ ofComplex) w :=
      hyperbolicLaplacian_const_mul c (contDiffAt_two_of_contDiffOn hH.1 hw)
    have h0 : ((c • H) ∘ ofComplex) w = c * (H ∘ ofComplex) w := rfl
    rw [h, h0]
    linear_combination c * hH.2.2 w hw⟩

variable [NeZero N]

/-- **Rational translates of Maass forms lie in `maassTileSpace`**: for `F` in `M(N, χ, λ)` and
`β ∈ GL(2, ℚ)` with `det β > 0`, the function `z ↦ F(βz)` is smooth, square-integrable on every
`σ 𝒟ᵒ` and has eigenvalue `λ`. -/
lemma comp_smul_mem_maassTileSpace (hF : F ∈ maassSpace N χ eigenvalue) (β : GL (Fin 2) ℚ)
    (hβ : 0 < (β : Matrix (Fin 2) (Fin 2) ℚ).det) :
    (fun z ↦ F (β.map (algebraMap ℚ ℝ) • z)) ∈ maassTileSpace eigenvalue := by
  have hb : 0 < (β.map (algebraMap ℚ ℝ)).det.val := ModularForm.det_map_ratCast_pos hβ
  refine ⟨contDiffOn_comp_smul hb hF.1, fun σ ↦ memLp_comp_smul β σ hF, fun w hw ↦ ?_⟩
  have h : hyperbolicLaplacian (F ∘ ofComplex) ↑(β.map (algebraMap ℚ ℝ) • ofComplex w) +
      eigenvalue * (F ∘ ofComplex) ↑(β.map (algebraMap ℚ ℝ) • ofComplex w) = 0 :=
    hF.2.2.2 _ (β.map (algebraMap ℚ ℝ) • ofComplex w).im_pos
  rw [hyperbolicLaplacian_comp_smul hb (hF.1.of_le (by simp)) hw]
  simpa only [Function.comp_apply, ofComplex_apply] using h

/-- **The `Γ₀(N)`-invariant elements of `maassTileSpace` are Maass forms**: an element `H` of
`maassTileSpace λ` with `H(γz) = H(z)` for all `γ ∈ Γ₀(N)`, `N ≠ 0`, lies in `M(N, 1, λ)`, the
fundamental domain `gammaZeroDomain N` being a finite union of translates of `𝒟ᵒ`. -/
lemma mem_maassSpace_of_mem_maassTileSpace (hH : H ∈ maassTileSpace eigenvalue)
    (hinv : ∀ γ ∈ Gamma0 N, ∀ τ : ℍ, H (γ • τ) = H τ) : H ∈ maassSpace N 1 eigenvalue := by
  refine ⟨hH.1, ?_, fun γ hγ z ↦ ?_, hH.2.2⟩
  · simp only [Function.comp_apply, ofComplex_apply]
    exact integrableOn_finite_iUnion.mpr fun q ↦
      (memLp_two_iff_integrable_sq_norm (hH.2.1 _).aestronglyMeasurable).mp (hH.2.1 _)
  · simp only [Function.comp_apply, ofComplex_apply, dirichletCharacter_one_apply_of_mem_gamma0 hγ,
      one_mul]
    exact hinv γ hγ z

end UpperHalfPlane
