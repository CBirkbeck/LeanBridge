import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.GreenIdentity
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-!
# Radial kernels on the upper half-plane

For `z` in `ℍ`, the function `w ↦ cosh d(z, w)` is
`coshDist z w = ((Re w - Re z)² + (Im w)² + (Im z)²) / (2 Im z Im w)`, and
`Δ_w φ(cosh d(z, w)) = (radialLaplacian φ)(cosh d(z, w))` with
`radialLaplacian φ (c) = (c² - 1) φ''(c) + 2 c φ'(c)`, since `|∇ cosh d|² = cosh² d - 1` and
`Δ cosh d = 2 cosh d` for the hyperbolic metric. For `φ` smooth and vanishing on `[C, ∞)`, the
function `w ↦ φ(cosh d(z, w))` is smooth with compact support in `ℍ`, so that Green's identity
(`UpperHalfPlane.integral_mul_hyperbolicLaplacian_eq`) gives, for `f` smooth on `ℍ`,
`∫_ℍ φ(cosh d(z, w)) Δf(w) dμ(w) = ∫_ℍ (radialLaplacian φ)(cosh d(z, w)) f(w) dμ(w)`.

## Main definitions

* `UpperHalfPlane.coshDist`: the function `w ↦ cosh d(z, w)`, on `ℂ`.
* `UpperHalfPlane.coshDistRe`, `UpperHalfPlane.coshDistIm`: its partial derivatives.
* `UpperHalfPlane.radialLaplacian`: the radial Laplacian.
* `UpperHalfPlane.coshDistKernel`: the function `w ↦ φ(cosh d(z, w))` on `ℍ`, extended by `0` to
  `ℂ`.

## Main results

* `UpperHalfPlane.hyperbolicLaplacian_ofReal_comp_coshDist`: the hyperbolic Laplacian of a radial
  function.
* `UpperHalfPlane.integral_kernel_mul_hyperbolicLaplacian`: Green's identity for a radial kernel.
-/

open Laplacian MeasureTheory Metric TauCeti Topology

open scoped ContDiff Gradient

namespace UpperHalfPlane

variable (z : ℍ) {φ : ℝ → ℝ} {w : ℂ} {H : ℂ → ℝ} {C : ℝ} {f : ℂ → ℂ}

lemma fderiv_one_eq_deriv_re (hH : DifferentiableAt ℝ H w) :
    fderiv ℝ H w 1 = deriv (fun s : ℝ ↦ H ⟨s, w.im⟩) w.re := by
  have hl : HasDerivAt (fun s : ℝ ↦ (⟨s, w.im⟩ : ℂ)) 1 w.re := by
    have h : (fun s : ℝ ↦ (⟨s, w.im⟩ : ℂ)) = fun s : ℝ ↦ (s : ℂ) + w.im * Complex.I := by
      funext s
      simp [Complex.ext_iff]
    rw [h]
    simpa using Complex.ofRealCLM.hasDerivAt.add_const (w.im * Complex.I : ℂ)
  exact (HasFDerivAt.comp_hasDerivAt w.re hH.hasFDerivAt hl).deriv.symm

lemma fderiv_I_eq_deriv_im (hH : DifferentiableAt ℝ H w) :
    fderiv ℝ H w Complex.I = deriv (fun t : ℝ ↦ H ⟨w.re, t⟩) w.im := by
  have hl : HasDerivAt (fun t : ℝ ↦ (⟨w.re, t⟩ : ℂ)) Complex.I w.im := by
    have h : (fun t : ℝ ↦ (⟨w.re, t⟩ : ℂ)) = fun t : ℝ ↦ (w.re : ℂ) + t * Complex.I := by
      funext t
      simp [Complex.ext_iff]
    rw [h]
    simpa using (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).const_add (w.re : ℂ)
  exact (HasFDerivAt.comp_hasDerivAt w.im hH.hasFDerivAt hl).deriv.symm

variable (w) in
/-- The extension to `w ∈ ℂ` of the function `w ↦ cosh d(z, w)` on `ℍ`
(`cosh_dist_eq_coshDist`). -/
noncomputable def coshDist : ℝ :=
  ((w.re - z.re) ^ 2 + w.im ^ 2 + z.im ^ 2) / (2 * z.im * w.im)

lemma cosh_dist_eq_coshDist (τ : ℍ) : Real.cosh (dist z τ) = coshDist z τ := by
  rw [cosh_dist', coshDist, coe_re, coe_im]
  congr 1
  ring1

lemma contDiffAt_coshDist (hw : w.im ≠ 0) : ContDiffAt ℝ ∞ (coshDist z) w := by
  have hre : ContDiffAt ℝ ∞ (fun c : ℂ ↦ c.re) w := Complex.reCLM.contDiff.contDiffAt
  have him : ContDiffAt ℝ ∞ (fun c : ℂ ↦ c.im) w := Complex.imCLM.contDiff.contDiffAt
  refine ContDiffAt.div (by fun_prop) (contDiffAt_const.mul him) ?_
  exact mul_ne_zero (mul_ne_zero two_ne_zero z.im_pos.ne') hw

variable (w) in
/-- The partial derivative of `coshDist z` in `Re w`. -/
noncomputable def coshDistRe : ℝ :=
  (w.re - z.re) / (z.im * w.im)

variable (w) in
/-- The partial derivative of `coshDist z` in `Im w`. -/
noncomputable def coshDistIm : ℝ :=
  (w.im ^ 2 - z.im ^ 2 - (w.re - z.re) ^ 2) / (2 * z.im * w.im ^ 2)

lemma contDiffAt_coshDistRe (hw : w.im ≠ 0) : ContDiffAt ℝ ∞ (coshDistRe z) w := by
  have hre : ContDiffAt ℝ ∞ (fun c : ℂ ↦ c.re) w := Complex.reCLM.contDiff.contDiffAt
  have him : ContDiffAt ℝ ∞ (fun c : ℂ ↦ c.im) w := Complex.imCLM.contDiff.contDiffAt
  exact ContDiffAt.div (hre.sub contDiffAt_const) (contDiffAt_const.mul him)
    (mul_ne_zero z.im_pos.ne' hw)

lemma contDiffAt_coshDistIm (hw : w.im ≠ 0) : ContDiffAt ℝ ∞ (coshDistIm z) w := by
  have hre : ContDiffAt ℝ ∞ (fun c : ℂ ↦ c.re) w := Complex.reCLM.contDiff.contDiffAt
  have him : ContDiffAt ℝ ∞ (fun c : ℂ ↦ c.im) w := Complex.imCLM.contDiff.contDiffAt
  refine ContDiffAt.div (by fun_prop) (contDiffAt_const.mul (him.pow 2)) ?_
  exact mul_ne_zero (mul_ne_zero two_ne_zero z.im_pos.ne') (pow_ne_zero 2 hw)

lemma fderiv_coshDist_one (hw : w.im ≠ 0) : fderiv ℝ (coshDist z) w 1 = coshDistRe z w := by
  rw [fderiv_one_eq_deriv_re ((contDiffAt_coshDist z hw).differentiableAt (by simp))]
  have hz : z.im ≠ 0 := z.im_pos.ne'
  have h1 :
      HasDerivAt (fun s : ℝ ↦ (s - z.re) ^ 2 + w.im ^ 2 + z.im ^ 2) (2 * (w.re - z.re)) w.re := by
    simpa using ((((hasDerivAt_id' w.re).sub_const z.re).pow 2).add_const (w.im ^ 2)).add_const
      (z.im ^ 2)
  have h : HasDerivAt (fun s : ℝ ↦ coshDist z ⟨s, w.im⟩) (coshDistRe z w) w.re :=
    (h1.div_const (2 * z.im * w.im)).congr_deriv <| by
      rw [coshDistRe]
      field_simp
  exact h.deriv

lemma fderiv_coshDist_I (hw : w.im ≠ 0) : fderiv ℝ (coshDist z) w Complex.I = coshDistIm z w := by
  rw [fderiv_I_eq_deriv_im ((contDiffAt_coshDist z hw).differentiableAt (by simp))]
  have hz : z.im ≠ 0 := z.im_pos.ne'
  have h1 : HasDerivAt (fun t : ℝ ↦ (w.re - z.re) ^ 2 + t ^ 2 + z.im ^ 2) (2 * w.im) w.im := by
    simpa using (((hasDerivAt_id' w.im).pow 2).const_add ((w.re - z.re) ^ 2)).add_const
      (z.im ^ 2)
  have h2 : HasDerivAt (fun t : ℝ ↦ 2 * z.im * t) (2 * z.im) w.im := by
    simpa using (hasDerivAt_id' w.im).const_mul (2 * z.im)
  have h : HasDerivAt (fun t : ℝ ↦ coshDist z ⟨w.re, t⟩) (coshDistIm z w) w.im :=
    (h1.div h2 (mul_ne_zero (mul_ne_zero two_ne_zero hz) hw)).congr_deriv <| by
      rw [coshDistIm]
      field_simp
      ring1
  exact h.deriv

lemma fderiv_coshDistRe_one (hw : w.im ≠ 0) : fderiv ℝ (coshDistRe z) w 1 = 1 / (z.im * w.im) := by
  rw [fderiv_one_eq_deriv_re ((contDiffAt_coshDistRe z hw).differentiableAt (by simp))]
  have h : HasDerivAt (fun s : ℝ ↦ coshDistRe z ⟨s, w.im⟩) (1 / (z.im * w.im)) w.re :=
    ((hasDerivAt_id' w.re).sub_const z.re).div_const (z.im * w.im)
  exact h.deriv

lemma fderiv_coshDistIm_I (hw : w.im ≠ 0) :
    fderiv ℝ (coshDistIm z) w Complex.I = (z.im ^ 2 + (w.re - z.re) ^ 2) / (z.im * w.im ^ 3) := by
  rw [fderiv_I_eq_deriv_im ((contDiffAt_coshDistIm z hw).differentiableAt (by simp))]
  have hz : z.im ≠ 0 := z.im_pos.ne'
  have h1 : HasDerivAt (fun t : ℝ ↦ t ^ 2 - z.im ^ 2 - (w.re - z.re) ^ 2) (2 * w.im) w.im := by
    simpa using (((hasDerivAt_id' w.im).pow 2).sub_const (z.im ^ 2)).sub_const
      ((w.re - z.re) ^ 2)
  have h2 : HasDerivAt (fun t : ℝ ↦ 2 * z.im * t ^ 2) (2 * z.im * (2 * w.im)) w.im := by
    simpa using ((hasDerivAt_id' w.im).pow 2).const_mul (2 * z.im)
  have h : HasDerivAt (fun t : ℝ ↦ coshDistIm z ⟨w.re, t⟩)
      ((z.im ^ 2 + (w.re - z.re) ^ 2) / (z.im * w.im ^ 3)) w.im :=
    (h1.div h2 (mul_ne_zero (mul_ne_zero two_ne_zero hz) (pow_ne_zero 2 hw))).congr_deriv <| by
      field_simp
      ring1
  exact h.deriv

variable (φ) in
/-- The **radial Laplacian** `(c² - 1) φ''(c) + 2 c φ'(c)` of a function `φ` of `c = cosh d`, so
that `Δ_w φ(cosh d(z, w))` is `(radialLaplacian φ)(cosh d(z, w))`
(`hyperbolicLaplacian_ofReal_comp_coshDist`). -/
noncomputable def radialLaplacian (c : ℝ) : ℝ :=
  (c ^ 2 - 1) * deriv (deriv φ) c + 2 * c * deriv φ c

lemma norm_gradient_coshDist_sq (hw : w.im ≠ 0) :
    ‖∇ (coshDist z) w‖ ^ 2 = coshDistRe z w ^ 2 + coshDistIm z w ^ 2 := by
  rw [← Complex.orthonormalBasisOneI.sum_sq_norm_inner_left, Fin.sum_univ_two,
    Complex.coe_orthonormalBasisOneI]
  simp [fderiv_coshDist_one z hw, fderiv_coshDist_I z hw]

lemma laplacian_coshDist (hw : 0 < w.im) :
    Δ (coshDist z) w = 1 / (z.im * w.im) + (z.im ^ 2 + (w.re - z.re) ^ 2) / (z.im * w.im ^ 3) := by
  have hq : ContDiffAt ℝ 2 (coshDist z) w := (contDiffAt_coshDist z hw.ne').of_le (by simp)
  have h1 : (fun c ↦ fderiv ℝ (coshDist z) c 1) =ᶠ[𝓝 w] coshDistRe z := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with c (hc : 0 < c.im)
    exact fderiv_coshDist_one z hc.ne'
  have h2 : (fun c ↦ fderiv ℝ (coshDist z) c Complex.I) =ᶠ[𝓝 w] coshDistIm z := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with c (hc : 0 < c.im)
    exact fderiv_coshDist_I z hc.ne'
  rw [laplacian_eq_sum_fderiv_fderiv_apply Complex.orthonormalBasisOneI
    (hq.hasFDerivAt_fderiv le_rfl).differentiableAt, Fin.sum_univ_two,
    Complex.coe_orthonormalBasisOneI]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h1.fderiv_eq, h2.fderiv_eq, fderiv_coshDistRe_one z hw.ne', fderiv_coshDistIm_I z hw.ne']

/-- **The hyperbolic Laplacian of a radial function**: for `φ` smooth, the function
`w ↦ φ(cosh d(z, w))` has hyperbolic Laplacian `(c² - 1) φ''(c) + 2 c φ'(c)` at `c = cosh d(z, w)`,
since `|∇ cosh d|² = cosh² d - 1` and `Δ cosh d = 2 cosh d`. -/
lemma hyperbolicLaplacian_ofReal_comp_coshDist (hφ : ContDiff ℝ ∞ φ) (hw : 0 < w.im) :
    hyperbolicLaplacian (fun c ↦ (φ (coshDist z c) : ℂ)) w =
      (radialLaplacian φ (coshDist z w) : ℝ) := by
  have hq : ContDiffAt ℝ 2 (coshDist z) w := (contDiffAt_coshDist z hw.ne').of_le (by simp)
  have hφ2 : ContDiffAt ℝ 2 φ (coshDist z w) := hφ.contDiffAt.of_le (by simp)
  have h : hyperbolicLaplacian (fun c ↦ (φ (coshDist z c) : ℂ)) w =
      (w.im ^ 2 : ℝ) * (Δ (φ ∘ coshDist z) w : ℝ) :=
    hyperbolicLaplacian_ofReal_comp (hφ2.comp w hq)
  rw [h, hφ2.laplacian_comp hq, norm_gradient_coshDist_sq z hw.ne', laplacian_coshDist z hw,
    radialLaplacian]
  have hz : z.im ≠ 0 := z.im_pos.ne'
  have hw0 : w.im ≠ 0 := hw.ne'
  simp only [coshDist, coshDistRe, coshDistIm]
  norm_cast
  field_simp
  ring1

variable (φ w) in
/-- The function `w ↦ φ(cosh d(z, w))` on `ℍ`, extended by `0` to `ℂ`: for `φ` smooth and vanishing
on `[C, ∞)`, it is smooth with compact support in `ℍ`. -/
noncomputable def coshDistKernel : ℝ :=
  if 0 < w.im then φ (coshDist z w) else 0

lemma coshDistKernel_coe (τ : ℍ) : coshDistKernel z φ τ = φ (Real.cosh (dist z τ)) := by
  have hw : 0 < (τ : ℂ).im := τ.im_pos
  rw [coshDistKernel, ite_eq_left hw, cosh_dist_eq_coshDist]

lemma half_le_cosh (d : ℝ) : d / 2 ≤ Real.cosh d := by
  rw [Real.cosh_eq]
  linarith [Real.add_one_le_exp d, Real.exp_pos (-d)]

lemma comp_cosh_dist_eq_zero (hφ0 : ∀ c, C ≤ c → φ c = 0) {τ : ℍ}
    (hτ : τ ∉ closedBall z (2 * |C|)) : φ (Real.cosh (dist z τ)) = 0 := by
  refine hφ0 _ ?_
  have h : 2 * |C| < dist z τ := by
    rw [mem_closedBall, not_le, dist_comm] at hτ
    exact hτ
  linarith [half_le_cosh (dist z τ), le_abs_self C]

lemma isCompact_image_coe_closedBall (r : ℝ) : IsCompact (((↑) : ℍ → ℂ) '' closedBall z r) :=
  (isCompact_closedBall z r).image continuous_coe

lemma image_coe_subset_im_pos (s : Set ℍ) : ((↑) : ℍ → ℂ) '' s ⊆ {c | 0 < c.im} := by
  rintro _ ⟨w, -, rfl⟩
  exact w.im_pos

lemma coshDistKernel_eq_zero (hφ0 : ∀ c, C ≤ c → φ c = 0)
    (hw : w ∉ ((↑) : ℍ → ℂ) '' closedBall z (2 * |C|)) : coshDistKernel z φ w = 0 := by
  by_cases him : 0 < w.im
  · have h : (⟨w, him⟩ : ℍ) ∉ closedBall z (2 * |C|) := fun h ↦ hw ⟨_, h, rfl⟩
    have h1 : coshDistKernel z φ (⟨w, him⟩ : ℍ) = φ (Real.cosh (dist z ⟨w, him⟩)) :=
      coshDistKernel_coe z ⟨w, him⟩
    rw [comp_cosh_dist_eq_zero z hφ0 h] at h1
    exact h1
  · rw [coshDistKernel, ite_eq_right him]

lemma hasCompactSupport_coshDistKernel (hφ0 : ∀ c, C ≤ c → φ c = 0) :
    HasCompactSupport (coshDistKernel z φ) :=
  HasCompactSupport.intro (isCompact_image_coe_closedBall z _)
    fun _ hw ↦ coshDistKernel_eq_zero z hφ0 hw

lemma tsupport_coshDistKernel_subset (hφ0 : ∀ c, C ≤ c → φ c = 0) :
    tsupport (coshDistKernel z φ) ⊆ {c | 0 < c.im} :=
  (closure_minimal (fun _ hw ↦ by_contra fun h ↦
    (Function.mem_support.mp hw) (coshDistKernel_eq_zero z hφ0 h))
    (isCompact_image_coe_closedBall z _).isClosed).trans (image_coe_subset_im_pos _)

lemma coshDistKernel_eventuallyEq (hw : 0 < w.im) :
    coshDistKernel z φ =ᶠ[𝓝 w] fun c ↦ φ (coshDist z c) := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with c (hc : 0 < c.im)
  rw [coshDistKernel, ite_eq_left hc]

lemma contDiff_coshDistKernel (hφ : ContDiff ℝ ∞ φ) (hφ0 : ∀ c, C ≤ c → φ c = 0) :
    ContDiff ℝ ∞ (coshDistKernel z φ) := by
  refine contDiff_iff_contDiffAt.mpr fun w ↦ ?_
  by_cases him : 0 < w.im
  · exact (hφ.contDiffAt.comp w (contDiffAt_coshDist z him.ne')).congr_of_eventuallyEq
      (coshDistKernel_eventuallyEq z him)
  · have h : w ∉ ((↑) : ℍ → ℂ) '' closedBall z (2 * |C|) := fun h ↦
      him (image_coe_subset_im_pos _ h)
    have hopen : IsOpen (((↑) : ℍ → ℂ) '' closedBall z (2 * |C|))ᶜ :=
      (isCompact_image_coe_closedBall z _).isClosed.isOpen_compl
    refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : ℝ))) ?_
    filter_upwards [hopen.mem_nhds h] with c hc
    exact coshDistKernel_eq_zero z hφ0 hc

/-- **Green's identity for a radial kernel**: for `φ` smooth vanishing on `[C, ∞)` and `f` smooth on
`ℍ`, `∫_ℍ φ(cosh d(z, w)) Δf(w) dμ(w) = ∫_ℍ (radialLaplacian φ)(cosh d(z, w)) f(w) dμ(w)`. -/
lemma integral_kernel_mul_hyperbolicLaplacian (hφ : ContDiff ℝ ∞ φ) (hφ0 : ∀ c, C ≤ c → φ c = 0)
    (hf : ContDiffOn ℝ ∞ f {w | 0 < w.im}) :
    ∫ w : ℍ, (φ (Real.cosh (dist z w)) : ℂ) * hyperbolicLaplacian f w =
      ∫ w : ℍ, (radialLaplacian φ (Real.cosh (dist z w)) : ℂ) * f w := by
  have h : ∫ w : ℍ, (coshDistKernel z φ w : ℂ) * hyperbolicLaplacian f w =
      ∫ w : ℍ, hyperbolicLaplacian (fun c ↦ (coshDistKernel z φ c : ℂ)) w * f w :=
    integral_mul_hyperbolicLaplacian_eq (contDiff_coshDistKernel z hφ hφ0)
      (hasCompactSupport_coshDistKernel z hφ0) (tsupport_coshDistKernel_subset z hφ0) hf
  simp only [coshDistKernel_coe] at h
  rw [h]
  refine integral_congr_ae (.of_forall fun w ↦ ?_)
  dsimp only
  have hev : (fun c ↦ (coshDistKernel z φ c : ℂ)) =ᶠ[𝓝 (w : ℂ)] fun c ↦ (φ (coshDist z c) : ℂ) :=
    (coshDistKernel_eventuallyEq z w.im_pos).fun_comp Complex.ofReal
  rw [hyperbolicLaplacian_congr hev, hyperbolicLaplacian_ofReal_comp_coshDist z hφ w.im_pos,
    cosh_dist_eq_coshDist]

end UpperHalfPlane
