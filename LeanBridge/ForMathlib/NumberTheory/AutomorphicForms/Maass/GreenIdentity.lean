import LeanBridge.ForMathlib.Analysis.Complex.UpperHalfPlane.StripIntegral
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.LaplacianMoebius
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# Green's identity for the hyperbolic Laplacian on `ℍ`

For `T` real-valued and smooth on `ℂ` with compact support in `ℍ` and `f` smooth on `ℍ`,
`∫_ℍ T Δf dμ = ∫_ℍ (ΔT) f dμ` for the hyperbolic Laplacian `Δ = y² (∂²/∂x² + ∂²/∂y²)` and the
invariant measure `dμ = dx dy / y²`: in coordinates, the factors `y²` and `y⁻²` cancel, and this is
Tau Ceti's Green's second identity for the flat Laplacian against a test function on the open set
`ℍ` of `ℂ` (`ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian`).

## Main results

* `UpperHalfPlane.integral_eq_setIntegral_im_pos`: the invariant integral on `ℍ` in coordinates on
  `ℂ`.
* `UpperHalfPlane.integral_mul_hyperbolicLaplacian_eq`: Green's identity.
-/

open Laplacian MeasureTheory Set TauCeti

open scoped ContDiff NNReal

namespace UpperHalfPlane

variable {T : ℂ → ℝ} {f A : ℂ → ℂ} {c : ℂ}

/-- **The invariant integral on `ℍ` in coordinates on `ℂ`**: the integral of `G` for the invariant
measure is the Lebesgue integral over `{Im c > 0}` of `(Im c)⁻² G(c)`. -/
lemma integral_eq_setIntegral_im_pos (G : ℍ → ℂ) :
    ∫ z, G z = ∫ c in {c : ℂ | 0 < c.im}, ((c.im ^ 2)⁻¹ : ℝ) • G (ofComplex c) := by
  rw [volume_def, integral_withDensity_eq_integral_smul measurable_volume_density]
  have h1 : ∫ z, ((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) • G z
      ∂(Measure.comap UpperHalfPlane.coe volume) =
        ∫ z, ((((z : ℂ).im ^ 2)⁻¹ : ℝ) • G (ofComplex (z : ℂ)))
          ∂(Measure.comap UpperHalfPlane.coe volume) := by
    refine integral_congr_ae (.of_forall fun z ↦ ?_)
    dsimp only
    rw [ofComplex_apply, NNReal.smul_def]
    simp
  refine h1.trans <| (measurableEmbedding_coe.integral_map
    (fun c : ℂ ↦ (((c.im ^ 2)⁻¹ : ℝ) • G (ofComplex c)))).symm.trans ?_
  rw [measurableEmbedding_coe.map_comap, range_coe]

lemma integral_eq_integral_of_forall_im_pos {G : ℍ → ℂ}
    (h : ∀ c : ℂ, 0 < c.im → ((c.im ^ 2)⁻¹ : ℝ) • G (ofComplex c) = A c)
    (h0 : ∀ c : ℂ, ¬0 < c.im → A c = 0) : ∫ z, G z = ∫ c, A c := by
  rw [integral_eq_setIntegral_im_pos, ← integral_indicator isOpen_upperHalfPlaneSet.measurableSet]
  refine integral_congr_ae (.of_forall fun c ↦ ?_)
  by_cases hc : 0 < c.im
  · rw [indicator_of_mem (by exact hc), h c hc]
  · rw [indicator_of_notMem (by exact hc), h0 c hc]

lemma hyperbolicLaplacian_eq_mul_laplacian (hf : ContDiffAt ℝ 2 f c) :
    hyperbolicLaplacian f c = (c.im ^ 2 : ℝ) * Δ f c := by
  rw [hyperbolicLaplacian, laplacian_eq_sum_fderiv_fderiv_apply Complex.orthonormalBasisOneI
    (hf.hasFDerivAt_fderiv le_rfl).differentiableAt, Complex.coe_orthonormalBasisOneI]
  simp

lemma hyperbolicLaplacian_ofReal_comp (hT : ContDiffAt ℝ 2 T c) :
    hyperbolicLaplacian (fun w ↦ (T w : ℂ)) c = (c.im ^ 2 : ℝ) * (Δ T c : ℝ) := by
  have h : hyperbolicLaplacian (Complex.ofRealCLM ∘ T) c =
      (c.im ^ 2 : ℝ) * Δ (Complex.ofRealCLM ∘ T) c :=
    hyperbolicLaplacian_eq_mul_laplacian (Complex.ofRealCLM.contDiff.comp_contDiffAt c hT)
  rw [hT.laplacian_CLM_comp_left] at h
  exact h

/-- **Green's identity on `ℍ`**: for `T` real-valued and smooth on `ℂ` with compact support in `ℍ`
and `f` smooth on `ℍ`, `∫_ℍ T Δf dμ = ∫_ℍ (ΔT) f dμ` for the hyperbolic Laplacian `Δ` and the
invariant measure `μ`. -/
lemma integral_mul_hyperbolicLaplacian_eq (hT : ContDiff ℝ ∞ T) (hK : HasCompactSupport T)
    (hTS : tsupport T ⊆ {w | 0 < w.im}) (hf : ContDiffOn ℝ ∞ f {w | 0 < w.im}) :
    ∫ z : ℍ, (T z : ℂ) * hyperbolicLaplacian f z =
      ∫ z : ℍ, hyperbolicLaplacian (fun w ↦ (T w : ℂ)) z * f z := by
  have hL : ∫ z : ℍ, (T z : ℂ) * hyperbolicLaplacian f z = ∫ c, T c • Δ f c := by
    refine integral_eq_integral_of_forall_im_pos (fun c hc ↦ ?_) fun c hc ↦ ?_
    · have hc2 : (c.im : ℂ) ≠ 0 := by
        exact_mod_cast hc.ne'
      rw [coe_ofComplex_of_im_pos hc, hyperbolicLaplacian_eq_mul_laplacian
        (contDiffAt_two_of_contDiffOn hf hc), Complex.real_smul, Complex.real_smul]
      push_cast
      field_simp
    · have hT0 : T c = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hc (hTS h)
      simp [hT0]
  have hR : ∫ z : ℍ, hyperbolicLaplacian (fun w ↦ (T w : ℂ)) z * f z = ∫ c, Δ T c • f c := by
    refine integral_eq_integral_of_forall_im_pos (fun c hc ↦ ?_) fun c hc ↦ ?_
    · have hc2 : (c.im : ℂ) ≠ 0 := by
        exact_mod_cast hc.ne'
      rw [coe_ofComplex_of_im_pos hc, hyperbolicLaplacian_ofReal_comp
        (hT.contDiffAt.of_le (by simp)), Complex.real_smul, Complex.real_smul]
      push_cast
      field_simp
    · have h0 : Δ T c = 0 :=
        image_eq_zero_of_notMem_tsupport fun h ↦ hc (hTS (tsupport_laplacian_subset T h))
      simp [h0]
  rw [hL, hR]
  exact ((hf.of_le (by simp)).integral_laplacian_smul_eq_integral_smul_laplacian
    (Ω := ⟨{w | 0 < w.im}, isOpen_upperHalfPlaneSet⟩) ⟨T, hT, hK, hTS⟩).symm

end UpperHalfPlane
