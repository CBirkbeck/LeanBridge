import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.HeckeAlgebra
import Mathlib.Geometry.Euclidean.Inversion.Calculus
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.RingTheory.Complex

/-!
# The hyperbolic volume is invariant under `SL(2, ℂ)`

The hyperbolic volume `dx₁ dx₂ dy / y³` on `ℋ₃` (`hyperbolicVolume`) is invariant under the action
of `SL(2, ℂ)`. By the Bruhat decomposition it suffices to treat the translations
`(x, y) ↦ (x + t, y)`, the diagonal matrices, which act by `(x, y) ↦ (a²x, |a|²y)`, and
`(0, -1; 1, 0)`, which acts by `(x, y) ↦ (-x̄, y) / (|x|² + y²)`, the composition of an isometry of
`ℝ³` and of the inversion in the unit sphere, whose derivative at `v` is `|v|⁻²` times a reflection
(`EuclideanGeometry.hasFDerivAt_inversion`). In each case the Jacobian of `g` at `(x, y)` is
`N⁻³`, where `N = |cx + d|² + |c|²y²` and the height of `g(x, y)` is `y / N`.

## Main results

* `HyperbolicThreeSpace.hyperbolicVolume_apply`: the hyperbolic volume as an integral over the image
  in `ℂ × ℝ`.
* `HyperbolicThreeSpace.hyperbolicVolume_smul`: the hyperbolic volume of `g A` is that of `A`.
* The instances `ContinuousConstSMul SL(2, ℂ) HyperbolicThreeSpace` and
  `SMulInvariantMeasure SL(2, ℂ) HyperbolicThreeSpace hyperbolicVolume`.
-/

open Complex EuclideanGeometry Matrix MeasureTheory Set TauCeti

open scoped ComplexConjugate MatrixGroups Pointwise

namespace HyperbolicThreeSpace

variable (g : SL(2, ℂ)) {A : Set HyperbolicThreeSpace}

instance : SecondCountableTopology HyperbolicThreeSpace :=
  inferInstanceAs (SecondCountableTopology (upperHalfSpaceOpens ℂ))

instance : BorelSpace HyperbolicThreeSpace :=
  inferInstanceAs (BorelSpace (upperHalfSpaceOpens ℂ))

lemma isOpenEmbedding_coords : Topology.IsOpenEmbedding coords :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℝ).toHomeomorph.isOpenEmbedding.comp
    (upperHalfSpaceOpens ℂ).isOpen.isOpenEmbedding_subtypeVal

instance : LocallyCompactSpace HyperbolicThreeSpace :=
  isOpenEmbedding_coords.locallyCompactSpace

lemma range_coords : range coords = {p : ℂ × ℝ | 0 < p.2} := by
  ext p
  refine ⟨?_, fun hp ↦ ⟨.mk (WithLp.toLp 2 p) hp, rfl⟩⟩
  rintro ⟨z, rfl⟩
  exact coords_snd_pos z

instance : ContinuousConstSMul SL(2, ℂ) HyperbolicThreeSpace where
  continuous_const_smul g := isOpenEmbedding_coords.isInducing.continuous_iff.mpr <|
    continuous_iff_continuousAt.mpr fun z ↦
      (analyticAt_moebius g (coords_snd_pos z)).continuousAt.comp
        isOpenEmbedding_coords.continuous.continuousAt

/-- **The hyperbolic volume as an integral**: for a measurable subset `A` of `ℋ₃`, its hyperbolic
volume is `∫_A dx₁ dx₂ dy / y³`, over the image of `A` in `ℂ × ℝ`. -/
lemma hyperbolicVolume_apply (hA : MeasurableSet A) :
    hyperbolicVolume A = ∫⁻ p in coords '' A, ENNReal.ofReal (p.2 ^ 3)⁻¹ := by
  have hsub : coords '' A ⊆ range coords := image_subset_range _ _
  have h₁ : (volume : Measure (ℂ × ℝ)).restrict (coords '' A) =
      (volume.restrict (range coords)).restrict (coords '' A) :=
    (Measure.restrict_restrict_of_subset hsub).symm
  rw [hyperbolicVolume, withDensity_apply _ hA, h₁, ← measurableEmbedding_coords.map_comap,
    setLIntegral_map (measurableEmbedding_coords.measurableSet_image.mpr hA) (by fun_prop)
      measurableEmbedding_coords.measurable, preimage_image_eq _ coords_injective]
  rfl

lemma moebius_inv_moebius {p : ℂ × ℝ} (hp : 0 < p.2) : moebius g⁻¹ (moebius g p) = p := by
  rw [← moebius_mul _ _ hp, inv_mul_cancel, moebius_one]

lemma coords_image_smul : coords '' (g • A) = moebius g '' (coords '' A) := by
  rw [← image_smul, image_image, image_image]
  rfl

instance : (volume : Measure (ℂ × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

private lemma lintegral_image_moebius {f' : ℂ × ℝ → (ℂ × ℝ) →L[ℝ] (ℂ × ℝ)}
    (hf : ∀ p : ℂ × ℝ, 0 < p.2 → HasFDerivAt (moebius g) (f' p) p)
    (hdet : ∀ p : ℂ × ℝ, 0 < p.2 → |(f' p).det| = (moebiusDenom g p)⁻¹ ^ 3) {s : Set (ℂ × ℝ)}
    (hs : MeasurableSet s) (hsU : ∀ p ∈ s, 0 < p.2) :
    ∫⁻ p in moebius g '' s, ENNReal.ofReal (p.2 ^ 3)⁻¹ = ∫⁻ p in s, ENNReal.ofReal (p.2 ^ 3)⁻¹ := by
  have hinj : InjOn (moebius g) s := fun p hp q hq hpq ↦ by
    rw [← moebius_inv_moebius g (hsU p hp), hpq, moebius_inv_moebius g (hsU q hq)]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun p hp ↦ (hf p (hsU p hp)).hasFDerivWithinAt) hinj]
  refine setLIntegral_congr_fun hs fun p hp ↦ ?_
  have hN : 0 < moebiusDenom g p := moebiusDenom_pos g (hsU p hp)
  have hy : 0 < p.2 := hsU p hp
  have h₂ : (moebius g p).2 = p.2 / moebiusDenom g p :=
    rfl
  rw [hdet p hy, h₂, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

private lemma hyperbolicVolume_smul_of_hasFDerivAt {f' : ℂ × ℝ → (ℂ × ℝ) →L[ℝ] (ℂ × ℝ)}
    (hf : ∀ p : ℂ × ℝ, 0 < p.2 → HasFDerivAt (moebius g) (f' p) p)
    (hdet : ∀ p : ℂ × ℝ, 0 < p.2 → |(f' p).det| = (moebiusDenom g p)⁻¹ ^ 3) (hA : MeasurableSet A) :
    hyperbolicVolume (g • A) = hyperbolicVolume A := by
  have hs : MeasurableSet (coords '' A) := measurableEmbedding_coords.measurableSet_image.mpr hA
  rw [hyperbolicVolume_apply (hA.const_smul g), hyperbolicVolume_apply hA, coords_image_smul,
    lintegral_image_moebius g hf hdet hs]
  rintro _ ⟨z, -, rfl⟩
  exact coords_snd_pos z

variable (t a : ℂ)

/-- The translation `(1, t; 0, 1)` of `SL(2, ℂ)`. -/
private def slTranslation : SL(2, ℂ) :=
  ⟨!![1, t; 0, 1], by simp⟩

/-- The diagonal matrix `(a, 0; 0, a⁻¹)` of `SL(2, ℂ)`, for `a ≠ 0`. -/
private noncomputable def slDiagonal (ha : a ≠ 0) : SL(2, ℂ) :=
  ⟨!![a, 0; 0, a⁻¹], by simp [ha]⟩

/-- The matrix `(0, -1; 1, 0)` of `SL(2, ℂ)`. -/
private def slInversion : SL(2, ℂ) :=
  ⟨!![0, -1; 1, 0], by simp⟩

private lemma hyperbolicVolume_slTranslation_smul (hA : MeasurableSet A) :
    hyperbolicVolume (slTranslation t • A) = hyperbolicVolume A := by
  refine hyperbolicVolume_smul_of_hasFDerivAt _ (f' := fun _ ↦ .id ℝ _) (fun p _ ↦ ?_)
    (fun p _ ↦ ?_)
    hA
  · have h : moebius (slTranslation t) = fun q ↦ q + (t, 0) := by
      funext q
      refine Prod.ext ?_ ?_ <;> simp [moebius, moebiusDenom, slTranslation]
    rw [h]
    exact (hasFDerivAt_id p).add_const _
  · simp [moebiusDenom, slTranslation, ContinuousLinearMap.det]

private lemma hyperbolicVolume_slDiagonal_smul (ha : a ≠ 0) (hA : MeasurableSet A) :
    hyperbolicVolume (slDiagonal a ha • A) = hyperbolicVolume A := by
  have hn : normSq a ≠ 0 := normSq_eq_zero.not.mpr ha
  let L : (ℂ × ℝ) →L[ℝ] (ℂ × ℝ) :=
    ContinuousLinearMap.prodMap ((a ^ 2) • ContinuousLinearMap.id ℝ ℂ)
      (normSq a • ContinuousLinearMap.id ℝ ℝ)
  refine hyperbolicVolume_smul_of_hasFDerivAt _ (f' := fun _ ↦ L) (fun p _ ↦ ?_) (fun p _ ↦ ?_) hA
  · have h : moebius (slDiagonal a ha) = L := by
      funext q
      have hc : (normSq a : ℂ) = a * conj a := (mul_conj a).symm
      have hc' : conj a ≠ 0 := (map_ne_zero _).mpr ha
      refine Prod.ext ?_ ?_
      · simp only [moebius, moebiusDenom, slDiagonal, L]
        simp [hc]
        field_simp
      · simp only [moebius, moebiusDenom, slDiagonal, L]
        simp
        field_simp
    rw [h]
    exact L.hasFDerivAt
  · have hdet : L.det = normSq a ^ 3 := by
      have h₁ : (L : (ℂ × ℝ) →ₗ[ℝ] (ℂ × ℝ)) = LinearMap.prodMap (Algebra.lmul ℝ ℂ (a ^ 2))
          (normSq a • LinearMap.id) := by
        ext <;> simp [L]
      have h₂ : L.det = LinearMap.det (L : (ℂ × ℝ) →ₗ[ℝ] (ℂ × ℝ)) :=
        rfl
      rw [h₂, h₁, LinearMap.det_prodMap, ← Algebra.norm_apply, Algebra.norm_complex_apply,
        LinearMap.det_smul, LinearMap.det_id, map_pow]
      simp
      ring1
    rw [hdet]
    simp [moebiusDenom, slDiagonal, abs_of_nonneg (normSq_nonneg a)]

private lemma abs_det_eq_one_of_comp_self {V : Type*} [AddCommGroup V] [Module ℝ V] {L : V →ₗ[ℝ] V}
    (h : L ∘ₗ L = LinearMap.id) : |LinearMap.det L| = 1 := by
  have h₁ : LinearMap.det L * LinearMap.det L = 1 := by
    rw [← LinearMap.det_comp, h, LinearMap.det_id]
  rcases mul_self_eq_one_iff.mp h₁ with h₂ | h₂ <;> simp [h₂]

private lemma abs_det_reflection {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K : Submodule ℝ V) [K.HasOrthogonalProjection] :
    |LinearMap.det ((K.reflection : V →L[ℝ] V) : V →ₗ[ℝ] V)| = 1 :=
  abs_det_eq_one_of_comp_self <| LinearMap.ext fun v ↦ K.reflection_reflection v

private lemma hyperbolicVolume_slInversion_smul (hA : MeasurableSet A) :
    hyperbolicVolume (slInversion • A) = hyperbolicVolume A := by
  let P : WithLp 2 (ℂ × ℝ) ≃L[ℝ] ℂ × ℝ := WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℝ
  let ρ : (ℂ × ℝ) →L[ℝ] (ℂ × ℝ) :=
    ContinuousLinearMap.prodMap (-(conjCLE : ℂ →L[ℝ] ℂ)) (.id ℝ ℝ)
  let R (p : ℂ × ℝ) : WithLp 2 (ℂ × ℝ) →L[ℝ] WithLp 2 (ℂ × ℝ) :=
    ((ℝ ∙ (P.symm p - 0))ᗮ.reflection : WithLp 2 (ℂ × ℝ) →L[ℝ] WithLp 2 (ℂ × ℝ))
  let c (p : ℂ × ℝ) : ℝ := (1 / dist (P.symm p) 0) ^ 2
  have hnorm (p : ℂ × ℝ) : ‖P.symm p‖ ^ 2 = moebiusDenom slInversion p := by
    have h₁ : ‖P.symm p‖ ^ 2 = ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 :=
      WithLp.prod_norm_sq_eq_of_L2 _
    rw [h₁]
    simp [moebiusDenom, slInversion, normSq_eq_norm_sq]
  have hc (p : ℂ × ℝ) : c p = (moebiusDenom slInversion p)⁻¹ := by
    simp only [c, dist_zero_right, one_div, inv_pow, hnorm]
  have hm : moebius slInversion = fun p ↦ ρ (P (inversion 0 1 (P.symm p))) := by
    funext p
    have h₁ : inversion 0 1 (P.symm p) = c p • P.symm p := by
      simp [inversion, c]
    have h₂ : P (c p • P.symm p) = c p • p := by
      rw [map_smul, P.apply_symm_apply]
    rw [h₁, h₂, hc]
    refine Prod.ext ?_ ?_
    · simp [moebius, slInversion, ρ, div_eq_inv_mul]
    · simp [moebius, ρ, div_eq_inv_mul]
  refine hyperbolicVolume_smul_of_hasFDerivAt _
    (f' := fun p ↦ ρ ∘L (P : WithLp 2 (ℂ × ℝ) →L[ℝ] ℂ × ℝ) ∘L (c p • R p) ∘L
      (P.symm : ℂ × ℝ →L[ℝ] WithLp 2 (ℂ × ℝ))) (fun p hp ↦ ?_) (fun p hp ↦ ?_) hA
  · have hne : P.symm p ≠ 0 := fun h ↦ hp.ne' <| by
      have h₁ : p = 0 := P.symm.map_eq_zero_iff.mp h
      rw [h₁]
      rfl
    rw [hm]
    exact ρ.hasFDerivAt.comp p (P.toContinuousLinearMap.hasFDerivAt.comp p
      ((hasFDerivAt_inversion hne).comp p P.symm.toContinuousLinearMap.hasFDerivAt))
  · have hρ : |LinearMap.det (ρ : (ℂ × ℝ) →ₗ[ℝ] ℂ × ℝ)| = 1 :=
      abs_det_eq_one_of_comp_self <| by
        ext <;> simp [ρ]
    have hR : |LinearMap.det (R p : WithLp 2 (ℂ × ℝ) →ₗ[ℝ] WithLp 2 (ℂ × ℝ))| = 1 :=
      abs_det_reflection _
    have hf : Module.finrank ℝ (WithLp 2 (ℂ × ℝ)) = 3 := by
      rw [P.toLinearEquiv.finrank_eq, Module.finrank_prod, Complex.finrank_real_complex,
        Module.finrank_self]
    have hdet : LinearMap.det ((ρ ∘L (P : WithLp 2 (ℂ × ℝ) →L[ℝ] ℂ × ℝ) ∘L (c p • R p) ∘L
        (P.symm : ℂ × ℝ →L[ℝ] WithLp 2 (ℂ × ℝ)) : (ℂ × ℝ) →L[ℝ] ℂ × ℝ) : (ℂ × ℝ) →ₗ[ℝ] ℂ × ℝ) =
        LinearMap.det (ρ : (ℂ × ℝ) →ₗ[ℝ] ℂ × ℝ) * (c p ^ 3 *
          LinearMap.det (R p : WithLp 2 (ℂ × ℝ) →ₗ[ℝ] WithLp 2 (ℂ × ℝ))) := by
      rw [← hf, ← LinearMap.det_smul, ← LinearMap.det_conj _ P.toLinearEquiv, ← LinearMap.det_comp]
      rfl
    have hc₀ : 0 ≤ c p := by
      positivity
    rw [ContinuousLinearMap.det, hdet, abs_mul, abs_mul, hρ, hR, one_mul, mul_one,
      abs_of_nonneg (pow_nonneg hc₀ 3), hc]

/-- **The hyperbolic volume is invariant under `SL(2, ℂ)`**: `vol(g A) = vol(A)` for `g ∈ SL(2, ℂ)`
and a measurable subset `A` of `ℋ₃`. -/
lemma hyperbolicVolume_smul (hA : MeasurableSet A) :
    hyperbolicVolume (g • A) = hyperbolicVolume A := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := g.fin_two_mul_sub_mul_eq_one
  by_cases hc : g 1 0 = 0
  · have ha : g 0 0 ≠ 0 := fun h ↦ by simp [h, hc] at hdet
    have hd : g 1 1 = (g 0 0)⁻¹ := by
      rw [hc, mul_zero, sub_zero] at hdet
      exact eq_inv_of_mul_eq_one_right hdet
    have hg : g = slTranslation (g 0 1 * g 0 0) * slDiagonal (g 0 0) ha := by
      refine Subtype.ext ?_
      rw [SpecialLinearGroup.coe_mul]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [slTranslation, slDiagonal, hc, hd, ha]
    rw [hg, mul_smul, hyperbolicVolume_slTranslation_smul _ (hA.const_smul _),
      hyperbolicVolume_slDiagonal_smul _ _ hA]
  · have hg : g = slTranslation (g 0 0 / g 1 0) * (slDiagonal (g 1 0)⁻¹ (inv_ne_zero hc) *
        (slInversion * slTranslation (g 1 1 / g 1 0))) := by
      refine Subtype.ext ?_
      rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
        SpecialLinearGroup.coe_mul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [slTranslation, slDiagonal, slInversion, hc]
      · field_simp
        linear_combination -hdet
      · field_simp
    rw [hg, mul_smul, mul_smul, mul_smul,
      hyperbolicVolume_slTranslation_smul _ (((hA.const_smul _).const_smul _).const_smul _),
      hyperbolicVolume_slDiagonal_smul _ _ ((hA.const_smul _).const_smul _),
      hyperbolicVolume_slInversion_smul (hA.const_smul _), hyperbolicVolume_slTranslation_smul _ hA]

instance : SMulInvariantMeasure SL(2, ℂ) HyperbolicThreeSpace hyperbolicVolume where
  measure_preimage_smul g A hA := by
    rw [preimage_smul]
    exact hyperbolicVolume_smul _ hA

end HyperbolicThreeSpace
