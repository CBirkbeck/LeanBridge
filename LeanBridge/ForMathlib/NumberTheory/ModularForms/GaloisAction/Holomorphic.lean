import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# Quotients of holomorphic functions on the upper half-plane

A quotient `A / D` of holomorphic functions on the upper half-plane that is locally bounded is
holomorphic, by Riemann's removable singularity theorem. This is how the conjugate of a modular form
by an automorphism of `ℂ` is shown to be holomorphic.

## Main results

* `TauCeti.GaloisAction.exists_mdifferentiable_mul_eq`: if `A` and `D ≠ 0` are holomorphic on the
  upper half-plane and `A / D` is bounded by a continuous function off the zeros of `D`, then
  `A = D * F` for a holomorphic function `F`.
-/

open UpperHalfPlane Filter

open scoped Topology Manifold

namespace TauCeti.GaloisAction

variable {A D a b : ℍ → ℂ} {ι : Type*} {z : ℂ}

lemma eventually_comp_ofComplex_ne_zero (hD : MDiff D) (hD0 : D ≠ 0) (hz : 0 < z.im) :
    ∀ᶠ w in 𝓝[≠] z, D (ofComplex w) ≠ 0 := by
  have h : ∀ᶠ w in 𝓝[≠] z, ¬(0 < w.im ∧ (D ∘ ofComplex) w = 0) :=
    not_frequently.mp <| accPt_iff_frequently_nhdsNE.not.mp <|
      UpperHalfPlane.not_accPt_zeros_comp_ofComplex hD hD0 hz
  filter_upwards [h, nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds hz)] with w hw hwz hw₀
  exact hw ⟨hwz, hw₀⟩

lemma exists_forall_ne_zero [Finite ι] {g : ι → ℍ → ℂ} (hg : ∀ i, MDiff (g i))
    (hg0 : ∀ i, g i ≠ 0) : ∃ τ, ∀ i, g i τ ≠ 0 := by
  have h : ∀ᶠ w in 𝓝[≠] Complex.I, ∀ i, g i (ofComplex w) ≠ 0 :=
    eventually_all.mpr fun i ↦ eventually_comp_ofComplex_ne_zero (hg i) (hg0 i) (by simp)
  rcases h.exists with ⟨w, hw⟩
  exact ⟨ofComplex w, hw⟩

lemma eq_of_mul_eq_mul (hD : MDiff D) (hD0 : D ≠ 0) (ha : MDiff a) (hb : MDiff b)
    (h : ∀ τ, D τ * a τ = D τ * b τ) : a = b :=
  sub_eq_zero.mp <| ((mul_eq_zero_iff hD (ha.sub hb)).mp <| funext fun τ ↦
    mul_sub (D τ) (a τ) (b τ) |>.trans <| sub_eq_zero.mpr (h τ)).resolve_left hD0

/-- **A locally bounded quotient of holomorphic functions is holomorphic**: if `A` and `D ≠ 0` are
holomorphic on the upper half-plane, and `A / D` is bounded by a continuous function off the zeros
of `D`, then `A = D * F` for a holomorphic function `F`. -/
lemma exists_mdifferentiable_mul_eq (hA : MDiff A) (hD : MDiff D) (hD0 : D ≠ 0) {B : ℍ → ℝ}
    (hB : Continuous B) (hbd : ∀ τ, D τ ≠ 0 → ‖A τ / D τ‖ ≤ B τ) :
    ∃ F : ℍ → ℂ, MDiff F ∧ ∀ τ, D τ * F τ = A τ := by
  let f₀ : ℂ → ℂ := fun z ↦ A (ofComplex z) / D (ofComplex z)
  let F₀ : ℂ → ℂ := fun z ↦ limUnder (𝓝[≠] z) f₀
  have hAc : DifferentiableOn ℂ (A ∘ ofComplex) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hA
  have hDc : DifferentiableOn ℂ (D ∘ ofComplex) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hD
  have hfat {z : ℂ} (hz : 0 < z.im) (hz' : D (ofComplex z) ≠ 0) : DifferentiableAt ℂ f₀ z :=
    ((hAc z hz).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hz)).div
      ((hDc z hz).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hz)) hz'
  have hval {z : ℂ} (hz : 0 < z.im) (hz' : D (ofComplex z) ≠ 0) : F₀ z = f₀ z :=
    ((hfat hz hz').continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
  have hdiff {z : ℂ} (hz : 0 < z.im) : DifferentiableAt ℂ F₀ z := by
    have hcont : ContinuousAt (B ∘ ofComplex) z :=
      hB.continuousAt.comp (mdifferentiableAt_ofComplex hz).continuousAt
    let s : Set ℂ :=
      {w | w ≠ z → 0 < w.im ∧ D (ofComplex w) ≠ 0 ∧ B (ofComplex w) < B (ofComplex z) + 1}
    have hs : s ∈ 𝓝 z := by
      have hev : ∀ᶠ w in 𝓝 z, w ∈ ({z}ᶜ : Set ℂ) → D (ofComplex w) ≠ 0 :=
        eventually_nhdsWithin_iff.mp (eventually_comp_ofComplex_ne_zero hD hD0 hz)
      filter_upwards [hev, isOpen_upperHalfPlaneSet.mem_nhds hz,
        hcont.eventually_lt_const (lt_add_one _)] with w hw₁ hw₂ hw₃ hwz
      exact ⟨hw₂, hw₁ hwz, hw₃⟩
    have hd : DifferentiableOn ℂ f₀ (s \ {z}) := fun w hw ↦
      (hfat (hw.1 hw.2).1 (hw.1 hw.2).2.1).differentiableWithinAt
    have hb : BddAbove (norm ∘ f₀ '' (s \ {z})) := by
      refine ⟨B (ofComplex z) + 1, ?_⟩
      rintro _ ⟨w, hw, rfl⟩
      exact (hbd _ (hw.1 hw.2).2.1).trans (hw.1 hw.2).2.2.le
    have hup : DifferentiableOn ℂ (Function.update f₀ z (limUnder (𝓝[≠] z) f₀)) s :=
      Complex.differentiableOn_update_limUnder_of_bddAbove hs hd hb
    refine (hup.differentiableAt hs).congr_of_eventuallyEq ?_
    filter_upwards [hs] with w hw
    rcases eq_or_ne w z with rfl | hwz
    · simp [F₀]
    · rw [Function.update_of_ne hwz]
      exact hval (hw hwz).1 (hw hwz).2.1
  have hmul {z : ℂ} (hz : 0 < z.im) : D (ofComplex z) * F₀ z = A (ofComplex z) := by
    have hev : (fun w ↦ D (ofComplex w) * F₀ w) =ᶠ[𝓝[≠] z] A ∘ ofComplex := by
      filter_upwards [eventually_comp_ofComplex_ne_zero hD hD0 hz,
        nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds hz)] with w hw₁ hw₂
      rw [hval hw₂ hw₁, mul_div_cancel₀ _ hw₁]
      rfl
    have hl : Tendsto (fun w ↦ D (ofComplex w) * F₀ w) (𝓝[≠] z) (𝓝 (D (ofComplex z) * F₀ z)) :=
      (((UpperHalfPlane.analyticAt_comp_ofComplex hD hz).continuousAt.mul
        (hdiff hz).continuousAt).tendsto).mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (hl.congr' hev)
      ((UpperHalfPlane.analyticAt_comp_ofComplex hA hz).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
  refine ⟨fun τ ↦ F₀ τ, UpperHalfPlane.mdifferentiable_iff.mpr fun z hz ↦ ?_, fun τ ↦ ?_⟩
  · refine (hdiff hz).differentiableWithinAt.congr (fun w hw ↦ ?_) ?_
    · simp [ofComplex_apply_of_im_pos hw]
    · simp [ofComplex_apply_of_im_pos hz]
  · simpa using hmul τ.im_pos

end TauCeti.GaloisAction
