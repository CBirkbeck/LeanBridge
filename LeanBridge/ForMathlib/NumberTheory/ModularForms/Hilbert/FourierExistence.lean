import LeanBridge.ForMathlib.Analysis.Fourier.TubeFourierSeries
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.FourierExpansion
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Existence of Fourier expansions of Hilbert modular forms

Let `F` be a totally real number field, `𝔟` an invertible fractional ideal and `φ : ℍⁿ → ℂ` a
holomorphic function invariant under the translations `z ↦ z + b`, `b ∈ 𝔟⁻¹`, such as a component of
a Hilbert modular form (LMFDB `mf.hilbert`), whose translations in `Γ₀(𝔑)_𝔟` are those by `𝔟⁻¹`.
Then `φ` is the sum `φ(z) = ∑_ν a(ν) e^{2πi Tr(νz)}` of a Fourier series over the trace dual
`(𝔟⁻¹)^∨ = 𝔟𝔡⁻¹` (LMFDB `mf.hilbert.q_expansion`), which converges absolutely.

Let `(e_j)` be a `ℤ`-basis of `𝔟⁻¹`. The vectors `(w(e_j))_w`, `w` running over the real places,
form an `ℝ`-basis of `ℝⁿ` (`NumberField.mixedEmbedding.fractionalIdealLatticeBasis`), so
`x ↦ (∑_j x_j w(e_j))_w` maps `ℂⁿ` onto `ℂⁿ`, the tube over the open convex cone
`{y : ∑_j y_j w(e_j) > 0 for all w}` onto `ℍⁿ`, and `ℤⁿ` onto the translations by `𝔟⁻¹`. The
function `x ↦ φ(∑_j x_j e_j)` is holomorphic on that tube and `ℤⁿ`-periodic, so it is the sum of its
Fourier series `∑_k c(k) e^{2πi k·x}` (`hasSum_tubeFourierCoeff_mul_cexp`). Every frequency
`k ∈ ℤⁿ` is `(Tr(ν e_j))_j` for exactly one `ν ∈ (𝔟⁻¹)^∨`, namely `ν = ∑_j k_j e_j^∨` for the dual
basis `(e_j^∨)` of `(e_j)` under the trace form, and then `k·x = Tr(νz)`.

## Main definitions

* `HilbertModularForm.IsTranslationInvariant`: invariance under the translations by `𝔟⁻¹`.

## Main results

* `HilbertModularForm.hasHilbertFourierExpansion_fourierCoeff` (LMFDB `mf.hilbert.q_expansion`): a
  holomorphic function on `ℍⁿ` invariant under the translations by `𝔟⁻¹` is the sum of its Fourier
  series over `(𝔟⁻¹)^∨`.
-/

open Complex Module NumberField InfinitePlace mixedEmbedding

open scoped nonZeroDivisors Real UpperHalfPlane

namespace HilbertModularForm

variable {F : Type*} [Field F] [NumberField F] (𝔟 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
  {φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ}

variable (φ) in
/-- A function `φ : ℍⁿ → ℂ` is **invariant under the translations by `𝔟⁻¹`**: `φ(z + b) = φ(z)` for
every `b ∈ 𝔟⁻¹`, the translate `z + b` being `(z_w + w(b))_w`, `w` running over the real places. -/
def IsTranslationInvariant : Prop :=
  ∀ b ∈ (↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F), ∀ z z' : {w : InfinitePlace F // w.IsReal} → ℍ,
    (∀ w, (z' w : ℂ) = z w + embedding_of_isReal w.2 b) → φ z' = φ z

/-- The index set of the `ℤ`-basis `basisOfFractionalIdeal F 𝔟⁻¹` of `𝔟⁻¹`. -/
private abbrev BasisIndex : Type _ :=
  Free.ChooseBasisIndex ℤ (↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F)

variable (m : BasisIndex 𝔟 → ℤ) (ν : fourierDual 𝔟) (z : {w : InfinitePlace F // w.IsReal} → ℂ)
  (j : BasisIndex 𝔟) (x : BasisIndex 𝔟 → ℂ) (w : {w : InfinitePlace F // w.IsReal})

/-- The point `(∑_j x_j w(e_j))_w` of `ℂⁿ`, for `x ∈ ℂ^ι` and the `ℤ`-basis `(e_j)` of `𝔟⁻¹`. -/
private noncomputable def latticePoint : ℂ :=
  ∑ j, x j * (embedding_of_isReal w.2 (basisOfFractionalIdeal F 𝔟⁻¹ j) : ℂ)

/-- The open convex cone `{y : ∑_j y_j w(e_j) > 0 for all w}` of `ℝ^ι`, whose tube is mapped onto
`ℍⁿ` by `latticePoint`. -/
private def latticeCone : Set (BasisIndex 𝔟 → ℝ) :=
  ⋂ w : {w : InfinitePlace F // w.IsReal},
    {y | 0 < ∑ j, y j * embedding_of_isReal w.2 (basisOfFractionalIdeal F 𝔟⁻¹ j)}

variable (φ) in
open scoped Classical in
/-- The function `x ↦ φ(∑_j x_j e_j)` on `ℂ^ι`, extended by `0` outside the tube over
`latticeCone 𝔟`. -/
private noncomputable def latticeLift : ℂ :=
  if ∀ w, 0 < (latticePoint 𝔟 x w).im then
    φ fun w ↦ UpperHalfPlane.ofComplex (latticePoint 𝔟 x w)
  else 0

/-- The coordinates `x ∈ ℂ^ι` of `z ∈ ℂⁿ`, with `∑_j x_j w(e_j) = z_w` for every real place `w`. -/
private noncomputable def latticeCoord : ℂ :=
  (fractionalIdealLatticeBasis F 𝔟⁻¹).repr (fun w ↦ (z w).re, 0) j +
    (fractionalIdealLatticeBasis F 𝔟⁻¹).repr (fun w ↦ (z w).im, 0) j * I

private lemma im_latticePoint : (latticePoint 𝔟 x w).im =
    ∑ j, (x j).im * embedding_of_isReal w.2 (basisOfFractionalIdeal F 𝔟⁻¹ j) := by
  simp only [latticePoint, im_sum, im_mul_ofReal]

variable {x} in
private lemma mem_tubeOver_latticeCone :
    x ∈ tubeOver (latticeCone 𝔟) ↔ ∀ w, 0 < (latticePoint 𝔟 x w).im := by
  simp [mem_tubeOver, latticeCone, im_latticePoint]

private lemma isOpen_latticeCone : IsOpen (latticeCone 𝔟) :=
  isOpen_iInter_of_finite fun _ ↦ isOpen_lt continuous_const (by fun_prop)

private lemma convex_latticeCone : Convex ℝ (latticeCone 𝔟) :=
  convex_iInter fun _ ↦ convex_halfSpace_gt ⟨fun _ _ ↦ by simp [add_mul, Finset.sum_add_distrib],
    fun _ _ ↦ by simp [mul_assoc, Finset.mul_sum]⟩ 0

private lemma sum_repr_mul_embedding (v : mixedSpace F) :
    ∑ j, (fractionalIdealLatticeBasis F 𝔟⁻¹).repr v j *
      embedding_of_isReal w.2 (basisOfFractionalIdeal F 𝔟⁻¹ j) = v.1 w := by
  conv_rhs => rw [← (fractionalIdealLatticeBasis F 𝔟⁻¹).sum_repr v]
  simp [Prod.fst_sum]

private lemma latticePoint_latticeCoord : latticePoint 𝔟 (latticeCoord 𝔟 z) = z := by
  funext w
  have h (v : mixedSpace F) : ∑ j, ((fractionalIdealLatticeBasis F 𝔟⁻¹).repr v j : ℂ) *
      (embedding_of_isReal w.2 (basisOfFractionalIdeal F 𝔟⁻¹ j) : ℂ) = v.1 w := by
    exact_mod_cast congrArg ((↑) : ℝ → ℂ) (sum_repr_mul_embedding 𝔟 w v)
  simp only [latticePoint, latticeCoord, add_mul, Finset.sum_add_distrib, mul_right_comm _ I,
    ← Finset.sum_mul, h]
  exact re_add_im (z w)

private lemma differentiable_latticePoint : Differentiable ℂ (latticePoint 𝔟) :=
  differentiable_pi.mpr fun w ↦ by
    unfold latticePoint
    fun_prop

open scoped Classical in
private lemma differentiableOn_latticeLift (hφ : IsHolomorphic φ) :
    DifferentiableOn ℂ (latticeLift 𝔟 φ) (tubeOver (latticeCone 𝔟)) := by
  rw [IsHolomorphic] at hφ
  refine (hφ.comp (differentiable_latticePoint 𝔟).differentiableOn fun _ hx ↦
    (mem_tubeOver_latticeCone 𝔟).mp hx).congr fun _ hx ↦ ?_
  exact ite_eq_left ((mem_tubeOver_latticeCone 𝔟).mp hx)

private lemma sum_intCast_smul_mem :
    ∑ j, m j • basisOfFractionalIdeal F 𝔟⁻¹ j ∈ (↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F) :=
  (mem_span_basisOfFractionalIdeal F).mp <|
    Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ (m j) (Submodule.subset_span ⟨j, rfl⟩)

private lemma latticeLift_add_intCast (hp : IsTranslationInvariant 𝔟 φ) :
    latticeLift 𝔟 φ (fun j ↦ x j + m j) = latticeLift 𝔟 φ x := by
  have hpt (w : {w : InfinitePlace F // w.IsReal}) : latticePoint 𝔟 (fun j ↦ x j + m j) w =
      latticePoint 𝔟 x w + embedding_of_isReal w.2 (∑ j, m j • basisOfFractionalIdeal F 𝔟⁻¹ j) := by
    simp [latticePoint, add_mul, Finset.sum_add_distrib]
  have him (w : {w : InfinitePlace F // w.IsReal}) :
      (latticePoint 𝔟 (fun j ↦ x j + m j) w).im = (latticePoint 𝔟 x w).im := by
    rw [hpt, add_im, ofReal_im, add_zero]
  by_cases h : ∀ w, 0 < (latticePoint 𝔟 x w).im
  · have h' (w : {w : InfinitePlace F // w.IsReal}) :
        0 < (latticePoint 𝔟 (fun j ↦ x j + m j) w).im :=
      (him w).symm ▸ h w
    rw [latticeLift, latticeLift, ite_eq_left h', ite_eq_left h]
    refine hp _ (sum_intCast_smul_mem 𝔟 m) _ _ fun w ↦ ?_
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (h' w),
      UpperHalfPlane.ofComplex_apply_of_im_pos (h w)]
    exact hpt w
  · rw [latticeLift, latticeLift, ite_eq_right (by simpa [him] using h), ite_eq_right h]

private lemma latticeLift_latticeCoord (τ : {w : InfinitePlace F // w.IsReal} → ℍ) :
    latticeLift 𝔟 φ (latticeCoord 𝔟 fun w ↦ (τ w : ℂ)) = φ τ := by
  have h : ∀ w, 0 < (τ w : ℂ).im := fun w ↦ (τ w).im_pos
  rw [latticeLift, latticePoint_latticeCoord, ite_eq_left h]
  simp

/-- The coordinates `(Tr(ν e_j))_j ∈ ℤ^ι` of `ν ∈ (𝔟⁻¹)^∨`. -/
private noncomputable def dualCoord : ℤ :=
  (exists_intCast_eq_trace 𝔟 ν j).choose

private lemma intCast_dualCoord :
    (dualCoord 𝔟 ν j : ℚ) = Algebra.trace ℚ F (ν * basisOfFractionalIdeal F 𝔟⁻¹ j) :=
  (exists_intCast_eq_trace 𝔟 ν j).choose_spec

open scoped Classical in
private lemma trace_sum_smul_traceDual_mul (k : BasisIndex 𝔟 → ℚ) (i : BasisIndex 𝔟) :
    Algebra.trace ℚ F ((∑ j, k j • (basisOfFractionalIdeal F 𝔟⁻¹).traceDual j) *
      basisOfFractionalIdeal F 𝔟⁻¹ i) = k i := by
  simp [Finset.sum_mul]

open scoped Classical in
private lemma sum_smul_traceDual_mem (k : BasisIndex 𝔟 → ℤ) :
    ∑ j, (k j : ℚ) • (basisOfFractionalIdeal F 𝔟⁻¹).traceDual j ∈ fourierDual 𝔟 := by
  have h := Submodule.traceDual_span_of_basis ℤ
    ((↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) (basisOfFractionalIdeal F 𝔟⁻¹)
    (Submodule.ext fun _ ↦ (mem_span_basisOfFractionalIdeal F).symm)
  rw [← FractionalIdeal.mem_coe, fourierDual, FractionalIdeal.coe_dual (A := ℤ) (K := ℚ)
    (Units.ne_zero _), ← Submodule.restrictScalars_mem ℤ, h]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ (k j) (Submodule.subset_span ⟨j, rfl⟩)

open scoped Classical in
/-- The bijection `ν ↦ (Tr(ν e_j))_j` from `(𝔟⁻¹)^∨` to `ℤ^ι`, whose inverse is `k ↦ ∑_j k_j e_j^∨`
for the dual basis `(e_j^∨)` of `(e_j)` under the trace form. -/
private noncomputable def dualEquiv : fourierDual 𝔟 ≃ (BasisIndex 𝔟 → ℤ) where
  toFun := dualCoord 𝔟
  invFun k := ⟨∑ j, (k j : ℚ) • (basisOfFractionalIdeal F 𝔟⁻¹).traceDual j,
    sum_smul_traceDual_mem 𝔟 k⟩
  left_inv ν := Subtype.ext <| by
    conv_rhs => rw [← (basisOfFractionalIdeal F 𝔟⁻¹).traceDual.sum_repr (ν : F)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Basis.traceDual_repr_apply, Algebra.traceForm_apply, intCast_dualCoord]
  right_inv k := funext fun j ↦ Int.cast_injective (α := ℚ) <| by
    rw [intCast_dualCoord, trace_sum_smul_traceDual_mul]

variable [IsTotallyReal F]

open scoped Classical in
private lemma sum_dualEquiv_mul : ∑ j, (dualEquiv 𝔟 ν j : ℂ) * x j =
    ∑ w, (embedding_of_isReal w.2 (ν : F) : ℂ) * latticePoint 𝔟 x w := by
  have h (j : BasisIndex 𝔟) : (dualEquiv 𝔟 ν j : ℂ) = ∑ w : {w : InfinitePlace F // w.IsReal},
      (embedding_of_isReal w.2 (ν : F) : ℂ) *
          embedding_of_isReal w.2 (basisOfFractionalIdeal F 𝔟⁻¹ j) := by
    rw [← Rat.cast_intCast, dualEquiv, Equiv.coe_fn_mk, intCast_dualCoord, coe_trace_eq_sum]
    simp only [map_mul, ofReal_mul]
  simp only [h, latticePoint, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring1

private lemma exists_hasHilbertFourierExpansion (hφ : IsHolomorphic φ)
    (hp : IsTranslationInvariant 𝔟 φ) : ∃ a, HasHilbertFourierExpansion 𝔟 φ a := by
  let y₀ : BasisIndex 𝔟 → ℝ := (fractionalIdealLatticeBasis F 𝔟⁻¹).repr (fun _ ↦ 1, 0)
  have hy₀ : y₀ ∈ latticeCone 𝔟 := Set.mem_iInter.mpr fun w ↦ by
    rw [Set.mem_ofPred_eq, sum_repr_mul_embedding]
    exact one_pos
  refine ⟨fun ν ↦ tubeFourierCoeff (latticeLift 𝔟 φ) y₀ (dualEquiv 𝔟 ν), fun z ↦ ?_⟩
  have hz : latticeCoord 𝔟 (fun w ↦ (z w : ℂ)) ∈ tubeOver (latticeCone 𝔟) :=
    (mem_tubeOver_latticeCone 𝔟).mpr fun w ↦ by
      rw [latticePoint_latticeCoord]
      exact (z w).im_pos
  have h : HasSum (fun k ↦ tubeFourierCoeff (latticeLift 𝔟 φ) y₀ k *
      cexp (2 * π * I * ∑ i, (k i : ℂ) * latticeCoord 𝔟 (fun w ↦ (z w : ℂ)) i))
      (latticeLift 𝔟 φ (latticeCoord 𝔟 fun w ↦ (z w : ℂ))) :=
    hasSum_tubeFourierCoeff_mul_cexp (isOpen_latticeCone 𝔟) (convex_latticeCone 𝔟)
      (differentiableOn_latticeLift 𝔟 hφ) (fun m x ↦ latticeLift_add_intCast 𝔟 m x hp) hy₀ hz
  rw [latticeLift_latticeCoord] at h
  refine ((dualEquiv 𝔟).hasSum_iff.mpr h).congr_fun fun ν ↦ ?_
  rw [Function.comp_apply, fourierExp, sum_dualEquiv_mul, latticePoint_latticeCoord]

/-- **Holomorphic functions on `ℍⁿ` invariant under the translations by `𝔟⁻¹` are the sums of their
Fourier series** (LMFDB `mf.hilbert.q_expansion`): for `F` totally real and `φ : ℍⁿ → ℂ`
holomorphic with `φ(z + b) = φ(z)` for `b ∈ 𝔟⁻¹`,
`φ(z) = ∑_{ν ∈ (𝔟⁻¹)^∨} a(ν) e^{2πi Tr(νz)}` with `a = fourierCoeff 𝔟 φ`. -/
lemma hasHilbertFourierExpansion_fourierCoeff (hφ : IsHolomorphic φ)
    (hp : IsTranslationInvariant 𝔟 φ) : HasHilbertFourierExpansion 𝔟 φ (fourierCoeff 𝔟 φ) := by
  rcases exists_hasHilbertFourierExpansion 𝔟 hφ hp with ⟨a, ha⟩
  rwa [ha.fourierCoeff_eq]

end HilbertModularForm
