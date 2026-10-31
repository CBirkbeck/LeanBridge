import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ThetaConstant

/-!
# Algebraic operations on holomorphic functions on the Siegel upper half-space

A function `f : ℋ_g → ℂ` is holomorphic (`SiegelUpperHalfSpace.IsHolomorphic`) exactly when its
extension `Z ↦ f((Z + Zᵀ)/2)` is complex differentiable on the open set of square matrices whose
symmetrisation lies in `ℋ_g`. On that set the extension of a product, difference or power is the
product, difference or power of the extensions, so the holomorphic functions are closed under
these operations, and under the doubling `Ω ↦ 2Ω`, which the extension turns into `Z ↦ 2Z`. They
make the polynomials in theta constants, the generators of the rings of Siegel modular forms of the
knowls `mf.siegel.family.gamma0_2` and `mf.siegel.family.gamma0_4_psi_4`, holomorphic.

## Main results

* `SiegelUpperHalfSpace.isHolomorphic_iff_differentiableOn`: a scalar function is holomorphic
  exactly when its extension is complex differentiable.
-/

open Complex Matrix

namespace SiegelUpperHalfSpace

variable {l : Type*} {Z : l → l → ℂ}

lemma extend_of_mem (u : SiegelUpperHalfSpace l → ℂ) (hZ : Z ∈ symmetrizePreimage l) :
    extend u Z = u ⟨symmetrize Z, transpose_symmetrize Z, hZ⟩ :=
  dite_eq_left hZ

variable (Z) in
lemma symmetrize_two_smul : symmetrize ((2 : ℂ) • Z) = (2 : ℂ) • symmetrize Z := by
  ext i j
  simp [symmetrize]
  ring1

variable [Fintype l] {f g : SiegelUpperHalfSpace l → ℂ}

/-- **A scalar function on `ℋ_g` is holomorphic exactly when its extension
`Z ↦ f((Z + Zᵀ)/2)` is complex differentiable** on the square matrices whose symmetrisation lies in
`ℋ_g`: every linear form on `ℂ` is a multiple of the identity. -/
lemma isHolomorphic_iff_differentiableOn :
    IsHolomorphic f ↔ DifferentiableOn ℂ (extend f) (symmetrizePreimage l) := by
  refine ⟨fun h ↦ h LinearMap.id, fun h φ ↦ (h.const_mul (φ 1)).congr fun Z hZ ↦ ?_⟩
  rw [extend_of_mem _ hZ, extend_of_mem _ hZ, Function.comp_apply]
  simpa [mul_comm] using φ.map_smul (f ⟨symmetrize Z, transpose_symmetrize Z, hZ⟩) 1

lemma IsHolomorphic.mul (hf : IsHolomorphic f) (hg : IsHolomorphic g) : IsHolomorphic (f * g) := by
  rw [isHolomorphic_iff_differentiableOn] at hf hg ⊢
  exact (hf.mul hg).congr fun Z hZ ↦ by simp only [Pi.mul_apply, extend_of_mem _ hZ]

lemma IsHolomorphic.sub (hf : IsHolomorphic f) (hg : IsHolomorphic g) : IsHolomorphic (f - g) := by
  rw [isHolomorphic_iff_differentiableOn] at hf hg ⊢
  exact (hf.sub hg).congr fun Z hZ ↦ by simp only [Pi.sub_apply, extend_of_mem _ hZ]

lemma IsHolomorphic.pow (hf : IsHolomorphic f) (n : ℕ) : IsHolomorphic (f ^ n) := by
  rw [isHolomorphic_iff_differentiableOn] at hf ⊢
  exact (hf.pow n).congr fun Z hZ ↦ by simp only [Pi.pow_apply, extend_of_mem _ hZ]

lemma IsHolomorphic.div_const (hf : IsHolomorphic f) (c : ℂ) : IsHolomorphic fun Ω ↦ f Ω / c := by
  rw [isHolomorphic_iff_differentiableOn] at hf ⊢
  exact (hf.mul_const c⁻¹).congr fun Z hZ ↦ by simp only [extend_of_mem _ hZ, div_eq_mul_inv]

lemma IsHolomorphic.comp_double (hf : IsHolomorphic f) : IsHolomorphic (f ∘ double) := by
  rw [isHolomorphic_iff_differentiableOn] at hf ⊢
  have hmaps : Set.MapsTo (fun Z : l → l → ℂ ↦ (2 : ℂ) • Z) (symmetrizePreimage l)
      (symmetrizePreimage l) := fun Z hZ ↦ by
    have h : ((2 : ℂ) • symmetrize Z).map im = (2 : ℝ) • (symmetrize Z).map im := by
      ext i j
      simp
    have hZ' : ((symmetrize Z).map im).PosDef := hZ
    rw [symmetrizePreimage, Set.mem_ofPred_eq, symmetrize_two_smul, h]
    exact hZ'.smul two_pos
  refine (hf.comp ((differentiable_id.const_smul (2 : ℂ)).differentiableOn) hmaps).congr
    fun Z hZ ↦ ?_
  have hZ2 : (2 : ℂ) • Z ∈ symmetrizePreimage l := hmaps hZ
  rw [extend_of_mem _ hZ, Function.comp_apply, Function.comp_apply, Pi.smul_apply, id,
    extend_of_mem _ hZ2]
  congr 1
  ext1
  exact (symmetrize_two_smul Z).symm

end SiegelUpperHalfSpace
