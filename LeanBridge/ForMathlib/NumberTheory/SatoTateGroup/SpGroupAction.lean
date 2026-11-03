import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.AmbientHighestWeight
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.IrrepOfRepresentation
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.SpBridge

/-!
# The action of `USp(2g)` on the Lie submodules of the tensor powers

The ambient group `USp(2g)` of a Sato–Tate group of odd weight acts on the tensor powers of its
standard representation. By the correspondence between the stable subspaces of the group and of its
Lie algebra, the Lie submodules of the tensor powers are representations of `USp(2g)`, irreducible
when they are irreducible as Lie modules.

## Main definitions

* `SatoTateGroup.ambientToUsp`: the ambient group `USp(2g)`, with matrices indexed by
  `Fin g ⊕ Fin g`.
* `SatoTateGroup.spGroupRep`: the representation of `USp(2g)` on a Lie submodule of a tensor power.

## Main results

* `SatoTateGroup.isIrreducible_spGroupRep`: an irreducible Lie module is an irreducible
  representation.
* `SatoTateGroup.continuous_spGroupRep`: the matrix coefficients are continuous.
-/

open LieAlgebra LieModule Matrix Module TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

namespace SatoTateGroup

variable {w g : ℕ}

/-- The ambient group, with matrices indexed by `Fin g ⊕ Fin g`. -/
def ambientToUsp : ambientGroup w (g + g) →* Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ where
  toFun h := (h : Matrix (Fin (g + g)) (Fin (g + g)) ℂ).submatrix finSumFinEquiv finSumFinEquiv
  map_one' := submatrix_one_equiv _
  map_mul' _ _ := (submatrix_mul_equiv _ _ _ _ _).symm

lemma ambientToUsp_eq_submatrix (h : ambientGroup w (g + g)) : ambientToUsp h =
    (h : Matrix (Fin (g + g)) (Fin (g + g)) ℂ).submatrix finSumFinEquiv finSumFinEquiv :=
  rfl

lemma injective_ambientToUsp :
    Function.Injective (ambientToUsp : ambientGroup w (g + g) → Matrix _ _ ℂ) := fun _ _ hk ↦
  Subtype.ext <| Subtype.ext <|
    submatrix_injective finSumFinEquiv.surjective finSumFinEquiv.surjective hk

lemma continuous_ambientToUsp_apply (a b : Fin g ⊕ Fin g) :
    Continuous fun h : ambientGroup w (g + g) ↦ ambientToUsp h a b :=
  (continuous_subtype_val.comp continuous_subtype_val).matrix_elem _ _

lemma charpoly_ambientToUsp (h : ambientGroup w (g + g)) :
    (ambientToUsp h).charpoly = (h : Matrix (Fin (g + g)) (Fin (g + g)) ℂ).charpoly :=
  charpoly_reindex finSumFinEquiv.symm _

lemma J_eq_submatrix_satoTateForm :
    J (Fin g) ℂ = (satoTateForm (g + g)).submatrix finSumFinEquiv finSumFinEquiv := by
  rw [← reindex_J_eq_satoTateForm]
  ext a b
  simp

lemma isUsp_ambientToUsp (hw : Odd w) (h : ambientGroup w (g + g)) : IsUsp (ambientToUsp h) := by
  have h₁ : ((h : Matrix (Fin (g + g)) (Fin (g + g)) ℂ))ᵀ * satoTateForm (g + g) *
      (h : Matrix (Fin (g + g)) (Fin (g + g)) ℂ) = satoTateForm (g + g) := by
    have h₂ : h.1 ∈ ambientGroup w (g + g) := h.2
    rwa [mem_ambientGroup, ambientForm, ite_eq_left hw] at h₂
  refine ⟨?_, ?_⟩
  · have h₂ : star (h : Matrix (Fin (g + g)) (Fin (g + g)) ℂ) *
        (h : Matrix (Fin (g + g)) (Fin (g + g)) ℂ) = 1 := Unitary.star_mul_self_of_mem h.1.2
    have h₃ : (star (h : Matrix (Fin (g + g)) (Fin (g + g)) ℂ) *
        (h : Matrix (Fin (g + g)) (Fin (g + g)) ℂ)).submatrix finSumFinEquiv finSumFinEquiv =
          (1 : Matrix (Fin (g + g)) (Fin (g + g)) ℂ).submatrix finSumFinEquiv finSumFinEquiv :=
      congrArg (fun M ↦ M.submatrix finSumFinEquiv finSumFinEquiv) h₂
    rw [submatrix_one_equiv, ← submatrix_mul_equiv _ _ _ finSumFinEquiv] at h₃
    exact h₃
  · have h₃ : (((h : Matrix (Fin (g + g)) (Fin (g + g)) ℂ))ᵀ * satoTateForm (g + g) *
        (h : Matrix (Fin (g + g)) (Fin (g + g)) ℂ)).submatrix finSumFinEquiv finSumFinEquiv =
          (satoTateForm (g + g)).submatrix finSumFinEquiv finSumFinEquiv :=
      congrArg (fun M ↦ M.submatrix finSumFinEquiv finSumFinEquiv) h₁
    rw [← J_eq_submatrix_satoTateForm, ← submatrix_mul_equiv _ _ _ finSumFinEquiv,
      ← submatrix_mul_equiv _ _ _ finSumFinEquiv, ← J_eq_submatrix_satoTateForm] at h₃
    exact h₃

lemma isUnit_ambientForm_of_odd (hw : Odd w) : IsUnit (ambientForm w (g + g)) := by
  rw [ambientForm, ite_eq_left hw, ← reindex_J_eq_satoTateForm, Matrix.isUnit_iff_isUnit_det,
    det_reindex_self]
  exact isUnit_det_J _ _

lemma exists_ambientToUsp_eq (hw : Odd w) {A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ}
    (hA : IsUsp A) : ∃ h : ambientGroup w (g + g), ambientToUsp h = A := by
  let B : Matrix (Fin (g + g)) (Fin (g + g)) ℂ :=
    A.submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  have h₁ : star B * B = 1 := by
    have h₃ : (Aᴴ * A).submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
        (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ).submatrix finSumFinEquiv.symm
          finSumFinEquiv.symm :=
      congrArg (fun M ↦ M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
        hA.conjTranspose_mul_self
    rw [submatrix_one_equiv, ← submatrix_mul_equiv _ _ _ finSumFinEquiv.symm] at h₃
    exact h₃
  have h₂ : Bᵀ * satoTateForm (g + g) * B = satoTateForm (g + g) := by
    have h₃ : (Aᵀ * J (Fin g) ℂ * A).submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
        (J (Fin g) ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm :=
      congrArg (fun M ↦ M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
        hA.transpose_mul_J_mul
    rw [← submatrix_mul_equiv _ _ _ finSumFinEquiv.symm,
      ← submatrix_mul_equiv _ _ _ finSumFinEquiv.symm] at h₃
    have h₄ :
        (J (Fin g) ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = satoTateForm (g + g) :=
      reindex_J_eq_satoTateForm g
    rw [h₄] at h₃
    exact h₃
  refine ⟨⟨⟨B, mem_unitaryGroup_iff'.mpr h₁⟩, ?_⟩, ?_⟩
  · rw [mem_ambientGroup, ambientForm, ite_eq_left hw]
    exact h₂
  · ext a b
    simp [ambientToUsp_eq_submatrix, B]

variable {P : Type*} [Fintype P] [DecidableEq P]

lemma tensorRep_mulVec_mem_of_lieSubmodule (hw : Odd w)
    (U : LieSubmodule ℂ (Symplectic.sp (Fin g) ℂ) (SpTensor P g)) (h : ambientGroup w (g + g))
    {f : SpTensor P g} (hf : f ∈ U) : (tensorRep (ambientToUsp h) *ᵥ f : SpTensor P g) ∈ U :=
  (isUsp_ambientToUsp hw h).tensorRep_mulVec_mem U.toSubmodule
    (fun X hX _ hf ↦ U.lie_mem (x := ⟨X, hX⟩) hf) hf

variable (hw : Odd w) (U : LieSubmodule ℂ (Symplectic.sp (Fin g) ℂ) (SpTensor P g))

/-- The **representation of `USp(2g)` on a Lie submodule** of a tensor power of its standard
representation. -/
def spGroupRep : Representation ℂ (ambientGroup w (g + g)) U where
  toFun h :=
    { toFun := fun f ↦ ⟨tensorRep (ambientToUsp h) *ᵥ f.1,
        tensorRep_mulVec_mem_of_lieSubmodule hw U h f.2⟩
      map_add' := fun f f' ↦ Subtype.ext (mulVec_add _ f.1 f'.1)
      map_smul' := fun c f ↦ Subtype.ext (mulVec_smul _ c f.1) }
  map_one' := LinearMap.ext fun f ↦ Subtype.ext <|
    (congrArg (fun A ↦ tensorRep A *ᵥ f.1) (map_one ambientToUsp)).trans (tensorRep_one_mulVec f.1)
  map_mul' h k := LinearMap.ext fun f ↦ Subtype.ext <|
    (congrArg (fun A ↦ tensorRep A *ᵥ f.1) (map_mul ambientToUsp h k)).trans
      (tensorRep_mul_mulVec _ _ f.1)

lemma coe_spGroupRep (h : ambientGroup w (g + g)) (f : U) :
    (spGroupRep hw U h f : SpTensor P g) = tensorRep (ambientToUsp h) *ᵥ f.1 :=
  rfl

/-- **An irreducible Lie submodule of a tensor power is an irreducible representation of the
group.** -/
lemma isIrreducible_spGroupRep [LieModule.IsIrreducible ℂ (Symplectic.sp (Fin g) ℂ) U] :
    (spGroupRep hw U).IsIrreducible := by
  have : Nontrivial U := LieModule.nontrivial_of_isIrreducible (R := ℂ)
    (L := Symplectic.sp (Fin g) ℂ) (M := U)
  refine ⟨fun τ ↦ ?_⟩
  let W : Submodule ℂ ((P → Fin g ⊕ Fin g) → ℂ) := τ.toSubmodule.map U.toSubmodule.subtype
  have hW : ∀ A, IsUsp A → ∀ f ∈ W, tensorRep A *ᵥ f ∈ W := by
    rintro A hA _ ⟨u, hu, rfl⟩
    rcases exists_ambientToUsp_eq (w := w) hw hA with ⟨h, rfl⟩
    exact ⟨spGroupRep hw U h u, τ.apply_mem_toSubmodule h hu, rfl⟩
  let τL : LieSubmodule ℂ (Symplectic.sp (Fin g) ℂ) U :=
    { τ.toSubmodule with
      lie_mem := fun {x m} hm ↦ by
        rcases tensorAction_mulVec_mem_of_mem_sp W hW x.2 (Submodule.mem_map_of_mem hm) with
          ⟨u, hu, h₁⟩
        have h₂ : u = ⁅x, m⁆ := Subtype.ext h₁
        exact h₂ ▸ hu }
  rcases eq_bot_or_eq_top τL with h | h
  · refine Or.inl (Subrepresentation.toSubmodule_injective ?_)
    have h₁ : τ.toSubmodule = τL.toSubmodule := rfl
    rw [h₁, h]
    rfl
  · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    have h₁ : τ.toSubmodule = τL.toSubmodule := rfl
    rw [h₁, h]
    rfl

/-- **The matrix coefficients of the representation on a Lie submodule are continuous.** -/
lemma continuous_spGroupRep (v : U) (φ : Dual ℂ U) :
    Continuous fun h ↦ φ (spGroupRep hw U h v) := by
  rcases LinearMap.exists_extend φ with ⟨φ', hφ'⟩
  have h₁ (h : ambientGroup w (g + g)) : φ (spGroupRep hw U h v) =
      ∑ a, (tensorRep (ambientToUsp h) *ᵥ v.1) a * (φ' : ((P → Fin g ⊕ Fin g) → ℂ) →ₗ[ℂ] ℂ)
        fun b ↦ if a = b then 1 else 0 := by
    rw [← hφ', LinearMap.comp_apply, Submodule.subtype_apply, coe_spGroupRep]
    exact LinearMap.pi_apply_eq_sum_univ (φ' : ((P → Fin g ⊕ Fin g) → ℂ) →ₗ[ℂ] ℂ) _
  simp only [h₁]
  refine continuous_finsetSum _ fun a _ ↦ Continuous.mul ?_ continuous_const
  exact continuous_finsetSum _ fun b _ ↦ (continuous_finsetProd _ fun _ _ ↦
    continuous_ambientToUsp_apply _ _).mul continuous_const

end SatoTateGroup
