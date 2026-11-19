import Mathlib.FieldTheory.Galois.Basic

/-!
# The Galois correspondence for the subextensions of a subextension

Let `Ω / F` be a field extension and `N` an intermediate field that is finite and Galois over `F`,
with group `G = Gal(N / F)`. An intermediate field `E ⊆ N` of `Ω / F` has the group
`fixingSubgroup (N ≃ₐ[F] N) (↑⁻¹' E)`, the subgroup of `G` fixing the elements of `E`, and a
subgroup `J` of `G` has the fixed field `IntermediateField.lift (IntermediateField.fixedField J)`,
read in `Ω`. This file states the Galois correspondence of `N / F` in these terms: the degree
`[E : F]` is the index of the group of `E`, the group of the fixed field of `J` is `J`, and the
fixed field of `J` lies in an intermediate field `L ⊆ N` when `J` contains the group of `L`, and
contains `E` when `J` lies in the group of `E`. It also shows that an intermediate field inside a
finite, or separable, one is finite, or separable, over `F`, and that in a tower `N / E / F` with
`N / F` finite Galois the image of `Gal(N / E)` in `Gal(N / F)` has index `[E : F]`.
-/

namespace AlgEquiv

lemma index_range_restrictScalarsHom (F E N : Type*) [Field F] [Field E] [Field N] [Algebra F E]
    [Algebra E N] [Algebra F N] [IsScalarTower F E N] [FiniteDimensional F N] [IsGalois F N] :
    (restrictScalarsHom (S := E) F : (N ≃ₐ[E] N) →* N ≃ₐ[F] N).range.index =
      Module.finrank F E := by
  have hE : IsGalois E N := IsGalois.tower_top_of_isGalois F E N
  have hf : FiniteDimensional E N := .of_restrictScalars_finite F E N
  set φ : (N ≃ₐ[E] N) →* N ≃ₐ[F] N := restrictScalarsHom F
  have h₁ : φ.range.index * Nat.card φ.range = Nat.card (N ≃ₐ[F] N) := φ.range.index_mul_card
  have h₂ : Nat.card φ.range = Nat.card (N ≃ₐ[E] N) :=
    (Nat.card_congr (Equiv.ofInjective _ (restrictScalars_injective F))).symm
  rw [h₂, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    ← Module.finrank_mul_finrank F E N] at h₁
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h₁

end AlgEquiv

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {L E N : IntermediateField F Ω}

namespace IntermediateField

lemma finiteDimensional_of_le [FiniteDimensional F N] (h : E ≤ N) : FiniteDimensional F E :=
  (restrictAlgEquiv h).symm.toLinearEquiv.finiteDimensional

lemma isSeparable_of_le [Algebra.IsSeparable F N] (h : E ≤ N) : Algebra.IsSeparable F E :=
  .of_algHom F N (inclusion h)

end IntermediateField

variable [IsGalois F N] in
lemma finrank_eq_index_fixingSubgroup (h : E ≤ N) :
    Module.finrank F E = (fixingSubgroup (N ≃ₐ[F] N) (((↑) : N → Ω) ⁻¹' E)).index := by
  have hset :
      ((IntermediateField.restrict h : IntermediateField F N) : Set N) = ((↑) : N → Ω) ⁻¹' E :=
    Set.ext fun x ↦ IntermediateField.mem_restrict h x
  rw [(IntermediateField.restrictAlgEquiv h).toLinearEquiv.finrank_eq,
    IntermediateField.finrank_eq_fixingSubgroup_index, IntermediateField.fixingSubgroup, hset]

variable [FiniteDimensional F N] in
lemma fixingSubgroup_preimage_lift_fixedField (J : Subgroup (N ≃ₐ[F] N)) :
    fixingSubgroup (N ≃ₐ[F] N) (((↑) : N → Ω) ⁻¹'
      IntermediateField.lift (IntermediateField.fixedField J)) = J := by
  have hset : ((↑) : N → Ω) ⁻¹' IntermediateField.lift (IntermediateField.fixedField J) =
      (IntermediateField.fixedField J : Set N) :=
    Set.ext fun x ↦ IntermediateField.mem_lift x
  rw [hset]
  exact IntermediateField.fixingSubgroup_fixedField J

variable [FiniteDimensional F N] [IsGalois F N] in
lemma lift_fixedField_le (hLN : L ≤ N) {J : Subgroup (N ≃ₐ[F] N)}
    (hJ : fixingSubgroup (N ≃ₐ[F] N) (((↑) : N → Ω) ⁻¹' L) ≤ J) :
    IntermediateField.lift (IntermediateField.fixedField J) ≤ L := by
  have hset :
      ((IntermediateField.restrict hLN : IntermediateField F N) : Set N) = ((↑) : N → Ω) ⁻¹' L :=
    Set.ext fun x ↦ IntermediateField.mem_restrict hLN x
  have hfix : IntermediateField.fixedField (fixingSubgroup (N ≃ₐ[F] N) (((↑) : N → Ω) ⁻¹' L)) =
      IntermediateField.restrict hLN := by
    rw [← hset]
    exact IsGalois.fixedField_fixingSubgroup _
  rintro _ ⟨y, hy, rfl⟩
  exact (IntermediateField.mem_restrict hLN y).mp (hfix ▸ IntermediateField.fixedField_le hJ hy)

lemma le_lift_fixedField (hEN : E ≤ N) {J : Subgroup (N ≃ₐ[F] N)}
    (hJ : J ≤ fixingSubgroup (N ≃ₐ[F] N) (((↑) : N → Ω) ⁻¹' E)) :
    E ≤ IntermediateField.lift (IntermediateField.fixedField J) := fun x hx ↦
  (IntermediateField.mem_lift (⟨x, hEN hx⟩ : N)).mpr <|
    (IntermediateField.mem_fixedField_iff _ _).mpr fun _ hσ ↦ hJ hσ ⟨⟨x, hEN hx⟩, hx⟩
