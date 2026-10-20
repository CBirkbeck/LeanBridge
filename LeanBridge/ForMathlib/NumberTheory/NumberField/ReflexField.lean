import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.CMField

/-!
# CM types and reflex fields

A CM type of a CM field `K` is a set `Φ` of complex embeddings of `K` containing exactly one of
each pair of complex conjugate embeddings. Every complex embedding of `K` takes values in the
algebraic closure `ℚ̄` of `ℚ` in `ℂ`, so the absolute Galois group `Gal(ℚ̄/ℚ)` acts on the complex
embeddings of `K` by composition. The reflex field of `Φ` is the fixed field in `ℚ̄` of the
stabilizer of `Φ`.

We take the embeddings of `K` into `ℂ`, which take values in `ℚ̄`, for the LMFDB's embeddings of `K`
into `ℚ̄`, so that Mathlib's complex embeddings and infinite places apply.

## Main definitions

* `NumberField.CMType` (LMFDB `nf.reflex_field`): the CM types of `K`.
* `NumberField.ComplexEmbedding.galoisMap`: the action of `Gal(ℚ̄/ℚ)` on complex embeddings.
* `NumberField.CMType.stabilizer`: the stabilizer of a CM type in `Gal(ℚ̄/ℚ)`.
* `NumberField.CMType.reflexField` (LMFDB `nf.reflex_field`).
* `NumberField.CMType.compl`: the complementary CM type.

## Main results

* `NumberField.CMType.card_cmType`: a totally complex field of degree `2g` has `2 ^ g` CM types,
  so `2 ^ (g - 1)` pairs of complex conjugate CM types (`NumberField.CMType.compl_ne`).
* `NumberField.CMType.compl_eq_image_conjugate`: the complement of a CM type is the set of
  conjugates of its embeddings.
* `NumberField.CMType.reflexField_compl`: a CM type and its complement have the same reflex field.
* `NumberField.CMType.reflexField_le_normalClosure`: the reflex field lies in the normal closure of
  `K` in `ℚ̄`, so it is a number field (`NumberField.CMType.finiteDimensional_reflexField`).
-/

open NumberField ComplexEmbedding InfinitePlace IntermediateField

namespace NumberField

variable {K : Type*} [Field K]

local notation "ℚ̄" => algebraicClosure ℚ ℂ

variable (K) in
/-- A **CM type** of a CM field `K` (LMFDB `nf.reflex_field`): a set `Φ` of complex embeddings of
`K` such that for every complex embedding `φ`, exactly one of `φ` and its complex conjugate lies in
`Φ`. A field with a real embedding has no CM type. -/
def CMType : Type _ :=
  {Φ : Set (K →+* ℂ) // ∀ φ, φ ∈ Φ ↔ conjugate φ ∉ Φ}

namespace CMType

variable (Φ : CMType K)

/-- The **complementary CM type** of `Φ`: the complex embeddings that are not in `Φ`, which are the
complex conjugates of the embeddings in `Φ` (`compl_eq_image_conjugate`). -/
def compl : CMType K :=
  ⟨Φ.1ᶜ, fun φ ↦ not_congr (Φ.2 φ)⟩

/-- The complement of a CM type is the set of the complex conjugates of its embeddings. -/
lemma compl_eq_image_conjugate : Φ.compl.1 = conjugate '' Φ.1 := by
  ext φ
  refine ⟨fun h ↦ ⟨conjugate φ, (Φ.2 _).mpr ?_, involutive_conjugate K φ⟩, ?_⟩
  · rwa [involutive_conjugate K φ]
  · rintro ⟨ψ, hψ, rfl⟩
    exact (Φ.2 ψ).mp hψ

variable [NumberField K]

/-- A CM type differs from its complement, so the CM types come in pairs of complex conjugate CM
types. -/
lemma compl_ne : Φ.compl ≠ Φ := fun h ↦ by
  let φ : K →+* ℂ := Classical.choice inferInstance
  have h' : φ ∈ Φ.compl.1 ↔ φ ∈ Φ.1 := by rw [h]
  exact not_iff_self h'

variable (K) in
/-- **A totally complex field of degree `2g` has `2 ^ g` CM types**: one choice of an embedding
for each complex place. -/
lemma card_cmType [IsTotallyComplex K] : Nat.card (CMType K) = 2 ^ (Module.finrank ℚ K / 2) := by
  classical
  have hne (φ : K →+* ℂ) : conjugate φ ≠ φ := fun h ↦
    IsTotallyComplex.complexEmbedding_not_isReal φ (isReal_iff.mpr h)
  have hc (φ : K →+* ℂ) :
      conjugate φ = (InfinitePlace.mk φ).embedding ↔ ¬φ = (InfinitePlace.mk φ).embedding := by
    rcases embedding_mk_eq φ with h | h <;> rw [h] <;> simp [hne φ, (hne φ).symm]
  let e : CMType K ≃ (InfinitePlace K → Bool) :=
    { toFun Φ w := decide (w.embedding ∈ Φ.1)
      invFun f := ⟨{φ | φ = (InfinitePlace.mk φ).embedding ↔ f (InfinitePlace.mk φ) = true},
        fun φ ↦ by
          simp only [Set.mem_ofPred_eq, mk_conjugate_eq, hc]
          tauto⟩
      left_inv Φ := by
        refine Subtype.ext (Set.ext fun φ ↦ ?_)
        simp only [Set.mem_ofPred_eq]
        rcases embedding_mk_eq φ with h | h
        · rw [h]
          simp
        · rw [h, Φ.2 φ]
          simp [(hne φ).symm]
      right_inv _ := by
        funext w
        simp }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_bool,
    Nat.card_eq_fintype_card, card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, IsTotallyComplex.finrank,
    Nat.mul_div_cancel_left _ two_pos]

end CMType

namespace ComplexEmbedding

variable [NumberField K] (ρ ρ' : ℚ̄ ≃ₐ[ℚ] ℚ̄) (φ : K →+* ℂ) (x : K)

lemma mem_algebraicClosure : φ x ∈ ℚ̄ :=
  mem_algebraicClosure_iff'.mpr ((IsIntegral.of_finite ℚ x).map φ.toRatAlgHom)

/-- The action of the absolute Galois group `Gal(ℚ̄/ℚ)`, for `ℚ̄` the algebraic closure of `ℚ` in
`ℂ`, on the complex embeddings of `K`: `galoisMap ρ φ = ρ ∘ φ`, since `φ` takes values in `ℚ̄`. -/
noncomputable def galoisMap : K →+* ℂ :=
  ℚ̄.val.toRingHom.comp (ρ.toRingEquiv.toRingHom.comp (φ.codRestrict ℚ̄ (mem_algebraicClosure φ)))

lemma galoisMap_apply : galoisMap ρ φ x = ρ ⟨φ x, mem_algebraicClosure φ x⟩ :=
  rfl

lemma galoisMap_one : galoisMap 1 φ = φ :=
  rfl

lemma galoisMap_mul : galoisMap (ρ * ρ') φ = galoisMap ρ (galoisMap ρ' φ) :=
  rfl

lemma galoisMap_inv_galoisMap : galoisMap ρ⁻¹ (galoisMap ρ φ) = φ := by
  rw [← galoisMap_mul, inv_mul_cancel, galoisMap_one]

lemma galoisMap_galoisMap_inv : galoisMap ρ (galoisMap ρ⁻¹ φ) = φ := by
  rw [← galoisMap_mul, mul_inv_cancel, galoisMap_one]

end ComplexEmbedding

namespace CMType

variable [NumberField K] (Φ : CMType K)

/-- The **stabilizer** of a CM type `Φ` in the absolute Galois group `Gal(ℚ̄/ℚ)`: the `ρ` with
`ρ Φ = Φ` (`mem_stabilizer_iff`). -/
def stabilizer : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄) where
  carrier := {ρ | ∀ φ, φ ∈ Φ.1 ↔ galoisMap ρ φ ∈ Φ.1}
  mul_mem' hρ hρ' φ := (hρ' φ).trans (hρ _)
  one_mem' _ := Iff.rfl
  inv_mem' hρ φ := ((hρ _).trans (by rw [galoisMap_galoisMap_inv])).symm

lemma mem_stabilizer_iff {ρ : ℚ̄ ≃ₐ[ℚ] ℚ̄} : ρ ∈ Φ.stabilizer ↔ galoisMap ρ '' Φ.1 = Φ.1 := by
  refine ⟨fun h ↦ Set.ext fun φ ↦ ⟨?_, fun hφ ↦ ⟨galoisMap ρ⁻¹ φ, ?_, ?_⟩⟩, fun h φ ↦ ?_⟩
  · rintro ⟨ψ, hψ, rfl⟩
    exact (h ψ).mp hψ
  · exact (h _).mpr (by rwa [galoisMap_galoisMap_inv])
  · exact galoisMap_galoisMap_inv ρ φ
  · refine ⟨fun hφ ↦ h ▸ ⟨φ, hφ, rfl⟩, fun hφ ↦ ?_⟩
    rw [← h] at hφ
    rcases hφ with ⟨ψ, hψ, hψφ⟩
    rwa [← galoisMap_inv_galoisMap ρ φ, ← hψφ, galoisMap_inv_galoisMap]

/-- The **reflex field** of a CM type `Φ` (LMFDB `nf.reflex_field`): the fixed field in the
algebraic closure `ℚ̄` of `ℚ` in `ℂ` of the subgroup `{ρ ∈ Gal(ℚ̄/ℚ) | ρ Φ = Φ}`. -/
noncomputable def reflexField : IntermediateField ℚ ℚ̄ :=
  fixedField Φ.stabilizer

lemma stabilizer_compl : Φ.compl.stabilizer = Φ.stabilizer :=
  Subgroup.ext fun _ ↦ forall_congr' fun _ ↦ not_iff_not

/-- A CM type and its complement have the same reflex field. -/
lemma reflexField_compl : Φ.compl.reflexField = Φ.reflexField := by
  rw [reflexField, reflexField, stabilizer_compl]

/-- The reflex field lies in the normal closure of `K` in `ℚ̄`, the field generated by the images of
the complex embeddings of `K`: an element of `Gal(ℚ̄/ℚ)` fixing it fixes every complex embedding of
`K`, hence `Φ`. -/
lemma reflexField_le_normalClosure : Φ.reflexField ≤ normalClosure ℚ K ℚ̄ := by
  have h : (normalClosure ℚ K ℚ̄).fixingSubgroup ≤ Φ.stabilizer := fun ρ hρ φ ↦ by
    have hρφ : galoisMap ρ φ = φ := by
      ext x
      exact congrArg Subtype.val ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hρ _
        ((φ.codRestrict ℚ̄ (mem_algebraicClosure φ)).toRatAlgHom.fieldRange_le_normalClosure
          ⟨x, rfl⟩))
    rw [hρφ]
  rw [← InfiniteGalois.fixedField_fixingSubgroup (normalClosure ℚ K ℚ̄)]
  exact fun x hx ↦ (mem_fixedField_iff _ x).mpr fun σ hσ ↦ (mem_fixedField_iff _ x).mp hx σ (h hσ)

/-- The reflex field is a finite extension of `ℚ`, so a number field. -/
lemma finiteDimensional_reflexField : FiniteDimensional ℚ Φ.reflexField :=
  let i : Φ.reflexField →ₐ[ℚ] normalClosure ℚ K ℚ̄ := inclusion Φ.reflexField_le_normalClosure
  .of_injective i.toLinearMap i.injective

end CMType

end NumberField
