import LeanBridge.ForMathlib.NumberTheory.NumberField.ReflexReflexField

/-!
# The reflex field of the reflex field as a fixed field

Let `Φ` be a CM type of a number field `K`. The reflex field of the reflex field of `Φ` (LMFDB
`nf.reflex_reflex_field`) is defined in `NumberField.CMType.reflexReflexField` as the intersection
of the subfields of `K` from which `Φ` is induced. This file proves that `Φ` is induced from it, so
that it is the smallest field of definition of `Φ`, and identifies it with the fixed field of the
stabiliser of `Φ_N` and with the reflex field of the reflex type.

Let `Ω` be a Galois extension of `ℚ`, finite or not, with a homomorphism `j : K → Ω`, and let `Φ_Ω`
be the CM type of `Ω` induced by `Φ`: the complex embeddings of `Ω` whose composite with `j` lies in
`Φ`. The group `Gal(Ω/ℚ)` acts on the right on the complex embeddings of `Ω`, by precomposition,
and transitively. Let `S` be the stabiliser of `Φ_Ω`. For a subfield `M` of `K`, the CM type `Φ` is
induced from `M` if and only if every automorphism of `Ω` fixing `j(M)` lies in `S`: two complex
embeddings of `K` that agree on `M` extend to complex embeddings `χ` and `χ ∘ g` of `Ω`, with `g`
fixing `j(M)`. The group `S` contains the open subgroup fixing the normal closure of `j(K)`, so it
is closed, and Krull's Galois correspondence turns this into: `Φ` is induced from `M` if and only if
`j(M)` contains the fixed field of `S`. So the fixed field of `S` lies in `j(K)`, and it is the
image of the smallest subfield of `K` from which `Φ` is induced.

For `Ω` a finite Galois extension `N` of `ℚ` containing `K`, such as a Galois closure of `K`, this
is the LMFDB's description of the reflex field of the reflex field as the subfield of `N` fixed by
the stabiliser of `Φ_N` (the knowl lets `Gal(N/K)` act on the CM types of `K`, an action that is
trivial; the action meant is that of `Gal(N/ℚ)` on the CM types of `N`). For `Ω` the algebraic
closure `ℚ̄` of `ℚ` in `ℂ` and `j` a complex embedding `φ₀` of `K`, the stabiliser `S` is the
stabiliser in `Gal(ℚ̄/ℚ)` of the reflex type of `Φ` with respect to `φ₀`, so the fixed field of `S`
is the reflex field of the reflex type: the classical form of the LMFDB's definition, which
`ReflexReflexFieldInverseType` states literally.

## Main definitions

* `NumberField.CMType.precompStabilizer`: the stabiliser of a CM type of `Ω` under the right action
  of the automorphisms of `Ω` by precomposition.

## Main results

* `NumberField.CMType.mem_precompStabilizer_iff_image_comp_eq`: `precompStabilizer` is the
  stabiliser `{g | Θ ∘ g = Θ}` of the right action by precomposition.
* `NumberField.CMType.isInducedFrom_iff_forall_comp_subtype_eq`: `Φ` is induced from `M` if and
  only if membership in `Φ` depends only on the restriction to `M`.
* `NumberField.CMType.isInducedFrom_iff_fixedField_le`: `Φ` is induced from `M` if and only if
  `j(M)` contains the fixed field of the stabiliser of `Φ_Ω`.
* `NumberField.CMType.map_reflexReflexField_eq_fixedField`: the image under `j` of the reflex field
  of the reflex field is the fixed field of the stabiliser of `Φ_Ω`.
* `NumberField.CMType.isInducedFrom_reflexReflexField` (LMFDB `nf.reflex_reflex_field`): `Φ` is
  induced from its reflex field of the reflex field.
* `NumberField.CMType.isLeast_reflexReflexField` (LMFDB `nf.reflex_reflex_field`): the reflex field
  of the reflex field is the smallest subfield of `K` from which `Φ` is induced.
* `NumberField.CMType.map_reflexReflexField_eq_reflexField_reflexType` (LMFDB
  `nf.reflex_reflex_field`): the image under `φ₀` of the reflex field of the reflex field is the
  reflex field of the reflex type with respect to `φ₀`.
* `NumberField.CMType.map_algebraMap_reflexReflexField` (LMFDB `nf.reflex_reflex_field`): in a
  finite Galois extension `N` of `ℚ` containing `K`, the reflex field of the reflex field is the
  fixed field of the stabiliser of `Φ_N`.
-/

open IntermediateField NumberField ComplexEmbedding

namespace NumberField.CMType

local notation "ℚ̄" => algebraicClosure ℚ ℂ

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra ℚ Ω] (Φ : CMType K) (Θ : CMType Ω)
  (j : K →+* Ω) {M : Subfield K}

/-- The stabiliser of a CM type `Θ` of a field `Ω` under the right action of the automorphisms of
`Ω` over `ℚ` on the complex embeddings of `Ω` by precomposition: the `g` such that `χ ∘ g ∈ Θ` if
and only if `χ ∈ Θ`, that is, such that `Θ ∘ g = Θ` (`mem_precompStabilizer_iff_image_comp_eq`),
or such that the CM type `Θ.induce g` is `Θ` (`mem_precompStabilizer_iff_induce_eq`). For a Galois
closure `N` of `K` and the CM type `Φ_N` induced by a CM type `Φ` of `K`, its fixed field is the
reflex field of the reflex field of `Φ` (LMFDB `nf.reflex_reflex_field`). -/
def precompStabilizer : Subgroup (Ω ≃ₐ[ℚ] Ω) where
  carrier := {g | ∀ χ : Ω →+* ℂ, χ ∈ Θ.1 ↔ χ.comp g ∈ Θ.1}
  mul_mem' hg hh χ := (hg χ).trans (hh _)
  one_mem' _ := Iff.rfl
  inv_mem' {g} hg χ := by
    have h : (χ.comp ((g⁻¹ : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω)).comp (g : Ω →+* Ω) = χ :=
      RingHom.ext fun x ↦ by simp
    exact ((hg _).trans (by rw [h])).symm

variable {Θ} in
lemma mem_precompStabilizer_iff {g : Ω ≃ₐ[ℚ] Ω} :
    g ∈ Θ.precompStabilizer ↔ ∀ χ : Ω →+* ℂ, χ ∈ Θ.1 ↔ χ.comp g ∈ Θ.1 :=
  Iff.rfl

variable {Θ} in
lemma mem_precompStabilizer_iff_induce_eq {g : Ω ≃ₐ[ℚ] Ω} :
    g ∈ Θ.precompStabilizer ↔ Θ.induce (g : Ω →+* Ω) = Θ :=
  ⟨fun h ↦ Subtype.ext <| Set.ext fun χ ↦ (h χ).symm, fun h χ ↦ by
    conv_lhs => rw [← h]
    rfl⟩

variable {Θ} in
/-- **`precompStabilizer` is the stabiliser for the right action by precomposition**: `g` lies in
it if and only if `Θ ∘ g = Θ`, where `Θ ∘ g` is the set of the `χ ∘ g` for `χ ∈ Θ`. -/
lemma mem_precompStabilizer_iff_image_comp_eq {g : Ω ≃ₐ[ℚ] Ω} :
    g ∈ Θ.precompStabilizer ↔ (fun χ : Ω →+* ℂ ↦ χ.comp g) '' Θ.1 = Θ.1 := by
  refine ⟨fun h ↦ Set.ext fun χ ↦ ⟨?_, fun hχ ↦ ⟨χ.comp ((g⁻¹ : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω),
    (inv_mem h χ).mp hχ, RingHom.ext fun x ↦ by simp⟩⟩, fun h χ ↦ ⟨fun hχ ↦ h.subset ⟨χ, hχ, rfl⟩,
    fun hχ ↦ ?_⟩⟩
  · rintro ⟨ψ, hψ, rfl⟩
    exact (h ψ).mp hψ
  · rcases h.symm.subset hχ with ⟨ψ, hψ, hψχ⟩
    have hψχ' : ψ = χ := RingHom.ext fun x ↦ by simpa using RingHom.congr_fun hψχ (g.symm x)
    exact hψχ' ▸ hψ

variable [Algebra.IsAlgebraic ℚ Ω] in
private lemma exists_comp_eq_of_isAlgebraic {L : Type*} [Field L] (i : L →+* Ω) (φ : L →+* ℂ) :
    ∃ χ : Ω →+* ℂ, χ.comp i = φ := by
  have hL : CharZero L := φ.charZero
  let _ : Algebra L Ω := i.toAlgebra
  have hΩ : Algebra.IsAlgebraic L Ω := .tower_top (K := ℚ) L
  exact ⟨lift Ω φ, lift_comp_algebraMap Ω φ⟩

variable [NumberField K]

/-- **A CM type is induced from a subfield if and only if membership depends only on the
restriction to it**: `Φ` is induced from `M` if and only if every complex embedding of `K` that
agrees on `M` with an embedding in `Φ` lies in `Φ`. -/
lemma isInducedFrom_iff_forall_comp_subtype_eq : Φ.IsInducedFrom M ↔
    ∀ φ φ' : K →+* ℂ, φ.comp M.subtype = φ'.comp M.subtype → φ ∈ Φ.1 → φ' ∈ Φ.1 := by
  refine ⟨fun ⟨Ψ, hΨ⟩ φ φ' h hφ ↦ (hΨ φ').mpr <| h ▸ (hΨ φ).mp hφ, fun h ↦ ?_⟩
  have h' (φ φ' : K →+* ℂ) (hφ : φ.comp M.subtype = φ'.comp M.subtype) : φ ∈ Φ.1 ↔ φ' ∈ Φ.1 :=
    ⟨h φ φ' hφ, h φ' φ hφ.symm⟩
  have hΨ (φ : K →+* ℂ) : (∃ φ' ∈ Φ.1, φ'.comp M.subtype = φ.comp M.subtype) ↔ φ ∈ Φ.1 :=
    ⟨fun ⟨φ', hφ', hφ⟩ ↦ (h' φ' φ hφ).mp hφ', fun hφ ↦ ⟨φ, hφ, rfl⟩⟩
  refine ⟨⟨{ψ | ∃ φ ∈ Φ.1, φ.comp M.subtype = ψ}, fun ψ ↦ ?_⟩, fun φ ↦ (hΨ φ).symm⟩
  rcases exists_comp_eq_of_isAlgebraic M.subtype ψ with ⟨φ, rfl⟩
  exact (hΨ φ).trans <| (Φ.2 φ).trans (hΨ (conjugate φ)).not.symm

variable [IsGalois ℚ Ω]

lemma isInducedFrom_iff_forall_mem_precompStabilizer : Φ.IsInducedFrom M ↔
    ∀ g : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ M, g (j x) = j x) → g ∈ (Φ.induce j).precompStabilizer := by
  refine ⟨fun ⟨Ψ, hΨ⟩ g hg χ ↦ ?_,
    fun h ↦ Φ.isInducedFrom_iff_forall_comp_subtype_eq.mpr fun φ φ' hφ hφΦ ↦ ?_⟩
  · have hχ : (χ.comp j).comp M.subtype = ((χ.comp ↑g).comp j).comp M.subtype :=
      RingHom.ext fun x ↦ congrArg χ (hg x x.2).symm
    exact (hΨ _).trans <| hχ ▸ (hΨ _).symm
  · rcases exists_comp_eq_of_isAlgebraic j φ with ⟨χ, rfl⟩
    rcases exists_comp_eq_of_isAlgebraic j φ' with ⟨χ', rfl⟩
    rcases exists_comp_symm_eq_of_comp_eq (k := ℚ) χ χ' (Subsingleton.elim _ _) with ⟨σ, rfl⟩
    exact (h σ.symm (fun x hx ↦ χ.injective (RingHom.congr_fun hφ ⟨x, hx⟩).symm) χ).mp hφΦ

lemma fixingSubgroup_fixedField_precompStabilizer :
    (fixedField (Φ.induce j).precompStabilizer).fixingSubgroup =
      (Φ.induce j).precompStabilizer := by
  have hle : (normalClosure ℚ K Ω).fixingSubgroup ≤ (Φ.induce j).precompStabilizer := by
    intro ρ hρ
    refine mem_precompStabilizer_iff.mpr fun χ ↦ ?_
    have hρj : (χ.comp ↑ρ).comp j = χ.comp j := RingHom.ext fun x ↦ congrArg χ <|
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hρ (j x)
        (j.toRatAlgHom.fieldRange_le_normalClosure ⟨x, rfl⟩)
    exact iff_of_eq (congrArg (· ∈ Φ.1) hρj.symm)
  exact InfiniteGalois.fixingSubgroup_fixedField ⟨_, Subgroup.isClosed_of_isOpen _ <|
    Subgroup.isOpen_mono hle (normalClosure ℚ K Ω).fixingSubgroup_isOpen⟩

/-- **A CM type is induced from a subfield if and only if its image contains the fixed field of
the stabiliser**: for a Galois extension `Ω` of `ℚ` with a homomorphism `j : K → Ω`, the CM type `Φ`
is induced from `M` if and only if `j(M)` contains the fixed field of the stabiliser of the CM type
of `Ω` induced by `Φ`. -/
lemma isInducedFrom_iff_fixedField_le :
    Φ.IsInducedFrom M ↔ (fixedField (Φ.induce j).precompStabilizer).toSubfield ≤ M.map j := by
  rw [Φ.isInducedFrom_iff_forall_mem_precompStabilizer j]
  refine ⟨fun h z hz ↦ ?_, fun h g hg ↦ ?_⟩
  · let F : IntermediateField ℚ Ω := (M.map j).toIntermediateField fun q ↦
      ⟨q, SubfieldClass.ratCast_mem M q, (map_ratCast j q).trans (eq_ratCast _ q).symm⟩
    have hF : F.fixingSubgroup ≤ (Φ.induce j).precompStabilizer := fun g hg ↦
      h g fun x hx ↦ (IntermediateField.mem_fixingSubgroup_iff F g).mp hg (j x) ⟨x, hx, rfl⟩
    exact ((fixedField_le hF).trans (InfiniteGalois.fixedField_fixingSubgroup F).le) hz
  · rw [← Φ.fixingSubgroup_fixedField_precompStabilizer j, IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    rcases h hz with ⟨x, hx, rfl⟩
    exact hg x hx

lemma fixedField_precompStabilizer_le_fieldRange :
    (fixedField (Φ.induce j).precompStabilizer).toSubfield ≤ j.fieldRange :=
  j.fieldRange_eq_map ▸ (Φ.isInducedFrom_iff_fixedField_le j).mp Φ.isInducedFrom_top

lemma reflexReflexField_eq_comap :
    Φ.reflexReflexField = (fixedField (Φ.induce j).precompStabilizer).toSubfield.comap j := by
  refine (Φ.reflexReflexField_le <| (Φ.isInducedFrom_iff_fixedField_le j).mpr
    (Subfield.map_comap_eq_self <| Φ.fixedField_precompStabilizer_le_fieldRange j).ge).antisymm <|
    le_sInf fun M hM ↦ ?_
  exact ((Subfield.gc_map_comap j).monotone_u <|
    (Φ.isInducedFrom_iff_fixedField_le j).mp hM).trans_eq (Subfield.comap_map j M)

/-- **The image of the reflex field of the reflex field is the fixed field of the stabiliser**:
for a Galois extension `Ω` of `ℚ` with a homomorphism `j : K → Ω`, the image under `j` of the
reflex field of the reflex field of `Φ` is the fixed field of the stabiliser of the CM type of `Ω`
induced by `Φ`. -/
lemma map_reflexReflexField_eq_fixedField :
    Φ.reflexReflexField.map j = (fixedField (Φ.induce j).precompStabilizer).toSubfield :=
  (congrArg (Subfield.map j) (Φ.reflexReflexField_eq_comap j)).trans <|
    Subfield.map_comap_eq_self <| Φ.fixedField_precompStabilizer_le_fieldRange j

variable (φ₀ : K →+* ℂ)

lemma mem_precompStabilizer_induce_codRestrict_iff {ρ : ℚ̄ ≃ₐ[ℚ] ℚ̄} :
    ρ ∈ (Φ.induce (φ₀.codRestrict ℚ̄ (mem_algebraicClosure φ₀))).precompStabilizer ↔
      ∀ τ, galoisMap τ φ₀ ∈ Φ.1 ↔ galoisMap (τ * ρ) φ₀ ∈ Φ.1 := by
  refine ⟨fun h τ ↦ h (ℚ̄.val.toRingHom.comp τ), fun h χ ↦ ?_⟩
  rcases exists_comp_symm_eq_of_comp_eq (k := ℚ) ℚ̄.val.toRingHom χ (Subsingleton.elim _ _) with
    ⟨σ, rfl⟩
  exact h σ.symm

/-- **A CM type is induced from its reflex field of the reflex field** (LMFDB
`nf.reflex_reflex_field`): the intersection of the subfields of `K` from which `Φ` is induced is a
subfield from which `Φ` is induced. -/
lemma isInducedFrom_reflexReflexField : Φ.IsInducedFrom Φ.reflexReflexField :=
  let φ₀ : K →+* ℂ := Classical.choice inferInstance
  (Φ.isInducedFrom_iff_fixedField_le (φ₀.codRestrict ℚ̄ (mem_algebraicClosure φ₀))).mpr
    (Φ.map_reflexReflexField_eq_fixedField _).ge

/-- **The reflex field of the reflex field is the smallest field of definition** (LMFDB
`nf.reflex_reflex_field`): it is the least subfield of `K` from which `Φ` is induced. The LMFDB
knowl says "largest", but a CM type induced from a subfield is induced from every larger
subfield. -/
lemma isLeast_reflexReflexField : IsLeast {M | Φ.IsInducedFrom M} Φ.reflexReflexField :=
  ⟨Φ.isInducedFrom_reflexReflexField, fun _ ↦ Φ.reflexReflexField_le⟩

/-- **In a finite Galois extension of `ℚ` containing `K`, the reflex field of the reflex field is
the fixed field of the stabiliser of the induced CM type** (LMFDB `nf.reflex_reflex_field`): for a
finite Galois extension `N` of `ℚ` containing `K`, such as a Galois closure of `K`, and the CM type
`Φ_N` of `N` induced by `Φ`, the subfield of `N` fixed by the `g ∈ Gal(N/ℚ)` with `Φ_N ∘ g = Φ_N`
is the reflex field of the reflex field of `Φ`. The LMFDB knowl lets `Gal(N/K)` act on the CM types
of `K`; that action is trivial. -/
lemma map_algebraMap_reflexReflexField (N : Type*) [Field N] [NumberField N] [IsGalois ℚ N]
    [Algebra K N] : Φ.reflexReflexField.map (algebraMap K N) =
      (fixedField (Φ.induce (algebraMap K N)).precompStabilizer).toSubfield :=
  Φ.map_reflexReflexField_eq_fixedField _

variable [IsCMField K]

lemma stabilizer_reflexType : (Φ.reflexType φ₀).stabilizer =
    (Φ.induce (φ₀.codRestrict ℚ̄ (mem_algebraicClosure φ₀))).precompStabilizer := by
  ext ρ
  rw [← inv_mem_iff (H := precompStabilizer _), mem_precompStabilizer_induce_codRestrict_iff]
  refine ⟨fun h τ ↦ ?_, fun h ψ ↦ ?_⟩
  · have hτ : galoisMap τ⁻¹ (algebraMap Φ.reflexField ℂ) ∈ (Φ.reflexType φ₀).1 ↔
        galoisMap ρ (galoisMap τ⁻¹ (algebraMap Φ.reflexField ℂ)) ∈ (Φ.reflexType φ₀).1 :=
      h _
    rwa [← galoisMap_mul, galoisMap_mem_reflexType_iff, galoisMap_mem_reflexType_iff, inv_inv,
      mul_inv_rev, inv_inv] at hτ
  · rcases exists_galoisMap_eq (algebraMap Φ.reflexField ℂ) ψ with ⟨σ, rfl⟩
    rw [← galoisMap_mul, galoisMap_mem_reflexType_iff, galoisMap_mem_reflexType_iff, mul_inv_rev]
    exact h σ⁻¹

/-- **The reflex field of the reflex field is the reflex field of the reflex type** (LMFDB
`nf.reflex_reflex_field`): for a CM type `Φ` of a CM field `K` and a complex embedding `φ₀` of `K`,
the image under `φ₀` of the smallest subfield of `K` from which `Φ` is induced is the reflex field
of the reflex type of `Φ` with respect to `φ₀`, as subfields of the algebraic closure `ℚ̄` of `ℚ` in
`ℂ`. -/
lemma map_reflexReflexField_eq_reflexField_reflexType :
    Φ.reflexReflexField.map (φ₀.codRestrict ℚ̄ (mem_algebraicClosure φ₀)) =
      (Φ.reflexType φ₀).reflexField.toSubfield := by
  rw [reflexField, Φ.stabilizer_reflexType φ₀]
  exact Φ.map_reflexReflexField_eq_fixedField _

lemma mem_reflexField_reflexType_iff {z : ℚ̄} :
    z ∈ (Φ.reflexType φ₀).reflexField ↔ ∃ x ∈ Φ.reflexReflexField, φ₀ x = z := by
  rw [← mem_toSubfield, ← Φ.map_reflexReflexField_eq_reflexField_reflexType φ₀, Subfield.mem_map]
  exact exists_congr fun x ↦ and_congr_right fun _ ↦ Subtype.ext_iff

end NumberField.CMType
