import Mathlib.NumberTheory.NumberField.CMField

/-!
# The maximal CM subfield of a number field

A subfield `E` of a number field `K` is totally real or CM exactly when complex conjugation induces
an automorphism of `E` commuting with all complex embeddings of `E`. Accordingly, the elements `x`
of `K` for which some `y ∈ K` satisfies `φ y = conj (φ x)` for every complex embedding `φ` of `K`
form a subfield, the largest one on which complex conjugation is defined in this way. It contains
every CM subfield and every totally real subfield of `K`, and it is CM as soon as `K` has a CM
subfield, so it is then the CM subfield of `K` of largest degree, which is unique. If `K` has no CM
subfield, it is the maximal real subfield of `K`.

## Main definitions

* `NumberField.maximalCMSubfield` (LMFDB `nf.maximal_cm_subfield`).
* `NumberField.conjMaximalCMSubfield`: complex conjugation on the maximal CM subfield.

## Main results

* `NumberField.IsCMField.le_maximalCMSubfield`: every CM subfield of `K` lies in the maximal CM
  subfield.
* `NumberField.isCMField_maximalCMSubfield`: the maximal CM subfield is CM when it is totally
  complex.
* `NumberField.isCMField_maximalCMSubfield_iff`: the maximal CM subfield is CM exactly when `K` has
  a CM subfield.
* `NumberField.IsCMField.eq_maximalCMSubfield`: a CM subfield of `K` of degree at least that of the
  maximal CM subfield is the maximal CM subfield.
* `NumberField.maximalCMSubfield_eq_maximalRealSubfield_iff`: when `K` has no CM subfield, the
  maximal CM subfield is the maximal real subfield, and only then.
-/

open NumberField ComplexEmbedding InfinitePlace

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The **maximal CM subfield** of a number field `K` (LMFDB `nf.maximal_cm_subfield`): the CM
subfield of `K` of largest degree. It is defined as the subfield of the `x ∈ K` such that some
`y ∈ K` satisfies `φ y = conj (φ x)` for every complex embedding `φ` of `K`; this is the largest
subfield of `K` that is totally real or CM.

If `K` has a CM subfield then this subfield is CM (`isCMField_maximalCMSubfield_iff`) and contains
every CM subfield of `K` (`IsCMField.le_maximalCMSubfield`), so it is the unique CM subfield of
largest degree (`IsCMField.eq_maximalCMSubfield`). Otherwise the LMFDB's maximal CM subfield does
not exist, and this is the junk value `maximalRealSubfield K`
(`maximalCMSubfield_eq_maximalRealSubfield_iff`). -/
def maximalCMSubfield : Subfield K where
  carrier := {x | ∃ y : K, ∀ φ : K →+* ℂ, φ y = star (φ x)}
  mul_mem' := fun ⟨y, hy⟩ ⟨y', hy'⟩ ↦ ⟨y * y', fun φ ↦ by rw [map_mul, map_mul, hy, hy', star_mul']⟩
  one_mem' := ⟨1, fun φ ↦ by rw [map_one, star_one]⟩
  add_mem' := fun ⟨y, hy⟩ ⟨y', hy'⟩ ↦ ⟨y + y', fun φ ↦ by rw [map_add, map_add, hy, hy', star_add]⟩
  zero_mem' := ⟨0, fun φ ↦ by rw [map_zero, star_zero]⟩
  neg_mem' := fun ⟨y, hy⟩ ↦ ⟨-y, fun φ ↦ by rw [map_neg, map_neg, hy, star_neg]⟩
  inv_mem' := fun _ ⟨y, hy⟩ ↦ ⟨y⁻¹, fun φ ↦ by rw [map_inv₀, map_inv₀, hy, star_inv₀]⟩

variable {K} (E : Subfield K) [IsCMField E] (φ : K →+* ℂ) (x : maximalCMSubfield K)

lemma mem_maximalCMSubfield_iff {a : K} :
    a ∈ maximalCMSubfield K ↔ ∃ y : K, ∀ φ : K →+* ℂ, φ y = star (φ a) :=
  Iff.rfl

/-- Every CM subfield of `K` lies in the maximal CM subfield. -/
lemma IsCMField.le_maximalCMSubfield : E ≤ maximalCMSubfield K :=
  fun a ha ↦ ⟨IsCMField.complexConj E ⟨a, ha⟩, fun φ ↦
    IsCMField.complexEmbedding_complexConj E (φ.comp E.subtype) ⟨a, ha⟩⟩

lemma maximalRealSubfield_le_maximalCMSubfield : maximalRealSubfield K ≤ maximalCMSubfield K :=
  fun a ha ↦ ⟨a, fun φ ↦ (ha φ).symm⟩

private lemma exists_apply_eq_star :
    ∃ y : maximalCMSubfield K, ∀ φ : K →+* ℂ, φ y = star (φ x) := by
  rcases x.2 with ⟨y, hy⟩
  exact ⟨⟨y, x, fun φ ↦ by rw [hy, star_star]⟩, hy⟩

private lemma eq_of_forall_apply_eq {a b : maximalCMSubfield K} (h : ∀ φ : K →+* ℂ, φ a = φ b) :
    a = b :=
  Subtype.ext <| (Classical.choice (inferInstance : Nonempty (K →+* ℂ))).injective (h _)

/-- The conjugate of an element of the maximal CM subfield. -/
private noncomputable def conjAux : maximalCMSubfield K :=
  (exists_apply_eq_star x).choose

private lemma apply_conjAux : φ (conjAux x) = star (φ x) :=
  (exists_apply_eq_star x).choose_spec φ

private lemma conjAux_conjAux : conjAux (conjAux x) = x :=
  eq_of_forall_apply_eq fun φ ↦ by rw [apply_conjAux, apply_conjAux, star_star]

variable (K) in
/-- **Complex conjugation** on the maximal CM subfield of `K`: the automorphism `c` such that
`φ (c x) = conj (φ x)` for every complex embedding `φ` of `K` (`apply_conjMaximalCMSubfield`). It is
the complex conjugation of every complex embedding of the maximal CM subfield
(`isConj_conjMaximalCMSubfield`). -/
noncomputable def conjMaximalCMSubfield : maximalCMSubfield K ≃ₐ[ℚ] maximalCMSubfield K :=
  RingEquiv.toRatAlgEquiv
    { toFun := conjAux
      invFun := conjAux
      left_inv := conjAux_conjAux
      right_inv := conjAux_conjAux
      map_mul' _ _ := eq_of_forall_apply_eq fun φ ↦ by simp [apply_conjAux]
      map_add' _ _ := eq_of_forall_apply_eq fun φ ↦ by simp [apply_conjAux] }

lemma apply_conjMaximalCMSubfield : φ (conjMaximalCMSubfield K x) = star (φ x) :=
  apply_conjAux φ x

lemma isConj_conjMaximalCMSubfield (ψ : maximalCMSubfield K →+* ℂ) :
    IsConj ψ (conjMaximalCMSubfield K) := by
  have : Algebra.IsAlgebraic (maximalCMSubfield K) K := .tower_top (K := ℚ) _
  ext y
  rw [conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply, ← lift_algebraMap_apply K ψ y,
    ← lift_algebraMap_apply K ψ]
  exact (apply_conjMaximalCMSubfield _ y).symm

/-- The maximal CM subfield is CM when it is totally complex: complex conjugation is then an
automorphism of order `2`, whose fixed field is totally real. -/
lemma isCMField_maximalCMSubfield [IsTotallyComplex (maximalCMSubfield K)] :
    IsCMField (maximalCMSubfield K) := by
  let ψ : maximalCMSubfield K →+* ℂ := Classical.choice inferInstance
  have hσ : orderOf (conjMaximalCMSubfield K) = 2 :=
    orderOf_isConj_two_of_ne_one (isConj_conjMaximalCMSubfield ψ)
      ((isConj_ne_one_iff (isConj_conjMaximalCMSubfield ψ)).mpr
        (IsTotallyComplex.complexEmbedding_not_isReal ψ))
  let F : IntermediateField ℚ (maximalCMSubfield K) :=
    IntermediateField.fixedField (Subgroup.zpowers (conjMaximalCMSubfield K))
  have : IsTotallyReal F := ⟨fun w ↦ by
    have : Algebra.IsAlgebraic F (maximalCMSubfield K) := .tower_top (K := ℚ) _
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext y
    rw [conjugate_coe_eq, ← lift_algebraMap_apply (maximalCMSubfield K) w.embedding y,
      starRingEnd_apply, ← (isConj_conjMaximalCMSubfield _).eq]
    exact congrArg _ ((IntermediateField.mem_fixedField_iff _ _).mp y.2 _ (Subgroup.mem_zpowers _))⟩
  have : Algebra.IsQuadraticExtension F (maximalCMSubfield K) :=
    ⟨by rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hσ]⟩
  exact IsCMField.ofCMExtension F (maximalCMSubfield K)

/-- The maximal CM subfield of `K` is CM exactly when `K` has a CM subfield. -/
lemma isCMField_maximalCMSubfield_iff :
    IsCMField (maximalCMSubfield K) ↔ ∃ E : Subfield K, IsCMField E := by
  refine ⟨fun h ↦ ⟨_, h⟩, fun ⟨E, _⟩ ↦ ?_⟩
  let _ : Algebra E (maximalCMSubfield K) :=
    (Subfield.inclusion (IsCMField.le_maximalCMSubfield E)).toAlgebra
  have : IsTotallyComplex (maximalCMSubfield K) := isTotallyComplex_of_algebra E _
  exact isCMField_maximalCMSubfield

/-- **The maximal CM subfield is the CM subfield of largest degree.** A CM subfield of `K` whose
degree is at least that of the maximal CM subfield is the maximal CM subfield. -/
lemma IsCMField.eq_maximalCMSubfield
    (h : Module.finrank ℚ (maximalCMSubfield K) ≤ Module.finrank ℚ E) :
    E = maximalCMSubfield K := by
  have hle : E ≤ maximalCMSubfield K := IsCMField.le_maximalCMSubfield E
  let f : E →ₗ[ℚ] maximalCMSubfield K := (Subfield.inclusion hle).toRatAlgHom.toLinearMap
  have hf : Function.Injective f := (Subfield.inclusion hle).injective
  refine hle.antisymm fun a ha ↦ ?_
  rcases (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((LinearMap.finrank_le_finrank_of_injective hf).antisymm h)).mp hf ⟨a, ha⟩ with ⟨y, hy⟩
  have hya : (y : K) = a := congrArg Subtype.val hy
  exact hya ▸ y.2

variable (K) in
lemma isTotallyReal_or_isTotallyComplex_maximalCMSubfield :
    IsTotallyReal (maximalCMSubfield K) ∨ IsTotallyComplex (maximalCMSubfield K) := by
  by_cases hσ : conjMaximalCMSubfield K = 1
  · exact .inl ⟨fun w ↦ isReal_iff.mpr <| isConj_one_iff.mp <|
      hσ ▸ isConj_conjMaximalCMSubfield w.embedding⟩
  · exact .inr ⟨fun w ↦ not_isReal_iff_isComplex.mp fun hw ↦
      (isConj_ne_one_iff (isConj_conjMaximalCMSubfield w.embedding)).mp hσ (isReal_iff.mp hw)⟩

/-- The maximal CM subfield of `K` is the maximal real subfield of `K` exactly when `K` has no CM
subfield. -/
lemma maximalCMSubfield_eq_maximalRealSubfield_iff :
    maximalCMSubfield K = maximalRealSubfield K ↔ ¬∃ E : Subfield K, IsCMField E := by
  refine ⟨fun h ⟨E, hE⟩ ↦ ?_, fun h ↦ ?_⟩
  · have : IsTotallyReal E :=
      isTotallyReal_iff_le_maximalRealSubfield.mpr (h ▸ IsCMField.le_maximalCMSubfield E)
    let w : InfinitePlace E := Classical.choice inferInstance
    exact not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w) (IsTotallyReal.isReal w)
  · rcases isTotallyReal_or_isTotallyComplex_maximalCMSubfield K with hK | hK
    · exact (isTotallyReal_iff_le_maximalRealSubfield.mp hK).antisymm
        maximalRealSubfield_le_maximalCMSubfield
    · exact absurd ⟨_, isCMField_maximalCMSubfield⟩ h

end NumberField
