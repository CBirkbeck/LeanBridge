import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Classification

/-!
# Extending embeddings of countable subfields of `ℂ` to automorphisms

Every field embedding `ι : K → ℂ` of a countable subfield `K ⊆ ℂ` is the restriction of an
automorphism of `ℂ`. This is what makes Galois conjugacy of newforms through automorphisms of `ℂ`
the same as Galois conjugacy through embeddings of their coefficient fields, or through
`Gal(ℚ̄/ℚ)` as in the LMFDB.

## Main results

* `IntermediateField.exists_algEquiv_apply_eq_of_countable`: an embedding of a countable subfield
  of `ℂ` into `ℂ` extends to an automorphism of `ℂ`.
-/

open Cardinal

namespace IntermediateField

variable {K : IntermediateField ℚ ℂ} [Countable K]

/-- **Embeddings of countable subfields of `ℂ` extend to automorphisms of `ℂ`**: for a countable
subfield `K ⊆ ℂ`, every embedding `ι : K → ℂ` is the restriction of an automorphism of `ℂ`.
Transcendence bases of `ℂ` over `K` and over `ι(K)` have the cardinality of `ℂ`, so `ι` extends to
an isomorphism between the purely transcendental extensions that they generate, and then to their
common algebraic closure `ℂ`. -/
lemma exists_algEquiv_apply_eq_of_countable (ι : K →ₐ[ℚ] ℂ) :
    ∃ σ : Gal(ℂ/ℚ), ∀ x : K, σ x = ι x := by
  let e₀ : K ≃ₐ[ℚ] ι.fieldRange := AlgEquiv.ofInjectiveField ι
  have : Countable ι.fieldRange := e₀.symm.injective.countable
  rcases exists_isTranscendenceBasis K ℂ with ⟨s, hs⟩
  rcases exists_isTranscendenceBasis ι.fieldRange ℂ with ⟨t, ht⟩
  have hℂ : ℵ₀ < #ℂ := mk_complex ▸ aleph0_lt_continuum
  rcases Cardinal.eq.mp <| (IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs
    (mk_le_aleph0_iff.mpr inferInstance) hℂ).symm.trans <|
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht
      (mk_le_aleph0_iff.mpr inferInstance) hℂ with ⟨e⟩
  have : IsAlgClosure (Algebra.adjoin K (Set.range ((↑) : s → ℂ))) ℂ :=
    IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  have : IsAlgClosure (Algebra.adjoin ι.fieldRange (Set.range ((↑) : t → ℂ))) ℂ :=
    IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  refine ⟨(IsAlgClosure.equivOfEquiv ℂ ℂ <| hs.1.aevalEquiv.symm.toRingEquiv.trans <|
    (MvPolynomial.renameEquiv K e).toRingEquiv.trans <|
      (MvPolynomial.mapEquiv t e₀.toRingEquiv).trans ht.1.aevalEquiv.toRingEquiv).toRatAlgEquiv,
    fun x ↦ ?_⟩
  have hx :
      (x : ℂ) = algebraMap (Algebra.adjoin K (Set.range ((↑) : s → ℂ))) ℂ (algebraMap K _ x) :=
    rfl
  rw [RingEquiv.coe_toRatAlgEquiv, hx, IsAlgClosure.equivOfEquiv_algebraMap]
  simp
  rfl

end IntermediateField
