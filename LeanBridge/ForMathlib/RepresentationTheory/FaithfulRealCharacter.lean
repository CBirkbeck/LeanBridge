import LeanBridge.ForMathlib.RepresentationTheory.CharacterLabel
import LeanBridge.ForMathlib.RepresentationTheory.FaithfulRationalCharacter

/-!
# Faithfulness of real Galois-orbit sums of characters

For a field `k` that is not algebraically closed, summing a complex character `χ` over its Galois
orbit gives a character with values in `k` (LMFDB `group.min_faithful_linear`), and the sum is
faithful exactly when each summand is. Besides `k = ℚ` (LeanBridge's `FDRep.rationalCharacter`),
the LMFDB tabulates the degrees over `k = ℝ`. The Galois group `Gal(ℂ/ℝ)` consists of the identity
and complex conjugation, so the orbit of `χ` is `{χ, χ̄}`, and its sum `FDRep.realCharacter` is `χ`
when `χ` is real valued and `χ + χ̄` otherwise. It is the character of a representation, the direct
sum of representations affording `χ` and `χ̄`, and it is real valued, being fixed by conjugation.

Faithfulness is the case `Gal(ℂ/ℝ)` of `FDRep.sum_faithful_iff` (`FaithfulRationalCharacter.lean`),
for the sum over any set of Galois conjugates `σ ∘ χ` of an irreducible character `χ`, `σ` an
automorphism of `ℂ`, containing `χ`. Each summand `σ ∘ χ` is faithful exactly when `χ` is, `σ`
being injective and fixing `χ(1)`.

## Main definitions

* `FDRep.realGaloisConjugates`, `FDRep.realCharacter` (LMFDB `group.min_faithful_linear`): the
  conjugates of a complex character under `Gal(ℂ/ℝ)` and their sum.

## Main results

* `FDRep.realCharacter_eq_of_conj_comp_eq`, `FDRep.realCharacter_eq_add` (LMFDB
  `group.min_faithful_linear`): the real orbit sum is `χ` or `χ + χ̄`.
* `FDRep.exists_real_character_eq_realCharacter` (LMFDB `group.min_faithful_linear`): the real orbit
  sum of an irreducible character is a real valued character.
* `FDRep.realCharacter_faithful_iff` (LMFDB `group.min_faithful_linear`): it is faithful exactly
  when the character is.
* `FDRep.faithful_iff_of_mem_realGaloisConjugates` (LMFDB `group.min_faithful_linear`): each
  summand is faithful exactly when the character is.
-/

open TauCeti

namespace FDRep

variable {G : Type} [Group G] (X : FDRep ℂ G)

/-- The **conjugates over `ℝ`** of the character `χ` of `X` (LMFDB `group.min_faithful_linear`):
the functions `σ ∘ χ` for `σ ∈ Gal(ℂ/ℝ)`, that is `χ` and its complex conjugate `χ̄`. -/
noncomputable def realGaloisConjugates : Set (G → ℂ) :=
  Set.range fun σ : ℂ ≃ₐ[ℝ] ℂ ↦ σ ∘ X.character

/-- The **real orbit sum** of the character `χ` of `X` (LMFDB `group.min_faithful_linear`): the sum
of the distinct conjugates of `χ` under `Gal(ℂ/ℝ)`, which is `χ` when `χ` is real valued and
`χ + χ̄` otherwise. -/
noncomputable def realCharacter : G → ℂ :=
  ∑ᶠ ψ ∈ X.realGaloisConjugates, ψ

lemma realGaloisConjugates_eq :
    X.realGaloisConjugates = {X.character, starRingEnd ℂ ∘ X.character} := by
  ext ψ
  refine ⟨?_, ?_⟩
  · rintro ⟨σ, rfl⟩
    rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with h | h
    · exact .inl (funext fun g ↦ congrArg (· (X.character g)) h)
    · exact .inr (funext fun g ↦ congrArg (· (X.character g)) h)
  · rintro (rfl | rfl)
    · exact ⟨1, rfl⟩
    · exact ⟨Complex.conjAe, rfl⟩

lemma finite_realGaloisConjugates : X.realGaloisConjugates.Finite :=
  Set.finite_range _

lemma realGaloisConjugates_subset_galoisConjugates : X.realGaloisConjugates ⊆ X.galoisConjugates :=
  fun _ ⟨σ, hσ⟩ ↦ ⟨σ.restrictScalars ℚ, hσ⟩

/-- **The real orbit sum of a real valued character is the character.** -/
lemma realCharacter_eq_of_conj_comp_eq (h : starRingEnd ℂ ∘ X.character = X.character) :
    X.realCharacter = X.character := by
  rw [realCharacter, realGaloisConjugates_eq, h, Set.pair_eq_singleton, finsum_mem_singleton]

/-- **The real orbit sum of a character that is not real valued is `χ + χ̄`.** -/
lemma realCharacter_eq_add (h : starRingEnd ℂ ∘ X.character ≠ X.character) :
    X.realCharacter = X.character + starRingEnd ℂ ∘ X.character := by
  rw [realCharacter, realGaloisConjugates_eq, finsum_mem_pair (Ne.symm h)]

lemma conj_realCharacter_apply (g : G) : starRingEnd ℂ (X.realCharacter g) = X.realCharacter g := by
  by_cases h : starRingEnd ℂ ∘ X.character = X.character
  · rw [X.realCharacter_eq_of_conj_comp_eq h]
    exact congrFun h g
  · rw [X.realCharacter_eq_add h, Pi.add_apply, Function.comp_apply, map_add, Complex.conj_conj,
      add_comm]

/-- **Each summand of the real orbit sum is faithful exactly when the character is** (LMFDB
`group.min_faithful_linear`), so the real orbit sum is faithful exactly when each of its summands
is. -/
lemma faithful_iff_of_mem_realGaloisConjugates {ψ : G → ℂ} (hψ : ψ ∈ X.realGaloisConjugates) :
    (∀ g, ψ g = ψ 1 → g = 1) ↔ ∀ g, X.character g = X.character 1 → g = 1 := by
  rcases X.realGaloisConjugates_subset_galoisConjugates hψ with ⟨σ, rfl⟩
  exact X.algEquiv_comp_faithful_iff σ

variable [Finite G] [CategoryTheory.Simple X]

/-- **The real orbit sum of an irreducible character is a real valued character** (LMFDB
`group.min_faithful_linear`): it is the character of the direct sum of representations affording
`χ` and, when it differs, `χ̄`, and its values are real, being fixed by complex conjugation. -/
lemma exists_real_character_eq_realCharacter :
    ∃ Y : FDRep ℂ G, (∀ g, ∃ r : ℝ, Y.character g = r) ∧ Y.character = X.realCharacter := by
  have hχ : X.character ∈ X.finite_realGaloisConjugates.toFinset :=
    X.finite_realGaloisConjugates.mem_toFinset.mpr ⟨1, rfl⟩
  rcases exists_character_eq_sum ⟨X.character, hχ⟩ fun ψ hψ ↦ by
      rcases X.realGaloisConjugates_subset_galoisConjugates
        (X.finite_realGaloisConjugates.mem_toFinset.mp hψ) with ⟨σ, rfl⟩
      rcases mem_irreducibleCharacters_iff.mp <| algEquiv_comp_mem_irreducibleCharacters σ
        X.character_mem_irreducibleCharacters with ⟨n, ρ, -, hρ⟩
      exact ⟨FDRep.of ρ, (character_of ρ).trans hρ⟩ with ⟨Y, hY⟩
  rw [← finsum_mem_eq_finite_toFinset_sum _ X.finite_realGaloisConjugates] at hY
  refine ⟨Y, fun g ↦ Complex.conj_eq_iff_real.mp ?_, hY⟩
  rw [hY]
  exact X.conj_realCharacter_apply g

/-- **The real orbit sum of an irreducible complex character is faithful exactly when the
character is** (LMFDB `group.min_faithful_linear`). -/
lemma realCharacter_faithful_iff : (∀ g, X.realCharacter g = X.realCharacter 1 → g = 1) ↔
    ∀ g, X.character g = X.character 1 → g = 1 :=
  X.sum_faithful_iff X.realGaloisConjugates_subset_galoisConjugates ⟨1, rfl⟩

end FDRep
