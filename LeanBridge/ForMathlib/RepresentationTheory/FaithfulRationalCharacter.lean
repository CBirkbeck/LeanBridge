import LeanBridge.ForMathlib.RepresentationTheory.RationalCharacterBasis
import TauCeti.RepresentationTheory.CharacterTable.Values

/-!
# Faithfulness of Galois-orbit sums of characters

For a field `k` that is not algebraically closed, summing a complex character `χ` over its Galois
orbit gives a character with values in `k` (LMFDB `group.min_faithful_linear`). For `k = ℚ`, the
case of the LMFDB's rational degrees, the sum over the conjugates `σ ∘ χ`, `σ ∈ Aut(ℂ)`, is
LeanBridge's `FDRep.rationalCharacter`, the character of a representation with values in `ℚ`
(`FDRep.exists_isRationalCharacter_character_eq_rationalCharacter`). A character `ψ` is faithful in
the knowl's sense when `ψ(g) = ψ(1)` only for `g = 1`. Each conjugate `σ ∘ χ` is faithful exactly
when `χ` is, `σ` being injective and fixing `χ(1)`. So is the sum: if `∑ σχ(g) = ∑ σχ(1)`, then
since every `σ ∘ χ` is the character of a representation, `Re σχ(g) ≤ |σχ(g)| ≤ χ(1)`, so all
these inequalities are equalities, and `χ(g) = χ(1)`. The real case, the sums `χ + χ̄` behind the
LMFDB's real degrees, is treated in `FaithfulRealCharacter.lean`.

## Main results

* `FDRep.algEquiv_comp_faithful_iff` (LMFDB `group.min_faithful_linear`): a Galois conjugate of a
  character is faithful exactly when the character is.
* `FDRep.rationalCharacter_faithful_iff` (LMFDB `group.min_faithful_linear`): the sum of the Galois
  conjugates of an irreducible complex character is faithful exactly when the character is.
-/

open TauCeti

namespace FDRep

variable {G : Type} [Group G] (X : FDRep ℂ G) (σ : ℂ ≃ₐ[ℚ] ℂ)

/-- **A Galois conjugate `σ ∘ χ` of a character `χ` is faithful exactly when `χ` is** (LMFDB
`group.min_faithful_linear`), `σ` being injective. -/
lemma algEquiv_comp_faithful_iff :
    (∀ g, (σ ∘ X.character) g = (σ ∘ X.character) 1 → g = 1) ↔
      ∀ g, X.character g = X.character 1 → g = 1 :=
  forall_congr' fun _ ↦ imp_congr_left σ.injective.eq_iff

variable [Finite G] [CategoryTheory.Simple X]

lemma norm_algEquiv_character_le (g : G) : ‖σ (X.character g)‖ ≤ Module.finrank ℂ X := by
  rcases mem_irreducibleCharacters_iff.mp
    (algEquiv_comp_mem_irreducibleCharacters σ X.character_mem_irreducibleCharacters) with
    ⟨n, ρ, -, hρ⟩
  have hn : n = Module.finrank ℂ X := by
    have h : ρ.character 1 = (σ ∘ X.character) 1 := congrFun hρ 1
    rw [Representation.char_one, Module.finrank_fin_fun, Function.comp_apply, char_one,
      map_natCast] at h
    exact_mod_cast h
  have h : ‖ρ.character g‖ ≤ Module.finrank ℂ (Fin n → ℂ) :=
    Representation.norm_char_le_finrank ρ (orderOf_pos g).ne' (pow_orderOf_eq_one g)
  rwa [hρ, Module.finrank_fin_fun, hn] at h

/-- **The sum of the Galois conjugates of an irreducible complex character is faithful exactly when
the character is** (LMFDB `group.min_faithful_linear`): if `∑ σχ(g) = ∑ σχ(1)`, the bounds
`Re σχ(g) ≤ |σχ(g)| ≤ χ(1)` are equalities, so `χ(g) = χ(1)`. -/
lemma rationalCharacter_faithful_iff :
    (∀ g, X.rationalCharacter g = X.rationalCharacter 1 → g = 1) ↔
      ∀ g, X.character g = X.character 1 → g = 1 := by
  rw [rationalCharacter, finsum_mem_eq_finite_toFinset_sum _ X.finite_galoisConjugates]
  have hmem (ψ : G → ℂ) (hψ : ψ ∈ X.finite_galoisConjugates.toFinset) :
      ∃ σ : ℂ ≃ₐ[ℚ] ℂ, σ ∘ X.character = ψ :=
    X.finite_galoisConjugates.mem_toFinset.mp hψ
  have hχ : X.character ∈ X.finite_galoisConjugates.toFinset :=
    X.finite_galoisConjugates.mem_toFinset.mpr ⟨1, rfl⟩
  refine ⟨fun h g hg ↦ h g ?_, fun h g hg ↦ h g ?_⟩
  · simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun ψ hψ ↦ ?_
    rcases hmem ψ hψ with ⟨σ, rfl⟩
    simp [hg]
  · have hle (ψ : G → ℂ) (hψ : ψ ∈ X.finite_galoisConjugates.toFinset) :
        (ψ g).re ≤ (ψ 1).re := by
      rcases hmem ψ hψ with ⟨σ, rfl⟩
      rw [Function.comp_apply, Function.comp_apply, char_one, map_natCast, Complex.natCast_re]
      exact (Complex.re_le_norm _).trans (X.norm_algEquiv_character_le σ g)
    have hsum : ∑ ψ ∈ X.finite_galoisConjugates.toFinset, (ψ g).re =
        ∑ ψ ∈ X.finite_galoisConjugates.toFinset, (ψ 1).re := by
      simpa using congrArg Complex.re hg
    have hre : (X.character g).re = (X.character 1).re :=
      (Finset.sum_eq_sum_iff_of_le hle).mp hsum _ hχ
    have hnorm : ‖X.character g‖ ≤ (X.character 1).re := by
      rw [char_one, Complex.natCast_re]
      exact X.norm_char_le_finrank g
    have hsq : ‖X.character g‖ ^ 2 = (X.character g).re ^ 2 + (X.character g).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring1
    refine Complex.ext hre ?_
    rw [char_one, Complex.natCast_im]
    nlinarith [norm_nonneg (X.character g), sq_nonneg (X.character g).im]

end FDRep
