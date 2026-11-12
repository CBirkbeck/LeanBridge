import LeanBridge.ForMathlib.RepresentationTheory.FaithfulCharacter
import LeanBridge.ForMathlib.RepresentationTheory.FaithfulDegree
import TauCeti.RepresentationTheory.CharacterTable.Table

/-!
# The irreducible degree `irr_ℂ(G)` from the character table

The irreducible degree `irr_ℂ(G)` of a finite group (LMFDB `group.min_faithful_linear`,
LeanBridge's `irreducibleDegree`) is the least `n` with a faithful irreducible matrix
representation `G ↪ GL_n(ℂ)`, or `-1` if there is none. It can be read off the character table:
a faithful irreducible representation of degree `n` exists exactly when some row `χ` of the
character table (Tau Ceti's `TauCeti.irreducibleCharacter ℂ i`) has degree `χ(1) = n` and is
faithful, `χ(g) = n` only for `g = 1`. The character of an irreducible matrix representation is a
row of the table, the row `χ` is afforded by Tau Ceti's irreducible representation on `ℂ^{χ(1)}`,
and a representation in characteristic `0` is faithful exactly when its character is
(`Representation.injective_iff_character_eq_character_one`).

## Main results

* `exists_injective_isIrreducible_iff` (LMFDB `group.min_faithful_linear`): `G` has a faithful
  irreducible representation of degree `n` over `ℂ` exactly when the character table has a
  faithful row of degree `n`.
* `irreducibleDegree_complex_eq` (LMFDB `group.min_faithful_linear`): `irr_ℂ(G)` is the least
  degree of a faithful row of the character table, or `-1` if there is none.
-/

open Matrix TauCeti

variable {G : Type*} [Group G] {n : ℕ}

namespace Matrix.GeneralLinearGroup

lemma injective_representation_iff {R : Type*} [CommRing R] (ρ : G →* GL (Fin n) R) :
    Function.Injective (representation ρ) ↔ Function.Injective ρ :=
  ⟨fun h g g' hgg' ↦ h (by simp only [representation, MonoidHom.comp_apply, hgg']),
    fun h g g' hgg' ↦ h (toLin.injective (Units.ext hgg'))⟩

end Matrix.GeneralLinearGroup

variable [Finite G]

/-- **The faithful irreducible representations of `G` over `ℂ` are read off the character table**
(LMFDB `group.min_faithful_linear`): `G` has a faithful irreducible matrix representation of degree
`n` exactly when some irreducible character `χ` has degree `n` and `χ(g) = n` only for `g = 1`. -/
lemma exists_injective_isIrreducible_iff :
    (∃ ρ : G →* GL (Fin n) ℂ, Function.Injective ρ ∧
      (GeneralLinearGroup.representation ρ).IsIrreducible) ↔
      ∃ i, characterDegree ℂ i = n ∧ ∀ g : G, irreducibleCharacter ℂ i g = n → g = 1 := by
  refine ⟨fun ⟨ρ, hinj, hirr⟩ ↦ ?_, fun ⟨i, hn, hi⟩ ↦ ?_⟩
  · rcases exists_irreducibleCharacter_eq (k := ℂ)
      (f := (GeneralLinearGroup.representation ρ).character) ⟨n, _, hirr, rfl⟩ with ⟨i, hi⟩
    have hdeg : characterDegree ℂ i = n := by
      have h : irreducibleCharacter ℂ i 1 = (GeneralLinearGroup.representation ρ).character 1 :=
        congrFun hi 1
      rw [irreducibleCharacter_one, Representation.char_one, Module.finrank_fin_fun] at h
      exact_mod_cast h
    refine ⟨i, hdeg, fun g hg ↦ ?_⟩
    refine (Representation.injective_iff_character_eq_character_one _).mp
      ((GeneralLinearGroup.injective_representation_iff ρ).mpr hinj) g ?_
    rw [← hi, hg, irreducibleCharacter_one, hdeg]
  · subst hn
    let τ : Representation ℂ G (Fin (characterDegree ℂ i) → ℂ) := irreducibleRepresentation ℂ i
    let ρ : G →* GL (Fin (characterDegree ℂ i)) ℂ :=
      GeneralLinearGroup.toLin.symm.toMonoidHom.comp τ.asGroupHom
    have hρ : GeneralLinearGroup.representation ρ = τ := by
      ext g : 1
      simp [GeneralLinearGroup.representation, ρ, Representation.asGroupHom_apply]
    have hτ : Function.Injective τ :=
      (Representation.injective_iff_character_eq_character_one τ).mpr fun g hg ↦ hi g <| by
        rwa [character_irreducibleRepresentation, irreducibleCharacter_one] at hg
    exact ⟨ρ, (GeneralLinearGroup.injective_representation_iff ρ).mp (hρ ▸ hτ),
      hρ ▸ inferInstance⟩

open scoped Classical in
/-- **The irreducible degree `irr_ℂ(G)` is the least degree of a faithful row of the character
table**, and `-1` if no row is faithful (LMFDB `group.min_faithful_linear`). -/
lemma irreducibleDegree_complex_eq : irreducibleDegree ℂ G = if h : ∃ n i,
    characterDegree ℂ i = n ∧ ∀ g : G, irreducibleCharacter ℂ i g = n → g = 1 then
      (Nat.find h : ℤ) else -1 := by
  rw [irreducibleDegree]
  by_cases h : ∃ n : ℕ, ∃ ρ : G →* GL (Fin n) ℂ, Function.Injective ρ ∧
      (GeneralLinearGroup.representation ρ).IsIrreducible
  · have h' : ∃ n i, characterDegree ℂ i = n ∧ ∀ g : G, irreducibleCharacter ℂ i g = n → g = 1 :=
      h.imp fun _ ↦ exists_injective_isIrreducible_iff.mp
    rw [dite_eq_left h, dite_eq_left h', Nat.cast_inj]
    exact le_antisymm (Nat.find_mono fun _ ↦ exists_injective_isIrreducible_iff.mpr)
      (Nat.find_mono fun _ ↦ exists_injective_isIrreducible_iff.mp)
  · rw [dite_eq_right h,
      dite_eq_right fun h' ↦ h (h'.imp fun _ ↦ exists_injective_isIrreducible_iff.mpr)]
