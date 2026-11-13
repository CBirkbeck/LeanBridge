import LeanBridge.ForMathlib.RepresentationTheory.FaithfulIrreducibleCharacter
import LeanBridge.ForMathlib.RepresentationTheory.RationalCharacterBasis
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.RingTheory.IntegralDomain

/-!
# The degrees `lin_ℂ(G)` and `irr_ℂ(G)` from the irreducible characters

The linear degree `lin_ℂ(G)` of a finite group (LMFDB `group.min_faithful_linear`, LeanBridge's
`linearDegree`) is the least `n` with a faithful matrix representation `G ↪ GL_n(ℂ)`. Unlike the
irreducible degree `irr_ℂ(G)`, it is not the degree of a single row of the character table: it
is the least degree `∑ mᵢ χᵢ(1)` of a faithful combination `∑ mᵢ χᵢ` of the irreducible characters
with coefficients `mᵢ ∈ ℕ`, a character being faithful when `χ(g) = χ(1)` only for `g = 1`. A
representation of degree `n` has a character `∑ mᵢ χᵢ` with `∑ mᵢ χᵢ(1) = n`, the `mᵢ` being the
multiplicities of the irreducible representations in it; conversely the direct sum of `mᵢ` copies
of the representation affording `χᵢ` has character `∑ mᵢ χᵢ`; and a representation is faithful
exactly when its character is (`Representation.injective_iff_character_eq_character_one`).

There may be no faithful irreducible representation, in which case `irr_ℂ(G) = -1`. This happens
for every finite abelian group `G` that is not cyclic: its irreducible complex representations
are one-dimensional, and a faithful one embeds `G` into `ℂˣ`, whose finite subgroups are cyclic.
The Klein four-group `C₂ × C₂` is the smallest example.

## Main results

* `isCyclic_of_injective_of_isIrreducible`: a finite abelian group with a faithful irreducible
  complex representation is cyclic.
* `irreducibleDegree_complex_eq_neg_one_of_not_isCyclic` (LMFDB `group.min_faithful_linear`): a
  finite abelian group that is not cyclic has `irr_ℂ(G) = -1`.
* `IsKleinFour.irreducibleDegree_complex_eq_neg_one` (LMFDB `group.min_faithful_linear`): the
  Klein four-group has no faithful irreducible complex representation.
* `exists_injective_iff_exists_nsmul_sum` (LMFDB `group.min_faithful_linear`): `G` has a faithful
  representation of degree `n` over `ℂ` exactly when some `ℕ`-combination of the irreducible
  characters of degree `n` is faithful.
* `linearDegree_complex_eq` (LMFDB `group.min_faithful_linear`): `lin_ℂ(G)` is the least degree of
  a faithful `ℕ`-combination of the irreducible characters.
-/

open Matrix Module Representation TauCeti

variable {G : Type} [Group G] {n : ℕ}

/-- **A finite abelian group with a faithful irreducible complex representation is cyclic**: the
representation is one-dimensional (Schur's lemma), so it embeds `G` into `ℂˣ`. -/
lemma isCyclic_of_injective_of_isIrreducible [Finite G] [IsMulCommutative G] {ρ : G →* GL (Fin n) ℂ}
    (hρ : Function.Injective ρ) (hirr : (GeneralLinearGroup.representation ρ).IsIrreducible) :
    IsCyclic G := by
  have hn : n = 1 := (finrank_fin_fun ℂ).symm.trans <|
    IsIrreducible.finrank_eq_one_of_isMulCommutative (GeneralLinearGroup.representation ρ)
  subst hn
  refine isCyclic_of_injective_ringHom ((Units.coeHom ℂ).comp (GeneralLinearGroup.det.comp ρ))
    fun g h hgh ↦ hρ <| Units.ext <| Matrix.ext fun i j ↦ ?_
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simpa using hgh

/-- **A finite abelian group that is not cyclic has no faithful irreducible complex
representation** (LMFDB `group.min_faithful_linear`), so its irreducible degree is
`irr_ℂ(G) = -1`. -/
lemma irreducibleDegree_complex_eq_neg_one_of_not_isCyclic [Finite G] [IsMulCommutative G]
    (hG : ¬IsCyclic G) : irreducibleDegree ℂ G = -1 := by
  rw [irreducibleDegree,
    dite_eq_right fun ⟨_, _, hρ, hirr⟩ ↦ hG (isCyclic_of_injective_of_isIrreducible hρ hirr)]

/-- **The Klein four-group has no faithful irreducible complex representation** (LMFDB
`group.min_faithful_linear`): `irr_ℂ(C₂ × C₂) = -1`, while it has faithful representations, for
instance its regular representation. -/
lemma IsKleinFour.irreducibleDegree_complex_eq_neg_one [IsKleinFour G] :
    irreducibleDegree ℂ G = -1 :=
  have : Finite G := instFinite
  have : IsMulCommutative G := isMulCommutative
  irreducibleDegree_complex_eq_neg_one_of_not_isCyclic not_isCyclic

namespace FDRep

lemma character_trivial_fin_zero :
    (FDRep.of (Representation.trivial ℂ G (Fin 0 → ℂ))).character = 0 :=
  funext fun g ↦ by
    rw [character_of, Representation.char_trivial, finrank_fin_fun, Nat.cast_zero, Pi.zero_apply]

lemma exists_character_eq_nsmul (X : FDRep ℂ G) (m : ℕ) :
    ∃ Y : FDRep ℂ G, Y.character = m • X.character := by
  induction m with
  | zero => exact ⟨_, character_trivial_fin_zero.trans (zero_nsmul _).symm⟩
  | succ m ih =>
    rcases ih with ⟨Y, hY⟩
    exact ⟨Y ⊞ X, by rw [char_biprod, hY, succ_nsmul]⟩

lemma exists_character_eq_sum_nsmul {ι : Type*} (s : Finset ι) (m : ι → ℕ) (X : ι → FDRep ℂ G) :
    ∃ Y : FDRep ℂ G, Y.character = ∑ i ∈ s, m i • (X i).character := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨_, character_trivial_fin_zero.trans Finset.sum_empty.symm⟩
  | insert i s hi ih =>
    rcases ih with ⟨Y, hY⟩
    rcases (X i).exists_character_eq_nsmul (m i) with ⟨Z, hZ⟩
    exact ⟨Z ⊞ Y, by rw [char_biprod, hZ, hY, Finset.sum_insert hi]⟩

lemma exists_representation_character_eq (Y : FDRep ℂ G) : ∃ ρ : G →* GL (Fin (finrank ℂ Y)) ℂ,
    (GeneralLinearGroup.representation ρ).character = Y.character := by
  let e : Y ≃ₗ[ℂ] (Fin (finrank ℂ Y) → ℂ) := (Module.finBasis ℂ Y).equivFun
  let τ : Representation ℂ G (Fin (finrank ℂ Y) → ℂ) := (e.conjAlgEquiv ℂ).toMonoidHom.comp Y.ρ
  let ρ : G →* GL (Fin (finrank ℂ Y)) ℂ :=
    GeneralLinearGroup.toLin.symm.toMonoidHom.comp τ.asGroupHom
  have hρ : GeneralLinearGroup.representation ρ = τ := by
    ext g : 1
    simp [GeneralLinearGroup.representation, ρ, Representation.asGroupHom_apply]
  refine ⟨ρ, funext fun g ↦ ?_⟩
  rw [hρ]
  exact LinearMap.trace_conj' (Y.ρ g) e

end FDRep

variable [Finite G]

/-- **The faithful representations of `G` over `ℂ` are read off the `ℕ`-combinations of the
irreducible characters** (LMFDB `group.min_faithful_linear`): `G` has a faithful matrix
representation of degree `n` exactly when, for some `mᵢ ∈ ℕ` with `∑ mᵢ χᵢ(1) = n`, the character
`ψ = ∑ mᵢ χᵢ` is faithful, `ψ(g) = n` only for `g = 1`. -/
lemma exists_injective_iff_exists_nsmul_sum : (∃ ρ : G →* GL (Fin n) ℂ, Function.Injective ρ) ↔
    ∃ m : Fin (Nat.card (ConjClasses G)) → ℕ, ∑ i, m i * characterDegree ℂ i = n ∧ ∀ g : G,
      (∑ i, m i • irreducibleCharacter ℂ i) g = n → g = 1 := by
  refine ⟨fun ⟨ρ, hρ⟩ ↦ ?_, fun ⟨m, hn, hm⟩ ↦ ?_⟩
  · let X : FDRep ℂ G := FDRep.of (GeneralLinearGroup.representation ρ)
    let m : Fin (Nat.card (ConjClasses G)) → ℕ :=
      fun i ↦ finrank ℂ (IntertwiningMap X.ρ (irreducibleRepresentation ℂ i))
    have hX : X.character = ∑ i, m i • irreducibleCharacter ℂ i :=
      character_eq_sum_nsmul_irreducibleCharacter X
    have h1 : X.character 1 = n := by
      rw [FDRep.char_one]
      exact congrArg Nat.cast (finrank_fin_fun ℂ)
    refine ⟨m, ?_, fun g hg ↦ ?_⟩
    · rw [hX] at h1
      simp only [nsmul_eq_mul, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply,
        irreducibleCharacter_one] at h1
      exact_mod_cast h1
    · refine (Representation.injective_iff_character_eq_character_one _).mp
        ((GeneralLinearGroup.injective_representation_iff ρ).mpr hρ) g ?_
      rw [← FDRep.character_of, h1, hX, hg]
  · rcases FDRep.exists_character_eq_sum_nsmul Finset.univ m
      (fun i ↦ FDRep.of (irreducibleRepresentation ℂ i)) with ⟨Y, hY⟩
    simp only [FDRep.character_of, character_irreducibleRepresentation] at hY
    have h1 : Y.character 1 = n := by
      rw [hY, ← hn]
      simp
    have hdim : finrank ℂ Y = n := by
      rw [FDRep.char_one] at h1
      exact_mod_cast h1
    subst hdim
    rcases Y.exists_representation_character_eq with ⟨ρ, hρ⟩
    refine ⟨ρ, (GeneralLinearGroup.injective_representation_iff ρ).mp <|
      (Representation.injective_iff_character_eq_character_one _).mpr fun g hg ↦ hm g ?_⟩
    rw [hρ, h1] at hg
    rw [← hY, hg]

/-- **The linear degree `lin_ℂ(G)` is the least degree of a faithful `ℕ`-combination of the
irreducible characters** (LMFDB `group.min_faithful_linear`): `lin_ℂ(G)` is the least
`∑ mᵢ χᵢ(1)`, `mᵢ ∈ ℕ`, such that `ψ = ∑ mᵢ χᵢ` is faithful, `ψ(g) = ψ(1)` only for `g = 1`. -/
lemma linearDegree_complex_eq : linearDegree ℂ G = sInf {n |
    ∃ m : Fin (Nat.card (ConjClasses G)) → ℕ, ∑ i, m i * characterDegree ℂ i = n ∧ ∀ g : G,
      (∑ i, m i • irreducibleCharacter ℂ i) g = n → g = 1} :=
  congrArg sInf <| Set.ext fun _ ↦ exists_injective_iff_exists_nsmul_sum
