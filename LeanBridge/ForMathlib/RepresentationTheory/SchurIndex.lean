import Mathlib.FieldTheory.Relrank
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.RepresentationTheory.CharacterTable.FieldOfValues
import TauCeti.RepresentationTheory.Induction.Cyclotomic.SplittingField

/-!
# The Schur index

Let `V` be a representation of a group `G` over a field `K`, with character `χ`, and let `F` be a
subfield of `K`. The field `F(χ)` generated over `F` by the values of `χ` is Tau Ceti's
`FDRep.characterField`. Every field `E` with `F(χ) ⊆ E ⊆ K` over which `V` is realized, in the
sense that `V ≃ K ⊗_E W` for a representation `W` of `G` over `E`, contains `F(χ)`, and the Schur
index of `χ` over `F` is the least degree `[E : F(χ)]` of such a field.

For an irreducible complex representation of a finite group, Brauer's theorem (Tau Ceti's
`FDRep.exists_simple_nonempty_iso_baseChange_adjoin_of_isPrimitiveRoot`) realizes `V` over the
cyclotomic field `ℚ(ζₑ)` of the exponent `e` of `G`, which has finite degree over `ℚ(χ)`; so the
Schur index over `ℚ` is a positive integer, attained by some field.

## Main definitions

* `FDRep.IsRealizedOver`: a representation is the scalar extension of a representation over an
  intermediate field.
* `FDRep.schurIndex` (LMFDB `group.representation.schur_index`).

## Main results

* `FDRep.schurIndex_eq_one_iff`: the Schur index is `1` exactly when the representation is realized
  over the field of character values.
* `FDRep.exists_relfinrank_eq_schurIndex`: a positive Schur index is the degree over `F(χ)` of a
  field over which the representation is realized.
* `FDRep.schurIndex_pos`: the Schur index over `ℚ` of an irreducible complex representation of a
  finite group is positive, so that it is attained.
-/

open CategoryTheory IntermediateField

namespace FDRep

section Field

variable {K G : Type*} [Field K] [Group G] (V : FDRep K G) (F : Type*) [Field F] [Algebra F K]

/-- A representation `V` of `G` over `K` is **realized over** an intermediate field `E` of `K / F`
if it is isomorphic to the scalar extension `K ⊗_E W` of a representation `W` of `G` over `E`. -/
def IsRealizedOver (E : IntermediateField F K) : Prop :=
  ∃ W : FDRep E G, Nonempty (FDRep.of (Representation.baseChange K W.ρ) ≅ V)

/-- The **Schur index** over `F` of the character `χ` of a representation `V` of `G` over `K`
(LMFDB `group.representation.schur_index`), for a subfield `F` of `K`: the least degree
`[E : F(χ)]` of an intermediate field `F(χ) ⊆ E ⊆ K` over which `V` is realized, where
`F(χ) = V.characterField F` is generated over `F` by the values of `χ`.

The LMFDB takes `K ⊆ ℂ`, a representation that is irreducible over `K`, and the minimum over all
such fields `E`. The minimum here runs over the fields of finite degree over `F(χ)`, which gives
the same value whenever one of them realizes `V`; when none does, the value is `0`. In the setting
of the LMFDB, irreducible complex representations of finite groups and `F = ℚ`, the Schur index is
positive (`FDRep.schurIndex_pos`), so the minimum is attained
(`FDRep.exists_relfinrank_eq_schurIndex`). -/
noncomputable def schurIndex : ℕ :=
  sInf {d | 0 < d ∧ ∃ E : IntermediateField F K, V.characterField F ≤ E ∧
    (V.characterField F).relfinrank E = d ∧ V.IsRealizedOver F E}

variable {V F}

/-- **A positive Schur index is attained**: it is the degree over `F(χ)` of a field
`F(χ) ⊆ E ⊆ K` over which the representation is realized. -/
lemma exists_relfinrank_eq_schurIndex (h : 0 < V.schurIndex F) : ∃ E : IntermediateField F K,
    V.characterField F ≤ E ∧ (V.characterField F).relfinrank E = V.schurIndex F ∧
      V.IsRealizedOver F E := by
  rcases Nat.sInf_mem (Nat.nonempty_of_pos_sInf h) with ⟨-, E, hE, hd, hV⟩
  exact ⟨E, hE, hd, hV⟩

/-- **The Schur index is `1` exactly when the representation is realized over its field of character
values.** -/
lemma schurIndex_eq_one_iff : V.schurIndex F = 1 ↔ V.IsRealizedOver F (V.characterField F) := by
  refine ⟨fun h ↦ ?_, fun h ↦ IsLeast.csInf_eq ⟨⟨one_pos, _, le_rfl, relfinrank_self _, h⟩,
    fun d hd ↦ hd.1⟩⟩
  rcases exists_relfinrank_eq_schurIndex (h ▸ one_pos) with ⟨E, hE, hd, hV⟩
  rw [h, relfinrank_eq_one_iff] at hd
  exact le_antisymm hd hE ▸ hV

end Field

section Complex

variable {G : Type} [Group G] [Finite G] (V : FDRep ℂ G) [Simple V]

/-- **The Schur index over `ℚ` of an irreducible complex representation of a finite group is
positive**: by Brauer's theorem the representation is realized over the cyclotomic field `ℚ(ζₑ)`
of the exponent `e` of `G`, which has finite degree over `ℚ(χ)`. -/
lemma schurIndex_pos : 0 < V.schurIndex ℚ := by
  have hn : Monoid.exponent G ≠ 0 := Monoid.exponent_ne_zero_of_finite
  rcases (⟨_, Complex.isPrimitiveRoot_exp _ hn⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ (Monoid.exponent G))
    with ⟨ζ, hζ⟩
  have : FiniteDimensional ℚ ℚ⟮ζ⟯ :=
    adjoin.finiteDimensional (hζ.isIntegral (Nat.pos_of_ne_zero hn)).tower_top
  have hle : V.characterField ℚ ≤ ℚ⟮ζ⟯ := V.characterField_le_adjoin_of_isPrimitiveRoot hζ
  have h : Module.finrank ℚ (V.characterField ℚ) * (V.characterField ℚ).relfinrank ℚ⟮ζ⟯ =
      Module.finrank ℚ ℚ⟮ζ⟯ := by
    rw [← relfinrank_bot_left, ← relfinrank_bot_left]
    exact relfinrank_mul_relfinrank bot_le hle
  have hζ' : Module.finrank ℚ ℚ⟮ζ⟯ ≠ 0 := Module.finrank_pos.ne'
  rw [← h] at hζ'
  rcases V.exists_simple_nonempty_iso_baseChange_adjoin_of_isPrimitiveRoot hζ with ⟨W, -, -, hW⟩
  exact (Nat.sInf_mem ⟨_, Nat.pos_of_ne_zero (right_ne_zero_of_mul hζ'), _, hle, rfl, W, hW⟩ :
    V.schurIndex ℚ ∈ _).1

end Complex

end FDRep
