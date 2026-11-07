import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.RealCount
import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Realizability
import TauCeti.RepresentationTheory.CharacterTable.Values

/-!
# The type of an irreducible complex representation

An irreducible complex representation `ρ` of a finite group is of one of three types (LMFDB
`group.representation.type`): **real** if it is conjugate to a representation by real matrices
(Tau Ceti's `Representation.IsRealizableOverReal`), **complex** if some character value `Tr ρ(g)`
is not real, and **quaternionic** (or **symplectic**) if the character values are all real but `ρ`
is not conjugate to a real representation. The types are exclusive, a representation realizable
over `ℝ` having real character values, and exhaustive.

The type is read off the Frobenius–Schur indicator `ν(ρ) = |G|⁻¹ ∑_g χ(g²)` (LMFDB
`artin.frobenius_schur_indicator`, Tau Ceti's `TauCeti.Representation.frobeniusSchurIndicator`),
which is `1`, `0` or `-1` (Tau Ceti's
`TauCeti.Representation.frobeniusSchurIndicator_eq_one_or_eq_zero_or_eq_neg_one`): `ν(ρ) = 1`
exactly in the real case (Tau Ceti's
`Representation.frobeniusSchurIndicator_eq_one_iff_isRealizableOverReal`), `ν(ρ) = 0` exactly in
the complex case, and `ν(ρ) = -1` exactly in the quaternionic case. The complex case comes from the
character table: `ρ` affords a row of the character table, whose indicator vanishes exactly when
inversion does not fix the row (Tau Ceti's `TauCeti.frobeniusSchurIndicatorRow_eq_zero_iff`), and
`χ(g⁻¹)` is the complex conjugate of `χ(g)`.

## Main definitions

* `Representation.IsComplexType` and `Representation.IsQuaternionicType` (LMFDB
  `group.representation.type`): the complex and the quaternionic types; the real type is Tau Ceti's
  `Representation.IsRealizableOverReal`.

## Main results

* `Representation.IsRealizableOverReal.not_isComplexType`: a representation of real type is not of
  complex type.
* `Representation.frobeniusSchurIndicator_eq_zero_iff_isComplexType` (LMFDB
  `group.representation.type`): `ν(ρ) = 0` exactly when `ρ` is of complex type.
* `Representation.frobeniusSchurIndicator_eq_neg_one_iff_isQuaternionicType` (LMFDB
  `group.representation.type`): `ν(ρ) = -1` exactly when `ρ` is of quaternionic type.
-/

open TauCeti Representation

namespace Representation

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- An irreducible complex representation `ρ` is of **complex** type (LMFDB
`group.representation.type`) if some character value `Tr ρ(g)` is not real. For a finite group
this is exactly when the Frobenius–Schur indicator vanishes
(`Representation.frobeniusSchurIndicator_eq_zero_iff_isComplexType`). -/
def IsComplexType : Prop :=
  ∃ g : G, (ρ.character g).im ≠ 0

/-- An irreducible complex representation `ρ` is of **quaternionic** (or **symplectic**) type (LMFDB
`group.representation.type`) if its character values are all real but it is not conjugate to a
representation by real matrices (Tau Ceti's `Representation.IsRealizableOverReal`). For a finite
group this is exactly when the Frobenius–Schur indicator is `-1`
(`Representation.frobeniusSchurIndicator_eq_neg_one_iff_isQuaternionicType`). -/
def IsQuaternionicType : Prop :=
  (∀ g : G, (ρ.character g).im = 0) ∧ ¬ρ.IsRealizableOverReal

variable {ρ}

/-- **A representation of real type is not of complex type**: its character is the character of a
real form, so it takes real values. -/
lemma IsRealizableOverReal.not_isComplexType (h : ρ.IsRealizableOverReal) : ¬ρ.IsComplexType := by
  rintro ⟨g, hg⟩
  rcases h with ⟨σ, hσ⟩
  exact hg <| by rw [hσ.char_eq g, Complex.ofReal_im]

variable (ρ) [Fintype G] [ρ.IsIrreducible]

/-- **An irreducible complex representation of a finite group has Frobenius–Schur indicator `0`
exactly when it is of complex type** (LMFDB `group.representation.type`), that is, when some
character value is not real. -/
lemma frobeniusSchurIndicator_eq_zero_iff_isComplexType :
    frobeniusSchurIndicator ρ = 0 ↔ ρ.IsComplexType := by
  have : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional ‹_›
  rcases exists_irreducibleCharacter_eq ℂ (character_mem_irreducibleCharacters ρ) with ⟨i, hi⟩
  have hν : frobeniusSchurIndicator ρ = frobeniusSchurIndicatorRow ℂ i := by
    rw [frobeniusSchurIndicatorRow_def, frobeniusSchurIndicator_def, frobeniusSchurIndicator_def,
      character_irreducibleRepresentation, hi]
  rw [hν, frobeniusSchurIndicatorRow_eq_zero_iff, forall_characterTable_inv_iff, hi, IsComplexType,
    not_forall]
  refine exists_congr fun g ↦ ?_
  rw [← conj_char, Complex.conj_eq_iff_im]

/-- **An irreducible complex representation of a finite group has Frobenius–Schur indicator `-1`
exactly when it is of quaternionic type** (LMFDB `group.representation.type`), that is, when its
character values are real but it is not realizable over `ℝ`. -/
lemma frobeniusSchurIndicator_eq_neg_one_iff_isQuaternionicType :
    frobeniusSchurIndicator ρ = -1 ↔ ρ.IsQuaternionicType := by
  have : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional ‹_›
  have h :
      ρ.IsQuaternionicType ↔ frobeniusSchurIndicator ρ ≠ 0 ∧ frobeniusSchurIndicator ρ ≠ 1 := by
    rw [IsQuaternionicType, ne_eq, ne_eq, frobeniusSchurIndicator_eq_zero_iff_isComplexType,
      frobeniusSchurIndicator_eq_one_iff_isRealizableOverReal, IsComplexType, not_exists]
    simp only [not_not]
  rw [h]
  rcases frobeniusSchurIndicator_eq_one_or_eq_zero_or_eq_neg_one ρ with hν | hν | hν <;>
    norm_num [hν]

end Representation
