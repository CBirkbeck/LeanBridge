import TauCeti.RepresentationTheory.Induction.Monomial

/-!
# Monomial groups (M-groups)

## Main definitions

* `IsMGroup` (LMFDB `group.monomial`).

## Main results

* `IsMGroup.of_isNilpotent`: finite nilpotent groups are M-groups, from Tau Ceti's
  `FDRep.exists_nonempty_iso_indFDRep_ofLinearCharacter_of_isNilpotent`.
-/

open CategoryTheory TauCeti

variable (G : Type) [Group G] [Finite G]

/-- A finite group `G` is **monomial**, or an **M-group** (LMFDB `group.monomial`), if every
complex irreducible representation of `G` is induced from a one-dimensional representation
`χ : H →* ℂˣ` of some subgroup `H`. -/
class IsMGroup : Prop where
  exists_iso_indFDRep (W : FDRep ℂ G) [Simple W] :
    ∃ (H : Subgroup G) (χ : H →* ℂˣ), Nonempty (W ≅ indFDRep (FDRep.ofLinearCharacter χ))

variable {G}

/-- Finite nilpotent groups are M-groups. -/
lemma IsMGroup.of_isNilpotent [Group.IsNilpotent G] : IsMGroup G :=
  ⟨fun W _ ↦ FDRep.exists_nonempty_iso_indFDRep_ofLinearCharacter_of_isNilpotent W⟩
