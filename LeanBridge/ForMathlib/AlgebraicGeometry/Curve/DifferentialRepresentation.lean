import Mathlib.RepresentationTheory.Character
import TauCeti.FieldTheory.FunctionField.Differential.Automorphism
import TauCeti.FieldTheory.FunctionField.Differential.Dimension

/-!
# The representation of a group of automorphisms on the holomorphic differentials

A group `G` acting on a curve `X` of genus `g` over `ℂ` (LMFDB
`curve.highergenus.aut.group_action`) acts on the `g`-dimensional complex vector space of
holomorphic differentials of `X`, which gives a representation of `G` (LMFDB
`curve.highergenus.aut.characters`). We formalise this representation and its character over the
function field `F` of the curve, over a field of constants `k`, for any group `G` acting on `F` by
automorphisms over `k`; a group acting on `X` acts on its function field, `g` acting by
`f ↦ f ∘ g⁻¹`. The holomorphic differentials of `X` are the regular Weil differentials of `F / k`,
those bounded by the zero divisor (Stichtenoth, Remark 1.5.12), a `k`-vector space of dimension the
genus over the exact field of constants (`TauCeti.finrank_weilDifferentialFiltration_zero`), and Tau
Ceti's `TauCeti.weilDifferentialRepresentation` is the action of the automorphisms of `F` on the
Weil differentials, `(σ • ω) a = ω (σ⁻¹ • a)`, which preserves the regular ones. The identification
of the regular Weil differentials of `ℂ(X) / ℂ` with the holomorphic differentials of `X` is not
formalised.

The characters that the knowl identifies are not the character of this representation but those of
`r` irreducible subrepresentations of `G`, given by the decomposition of the Jacobian of `X` by the
group algebra of `G` into a product `A₁ ^ e₁ × ⋯ × A_r ^ e_r` of powers of abelian varieties (LMFDB
`curve.highergenus.aut.groupalgebradecomp`), and it identifies them by their index in the character
table of `G` as listed by Magma. Jacobians, and so the group algebra decomposition and these
characters, are not available, and the indexing is a database ordering of the irreducible
characters (`TauCeti.irreducibleCharacters`): neither is formalised.

## Main definitions

* `TauCeti.regularDifferentialRepresentation` (LMFDB `curve.highergenus.aut.characters`): the
  representation of a group of automorphisms of `F / k` on the regular Weil differentials.
* `TauCeti.regularDifferentialCharacter` (LMFDB `curve.highergenus.aut.characters`): its
  character.

## Main results

* `TauCeti.regularDifferentialCharacter_one`: the representation on the regular differentials has
  dimension the genus.
-/

namespace TauCeti

variable {k F G : Type*} [Field k] [Field F] [Algebra k F] [Group G] (φ : G →* (F ≃ₐ[k] F))

/-- The **representation of a group `G` of automorphisms of a function field `F / k` on its
regular differentials** (LMFDB `curve.highergenus.aut.characters`): the Weil differentials of
`F / k` bounded by the zero divisor, the holomorphic differentials of the curve with function field
`F`, on which an automorphism `σ` acts by `(σ • ω) a = ω (σ⁻¹ • a)`, restricting Tau Ceti's
`TauCeti.weilDifferentialRepresentation`, through the action `φ` of `G` on `F`. Its character is
the character of the curve's group of automorphisms on its holomorphic differentials. -/
noncomputable def regularDifferentialRepresentation :
    Representation k G (weilDifferentialFiltration (0 : Divisor k F)) :=
  ((repartitionRepresentation k k F).dual.subrepresentation (weilDifferentialFiltration 0)
    fun σ _ hω ↦ (smul_zero σ : σ • (0 : Divisor k F) = 0) ▸
      (repartitionRepresentation_dual_mem_weilDifferentialFiltration_smul_iff σ).mpr hω).comp φ

/-- The **character** of the representation of a group `G` of automorphisms of a function field
`F / k` on its regular differentials (LMFDB `curve.highergenus.aut.characters`): the character of
the group of automorphisms of a curve on its holomorphic differentials. The characters the knowl
identifies are those of the irreducible subrepresentations given by the group algebra
decomposition of the Jacobian, which are not formalised. -/
noncomputable def regularDifferentialCharacter : G → k :=
  Representation.character (V := weilDifferentialFiltration (0 : Divisor k F))
    (regularDifferentialRepresentation φ)

/-- **The representation on the regular differentials has dimension the genus**: its character
takes the value `g` at the identity, for a function field `F` over its exact field of constants
`k`. -/
lemma regularDifferentialCharacter_one (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) :
    regularDifferentialCharacter φ 1 = genus k F := by
  have : FiniteDimensional k (weilDifferentialFiltration (0 : Divisor k F)) :=
    finiteDimensional_weilDifferentialFiltration hF 0
  rw [regularDifferentialCharacter, Representation.char_one,
    finrank_weilDifferentialFiltration_zero hF hex]

end TauCeti
