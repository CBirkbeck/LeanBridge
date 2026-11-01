import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.LevelTwoOddCharacteristics
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.LevelTwoScalarRepresentation

/-!
# The action of `S₆` on the scalar-valued Siegel modular forms on `Γ[2]`

The knowl `mf.siegel.family.gamma_2` makes `S₆ ≅ Sp(4, ℤ)/Γ[2]` act on the spaces of Siegel
modular forms on the principal congruence subgroup `Γ[2]`. For the scalar weights `det^k` (the
case `j = 0` of `M_{k,j}(Γ[2])`), this is the representation
`SiegelUpperHalfSpace.levelTwoScalarRep` of `Sp(4, ℤ)/Γ[2]` on `M_k(Γ[2])` transported through the
isomorphism `SymplecticGroup.quotientGammaTwoEquivPerm : Sp(4, ℤ)/Γ[2] ≅ S₆` given by the action on
the six odd theta characteristics. The vector-valued weights `ρ_{k,j}`, `j > 0`, the isotypic
decompositions and the Eisenstein subspaces are not formalised here.

## Main definitions

* `SiegelUpperHalfSpace.levelTwoSymmetricRep`: the representation of `S₆` on `M_k(Γ[2])`.
-/

open Matrix SymplecticGroup

namespace SiegelUpperHalfSpace

variable (k : ℤ) (q : symplecticGroup (Fin 2) ℤ ⧸ Gamma (Fin 2) 2)

/-- The **representation of `S₆` on `M_k(Γ[2])`** (LMFDB `mf.siegel.family.gamma_2`): the action
`f ↦ f ∣_k γ⁻¹` of `Sp(4, ℤ)/Γ[2]` on the scalar-valued Siegel modular forms of weight `k` on
`Γ[2]`, transported through `Sp(4, ℤ)/Γ[2] ≅ S₆`, the action on the six odd theta characteristics
numbered by `Fin 6`. -/
noncomputable def levelTwoSymmetricRep :
    Representation ℂ (Equiv.Perm (Fin 6)) (scalarModularForms k IgusaLevelTwo.principal) :=
  (levelTwoScalarRep k).comp quotientGammaTwoEquivPerm.symm.toMonoidHom

lemma levelTwoSymmetricRep_apply :
    levelTwoSymmetricRep k (quotientGammaTwoEquivPerm q) = levelTwoScalarRep k q := by
  simp [levelTwoSymmetricRep]

end SiegelUpperHalfSpace
