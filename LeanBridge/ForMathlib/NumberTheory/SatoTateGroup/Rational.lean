import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.Basic
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational

/-!
# Rational Sato–Tate groups and their minimal supergroups

A Sato–Tate group `G ⊆ U(d)` is rational if the average of every irreducible character `χ` of
`GL_d(ℂ)` over every connected component `H` of `G`, for the Haar measure restricted to `H` and
normalised to mass `1`, is an integer. The irreducible characters are taken to be those of Tau
Ceti's rational Weyl modules `V_λ`, for the dominant weights `λ` of `GL_d`: these are irreducible,
but that they exhaust the irreducible rational representations of `GL_d(ℂ)` (and so, restricted to
`U(d)`, the irreducible characters that matter) is not proved in Tau Ceti.

The minimal supergroups of `G` are the closed subgroups of its ambient group that contain `G`
properly with finite index and contain no other such supergroup properly; for rational `G` the
LMFDB lists only the rational ones, and calls `G` maximal if it has none.

## Main definitions

* `SatoTateGroup.IsRationalSubgroup`: the rationality condition on a closed subgroup of `U(d)`.
* `SatoTateGroup.IsRational` (LMFDB `st_group.rational`).
* `SatoTateGroup.IsFiniteIndexSupergroup`: proper closed finite-index supergroups in the ambient
  group.
* `SatoTateGroup.IsMinimalSupergroup`, `SatoTateGroup.IsMinimalRationalSupergroup`,
  `SatoTateGroup.IsMaximal` (LMFDB `st_group.supgroups`).
-/

open Matrix MeasureTheory TauCeti

namespace SatoTateGroup

variable {d : ℕ} (K : Subgroup (unitaryGroup (Fin d) ℂ)) (G : SatoTateGroup)
    (H : Subgroup (unitaryGroup (Fin G.degree) ℂ))

/-- A closed subgroup `K` of `U(d)` satisfies the **rationality condition** of LMFDB
`st_group.rational` if for every dominant weight `λ` of `GL_d` and every connected component `C` of
`K`, the average `∫_C χ_λ dμ / μ(C)` of the character `χ_λ` of Tau Ceti's rational Weyl module
`V_λ` over `C`, for the Haar probability measure `μ` of `K`, is an integer. -/
def IsRationalSubgroup (hK : IsClosed (K : Set (unitaryGroup (Fin d) ℂ))) : Prop :=
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  ∀ (l : DominantWeight d) (g : K), ∃ n : ℤ,
    (∫ x in connectedComponent g, Representation.character
        (V := (weylModuleOfShape ℂ d l.detShiftShape).toSubmodule) (rationalWeylRep ℂ d l)
        (Unitary.toUnits (x : unitaryGroup (Fin d) ℂ)) ∂haarProb K) /
      (haarProb K (connectedComponent g)).toReal = (n : ℂ)

/-- A Sato–Tate group `G` of degree `d` is **rational** (LMFDB `st_group.rational`) if for every
irreducible character `χ` of `GL_d(ℂ)` and every connected component `H` of `G`, the integral of
`χ` over `H` for the Haar measure restricted to `H` and normalised so that `H` has measure `1` is
an integer. The irreducible characters are those of Tau Ceti's rational Weyl modules `V_λ` for the
dominant weights `λ` of `GL_d`; that these are all the irreducible rational characters of `GL_d(ℂ)`
is the highest-weight classification, not proved in Tau Ceti. The connected components are the
cosets of the identity component. -/
def IsRational : Prop :=
  IsRationalSubgroup G.toSubgroup G.isClosed

/-- A subgroup `H` of `U(d)` is a **proper finite-index supergroup** of the Sato–Tate group `G` if
it is closed, lies in the ambient group of `G`, contains `G` properly, and `G` has finite index
in it. -/
def IsFiniteIndexSupergroup : Prop :=
  IsClosed (H : Set (unitaryGroup (Fin G.degree) ℂ)) ∧ H ≤ G.ambient ∧ G.toSubgroup < H ∧
    G.toSubgroup.relIndex H ≠ 0

/-- A **minimal supergroup** (LMFDB `st_group.supgroups`) of a Sato–Tate group `G`: a proper
finite-index supergroup `H` of `G` in its ambient group that properly contains no other proper
finite-index supergroup of `G`. -/
def IsMinimalSupergroup : Prop :=
  G.IsFiniteIndexSupergroup H ∧ ∀ H', G.IsFiniteIndexSupergroup H' → ¬H' < H

/-- A **minimal rational supergroup** (LMFDB `st_group.supgroups`) of a Sato–Tate group `G`: a
rational proper finite-index supergroup `H` of `G` that properly contains no other rational proper
finite-index supergroup of `G`. For rational `G` these are the minimal supergroups the LMFDB
lists. -/
def IsMinimalRationalSupergroup : Prop :=
  ∃ hH : G.IsFiniteIndexSupergroup H, IsRationalSubgroup H hH.1 ∧
    ∀ H' (hH' : G.IsFiniteIndexSupergroup H'), IsRationalSubgroup H' hH'.1 → ¬H' < H

/-- A rational Sato–Tate group `G` is **maximal** (LMFDB `st_group.supgroups`) if it has no
rational proper finite-index supergroup in its ambient group. -/
def IsMaximal : Prop :=
  G.IsRational ∧ ∀ H (hH : G.IsFiniteIndexSupergroup H), ¬IsRationalSubgroup H hH.1

end SatoTateGroup
