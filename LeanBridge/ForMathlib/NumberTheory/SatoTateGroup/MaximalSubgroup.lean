import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.LieGroup
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.SupergroupIdentityComponent

/-!
# The maximal subgroups of a Sato–Tate group

The maximal subgroups (LMFDB `st_group.subgroups`) of a Sato–Tate group `G` are its proper
subgroups of finite index that are contained in no other proper subgroup of `G`. As in the knowl,
they are subgroups of the abstract group `G`, not assumed closed. Every subgroup `H` of finite
index of `G` contains the identity component `G⁰`
(`SatoTateGroup.connectedComponentOfOne_le_of_finiteIndex`, through the exponential map of the
compact Lie group `G`), so it has the same identity component `H⁰ = G⁰` (LMFDB
`st_group.identity_component`, `SatoTateGroup.identityComponent`); in particular so do the maximal
subgroups of `G`.

## Main definitions

* `SatoTateGroup.IsMaximalSubgroup` (LMFDB `st_group.subgroups`): the maximal subgroups of a
  Sato–Tate group.

## Main results

* `SatoTateGroup.map_connectedComponentOfOne_eq_of_relIndex_ne_zero`: a subgroup of finite index
  of a Sato–Tate group `G` has the identity component `G⁰`.
* `SatoTateGroup.IsMaximalSubgroup.map_connectedComponentOfOne_eq` (LMFDB `st_group.subgroups`):
  the maximal subgroups of a Sato–Tate group `G` have the identity component `G⁰`.
-/

open Matrix

open Subgroup (connectedComponentOfOne)

namespace SatoTateGroup

variable {G : SatoTateGroup} {H : Subgroup (unitaryGroup (Fin G.degree) ℂ)}

variable (G H) in
/-- A **maximal subgroup** (LMFDB `st_group.subgroups`) of a Sato–Tate group `G`: a proper subgroup
`H` of `G` of finite index that is contained in no other proper subgroup of `G`. As in the knowl,
`H` is a subgroup of the abstract group `G`, not assumed closed; it contains the identity component
of `G` (`SatoTateGroup.connectedComponentOfOne_le_of_finiteIndex`). -/
def IsMaximalSubgroup : Prop :=
  H < G.toSubgroup ∧ H.relIndex G.toSubgroup ≠ 0 ∧ ∀ K, H < K → ¬K < G.toSubgroup

/-- **A subgroup `H` of finite index of a Sato–Tate group `G` has the identity component
`H⁰ = G⁰`**, closed or not: `H` contains `G⁰`, a connected subset through `1`. -/
lemma map_connectedComponentOfOne_eq_of_relIndex_ne_zero (hHG : H ≤ G.toSubgroup)
    (hH : H.relIndex G.toSubgroup ≠ 0) :
    (connectedComponentOfOne H).map H.subtype = G.identityComponent.toSubgroup :=
  have : (H.subgroupOf G.toSubgroup).FiniteIndex := ⟨hH⟩
  (Subgroup.map_connectedComponentOfOne_eq_of_le_subgroupOf hHG
    (G.connectedComponentOfOne_le_of_finiteIndex _)).symm

/-- **A maximal subgroup `H` of a Sato–Tate group `G` has the identity component `H⁰ = G⁰`**
(LMFDB `st_group.subgroups`). -/
lemma IsMaximalSubgroup.map_connectedComponentOfOne_eq (hH : G.IsMaximalSubgroup H) :
    (connectedComponentOfOne H).map H.subtype = G.identityComponent.toSubgroup :=
  map_connectedComponentOfOne_eq_of_relIndex_ne_zero hH.1.le hH.2.1

end SatoTateGroup
