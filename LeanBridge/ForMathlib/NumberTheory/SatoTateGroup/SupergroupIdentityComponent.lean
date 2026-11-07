import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.IdentityComponent
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.Rational

/-!
# The identity component of a finite-index supergroup

A closed subgroup `K` of finite index in a subgroup `L` of a topological group is open in `L`, so it
contains the identity component of `L` (Tau Ceti's `Subgroup.connectedComponentOfOne_le_of_isOpen`);
the identity component of `L` is then a connected subset of `K` through `1`, so it is the identity
component of `K`. For a Sato–Tate group `G` this says that its proper finite-index supergroups `H`,
in particular its minimal supergroups and its minimal rational supergroups (LMFDB
`st_group.supgroups`), have the same identity component `H⁰ = G⁰` (LMFDB
`st_group.identity_component`, `SatoTateGroup.identityComponent`).

## Main results

* `Subgroup.map_connectedComponentOfOne_eq_of_le`: a closed subgroup of finite index in a subgroup
  `L` of a topological group has the same identity component as `L`.
* `SatoTateGroup.IsFiniteIndexSupergroup.map_connectedComponentOfOne_eq`,
  `SatoTateGroup.IsMinimalSupergroup.map_connectedComponentOfOne_eq` and
  `SatoTateGroup.IsMinimalRationalSupergroup.map_connectedComponentOfOne_eq` (LMFDB
  `st_group.supgroups`): the proper finite-index supergroups of a Sato–Tate group `G`, and so its
  minimal and minimal rational supergroups, have identity component `G⁰`.
-/

open Matrix

open Subgroup (connectedComponentOfOne)

namespace Subgroup

variable {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] {K L : Subgroup X}

variable (L) in
lemma coe_map_subtype_connectedComponentOfOne :
    ((connectedComponentOfOne L).map L.subtype : Set X) = connectedComponentIn L 1 :=
  (connectedComponentIn_eq_image L.one_mem).symm

/-- **A closed subgroup `K` of finite index in a subgroup `L` of a topological group has the same
identity component as `L`**: `K` is open in `L`, so it contains the identity component of `L`, a
connected subset through `1`. -/
lemma map_connectedComponentOfOne_eq_of_le (hKL : K ≤ L) (hK : IsClosed (K : Set X))
    (hKL' : K.relIndex L ≠ 0) :
    (connectedComponentOfOne L).map L.subtype = (connectedComponentOfOne K).map K.subtype := by
  have : (K.subgroupOf L).FiniteIndex := ⟨hKL'⟩
  have hK' : IsOpen ((K.subgroupOf L : Subgroup L) : Set L) :=
    (K.subgroupOf L).isOpen_of_isClosed_of_finiteIndex (hK.preimage continuous_subtype_val)
  have hle : connectedComponentIn (L : Set X) 1 ⊆ K := by
    rw [← coe_map_subtype_connectedComponentOfOne]
    rintro _ ⟨x, hx, rfl⟩
    exact connectedComponentOfOne_le_of_isOpen hK' hx
  refine SetLike.coe_injective ?_
  rw [coe_map_subtype_connectedComponentOfOne, coe_map_subtype_connectedComponentOfOne]
  exact subset_antisymm (isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn L.one_mem) hle) (connectedComponentIn_mono 1 hKL)

end Subgroup

namespace SatoTateGroup

variable {G : SatoTateGroup} {H : Subgroup (unitaryGroup (Fin G.degree) ℂ)}

/-- **A proper finite-index supergroup `H` of a Sato–Tate group `G` has the identity component
`H⁰ = G⁰`** (LMFDB `st_group.supgroups`): the identity component of `H`, as a subgroup of the
unitary group, is that of `G` (`SatoTateGroup.identityComponent`), `G` being closed of finite index
in `H`. -/
lemma IsFiniteIndexSupergroup.map_connectedComponentOfOne_eq (hH : G.IsFiniteIndexSupergroup H) :
    (connectedComponentOfOne H).map H.subtype = G.identityComponent.toSubgroup :=
  Subgroup.map_connectedComponentOfOne_eq_of_le hH.2.2.1.le G.isClosed hH.2.2.2

/-- **A minimal supergroup `H` of a Sato–Tate group `G` has the identity component `H⁰ = G⁰`**
(LMFDB `st_group.supgroups`). -/
lemma IsMinimalSupergroup.map_connectedComponentOfOne_eq (hH : G.IsMinimalSupergroup H) :
    (connectedComponentOfOne H).map H.subtype = G.identityComponent.toSubgroup :=
  hH.1.map_connectedComponentOfOne_eq

/-- **A minimal rational supergroup `H` of a Sato–Tate group `G` has the identity component
`H⁰ = G⁰`** (LMFDB `st_group.supgroups`). -/
lemma IsMinimalRationalSupergroup.map_connectedComponentOfOne_eq
    (hH : G.IsMinimalRationalSupergroup H) :
    (connectedComponentOfOne H).map H.subtype = G.identityComponent.toSubgroup :=
  hH.fst.map_connectedComponentOfOne_eq

end SatoTateGroup
