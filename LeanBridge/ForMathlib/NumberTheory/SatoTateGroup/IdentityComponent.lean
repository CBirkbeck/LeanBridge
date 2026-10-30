import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.Label

/-!
# The identity component of a Sato–Tate group

The Sato–Tate group `ST(A)` of an abelian variety `A` (LMFDB `g2c.st_group`) is a compact Lie group,
not necessarily connected. Its identity component `ST⁰(A)` (LMFDB `g2c.st_group_identity_component`,
`st_group.identity_component`), the connected component of the identity, is a closed normal
subgroup (`Subgroup.connectedComponentOfOne`, `Subgroup.normal_connectedComponentOfOne`), the
identity element of the component group `ST(A) / ST⁰(A)` (LMFDB `st_group.component_group`,
`SatoTateGroup.componentGroup`). It is itself a Sato–Tate group of the same weight and degree,
closed in the unitary group, and the LMFDB labels it as such.

The Sato–Tate group of an abelian variety is not available: LeanBridge's `SatoTateGroup` is an
abstract compact subgroup of `USp(d)` or `O(d)`, so the identity component is formalised for these.
For an abelian surface `A` over `ℚ`, `ST⁰(A)` is one of `U(1)`, `SU(2)`, `U(1) × U(1)`,
`U(1) × SU(2)`, `SU(2) × SU(2)` and `USp(4)` up to conjugacy, according to the real geometric
endomorphism algebra `End(A_ℚ̄) ⊗ ℝ` (Fité, Kedlaya, Rotger and Sutherland); these six groups are
`SatoTateGroup.AbelianSurfaceIdentityComponent.toSatoTateGroup`, but the classification itself is
not formalised, nor is the surjection of the component group onto the Galois group of the
endomorphism field of `A`, an isomorphism in dimension at most `3`.

## Main definitions

* `SatoTateGroup.identityComponent` (LMFDB `g2c.st_group_identity_component`,
  `st_group.identity_component`): the identity component `G⁰` of a Sato–Tate group `G`, as a
  Sato–Tate group.

## Main results

* The instance `ConnectedSpace G.identityComponent.toSubgroup`: the identity component is
  connected.
* `SatoTateGroup.numComponents_identityComponent`: the identity component has one component.
-/

open Subgroup (connectedComponentOfOne)

namespace SatoTateGroup

variable (G : SatoTateGroup)

/-- The **identity component** `G⁰` (LMFDB `g2c.st_group_identity_component`,
`st_group.identity_component`) of a Sato–Tate group `G`, as a Sato–Tate group of the same weight and
degree: the connected component of the identity of `G` (`Subgroup.connectedComponentOfOne`), a
subgroup of the unitary group `U(d)` that is closed in `U(d)`, as `G` is. It is a normal subgroup of
`G` (`Subgroup.normal_connectedComponentOfOne`), the identity element of the component group
`G / G⁰` (LMFDB `st_group.component_group`, `SatoTateGroup.componentGroup`). -/
noncomputable def identityComponent : SatoTateGroup where
  weight := G.weight
  degree := G.degree
  even_degree_of_odd_weight := G.even_degree_of_odd_weight
  toSubgroup := (connectedComponentOfOne G.toSubgroup).map G.toSubgroup.subtype
  isClosed := by
    rw [Subgroup.coe_map, Subgroup.coe_subtype, Subgroup.coe_connectedComponentOfOne]
    exact G.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
  le_ambientGroup := (Subgroup.map_subtype_le _).trans G.le_ambientGroup

lemma identityComponent_toSubgroup_le : G.identityComponent.toSubgroup ≤ G.toSubgroup :=
  Subgroup.map_subtype_le _

instance : ConnectedSpace G.identityComponent.toSubgroup := by
  have h : IsConnected (Subtype.val '' connectedComponent (1 : G.toSubgroup)) :=
    isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  exact isConnected_iff_connectedSpace.mp h

/-- **The identity component of a Sato–Tate group has one component**: being connected, it is its
own identity component, and its component group is trivial. -/
lemma numComponents_identityComponent : G.identityComponent.numComponents = 1 := by
  rw [numComponents, ← Subgroup.index_eq_card, Subgroup.connectedComponentOfOne_eq_top,
    Subgroup.index_top]

end SatoTateGroup
