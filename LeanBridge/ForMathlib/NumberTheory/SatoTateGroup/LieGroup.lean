import LeanBridge.ForMathlib.Geometry.Manifold.Algebra.LieGroupFiniteIndex
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.Basic
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import TauCeti.Analysis.Matrix.Normed

/-!
# Sato–Tate groups are compact Lie groups

A Sato–Tate group `G` of degree `d` (LMFDB `st_group.definition`) is a closed subgroup of the
unitary group `U(d)`, so its image under the inclusion `Unitary.toUnits` of `U(d)` into the group
`GL_d(ℂ)` of units of the matrix algebra is closed. By Cartan's closed-subgroup theorem (Tau Ceti)
this image is a Lie group, and it is compact: a Sato–Tate group is a compact Lie group
(`SatoTateGroup.isEmbeddedLieSubgroup`). As a topological group, `G` is isomorphic to its image in
`GL_d(ℂ)`, which is locally path-connected, so `G` is locally path-connected. Hence its identity
component `G⁰` (`Subgroup.connectedComponentOfOne`, a closed normal subgroup by Tau Ceti's
instances) is open, of finite index (LMFDB `st_group.identity_component`, `st_group.index`), and
lies in every subgroup of finite index of `G`, closed or not.

The Lie group `GL_d(ℂ)` is Mathlib's group of units of the normed algebra of matrices, for the `L∞`
operator norm, as in Tau Ceti and in `SatoTateGroup.realDimension`. The topology of this norm is the
entrywise topology of `U(d)`, but not the same instance, so the statements about `G` are made for
the entrywise topology, and the topology of the operator norm is selected only inside proofs.

## Main results

* `SatoTateGroup.isEmbeddedLieSubgroup`: a Sato–Tate group of degree `d` is an embedded Lie subgroup
  of `GL_d(ℂ)`, a compact Lie group.
* The instance `LocallyPathConnectedSpace G.toSubgroup`: a Sato–Tate group is locally
  path-connected.
* `SatoTateGroup.isOpen_connectedComponentOfOne`: the identity component of a Sato–Tate group is
  open.
* `SatoTateGroup.finiteIndex_connectedComponentOfOne` (LMFDB `st_group.identity_component`,
  `st_group.index`): the identity component of a Sato–Tate group has finite index, also an
  instance.
* `SatoTateGroup.connectedComponentOfOne_le_of_finiteIndex`: the identity component of a Sato–Tate
  group lies in each of its subgroups of finite index.
-/

open Matrix TauCeti Lie

open scoped ContDiff Manifold Matrix.Norms.Operator

open Subgroup (connectedComponentOfOne)

lemma Unitary.continuous_toUnits {R : Type*} [Monoid R] [StarMul R] [TopologicalSpace R]
    [ContinuousStar R] : Continuous (toUnits : unitary R → Rˣ) :=
  Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_subtype_val.star⟩

namespace SatoTateGroup

variable (G : SatoTateGroup)

lemma isClosed_map_toUnits :
    IsClosed (G.toSubgroup.map Unitary.toUnits : Set (GL (Fin G.degree) ℂ)) := by
  have h : (G.toSubgroup.map Unitary.toUnits : Set (Matrix (Fin G.degree) (Fin G.degree) ℂ)ˣ) =
      Units.val ⁻¹' (Subtype.val '' (G.toSubgroup : Set (unitaryGroup (Fin G.degree) ℂ))) := by
    ext u
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, hgu⟩
      exact ⟨g, hg, Units.ext hgu⟩
  rw [h]
  exact (isClosed_unitary.isClosedEmbedding_subtypeVal.isClosedMap _ G.isClosed).preimage
    Units.continuous_val

attribute [local instance] Matrix.linftyOpTopologicalSpace in
/-- **A Sato–Tate group of degree `d` is a compact Lie group**: its image in `GL_d(ℂ)` is a closed
subgroup, so an embedded Lie subgroup by the closed-subgroup theorem, for the Lie group structure of
the units of the normed algebra of matrices. -/
lemma isEmbeddedLieSubgroup :
    IsEmbeddedLieSubgroup (I := 𝓘(ℝ, Matrix (Fin G.degree) (Fin G.degree) ℂ))
      (G.toSubgroup.map Unitary.toUnits) :=
  isEmbeddedLieSubgroup_of_isClosed G.isClosed_map_toUnits

instance : LocallyPathConnectedSpace G.toSubgroup := by
  let _ : TopologicalSpace (Matrix (Fin G.degree) (Fin G.degree) ℂ) :=
    Matrix.linftyOpTopologicalSpace _ _ _
  have _ : ContinuousStar (Matrix (Fin G.degree) (Fin G.degree) ℂ) :=
    Matrix.linftyOpContinuousStar _ _
  have _ : LocallyPathConnectedSpace (G.toSubgroup.map Unitary.toUnits) :=
    Subgroup.locallyPathConnectedSpace_of_isClosed 𝓘(ℝ, Matrix (Fin G.degree) (Fin G.degree) ℂ)
      G.isClosed_map_toUnits
  have _ : CompactSpace G.toSubgroup := isCompact_iff_compactSpace.mp G.isClosed.isCompact
  let e : G.toSubgroup ≃* G.toSubgroup.map Unitary.toUnits :=
    G.toSubgroup.equivMapOfInjective Unitary.toUnits Unitary.toUnits_injective
  have he : Continuous e.toEquiv :=
    (Unitary.continuous_toUnits.comp continuous_subtype_val).subtype_mk _
  exact he.homeoOfEquivCompactToT2.symm.locallyPathConnectedSpace

/-- **The identity component of a Sato–Tate group is open**, a Sato–Tate group being locally
path-connected. -/
lemma isOpen_connectedComponentOfOne :
    IsOpen (connectedComponentOfOne G.toSubgroup : Set G.toSubgroup) :=
  isOpen_connectedComponent

/-- **The identity component `G⁰` of a Sato–Tate group `G` has finite index** (LMFDB
`st_group.identity_component`, `st_group.index`): it is an open subgroup of the compact group `G`.
It is a normal subgroup (Tau Ceti's instance `Subgroup.normal_connectedComponentOfOne`), and its
index is the order of the component group `G / G⁰`. -/
lemma finiteIndex_connectedComponentOfOne : (connectedComponentOfOne G.toSubgroup).FiniteIndex :=
  have : Finite (G.toSubgroup ⧸ connectedComponentOfOne G.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ G.isOpen_connectedComponentOfOne
  Subgroup.finiteIndex_of_finite_quotient

instance : (connectedComponentOfOne G.toSubgroup).FiniteIndex :=
  G.finiteIndex_connectedComponentOfOne

/-- **The identity component `G⁰` of a Sato–Tate group `G` lies in every subgroup `H` of finite
index of `G`**, closed or not: the image of `H` in `GL_d(ℂ)` has finite index in the image of `G`,
a closed subgroup of the Lie group `GL_d(ℂ)`. -/
lemma connectedComponentOfOne_le_of_finiteIndex (H : Subgroup G.toSubgroup) [H.FiniteIndex] :
    connectedComponentOfOne G.toSubgroup ≤ H := by
  let _ : TopologicalSpace (Matrix (Fin G.degree) (Fin G.degree) ℂ) :=
    Matrix.linftyOpTopologicalSpace _ _ _
  have _ : ContinuousStar (Matrix (Fin G.degree) (Fin G.degree) ℂ) :=
    Matrix.linftyOpContinuousStar _ _
  have hK : IsClosed (G.toSubgroup.map Unitary.toUnits : Set (GL (Fin G.degree) ℂ)) :=
    G.isClosed_map_toUnits
  let e : G.toSubgroup ≃* G.toSubgroup.map Unitary.toUnits :=
    G.toSubgroup.equivMapOfInjective Unitary.toUnits Unitary.toUnits_injective
  have he : Continuous e.toMonoidHom :=
    (Unitary.continuous_toUnits.comp continuous_subtype_val).subtype_mk _
  have _ : (H.map e.toMonoidHom).FiniteIndex :=
    ⟨(H.index_map_equiv e).trans_ne H.index_ne_zero_of_finite⟩
  have h₁ : (connectedComponentOfOne G.toSubgroup).map e.toMonoidHom ≤
      connectedComponentOfOne (G.toSubgroup.map Unitary.toUnits) :=
    Subgroup.map_connectedComponentOfOne_le he
  have h₂ : connectedComponentOfOne (G.toSubgroup.map Unitary.toUnits) ≤ H.map e.toMonoidHom :=
    Subgroup.connectedComponentOfOne_le_of_isClosed 𝓘(ℝ, Matrix (Fin G.degree) (Fin G.degree) ℂ)
      hK _
  exact (Subgroup.map_le_map_iff_of_injective e.injective).mp (h₁.trans h₂)

end SatoTateGroup
