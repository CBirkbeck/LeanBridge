import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.Topology.Algebra.Group.Connected

/-!
# The identity component of a compact Lie group

The identity component `G⁰` of a topological group `G` is Mathlib's
`Subgroup.connectedComponentOfOne G`, a closed normal subgroup (Tau Ceti's instance
`Subgroup.normal_connectedComponentOfOne`). A topological group that is a manifold over a real model
with corners is locally path-connected, its model space being homeomorphic to a convex subset of a
real normed space, so `G⁰` is open in it; and an open subgroup of a compact group has finite index.
So the identity component of a compact real Lie group is a normal subgroup of finite index (LMFDB
`st_group.index`), and this index is by definition the cardinality of the component group `G / G⁰`
(LMFDB `st_group.component_group`, `Subgroup.index_eq_card`).

## Main results

* `Subgroup.isOpen_connectedComponentOfOne`: the identity component of a topological group that is
  a manifold over a real model with corners is open.
* `LieGroup.finiteIndex_connectedComponentOfOne` (LMFDB `st_group.index`): the identity component
  of a compact real Lie group has finite index.
-/

open scoped ContDiff

open Subgroup (connectedComponentOfOne)

variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace G] [ChartedSpace H G] [Group G]

lemma ModelWithCorners.locallyPathConnectedSpace (I : ModelWithCorners ℝ E H) :
    LocallyPathConnectedSpace H :=
  have : LocallyPathConnectedSpace (Set.range I) := I.convex_range.locallyPathConnectedSpace
  I.isClosedEmbedding.isEmbedding.toHomeomorph.symm.locallyPathConnectedSpace

namespace Subgroup

variable [IsTopologicalGroup G]

/-- **The identity component of a topological group that is a manifold over a real model with
corners is open**, the group being locally path-connected. -/
lemma isOpen_connectedComponentOfOne (I : ModelWithCorners ℝ E H) :
    IsOpen (connectedComponentOfOne G : Set G) :=
  have : LocallyPathConnectedSpace H := I.locallyPathConnectedSpace
  have : LocallyPathConnectedSpace G := ChartedSpace.locallyPathConnectedSpace H G
  isOpen_connectedComponent

lemma finiteIndex_connectedComponentOfOne [CompactSpace G] (I : ModelWithCorners ℝ E H) :
    (connectedComponentOfOne G).FiniteIndex :=
  have : Finite (G ⧸ connectedComponentOfOne G) :=
    quotient_finite_of_isOpen _ (isOpen_connectedComponentOfOne I)
  finiteIndex_of_finite_quotient

end Subgroup

/-- **The identity component of a compact real Lie group has finite index** (LMFDB
`st_group.index`): it is an open subgroup of a compact group. It is a normal subgroup (Tau Ceti's
instance `Subgroup.normal_connectedComponentOfOne`), and its index is the cardinality of the
component group `G / G⁰` (`Subgroup.index_eq_card`). -/
lemma LieGroup.finiteIndex_connectedComponentOfOne (I : ModelWithCorners ℝ E H) (n : ℕ∞ω)
    [LieGroup I n G] [CompactSpace G] :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I n
    (connectedComponentOfOne G).FiniteIndex :=
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I n
  Subgroup.finiteIndex_connectedComponentOfOne I
