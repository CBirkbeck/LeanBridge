import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Connected.Clopen

/-!
# The connected components of a topological group

The connected component of an element `g` of a topological group `G` is the coset `g G⁰` of the
identity component `G⁰ = Subgroup.connectedComponentOfOne G`, by Mathlib's
`smul_connectedComponent`. So the connected components of `G` are the cosets of `G⁰`, and the space
`ConnectedComponents G` of its connected components is the coset space `G ⧸ G⁰`.

## Main definitions

* `connectedComponentsEquivQuotient`: the bijection between the connected components of a
  topological group `G` and the cosets of its identity component, sending the connected component
  of `g` to the coset `g G⁰`.

## Main results

* `connectedComponent_eq_smul`: the connected component of `g` is the coset `g G⁰`.
-/

open scoped Pointwise

open Subgroup (connectedComponentOfOne)

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (g h : G)

/-- **The connected component of an element `g` of a topological group is the coset `g G⁰`** of the
identity component `G⁰`. -/
lemma connectedComponent_eq_smul : connectedComponent g = g • (connectedComponentOfOne G : Set G) :=
  (congrArg connectedComponent (mul_one g)).symm.trans (smul_connectedComponent g 1).symm

lemma connectedComponent_eq_connectedComponent_iff :
    connectedComponent g = connectedComponent h ↔ g⁻¹ * h ∈ connectedComponentOfOne G := by
  rw [eq_comm, connectedComponent_eq_iff_mem, connectedComponent_eq_smul,
    Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe]

variable (G) in
/-- The **connected components of a topological group `G` are the cosets of its identity component**
`G⁰`: the bijection between `ConnectedComponents G` and `G ⧸ G⁰` sending the connected component of
`g` to the coset `g G⁰`. -/
def connectedComponentsEquivQuotient : ConnectedComponents G ≃ G ⧸ connectedComponentOfOne G :=
  Quotient.congr (Equiv.refl G) fun g h ↦
    (connectedComponent_eq_connectedComponent_iff g h).trans QuotientGroup.leftRel_apply.symm

lemma connectedComponentsEquivQuotient_mk :
    connectedComponentsEquivQuotient G (.mk g) = (g : G ⧸ connectedComponentOfOne G) :=
  rfl
