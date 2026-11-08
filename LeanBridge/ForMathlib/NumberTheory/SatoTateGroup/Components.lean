import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.Label
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.LieGroup
import LeanBridge.ForMathlib.Topology.Algebra.Group.ConnectedComponents

/-!
# The components of a Sato–Tate group

A Sato–Tate group `G` (LMFDB `st_group.definition`) is a compact Lie group, so its identity
component `G⁰` is open, of finite index (`SatoTateGroup.finiteIndex_connectedComponentOfOne`), and
normal (Tau Ceti's instance `Subgroup.normal_connectedComponentOfOne`). The connected components of
`G` are the cosets `g G⁰` (`connectedComponent_eq_smul`), so they are finitely many, and their
number is the order of the component group `G / G⁰` (LMFDB `st_group.components`,
`st_group.component_group`), the number of components `c` of the label of `G`
(`SatoTateGroup.numComponents`, LMFDB `st_group.label`), which is therefore positive.

## Main results

* `SatoTateGroup.finite_connectedComponents` (LMFDB `st_group.components`): a Sato–Tate group has
  finitely many connected components.
* `SatoTateGroup.card_connectedComponents` (LMFDB `st_group.components`): the number of connected
  components of a Sato–Tate group is the order of its component group.
* `SatoTateGroup.numComponents_pos`: the number of components of a Sato–Tate group is positive.
-/

namespace SatoTateGroup

variable (G : SatoTateGroup)

/-- **A Sato–Tate group has finitely many connected components** (LMFDB `st_group.components`):
they are the cosets of its identity component, which has finite index. -/
lemma finite_connectedComponents : Finite (ConnectedComponents G.toSubgroup) :=
  .of_equiv _ (connectedComponentsEquivQuotient G.toSubgroup).symm

instance : Finite (ConnectedComponents G.toSubgroup) :=
  G.finite_connectedComponents

/-- **The number of connected components of a Sato–Tate group `G` is the order of its component
group `G / G⁰`** (LMFDB `st_group.components`), the number of components `c` of its label. -/
lemma card_connectedComponents : Nat.card (ConnectedComponents G.toSubgroup) = G.numComponents :=
  Nat.card_congr (connectedComponentsEquivQuotient G.toSubgroup)

/-- **The number of components of a Sato–Tate group is positive**, as the consistency of its labels
(LMFDB `st_group.label`) asks. -/
lemma numComponents_pos : 0 < G.numComponents :=
  Nat.card_pos

end SatoTateGroup
