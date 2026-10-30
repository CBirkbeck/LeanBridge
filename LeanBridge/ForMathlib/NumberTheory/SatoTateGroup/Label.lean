import LeanBridge.ForMathlib.GroupTheory.Label.Group
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.Basic
import TauCeti.Topology.Algebra.Group.Connected

/-!
# Labels of Sato–Tate groups

The LMFDB labels a Sato–Tate group `G` (LMFDB `st_group.label`) by `w.d.A.c.ns`, where

* `w` is the weight (`SatoTateGroup.weight`, LMFDB `st_group.weight`);
* `d` is the degree (`SatoTateGroup.degree`, LMFDB `st_group.degree`), a positive integer;
* `A` is an upper-case letter identifying the identity component `G⁰` among those of weight `w` and
  degree `d`, ordered by moment simplex, omitted when `w = 0`;
* `c` is the number of components (`SatoTateGroup.numComponents`, LMFDB `st_group.components`),
  the order of the component group `G / G⁰` (`SatoTateGroup.componentGroup`, LMFDB
  `st_group.component_group`);
* `n` is the second entry of the small group id `[c, n]` of the component group (LMFDB
  `group.small_group_label`);
* `s` is a lower-case letter distinguishing the groups for which all the preceding invariants
  coincide, ordered by moment simplex;

and `n` and `s` may be omitted when `w = 0` and `d = 1`. The invariants `w`, `d` and `c` are
functions of `G`, and the component group, whose isomorphism class `n` encodes, is a quotient of
`G`; but the letters `A` and `s` come from orderings by moment simplex (LMFDB
`st_group.moment_simplex`) that the knowl leaves implicit, and `n` from the numbering of the
SmallGroups library, a database numbering: neither is formalised, nor what `A`, `n` and `s`
identify (the identity component, the isomorphism class of the component group, the group, up to
an equivalence the knowl does not state). We record labels as data (`SatoTateGroup.Label`) and say
when a label is consistent with a Sato–Tate group (`SatoTateGroup.Label.IsConsistent`). The
consistency asks for `c > 0`, that is, for a finite component group: a closed subgroup of `U(d)` is
a compact Lie group, with finitely many components, which is not proved here.

According to the knowl, the identity component of a Sato–Tate group of weight `0` is trivial, which
is why `A` is omitted: this holds for the Sato–Tate groups of motives, which LeanBridge's
`SatoTateGroup` does not record, not for every compact subgroup of `O(d)`.

## Main definitions

* `SatoTateGroup.componentGroup` (LMFDB `st_group.label`, `st_group.component_group`): the
  component group `G / G⁰`.
* `SatoTateGroup.numComponents` (LMFDB `st_group.label`, `st_group.components`): the number of
  components.
* `SatoTateGroup.Label`, `SatoTateGroup.Label.toString` and `SatoTateGroup.Label.IsConsistent`
  (LMFDB `st_group.label`): labels `w.d.A.c.ns` and their consistency with a Sato–Tate group.
-/

open Subgroup (connectedComponentOfOne)

namespace SatoTateGroup

variable (G : SatoTateGroup)

/-- The **component group** `G / G⁰` of a Sato–Tate group (LMFDB `st_group.component_group`), the
quotient by its identity component, a normal subgroup (`Subgroup.normal_connectedComponentOfOne`).
-/
abbrev componentGroup : Type :=
  G.toSubgroup ⧸ connectedComponentOfOne G.toSubgroup

/-- The **number of components** `c` of a Sato–Tate group (LMFDB `st_group.components`,
`st_group.label`): the cardinality of the component group `G / G⁰`, finite for a compact Lie group;
`Nat.card` would give `0` for infinitely many components. -/
noncomputable def numComponents : ℕ :=
  Nat.card G.componentGroup

/-- The **label** `w.d.A.c.ns` of a Sato–Tate group (LMFDB `st_group.label`), as data: the weight
`w`, the degree `d`, the letter `A` of the identity component (`none` when `w = 0`), the number `c`
of components, and the small group id `n` of the component group with the letter `s`, omitted
together (`none`) when `w = 0` and `d = 1`. The letters `A` and `s` and the id `n` are database
numberings, recorded here but not determined. -/
@[ext]
structure Label where
  /-- The weight `w`. -/
  weight : ℕ
  /-- The degree `d`. -/
  degree : ℕ
  /-- The letter `A` of the identity component, omitted in weight `0`. -/
  identityComponent : Option Char
  /-- The number `c` of components. -/
  numComponents : ℕ
  /-- The small group id `n` of the component group and the letter `s`, if present. -/
  tail : Option (ℕ × Char)

namespace Label

variable (ℓ : Label)

/-- The string `w.d.A.c.ns` of the label of a Sato–Tate group, the parts `A.` and `.ns` being
omitted when absent, as in `1.4.F.1.1a` or `0.1.3`. -/
def toString : String :=
  ℓ.weight.repr ++ "." ++ ℓ.degree.repr ++ "." ++
    (ℓ.identityComponent.map fun A ↦ A.toString ++ ".").getD "" ++ ℓ.numComponents.repr ++
    (ℓ.tail.map fun p ↦ "." ++ p.1.repr ++ p.2.toString).getD ""

/-- A label `w.d.A.c.ns` is **consistent** with a Sato–Tate group `G` (LMFDB `st_group.label`) if
`w`, `d` and `c` are the weight, the degree and the number of components of `G`, the latter two
positive, `A` is an upper-case letter given exactly in positive weight, `[c, n]` is consistent with
the component group of `G` as a small group id and `s` is a lower-case letter, and `n` and `s` are
only omitted when `w = 0` and `d = 1`. -/
def IsConsistent : Prop :=
  ℓ.weight = G.weight ∧ ℓ.degree = G.degree ∧ 0 < ℓ.degree ∧ ℓ.numComponents = G.numComponents ∧
    0 < ℓ.numComponents ∧ (ℓ.identityComponent = none ↔ ℓ.weight = 0) ∧
    (∀ A ∈ ℓ.identityComponent, A.isUpper) ∧ (ℓ.tail = none → ℓ.weight = 0 ∧ ℓ.degree = 1) ∧
    ∀ p ∈ ℓ.tail, (⟨ℓ.numComponents, p.1⟩ : Group.SmallGroupId).IsConsistent G.componentGroup ∧
      p.2.isLower

end Label

end SatoTateGroup
