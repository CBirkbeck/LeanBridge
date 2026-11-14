import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Order.Quotient
import TauCeti.Algebra.Group.Subgroup.Conjugates

/-!
# The poset of conjugacy classes of subgroups

The LMFDB draws the subgroup diagram of a finite group `G` on the conjugacy classes of subgroups,
not on the subgroups themselves (LMFDB `group.subgroup.diagram.lmfdb`): it is the Hasse diagram of
the conjugacy classes of subgroups ordered by inclusion, `[H] ≤ [K]` when a conjugate of `H` lies
in `K`. To label subgroups it uses the same order, and the analogous order on the subgroups up to
automorphism (LMFDB `group.computing_subgroup_labels`). We treat both at once. For a group `A`
acting on `G` by automorphisms, the orbits of `A` on the subgroups of `G` carry the order induced
by inclusion: Mathlib's preorder on a quotient (`Mathlib.Order.Quotient`), the transitive closure
of inclusion and of the orbit relation. In it `[H] ≤ [K]` if and only if `a • H ≤ K` for some
`a : A`, and it is a partial order when `G` is finite, since then `a • H ≤ K` and `b • K ≤ H` force
`a • H = K` by counting. Conjugation is the case `A = ConjAct G`, and automorphisms the case
`A = MulAut G`.

The number of subgroups in the conjugacy class of `H` is the index of its normaliser (Tau Ceti's
`Subgroup.index_normalizer_eq_ncard_orbit`); the LMFDB writes it as a left subscript when it is
greater than one, so that the normal subgroups are those without a subscript.

## Main definitions

* The partial order on `MulAction.orbitRel.Quotient A (Subgroup G)` for finite `G`, which extends
  Mathlib's preorder on a quotient.
* `Subgroup.conjClassesDiagram` (LMFDB `group.subgroup.diagram.lmfdb`): the Hasse diagram of the
  conjugacy classes of subgroups.

## Main results

* `Subgroup.mk_le_mk_iff_exists_smul_le`: `[H] ≤ [K]` if and only if `a • H ≤ K` for some `a`.
* `Subgroup.mk_lt_mk_iff_exists_smul_le`: `[H] < [K]` if and only if `a • H ≤ K` for some `a` and
  `a • K ≤ H` for no `a`.
* `Subgroup.normal_iff_ncard_orbit_le_one`: in a finite group, a subgroup is normal if and only if
  its conjugacy class has at most one element.
-/

open MulAction Subgroup

open scoped Pointwise

variable {A G : Type*} [Group A] [Group G] [MulDistribMulAction A G]

namespace Subgroup

variable {H K : Subgroup G}

private lemma exists_smul_le_of_reflTransGen
    (h : Relation.ReflTransGen (fun L M : Subgroup G ↦ L ≤ M ∨ L ∈ orbit A M) H K) :
    ∃ a : A, a • H ≤ K := by
  induction h with
  | refl => exact ⟨1, (one_smul A H).le⟩
  | tail _ h ih =>
    rcases ih with ⟨a, ha⟩
    rcases h with h | ⟨b, rfl⟩
    · exact ⟨a, ha.trans h⟩
    · exact ⟨b⁻¹ * a, (mul_smul b⁻¹ a H).trans_le <| subset_pointwise_smul_iff.mp ha⟩

/-- **The order on the classes of subgroups**: for the order induced by inclusion on the orbits of
`A` on the subgroups of `G`, Mathlib's preorder on a quotient, `[H] ≤ [K]` if and only if
`a • H ≤ K` for some `a : A`, that is, for `A = ConjAct G`, a conjugate of `H` lies in `K`. -/
lemma mk_le_mk_iff_exists_smul_le :
    (Quotient.mk _ H : orbitRel.Quotient A (Subgroup G)) ≤ Quotient.mk _ K ↔ ∃ a : A, a • H ≤ K :=
  ⟨fun h ↦ exists_smul_le_of_reflTransGen (Quotient.le_def.mp h).to_reflTransGen, fun ⟨a, ha⟩ ↦
    Quotient.le_def.mpr <| .tail (.single <| .inr ⟨a⁻¹, inv_smul_smul a H⟩) (.inl ha)⟩

/-- **The proper supergroups of a class of subgroups** (LMFDB `group.computing_subgroup_labels`):
`[H] < [K]` if and only if `a • H ≤ K` for some `a : A` and `a • K ≤ H` for no `a : A`. -/
lemma mk_lt_mk_iff_exists_smul_le :
    (Quotient.mk _ H : orbitRel.Quotient A (Subgroup G)) < Quotient.mk _ K ↔ (∃ a : A, a • H ≤ K) ∧
      ∀ a : A, ¬a • K ≤ H := by
  rw [lt_iff_le_not_ge, mk_le_mk_iff_exists_smul_le, mk_le_mk_iff_exists_smul_le, not_exists]

lemma Ioi_mk_ne_of_forall_not_smul_le {M : Subgroup G} (hH : H ≤ M) (hM : ∀ a : A, ¬a • M ≤ H)
    (hK : ∀ a : A, ¬a • K ≤ M) :
    Set.Ioi (Quotient.mk _ H : orbitRel.Quotient A (Subgroup G)) ≠ Set.Ioi (Quotient.mk _ K) := by
  intro h
  have hM' : Quotient.mk _ M ∈ Set.Ioi (Quotient.mk _ H : orbitRel.Quotient A (Subgroup G)) :=
    mk_lt_mk_iff_exists_smul_le.mpr ⟨⟨1, (one_smul A H).trans_le hH⟩, hM⟩
  rw [h] at hM'
  exact (mk_lt_mk_iff_exists_smul_le.mp hM').1.elim hK

@[nolint defsWithUnderscore]
instance [Finite G] : PartialOrder (orbitRel.Quotient A (Subgroup G)) :=
  { (inferInstance : Preorder (orbitRel.Quotient A (Subgroup G))) with
    le_antisymm := by
      rintro ⟨H⟩ ⟨K⟩ hHK hKH
      rcases mk_le_mk_iff_exists_smul_le.mp hHK with ⟨a, ha⟩
      rcases mk_le_mk_iff_exists_smul_le.mp hKH with ⟨b, hb⟩
      have hcard : Nat.card K ≤ Nat.card ↥(a • H) :=
        (Nat.card_congr (equivSMul b K).toEquiv).trans_le (card_le_of_le hb) |>.trans_eq
          (Nat.card_congr (equivSMul a H).toEquiv)
      exact Quotient.sound ⟨a⁻¹, inv_smul_eq_iff.mpr (eq_of_le_of_card_ge ha hcard).symm⟩ }

variable (G) in
/-- The **subgroup diagram of `G` in the LMFDB** (LMFDB `group.subgroup.diagram.lmfdb`): the Hasse
diagram of the conjugacy classes of subgroups of `G`, ordered by inclusion up to conjugacy, two
classes being adjacent when one covers the other. The LMFDB draws it for finite groups, for which
the order is a partial order. The diagram of LMFDB `group.subgroup.diagram` is instead the Hasse
diagram `SimpleGraph.hasse (Subgroup G)`. -/
abbrev conjClassesDiagram : SimpleGraph (orbitRel.Quotient (ConjAct G) (Subgroup G)) :=
  SimpleGraph.hasse _

/-- **The normal subgroups are those alone in their conjugacy class** (LMFDB
`group.subgroup.diagram.lmfdb`): in a finite group, a subgroup is normal if and only if its
conjugacy class has at most one element, i.e. carries no left subscript in the LMFDB's diagram. -/
lemma normal_iff_ncard_orbit_le_one [Finite G] : H.Normal ↔ (orbit (ConjAct G) H).ncard ≤ 1 := by
  have h : 0 < (orbit (ConjAct G) H).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨H, mem_orbit_self H⟩
  rw [← normalizer_eq_top_iff, ← index_eq_one, index_normalizer_eq_ncard_orbit]
  omega

end Subgroup
