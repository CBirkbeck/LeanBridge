import Mathlib.GroupTheory.OrderOfElement
import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.Algebra.Group.Conj

/-!
# Autjugacy classes

The autjugacy class of an element `x` of a group `G` (LMFDB `group.autjugacy_class`) is its orbit
`{φ x | φ ∈ Aut(G)}` under the automorphism group, `MulAction.orbit (MulAut G) x`. Automorphisms
permute the conjugacy classes (Tau Ceti's action of `MulAut G` on `ConjClasses G`), and we prove
that an autjugacy class is the disjoint union of the conjugacy classes in the orbit of the class of
`x`, all of the same size, whose elements all have the order of `x`.

## Main results

* `MulAut.orbit_eq_iUnion_carrier` (LMFDB `group.autjugacy_class`): the autjugacy class of `x` is
  the union of the conjugacy classes in the orbit of the class of `x`.
* `MulAut.pairwiseDisjoint_carrier_orbit` (LMFDB `group.autjugacy_class`): these conjugacy classes
  are pairwise disjoint.
* `MulAut.natCard_carrier_of_mem_orbit` (LMFDB `group.autjugacy_class`): they all have the size of
  the class of `x`.
* `MulAut.orderOf_of_mem_carrier_of_mem_orbit` (LMFDB `group.autjugacy_class`): their elements all
  have the order of `x`.
-/

open MulAction

namespace MulAut

variable {G : Type*} [Group G] (x : G)

lemma carrier_mk_apply (φ : MulAut G) :
    (ConjClasses.mk (φ x)).carrier = φ '' (ConjClasses.mk x).carrier := by
  ext z
  rw [ConjClasses.mem_carrier_iff_mk_eq]
  refine ⟨fun h ↦ ⟨φ.symm z, ?_, φ.apply_symm_apply z⟩, ?_⟩
  · rw [ConjClasses.mem_carrier_iff_mk_eq]
    simpa using congrArg (φ.symm • ·) h
  · rintro ⟨w, hw, rfl⟩
    rw [ConjClasses.mem_carrier_iff_mk_eq] at hw
    rw [← smul_conjClasses_mk, hw, smul_conjClasses_mk]

/-- **An autjugacy class is a union of conjugacy classes** (LMFDB `group.autjugacy_class`): the
orbit of `x` under `Aut(G)` is the union of the conjugacy classes in the orbit of the class of `x`
under `Aut(G)`. -/
lemma orbit_eq_iUnion_carrier :
    orbit (MulAut G) x = ⋃ c ∈ orbit (MulAut G) (ConjClasses.mk x), c.carrier := by
  ext y
  simp only [Set.mem_iUnion, mem_orbit_iff]
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨_, ⟨φ, rfl⟩, ConjClasses.mem_carrier_mk⟩
  · rintro ⟨_, ⟨φ, rfl⟩, hy⟩
    rw [smul_conjClasses_mk, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj,
      isConj_iff] at hy
    rcases hy with ⟨g, hg⟩
    refine ⟨conj g⁻¹ * φ, ?_⟩
    rw [mul_smul, MulAut.smul_def, MulAut.smul_def, conj_apply, ← hg]
    simp [mul_assoc]

/-- **The conjugacy classes in an autjugacy class are pairwise disjoint** (LMFDB
`group.autjugacy_class`). -/
lemma pairwiseDisjoint_carrier_orbit :
    (orbit (MulAut G) (ConjClasses.mk x)).PairwiseDisjoint ConjClasses.carrier :=
  (Set.pairwiseDisjoint_fiber ConjClasses.mk _).mono_on fun _ _ ↦
    ConjClasses.carrier_eq_preimage_mk.le

/-- **The conjugacy classes in an autjugacy class have the same size** (LMFDB
`group.autjugacy_class`). -/
lemma natCard_carrier_of_mem_orbit {c : ConjClasses G}
    (hc : c ∈ orbit (MulAut G) (ConjClasses.mk x)) :
    Nat.card c.carrier = Nat.card (ConjClasses.mk x).carrier := by
  rcases hc with ⟨φ, rfl⟩
  dsimp only
  rw [smul_conjClasses_mk, carrier_mk_apply, Nat.card_image_of_injective φ.injective]

lemma orderOf_of_mem_orbit {y : G} (hy : y ∈ orbit (MulAut G) x) : orderOf y = orderOf x := by
  rcases hy with ⟨φ, rfl⟩
  exact φ.orderOf_eq x

/-- **The conjugacy classes in an autjugacy class have the same order** (LMFDB
`group.autjugacy_class`): every element of every conjugacy class in the autjugacy class of `x` has
the order of `x`. -/
lemma orderOf_of_mem_carrier_of_mem_orbit {c : ConjClasses G}
    (hc : c ∈ orbit (MulAut G) (ConjClasses.mk x)) {y : G} (hy : y ∈ c.carrier) :
    orderOf y = orderOf x :=
  orderOf_of_mem_orbit x <| (orbit_eq_iUnion_carrier x).symm ▸ Set.mem_biUnion hc hy

end MulAut
