import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# Subgroups as subsets that are groups for the induced operation

The LMFDB defines a subgroup of a group `G` (LMFDB `group.subgroup`) as a subset `H` such that the
operation of `G` restricts to a binary operation on `H` and `H` is a group for this induced
operation, and states that equivalently `H` is closed under the operation, contains the identity of
`G` and the inverses in `G` of its elements: the three conditions that make up Mathlib's
`Subgroup`. We define the first notion and prove the equivalence.

## Main definitions

* `Set.IsGroupForInducedMul` (LMFDB `group.subgroup`): a subset that is a group for the operation
  induced by `G`.

## Main results

* `Set.isGroupForInducedMul_coe` (LMFDB `group.subgroup`): the carrier of a subgroup is a group for
  the induced operation.
* `Set.isGroupForInducedMul_iff` (LMFDB `group.subgroup`): a subset is a group for the induced
  operation if and only if it is closed under the operation, contains the identity of `G` and the
  inverses in `G` of its elements.
* `Set.isGroupForInducedMul_iff_exists_subgroup` (LMFDB `group.subgroup`): a subset is a group for
  the induced operation if and only if it is the carrier of a `Subgroup`.
-/

namespace Set

variable {G : Type*} [Group G] {H : Set G}

variable (H) in
/-- A subset `H` of a group `G` **is a group for the induced operation** (LMFDB `group.subgroup`,
where this defines a subgroup): the operation of `G` restricts to a binary operation on `H`, that
is `H` carries an operation agreeing with that of `G`, and `H` is a group for it. -/
def IsGroupForInducedMul : Prop :=
  ∃ _ : Group H, ∀ a b : H, ((a * b : H) : G) = a * b

/-- **The carrier of a subgroup is a group for the induced operation** (LMFDB
`group.subgroup`). -/
lemma isGroupForInducedMul_coe (K : Subgroup G) : (K : Set G).IsGroupForInducedMul :=
  ⟨K.toGroup, fun _ _ ↦ rfl⟩

/-- **Subgroups by the induced operation and by three conditions** (LMFDB `group.subgroup`): a
subset `H` of `G` is a group for the operation induced by `G` if and only if it is closed under the
operation, contains the identity of `G`, and contains the inverse in `G` of each of its
elements. -/
lemma isGroupForInducedMul_iff :
    H.IsGroupForInducedMul ↔ (∀ a ∈ H, ∀ b ∈ H, a * b ∈ H) ∧ 1 ∈ H ∧ ∀ a ∈ H, a⁻¹ ∈ H := by
  constructor
  · rintro ⟨_, hmul⟩
    let f : H →* G := MonoidHom.mk' (↑) hmul
    refine ⟨fun a ha b hb ↦ hmul ⟨a, ha⟩ ⟨b, hb⟩ ▸ Subtype.prop _, f.map_one ▸ Subtype.prop _,
      fun a ha ↦ f.map_inv ⟨a, ha⟩ ▸ Subtype.prop _⟩
  · rintro ⟨hmul, hone, hinv⟩
    exact isGroupForInducedMul_coe ⟨⟨⟨H, fun ha hb ↦ hmul _ ha _ hb⟩, hone⟩, fun ha ↦ hinv _ ha⟩

/-- **A subset is a group for the induced operation if and only if it is a subgroup** (LMFDB
`group.subgroup`): the carrier of one of Mathlib's `Subgroup`s, which are bundled with the three
conditions of `Set.isGroupForInducedMul_iff`. -/
lemma isGroupForInducedMul_iff_exists_subgroup :
    H.IsGroupForInducedMul ↔ ∃ K : Subgroup G, (K : Set G) = H := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases isGroupForInducedMul_iff.mp h with ⟨hmul, hone, hinv⟩
    exact ⟨⟨⟨⟨H, fun ha hb ↦ hmul _ ha _ hb⟩, hone⟩, fun ha ↦ hinv _ ha⟩, rfl⟩
  · rintro ⟨K, rfl⟩
    exact isGroupForInducedMul_coe K

end Set
