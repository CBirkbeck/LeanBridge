import Mathlib.GroupTheory.SpecificGroups.ZGroup

/-!
# A-groups

An A-group is a group all of whose Sylow subgroups are abelian, the abelian analogue of Mathlib's
Z-groups `IsZGroup`.

## Main definitions

* `IsAGroup` (LMFDB `group.a_group`).

## Main results

* `IsZGroup.isAGroup`: every Z-group is an A-group.
-/

variable (G : Type*) [Group G]

/-- A group is an **A-group** (LMFDB `group.a_group`) if all of its Sylow subgroups are abelian. -/
@[mk_iff] class IsAGroup : Prop where
  isMulCommutative_sylow : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsMulCommutative P

variable {G}

/-- Every Z-group is an A-group, since cyclic groups are abelian. -/
lemma IsZGroup.isAGroup [IsZGroup G] : IsAGroup G := by
  refine ⟨fun p hp P ↦ ?_⟩
  have hP : IsCyclic P := isZGroup p hp P
  infer_instance

instance [IsZGroup G] : IsAGroup G :=
  IsZGroup.isAGroup

instance [IsMulCommutative G] : IsAGroup G :=
  ⟨fun _ _ _ ↦ inferInstance⟩
