import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Quasisimple groups

A group `G` is quasisimple if it is perfect and a central extension of a simple group: the quotient
`G ⧸ A` by some subgroup `A` of the centre of `G` is simple. That subgroup is then the centre, so
`G` is quasisimple if and only if it is perfect and `G ⧸ Z(G)` is simple, the usual definition.

## Main definitions

* `IsQuasisimple` (LMFDB `group.quasisimple`).

## Main results

* `isQuasisimple_iff_isSimpleGroup_quotient_center`: `G` is quasisimple if and only if it is
  perfect and `G ⧸ Z(G)` is simple.
* `IsSimpleGroup.isQuasisimple`: non-abelian simple groups are quasisimple.
-/

open Group Subgroup

variable (G : Type*) [Group G]

/-- A group `G` is **quasisimple** (LMFDB `group.quasisimple`) if it is perfect and a central
extension of a simple group: the quotient `G ⧸ A` by some subgroup `A` of the centre of `G` is
simple. -/
class IsQuasisimple : Prop where
  /-- A quasisimple group is perfect. -/
  isPerfect : Group.IsPerfect G
  /-- A quasisimple group is a central extension of a simple group. -/
  exists_le_center : ∃ (A : Subgroup G) (_ : A.Normal), A ≤ center G ∧ IsSimpleGroup (G ⧸ A)

variable {G}

/-- **A group is quasisimple if and only if it is perfect and its quotient by its centre is
simple** (LMFDB `group.quasisimple`): the central subgroup with simple quotient is the centre. -/
lemma isQuasisimple_iff_isSimpleGroup_quotient_center :
    IsQuasisimple G ↔ Group.IsPerfect G ∧ IsSimpleGroup (G ⧸ center G) := by
  refine ⟨fun ⟨hP, A, hA, hAZ, hS⟩ ↦ ⟨hP, ?_⟩,
    fun ⟨hP, hS⟩ ↦ ⟨hP, center G, inferInstance, le_rfl, hS⟩⟩
  have hZ : ((center G).map (QuotientGroup.mk' A)).Normal :=
    Normal.map inferInstance _ (QuotientGroup.mk'_surjective A)
  rcases hZ.eq_bot_or_eq_top with h | h
  · have hZA : center G ≤ A :=
      ((Subgroup.map_eq_bot_iff _).mp h).trans (QuotientGroup.ker_mk' A).le
    rcases hAZ.antisymm hZA with rfl
    exact hS
  · have hc : IsMulCommutative (G ⧸ A) := by
      refine ⟨⟨fun x y ↦ ?_⟩⟩
      rcases h.ge (mem_top x) with ⟨a, ha, rfl⟩
      rcases h.ge (mem_top y) with ⟨b, -, rfl⟩
      rw [← map_mul, ← map_mul, mem_center_iff.mp ha b]
    exact absurd IsPerfect.subsingleton_of_isMulCommutative (not_subsingleton (G ⧸ A))

/-- **Non-abelian simple groups are quasisimple** (LMFDB `group.quasisimple`). -/
lemma IsSimpleGroup.isQuasisimple [IsSimpleGroup G] (hG : ¬IsMulCommutative G) : IsQuasisimple G :=
  ⟨⟨(eq_bot_or_eq_top_of_normal (commutator G)).resolve_left (hG ∘ (commutator_eq_bot_iff G).mp)⟩,
    ⊥, inferInstance, bot_le, QuotientGroup.quotientBot.isSimpleGroup⟩
