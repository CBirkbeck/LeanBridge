import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Solvable

/-!
# Metabelian groups

## Main definitions

* `IsMetabelian` (LMFDB `group.metabelian`).

## Main results

* `isMetabelian_iff_derivedSeries_two`: `G` is metabelian if and only if `G⁽²⁾ = 1`.
* `isMetabelian_iff_exists_normal`: `G` is metabelian if and only if it is an extension of an
  abelian group by an abelian group.
* The instance `Group.IsSolvable G` for metabelian `G`.
-/

variable (G : Type*) [Group G]

/-- A group is **metabelian** (LMFDB `group.metabelian`) if its commutator subgroup is abelian. -/
@[mk_iff] class IsMetabelian : Prop where
  isMulCommutative_commutator : IsMulCommutative (commutator G)

/-- A group is metabelian if and only if the second term of its derived series is trivial. -/
lemma isMetabelian_iff_derivedSeries_two : IsMetabelian G ↔ derivedSeries G 2 = ⊥ := by
  rw [isMetabelian_iff, derivedSeries_succ, derivedSeries_one, Subgroup.commutator_self_eq_bot_iff]

/-- A group is metabelian if and only if it has an abelian normal subgroup with abelian quotient. -/
lemma isMetabelian_iff_exists_normal : IsMetabelian G ↔
    ∃ (N : Subgroup G) (_ : N.Normal), IsMulCommutative N ∧ IsMulCommutative (G ⧸ N) := by
  refine ⟨fun h ↦ ⟨commutator G, inferInstance, h.1, ?_⟩, fun ⟨N, hN, hN1, hN2⟩ ↦ ⟨?_⟩⟩
  · have hA : IsMulCommutative (Abelianization G) := inferInstance
    exact hA
  · have hle : commutator G ≤ N := by
      refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ ↦ ?_
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact hN2.is_comm.comm _ _
    rw [← Subgroup.commutator_self_eq_bot_iff, eq_bot_iff,
      ← Subgroup.commutator_self_eq_bot_iff.mpr hN1]
    exact Subgroup.commutator_mono hle hle

instance [IsMulCommutative G] : IsMetabelian G :=
  ⟨inferInstance⟩

instance [IsMetabelian G] : Group.IsSolvable G :=
  ⟨⟨2, (isMetabelian_iff_derivedSeries_two G).mp inferInstance⟩⟩
