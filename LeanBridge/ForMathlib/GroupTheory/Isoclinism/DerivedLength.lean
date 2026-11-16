import LeanBridge.ForMathlib.GroupTheory.IsoclinismInvariants
import Mathlib.GroupTheory.IsPerfect

/-!
# The derived length of isoclinic groups

Isoclinic groups `G` and `H` (LMFDB `group.isoclinism`) have isomorphic commutator subgroups, and
from its first term on, the derived series of a group is that of its commutator subgroup. So the
derived length of LMFDB `group.derived_series`, the index at which the derived series becomes
stationary, is the same for `G` and `H` when both are perfect or neither is. This covers the
nontrivial solvable groups, which are not perfect, and non-solvable groups such as `S₅` and
`S₅ × C₂` as well. The hypothesis cannot be dropped: `A₅` and `A₅ × C₂` are isoclinic, of derived
lengths `0` and `1`.

The trivial group, which is perfect, is the exception that LMFDB `group.isoclinism` makes: its
nilpotency class and derived length, both `0`, differ from those of every nontrivial group
isoclinic to it.

## Main results

* `Group.IsIsoclinic.derivedLength_eq_of_isPerfect_iff` (LMFDB `group.isoclinism`): isoclinic
  groups that are both perfect or both not perfect have the same derived length.
* `Group.IsIsoclinic.nilpotencyClass_ne_of_subsingleton` (LMFDB `group.isoclinism`): the nilpotency
  class of the trivial group differs from that of every nontrivial group isoclinic to it.
* `Group.IsIsoclinic.derivedLength_ne_of_subsingleton` (LMFDB `group.isoclinism`): so does its
  derived length.
-/

open Subgroup

namespace Group.IsIsoclinic

variable {G H : Type*} [Group G] [Group H]

lemma derivedSeries_add_two_eq_iff (h : IsIsoclinic G H) (n : ℕ) :
    derivedSeries G (n + 2) = derivedSeries G (n + 1) ↔
      derivedSeries H (n + 2) = derivedSeries H (n + 1) := by
  rcases h with ⟨e⟩
  rw [← map_subtype_derivedSeries_commutator (G := G) (n + 1),
    ← map_subtype_derivedSeries_commutator (G := G) n,
    ← map_subtype_derivedSeries_commutator (G := H) (n + 1),
    ← map_subtype_derivedSeries_commutator (G := H) n,
    (map_injective (subtype_injective _)).eq_iff, (map_injective (subtype_injective _)).eq_iff,
    ← map_derivedSeries_eq (f := e.commutatorEquiv.toMonoidHom) e.commutatorEquiv.surjective,
    ← map_derivedSeries_eq (f := e.commutatorEquiv.toMonoidHom) e.commutatorEquiv.surjective,
    (map_injective e.commutatorEquiv.injective).eq_iff]

/-- **The derived length is an isoclinism invariant of the groups that are both perfect or both not
perfect** (LMFDB `group.isoclinism`, with the derived length of `group.derived_series`): from its
first term on, the derived series of a group is that of its commutator subgroup. -/
lemma derivedLength_eq_of_isPerfect_iff (h : IsIsoclinic G H) (hGH : IsPerfect G ↔ IsPerfect H) :
    derivedLength G = derivedLength H :=
  congrArg sInf <| Set.ext fun
    | 0 => isPerfect_def.symm.trans <| hGH.trans isPerfect_def
    | k + 1 => h.derivedSeries_add_two_eq_iff k

/-- **The trivial group is an exception for the nilpotency class** (LMFDB `group.isoclinism`): its
nilpotency class is `0`, and that of every nontrivial group isoclinic to it is not. -/
lemma nilpotencyClass_ne_of_subsingleton [Subsingleton G] [Nontrivial H] (h : IsIsoclinic G H) :
    nilpotencyClass G ≠ nilpotencyClass H := by
  have : IsNilpotent H := h.isNilpotent_iff.mp inferInstance
  rw [nilpotencyClass_zero_iff_subsingleton.mpr ‹_›, ne_comm, Ne,
    nilpotencyClass_zero_iff_subsingleton]
  exact not_subsingleton H

/-- **The trivial group is an exception for the derived length** (LMFDB `group.isoclinism`): its
derived length is `0`, and that of every nontrivial group isoclinic to it is not. -/
lemma derivedLength_ne_of_subsingleton [Subsingleton G] [Nontrivial H] (h : IsIsoclinic G H) :
    derivedLength G ≠ derivedLength H := by
  have hH : commutator H = ⊥ := (h.derivedSeries_succ_eq_bot_iff 0).mp <| Subsingleton.elim _ _
  rw [derivedLength, derivedLength, Nat.sInf_eq_zero.mpr <| .inl <| Subsingleton.elim _ _,
    ne_comm, Ne, Nat.sInf_eq_zero, not_or]
  exact ⟨fun h₀ ↦ bot_ne_top <| hH.symm.trans h₀,
    Set.nonempty_iff_ne_empty.mp ⟨1, by simp [hH]⟩⟩

end Group.IsIsoclinic
