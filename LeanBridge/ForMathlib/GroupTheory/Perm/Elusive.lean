import Mathlib.Combinatorics.Derangements.Basic
import TauCeti.GroupTheory.Perm.PermCongr

/-!
# Elusive permutation groups

A transitive permutation group is elusive if none of its elements of prime order is
fixed-point-free. By a theorem of Fein, Kantor and Schacher, every transitive permutation group of
degree at least two has a fixed-point-free element of prime-power order, so the elusive groups are
those for which such an element can never be chosen of prime order.

## Main definitions

* `Subgroup.IsElusive` (LMFDB `gg.elusive_group`).

## Main results

* `Subgroup.isElusive_map_permCongrHom_iff`: being elusive does not depend on the numbering of the
  points.
* `Subgroup.isElusive_map_conj_iff`: being elusive is invariant under conjugation in the symmetric
  group, so it is a property of the conjugacy class of a transitive group, the class that a label
  `nTt` records.
-/

open Equiv MulAction

namespace Subgroup

variable {α β : Type*} (H : Subgroup (Perm α)) (e : α ≃ β)

/-- A permutation group `H ≤ Sym(α)` is **elusive** (LMFDB `gg.elusive_group`) if it is transitive
and none of its elements of prime order is a derangement, that is, fixed-point-free. -/
structure IsElusive : Prop where
  isPretransitive : IsPretransitive H α
  notMem_derangements : ∀ σ ∈ H, (orderOf σ).Prime → σ ∉ derangements α

variable {H}

lemma IsElusive.map_permCongrHom (h : H.IsElusive) :
    (H.map e.permCongrHom.toMonoidHom).IsElusive := by
  refine ⟨(isPretransitive_map_permCongrHom_iff e H).mpr h.1, ?_⟩
  rintro _ ⟨σ, hσ, rfl⟩ hp hd
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hp
  exact h.2 σ hσ hp fun x hx ↦ hd (e x) (by simp [hx])

variable (H)

/-- **Being elusive does not depend on the numbering of the points**: transporting a permutation
group along a bijection `α ≃ β` preserves it. -/
lemma isElusive_map_permCongrHom_iff :
    (H.map e.permCongrHom.toMonoidHom).IsElusive ↔ H.IsElusive := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map_permCongrHom e⟩
  have h' : ((H.map e.permCongrHom.toMonoidHom).map e.symm.permCongrHom.toMonoidHom).IsElusive :=
    h.map_permCongrHom e.symm
  rwa [map_map, ← permCongrHom_symm, MulEquiv.toMonoidHom_eq_coe, MulEquiv.toMonoidHom_eq_coe,
    MulEquiv.toMonoidHom_symm_comp_toMonoidHom, map_id] at h'

/-- **Being elusive is invariant under conjugation in the symmetric group**, so it is a property of
the conjugacy class of a permutation group. -/
lemma isElusive_map_conj_iff (τ : Perm α) :
    (H.map (MulAut.conj τ).toMonoidHom).IsElusive ↔ H.IsElusive := by
  rw [conj_eq_permCongrHom, isElusive_map_permCongrHom_iff]

end Subgroup
