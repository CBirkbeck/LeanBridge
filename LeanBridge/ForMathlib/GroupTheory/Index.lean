import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Ring

/-!
# The index of a subgroup in its product with a normal subgroup

For subgroups `A` and `N` of a group, with `N` normal, Mathlib proves `[A N : N] = [A : A ∩ N]`.
This file adds the product formula `#(A N) #(A ∩ N) = #A #N` and, for a finite group, the other
half of the second isomorphism theorem, `[A N : A] = [N : A ∩ N]`.
-/

namespace Subgroup

variable {G : Type*} [Group G] (A N : Subgroup G) [N.Normal]

lemma card_sup_mul_card_inf : Nat.card ↥(A ⊔ N) * Nat.card ↥(A ⊓ N) = Nat.card A * Nat.card N := by
  have h₁ : N.relIndex (A ⊔ N) * Nat.card ↥(N ⊓ (A ⊔ N)) = Nat.card ↥(A ⊔ N) :=
    N.relIndex_mul_card _
  have h₂ : N.relIndex A * Nat.card ↥(N ⊓ A) = Nat.card A := N.relIndex_mul_card A
  rw [inf_of_le_left le_sup_right, relIndex_sup_right] at h₁
  rw [← h₁, ← h₂, inf_comm A N]
  ring1

variable [Finite G] in
lemma relIndex_sup_of_normal : A.relIndex (A ⊔ N) = A.relIndex N := by
  have h₁ : A.relIndex (A ⊔ N) * Nat.card ↥(A ⊓ (A ⊔ N)) = Nat.card ↥(A ⊔ N) :=
    A.relIndex_mul_card _
  have h₂ : A.relIndex N * Nat.card ↥(A ⊓ N) = Nat.card N := A.relIndex_mul_card N
  rw [inf_of_le_left le_sup_left] at h₁
  refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos Nat.card_pos Nat.card_pos :
    0 < Nat.card A * Nat.card ↥(A ⊓ N)) ?_
  rw [← mul_assoc, h₁, card_sup_mul_card_inf, ← h₂]
  ring1

end Subgroup
