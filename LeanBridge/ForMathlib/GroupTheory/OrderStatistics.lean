import Mathlib.GroupTheory.OrderOfElement

/-!
# The order statistics of a finite group

The order statistics determine the number of solutions of `g ^ 2 = 1`, which isomorphic groups
share; it tells many groups of the same order apart.

## Main definitions

* `Monoid.orderStatistics` (LMFDB `group.order_stats`): the multiset of the orders of the elements
  of a finite group.
-/

namespace Monoid

variable (G : Type*) [Monoid G] [Fintype G]

/-- The **order statistics** (LMFDB `group.order_stats`) of a finite group `G`: the multiset of the
orders `orderOf g` of its elements `g`, each order counted with multiplicity the number of elements
of that order. -/
noncomputable def orderStatistics : Multiset ℕ :=
  (Finset.univ : Finset G).val.map orderOf

lemma card_orderStatistics : (orderStatistics G).card = Fintype.card G :=
  Multiset.card_map _ _

lemma count_orderStatistics (n : ℕ) :
    (orderStatistics G).count n = (Finset.univ.filter fun g : G ↦ orderOf g = n).card := by
  rw [orderStatistics, Multiset.count_map, ← Finset.filter_val, Finset.card_val]
  simp only [eq_comm]

end Monoid

lemma MulEquiv.card_sq_eq_one {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    Nat.card {g : G // g ^ 2 = 1} = Nat.card {h : H // h ^ 2 = 1} :=
  Nat.card_congr <| f.toEquiv.subtypeEquiv fun g ↦ by
    rw [← f.map_eq_one_iff, map_pow]
    rfl
