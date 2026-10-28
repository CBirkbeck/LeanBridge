import Mathlib.GroupTheory.OrderOfElement

/-!
# The order statistics of a finite group

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
