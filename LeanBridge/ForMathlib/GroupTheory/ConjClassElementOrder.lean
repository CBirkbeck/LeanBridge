import LeanBridge.ForMathlib.GroupTheory.Label.ConjClass
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The common order of the elements of a conjugacy class

The LMFDB draws a finite group as disks, one for each conjugacy class, coloured and placed
according to the order `o` of the elements of the class (LMFDB `group.picture_description`). That
order is well defined: all elements of a conjugacy class have the same order, LeanBridge's
`IsConj.orderOf_eq`, so that a class `c` has an order `c.elementOrder`
(`ConjClasses.elementOrder`). The colour is read off the decomposition `o = 2 ^ A × (odd)` with
`A = v₂(o)`: in a finite group `o` is positive, so its part prime to `2` is odd. The disks are
placed by the number of prime factors of `o`, counted with multiplicity, with the identity at the
centre: its class is the only one of order `1`, the only order without a prime factor. The rest of
the knowl, the sizes, colours and positions of the disks, is a display convention.

## Main results

* `ConjClasses.orderOf_eq_elementOrder`: every element of a conjugacy class has the order of the
  class.
* `ConjClasses.elementOrder_eq_one_iff`: the class of the identity is the only conjugacy class of
  order `1`.
* `ConjClasses.odd_elementOrder_div_two_pow`: in a finite group, the order of a conjugacy class
  divided by `2 ^ v₂` of it is odd.
-/

namespace ConjClasses

variable {G : Type*} [Group G] {c : ConjClasses G}

/-- **All elements of a conjugacy class have the same order** (LMFDB `group.picture_description`),
the order `c.elementOrder` of the class. -/
lemma orderOf_eq_elementOrder {x : G} (hx : x ∈ c.carrier) : orderOf x = c.elementOrder :=
  congrArg elementOrder <| mem_carrier_iff_mk_eq.mp hx

/-- **The class of the identity is the only conjugacy class of order `1`** (LMFDB
`group.picture_description`): it is the disk at the centre of the LMFDB's picture, the only one
whose order has no prime factor (Mathlib's
`ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one`). -/
lemma elementOrder_eq_one_iff : c.elementOrder = 1 ↔ c = 1 := by
  rcases mk_surjective c with ⟨x, rfl⟩
  rw [elementOrder_mk, orderOf_eq_one_iff, one_eq_mk_one, mk_eq_mk_iff_isConj, isConj_one_left]

/-- **The order of a conjugacy class is `2 ^ A` times an odd number, `A = v₂(o)`** (LMFDB
`group.picture_description`), in a finite group: `o / 2 ^ v₂(o)` is odd, and
`2 ^ v₂(o) * (o / 2 ^ v₂(o)) = o` is Mathlib's `Nat.ordProj_mul_ordCompl_eq_self`. -/
lemma odd_elementOrder_div_two_pow [Finite G] :
    Odd (c.elementOrder / 2 ^ c.elementOrder.factorization 2) := by
  rcases mk_surjective c with ⟨x, rfl⟩
  rw [elementOrder_mk]
  exact Nat.coprime_two_left.mp <| Nat.coprime_ordCompl Nat.prime_two (orderOf_pos x).ne'

end ConjClasses
