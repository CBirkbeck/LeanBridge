import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# The least primitive root modulo a prime

Sutherland's labels for subgroups of `GL₂(𝔽_p)`, which the LMFDB uses (LMFDB `gl2.borel`,
`gl2.split_cartan`, `gl2.nonsplit_cartan`, `gl2.normalizer_split_cartan`,
`gl2.normalizer_nonsplit_cartan`), are normalised by the least positive integer generating
`(ℤ/pℤ)ˣ`, written `r` or `ε`. It is a non-square modulo every odd prime, which is what makes the
matrices `!![x, ε * y; y, x]` of the non-split Cartan subgroup `Cn` invertible.

## Main definitions

* `ZMod.leastPrimitiveRoot p`: the least positive integer whose class generates `(ℤ/pℤ)ˣ`.

## Main results

* `ZMod.orderOf_leastPrimitiveRoot`: its class has multiplicative order `p - 1`.
* `ZMod.leastPrimitiveRoot_le`: it is at most every positive integer whose class has order `p - 1`.
* `ZMod.not_isSquare_leastPrimitiveRoot`: it is not a square modulo an odd prime `p`.
-/

namespace ZMod

variable (p : ℕ) [Fact p.Prime]

lemma exists_pos_orderOf_eq : ∃ r : ℕ, 0 < r ∧ orderOf (r : ZMod p) = p - 1 := by
  rcases IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ) with ⟨g, hg⟩
  refine ⟨(g : ZMod p).val, val_pos.mpr g.ne_zero, ?_⟩
  rw [natCast_zmod_val, orderOf_units, hg, Nat.card_eq_fintype_card, card_units]

/-- The **least primitive root** modulo a prime `p`: the least positive integer `r` whose class
generates `(ℤ/pℤ)ˣ`, that is, has multiplicative order `p - 1`. It is the `r` (or `ε`) of
Sutherland's labels for subgroups of `GL₂(𝔽_p)`; for `p = 2` it is `1`. -/
noncomputable def leastPrimitiveRoot : ℕ :=
  Nat.find (exists_pos_orderOf_eq p)

lemma leastPrimitiveRoot_pos : 0 < leastPrimitiveRoot p :=
  (Nat.find_spec (exists_pos_orderOf_eq p)).1

/-- The class of the least primitive root generates `(ℤ/pℤ)ˣ`: its order is `p - 1`. -/
lemma orderOf_leastPrimitiveRoot : orderOf (leastPrimitiveRoot p : ZMod p) = p - 1 :=
  (Nat.find_spec (exists_pos_orderOf_eq p)).2

variable {p} in
/-- **The least primitive root is least**: it is at most every positive integer whose class
generates `(ℤ/pℤ)ˣ`. -/
lemma leastPrimitiveRoot_le {r : ℕ} (hr : 0 < r) (h : orderOf (r : ZMod p) = p - 1) :
    leastPrimitiveRoot p ≤ r :=
  Nat.find_min' _ ⟨hr, h⟩

lemma leastPrimitiveRoot_ne_zero : (leastPrimitiveRoot p : ZMod p) ≠ 0 :=
  (orderOf_pos_iff.mp <| (orderOf_leastPrimitiveRoot p).symm ▸
    Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt).isUnit.ne_zero

/-- The least primitive root modulo an odd prime is a quadratic non-residue. -/
lemma not_isSquare_leastPrimitiveRoot (hp : p ≠ 2) : ¬IsSquare (leastPrimitiveRoot p : ZMod p) := by
  rw [euler_criterion p (leastPrimitiveRoot_ne_zero p)]
  intro h
  have h₂ : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h₃ : p - 1 ≤ p / 2 :=
    Nat.le_of_dvd (by omega) (orderOf_leastPrimitiveRoot p ▸ orderOf_dvd_of_pow_eq_one h)
  omega

end ZMod
