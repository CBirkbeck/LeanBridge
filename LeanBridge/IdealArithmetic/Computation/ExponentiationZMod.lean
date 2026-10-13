/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import Mathlib.Tactic

/-!

Algorithm and tactic for simplifying modular exponentiation.

## Main definition
- `squareAndMultiply`: the square and multiply algorithm in its tail recursive version.

## Tactics
- `zmod_pow`: simplifies expressions of the form `(a : ZMod m) ^ n`. -/

-- NOTE: we operate in ℕ (this is faster) and reduce at every step.
@[reducible]
def squareAndMultiply_aux (m b e res : ℕ) : ℕ :=
  match e with
    | 0 => res
    | Nat.succ e =>
      let res' := if (Nat.add e 1) % 2 = 1 then (Nat.mul res b) % m else res
      squareAndMultiply_aux m ((b * b) % m) ((Nat.add e 1) / 2) res'


lemma squareAndMultiply_aux_eq_pow {m b e res} :
    (squareAndMultiply_aux m b e res : ZMod m) = res * (b : ZMod m) ^ e := by
  revert b res
  induction' e using Nat.binaryRec with bit e hi
  · intro b res
    simp only [squareAndMultiply_aux, pow_zero, mul_one]
    rfl
  · intro b res
    cases bit
    · by_cases he : e = 0
      · rw [he, Nat.bit_false_zero, pow_zero, mul_one] ; rfl
      · have : Nat.bit false e ≠ 0 := by
          simp only [ne_eq, Nat.bit_eq_zero_iff, he, and_true, not_false_eq_true]
        obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero this
        have heven : (a + 1) % 2 ≠ 1 := by
          simp only [ne_eq, Nat.mod_two_not_eq_one]
          refine Eq.symm (Nat.eq_of_beq_eq_true ?_)
          show Nat.beq 0 (a.succ % 2) = true
          rw [← ha, Nat.bit_mod_two]
          rfl
        unfold squareAndMultiply_aux
        simp only [ha, heven, ↓reduceIte, Nat.succ_eq_add_one]
        have : (a + 1) / 2 = e := by show a.succ / 2 = e  ; rw [← ha, Nat.bit_div_two]
        simp only [this, hi, ZMod.natCast_mod, ← sq, Nat.cast_pow, ← pow_mul]
        congr
    · have : Nat.bit true e ≠ 0 := by
        simp only [ne_eq, Nat.bit_eq_zero_iff, Bool.true_eq_false, and_false, not_false_eq_true]
      obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero this
      have hneven : (a + 1) % 2 = 1 := by
        refine Nat.mod_two_ne_zero.mp ?_
        refine Ne.symm (Nat.ne_of_beq_eq_false ?_)
        show Nat.beq 0 (a.succ % 2) = false
        rw [← ha, Nat.bit_mod_two]
        rfl
      unfold squareAndMultiply_aux
      simp only [ha, hneven, ↓reduceIte, Nat.succ_eq_add_one]
      have : (a + 1) / 2 = e := by show a.succ / 2 = e ; rw [← ha, Nat.bit_div_two]
      simp only [this, hi, ZMod.natCast_mod, ← sq, Nat.cast_pow, ← pow_mul]
      suffices haux : a + 1 = 2 * e + 1  by
        rw [haux]
        simp only [Nat.mul_eq, Nat.cast_mul]
        ring
      exact id (Eq.symm ha)

@[reducible]
def squareAndMultiply (b e m : ℕ) : ℕ := squareAndMultiply_aux m (b % m) e 1

/-- Proof of correctness of `squareAndMultiply`. -/
lemma squareAndMultiply_eq_pow {m b e} :
    (squareAndMultiply b e m : ZMod m) = (b : ZMod m) ^ e := by
  unfold squareAndMultiply
  rw [squareAndMultiply_aux_eq_pow ]
  simp only [Nat.cast_one, ZMod.natCast_mod, one_mul]


/-- Tactic to simplify expressions of the form `(a : ZMod m) ^ n` using a tail-recursive algorithm. -/
macro "zmod_pow" : tactic =>
  `(tactic| (
    try simp only [Int.cast_ofNat]
    erw [← squareAndMultiply_eq_pow]
    repeat (unfold squareAndMultiply_aux ; dsimp)
    try decide
  ))

-- EXAMPLES


example : (3 : ZMod 30) ^ 11002324556787 = 27  := by
  zmod_pow

example : (3 : ZMod 10020313) ^ 11002324556787 ≠ 1  := by
  zmod_pow

@[reducible]
def P := ![35567,300,4569876,578]

example : ∀ i, (3 : ZMod 12838) ^ (P i) ≠ 1 := by
  intro i ; fin_cases i ; repeat zmod_pow
