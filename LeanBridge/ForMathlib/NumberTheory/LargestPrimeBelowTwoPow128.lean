import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

/-!
# The largest prime below `2 ^ 128`

To label the divisions and conjugacy classes of finite groups, the LMFDB picks pseudo-random group
elements with the exponential generator `a_j = a_0 b ^ j mod p`, where
`p = 340282366920938463463374607431768211297` is "the largest prime less than `2^128`" (LMFDB
`group.pseudo_random_elements`). We prove that statement.

The number `p = 2 ^ 128 - 159` is prime by Lucas's test (Mathlib's `lucas_primality`) with the
witness `5`: `5 ^ (p - 1) = 1` and `5 ^ ((p - 1) / q) ≠ 1` modulo `p` for each prime factor `q` of
`p - 1 = 2 ^ 5 · 3 · 10253 · 29333 · 4454477 · 42113237 · 62826870453001`. The last factor is
certified in the same way, with the witness `11` and
`62826870453000 = 2 ^ 3 · 3 · 5 ^ 3 · 73 · 13147 · 21821`, and the other factors by `norm_num`. The
`158` numbers `n` between `p` and `2 ^ 128` are composite, since `2 ^ (n - 1) ≠ 1` modulo `n`,
against Fermat's little theorem. The modular powers are evaluated by `reduce_mod_char`. The
generator, its constants `a_0` and `b` and the sequences of group elements built from it are
database conventions.

## Main results

* `Nat.prime_two_pow_128_sub_159`: `2 ^ 128 - 159` is prime.
* `Nat.isGreatest_prime_lt_two_pow_128`: it is the largest prime below `2 ^ 128`.
-/

namespace Nat

variable {n : ℕ}

lemma two_pow_128_sub_159 : 2 ^ 128 - 159 = 340282366920938463463374607431768211297 :=
  rfl

private lemma mem_of_prime_dvd {q k : ℕ} (hq : q.Prime) {l : List ℕ} (hl : ∀ r ∈ l, r.Prime)
    (hn : n ∣ l.prod ^ k) (h : q ∣ n) : q ∈ l :=
  mem_list_primes_of_dvd_prod hq.prime (fun r hr ↦ (hl r hr).prime) <| hq.dvd_of_dvd_pow <|
    h.trans hn

private lemma prime_62826870453001 : Nat.Prime 62826870453001 := by
  refine lucas_primality _ 11 (by reduce_mod_char) fun q hq hqd ↦ ?_
  have hmem : q ∈ [2, 3, 5, 73, 13147, 21821] :=
    mem_of_prime_dvd (k := 3) hq (by norm_num) (by norm_num) hqd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals reduce_mod_char
  all_goals decide

/-- **`2 ^ 128 - 159` is prime** (LMFDB `group.pseudo_random_elements`), by Lucas's test with the
witness `5`. -/
lemma prime_two_pow_128_sub_159 : Nat.Prime 340282366920938463463374607431768211297 := by
  refine lucas_primality _ 5 (by reduce_mod_char) fun q hq hqd ↦ ?_
  have hl : ∀ r ∈ [2, 3, 10253, 29333, 4454477, 42113237, 62826870453001], r.Prime := by
    simp only [List.forall_mem_cons]
    exact ⟨prime_two, prime_three, by norm_num, by norm_num, by norm_num, by norm_num,
      prime_62826870453001, fun _ h ↦ absurd h List.not_mem_nil⟩
  have hmem : q ∈ [2, 3, 10253, 29333, 4454477, 42113237, 62826870453001] :=
    mem_of_prime_dvd (k := 5) hq hl (by norm_num) hqd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals reduce_mod_char
  all_goals decide

private lemma not_prime_of_two_pow_ne_one (hn : 2 < n) (h : (2 : ZMod n) ^ (n - 1) ≠ 1) :
    ¬n.Prime := by
  intro hp
  have : Fact n.Prime := ⟨hp⟩
  refine h (ZMod.pow_card_sub_one_eq_one fun h2 ↦ ?_)
  have hdvd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp (by exact_mod_cast h2)
  exact (le_of_dvd two_pos hdvd).not_gt hn

/-- **`2 ^ 128 - 159` is the largest prime below `2 ^ 128`** (LMFDB
`group.pseudo_random_elements`): it is prime, and each of the `158` numbers `n` between it and
`2 ^ 128` is composite, as `2 ^ (n - 1) ≠ 1` modulo `n`. -/
lemma isGreatest_prime_lt_two_pow_128 :
    IsGreatest {q : ℕ | q.Prime ∧ q < 2 ^ 128} 340282366920938463463374607431768211297 := by
  refine ⟨⟨prime_two_pow_128_sub_159, by norm_num⟩, fun q ⟨hq, hq2⟩ ↦ ?_⟩
  by_contra! h
  interval_cases q
  all_goals exact not_prime_of_two_pow_ne_one (by norm_num) (by reduce_mod_char; decide) hq

end Nat
