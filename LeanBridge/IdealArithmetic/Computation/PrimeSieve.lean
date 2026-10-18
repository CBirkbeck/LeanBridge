/-
Copyright (c) 2025 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Ordmap.Ordset
import Batteries.Data.RBMap.WF
import Lean.Data.RBTree
import Mathlib.Tactic

/-! # The Segmented Prime Sieve

Implements the segmented prime sieve of Eratosthenes.

# Main definition:
- `PrimeSieve`: computes all the prime numbers in a given interval.

# Main result:
- `PrimeSieve_mem` : proves correctness of the program.  -/

def PrimeSieve_loop (P : List ℕ) (cont : ℕ) (accum : List ℕ) : List ℕ :=
  match cont , accum with
  | 0, accum => accum
  | cont + 1 , accum => if h : cont + 1 < P.length then
    PrimeSieve_loop P cont (List.filter
      (fun x => x ≠ P[cont + 1] → x.mod P[cont + 1] ≠ 0 ) accum) else []

/-- The Segmented Prime Sieve:
  Computes a list of all the primes `p` such that `A < p ≤ B`. For correctness, `L` must be
  a list with `¬ 1 ∈ L` and containing all the primes up to the square root of `B`.
  Tail recursive implementation. -/
def PrimeSieve (A : ℕ) (B : ℕ) (L : List ℕ) : List ℕ :=
  let P := (0 :: L)
  let m := List.length L
  let r := B - A
  (PrimeSieve_loop P m ((List.range r).map (fun k => A + 1 + k) ))

/- Proof of correctness of `PrimeSieve`.   -/

lemma PrimeSieve_loop_sublist_aux {P : List ℕ} {c : ℕ} (hcl : c < P.length) {L₁ L₂ : List ℕ}
    (hL : L₁.Sublist L₂)  : (PrimeSieve_loop P c L₁).Sublist (PrimeSieve_loop P c L₂) := by
  revert L₁ L₂
  induction c with
  | zero =>
    intro L₁ L₂ hL
    simp only [PrimeSieve_loop, hL]
  | succ c hc =>
    intro L₁ L₂ hL
    simp only [PrimeSieve_loop, hcl, ↓reduceDIte, ne_eq]
    exact hc (show c < P.length by omega) (List.Sublist.filter _ hL)

lemma PrimeSieve_loop_sublist {P : List ℕ} {c d : ℕ} (h : c ≤ d)
    (hdd : d < P.length) (L : List ℕ) :
    (PrimeSieve_loop P d L).Sublist (PrimeSieve_loop P c L) := by
  induction d with
  | zero => rw [nonpos_iff_eq_zero.1 h]
  | succ d hd =>
    have hdaux : d < P.length := by omega
    have haux: (PrimeSieve_loop P (d + 1) L).Sublist (PrimeSieve_loop P d L) := by
      simp only [PrimeSieve_loop, hdd, ↓reduceDIte]
      refine PrimeSieve_loop_sublist_aux hdaux ?_
      simp only [ ne_eq, List.filter_sublist]
    by_cases hi : c ≤ d
    · refine List.Sublist.trans haux (hd hi hdaux)
    · rw [(show (c = d + 1) by omega )]

lemma PrimeSieve_loop_multiples_aux (P : List ℕ)  (i : ℕ)
    (hdd : i < P.length) (L : List ℕ)
    (n : ℕ) (hz : P[0] = 0) (hn : P[i] ∣ n) (hneq : n ≠ P[i]) :
    ¬ n ∈ PrimeSieve_loop P i L := by
  match i with
  | 0 =>
    simp only [hz, zero_dvd_iff] at hn
    simp only [hn, hz, ne_eq, not_true_eq_false] at hneq
  | i + 1 =>
    simp only [PrimeSieve_loop, hdd, ↓reduceDIte, ne_eq]
    intro hnn
    have hnaux : n ∈ PrimeSieve_loop P 0
      ((List.filter (fun x => x ≠ P[i+ 1] → x.mod P[i + 1] ≠ 0 ) L)):= by
      refine List.Sublist.mem hnn (PrimeSieve_loop_sublist (by omega) (by omega) _)
    simp only [PrimeSieve_loop, ne_eq, decide_implies, decide_not, dite_eq_ite, ite_not,
      Bool.if_true_left, List.mem_filter, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not] at hnaux
    rw [Nat.dvd_iff_mod_eq_zero] at hn
    rcases hnaux.2 with h1 | h2
    · contradiction
    · contradiction

lemma PrimeSieve_loop_prime_mem {P : List ℕ} {i : ℕ} (hdd : i < P.length)
    {L : List ℕ} {n : ℕ} (hnl : n ∈ L)
    (hn : ∀ k, ∀ h : k ≤ i , P[k] ≠ n → ¬ P[k] ∣ n) :
    n ∈ PrimeSieve_loop P i L := by
  revert L
  induction i with
  | zero => simp only [PrimeSieve_loop, imp_self, implies_true]
  | succ i hi =>
    intro L hnndup
    simp only [PrimeSieve_loop, hdd, ↓reduceDIte, ne_eq, decide_implies, decide_not, dite_eq_ite,
      ite_not, Bool.if_true_left]
    refine hi (by omega) ?_ ?_
    · intro k hk
      exact hn k (by omega)
    · simp only [List.mem_filter, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not]
      refine ⟨hnndup, ?_ ⟩
      by_cases h : n = P[i + 1]
      · left ; exact h
      · right
        erw [← Nat.dvd_iff_mod_eq_zero]
        exact (hn (i + 1) (by omega)) fun a ↦ h (id (Eq.symm a))

/-- If every prime below `Nat.sqrt B + 1` is included in `L`, and `¬ 1 ∈ L`, then `PrimeSieve A B L` consists precisely
on those primes in the interval `A < p ∧ p ≤ B`.  -/
lemma PrimeSieve_mem (A : ℕ) (B : ℕ) (hA : 1 ≤ A) (L : List ℕ)
    (h : ∀ q, Nat.Prime q → q < Nat.sqrt B + 1 → q ∈ L) (hpL : ¬ 1 ∈ L) (p : ℕ)  :
    p ∈ PrimeSieve A B L ↔ Nat.Prime p ∧ A < p ∧ p ≤ B := by
  constructor
  · intro hp
    have hleaux : A < p ∧ p ≤ B := by
      have : p ∈ ((List.range (B - A)).map (fun k => A + 1 + k) ) := by
        refine List.Sublist.mem hp ?_
        refine PrimeSieve_loop_sublist (P := (0 :: L)) (c := 0) (d := List.length L) (by omega)
          (by simp) ((List.map (fun k ↦ A + 1 + k) (List.range (B - A))))
      simp only [List.mem_map, List.mem_range] at this
      omega
    refine ⟨?_, hleaux⟩
    rw [Nat.prime_def_le_sqrt]
    refine ⟨by omega, ?_ ⟩
    intro m hmm hmsq
    let q := Nat.minFac m
    have hqp : Nat.Prime q := Nat.minFac_prime (by omega)
    have hqm : q ≤ m := Nat.minFac_le (by omega)
    suffices ¬ q ∣ p by exact fun hc => this (dvd_trans (Nat.minFac_dvd m) hc)
    have hqmem : q ∈ L := by
      refine h q hqp ?_
      refine lt_of_le_of_lt (le_trans hqm hmsq ) ?_
      refine Order.lt_add_one_iff.mpr (Nat.sqrt_le_sqrt hleaux.2)
    intro hc
    obtain ⟨j, hjl, hj⟩ := List.getElem_of_mem hqmem
    have := (PrimeSieve_loop_multiples_aux (0 :: L) (j + 1) (by simp [hjl])
      ((List.range (B - A)).map (fun k => A + 1 + k) ) p rfl ?_ ?_)
    apply this
    refine List.Sublist.mem hp ?_
    refine PrimeSieve_loop_sublist (P := (0 :: L)) (c := j + 1)
      (d := List.length L) (by omega) (by simp) _
    · simp only [List.getElem_cons_succ, hj, hc]
    · simp only [List.getElem_cons_succ, hj, ne_eq]
      have := lt_of_le_of_lt hmsq (Nat.sqrt_lt_self (n := p) (by omega))
      linarith
  · rintro ⟨hp, hla, hlb⟩
    refine PrimeSieve_loop_prime_mem (i := L.length)
      (L := ((List.range (B - A)).map (fun k => A + 1 + k) )) (n := p) ?_ ?_ ?_
    · simp
    · simp only [List.mem_map, List.mem_range]
      use (p - (A + 1))
      omega
    · intro k hk hneq
      match k with
      | 0 =>
        simp only [List.getElem_cons_zero, zero_dvd_iff, ne_eq]
        exact id (Ne.symm hneq)
      | k + 1 =>
        simp at hneq ⊢
        intro hc
        rw [Nat.dvd_prime hp] at hc
        simp only [hneq, or_false] at hc
        simp only [← hc, List.getElem_mem, not_true_eq_false] at hpL

/-- Specialized version of `PrimeSieve_mem ` where `L` is taken to contain exactly those primes
below `Nat.sqrt B + 1`.  -/
lemma PrimeSieve_mem_of_primesBelow (A : ℕ) (B C : ℕ) (hC : C ≤ B)
    (hA : 1 ≤ A) (L : List ℕ)
    (hL : L.toFinset = Nat.primesBelow (B.sqrt + 1))  (p : ℕ) :
    p ∈ PrimeSieve A C L ↔ Nat.Prime p ∧ A < p ∧ p ≤ C := by
  refine PrimeSieve_mem A C hA L ?_ ?_ p
  · intro q hqp hqlt
    suffices q ∈ L.toFinset by exact List.mem_dedup.mp this
    rw [hL]
    refine Nat.mem_primesBelow.mpr ⟨?_, hqp⟩
    refine lt_of_lt_of_le hqlt ?_
    simp only [add_le_add_iff_right]
    exact Nat.sqrt_le_sqrt hC
  · intro hc
    have : 1 ∈ L.toFinset := by exact List.mem_toFinset.mpr hc
    rw [hL, Nat.mem_primesBelow] at this
    exact Nat.prime_one_false this.2

lemma list_eq_primesBelow {B : ℕ} {L : List ℕ}
    (h : ∀ p, p ∈ L ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ B) :
    L.toFinset = Nat.primesBelow (B + 1) := by
  ext p
  rw [List.mem_toFinset]
  convert h p
  rw [Nat.mem_primesBelow]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ⟨ Nat.Prime.one_lt h2 , by omega⟩ ⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, h1 ⟩

lemma primes_below_append  (e P : List ℕ) (hneq : e ≠ []) (L : List (List ℕ))
  (he : List.Pairwise (fun x1 x2 => x1 < x2) e)
  (hlength : e.length = L.length + 1) (hM : P.toFinset = Nat.primesBelow (Nat.sqrt (e.getLast hneq) + 1) )
  (hez : e[0]'(List.length_pos_iff.mpr hneq) ≠ 0)
  (hl : ∀ i, ∀ h : i + 1 < e.length , PrimeSieve (e[i]) (e[i + 1]) P = L[i]) (p : ℕ) :
  p ∈ List.foldr (fun x y => x ++ y) [] L ↔
    Nat.Prime p ∧ e[0]'(List.length_pos_iff.mpr hneq) < p ∧ p ≤ e.getLast hneq := by
  revert L
  induction e with
  | nil => exact fun L hlength hl ↦ False.elim (hneq rfl)
  | cons e es hes =>
    intro L hlength
    simp only [List.length_cons, add_lt_add_iff_right, List.getElem_cons_succ,
      List.getElem_cons_zero]
    intro hl
    match L with
    | [] =>
      simp only [List.length_cons, List.length_nil, zero_add, Nat.add_eq_right,
        List.length_eq_zero_iff] at hlength
      simp_rw [hlength]
      simp only [List.foldr_nil, List.not_mem_nil, List.getLast_singleton, false_iff, not_and,
        not_le, imp_self, implies_true]
    | (b :: bs) =>
      by_cases hess : es = []
      · simp[hess] at hlength
      · simp
        rw [List.getLast_cons hess]
        haveI : NeZero (e :: es).length := Nat.instNeZeroSucc
        have hlees : e <  es[0]'(List.length_pos_iff.mpr hess) :=
          List.rel_of_pairwise_cons he (List.getElem_mem _)
        have hleql : es[0]'(List.length_pos_iff.mpr hess) ≤ es.getLast hess := by
          rcases es with _ | ⟨a, as⟩
          · exact absurd rfl hess
          · rcases List.mem_cons.1 (List.getLast_mem hess) with h | h
            · exact h.ge
            · exact (List.rel_of_pairwise_cons (List.pairwise_cons.1 he).2 h).le
        have : e < p ∧ p ≤ es.getLast hess ↔ (e < p ∧ p ≤ es[0]'(List.length_pos_iff.mpr hess)) ∨ (es[0]'(List.length_pos_iff.mpr hess) < p ∧  p ≤ es.getLast hess) := by
          constructor
          · rintro ⟨he1, he2⟩
            omega
          · rintro (⟨he1, he2⟩ | ⟨he3, he4⟩)
            · refine ⟨he1, le_trans he2 hleql ⟩
            · refine ⟨lt_trans hlees he3, he4⟩
        rw [this, and_or_left]
        simp at he
        rw [List.getLast_cons hess] at hM
        simp at hlength
        have haux : (p ∈ List.foldr (fun x y ↦ x ++ y) [] bs ↔ Nat.Prime p ∧ es[0] < p ∧ p ≤ es.getLast hess) := by
          apply hes hess he.2 hM ?_ bs hlength
          intro i hi
          refine hl (i + 1) hi
          exact Nat.ne_zero_of_lt hlees
        have := hl 0 (by omega)
        simp only [List.getElem_cons_zero] at this
        refine or_congr ?_ haux
        rw [← this]
        refine PrimeSieve_mem_of_primesBelow e _ _ hleql ?_ P hM p
        simp at hez
        omega

lemma sqrt10000 : Nat.sqrt 10000  = 100 := Nat.sqrt_eq' 100

def primes_below_100 := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

lemma primes_below_100_proof : primes_below_100.toFinset = Nat.primesBelow (Nat.sqrt 10000 + 1) := by
  refine list_eq_primesBelow ?_
  have heq : PrimeSieve 1 100 [2, 3, 5,7] = primes_below_100 := by rfl
  intro p
  rw [← PrimeSieve_mem_of_primesBelow 1 (Nat.sqrt 10000) (Nat.sqrt 10000) (by omega)
    (by omega) [2, 3, 5,7] ?_ p, sqrt10000, heq]
  rw [sqrt10000]
  decide +kernel

-----------

open Ordnode

/-- We extract element in a Ordnode contained in the interval [l₁, l₂].  -/
def Ordnode.extractRangeTree {α : Type*} [LinearOrder α] [DecidableLT α]
  (t : Ordnode α) (l₁ l₂ : α) : Ordnode α :=
  match t with
  | nil => nil
  | node _ l v r =>
    if l₂ < v then -- if the upper limit is too small, we go to the left tree.
      extractRangeTree l l₁ l₂
    else if v < l₁ then --If the lower limit is too big, we look at the right tree.
      extractRangeTree r l₁ l₂
    else -- If the value is in the range, we look at both subtrees.
      let left := extractRangeTree l l₁ l₂
      let right := extractRangeTree r l₁ l₂
      node 0 left v right -- We link them. Balance is violated. This is no longer a Valid tree, but
      -- this makes the proof much easier.

lemma Ordnode.extractRangeTree_emem {α : Type*} [LinearOrder α] [DecidableLT α]
  {t : Ordnode α} (ht : t.Bounded ⊥ ⊤) (l₁ l₂ : α) (x : α) :
    Ordnode.Emem x (Ordnode.extractRangeTree t l₁ l₂)
      ↔ Ordnode.Emem x t ∧ l₁ ≤ x ∧ x ≤ l₂ := by
  induction t with
  | nil => simp [extractRangeTree, Emem, Any]
  | node m t1 v t2 hi1 hi2 =>
    have : (node m t1 v t2).Bounded ⊥ ⊤ = (t1.Bounded ⊥ ↑v ∧ t2.Bounded ↑v ⊤) := by rfl
    rw [this] at ht
    by_cases hl : l₂ < v
    · simp only [extractRangeTree, hl, ↓reduceIte, hi1 (Ordnode.Bounded.weak_right ht.1),
      and_congr_left_iff, and_imp]
      intro ha1 ha2
      constructor
      · intro hmem1
        simp only [Emem, Any]
        left
        exact hmem1
      · intro hmem2
        simp only [Emem, Any] at hmem2
        rcases hmem2 with hc1 | hc2 | hc3
        · exact hc1
        · exfalso
          exact (lt_self_iff_false _ ).1 (lt_of_le_of_lt (hc2 ▸ ha2) hl)
        · have := Ordnode.Bounded.mem_gt ht.2
          rw [Ordnode.all_iff_forall] at this
          specialize this x hc3
          exfalso
          exact (lt_self_iff_false _ ).1 (lt_trans (lt_of_lt_of_le this ha2) hl)
    · by_cases hl2 : v < l₁
      · simp [extractRangeTree, hl, hl2, hi2 (Ordnode.Bounded.weak_left ht.2)]
        intro ha1 ha2
        constructor
        · intro hmem1
          simp only [Emem, Any]
          right ; right
          exact hmem1
        · intro hmem2
          simp only [Emem, Any] at hmem2
          rcases hmem2 with hc1 | hc2 | hc3
          · have := Ordnode.Bounded.mem_lt ht.1
            rw [Ordnode.all_iff_forall] at this
            specialize this x hc1
            exfalso
            exact (lt_self_iff_false _ ).1 (lt_trans hl2 (lt_of_le_of_lt ha1 this))
          · exfalso
            exact (lt_self_iff_false _ ).1 (lt_of_le_of_lt (hc2 ▸ ha1) hl2)
          · exact hc3
      · simp [extractRangeTree, hl, hl2, Emem, Any]
        specialize hi1 (Ordnode.Bounded.weak_right ht.1)
        specialize hi2 (Ordnode.Bounded.weak_left ht.2)
        simp [Emem] at hi1 hi2
        rw [hi1, hi2]
        aesop

lemma Ordnode.extractRangeTree_toList_mem {α : Type*} [LinearOrder α] [DecidableLT α]
  {t : Ordnode α} (ht : t.Bounded ⊥ ⊤) (l₁ l₂ : α) (x : α) :
    x ∈ (Ordnode.extractRangeTree t l₁ l₂).toList  ↔ x ∈ t.toList ∧ l₁ ≤ x ∧ x ≤ l₂ := by
  rw [← Ordnode.emem_iff_mem_toList, ← Ordnode.emem_iff_mem_toList]
  exact Ordnode.extractRangeTree_emem ht l₁ l₂ x

lemma Ordnode.ofList_valid {α : Type*} [Preorder α] [Std.Total fun (x1 x2 : α) => x1 ≤ x2]
  [DecidableLE α] (t : List α) :
  Ordnode.Valid (ofList t) := by
  induction t with
  | nil =>
    simp only [ofList, List.foldr_nil]
    exact valid_nil
  | cons m t1 v =>
    simp only [ofList, List.foldr_cons]
    apply Ordnode.insert.valid
    exact v

lemma Ordnode.ofList_bounded {α : Type*} [Preorder α] [Std.Total fun (x1 x2 : α) => x1 ≤ x2]
  [DecidableLE α] (t : List α) :
  Ordnode.Bounded (ofList t) ⊥ ⊤  := (Ordnode.ofList_valid t).ord

/- Primes below 10,000

Compute all the prime numbers up to 10,000. We use a precomputed list of the primes below 100.
We split things up in intervals of length 300 for smaller proofs and to avoid `maxRecDepth`
(recursion bound on the elaborator) errors, however longer intervals may be considered
with `decide+kernel`, which directly invokes kernel reduction.  -/

def primesBelow10000 :=
  [[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199],
  [211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397],
  [401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599],
  [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797],
  [809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997],
  [1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193],
  [1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399],
  [1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597],
  [1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789],
  [1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999],
  [2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179],
  [2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399],
  [2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593],
  [2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797],
  [2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999],
  [3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191],
  [3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391],
  [3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593],
  [3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797],
  [3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989],
  [4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177],
  [4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397],
  [4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597],
  [4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799],
  [4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999],
  [5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197],
  [5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399],
  [5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591],
  [5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791],
  [5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987],
  [6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199],
  [6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397],
  [6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599],
  [6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793],
  [6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997],
  [7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193],
  [7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393],
  [7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591],
  [7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793],
  [7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993],
  [8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191],
  [8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389],
  [8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599],
  [8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783],
  [8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999],
  [9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199],
   [9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397],
   [9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587],
   [9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791],
   [9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973]]

def e_interval_aux := [1, 200, 400, 600, 800, 1000, 1200, 1400, 1600, 1800, 2000, 2200,
  2400, 2600, 2800, 3000, 3200, 3400, 3600, 3800, 4000, 4200, 4400, 4600, 4800, 5000, 5200, 5400,
  5600, 5800, 6000, 6200, 6400, 6600, 6800, 7000, 7200, 7400, 7600, 7800, 8000, 8200, 8400, 8600, 8800, 9000, 9200, 9400, 9600, 9800,10000]

lemma e_sorted : List.Pairwise (fun x1 x2 => x1 < x2) e_interval_aux := by decide

-- Reach max recursiond depth
/- lemma primesBelow10000_eq_primesBelow_aux_fldr :
  List.foldr (fun x y => x ++ y) [] primesBelow_aux = primesBelow10000 := rfl -/

lemma PB0 : PrimeSieve 1 200 primes_below_100 = primesBelow10000[0] := by decide+kernel
lemma PB200 : PrimeSieve 200 400 primes_below_100 = [211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397] := by decide+kernel
lemma PB400 : PrimeSieve 400 600 primes_below_100 = [401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599] := by decide+kernel
lemma PB600 : PrimeSieve 600 800 primes_below_100 = [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797] := by decide+kernel
lemma PB800 : PrimeSieve 800 1000 primes_below_100 = [809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997] := by decide+kernel
lemma PB1000 : PrimeSieve 1000 1200 primes_below_100 = [1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193] := by decide+kernel
lemma PB1200 : PrimeSieve 1200 1400 primes_below_100 = [1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399] := by decide+kernel
lemma PB1400 : PrimeSieve 1400 1600 primes_below_100 = [1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597] := by decide+kernel
lemma PB1600 : PrimeSieve 1600 1800 primes_below_100 = [1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789] :=by decide+kernel
lemma PB1800 : PrimeSieve 1800 2000 primes_below_100 = [1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999] := by decide+kernel
lemma PB2000 : PrimeSieve 2000 2200 primes_below_100 = [2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179] := by decide+kernel
lemma PB2200 : PrimeSieve 2200 2400 primes_below_100 = [2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399] := by decide+kernel
lemma PB2400 : PrimeSieve 2400 2600 primes_below_100 = [2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593] := by decide+kernel
lemma PB2600 : PrimeSieve 2600 2800 primes_below_100 = [2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797] := by decide+kernel
lemma PB2800 : PrimeSieve 2800 3000 primes_below_100 = [2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999] := by decide+kernel
lemma PB3000 : PrimeSieve 3000 3200 primes_below_100 = [3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191] := by decide+kernel
lemma PB3200 : PrimeSieve 3200 3400 primes_below_100 = [3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391] := by decide+kernel
lemma PB3400 : PrimeSieve 3400 3600 primes_below_100 = [3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593] := by decide+kernel
lemma PB3600 : PrimeSieve 3600 3800 primes_below_100 = [3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797] := by decide+kernel
lemma PB3800 : PrimeSieve 3800 4000 primes_below_100 = [3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989] := by decide+kernel
lemma PB4000 : PrimeSieve 4000 4200 primes_below_100 = [4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177] := by decide+kernel
lemma PB4200 : PrimeSieve 4200 4400 primes_below_100 = [4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397] := by decide+kernel
lemma PB4400 : PrimeSieve 4400 4600 primes_below_100 = [4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597] := by decide+kernel
lemma PB4600 : PrimeSieve 4600 4800 primes_below_100 = [4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799] := by decide+kernel
lemma PB4800 : PrimeSieve 4800 5000 primes_below_100 = [4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999] := by decide+kernel
lemma PB5000 : PrimeSieve 5000 5200 primes_below_100 = [5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197] :=by decide+kernel
lemma PB5200 : PrimeSieve 5200 5400 primes_below_100 = [5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399] := by decide+kernel
lemma PB5400 : PrimeSieve 5400 5600 primes_below_100 = [5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591] := by decide+kernel
lemma PB5600 : PrimeSieve 5600 5800 primes_below_100 = [5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791] := by decide+kernel
lemma PB5800 : PrimeSieve 5800 6000 primes_below_100 = [5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987] := by decide+kernel
lemma PB6000 : PrimeSieve 6000 6200 primes_below_100 = [6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199] := by decide+kernel
lemma PB6200 : PrimeSieve 6200 6400 primes_below_100 = [6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397] := by decide+kernel
lemma PB6400 : PrimeSieve 6400 6600 primes_below_100 = [6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599] := by decide+kernel
lemma PB6600 : PrimeSieve 6600 6800 primes_below_100 = [6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793] := by decide+kernel
lemma PB6800 : PrimeSieve 6800 7000 primes_below_100 = [6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997] := by decide+kernel
lemma PB7000 : PrimeSieve 7000 7200 primes_below_100 = [7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193] := by decide+kernel
lemma PB7200 : PrimeSieve 7200 7400 primes_below_100 = [7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393] :=by decide+kernel
lemma PB7400 : PrimeSieve 7400 7600 primes_below_100 = [7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591] := by decide+kernel
lemma PB7600 : PrimeSieve 7600 7800 primes_below_100 = [7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793] :=by decide+kernel
lemma PB7800 : PrimeSieve 7800 8000 primes_below_100 = [7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993] := by decide+kernel
lemma PB8000 : PrimeSieve 8000 8200 primes_below_100 = [8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191] := by decide+kernel
lemma PB8200 : PrimeSieve 8200 8400 primes_below_100 = [8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389] := by decide+kernel
lemma PB8400 : PrimeSieve 8400 8600 primes_below_100 = [8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599] := by decide+kernel
lemma PB8600 : PrimeSieve 8600 8800 primes_below_100 = [8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783] := by decide+kernel
lemma PB8800 : PrimeSieve 8800 9000 primes_below_100 = [8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999] := by decide+kernel
lemma PB9000 : PrimeSieve 9000 9200 primes_below_100 = [9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199] := by decide+kernel
lemma PB9200 : PrimeSieve 9200 9400 primes_below_100 = [9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397] := by decide+kernel
lemma PB9400 : PrimeSieve 9400 9600 primes_below_100 = [9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587] := by decide+kernel
lemma PB9600 : PrimeSieve 9600 9800 primes_below_100 = [9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791] := by decide+kernel
lemma PB9800 : PrimeSieve 9800 10000 primes_below_100 = [9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973] := by decide+kernel

lemma primes_below_10000 (p : ℕ):
  p ∈ primesBelow10000.foldr (fun x y => x ++ y) [] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 10000 := by
  convert primes_below_append e_interval_aux primes_below_100 (by decide) primesBelow10000 (by decide) ?_ ?_ (by decide) ?_ p
  · rfl
  · rfl
  · rfl
  · exact primes_below_100_proof
  · intro i hi
    have : e_interval_aux.length = 51 := by decide
    have hif : i < 50 := by omega
    interval_cases i
    exact PB0 ; exact PB200 ; exact PB400 ; exact PB600 ; exact PB800 ; exact PB1000 ; exact PB1200
    exact PB1400 ; exact PB1600 ; exact PB1800 ; exact PB2000 ; exact PB2200 ; exact PB2400 ; exact PB2600
    exact PB2800 ; exact PB3000 ; exact PB3200 ; exact PB3400 ; exact PB3600 ; exact PB3800 ; exact PB4000
    exact PB4200 ; exact PB4400 ; exact PB4600 ; exact PB4800 ; exact PB5000 ; exact PB5200 ; exact PB5400
    exact PB5600 ; exact PB5800 ; exact PB6000 ; exact PB6200 ; exact PB6400 ; exact PB6600 ; exact PB6800
    exact PB7000 ; exact PB7200 ; exact PB7400 ; exact PB7600 ; exact PB7800 ; exact PB8000 ; exact PB8200
    exact PB8400 ; exact PB8600 ; exact PB8800 ; exact PB9000 ; exact PB9200 ; exact PB9400 ; exact PB9600
    exact PB9800

/-- The tree with the primes-/
def PTreeE := node 1229 (node 717 (node 461 (node 333 (node 205 (node 141 (node 77 (node 45 (node 29 (node 21 (node 13 (node 9 (node 5 (node 3 (node 1 (nil) 2 (nil) ) 3 (node 1 (nil) 5 (nil) ) ) 7 (node 1 (nil) 11 (nil) ) ) 13 (node 3 (node 1 (nil) 17 (nil) ) 19 (node 1 (nil) 23 (nil) ) ) ) 29 (node 3 (node 1 (nil) 31 (nil) ) 37 (node 1 (nil) 41 (nil) ) ) ) 43 (node 7 (node 3 (node 1 (nil) 47 (nil) ) 53 (node 1 (nil) 59 (nil) ) ) 61 (node 3 (node 1 (nil) 67 (nil) ) 71 (node 1 (nil) 73 (nil) ) ) ) ) 79 (node 7 (node 3 (node 1 (nil) 83 (nil) ) 89 (node 1 (nil) 97 (nil) ) ) 101 (node 3 (node 1 (nil) 103 (nil) ) 107 (node 1 (nil) 109 (nil) ) ) ) ) 113 (node 15 (node 7 (node 3 (node 1 (nil) 127 (nil) ) 131 (node 1 (nil) 137 (nil) ) ) 139 (node 3 (node 1 (nil) 149 (nil) ) 151 (node 1 (nil) 157 (nil) ) ) ) 163 (node 7 (node 3 (node 1 (nil) 167 (nil) ) 173 (node 1 (nil) 179 (nil) ) ) 181 (node 3 (node 1 (nil) 191 (nil) ) 193 (node 1 (nil) 197 (nil) ) ) ) ) ) 199 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 211 (nil) ) 223 (node 1 (nil) 227 (nil) ) ) 229 (node 3 (node 1 (nil) 233 (nil) ) 239 (node 1 (nil) 241 (nil) ) ) ) 251 (node 7 (node 3 (node 1 (nil) 257 (nil) ) 263 (node 1 (nil) 269 (nil) ) ) 271 (node 3 (node 1 (nil) 277 (nil) ) 281 (node 1 (nil) 283 (nil) ) ) ) ) 293 (node 15 (node 7 (node 3 (node 1 (nil) 307 (nil) ) 311 (node 1 (nil) 313 (nil) ) ) 317 (node 3 (node 1 (nil) 331 (nil) ) 337 (node 1 (nil) 347 (nil) ) ) ) 349 (node 7 (node 3 (node 1 (nil) 353 (nil) ) 359 (node 1 (nil) 367 (nil) ) ) 373 (node 3 (node 1 (nil) 379 (nil) ) 383 (node 1 (nil) 389 (nil) ) ) ) ) ) ) 397 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 401 (nil) ) 409 (node 1 (nil) 419 (nil) ) ) 421 (node 3 (node 1 (nil) 431 (nil) ) 433 (node 1 (nil) 439 (nil) ) ) ) 443 (node 7 (node 3 (node 1 (nil) 449 (nil) ) 457 (node 1 (nil) 461 (nil) ) ) 463 (node 3 (node 1 (nil) 467 (nil) ) 479 (node 1 (nil) 487 (nil) ) ) ) ) 491 (node 15 (node 7 (node 3 (node 1 (nil) 499 (nil) ) 503 (node 1 (nil) 509 (nil) ) ) 521 (node 3 (node 1 (nil) 523 (nil) ) 541 (node 1 (nil) 547 (nil) ) ) ) 557 (node 7 (node 3 (node 1 (nil) 563 (nil) ) 569 (node 1 (nil) 571 (nil) ) ) 577 (node 3 (node 1 (nil) 587 (nil) ) 593 (node 1 (nil) 599 (nil) ) ) ) ) ) 601 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 607 (nil) ) 613 (node 1 (nil) 617 (nil) ) ) 619 (node 3 (node 1 (nil) 631 (nil) ) 641 (node 1 (nil) 643 (nil) ) ) ) 647 (node 7 (node 3 (node 1 (nil) 653 (nil) ) 659 (node 1 (nil) 661 (nil) ) ) 673 (node 3 (node 1 (nil) 677 (nil) ) 683 (node 1 (nil) 691 (nil) ) ) ) ) 701 (node 15 (node 7 (node 3 (node 1 (nil) 709 (nil) ) 719 (node 1 (nil) 727 (nil) ) ) 733 (node 3 (node 1 (nil) 739 (nil) ) 743 (node 1 (nil) 751 (nil) ) ) ) 757 (node 7 (node 3 (node 1 (nil) 761 (nil) ) 769 (node 1 (nil) 773 (nil) ) ) 787 (node 3 (node 1 (nil) 797 (nil) ) 809 (node 1 (nil) 811 (nil) ) ) ) ) ) ) ) 821 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 823 (nil) ) 827 (node 1 (nil) 829 (nil) ) ) 839 (node 3 (node 1 (nil) 853 (nil) ) 857 (node 1 (nil) 859 (nil) ) ) ) 863 (node 7 (node 3 (node 1 (nil) 877 (nil) ) 881 (node 1 (nil) 883 (nil) ) ) 887 (node 3 (node 1 (nil) 907 (nil) ) 911 (node 1 (nil) 919 (nil) ) ) ) ) 929 (node 15 (node 7 (node 3 (node 1 (nil) 937 (nil) ) 941 (node 1 (nil) 947 (nil) ) ) 953 (node 3 (node 1 (nil) 967 (nil) ) 971 (node 1 (nil) 977 (nil) ) ) ) 983 (node 7 (node 3 (node 1 (nil) 991 (nil) ) 997 (node 1 (nil) 1009 (nil) ) ) 1013 (node 3 (node 1 (nil) 1019 (nil) ) 1021 (node 1 (nil) 1031 (nil) ) ) ) ) ) 1033 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 1039 (nil) ) 1049 (node 1 (nil) 1051 (nil) ) ) 1061 (node 3 (node 1 (nil) 1063 (nil) ) 1069 (node 1 (nil) 1087 (nil) ) ) ) 1091 (node 7 (node 3 (node 1 (nil) 1093 (nil) ) 1097 (node 1 (nil) 1103 (nil) ) ) 1109 (node 3 (node 1 (nil) 1117 (nil) ) 1123 (node 1 (nil) 1129 (nil) ) ) ) ) 1151 (node 15 (node 7 (node 3 (node 1 (nil) 1153 (nil) ) 1163 (node 1 (nil) 1171 (nil) ) ) 1181 (node 3 (node 1 (nil) 1187 (nil) ) 1193 (node 1 (nil) 1201 (nil) ) ) ) 1213 (node 7 (node 3 (node 1 (nil) 1217 (nil) ) 1223 (node 1 (nil) 1229 (nil) ) ) 1231 (node 3 (node 1 (nil) 1237 (nil) ) 1249 (node 1 (nil) 1259 (nil) ) ) ) ) ) ) ) 1277 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 1279 (nil) ) 1283 (node 1 (nil) 1289 (nil) ) ) 1291 (node 3 (node 1 (nil) 1297 (nil) ) 1301 (node 1 (nil) 1303 (nil) ) ) ) 1307 (node 7 (node 3 (node 1 (nil) 1319 (nil) ) 1321 (node 1 (nil) 1327 (nil) ) ) 1361 (node 3 (node 1 (nil) 1367 (nil) ) 1373 (node 1 (nil) 1381 (nil) ) ) ) ) 1399 (node 15 (node 7 (node 3 (node 1 (nil) 1409 (nil) ) 1423 (node 1 (nil) 1427 (nil) ) ) 1429 (node 3 (node 1 (nil) 1433 (nil) ) 1439 (node 1 (nil) 1447 (nil) ) ) ) 1451 (node 7 (node 3 (node 1 (nil) 1453 (nil) ) 1459 (node 1 (nil) 1471 (nil) ) ) 1481 (node 3 (node 1 (nil) 1483 (nil) ) 1487 (node 1 (nil) 1489 (nil) ) ) ) ) ) 1493 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 1499 (nil) ) 1511 (node 1 (nil) 1523 (nil) ) ) 1531 (node 3 (node 1 (nil) 1543 (nil) ) 1549 (node 1 (nil) 1553 (nil) ) ) ) 1559 (node 7 (node 3 (node 1 (nil) 1567 (nil) ) 1571 (node 1 (nil) 1579 (nil) ) ) 1583 (node 3 (node 1 (nil) 1597 (nil) ) 1601 (node 1 (nil) 1607 (nil) ) ) ) ) 1609 (node 15 (node 7 (node 3 (node 1 (nil) 1613 (nil) ) 1619 (node 1 (nil) 1621 (nil) ) ) 1627 (node 3 (node 1 (nil) 1637 (nil) ) 1657 (node 1 (nil) 1663 (nil) ) ) ) 1667 (node 7 (node 3 (node 1 (nil) 1669 (nil) ) 1693 (node 1 (nil) 1697 (nil) ) ) 1699 (node 3 (node 1 (nil) 1709 (nil) ) 1721 (node 1 (nil) 1723 (nil) ) ) ) ) ) ) 1733 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 1741 (nil) ) 1747 (node 1 (nil) 1753 (nil) ) ) 1759 (node 3 (node 1 (nil) 1777 (nil) ) 1783 (node 1 (nil) 1787 (nil) ) ) ) 1789 (node 7 (node 3 (node 1 (nil) 1801 (nil) ) 1811 (node 1 (nil) 1823 (nil) ) ) 1831 (node 3 (node 1 (nil) 1847 (nil) ) 1861 (node 1 (nil) 1867 (nil) ) ) ) ) 1871 (node 15 (node 7 (node 3 (node 1 (nil) 1873 (nil) ) 1877 (node 1 (nil) 1879 (nil) ) ) 1889 (node 3 (node 1 (nil) 1901 (nil) ) 1907 (node 1 (nil) 1913 (nil) ) ) ) 1931 (node 7 (node 3 (node 1 (nil) 1933 (nil) ) 1949 (node 1 (nil) 1951 (nil) ) ) 1973 (node 3 (node 1 (nil) 1979 (nil) ) 1987 (node 1 (nil) 1993 (nil) ) ) ) ) ) 1997 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 1999 (nil) ) 2003 (node 1 (nil) 2011 (nil) ) ) 2017 (node 3 (node 1 (nil) 2027 (nil) ) 2029 (node 1 (nil) 2039 (nil) ) ) ) 2053 (node 7 (node 3 (node 1 (nil) 2063 (nil) ) 2069 (node 1 (nil) 2081 (nil) ) ) 2083 (node 3 (node 1 (nil) 2087 (nil) ) 2089 (node 1 (nil) 2099 (nil) ) ) ) ) 2111 (node 15 (node 7 (node 3 (node 1 (nil) 2113 (nil) ) 2129 (node 1 (nil) 2131 (nil) ) ) 2137 (node 3 (node 1 (nil) 2141 (nil) ) 2143 (node 1 (nil) 2153 (nil) ) ) ) 2161 (node 7 (node 3 (node 1 (nil) 2179 (nil) ) 2203 (node 1 (nil) 2207 (nil) ) ) 2213 (node 3 (node 1 (nil) 2221 (nil) ) 2237 (node 1 (nil) 2239 (nil) ) ) ) ) ) ) ) ) 2243 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 2251 (nil) ) 2267 (node 1 (nil) 2269 (nil) ) ) 2273 (node 3 (node 1 (nil) 2281 (nil) ) 2287 (node 1 (nil) 2293 (nil) ) ) ) 2297 (node 7 (node 3 (node 1 (nil) 2309 (nil) ) 2311 (node 1 (nil) 2333 (nil) ) ) 2339 (node 3 (node 1 (nil) 2341 (nil) ) 2347 (node 1 (nil) 2351 (nil) ) ) ) ) 2357 (node 15 (node 7 (node 3 (node 1 (nil) 2371 (nil) ) 2377 (node 1 (nil) 2381 (nil) ) ) 2383 (node 3 (node 1 (nil) 2389 (nil) ) 2393 (node 1 (nil) 2399 (nil) ) ) ) 2411 (node 7 (node 3 (node 1 (nil) 2417 (nil) ) 2423 (node 1 (nil) 2437 (nil) ) ) 2441 (node 3 (node 1 (nil) 2447 (nil) ) 2459 (node 1 (nil) 2467 (nil) ) ) ) ) ) 2473 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 2477 (nil) ) 2503 (node 1 (nil) 2521 (nil) ) ) 2531 (node 3 (node 1 (nil) 2539 (nil) ) 2543 (node 1 (nil) 2549 (nil) ) ) ) 2551 (node 7 (node 3 (node 1 (nil) 2557 (nil) ) 2579 (node 1 (nil) 2591 (nil) ) ) 2593 (node 3 (node 1 (nil) 2609 (nil) ) 2617 (node 1 (nil) 2621 (nil) ) ) ) ) 2633 (node 15 (node 7 (node 3 (node 1 (nil) 2647 (nil) ) 2657 (node 1 (nil) 2659 (nil) ) ) 2663 (node 3 (node 1 (nil) 2671 (nil) ) 2677 (node 1 (nil) 2683 (nil) ) ) ) 2687 (node 7 (node 3 (node 1 (nil) 2689 (nil) ) 2693 (node 1 (nil) 2699 (nil) ) ) 2707 (node 3 (node 1 (nil) 2711 (nil) ) 2713 (node 1 (nil) 2719 (nil) ) ) ) ) ) ) 2729 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 2731 (nil) ) 2741 (node 1 (nil) 2749 (nil) ) ) 2753 (node 3 (node 1 (nil) 2767 (nil) ) 2777 (node 1 (nil) 2789 (nil) ) ) ) 2791 (node 7 (node 3 (node 1 (nil) 2797 (nil) ) 2801 (node 1 (nil) 2803 (nil) ) ) 2819 (node 3 (node 1 (nil) 2833 (nil) ) 2837 (node 1 (nil) 2843 (nil) ) ) ) ) 2851 (node 15 (node 7 (node 3 (node 1 (nil) 2857 (nil) ) 2861 (node 1 (nil) 2879 (nil) ) ) 2887 (node 3 (node 1 (nil) 2897 (nil) ) 2903 (node 1 (nil) 2909 (nil) ) ) ) 2917 (node 7 (node 3 (node 1 (nil) 2927 (nil) ) 2939 (node 1 (nil) 2953 (nil) ) ) 2957 (node 3 (node 1 (nil) 2963 (nil) ) 2969 (node 1 (nil) 2971 (nil) ) ) ) ) ) 2999 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 3001 (nil) ) 3011 (node 1 (nil) 3019 (nil) ) ) 3023 (node 3 (node 1 (nil) 3037 (nil) ) 3041 (node 1 (nil) 3049 (nil) ) ) ) 3061 (node 7 (node 3 (node 1 (nil) 3067 (nil) ) 3079 (node 1 (nil) 3083 (nil) ) ) 3089 (node 3 (node 1 (nil) 3109 (nil) ) 3119 (node 1 (nil) 3121 (nil) ) ) ) ) 3137 (node 15 (node 7 (node 3 (node 1 (nil) 3163 (nil) ) 3167 (node 1 (nil) 3169 (nil) ) ) 3181 (node 3 (node 1 (nil) 3187 (nil) ) 3191 (node 1 (nil) 3203 (nil) ) ) ) 3209 (node 7 (node 3 (node 1 (nil) 3217 (nil) ) 3221 (node 1 (nil) 3229 (nil) ) ) 3251 (node 3 (node 1 (nil) 3253 (nil) ) 3257 (node 1 (nil) 3259 (nil) ) ) ) ) ) ) ) ) 3271 (node 255 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 3299 (nil) ) 3301 (node 1 (nil) 3307 (nil) ) ) 3313 (node 3 (node 1 (nil) 3319 (nil) ) 3323 (node 1 (nil) 3329 (nil) ) ) ) 3331 (node 7 (node 3 (node 1 (nil) 3343 (nil) ) 3347 (node 1 (nil) 3359 (nil) ) ) 3361 (node 3 (node 1 (nil) 3371 (nil) ) 3373 (node 1 (nil) 3389 (nil) ) ) ) ) 3391 (node 15 (node 7 (node 3 (node 1 (nil) 3407 (nil) ) 3413 (node 1 (nil) 3433 (nil) ) ) 3449 (node 3 (node 1 (nil) 3457 (nil) ) 3461 (node 1 (nil) 3463 (nil) ) ) ) 3467 (node 7 (node 3 (node 1 (nil) 3469 (nil) ) 3491 (node 1 (nil) 3499 (nil) ) ) 3511 (node 3 (node 1 (nil) 3517 (nil) ) 3527 (node 1 (nil) 3529 (nil) ) ) ) ) ) 3533 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 3539 (nil) ) 3541 (node 1 (nil) 3547 (nil) ) ) 3557 (node 3 (node 1 (nil) 3559 (nil) ) 3571 (node 1 (nil) 3581 (nil) ) ) ) 3583 (node 7 (node 3 (node 1 (nil) 3593 (nil) ) 3607 (node 1 (nil) 3613 (nil) ) ) 3617 (node 3 (node 1 (nil) 3623 (nil) ) 3631 (node 1 (nil) 3637 (nil) ) ) ) ) 3643 (node 15 (node 7 (node 3 (node 1 (nil) 3659 (nil) ) 3671 (node 1 (nil) 3673 (nil) ) ) 3677 (node 3 (node 1 (nil) 3691 (nil) ) 3697 (node 1 (nil) 3701 (nil) ) ) ) 3709 (node 7 (node 3 (node 1 (nil) 3719 (nil) ) 3727 (node 1 (nil) 3733 (nil) ) ) 3739 (node 3 (node 1 (nil) 3761 (nil) ) 3767 (node 1 (nil) 3769 (nil) ) ) ) ) ) ) 3779 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 3793 (nil) ) 3797 (node 1 (nil) 3803 (nil) ) ) 3821 (node 3 (node 1 (nil) 3823 (nil) ) 3833 (node 1 (nil) 3847 (nil) ) ) ) 3851 (node 7 (node 3 (node 1 (nil) 3853 (nil) ) 3863 (node 1 (nil) 3877 (nil) ) ) 3881 (node 3 (node 1 (nil) 3889 (nil) ) 3907 (node 1 (nil) 3911 (nil) ) ) ) ) 3917 (node 15 (node 7 (node 3 (node 1 (nil) 3919 (nil) ) 3923 (node 1 (nil) 3929 (nil) ) ) 3931 (node 3 (node 1 (nil) 3943 (nil) ) 3947 (node 1 (nil) 3967 (nil) ) ) ) 3989 (node 7 (node 3 (node 1 (nil) 4001 (nil) ) 4003 (node 1 (nil) 4007 (nil) ) ) 4013 (node 3 (node 1 (nil) 4019 (nil) ) 4021 (node 1 (nil) 4027 (nil) ) ) ) ) ) 4049 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 4051 (nil) ) 4057 (node 1 (nil) 4073 (nil) ) ) 4079 (node 3 (node 1 (nil) 4091 (nil) ) 4093 (node 1 (nil) 4099 (nil) ) ) ) 4111 (node 7 (node 3 (node 1 (nil) 4127 (nil) ) 4129 (node 1 (nil) 4133 (nil) ) ) 4139 (node 3 (node 1 (nil) 4153 (nil) ) 4157 (node 1 (nil) 4159 (nil) ) ) ) ) 4177 (node 15 (node 7 (node 3 (node 1 (nil) 4201 (nil) ) 4211 (node 1 (nil) 4217 (nil) ) ) 4219 (node 3 (node 1 (nil) 4229 (nil) ) 4231 (node 1 (nil) 4241 (nil) ) ) ) 4243 (node 7 (node 3 (node 1 (nil) 4253 (nil) ) 4259 (node 1 (nil) 4261 (nil) ) ) 4271 (node 3 (node 1 (nil) 4273 (nil) ) 4283 (node 1 (nil) 4289 (nil) ) ) ) ) ) ) ) 4297 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 4327 (nil) ) 4337 (node 1 (nil) 4339 (nil) ) ) 4349 (node 3 (node 1 (nil) 4357 (nil) ) 4363 (node 1 (nil) 4373 (nil) ) ) ) 4391 (node 7 (node 3 (node 1 (nil) 4397 (nil) ) 4409 (node 1 (nil) 4421 (nil) ) ) 4423 (node 3 (node 1 (nil) 4441 (nil) ) 4447 (node 1 (nil) 4451 (nil) ) ) ) ) 4457 (node 15 (node 7 (node 3 (node 1 (nil) 4463 (nil) ) 4481 (node 1 (nil) 4483 (nil) ) ) 4493 (node 3 (node 1 (nil) 4507 (nil) ) 4513 (node 1 (nil) 4517 (nil) ) ) ) 4519 (node 7 (node 3 (node 1 (nil) 4523 (nil) ) 4547 (node 1 (nil) 4549 (nil) ) ) 4561 (node 3 (node 1 (nil) 4567 (nil) ) 4583 (node 1 (nil) 4591 (nil) ) ) ) ) ) 4597 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 4603 (nil) ) 4621 (node 1 (nil) 4637 (nil) ) ) 4639 (node 3 (node 1 (nil) 4643 (nil) ) 4649 (node 1 (nil) 4651 (nil) ) ) ) 4657 (node 7 (node 3 (node 1 (nil) 4663 (nil) ) 4673 (node 1 (nil) 4679 (nil) ) ) 4691 (node 3 (node 1 (nil) 4703 (nil) ) 4721 (node 1 (nil) 4723 (nil) ) ) ) ) 4729 (node 15 (node 7 (node 3 (node 1 (nil) 4733 (nil) ) 4751 (node 1 (nil) 4759 (nil) ) ) 4783 (node 3 (node 1 (nil) 4787 (nil) ) 4789 (node 1 (nil) 4793 (nil) ) ) ) 4799 (node 7 (node 3 (node 1 (nil) 4801 (nil) ) 4813 (node 1 (nil) 4817 (nil) ) ) 4831 (node 3 (node 1 (nil) 4861 (nil) ) 4871 (node 1 (nil) 4877 (nil) ) ) ) ) ) ) 4889 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 4903 (nil) ) 4909 (node 1 (nil) 4919 (nil) ) ) 4931 (node 3 (node 1 (nil) 4933 (nil) ) 4937 (node 1 (nil) 4943 (nil) ) ) ) 4951 (node 7 (node 3 (node 1 (nil) 4957 (nil) ) 4967 (node 1 (nil) 4969 (nil) ) ) 4973 (node 3 (node 1 (nil) 4987 (nil) ) 4993 (node 1 (nil) 4999 (nil) ) ) ) ) 5003 (node 15 (node 7 (node 3 (node 1 (nil) 5009 (nil) ) 5011 (node 1 (nil) 5021 (nil) ) ) 5023 (node 3 (node 1 (nil) 5039 (nil) ) 5051 (node 1 (nil) 5059 (nil) ) ) ) 5077 (node 7 (node 3 (node 1 (nil) 5081 (nil) ) 5087 (node 1 (nil) 5099 (nil) ) ) 5101 (node 3 (node 1 (nil) 5107 (nil) ) 5113 (node 1 (nil) 5119 (nil) ) ) ) ) ) 5147 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 5153 (nil) ) 5167 (node 1 (nil) 5171 (nil) ) ) 5179 (node 3 (node 1 (nil) 5189 (nil) ) 5197 (node 1 (nil) 5209 (nil) ) ) ) 5227 (node 7 (node 3 (node 1 (nil) 5231 (nil) ) 5233 (node 1 (nil) 5237 (nil) ) ) 5261 (node 3 (node 1 (nil) 5273 (nil) ) 5279 (node 1 (nil) 5281 (nil) ) ) ) ) 5297 (node 15 (node 7 (node 3 (node 1 (nil) 5303 (nil) ) 5309 (node 1 (nil) 5323 (nil) ) ) 5333 (node 3 (node 1 (nil) 5347 (nil) ) 5351 (node 1 (nil) 5381 (nil) ) ) ) 5387 (node 7 (node 3 (node 1 (nil) 5393 (nil) ) 5399 (node 1 (nil) 5407 (nil) ) ) 5413 (node 3 (node 1 (nil) 5417 (nil) ) 5419 (node 1 (nil) 5431 (nil) ) ) ) ) ) ) ) ) ) 5437 (node 511 (node 255 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 5441 (nil) ) 5443 (node 1 (nil) 5449 (nil) ) ) 5471 (node 3 (node 1 (nil) 5477 (nil) ) 5479 (node 1 (nil) 5483 (nil) ) ) ) 5501 (node 7 (node 3 (node 1 (nil) 5503 (nil) ) 5507 (node 1 (nil) 5519 (nil) ) ) 5521 (node 3 (node 1 (nil) 5527 (nil) ) 5531 (node 1 (nil) 5557 (nil) ) ) ) ) 5563 (node 15 (node 7 (node 3 (node 1 (nil) 5569 (nil) ) 5573 (node 1 (nil) 5581 (nil) ) ) 5591 (node 3 (node 1 (nil) 5623 (nil) ) 5639 (node 1 (nil) 5641 (nil) ) ) ) 5647 (node 7 (node 3 (node 1 (nil) 5651 (nil) ) 5653 (node 1 (nil) 5657 (nil) ) ) 5659 (node 3 (node 1 (nil) 5669 (nil) ) 5683 (node 1 (nil) 5689 (nil) ) ) ) ) ) 5693 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 5701 (nil) ) 5711 (node 1 (nil) 5717 (nil) ) ) 5737 (node 3 (node 1 (nil) 5741 (nil) ) 5743 (node 1 (nil) 5749 (nil) ) ) ) 5779 (node 7 (node 3 (node 1 (nil) 5783 (nil) ) 5791 (node 1 (nil) 5801 (nil) ) ) 5807 (node 3 (node 1 (nil) 5813 (nil) ) 5821 (node 1 (nil) 5827 (nil) ) ) ) ) 5839 (node 15 (node 7 (node 3 (node 1 (nil) 5843 (nil) ) 5849 (node 1 (nil) 5851 (nil) ) ) 5857 (node 3 (node 1 (nil) 5861 (nil) ) 5867 (node 1 (nil) 5869 (nil) ) ) ) 5879 (node 7 (node 3 (node 1 (nil) 5881 (nil) ) 5897 (node 1 (nil) 5903 (nil) ) ) 5923 (node 3 (node 1 (nil) 5927 (nil) ) 5939 (node 1 (nil) 5953 (nil) ) ) ) ) ) ) 5981 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 5987 (nil) ) 6007 (node 1 (nil) 6011 (nil) ) ) 6029 (node 3 (node 1 (nil) 6037 (nil) ) 6043 (node 1 (nil) 6047 (nil) ) ) ) 6053 (node 7 (node 3 (node 1 (nil) 6067 (nil) ) 6073 (node 1 (nil) 6079 (nil) ) ) 6089 (node 3 (node 1 (nil) 6091 (nil) ) 6101 (node 1 (nil) 6113 (nil) ) ) ) ) 6121 (node 15 (node 7 (node 3 (node 1 (nil) 6131 (nil) ) 6133 (node 1 (nil) 6143 (nil) ) ) 6151 (node 3 (node 1 (nil) 6163 (nil) ) 6173 (node 1 (nil) 6197 (nil) ) ) ) 6199 (node 7 (node 3 (node 1 (nil) 6203 (nil) ) 6211 (node 1 (nil) 6217 (nil) ) ) 6221 (node 3 (node 1 (nil) 6229 (nil) ) 6247 (node 1 (nil) 6257 (nil) ) ) ) ) ) 6263 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 6269 (nil) ) 6271 (node 1 (nil) 6277 (nil) ) ) 6287 (node 3 (node 1 (nil) 6299 (nil) ) 6301 (node 1 (nil) 6311 (nil) ) ) ) 6317 (node 7 (node 3 (node 1 (nil) 6323 (nil) ) 6329 (node 1 (nil) 6337 (nil) ) ) 6343 (node 3 (node 1 (nil) 6353 (nil) ) 6359 (node 1 (nil) 6361 (nil) ) ) ) ) 6367 (node 15 (node 7 (node 3 (node 1 (nil) 6373 (nil) ) 6379 (node 1 (nil) 6389 (nil) ) ) 6397 (node 3 (node 1 (nil) 6421 (nil) ) 6427 (node 1 (nil) 6449 (nil) ) ) ) 6451 (node 7 (node 3 (node 1 (nil) 6469 (nil) ) 6473 (node 1 (nil) 6481 (nil) ) ) 6491 (node 3 (node 1 (nil) 6521 (nil) ) 6529 (node 1 (nil) 6547 (nil) ) ) ) ) ) ) ) 6551 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 6553 (nil) ) 6563 (node 1 (nil) 6569 (nil) ) ) 6571 (node 3 (node 1 (nil) 6577 (nil) ) 6581 (node 1 (nil) 6599 (nil) ) ) ) 6607 (node 7 (node 3 (node 1 (nil) 6619 (nil) ) 6637 (node 1 (nil) 6653 (nil) ) ) 6659 (node 3 (node 1 (nil) 6661 (nil) ) 6673 (node 1 (nil) 6679 (nil) ) ) ) ) 6689 (node 15 (node 7 (node 3 (node 1 (nil) 6691 (nil) ) 6701 (node 1 (nil) 6703 (nil) ) ) 6709 (node 3 (node 1 (nil) 6719 (nil) ) 6733 (node 1 (nil) 6737 (nil) ) ) ) 6761 (node 7 (node 3 (node 1 (nil) 6763 (nil) ) 6779 (node 1 (nil) 6781 (nil) ) ) 6791 (node 3 (node 1 (nil) 6793 (nil) ) 6803 (node 1 (nil) 6823 (nil) ) ) ) ) ) 6827 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 6829 (nil) ) 6833 (node 1 (nil) 6841 (nil) ) ) 6857 (node 3 (node 1 (nil) 6863 (nil) ) 6869 (node 1 (nil) 6871 (nil) ) ) ) 6883 (node 7 (node 3 (node 1 (nil) 6899 (nil) ) 6907 (node 1 (nil) 6911 (nil) ) ) 6917 (node 3 (node 1 (nil) 6947 (nil) ) 6949 (node 1 (nil) 6959 (nil) ) ) ) ) 6961 (node 15 (node 7 (node 3 (node 1 (nil) 6967 (nil) ) 6971 (node 1 (nil) 6977 (nil) ) ) 6983 (node 3 (node 1 (nil) 6991 (nil) ) 6997 (node 1 (nil) 7001 (nil) ) ) ) 7013 (node 7 (node 3 (node 1 (nil) 7019 (nil) ) 7027 (node 1 (nil) 7039 (nil) ) ) 7043 (node 3 (node 1 (nil) 7057 (nil) ) 7069 (node 1 (nil) 7079 (nil) ) ) ) ) ) ) 7103 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 7109 (nil) ) 7121 (node 1 (nil) 7127 (nil) ) ) 7129 (node 3 (node 1 (nil) 7151 (nil) ) 7159 (node 1 (nil) 7177 (nil) ) ) ) 7187 (node 7 (node 3 (node 1 (nil) 7193 (nil) ) 7207 (node 1 (nil) 7211 (nil) ) ) 7213 (node 3 (node 1 (nil) 7219 (nil) ) 7229 (node 1 (nil) 7237 (nil) ) ) ) ) 7243 (node 15 (node 7 (node 3 (node 1 (nil) 7247 (nil) ) 7253 (node 1 (nil) 7283 (nil) ) ) 7297 (node 3 (node 1 (nil) 7307 (nil) ) 7309 (node 1 (nil) 7321 (nil) ) ) ) 7331 (node 7 (node 3 (node 1 (nil) 7333 (nil) ) 7349 (node 1 (nil) 7351 (nil) ) ) 7369 (node 3 (node 1 (nil) 7393 (nil) ) 7411 (node 1 (nil) 7417 (nil) ) ) ) ) ) 7433 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 7451 (nil) ) 7457 (node 1 (nil) 7459 (nil) ) ) 7477 (node 3 (node 1 (nil) 7481 (nil) ) 7487 (node 1 (nil) 7489 (nil) ) ) ) 7499 (node 7 (node 3 (node 1 (nil) 7507 (nil) ) 7517 (node 1 (nil) 7523 (nil) ) ) 7529 (node 3 (node 1 (nil) 7537 (nil) ) 7541 (node 1 (nil) 7547 (nil) ) ) ) ) 7549 (node 15 (node 7 (node 3 (node 1 (nil) 7559 (nil) ) 7561 (node 1 (nil) 7573 (nil) ) ) 7577 (node 3 (node 1 (nil) 7583 (nil) ) 7589 (node 1 (nil) 7591 (nil) ) ) ) 7603 (node 7 (node 3 (node 1 (nil) 7607 (nil) ) 7621 (node 1 (nil) 7639 (nil) ) ) 7643 (node 3 (node 1 (nil) 7649 (nil) ) 7669 (node 1 (nil) 7673 (nil) ) ) ) ) ) ) ) ) 7681 (node 255 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 7687 (nil) ) 7691 (node 1 (nil) 7699 (nil) ) ) 7703 (node 3 (node 1 (nil) 7717 (nil) ) 7723 (node 1 (nil) 7727 (nil) ) ) ) 7741 (node 7 (node 3 (node 1 (nil) 7753 (nil) ) 7757 (node 1 (nil) 7759 (nil) ) ) 7789 (node 3 (node 1 (nil) 7793 (nil) ) 7817 (node 1 (nil) 7823 (nil) ) ) ) ) 7829 (node 15 (node 7 (node 3 (node 1 (nil) 7841 (nil) ) 7853 (node 1 (nil) 7867 (nil) ) ) 7873 (node 3 (node 1 (nil) 7877 (nil) ) 7879 (node 1 (nil) 7883 (nil) ) ) ) 7901 (node 7 (node 3 (node 1 (nil) 7907 (nil) ) 7919 (node 1 (nil) 7927 (nil) ) ) 7933 (node 3 (node 1 (nil) 7937 (nil) ) 7949 (node 1 (nil) 7951 (nil) ) ) ) ) ) 7963 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 7993 (nil) ) 8009 (node 1 (nil) 8011 (nil) ) ) 8017 (node 3 (node 1 (nil) 8039 (nil) ) 8053 (node 1 (nil) 8059 (nil) ) ) ) 8069 (node 7 (node 3 (node 1 (nil) 8081 (nil) ) 8087 (node 1 (nil) 8089 (nil) ) ) 8093 (node 3 (node 1 (nil) 8101 (nil) ) 8111 (node 1 (nil) 8117 (nil) ) ) ) ) 8123 (node 15 (node 7 (node 3 (node 1 (nil) 8147 (nil) ) 8161 (node 1 (nil) 8167 (nil) ) ) 8171 (node 3 (node 1 (nil) 8179 (nil) ) 8191 (node 1 (nil) 8209 (nil) ) ) ) 8219 (node 7 (node 3 (node 1 (nil) 8221 (nil) ) 8231 (node 1 (nil) 8233 (nil) ) ) 8237 (node 3 (node 1 (nil) 8243 (nil) ) 8263 (node 1 (nil) 8269 (nil) ) ) ) ) ) ) 8273 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 8287 (nil) ) 8291 (node 1 (nil) 8293 (nil) ) ) 8297 (node 3 (node 1 (nil) 8311 (nil) ) 8317 (node 1 (nil) 8329 (nil) ) ) ) 8353 (node 7 (node 3 (node 1 (nil) 8363 (nil) ) 8369 (node 1 (nil) 8377 (nil) ) ) 8387 (node 3 (node 1 (nil) 8389 (nil) ) 8419 (node 1 (nil) 8423 (nil) ) ) ) ) 8429 (node 15 (node 7 (node 3 (node 1 (nil) 8431 (nil) ) 8443 (node 1 (nil) 8447 (nil) ) ) 8461 (node 3 (node 1 (nil) 8467 (nil) ) 8501 (node 1 (nil) 8513 (nil) ) ) ) 8521 (node 7 (node 3 (node 1 (nil) 8527 (nil) ) 8537 (node 1 (nil) 8539 (nil) ) ) 8543 (node 3 (node 1 (nil) 8563 (nil) ) 8573 (node 1 (nil) 8581 (nil) ) ) ) ) ) 8597 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 8599 (nil) ) 8609 (node 1 (nil) 8623 (nil) ) ) 8627 (node 3 (node 1 (nil) 8629 (nil) ) 8641 (node 1 (nil) 8647 (nil) ) ) ) 8663 (node 7 (node 3 (node 1 (nil) 8669 (nil) ) 8677 (node 1 (nil) 8681 (nil) ) ) 8689 (node 3 (node 1 (nil) 8693 (nil) ) 8699 (node 1 (nil) 8707 (nil) ) ) ) ) 8713 (node 15 (node 7 (node 3 (node 1 (nil) 8719 (nil) ) 8731 (node 1 (nil) 8737 (nil) ) ) 8741 (node 3 (node 1 (nil) 8747 (nil) ) 8753 (node 1 (nil) 8761 (nil) ) ) ) 8779 (node 7 (node 3 (node 1 (nil) 8783 (nil) ) 8803 (node 1 (nil) 8807 (nil) ) ) 8819 (node 3 (node 1 (nil) 8821 (nil) ) 8831 (node 1 (nil) 8837 (nil) ) ) ) ) ) ) ) 8839 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 8849 (nil) ) 8861 (node 1 (nil) 8863 (nil) ) ) 8867 (node 3 (node 1 (nil) 8887 (nil) ) 8893 (node 1 (nil) 8923 (nil) ) ) ) 8929 (node 7 (node 3 (node 1 (nil) 8933 (nil) ) 8941 (node 1 (nil) 8951 (nil) ) ) 8963 (node 3 (node 1 (nil) 8969 (nil) ) 8971 (node 1 (nil) 8999 (nil) ) ) ) ) 9001 (node 15 (node 7 (node 3 (node 1 (nil) 9007 (nil) ) 9011 (node 1 (nil) 9013 (nil) ) ) 9029 (node 3 (node 1 (nil) 9041 (nil) ) 9043 (node 1 (nil) 9049 (nil) ) ) ) 9059 (node 7 (node 3 (node 1 (nil) 9067 (nil) ) 9091 (node 1 (nil) 9103 (nil) ) ) 9109 (node 3 (node 1 (nil) 9127 (nil) ) 9133 (node 1 (nil) 9137 (nil) ) ) ) ) ) 9151 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 9157 (nil) ) 9161 (node 1 (nil) 9173 (nil) ) ) 9181 (node 3 (node 1 (nil) 9187 (nil) ) 9199 (node 1 (nil) 9203 (nil) ) ) ) 9209 (node 7 (node 3 (node 1 (nil) 9221 (nil) ) 9227 (node 1 (nil) 9239 (nil) ) ) 9241 (node 3 (node 1 (nil) 9257 (nil) ) 9277 (node 1 (nil) 9281 (nil) ) ) ) ) 9283 (node 15 (node 7 (node 3 (node 1 (nil) 9293 (nil) ) 9311 (node 1 (nil) 9319 (nil) ) ) 9323 (node 3 (node 1 (nil) 9337 (nil) ) 9341 (node 1 (nil) 9343 (nil) ) ) ) 9349 (node 7 (node 3 (node 1 (nil) 9371 (nil) ) 9377 (node 1 (nil) 9391 (nil) ) ) 9397 (node 3 (node 1 (nil) 9403 (nil) ) 9413 (node 1 (nil) 9419 (nil) ) ) ) ) ) ) 9421 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 9431 (nil) ) 9433 (node 1 (nil) 9437 (nil) ) ) 9439 (node 3 (node 1 (nil) 9461 (nil) ) 9463 (node 1 (nil) 9467 (nil) ) ) ) 9473 (node 7 (node 3 (node 1 (nil) 9479 (nil) ) 9491 (node 1 (nil) 9497 (nil) ) ) 9511 (node 3 (node 1 (nil) 9521 (nil) ) 9533 (node 1 (nil) 9539 (nil) ) ) ) ) 9547 (node 15 (node 7 (node 3 (node 1 (nil) 9551 (nil) ) 9587 (node 1 (nil) 9601 (nil) ) ) 9613 (node 3 (node 1 (nil) 9619 (nil) ) 9623 (node 1 (nil) 9629 (nil) ) ) ) 9631 (node 7 (node 3 (node 1 (nil) 9643 (nil) ) 9649 (node 1 (nil) 9661 (nil) ) ) 9677 (node 3 (node 1 (nil) 9679 (nil) ) 9689 (node 1 (nil) 9697 (nil) ) ) ) ) ) 9719 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 9721 (nil) ) 9733 (node 1 (nil) 9739 (nil) ) ) 9743 (node 3 (node 1 (nil) 9749 (nil) ) 9767 (node 1 (nil) 9769 (nil) ) ) ) 9781 (node 7 (node 3 (node 1 (nil) 9787 (nil) ) 9791 (node 1 (nil) 9803 (nil) ) ) 9811 (node 3 (node 1 (nil) 9817 (nil) ) 9829 (node 1 (nil) 9833 (nil) ) ) ) ) 9839 (node 15 (node 7 (node 3 (node 1 (nil) 9851 (nil) ) 9857 (node 1 (nil) 9859 (nil) ) ) 9871 (node 3 (node 1 (nil) 9883 (nil) ) 9887 (node 1 (nil) 9901 (nil) ) ) ) 9907 (node 7 (node 3 (node 1 (nil) 9923 (nil) ) 9929 (node 1 (nil) 9931 (nil) ) ) 9941 (node 3 (node 1 (nil) 9949 (nil) ) 9967 (node 1 (nil) 9973 (nil) ) ) ) ) ) ) ) ) )

set_option maxRecDepth 10000
lemma PTree_ofList : ofList (primesBelow10000.foldr (fun x y => x ++ y) []) = PTreeE := by rfl
lemma PTree_toList : PTreeE.toList = (primesBelow10000.foldr (fun x y => x ++ y) []) := by rfl

lemma PTree_bounded : PTreeE.Bounded ⊥ ⊤ := by
  rw [← PTree_ofList]
  exact Ordnode.ofList_bounded _

lemma primes_range (l₁ l₂ : ℕ) (hle : l₂ ≤ 10000) {p : ℕ} :
  p ∈ (Ordnode.extractRangeTree PTreeE (l₁ + 1) l₂).toList  ↔ Nat.Prime p ∧ l₁ < p ∧ p ≤ l₂ := by
  rw [Ordnode.extractRangeTree_toList_mem PTree_bounded,
    PTree_toList, primes_below_10000]
  apply Iff.intro
  · rintro ⟨⟨left, ⟨left_2, right_1⟩⟩, ⟨left_1, right⟩⟩
    simp_all only [and_true, true_and]
    exact left_1
  · rintro ⟨left, ⟨left_1, right⟩⟩
    simp_all only [true_and, and_true]
    exact ⟨⟨Nat.Prime.one_lt left, by omega⟩,  left_1 ⟩

example {p} :
  p ∈ [3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637,
    3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797,
    3803]  ↔ Nat.Prime p ∧ 3506 < p ∧ p ≤ 3804 := by
  convert primes_range 3506 3804 (by omega)
  rfl
