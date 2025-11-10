/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Normed.Field.Lemmas

def toRat (p : ℕ × ℕ) : ℚ := p.1 / p.2

section binarySplit

open Finset

variable (p q a b : ℕ → ℕ)

def binarySplit (m n : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  if m < n then
    if m + 1 = n then
      (a m, b m, p m, q m)
    else
      let k := (m + n) / 2
      let (psl, qsl, ptl, qtl) := binarySplit m k
      let (psr, qsr, ptr, qtr) := binarySplit k n
      (psl * qtl * qsr + ptl * qsl * psr, qsl * qtl * qsr, ptl * ptr, qtl * qtr)
  else
    (0, 1, 1, 1)

def binarySplitSum (n : ℕ) : ℕ × ℕ :=
  ((binarySplit p q a b 0 n).1, (binarySplit p q a b 0 n).2.1)

variable {p q a b}

lemma binarySplit_nonzero {m n : ℕ} (hb : ∀ i, b i ≠ 0) (hq : ∀ i, q i ≠ 0) :
    (binarySplit p q a b m n).2.1 ≠ 0 ∧ (binarySplit p q a b m n).2.2.2 ≠ 0 := by
  fun_induction binarySplit with simp_all

lemma binarySplit_pt {m n : ℕ} :
    (binarySplit p q a b m n).2.2.1 = ∏ j ∈ Ico m n, p j := by
  fun_induction binarySplit with
  | case1 | case3 => simp_all
  | @case2 m n hmn hmn' k psl qsl ptl qtl hl psr qsr ptr qtr hr ih1 ih2 =>
    simp only [hl] at ih1
    simp only [hr] at ih2
    simp only [ih1, ih2]
    rw [prod_Ico_consecutive _ (by grind) (by grind)]

lemma binarySplit_qt {m n : ℕ} :
    (binarySplit p q a b m n).2.2.2 = ∏ j ∈ Ico m n, q j := by
  fun_induction binarySplit with
  | case1 | case3 => simp_all
  | @case2 m n hmn hmn' k psl qsl ptl qtl hl psr qsr ptr qtr hr ih1 ih2 =>
    simp only [hl] at ih1
    simp only [hr] at ih2
    simp only [ih1, ih2]
    rw [prod_Ico_consecutive _ (by grind) (by grind)]

lemma binarySplit_spec {m n ps qs pt qt : ℕ} (hb : ∀ i, b i ≠ 0) (hq : ∀ i, q i ≠ 0)
    (h : (ps, qs, pt, qt) = binarySplit p q a b m n) :
    (∏ j ∈ Ico m n, (p j / q j : ℚ) = pt / qt) ∧
    (∑ i ∈ Ico m n, (a i / b i : ℚ) * (∏ j ∈ Ico m i, p j / q j : ℚ) = ps / qs) := by
  fun_induction binarySplit generalizing ps qs pt qt with
  | case1 => simp_all
  | case3 => simp_all
  | @case2 m n hmn hmn' k psl qsl ptl qtl hl psr qsr ptr qtr hr ih1 ih2 =>
    specialize ih1 hl.symm
    specialize ih2 hr.symm
    have hmk : m ≤ k := by grind
    have hkn : k ≤ n := by grind
    cases h
    constructor
    · rw [← prod_Ico_consecutive _ hmk hkn, ih1.1, ih2.1, Nat.cast_mul, Nat.cast_mul,
        div_mul_div_comm]
    · calc
        _ = psl / qsl + ∑ i ∈ Ico k n, a i / b i * (∏ j ∈ Ico m i, p j / q j : ℚ) := by
          rw [← sum_Ico_consecutive _ hmk hkn, ih1.2]
        _ = psl / qsl + ptl / qtl * ∑ i ∈ Ico k n, a i / b i * (∏ j ∈ Ico k i, p j / q j : ℚ) := by
          simp_rw [mul_sum, mul_left_comm ((ptl : ℚ) / _)]
          congr! 3 with i hi
          simp only [Finset.mem_Ico] at hi
          rw [← prod_Ico_consecutive _ hmk hi.1, ih1.1]
        _ = _ := by
          obtain ⟨hqsl, hqtl⟩ := binarySplit_nonzero (p := p) (a := a) (m := m) (n := k) hb hq
          simp only [hl] at hqsl hqtl
          obtain ⟨hqsr, hqtr⟩ := binarySplit_nonzero (p := p) (a := a) (m := k) (n := n) hb hq
          simp only [hr] at hqsr hqtr
          rw [ih2.2]
          simp [field]

lemma binarySplitSum_spec {n : ℕ} (hb : ∀ i, b i ≠ 0) (hq : ∀ i, q i ≠ 0) :
    toRat (binarySplitSum p q a b n) =
      ∑ i ∈ range n, (a i / b i : ℚ) * (∏ j ∈ range i, p j / q j : ℚ) := by
  rw [binarySplitSum]
  match hmn : binarySplit p q a b 0 n with
  | ⟨pt, qt, ps, qs⟩ => rw [toRat, ← (binarySplit_spec hb hq hmn.symm).2, range_eq_Ico]

end binarySplit
