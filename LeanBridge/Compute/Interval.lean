/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Real.StarOrdered

section interval
open Set

lemma add_interval {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    x + y ∈ Icc (a + c) (b + d) := by
  grind

lemma sub_interval {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    x - y ∈ Icc (a - d) (b - c) := by
  grind

lemma mul_interval {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (ha : 0 < a) (hc : 0 < c) : x * y ∈ Icc (a * c) (b * d) := by
  simp only [mem_Icc] at hx hy ⊢
  constructor <;> nlinarith

lemma mul_interval_of_neg_pos {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (ha : b < 0) (hc : 0 < c) : x * y ∈ Icc (a * d) (b * c) := by
  simp only [mem_Icc] at hx hy ⊢;
  constructor <;> nlinarith

lemma mul_interval_of_pos_neg {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (ha : 0 < a) (hc : d < 0) : x * y ∈ Icc (b * c) (a * d) := by
  simp only [mem_Icc] at hx hy ⊢;
  constructor <;> nlinarith

lemma mul_interval_of_neg {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (hb : b < 0) (hc : d < 0) : x * y ∈ Icc (b * d) (a * c) := by
  simp only [mem_Icc] at hx hy ⊢;
  constructor <;> nlinarith

lemma const_interval {x : ℝ} : x ∈ Icc x x := by simp

lemma neg_interval {x a b : ℝ} (hx : x ∈ Icc a b) : -x ∈ Icc (-b) (-a) := by
  rwa [← neg_Icc, neg_mem_neg]

lemma interval_end {x a b c d : ℝ} (hx : x ∈ Icc a b) (hca : c ≤ a) (hbd : b ≤ d) : x ∈ Icc c d :=
  Icc_subset_Icc hca hbd hx

end interval
