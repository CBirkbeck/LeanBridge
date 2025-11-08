/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import LeanBridge.Compute.Interval
import Mathlib

/-!
# Estimates on natural log of rationals close to 1
-/

open Filter
open Topology BigOperators
open Finset hiding Icc Ioo
open Set

def toRat (p : ℕ × ℕ) : ℚ := p.1 / p.2

@[simp] lemma Nat.div_eq' {a b : ℕ} : a.div b = a / b := by rfl

namespace Real

section taylor

set_option linter.unusedSimpArgs false in
lemma artanh_partial_series_bound_aux' {y : ℝ} (n : ℕ) (hy₁ : -1 < y) (hy₂ : y < 1) :
    HasDerivAt
      (fun x ↦ 1 / 2 * log ((1 + x) / (1 - x)) - (∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1)))
      ((y ^ 2) ^ n / (1 - y ^ 2)) y := by
  refine ((((((hasDerivAt_id _).const_add _).div ((hasDerivAt_id _).const_sub _) (by grind)).log
          ?_).const_mul _).sub (HasDerivAt.fun_sum fun i hi ↦ (hasDerivAt_pow _ _).div_const _))
        |>.congr_deriv ?_
  · simp only [id_eq, div_ne_zero_iff, Pi.div_apply]; grind
  have : (∑ i ∈ range n, (2*i+1) * y ^ (2*i) / (2*i+1)) = (∑ i ∈ range n, (y^2) ^ i) := by
    congr with i
    simp [field, mul_comm, ← pow_mul]
  have hy₃ : y ^ 2 ≠ 1 := by simp [hy₁.ne', hy₂.ne]
  have hy₄ : (1 - y) * (1 + y) = 1 - y ^ 2 := by ring
  simp [this, field, geom_sum_eq hy₃, hy₄, sub_ne_zero_of_ne, hy₃.symm]
  ring

lemma artanh_partial_series_symmetric_bound {x : ℝ} (h : |x| < 1) (n : ℕ) :
    |∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1) - 1 / 2 * log ((1 + x) / (1 - x))| ≤
      |x| ^ (2 * n + 1) / (1 - x ^ 2) := by
  let F (x : ℝ) : ℝ :=
    1 / 2 * log ((1 + x) / (1 - x)) - (∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1))
  let F' (y : ℝ) : ℝ := (y ^ 2) ^ n / (1 - y ^ 2)
  have hI : Icc (-|x|) |x| ⊆ Ioo (-1 : ℝ) 1 := Icc_subset_Ioo (by simp [h]) h
  have A : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt F (F' y) y := by
    intro y hy
    exact artanh_partial_series_bound_aux' _ (by grind) (by grind)
  have B : ∀ y ∈ Set.Icc (-|x|) |x|, ‖F' y‖ ≤ |x| ^ (2 * n) / (1 - x ^ 2) := fun y hy ↦ by
    have : y ^ 2 ≤ x ^ 2 := sq_le_sq.2 (abs_le.2 hy)
    calc
    ‖F' y‖ = (y ^ 2) ^ n / |1 - y ^ 2| := by simp [F']
    _ = (y ^ 2) ^ n / (1 - y ^ 2) := by rw [abs_of_pos (by simpa [abs_lt] using hI hy)]
    _ ≤ (x ^ 2) ^ n / (1 - x ^ 2) := by gcongr ?_ ^ n / (1 - ?_); simpa [abs_lt] using h
    _ ≤ |x| ^ (2 * n) / (1 - x ^ 2) := by simp [pow_mul]
  have C : ‖F x - F 0‖ ≤ |x| ^ (2 * n) / (1 - x^2) * ‖x - 0‖ :=
    (convex_Icc (-|x|) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy ↦ (A _ (hI hy)).hasDerivWithinAt) B
      (by simp) (by simp [le_abs_self, neg_le, neg_le_abs x])
  simpa [F, abs_sub_comm, pow_succ, div_mul_eq_mul_div] using C

lemma artanh_partial_series_lower_bound {x : ℝ} (h₀ : 0 ≤ x) (h : x < 1) (n : ℕ) :
    ∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1) ≤ 1 / 2 * log ((1 + x) / (1 - x)) := by
  let F (x : ℝ) : ℝ :=
    1 / 2 * log ((1 + x) / (1 - x)) - (∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1))
  let F' (y : ℝ) : ℝ := (y ^ 2) ^ n / (1 - y ^ 2)
  have A : ∀ y ∈ Icc 0 x, HasDerivAt F (F' y) y := by
    intro y hy
    exact artanh_partial_series_bound_aux' _ (by grind) (by grind)
  suffices 0 ≤ F x by linear_combination this
  suffices MonotoneOn F (Icc 0 x) by simpa [F] using this ⟨le_rfl, h₀⟩ ⟨h₀, le_rfl⟩ h₀
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
    (fun y hy ↦ (A y hy).continuousAt.continuousWithinAt)
    (fun y hy ↦ (A y (interior_subset hy)).hasDerivWithinAt) ?_
  intro y hy
  simp only [interior_Icc, Set.mem_Ioo] at hy
  simp only [F']
  have : 0 ≤ 1 - y ^ 2 := by calc
    0 ≤ 1 - x ^ 2 := by simp [abs_of_nonneg h₀, h.le]
    _ ≤ 1 - y ^ 2 := sub_le_sub_left (pow_le_pow_left₀ hy.1.le hy.2.le 2) 1
  positivity

lemma log_bounds
    (n k d : ℕ) (q : ℝ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hd : d = 2 * k * (k + 1) * ((2 * k + 1) ^ (2 * n - 1)))
    (hq : q = ∑ i ∈ Finset.range n, (((2 * k + 1 : ℝ) ^ 2)⁻¹) ^ i / (2 * i + 1)) :
    log ((k + 1) / k) ∈ Set.Icc
      (2 / (2 * k + 1) * q : ℝ)
      (2 / (2 * k + 1) * q + (d : ℝ)⁻¹) := by
  let x₀ := (2 * k + 1 : ℝ)⁻¹
  have hx₀ : 0 ≤ x₀ := by positivity
  have hx₁ : x₀ < 1 := inv_lt_one_of_one_lt₀ (by simpa using hk.bot_lt)
  let t₀ := ∑ i ∈ range n, x₀ ^ (2 * i + 1) / (2 * i + 1)
  set t₁ := log ((1 + x₀) / (1 - x₀)) with ht₁
  let e := |x₀| ^ (2 * n + 1) / (1 - x₀ ^ 2)
  have ht₀ : 2 / (2 * k + 1) * q = 2 * t₀ := by calc
    _ = 2 * ∑ i ∈ Finset.range n, ((2 * k + 1 : ℝ) ^ 2)⁻¹ ^ i / ((2 * k + 1) * (2 * i + 1)) := by
      simp [hq, mul_sum, div_mul_div_comm, -inv_pow, mul_div_assoc]
    _ = 2 * t₀ := by
      simp only [t₀]
      congr! 2 with i hi
      simp [field, pow_succ, pow_mul]
  have hk' : (k + 1 : ℝ) / k = (1 + x₀) / (1 - x₀) := by
    simp [x₀, field]
    ring
  have ht₀' : t₀ ≤ 1 / 2 * t₁ := artanh_partial_series_lower_bound (by positivity)
    (inv_lt_one_of_one_lt₀ (by simpa using hk.bot_lt)) n
  have ht₁' : 1 / 2 * t₁ ≤ t₀ + e := by
    have he' : |t₀ - 1 / 2 * t₁| ≤ e :=
      artanh_partial_series_symmetric_bound (by simpa [abs_of_nonneg hx₀] using hx₁) n
    rw [abs_le] at he'
    linear_combination he'.1
  have he : 2 * e = (d : ℝ)⁻¹ := by
    have hk'' : (2 * k + 1 : ℝ) ^ 2 - 1 = 4 * k * (k + 1) := by ring
    simp only [e, abs_of_nonneg hx₀, x₀, hd]
    simp [field, hk'', mul_assoc, ← pow_add]
    rw [mul_comm]
    congr! 2
    · omega
    · norm_num
  rw [ht₀, hk', ← ht₁, ← he, ← mul_add]
  constructor
  · linear_combination 2 * ht₀'
  · linear_combination 2 * ht₁'

end taylor

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

lemma binarySplit_nonzero {m n ps qs pt qt : ℕ} (hb : ∀ i, b i ≠ 0) (hq : ∀ i, q i ≠ 0)
    (h : (ps, qs, pt, qt) = binarySplit p q a b m n) :
    qs ≠ 0 ∧ qt ≠ 0 := by
  fun_induction binarySplit generalizing ps qs pt qt with simp_all

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
          obtain ⟨hqsl, hqtl⟩ := binarySplit_nonzero hb hq hl.symm
          obtain ⟨hqsr, hqtr⟩ := binarySplit_nonzero hb hq hr.symm
          rw [ih2.2]
          simp [field]

lemma binarySplitSum_spec {n : ℕ} (hb : ∀ i, b i ≠ 0) (hq : ∀ i, q i ≠ 0) :
    toRat (binarySplitSum p q a b n) =
      ∑ i ∈ range n, (a i / b i : ℚ) * (∏ j ∈ range i, p j / q j : ℚ) := by
  rw [binarySplitSum]
  match hmn : binarySplit p q a b 0 n with
  | ⟨pt, qt, ps, qs⟩ => rw [toRat, ← (binarySplit_spec hb hq hmn.symm).2, range_eq_Ico]

end binarySplit

section kernel

def _root_.Nat.eager (n : ℕ) (k : ℕ → ℕ × ℕ) : ℕ × ℕ :=
  n.rec (k 0) (fun n _ ↦ k n.succ)

@[simp] lemma eager_eq {n : ℕ} {k} : n.eager k = k n := by cases n <;> rfl

def iterate (k : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ :=
  Nat.rec (fun a b ↦ (a, b)) fun n r a b ↦
    a.eager fun _ ↦
      r ((b.mul k).add (a.mul (n.mul 2).succ)) ((b.mul k).mul (n.mul 2).succ)

@[simp] lemma iterate_zero {k a b} : iterate k 0 a b = (a, b) := rfl

lemma iterate_succ {k n a b : ℕ} :
    iterate k (n + 1) a b =
      iterate k n
       ((b.mul k).add (a.mul (n.mul 2).succ)) ((b.mul k).mul (n.mul 2).succ) := by
  rw [iterate]
  exact eager_eq

@[simp] lemma iterate_succ' {k n a b : ℕ} :
    iterate k (n + 1) a b =
      iterate k n (b * k + a * (n * 2 + 1)) (b * k * (n * 2 + 1)) := by
  rw [iterate_succ]
  rfl

lemma iterate_snd_ne_zero {k n a b : ℕ} (hk : k ≠ 0) (hb : b ≠ 0) :
    (iterate k n a b).2 ≠ 0 := by
  induction n generalizing a b with
  | zero => simpa
  | succ n ih =>
    simp only [iterate_succ']
    apply ih _
    positivity

lemma toRat_inner_fn {k n a b : ℕ} (hk : k ≠ 0) (hb : b ≠ 0) :
    toRat ⟨b * k + a * (n * 2 + 1), b * k * (n * 2 + 1)⟩ =
      1 / (2 * n + 1) + (k : ℚ)⁻¹ * toRat (a, b) := by
  have : (k : ℚ) ≠ 0 := by positivity
  have : (b : ℚ) ≠ 0 := by positivity
  simp [toRat, field]

lemma iterate_rat {k n a b : ℕ} (hk : k ≠ 0) (hb : b ≠ 0) :
    toRat (iterate k n a b) =
      ∑ i ∈ Finset.range n, ((k : ℚ)⁻¹) ^ i / (2 * i + 1) + (k : ℚ)⁻¹ ^ n * toRat (a, b) := by
  induction n generalizing a b with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ', ih (by positivity), toRat_inner_fn hk hb, Finset.sum_range_succ, mul_add,
      ← add_assoc, mul_one_div, ← mul_assoc, pow_succ]

lemma myBinarySplit_aux (k a b : ℕ) :
    (binarySplit (fun _ ↦ 1) (fun _ ↦ k) (fun _ ↦ 1) (fun i ↦ 2 * i + 1) a b).2.2.1 = 1 := by
  simp [binarySplit_pt]

def myBinarySplit (k a b : ℕ) : ℕ × ℕ × ℕ :=
  match binarySplit (fun _ ↦ 1) (fun _ ↦ k) (fun _ ↦ 1) (fun i ↦ 2 * i + 1) a b with
  | ⟨p, q, _, b⟩ => ⟨p, q, b⟩

def myBinarySplitSum (k n : ℕ) : ℕ × ℕ :=
  binarySplitSum (fun _ ↦ 1) (fun _ ↦ k) (fun _ ↦ 1) (fun i ↦ 2 * i + 1) n

lemma myBinarySplitSum_eq {k n} :
    myBinarySplitSum k n = match myBinarySplit k 0 n with | ⟨p, q, _⟩ => (p, q) := by
  rw [myBinarySplitSum, myBinarySplit, binarySplitSum]

lemma toRat_myBinarySplitSum_eq {k n} (hk : k ≠ 0) :
    toRat (myBinarySplitSum k n) = ∑ i ∈ Finset.range n, ((k : ℚ)⁻¹) ^ i / (2 * i + 1) := by
  rw [myBinarySplitSum, binarySplitSum_spec (fun _ ↦ by positivity) (fun _ ↦ hk)]
  congr! 1 with i hi
  simp
  ring

lemma myBinarySplit_of_le {k a b : ℕ} (hab : b.ble a) :
    myBinarySplit k a b = (0, 1, 1) := by
  simp only [Nat.ble_eq] at hab
  rw [myBinarySplit, binarySplit, if_neg (by simpa)]

lemma myBinarySplit_of_base {k a a' b : ℕ} (hab : a.succ.beq b)
    (ha' : a'.beq (Nat.mul 2 a).succ) :
    myBinarySplit k a b = (1, a', k) := by
  simp only [Nat.succ_eq_add_one, Nat.beq_eq, Nat.mul_eq] at hab ha'
  rw [myBinarySplit, binarySplit, if_pos (by omega), if_pos hab]
  grind

lemma myBinarySplit_rec {k a b m pl ql bl pr qr br p' q' b' : ℕ} (hab : a.succ.blt b)
    (hm : m.beq ((a.add b).div 2))
    (hp' : p'.beq (Nat.add ((pl.mul bl).mul qr) (ql.mul pr)))
    (hq' : q'.beq ((ql.mul bl).mul qr))
    (hb' : b'.beq (bl.mul br))
    (ham : myBinarySplit k a m = (pl, ql, bl))
    (hmb : myBinarySplit k m b = (pr, qr, br)) :
    myBinarySplit k a b = (p', q', b') := by
  simp only [Nat.succ_eq_add_one, Nat.blt_eq, Nat.add_eq, Nat.div_eq', Nat.beq_eq,
    Nat.mul_eq] at hab hm hp' hq' hb'
  subst hm hp' hq' hb'
  rw [myBinarySplit] at ham hmb ⊢
  rw [binarySplit, if_pos (by grind), if_neg (by grind)]
  dsimp at ham hmb ⊢
  cases ham
  cases hmb
  rw [myBinarySplit_aux]
  simp

end kernel

lemma abs_sub_le_of_mem_Icc {a b c d : ℝ}
    (ha : a ∈ Icc c d)
    (hb : b ∈ Icc c d) :
    |a - b| ≤ |d - c| := by
  simp only [Set.mem_Icc] at ha hb ⊢
  obtain hdc | hcd := lt_or_ge d c
  · grind
  rw [abs_of_nonneg (show 0 ≤ d - c by linarith), abs_sub_le_iff]
  constructor <;> linarith

lemma abs_log_sub_le_better'
    (n k d e p q x y : ℕ)
    (hn : n ≠ 0)
    (hk : k ≠ 0)
    -- (hd₀ : d ≠ 0)
    (he : e = 2 * k * (k + 1) * ((2 * k + 1) ^ (2 * n - 1)))
    -- (hd : d ≤ e)
    (hpq : p / q - (d : ℝ)⁻¹ ≤ (2 * x) / ((2 * k + 1) * y))
    (hpq' : (2 * x : ℝ) / ((2 * k + 1) * y) + (e : ℝ)⁻¹ ≤ p / q + (d : ℝ)⁻¹)
    (hxy : (x, y) = iterate ((2 * k + 1) ^ 2) n 0 1) :
    |log ((k + 1) / k) - p / q| ≤ (d : ℝ)⁻¹ := by
  have : toRat (x, y) = ∑ i ∈ Finset.range n, (((2 * k + 1 : ℝ) ^ 2)⁻¹) ^ i / (2 * i + 1) := by
    rw [hxy, iterate_rat (by positivity) (by positivity)]
    simp [toRat]
  let lo : ℝ := 2 / (2 * k + 1) * (x / y)
  have hlo : lo = (2 * x) / ((2 * k + 1) * y) := by simp [lo, div_mul_div_comm]
  rw [← hlo] at hpq hpq'
  have h₁ : lo ≤ _ ∧ _ ≤ lo + _ :=
    log_bounds n k e (x / y) hk hn he (by simpa [toRat] using this)
  rw [abs_le]
  constructor
  · linear_combination hpq + h₁.1
  · linear_combination hpq' + h₁.2

lemma abs_log_sub_le_better
    (n k k₁ k₂ k₃ d e p q x y g g' q' d' y' e' : ℕ)
    (hn₀ : Nat.blt 0 n)
    (hk₀ : Nat.blt 0 k)
    (hd₀ : Nat.blt 0 d)
    (hq₀ : Nat.blt 0 q)
    (he₀ : Nat.blt 0 e)
    (hk₁ : k₁.beq k.succ) (hk₂ : k₂.beq (k.add k₁)) (hk₃ : k₃.beq (k₂.mul k₂))
    (he : e.beq ((Nat.mul 2 (k.mul k₁)).mul (k₂.pow ((n.mul 2).sub 1))))
    (hq' : q.beq (g.mul q')) (hd' : d.beq (g.mul d'))
    (hy' : (y.mul k₂).beq (g'.mul y')) (he' : e.beq (g'.mul e'))
    (h₁ : ((d.mul q').mul (((x.mul 2).mul e').add y')).ble ((e.mul y').mul ((d'.mul p).add q')))
    (h₂ : (((g'.mul y').mul p).mul d').ble (q'.mul ((d.mul (x.mul 2)).add (y.mul k₂))))
    (hxy : (x, y) = iterate k₃ n 0 1) :
    |log (OfNat.ofNat k₁ / OfNat.ofNat k) - OfNat.ofNat p / OfNat.ofNat q| ≤ (OfNat.ofNat d)⁻¹ := by
  simp [← mul_assoc, mul_comm n 2] at hn₀ hk₀ hd₀ hq₀ he₀ hk₁ hk₂ hk₃ he hq' hd' hy' he' h₁ h₂
  replace hk₂ : k₂ = 2 * k + 1 := by grind
  replace hk₃ : k₃ = (2 * k + 1) ^ 2 := by grind
  subst hk₁ hk₂ hk₃
  suffices |log ((k + 1 : ℝ) / k) - (p / q : ℝ)| ≤ (d : ℝ)⁻¹ by
    rw [← Nat.cast_add_one] at this
    simpa [← Lean.Grind.Semiring.ofNat_eq_natCast] using this
  have hy₀ : y ≠ 0 := by
    have : (iterate ((2 * k + 1) ^ 2) n 0 1).2 ≠ 0 :=
      iterate_snd_ne_zero (by positivity) (by simp)
    rw [← hxy] at this
    exact this
  apply abs_log_sub_le_better' n k d e p q x y hn₀.ne' hk₀.ne' he _ _ hxy
  · rw [← one_div, sub_le_iff_le_add, div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    norm_cast
    calc
      p * ((2 * k + 1) * y * d) = g' * y' * p * d' * g := by grind
      _ ≤ q' * (d * x * 2 + y * (2 * k + 1)) * g := by grw [h₂]
      _ = (2 * x * d + (2 * k + 1) * y * 1) * q := by grind
  · rw [← one_div, ← one_div, div_add_div _ _ (by positivity) (by positivity),
      div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    norm_cast
    calc
      (2 * x * e + (2 * k + 1) * y * 1) * (q * d) = d * q' * (x * 2 * e' + y') * (g * g') := by grind
      _ ≤ e * y' * (d' * p + q') * (g * g') := by grw [h₁]
      _ = (p * d + q * 1) * ((2 * k + 1) * y * e) := by grind

lemma abs_log_sub_le_better_red
    (n k d e p x y : ℕ)
    (hn : n ≠ 0)
    (hk : k ≠ 0)
    -- (hd₀ : d ≠ 0)
    (he : e = 2 * k * (k + 1) * ((2 * k + 1) ^ (2 * n - 1)))
    -- (hd : d ≤ e)
    (hpq : p / d - (d : ℝ)⁻¹ ≤ (2 * x) / ((2 * k + 1) * y))
    (hpq' : (2 * x : ℝ) / ((2 * k + 1) * y) + (e : ℝ)⁻¹ ≤ p / d + (d : ℝ)⁻¹)
    (hxy : (x, y) = iterate ((2 * k + 1) ^ 2) n 0 1) :
    |log ((k + 1) / k) - p / d| ≤ (d : ℝ)⁻¹ := by
  have : toRat (x, y) = ∑ i ∈ Finset.range n, (((2 * k + 1 : ℝ) ^ 2)⁻¹) ^ i / (2 * i + 1) := by
    rw [hxy, iterate_rat (by positivity) (by positivity)]
    simp [toRat]
  let lo : ℝ := 2 / (2 * k + 1) * (x / y)
  have hlo : lo = (2 * x) / ((2 * k + 1) * y) := by simp [lo, div_mul_div_comm]
  rw [← hlo] at hpq hpq'
  have h₁ : lo ≤ _ ∧ _ ≤ lo + _ :=
    log_bounds n k e (x / y) hk hn he (by simpa [toRat] using this)
  rw [abs_le]
  constructor
  · linear_combination hpq + h₁.1
  · linear_combination hpq' + h₁.2

lemma abs_log_sub_le'
    (n k d p q x y : ℕ)
    (hn : n ≠ 0)
    (hk : k ≠ 0)
    (hd₀ : d ≠ 0)
    (hd : d ≤ 2 * k * (k + 1) * ((2 * k + 1) ^ (2 * n - 1)))
    (hpq : (2 * x : ℝ) / ((2 * k + 1) * y) ≤ p / q)
    (hpq' : (p / q : ℝ) ≤ (2 * x) / ((2 * k + 1) * y) + (d : ℝ)⁻¹)
    (hxy : (x, y) = iterate ((2 * k + 1) ^ 2) n 0 1) :
    |log ((k + 1) / k) - p / q| ≤ (d : ℝ)⁻¹ := by
  set e := 2 * k * (k + 1) * ((2 * k + 1) ^ (2 * n - 1))
  have : toRat (x, y) = ∑ i ∈ Finset.range n, (((2 * k + 1 : ℝ) ^ 2)⁻¹) ^ i / (2 * i + 1) := by
    rw [hxy, iterate_rat (by positivity) (by positivity)]
    simp [toRat]
  let lo : ℝ := 2 / (2 * k + 1) * (x / y)
  have h₁' : _ ∈ Set.Icc lo (lo + (e : ℝ)⁻¹) :=
    log_bounds n k e (x / y) hk hn rfl (by simpa [toRat] using this)
  have h₁ : log ((k + 1) / k) ∈ Set.Icc lo (lo + (d : ℝ)⁻¹) :=
    Icc_subset_Icc_right (by grw [hd]) h₁'
  have h₂ : (p / q : ℝ) ∈ Set.Icc lo (lo + (d : ℝ)⁻¹) := by simp [lo, div_mul_div_comm, hpq, hpq']
  simpa using abs_sub_le_of_mem_Icc h₁ h₂

lemma abs_log_sub_le
    (n k k₁ k₂ k₃ d p q g x y d' y' : ℕ)
    (hn : Nat.blt 0 n) (hk : Nat.blt 0 k) (hq : Nat.blt 0 q) (hd₀ : Nat.blt 0 d)
    (hk₁ : k₁.beq k.succ) (hk₂ : k₂.beq (k.add k₁)) (hk₃ : k₃.beq (k₂.mul k₂))
    (hd : d.ble ((Nat.mul 2 (k.mul k₁)).mul (k₂.pow ((n.mul 2).sub 1))))
    (hpq : (q.mul (x.mul 2)).ble (p.mul (y.mul k₂)))
    (hd' : d.beq (g.mul d')) (hy' : (y.mul k₂).beq (g.mul y'))
    (hpq' : (d.mul (p.mul y')).ble (q.mul (((d'.mul (x.mul 2))).add y')))
    (hxy : (x, y) = iterate k₃ n 0 1) :
    |log (OfNat.ofNat k₁ / OfNat.ofNat k) - OfNat.ofNat p / OfNat.ofNat q| ≤ (OfNat.ofNat d)⁻¹ := by
  simp [← mul_assoc, mul_comm n 2] at hn hk hq hd₀ hk₁ hk₂ hk₃ hd hpq hd' hy' hpq'
  replace hk₂ : k₂ = 2 * k + 1 := by grind
  replace hk₃ : k₃ = (2 * k + 1) ^ 2 := by grind
  subst hk₁ hk₂ hk₃
  suffices |log ((k + 1 : ℝ) / k) - (p / q : ℝ)| ≤ (d : ℝ)⁻¹ by
    rw [← Nat.cast_add_one] at this
    simpa [← Lean.Grind.Semiring.ofNat_eq_natCast] using this
  have hy₀ : y ≠ 0 := by
    have : (iterate ((2 * k + 1) ^ 2) n 0 1).2 ≠ 0 :=
      iterate_snd_ne_zero (by positivity) (by simp)
    rw [← hxy] at this
    exact this
  apply abs_log_sub_le' n k d p q x y hn.ne' hk.ne' hd₀.ne' hd _ _ hxy
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    norm_cast
    linear_combination hpq
  · rw [← one_div, div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    norm_cast
    calc
      p * ((2 * k + 1) * y * d) = d * p * y' * g := by grind
      _ ≤ (q * (d' * x * 2 + y')) * g := by grw [hpq']
      _ = (2 * x * d + (2 * k + 1) * y * 1) * q := by grind

section

lemma decompose :
    log 2 = 7 * log (16 / 15) + 5 * log (25 / 24) + 3 * log (81 / 80) := by
  have : (2 : ℝ) = (16 / 15) ^ 7 * (25 / 24) ^ 5 * (81 / 80) ^ 3 := by norm_num
  rw [this, log_mul (by simp) (by simp), log_mul (by simp) (by simp),
    log_pow, log_pow, log_pow]
  simp

lemma combine
    (p q p₁ p₂ p₃ d₁ i : ℕ)
    (hp : p.beq (((p₁.mul 7).add (p₂.mul 5)).add (p₃.mul 3)))
    (hd₁ : ((Nat.pow 2 i).mul 15).ble d₁)
    (h₁ : |log (16 / 15) - OfNat.ofNat p₁ / OfNat.ofNat q| ≤ (OfNat.ofNat d₁)⁻¹)
    (h₂ : |log (25 / 24) - OfNat.ofNat p₂ / OfNat.ofNat q| ≤ (OfNat.ofNat d₁)⁻¹)
    (h₃ : |log (81 / 80) - OfNat.ofNat p₃ / OfNat.ofNat q| ≤ (OfNat.ofNat d₁)⁻¹) :
    |log 2 - (OfNat.ofNat p / OfNat.ofNat q : ℚ)| ≤ (2 ^ (OfNat.ofNat i))⁻¹ := by
  simp [Nat.mul_eq, Nat.add_eq, Nat.beq_eq, Nat.ble_eq] at hp hd₁
  replace h₁ : |log (16 / 15) - p₁ / q| ≤ (d₁ : ℝ)⁻¹ := by
    simpa [← Lean.Grind.Semiring.ofNat_eq_natCast] using h₁
  replace h₂ : |log (25 / 24) - p₂ / q| ≤ (d₁ : ℝ)⁻¹ := by
    simpa [← Lean.Grind.Semiring.ofNat_eq_natCast] using h₂
  replace h₃ : |log (81 / 80) - p₃ / q| ≤ (d₁ : ℝ)⁻¹ := by
    simpa [← Lean.Grind.Semiring.ofNat_eq_natCast] using h₃
  suffices |log 2 - p / q| ≤ (2 ^ i : ℝ)⁻¹ by
    simp only [Rat.cast_div]
    exact this
  calc
    |log 2 - p / q| = |7 * (log (16 / 15) - p₁ / q) +
                       5 * (log (25 / 24) - p₂ / q) +
                       3 * (log (81 / 80) - p₃ / q)| := by
      simp only [decompose, hp, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring_nf
    _ ≤ |7 * (log (16 / 15) - p₁ / q)| +
        |5 * (log (25 / 24) - p₂ / q)| +
        |3 * (log (81 / 80) - p₃ / q)| := abs_add_three _ _ _
    _ = 7 * |log (16 / 15) - p₁ / q| +
        5 * |log (25 / 24) - p₂ / q| +
        3 * |log (81 / 80) - p₃ / q| := by simp
    _ ≤ 15 * (d₁ : ℝ)⁻¹ := by linear_combination 7 * h₁ + 5 * h₂ + 3 * h₃
    _ ≤ (2 ^ i : ℝ)⁻¹ := by grw [← hd₁]; simp

open Matrix

namespace decomp2

def x : Fin 10 → ℤ :=
  ![84330, 56513, 74396, 53829, 89725, 33896, 75974, 97994, 68941, 16808]

noncomputable def z_aux : Fin 10 → ℝ :=
  ![8268800 / 8268799,
    5909761 / 5909760,
    5142501 / 5142500,
    4096576 / 4096575,
    4090625 / 4090624,
    4004001 / 4004000,
    709632 / 709631,
    613089 / 613088,
    601426 / 601425,
    71875 / 71874]

lemma z_aux_ne_zero (i : Fin 10) : z_aux i ≠ 0 := by
  fin_cases i <;> simp [z_aux]

theorem main' : ∏ i : Fin 10, z_aux i ^ x i = 2 := by
  norm_num [Fin.prod_univ_succ, z_aux, x]

lemma main : 84330 * log (8268800 / 8268799) +
             56513 * log (5909761 / 5909760) +
             74396 * log (5142501 / 5142500) +
             53829 * log (4096576 / 4096575) +
             89725 * log (4090625 / 4090624) +
             33896 * log (4004001 / 4004000) +
             75974 * log (709632 / 709631) +
             97994 * log (613089 / 613088) +
             68941 * log (601426 / 601425) +
             16808 * log (71875 / 71874) = log 2 := by
  suffices ∑ i : Fin 10, (x i : ℝ) * log (z_aux i) = log 2 by
    norm_num [Fin.sum_univ_succ, z_aux, x] at this
    simpa [add_assoc] using this
  rw [← main', log_prod]
  · simp only [log_zpow]
  simp [zpow_ne_zero, z_aux_ne_zero]

end decomp2

section

def A : Matrix (Fin 15) (Fin 15) ℤ :=
  !![2, 5, -4, -1, 1, -1, -1, 0, 0, 0, -2, 0, 0, 2, 1;
     1, 5, 0, 2, 0, 0, 0, -2, 0, 1, 1, -1, -3, 1, 0;
     -6, 4, -2, 0, 2, 2, 0, -2, 2, 0, 0, -1, -1, 0, 0;
     -1, 1, -5, -1, -1, 1, 0, 1, 1, 1, 1, -2, 0, 1, 0;
     -8, -1, -1, 4, 1, -2, 1, 0, -1, 1, 0, 0, -1, 0, 1;
     -1, -1, 3, 0, 4, 0, 1, 1, 0, -1, 0, 0, -2, -1, -1;
     1, -2, 0, -1, -1, 1, 2, 0, 0, -4, 0, 1, 1, 1, 0;
     1, -1, 0, 1, 0, 2, 2, -4, 1, -1, 1, 0, 0, -1, 0;
     -4, -5, 2, 2, -1, 2, -2, 0, 0, 0, 0, -1, 0, 0, 2;
     9, 1, -2, 1, -3, -1, 0, 0, 1, 0, -2, 0, 2, 0, 0;
     -6, 2, -2, 6, 0, -1, -1, 2, -1, 0, 0, 0, 0, 0, -1;
     1, 1, 5, 2, -7, 1, 0, -1, 0, 0, 1, 0, 0, 0, 0;
     -4, 8, 0, 2, -1, -3, -1, 0, 0, 0, 2, 0, 0, 0, -1;
     -4, -2, -1, -3, 1, 0, 1, 0, 0, -1, 1, 3, -1, 0, 0;
     -2, -5, 1, -2, 0, -2, -1, 2, 0, 0, 0, 0, 1, 2, 0]

def x : Fin 15 → ℤ :=
  ![122324552, -75806406, -58834645, 52889168, -9727598, 90645248, -61102303, 108313849, 6176249,
    -29974075, 23287250, 64465156, 11016954, 12805279, 19164767]

def y_aux : Fin 15 → ℚ :=
  ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

lemma y_aux_ne_zero : ∀ i, y_aux i ≠ 0 := by decide +kernel

noncomputable def y (i : Fin 15) : ℝ := log (y_aux i)

lemma x_vecMul_A : x ᵥ* A = ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [← Matrix.vecMulᵣ_eq]
  decide +kernel

def z_aux : Fin 15 → ℚ :=
  ![929166876 / 929166875,
    920577798 / 920577797,
    876219201 / 876219200,
    658831251 / 658831250,
    611969281 / 611969280,
    591130375 / 591130374,
    490145734 / 490145733,
    487530862 / 487530861,
    457318225 / 457318224,
    415704576 / 415704575,
    382241601 / 382241600,
    370256250 / 370256249,
    308950929 / 308950928,
    293635441 / 293635440,
    136835245 / 136835244]

noncomputable def z (i : Fin 15) : ℝ := log (z_aux i)

lemma A_mulVec_y_aux : ∀ j, ∏ i, y_aux i ^ A j i = z_aux j := by decide +kernel

lemma A_mulVec_y : A.map (↑) *ᵥ y = z := by
  ext i
  simp [Matrix.mulVec_eq_sum, y, z, ← A_mulVec_y_aux, log_prod, y_aux_ne_zero, zpow_ne_zero,
    mul_comm]

lemma main : 122324552 * log (929166876 / 929166875) +
             -75806406 * log (920577798 / 920577797) +
             -58834645 * log (876219201 / 876219200) +
             52889168 * log (658831251 / 658831250) +
             -9727598 * log (611969281 / 611969280) +
             90645248 * log (591130375 / 591130374) +
             -61102303 * log (490145734 / 490145733) +
             108313849 * log (487530862 / 487530861) +
             6176249 * log (457318225 / 457318224) +
             -29974075 * log (415704576 / 415704575) +
             23287250 * log (382241601 / 382241600) +
             64465156 * log (370256250 / 370256249) +
             11016954 * log (308950929 / 308950928) +
             12805279 * log (293635441 / 293635440) +
             19164767 * log (136835245 / 136835244) = log 2 := by calc
    _ = (fun i ↦ (x i : ℝ)) ⬝ᵥ z := by
      simp [dotProduct, Fin.sum_univ_succ, x, z, z_aux, add_assoc]
    _ = (fun i ↦ (x i : ℝ)) ⬝ᵥ (A.map (↑) *ᵥ y) := by
      rw [A_mulVec_y]
    _ = (fun i ↦ (x i : ℝ)) ᵥ* (A.map (↑)) ⬝ᵥ y := by
      rw [dotProduct_mulVec]
    _ = (fun i ↦ ((x ᵥ* A) i : ℝ)) ⬝ᵥ y := by
      congr! 1
      ext i
      simp [Matrix.vecMul_eq_sum]
    _ = log 2 := by
      simp [x_vecMul_A, dotProduct, y, Fin.sum_univ_succ, y_aux]

end

end

-- adapted from https://hackage.haskell.org/package/base-4.21.0.0/docs/src/Data.Ratio.html#local-6989586621679140706
partial def simplest (n d n' d' : ℕ) (pn qn pn' qn' : ℕ) : ℕ × ℕ :=
  let q := n / d
  let r := n % d
  let q' := n' / d'
  let r' := n' % d'
  if r = 0 then (q * pn' + pn, q * qn' + qn) else
  if q ≠ q' then ((q+1) * pn' + pn, (q+1) * qn' + qn) else
  simplest d' r' d r pn' qn' (q * pn' + pn) (q * qn' + qn)

def reduce (n d n' d' : ℕ) : ℕ × ℕ :=
  simplest d' (n' % d') d (n % d) 1 0 (n / d) 1

def iterateC (k : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, a, b => (a, b)
  | n + 1, a, b =>
    iterateC k n (b * k + a * (2 * n + 1)) ((b * k) * (2 * n + 1))

section

open Lean

open Qq OfNat in
def mkType (k₁ k p q d : ℕ) : Q(Prop) :=
  let k₁ : Q(ℕ) := mkRawNatLit k₁
  let k : Q(ℕ) := mkRawNatLit k
  let p : Q(ℕ) := mkRawNatLit p
  let q : Q(ℕ) := mkRawNatLit q
  let d : Q(ℕ) := mkRawNatLit d
  q(|Real.log (ofNat $k₁ / ofNat $k) - ofNat $p / ofNat $q| ≤ (ofNat $d)⁻¹)

open Qq OfNat in
def mkDiv (p q : ℕ) : Q(ℚ) :=
  let p : Q(ℕ) := mkRawNatLit p
  let q : Q(ℕ) := mkRawNatLit q
  q(ofNat $p / ofNat $q)

open Qq OfNat in
def mkType2 (d : ℕ) (e : Q(ℚ)) : Q(Prop) :=
  let d : Q(ℕ) := mkRawNatLit d
  q(|Real.log 2 - $e| ≤ (2 ^ ofNat $d)⁻¹)

def mkContinuedFractionProof (k n : ℕ) : ℕ × ℕ × ℕ × Expr :=
  let k₁ : ℕ := k + 1
  let k₂ : ℕ := k + k₁
  let k₃ := k₂ ^ 2
  let d := 2 * k * k₁ * (k₂ ^ (2 * n - 1))
  let (x, y) := iterateC k₃ n 0 1
  let g := Nat.gcd d (y * k₂)
  let d' := d / g
  let y' := (y * k₂) / g
  let (p, q) : ℕ × ℕ := reduce (2 * x) (y * k₂) (2 * x * d' + y') (d * y')
  let pf₁ : Expr := mkApp5 (mkConst ``Real.abs_log_sub_le) (mkNatLit n) (mkRawNatLit k)
    (mkRawNatLit k₁) (mkNatLit k₂) (mkNatLit k₃)
  let pf₂ : Expr := mkApp8 pf₁ (mkRawNatLit d) (mkRawNatLit p) (mkRawNatLit q) (mkNatLit g)
    (mkNatLit x) (mkNatLit y) (mkNatLit d') (mkNatLit y')
  let pf₃ : Expr := mkApp7 pf₂ reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue
    reflBoolTrue reflBoolTrue reflBoolTrue
  let pf₄ : Expr := mkApp6 pf₃ reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue
      (mkApp2
        (Lean.mkConst ``Eq.refl [1])
        (mkApp2 (Lean.mkConst ``Prod [0, 0]) (Lean.mkConst ``Nat) (Lean.mkConst ``Nat))
        (mkApp4 (Lean.mkConst ``Prod.mk [0, 0])
          (Lean.mkConst ``Nat) (Lean.mkConst ``Nat) (mkRawNatLit x) (mkRawNatLit y)))
  (p, q, d, pf₄)

open Lean
elab "bound_logc%" ppSpace k:num n:num : term => do
  let n : ℕ := n.getNat
  let k : ℕ := k.getNat
  unless k ≠ 0 do throwError "first argument must be nonzero"
  unless n ≠ 0 do throwError "second argument must be nonzero"
  let (p, q, d, pf) := mkContinuedFractionProof k n
  let ty := mkType (k + 1) k p q d
  let nm ← Meta.mkAuxLemma [] ty pf none
  return mkConst nm

def mkDyadicProof (k n i j : ℕ) : MetaM (ℕ × Expr) := do
  let k₁ : ℕ := k + 1
  let k₂ : ℕ := k + k₁
  let k₃ := k₂ ^ 2
  let e := 2 * k * k₁ * (k₂ ^ (2 * n - 1))
  let d : ℕ := 2 ^ i
  unless d ≤ 2 * e do
    let lo := (d + 4 * k * k₁ - 1) / (4 * k * k₁)
    throwError
      "not enough terms in expansion at {k}; can only get precision {Nat.log2 (2 * e)}.\n\
      for your desired precision, try {1 + (Nat.logC k₂ lo + 1) / 2} terms"
  let q := 2 ^ j
  unless (2 * e - d) * q ≥ e * d do
    throwError s!"need larger denominators to stay in interval, try j = \
      {Nat.log2 ((e * d + 2 * e - d - 1) / (2 * e - d) - 1) + 1}"
  let (x, y) := iterateC k₃ n 0 1
  let p := (2 * (x * 2) * q * e + q * (y * k₂) + (y * k₂) * e) / (2 * (y * k₂) * e)
  let g' := Nat.gcd e (y * k₂)
  let e' := e / g'
  let y' := (y * k₂) / g'
  let g := Nat.gcd d q
  let d' := d / g
  let q' := q / g
  let pf₁ : Expr := mkApp5 (mkConst ``Real.abs_log_sub_le_better) (mkNatLit n) (mkRawNatLit k)
    (mkRawNatLit k₁) (mkNatLit k₂) (mkNatLit k₃)
  let pf₂ : Expr := mkApp6 pf₁ (mkRawNatLit d) (mkNatLit e) (mkRawNatLit p) (mkRawNatLit q)
    (mkNatLit x) (mkNatLit y)
  let pf₃ : Expr := mkApp6 pf₂ (mkNatLit g) (mkNatLit g') (mkNatLit q') (mkNatLit d')
    (mkNatLit y') (mkNatLit e')
  let pf₄ : Expr := mkApp5 pf₃ reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue
  let pf₅ : Expr := mkApp8 pf₄ reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue
    reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue
  let pf₆ : Expr := mkApp3 pf₅ reflBoolTrue reflBoolTrue
      (mkApp2
        (Lean.mkConst ``Eq.refl [1])
        (mkApp2 (Lean.mkConst ``Prod [0, 0]) (Lean.mkConst ``Nat) (Lean.mkConst ``Nat))
        (mkApp4 (Lean.mkConst ``Prod.mk [0, 0])
          (Lean.mkConst ``Nat) (Lean.mkConst ``Nat) (mkRawNatLit x) (mkRawNatLit y)))
  return (p, pf₆)

elab "bound_log%" ppSpace k:num n:num i:num j:num : term => do
  let n : ℕ := n.getNat
  let k : ℕ := k.getNat
  let i : ℕ := i.getNat
  let j : ℕ := j.getNat
  unless k ≠ 0 do throwError "first argument must be nonzero"
  unless n ≠ 0 do throwError "second argument must be nonzero"
  let (p, pf) ← mkDyadicProof k n i j
  let ty := mkType (k + 1) k p (2 ^ j) (2 ^ i)
  let nm ← Meta.mkAuxLemma [] ty pf none
  return mkConst nm

elab "bound_log2%" ppSpace i:num : command => Elab.Command.liftTermElabM do
  let i : ℕ := i.getNat
  let i' : ℕ := i + 4
  let d' := 2 ^ i'
  let q := d'
  let (p₁, pf₁) ← do
    let k₁ := (d' + 479) / 480
    let n₁ := (Nat.logC 31 k₁ + 1) / 2 + 1
    mkDyadicProof 15 n₁ i' i'
  let ty₁ := mkType 16 15 p₁ q d'
  let (p₂, pf₂) ← do
    let k₂ := (d' + 1199) / 1200
    let n₂ := (Nat.logC 49 k₂ + 1) / 2 + 1
    mkDyadicProof 24 n₂ i' i'
  let ty₂ := mkType 25 24 p₂ q d'
  let (p₃, pf₃) ← do
    let k₃ := (d' + 12959) / 12960
    let n₃ := (Nat.logC 161 k₃ + 1) / 2 + 1
    mkDyadicProof 80 n₃ i' i'
  let ty₃ := mkType 81 80 p₃ q (2 ^ i')
  let p := p₁ * 7 + p₂ * 5 + p₃ * 3
  let nm ← Meta.mkAuxDefinition (.mkSimple s!"log2Approx{i}") (mkConst ``Rat) (mkDiv p q)
  let nm₁ ← Meta.mkAuxLemma [] ty₁ pf₁ none
  let nm₂ ← Meta.mkAuxLemma [] ty₂ pf₂ none
  let nm₃ ← Meta.mkAuxLemma [] ty₃ pf₃ none
  let pf : Expr := mkApp7 (mkConst ``combine) (mkRawNatLit p) (mkRawNatLit q) (mkRawNatLit p₁)
    (mkRawNatLit p₂) (mkRawNatLit p₃) (mkRawNatLit (2 ^ (i + 4))) (mkRawNatLit i)
  let pf : Expr := mkApp5 pf reflBoolTrue reflBoolTrue (mkConst nm₁) (mkConst nm₂) (mkConst nm₃)
  let ty := mkType2 i nm
  let _ ← addDecl (.thmDecl
    { name := (.mkSimple s!"log2Approx{i}_spec"),
      levelParams := [],
      type := ty,
      value := pf})

-- whatsnew in
-- bound_log2% 332193

end

-- lemma ineq : (2 ^ 332193 : ℝ)⁻¹ ≤ (10 ^ 100000)⁻¹ := by
--   apply inv_anti₀ (by simp)
--   suffices 10 ^ 100000 ≤ 2 ^ 332193 from mod_cast this
--   decide +kernel

-- example : |log 2 - (log2Approx332193 : ℚ)| ≤ (10 ^ 100000)⁻¹ := calc
--   _ ≤ (2 ^ 332193)⁻¹ := log2Approx332193_spec
--   _ ≤ (10 ^ 100000)⁻¹ := ineq
