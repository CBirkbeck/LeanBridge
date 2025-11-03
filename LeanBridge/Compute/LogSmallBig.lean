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

namespace Real

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

def _root_.Nat.eager (n : ℕ) (k : ℕ → ℕ × ℕ) : ℕ × ℕ :=
  n.rec (k 0) (fun n _ ↦ k n.succ)

@[simp] lemma eager_eq {n : ℕ} {k} : n.eager k = k n := by cases n <;> rfl

def iterate (k : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ :=
  Nat.rec (fun acc ↦ acc) fun n r acc ↦
    acc.1.eager fun _ ↦
      r ⟨(acc.2.mul k).add (acc.1.mul (n.mul 2).succ), (acc.2.mul k).mul (n.mul 2).succ⟩

@[simp] lemma iterate_zero {k acc} : iterate k 0 acc = acc := rfl

lemma iterate_succ {k n : ℕ} {acc : ℕ × ℕ} :
    iterate k (n + 1) acc =
      iterate k n (
        ⟨(acc.2.mul k).add (acc.1.mul (n.mul 2).succ), (acc.2.mul k).mul (n.mul 2).succ⟩) := by
  rw [iterate]
  exact eager_eq

@[simp] lemma iterate_succ' {k n : ℕ} {acc : ℕ × ℕ} :
    iterate k (n + 1) acc =
      iterate k n ⟨acc.2 * k + acc.1 * (n * 2 + 1), acc.2 * k * (n * 2 + 1)⟩ := by
  rw [iterate_succ]
  rfl

lemma iterate_snd_ne_zero {k n : ℕ} {acc : ℕ × ℕ} (hk : k ≠ 0) (hacc : acc.2 ≠ 0) :
    (iterate k n acc).2 ≠ 0 := by
  induction n generalizing acc with
  | zero => simpa
  | succ n ih =>
    simp only [iterate_succ']
    apply ih _
    positivity

def toRat (p : ℕ × ℕ) : ℚ := p.1 / p.2

lemma toRat_inner_fn {k n : ℕ} (hk : k ≠ 0) {acc : ℕ × ℕ} (hacc : acc.2 ≠ 0) :
    toRat ⟨acc.2 * k + acc.1 * (n * 2 + 1), acc.2 * k * (n * 2 + 1)⟩ =
      1 / (2 * n + 1) + (k : ℚ)⁻¹ * toRat acc := by
  have : (k : ℚ) ≠ 0 := by positivity
  have : (acc.2 : ℚ) ≠ 0 := by positivity
  simp [toRat, field]

lemma iterate_rat {k n : ℕ} (hk : k ≠ 0) {acc : ℕ × ℕ} (hacc : acc.2 ≠ 0):
    toRat (iterate k n acc) =
      ∑ i ∈ Finset.range n, ((k : ℚ)⁻¹) ^ i / (2 * i + 1) + (k : ℚ)⁻¹ ^ n * toRat acc := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ', ih (by positivity), toRat_inner_fn hk hacc, Finset.sum_range_succ, mul_add,
      ← add_assoc, mul_one_div, ← mul_assoc, pow_succ]

lemma log_bounds'
    (n k k' k'' k2 : ℕ) (d g : ℕ) (x y x' y' x'' y'' : ℕ) (hk : Nat.blt 0 k) (hn : Nat.blt 0 n)
    (hk' : k'.beq k.succ)
    (hk'' : k''.beq (Nat.mul 2 k).succ)
    (hk2 : k2.beq (k''.pow 2))
    (hx' : x'.beq (x.mul 2))
    (hy' : y'.beq (y.mul k''))
    (hd : d.beq ((k2.sub 1).mul (k''.pow ((n.mul 2).sub 1))))
    (hg : Nat.blt 0 g)
    (hx'' : (x''.mul g).beq ((d.mul x').add (y'.mul 2)))
    (hy'' : (y''.mul g).beq (d.mul y'))
    (hx : (x, y) = iterate k2 n (0, 1)) :
    OfNat.ofNat x' / OfNat.ofNat y' ≤ log (OfNat.ofNat k' / OfNat.ofNat k) ∧
      log (OfNat.ofNat k' / OfNat.ofNat k) ≤ OfNat.ofNat x'' / OfNat.ofNat y'' := by
  simp only [Lean.Grind.Semiring.ofNat_eq_natCast]
  let x₀ := (2 * k + 1 : ℝ)⁻¹
  have hx₀ : 0 ≤ x₀ := by positivity
  have hx₁ : x₀ < 1 := inv_lt_one_of_one_lt₀ (by simpa using hk)
  let t₀ := ∑ i ∈ range n, x₀ ^ (2 * i + 1) / (2 * i + 1)
  let t₁ := 1 / 2 * log ((1 + x₀) / (1 - x₀))
  have ht : (x' / y' : ℝ) = 2 * t₀ := calc
    (x' / y' : ℝ) = 2 / (2 * k + 1) * toRat (x, y) := by
      simp only [Nat.succ_eq_add_one, Nat.beq_eq, Nat.mul_eq] at hk' hk'' hx' hy'
      subst hk' hk'' hx' hy'
      rw [toRat, Rat.cast_div, mul_comm (_ / _)]
      simp [div_mul_div_comm]
    _ = 2 * ∑ i ∈ Finset.range n, ((2 * k + 1 : ℝ) ^ 2)⁻¹ ^ i / ((2 * k + 1) * (2 * i + 1)) := by
      simp only [Nat.mul_eq, Nat.succ_eq_add_one, Nat.beq_eq, Nat.pow_eq] at hk'' hk2
      subst hk'' hk2
      rw [hx, iterate_rat (by positivity) (by simp), toRat]
      simp [mul_sum, div_mul_div_comm, -inv_pow, mul_div_assoc]
    _ = 2 * t₀ := by
      simp only [t₀]
      congr! 2 with i hi
      simp [field, pow_succ, pow_mul]
  have hm : (k' / k : ℝ) = (1 + x₀) / (1 - x₀) := by
    simp only [Nat.blt_eq] at hk
    simp only [Nat.succ_eq_add_one, Nat.beq_eq] at hk'
    simp [hk', x₀, field]
    ring
  have ht₀ : t₀ ≤ t₁ := artanh_partial_series_lower_bound (by positivity)
    (inv_lt_one_of_one_lt₀ (by simpa using hk)) n
  obtain ⟨hy'₀, hd₀⟩ : y' ≠ 0 ∧ d ≠ 0 := by
    simp only [Nat.mul_eq, Nat.add_eq, Nat.beq_eq, Nat.succ_eq_add_one, Nat.pow_eq, Nat.sub_eq,
      Nat.blt_eq] at hx'' hy'' hy' hk'' hk2 hd hk
    subst hy' hk'' hk2
    have : y ≠ 0 := by
      have : (iterate ((2 * k + 1) ^ 2) n (0, 1)).2 ≠ 0 :=
        iterate_snd_ne_zero (by positivity) (by simp)
      rw [← hx] at this
      exact this
    have : d ≠ 0 := by
      rintro rfl
      simp [add_sq, hk.ne'] at hd
    grind
  constructor
  · rw [ht, hm, ← le_div_iff₀' zero_lt_two, ← one_div_mul_eq_div]
    exact ht₀
  · let e := |x₀| ^ (2 * n + 1) / (1 - x₀ ^ 2)
    have he' : |t₀ - t₁| ≤ e :=
      artanh_partial_series_symmetric_bound (x := x₀) (by simpa [abs_of_nonneg hx₀] using hx₁) n
    have ht' : t₁ ≤ t₀ + e := by
      rw [abs_le] at he'
      linear_combination he'.1
    have he : e = (d : ℝ)⁻¹ := by
      simp only [Nat.sub_eq, Nat.mul_eq, Nat.pow_eq, Nat.beq_eq, Nat.succ_eq_add_one,
        Nat.blt_eq] at hd hk2 hk'' hk hn
      subst hk'' hk2 hd
      simp only [e, abs_of_nonneg hx₀, x₀]
      simp [field, ← pow_add]
      congr! 2
      grind
    calc
      log (k' / k) = 2 * t₁ := by rw [hm, ← mul_assoc, mul_div_cancel₀ _ two_ne_zero, one_mul]
      _ ≤ 2 * t₀ + 2 * e := by grw [ht', mul_add]
      _ = (x' / y') + 2 * (d : ℝ)⁻¹ := by rw [ht, he]
      _ = (x'' * g) / (y'' * g) := by
        simp only [Nat.mul_eq, Nat.add_eq, Nat.beq_eq] at hx'' hy''
        rw [← Nat.cast_mul, ← Nat.cast_mul, hx'', hy'']
        simp [field]
      _ = x'' / y'' := by
        simp only [Nat.mul_eq, Nat.add_eq, Nat.beq_eq] at hx'' hy'' hg
        rw [mul_div_mul_right]
        simp only [ne_eq, Nat.cast_eq_zero]
        rintro rfl
        simp [hd₀, hy'₀] at hy''

-- lemma log_bounds'
--     (n k k' k'' k2 : ℕ) (d g : ℕ) (x y x' y' x'' y'' : ℕ) (hk : Nat.blt 0 k) (hn : Nat.blt 0 n)
--     (hk' : k'.beq k.succ)
--     (hk'' : k''.beq (Nat.mul 2 k).succ)
--     (hk2 : k2.beq (k''.pow 2))
--     (hx' : x'.beq (x.mul 2))
--     (hy' : y'.beq (y.mul k''))
--     (hd : d.beq ((k2.sub 1).mul (k''.pow ((n.mul 2).sub 1))))
--     (hg : Nat.blt 0 g)
--     (hx'' : (x''.mul g).beq ((d.mul x').add (y'.mul 2)))
--     (hy'' : (y''.mul g).beq (d.mul y'))
--     (hx : (x, y) = iterate k2 n (0, 1)) :

-- assumes 0 < n % d < n' % d'
-- adapted from https://hackage.haskell.org/package/base-4.21.0.0/docs/src/Data.Ratio.html#local-6989586621679140706
partial def simplest' (n d n' d' : ℕ) : ℕ × ℕ :=
  let q := Nat.div n d
  let r := Nat.mod n d
  let q' := Nat.div n' d'
  let r' := Nat.mod n' d'
  if r = 0 then
    (q, 1)
  else if q ≠ q' then
    (q + 1, 1)
  else
    let (n'', d'') := simplest' d' r' d r
    (q * n'' + d'', n'')

def iterateC (k : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, acc => acc
  | n + 1, (a, b) =>
    iterateC k n (b * k + a * (2 * n + 1), (b * k) * (2 * n + 1))

#eval simplest' 69314718055994 100000000000000 69314718055995 100000000000000
-- #eval
--   let (x, y) := iterateC 961 10 (0, 1)
--   let x' :=


-- #exit

open Lean
elab "bound_log%" k:num n:num : term => do
  let n : ℕ := n.getNat
  let k : ℕ := k.getNat
  unless k ≠ 0 do throwError "first argument must be nonzero"
  unless n ≠ 0 do throwError "second argument must be nonzero"
  let k' : ℕ := k + 1
  let k'' := 2 * k + 1
  let k2 := k'' ^ 2
  let d := (k2 - 1) * (k'' ^ (2 * n - 1))
  let (x, y) := iterateC k2 n (0, 1)
  let x' := x * 2
  let y' := y * k''
  let g := Nat.gcd d y'
  let d' := d / g
  let x'' := (d' * x' + (y' / g) * 2)
  let y'' := d' * y'
  let pf : Expr := Lean.mkApp7 (Lean.mkConst ``log_bounds') (mkNatLit n)
    (mkRawNatLit k) (mkRawNatLit k') (mkNatLit k'') (mkNatLit k2) (mkNatLit d) (mkNatLit g)
  let pf : Expr := mkApp6 pf
    (mkNatLit x) (mkNatLit y) (mkRawNatLit x') (mkRawNatLit y') (mkRawNatLit x'') (mkRawNatLit y'')
  let pf : Expr := mkApp7 pf reflBoolTrue reflBoolTrue reflBoolTrue
    reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue
  return Lean.mkApp5 pf reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue
      (mkApp2
        (Lean.mkConst ``Eq.refl [1])
        (mkApp2 (Lean.mkConst ``Prod [0, 0]) (Lean.mkConst ``Nat) (Lean.mkConst ``Nat))
        (mkApp4 (Lean.mkConst ``Prod.mk [0, 0])
          (Lean.mkConst ``Nat) (Lean.mkConst ``Nat) (mkRawNatLit x) (mkRawNatLit y)))

-- section

set_option trace.profiler true
set_option trace.profiler.useHeartbeats true

-- #exit

def log1 := bound_log% 15 10059
def log2 := bound_log% 24 8876
def log3 := bound_log% 80 6798

#exit

lemma decompose :
    log 2 = 7 * log (16 / 15) + 5 * log (25 / 24) + 3 * log (81 / 80) := by
  have : (2 : ℝ) = (16 / 15) ^ 7 * (25 / 24) ^ 5 * (81 / 80) ^ 3 := by norm_num
  rw [this, log_mul (by simp) (by simp), log_mul (by simp) (by simp),
    log_pow, log_pow, log_pow]
  simp

lemma combine {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ a₃ b₃ c₃ d₃} (x y n x' : ℕ)
    (ha₁ : Nat.blt 0 a₁) (hb₁ : Nat.blt 0 b₁)
    (ha₂ : Nat.blt 0 a₂) (hb₂ : Nat.blt 0 b₂)
    (ha₃ : Nat.blt 0 a₃) (hb₃ : Nat.blt 0 b₃)
    (hx'' : Nat.blt 0 x')
    (hx' : (x'.add y).beq (x.mul (Nat.pow 10 n)))
    (h : (x'.mul (b₁.mul (b₂.mul b₃))).ble <|
      ((Nat.pow 10 n).mul y).mul (
      Nat.add (Nat.mul 7 (a₁.mul (b₂.mul b₃)))
      (Nat.add (Nat.mul 5 (a₂.mul (b₁.mul b₃)))
        (Nat.mul 3 (a₃.mul (b₁.mul b₂))))))
    (h' : (((Nat.pow 10 n).mul y).mul (
      Nat.add (Nat.mul 7 (c₁.mul (d₂.mul d₃)))
      (Nat.add (Nat.mul 5 (c₂.mul (d₁.mul d₃)))
        (Nat.mul 3 (c₃.mul (d₁.mul d₂)))))).ble
      ((((Nat.pow 10 n).mul x).add y).mul (d₁.mul (d₂.mul d₃))))
    (h₁ : OfNat.ofNat a₁ / OfNat.ofNat b₁ ≤ log (16 / 15) ∧
      log (16 / 15) ≤ OfNat.ofNat c₁ / OfNat.ofNat d₁)
    (h₂ : OfNat.ofNat a₂ / OfNat.ofNat b₂ ≤ log (25 / 24) ∧
      log (25 / 24) ≤ OfNat.ofNat c₂ / OfNat.ofNat d₂)
    (h₃ : OfNat.ofNat a₃ / OfNat.ofNat b₃ ≤ log (81 / 80) ∧
      log (81 / 80) ≤ OfNat.ofNat c₃ / OfNat.ofNat d₃) :
    |log 2 - OfNat.ofNat x / OfNat.ofNat y| ≤ (10 ^ OfNat.ofNat n)⁻¹ := by
  replace h₁ : log (16 / 15) ∈ Set.Icc (a₁ / b₁ : ℝ) (c₁ / d₁) := by
    simpa [← Grind.Semiring.ofNat_eq_natCast] using h₁
  replace h₂ : log (25 / 24) ∈ Set.Icc (a₂ / b₂ : ℝ) (c₂ / d₂) := by
    simpa [← Grind.Semiring.ofNat_eq_natCast] using h₂
  replace h₃ : log (81 / 80) ∈ Set.Icc (a₃ / b₃ : ℝ) (c₃ / d₃) := by
    simpa [← Grind.Semiring.ofNat_eq_natCast] using h₃
  suffices |log 2 - x / y| ≤ (10 ^ n)⁻¹ by
    simpa [← Grind.Semiring.ofNat_eq_natCast] using this
  suffices x / y - (10 ^ n)⁻¹ ≤ log 2 ∧ log 2 ≤ x / y + (10 ^ n)⁻¹ by
    rwa [abs_le, le_sub_iff_add_le', sub_le_iff_le_add', ← sub_eq_add_neg]
  have : log 2 = 7 * log (16 / 15) + 5 * log (25 / 24) + 3 * log (81 / 80) := by
    rw [decompose]
  simp only [Nat.blt_eq] at ha₁ hb₁ ha₂ hb₂ ha₃ hb₃ hx''
  simp only [Nat.mul_eq, Nat.pow_eq, Nat.add_eq, Nat.ble_eq, Nat.beq_eq, ← mul_assoc,
    ← add_assoc] at h h' hx'
  rw [this]
  have hy : y ≠ 0 := by
    rintro rfl
    obtain rfl : x' = 0 := by simpa [hb₁.ne', hb₂.ne', hb₃.ne'] using h
    simp at hx''
  refine interval_end
    (add_interval (add_interval
      (mul_interval const_interval h₁ (by simp) (by positivity))
      (mul_interval const_interval h₂ (by simp) (by positivity)))
      (mul_interval const_interval h₃ (by simp) (by positivity))) ?_ ?_
  · field_simp
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rify at hx'
    rw [← hx']
    simp
    norm_cast
    linear_combination h
  · have hd₁ : d₁ ≠ 0 := by
      rintro rfl
      simp only [CharP.cast_eq_zero, div_zero, Set.mem_Icc] at h₁
      exact (log_pos (by norm_num1)).not_ge h₁.2
    have hd₂ : d₂ ≠ 0 := by
      rintro rfl
      simp only [CharP.cast_eq_zero, div_zero, Set.mem_Icc] at h₂
      exact (log_pos (by norm_num1)).not_ge h₂.2
    have hd₃ : d₃ ≠ 0 := by
      rintro rfl
      simp only [CharP.cast_eq_zero, div_zero, Set.mem_Icc] at h₃
      exact (log_pos (by norm_num1)).not_ge h₃.2
    field_simp
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    norm_cast
    linear_combination h'
