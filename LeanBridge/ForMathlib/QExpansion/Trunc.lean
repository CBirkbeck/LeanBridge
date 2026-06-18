import LeanBridge.ForMathlib.QExpansion.DeltaPoC
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Truncated representation of complex power series by rational lists

We define `approxTo N l f`, meaning the complex power series `f` agrees with the rational
list `l` (cast to `ℂ`) on the first `N` coefficients. We then prove that this relation is
preserved by addition, subtraction, scalar multiplication, multiplication, and powers, with
the operations on the list side defined by truncating ring operations.
-/

namespace LeanBridge.QExpansion

open List PowerSeries

/-! ## Definition -/

/-- `approxTo N l f` says the complex power series `f` agrees with the rational coefficient
list `l` on the first `N` coefficients. -/
def approxTo (N : ℕ) (l : List ℚ) (f : PowerSeries ℂ) : Prop :=
  ∀ i, i < N → (PowerSeries.coeff (R := ℂ) i) f = ((l.getD i 0 : ℚ) : ℂ)

/-! ## Helper lemmas about `addPointwise` and `take` -/

@[simp]
lemma getD_addPointwise (l₁ l₂ : List ℚ) (i : ℕ) :
    (l₁.addPointwise l₂).getD i 0 = l₁.getD i 0 + l₂.getD i 0 := by
  induction l₁ generalizing l₂ i with
  | nil => simp [List.addPointwise]
  | cons a as ih =>
    cases l₂ with
    | nil => simp [List.addPointwise]
    | cons b bs =>
      cases i with
      | zero => simp [List.addPointwise, List.getD_cons_zero]
      | succ k => simpa [List.addPointwise, List.getD_cons_succ] using ih bs k

@[simp]
lemma getD_neg_map (l : List ℚ) (i : ℕ) :
    (l.map Neg.neg).getD i 0 = -(l.getD i 0) := by
  induction l generalizing i with
  | nil => simp
  | cons a as ih =>
    cases i with
    | zero => simp
    | succ k => simpa using ih k

@[simp]
lemma getD_mulPointwise (c : ℚ) (l : List ℚ) (i : ℕ) :
    (l.mulPointwise c).getD i 0 = c * l.getD i 0 := by
  induction l generalizing i with
  | nil => simp [List.mulPointwise]
  | cons a as ih =>
    cases i with
    | zero => simp [List.mulPointwise]
    | succ k => simpa [List.mulPointwise] using ih k

lemma getD_take (l : List ℚ) (N i : ℕ) (h : i < N) :
    (l.take N).getD i 0 = l.getD i 0 := by
  rcases lt_or_ge i l.length with hil | hil
  · rw [List.getD_eq_getElem _ _ hil, List.getD_eq_getElem _ _ (by simp [hil, h])]
    simp [List.getElem_take]
  · have h1 : (l.take N).length ≤ i := by
      rw [List.length_take]; exact min_le_of_right_le hil
    rw [List.getD_eq_default _ _ hil, List.getD_eq_default _ _ h1]

/-! ## Closure under operations -/

lemma approxTo_add {N : ℕ} {l₁ l₂ : List ℚ} {f g : PowerSeries ℂ}
    (h₁ : approxTo N l₁ f) (h₂ : approxTo N l₂ g) :
    approxTo N (addTrunc N l₁ l₂) (f + g) := by
  intro i hi
  rw [map_add, h₁ i hi, h₂ i hi, addTrunc, getD_take _ _ _ hi, getD_addPointwise]
  push_cast
  ring

lemma approxTo_neg {N : ℕ} {l : List ℚ} {f : PowerSeries ℂ}
    (h : approxTo N l f) :
    approxTo N (l.map Neg.neg) (-f) := by
  intro i hi
  rw [map_neg, h i hi, getD_neg_map]
  push_cast
  ring

lemma approxTo_sub {N : ℕ} {l₁ l₂ : List ℚ} {f g : PowerSeries ℂ}
    (h₁ : approxTo N l₁ f) (h₂ : approxTo N l₂ g) :
    approxTo N (subTrunc N l₁ l₂) (f - g) := by
  intro i hi
  rw [map_sub, h₁ i hi, h₂ i hi, subTrunc, getD_take _ _ _ hi, getD_addPointwise,
      getD_neg_map]
  push_cast
  ring

lemma approxTo_smul_C {N : ℕ} {l : List ℚ} {f : PowerSeries ℂ} (c : ℚ)
    (h : approxTo N l f) :
    approxTo N (smulTrunc N c l) ((c : ℂ) • f) := by
  intro i hi
  rw [map_smul, h i hi, smulTrunc, getD_take _ _ _ hi, getD_mulPointwise]
  push_cast
  ring

/-- The convolution of two lists, viewed coefficient-wise via `getD`, equals the antidiagonal
sum (in any commutative semiring with decidable equality). -/
lemma getD_convolve (l₁ l₂ : List ℚ) (n : ℕ) :
    (l₁.convolve l₂).getD n 0
      = ∑ p ∈ Finset.antidiagonal n, l₁.getD p.1 0 * l₂.getD p.2 0 := by
  have key : Polynomial.ofList (l₁.convolve l₂)
      = (Polynomial.ofList l₁) * (Polynomial.ofList l₂) := ofList_convolve_eq_mul l₁ l₂
  have hcoeff : (l₁.convolve l₂).getD n 0
      = (Polynomial.ofList (l₁.convolve l₂)).coeff n :=
    (Polynomial.coeff_ofList _ _).symm
  rw [hcoeff, key, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intros p _
  rw [Polynomial.coeff_ofList, Polynomial.coeff_ofList]

lemma approxTo_mul {N : ℕ} {l₁ l₂ : List ℚ} {f g : PowerSeries ℂ}
    (h₁ : approxTo N l₁ f) (h₂ : approxTo N l₂ g) :
    approxTo N (mulTrunc N l₁ l₂) (f * g) := by
  intro n hn
  rw [PowerSeries.coeff_mul, mulTrunc, getD_take _ _ _ hn, getD_convolve]
  push_cast
  apply Finset.sum_congr rfl
  intros p hp
  simp only [Finset.mem_antidiagonal] at hp
  have hp1 : p.1 < N := lt_of_le_of_lt (Nat.le_add_right _ _) (hp ▸ hn)
  have hp2 : p.2 < N := lt_of_le_of_lt (Nat.le_add_left _ _) (hp ▸ hn)
  rw [h₁ p.1 hp1, h₂ p.2 hp2]

lemma approxTo_zero {N : ℕ} : approxTo N [] (0 : PowerSeries ℂ) := by
  intro i _
  simp [List.getD_nil]

lemma approxTo_one {N : ℕ} : approxTo N (oneTrunc N) (1 : PowerSeries ℂ) := by
  intro i hi
  unfold oneTrunc
  rw [PowerSeries.coeff_one]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [List.getElem_map, List.getElem_range]
  by_cases h : i = 0
  · simp [h]
  · simp [h]

lemma approxTo_pow {N : ℕ} {l : List ℚ} {f : PowerSeries ℂ}
    (h : approxTo N l f) (k : ℕ) :
    approxTo N (powTrunc N l k) (f ^ k) := by
  induction k with
  | zero =>
    rw [powTrunc, pow_zero]
    exact approxTo_one
  | succ k ih =>
    rw [powTrunc, pow_succ, mul_comm]
    exact approxTo_mul h ih

end LeanBridge.QExpansion
