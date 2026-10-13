/-
Copyright (c) 2025 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Real.Hom
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Sign.Basic
import Mathlib.Data.List.Destutter
import LeanBridge.ForMathlib.Algebra.Polynomial.PolynomialsAsLists

open Polynomial

/- !

# Sturm's Theorem

In this file, we develop some theory about real closed fields and prove a version of Sturm's theorem to
count the roots of a polynomial in an interval.

## Remark
Note that an alternative definition `IsRealClosed` now exists in Mathlib by
Artie Khovanov, which was developed in parallel to this formalization.
Some of our formalized results, like the proofs leading to `mean_value_theorem`,
are now part of the repository mantained by Artie Khovanov on real closed fields,
for an  eventual PR to Mathlib.

## Main Definitions:
- `IsRealClosedField`: A totally ordered field is a real closed field if it satisfies
  the intermediate value theorem for polynomial functions.
- `signChanges` : The number of sign changes in a sequence.
- `IsSturmSequence` : A predicate on a list of polynomials, stating that it is a sturm sequence.
- `SturmBuilderOfList`: a structure that builds a sturm sequence in a computable way.

## Main Results:
- `mean_value_theorem` : the mean value theorem for polynomial functions in real closed fields.
- `sturm_theorem` : given a sturm sequence starting with `f` and `derivative f`,
  the number of roots of the polynomial in an interval `[a,b]` is given by the difference of
  sign changes in the sequence evaluated at `a` and `b`.
  * We assume that none of the polynomials in the sequence vanish at `a` nor `b`. This is to avoid the
    technical difficulties of working with the sign changes of lists with zeros.
- `sturm_theorem_total` : Sturm's theorem for the interval `(-∞, ∞)`.
- `sturm_theorem_map`: if the polynomial is defined over a subring of a real closed field, then this result allows
  us to perform all of the computations in this subring. This is useful for polynomials over `ℤ` as
  we do not want to compute in `ℝ` where we do not have decidable equality.

## Examples:
- `real_roots1`: the polynomial `X ^ 5 - 3 * X ^ 3 + 9 * X - 8` has `1` real root in `(-∞, ∞)`.
- `real_roots2`: the polynomial `X ^ 8 - X ^ 7 - 3 * X ^ 6 + 3 * X ^ 5 + 3 * X ^ 4 - 6 * X ^ 3 - 2 * X ^ 2 + 3 * X + 1`
    has `4` real root in `(-∞, ∞)`.

## Notes
- The remark in `sturm_theorem` does not represent a big impediment in applications.
  If one wants to prove that the number of roots of `P` in the interval `[a,b]`
  (where `a` and `b` are not roots of `P`) is equal to `n`, and `a` happens to be a root of one of the
  polynomials in the sequence, then one can choose an appropiate
  `ε > 0` and count roots in `[a - ε, b + ε ]`and `[a + ε, b - ε ]`.
- For the proof of Sturm's theorem, we follows a similar path to `John Harrison` proof in HOL.
- For proving `Rolle's theorem` and the `Mean value theorem` we follow a similar strategy as
  `Assia Mahboubi` and `Cyril Cohen's`, Formal proofs in real algebraic geometry.

## Related work:
* Verifying accuracy of polynomial approximations in HOl -- `John Harrison` (1997).
  Sturm's theorem is proven over the real numbers.
* A Formalisation of Sturm’s Theorem -- `Manuel Eberl` (2014)
* It has also been formalized by NASA researchers in Langley (2014)
* `Assia Mahboubi` and `Cyril Cohen` formalized sign changes of pseudo-remainder sequences
 in Coq over real closed fields. Sturm theorem is a corollary of these results.-/



def IsRealClosedField (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] : Prop :=
    ∀ {a b t : F} , ∀ {P : F[X]},
    a ≤ b → t ∈ Set.Ioo (P.eval a) (P.eval b) → ∃ s, s ∈ Set.Ioo a b ∧ P.eval s = t

lemma Real.IsRealClosedField : IsRealClosedField ℝ := by
  rintro a b t P hab h
  let f : ℝ → ℝ := fun x => P.eval x
  exact (Set.mem_image _ _ _).1
    (intermediate_value_Ioo hab (f := f) (Polynomial.continuousOn P ) h)

namespace IsRealClosedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
open Set

lemma polynomial_has_root_of_le_zero_of_pos (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (ha : P.eval a < 0) (hb : 0 < P.eval b ) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  exact hc hab ⟨ha, hb⟩

lemma polynomial_has_root_of_pos_le_zero (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (ha : 0 < P.eval a) (hb : P.eval b < 0 ) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  obtain ⟨s, hs1, hs2⟩ := @hc a b 0 (- P) hab (by simp[ha, hb])
  simp only [eval_neg, neg_eq_zero] at hs2
  exact ⟨s, hs1, hs2 ⟩

lemma intermediate_value_theorem_swap (hc : IsRealClosedField F) {a b t : F} (hab : a ≤ b)
    {P : F[X]} (hmem : t ∈ Set.Ioo (P.eval b) (P.eval a)) : ∃ s, s ∈ Set.Ioo a b ∧ P.eval s = t := by
  obtain ⟨s, hs1, hs2⟩ := @hc a b (-t) (- P) hab (by simp [hmem.1, hmem.2])
  simp at hs2
  exact ⟨s, hs1, hs2⟩

lemma sign_ne_eq_iff_of_ne_zero {a b : SignType} (ha : a ≠ 0) (hb : b ≠ 0) :
  a ≠ b ↔ a * b = - 1 := by
  cases a ;
  cases b ; simp ; simp at ha ; simp at ha
  cases b ; simp at hb ; simp ; simp
  cases b ; simp at hb ; simp ; simp


lemma polynomial_has_root_of_mul_neg (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (habm : (P.eval a) * (P.eval b) < 0) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  rcases lt_trichotomy (P.eval a) 0 with hl1 | hl2 | hl3
  · have : eval b P > 0 := by nlinarith
    exact polynomial_has_root_of_le_zero_of_pos hc hab hl1 this
  · simp[hl2] at habm
  · have : eval b P < 0 := by nlinarith
    exact polynomial_has_root_of_pos_le_zero hc hab hl3 this


lemma polynomial_has_root_of_ne_sign (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (hne : SignType.sign (P.eval a) ≠ SignType.sign (P.eval b)) (hanz : P.eval a ≠ 0)
    (hbnz : P.eval b ≠ 0) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  rw [sign_ne_eq_iff_of_ne_zero (by simp[hanz]) (by simp[hbnz] ), ← sign_mul,
    sign_eq_neg_one_iff] at hne
  exact polynomial_has_root_of_mul_neg hc hab hne


lemma neg_of_ne_zero_of_exists_neg (hc : IsRealClosedField F) {a b m : F} {P : F[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hneg : P.eval m < 0) :
    ∀ x ∈ Ioo a b , P.eval x < 0 := by
  intro x hx
  by_contra! hc'
  rcases le_iff_lt_or_eq.1 hc' with hz1 | hz2
  · rcases le_or_gt m x with hm1 | hm2
    · obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_le_zero_of_pos hc hm1 hneg hz1
      refine hP s ?_ hs2
      simp only [mem_Ioo] at hs1 hx ⊢
      exact ⟨lt_trans hm.1 hs1.1, lt_trans hs1.2 hx.2⟩
    · obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_pos_le_zero hc (le_of_lt hm2) hz1 hneg
      refine hP s ?_ hs2
      simp only [mem_Ioo] at hs1 hx ⊢
      exact ⟨lt_trans hx.1 hs1.1, lt_trans hs1.2 hm.2⟩
  · exact hP x hx hz2.symm

lemma nonpos_of_ne_zero_of_exists_neg (hc : IsRealClosedField F) {a b m : F} {P : F[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hneg : P.eval m < 0) :
    ∀ x ∈ Icc a b , P.eval x ≤ 0 := by
  intro x hmem
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc hmem with ha | hb | hx
  · rw [ha]
    by_contra! hc'
    obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_pos_le_zero hc (le_of_lt hm.1) hc' hneg
    refine hP s ?_ hs2
    simp only [mem_Ioo] at hs1
    exact ⟨hs1.1, lt_trans hs1.2 hm.2⟩
  · rw [hb]
    by_contra! hc'
    obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_le_zero_of_pos hc (le_of_lt hm.2) hneg hc'
    refine hP s ?_ hs2
    simp only [mem_Ioo] at hs1
    exact ⟨lt_trans hm.1 hs1.1, hs1.2⟩
  · exact le_of_lt (neg_of_ne_zero_of_exists_neg hc hP hm hneg x hx)


lemma pos_of_ne_zero_of_exists_pos (hc : IsRealClosedField F) {a b m : F} {P : F[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hpos : P.eval m > 0) :
    ∀ x ∈ Ioo a b , P.eval x > 0 := by
  have := neg_of_ne_zero_of_exists_neg hc (P := - P)
    (by simp only [eval_neg, ne_eq, neg_eq_zero] ; exact hP ) hm (by simp[hpos])
  simp at this ⊢
  exact this

lemma nonneg_of_ne_zero_of_exists_pos (hc : IsRealClosedField F) {a b m : F} {P : F[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hpos : P.eval m > 0) :
    ∀ x ∈ Icc a b , P.eval x ≥ 0 := by
  have := nonpos_of_ne_zero_of_exists_neg hc (P := - P)
    (by simp only [eval_neg, ne_eq, neg_eq_zero] ; exact hP ) hm (by simp[hpos])
  simp at this ⊢
  exact this

lemma constant_sign_of_ne_zero (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (hP : ∀ x ∈ Ioo a b, P.eval x ≠ 0) :
    (∀ x ∈ Ioo a b , P.eval x > 0) ∨ (∀ x ∈ Ioo a b , P.eval x < 0)  := by
  rcases le_iff_lt_or_eq.1 hab with h1 | h2
  · obtain ⟨m, hm⟩ := exists_between  h1
    rcases lt_trichotomy (P.eval m) 0 with hl1 | hl2 | hl3
    · right
      exact neg_of_ne_zero_of_exists_neg hc hP hm hl1
    · exfalso ; exact hP m hm hl2
    · left
      exact pos_of_ne_zero_of_exists_pos hc hP hm hl3
  · simp [h2]

lemma constant_sign_of_ne_zero' (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (hP : ∀ x ∈ Ioo a b, P.eval x ≠ 0) :
    (∀ x ∈ Icc a b , P.eval x ≥ 0) ∨ (∀ x ∈ Icc a b , P.eval x ≤ 0) := by
  rcases le_iff_lt_or_eq.1 hab with h1 | h2
  · obtain ⟨m, hm⟩ := exists_between  h1
    rcases lt_trichotomy (P.eval m) 0 with hl1 | hl2 | hl3
    · right
      exact nonpos_of_ne_zero_of_exists_neg hc hP hm hl1
    · exfalso ; exact hP m hm hl2
    · left
      exact nonneg_of_ne_zero_of_exists_pos hc hP hm hl3
  · simp [h2, LinearOrder.le_total 0 (eval b P)]

/- Weak version of Rolle's theorem for successive roots. -/
lemma rolle_theorem_weak (hc : IsRealClosedField F) {a b : F} (hab : a < b) {P : F[X]}
    (hP : ∀ x ∈ Ioo a b, P.eval x ≠ 0) (hPa : P.eval a = 0) (hPb : P.eval b = 0) :
    ∃ c ∈ Ioo a b , (derivative P).eval c = 0 := by
  have hPnz : P ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := exists_between hab
    specialize hP m hm
    simp [h, eval_zero] at hP
  obtain ⟨Q' , hQ'1, hQ'2⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hPnz a
  have hQnz : Q' ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQ'1
    exact hPnz hQ'1
  obtain ⟨Q , hQ1, hQ2⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q' hQnz b
  rw [hQ1] at hQ'1
  have ham : rootMultiplicity a P ≠ 0 := by
    rw [← pos_iff_ne_zero]
    refine (Polynomial.rootMultiplicity_pos hPnz).2 ?_
    exact hPa
  have hbm : rootMultiplicity b Q' ≠ 0 := by
    rw [← pos_iff_ne_zero]
    refine (Polynomial.rootMultiplicity_pos hQnz).2 ?_
    rw [hQ'1 ] at hPb
    simp[(sub_ne_zero_of_ne (Ne.symm (ne_of_lt hab))), hQnz] at hPb
    rcases hPb with hPb1 | hPb2
    · exact hPb1
    · rw [hQ1]
      simp[hPb2]
  rw [← Nat.succ_pred_eq_of_ne_zero ham, ← Nat.succ_pred_eq_of_ne_zero hbm] at hQ'1
  have hQr : Q.eval a ≠ 0 ∧ Q.eval b ≠ 0 := by
    constructor
    · intro hc
      apply hQ'2
      rw [Polynomial.dvd_iff_isRoot, hQ1]
      simp[hc]
    · rwa [Polynomial.dvd_iff_isRoot] at hQ2
  set Q1 : F[X] := C (rootMultiplicity b Q' : F) * (X - C a) * Q +
      C (rootMultiplicity a P : F) * (X - C b) * Q + (X - C a) * (X - C b) * derivative Q with hQd
  have hderiv : derivative P = ((X - C a) ^ (rootMultiplicity a P).pred) *
    ((X - C b) ^ (rootMultiplicity b Q').pred) * Q1 := by
    nth_rw 1 [hQ'1, hQd, ← mul_assoc, derivative_mul, derivative_mul,
      derivative_pow, derivative_pow, derivative_X_sub_C, derivative_X_sub_C, mul_one, mul_one]
    rw [mul_add, mul_add, add_mul _ _ Q]
    nth_rw 2 [add_comm]
    have : ∀ n : ℕ , (n : F[X]) + 1 = ↑(n + 1) := fun n => by simp only [Nat.cast_add, Nat.cast_one]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · simp [Nat.succ_eq_add_one] ; simp_rw [this, Nat.sub_one_add_one hbm] ; ring
    · simp [Nat.succ_eq_add_one] ; simp_rw [this, Nat.sub_one_add_one ham] ; ring
    · simp [Nat.succ_eq_add_one] ; ring
  have hQ1a : Q1.eval a =  - (rootMultiplicity a P) * (b - a) * (Q.eval a) := by
    rw [hQd] ; simp ; ring
  have hQ1b : Q1.eval b =  (rootMultiplicity b Q') * (b - a) * (Q.eval b) := by
    rw [hQd] ; simp
  have hQIoo : ∀ x ∈ Ioo a b, Q.eval x ≠ 0 := by
    intro x hmem h
    apply hP x hmem
    rw [hQ'1] ; simp[h]
  have hzQ : ∃ c ∈ Ioo a b , Q1.eval c = 0 := by
    apply polynomial_has_root_of_mul_neg hc (le_of_lt hab)
    simp [hQ1a, hQ1b]
    have : ↑(rootMultiplicity a P) * (b - a) * eval a Q * (↑(rootMultiplicity b Q') * (b - a) * eval b Q) =
      ↑(rootMultiplicity a P) * (↑(rootMultiplicity b Q') * (b - a) * (b - a) * ((eval a Q) * (eval b Q))) := by ring
    rw [this]
    refine mul_pos ?_ (mul_pos ((mul_pos ((mul_pos ?_ ?_)) ?_)) ?_)
    · rw [Nat.cast_pos]
      exact Nat.pos_of_ne_zero ham
    · rw [Nat.cast_pos]
      exact Nat.pos_of_ne_zero hbm
    · linarith
    · linarith
    · refine lt_of_le_of_ne ?_ ?_
      · rcases constant_sign_of_ne_zero' hc (le_of_lt hab) hQIoo with hqal | hqag
        · refine mul_nonneg (hqal a (by simp [le_of_lt hab])) (hqal b (by simp [le_of_lt hab]))
        · refine mul_nonneg_of_nonpos_of_nonpos (hqag a (by simp [le_of_lt hab]))
            (hqag b (by simp [le_of_lt hab]))
      · simp[hQr]
  obtain ⟨c, hcI, hc⟩ := hzQ
  use c
  refine ⟨hcI, ?_ ⟩
  simp [hderiv, hc]

lemma rolle_theorem_weak' (hc : IsRealClosedField F) {a b : F} (hab : a < b) {P : F[X]}
    (hPa : P.eval a = 0) (hPb : P.eval b = 0) :
    ∃ c ∈ Ioo a b , ((derivative P).eval c = 0 ∨ P.eval c = 0) := by
  by_contra! hcc
  have hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0 := fun x hx => (hcc x hx).2
  obtain ⟨c, hc1, hc2⟩ := rolle_theorem_weak hc hab hP hPa hPb
  exact (hcc c hc1).1 hc2

open Finset

/-- Based on Assia and Cyril paper-/
lemma rolle_theorem_induction (hc : IsRealClosedField F) (n : ℕ)
    {a b : F} {P : F[X]} (hab : a < b) (hPa : P.eval a = 0) (hPb : P.eval b = 0)
    (hcard : #((Multiset.toFinset P.roots).filter ( fun x => x ∈ Ioo a b)) < n) :
    ∃ c ∈ Ioo a b, (derivative P).eval c = 0 := by
  revert P a b
  induction n with
  | zero => simp only [Set.mem_Ioo, not_lt_zero', IsEmpty.forall_iff, implies_true]
  | succ n hn =>
    intro a b P hab hPa hPb hcard
    obtain ⟨c , hcmem, hcd⟩ := rolle_theorem_weak' hc hab hPa hPb
    rcases hcd with hcd1 | hcd2
    · exact ⟨c, hcmem, hcd1⟩
    · have : P ≠ 0 → filter (fun x ↦ x ∈ Set.Ioo a c) P.roots.toFinset
        ⊂ filter (fun x ↦ x ∈ Set.Ioo a b) P.roots.toFinset := by
        intro hPz
        rw [Finset.ssubset_def, Finset.not_subset]
        constructor
        · intro r hr
          simp at hr ⊢
          refine ⟨hr.1, ⟨hr.2.1, lt_trans hr.2.2 hcmem.2 ⟩ ⟩
        · use c
          simp [hcd2, hPz]
          exact hcmem
      by_cases hPz : P = 0
      · simp [hPz, exists_between hab]
      · obtain ⟨r, hr1, hr2⟩ := hn hcmem.1 hPa hcd2 (by linarith [Finset.card_lt_card (this hPz)])
        refine ⟨r, ⟨hr1.1, lt_trans hr1.2 hcmem.2⟩, hr2  ⟩

/- Rolle's  theorem for polynomials  -/
theorem rolle_theorem (hc : IsRealClosedField F) {a b : F} {P : F[X]} (hab : a < b)
    (hPab : P.eval a = P.eval b) : ∃ c ∈ Ioo a b, (derivative P).eval c = 0 := by
  wlog h : P.eval a = 0
  · have := this hc (P := P - C (P.eval a) ) hab
    simp at this
    simp [this, hPab]
  · rw [h] at hPab
    exact rolle_theorem_induction hc
      ((#((Multiset.toFinset P.roots).filter ( fun x => x ∈ Ioo a b))) + 1)
      hab h hPab.symm (lt_add_one _)

/- Mean value theorem for polynomials -/
theorem mean_value_theorem  (hc : IsRealClosedField F) {a b : F} {P : F[X]} (hab : a < b) :
    ∃ c ∈ Ioo a b , P.eval b - P.eval a = ((derivative P).eval c) * (b - a) := by
  let Q : F[X] :=  (C (P.eval b) - C (P.eval a)) * (X - C a) - (C b - C a) * (P - C (P.eval a))
  have Q_deriv : derivative Q = (C (P.eval b) - C (P.eval a)) - (C b - C a) * (derivative P) := by
    simp[Q]
  have hQa : Q.eval a = 0 := by simp[Q]
  have hQb : Q.eval b = 0 := by simp[Q] ; ring
  obtain ⟨c, hcmem, hc⟩ := rolle_theorem hc hab (Eq.trans hQa hQb.symm)
  use c , hcmem
  rw [Q_deriv] at hc
  simp at hc
  linarith

lemma change_sign_of_unique_root_of_squarefree (hc : IsRealClosedField F) {a b c : F}
    {P : F[X]} (hab : a < b) (hmem : c ∈ Ioo a b) (hr : P.eval c = 0)
    (hur : ∀ x ∈ Icc a b , (P.eval x = 0 → x = c))
    (hd : ∀ x ∈ Icc a b, (derivative P).eval x ≠ 0) : (P.eval a) * (P.eval b) < 0 := by
  by_contra! hcc
  rcases le_iff_eq_or_lt.1 hcc with hz | hpos
  · simp at hz
    rcases hz with ha | hb
    · rw [hur a (Set.left_mem_Icc.2 (le_of_lt hab)) ha] at hmem
      exact Set.left_notMem_Ioo hmem
    · rw [hur b (Set.right_mem_Icc.2 (le_of_lt hab)) hb] at hmem
      exact Set.right_notMem_Ioo hmem
  · rcases mul_pos_iff.1 hpos with hpos1 | hpos2
    · by_cases hleq : eval a P < eval b P
      · rw [← hr] at hpos1
        obtain ⟨s, hsmem, hs⟩  := hc (le_of_lt hmem.2) ⟨hpos1.1, hleq⟩
        obtain ⟨t, htmem, htmem2⟩ := rolle_theorem hc (lt_trans hmem.1 hsmem.1) hs.symm
        refine hd t ?_ htmem2
        exact ⟨le_of_lt htmem.1, le_of_lt (lt_trans htmem.2 hsmem.2) ⟩
      · push Not at hleq
        rcases le_iff_eq_or_lt.1 hleq with hz2 | hpos'
        · obtain ⟨t, htmem, htmem2⟩ := rolle_theorem hc hab hz2.symm
          refine hd t ?_ htmem2
          exact mem_Icc_of_Ioo htmem
        · rw [← hr] at hpos1
          obtain ⟨s, hsmem, hs⟩  := intermediate_value_theorem_swap hc (le_of_lt hmem.1) ⟨hpos1.2, hpos'⟩
          obtain ⟨t, htmem, htmem2⟩ := rolle_theorem hc (lt_trans hsmem.2 hmem.2 ) hs
          refine hd t ?_ htmem2
          exact ⟨le_of_lt (lt_trans hsmem.1 htmem.1), le_of_lt (htmem.2)⟩
    · by_cases hleq : eval a P < eval b P
      · rw [← hr] at hpos2
        obtain ⟨s, hsmem, hs⟩ := hc (le_of_lt hmem.1) ⟨hleq, hpos2.2⟩
        obtain ⟨t, htmem, htmem2⟩ := rolle_theorem hc (lt_trans hsmem.2 hmem.2) hs
        refine hd t ?_ htmem2
        exact ⟨le_of_lt (lt_trans hsmem.1 htmem.1), le_of_lt (htmem.2)⟩
      · push Not at hleq
        rcases le_iff_eq_or_lt.1 hleq with hz2 | hpos'
        · obtain ⟨t, htmem, htmem2⟩ := rolle_theorem hc hab hz2.symm
          refine hd t ?_ htmem2
          exact mem_Icc_of_Ioo htmem
        · rw [← hr] at hpos2
          obtain ⟨s, hsmem, hs⟩  := intermediate_value_theorem_swap hc (le_of_lt hmem.2) ⟨hpos', hpos2.1⟩
          obtain ⟨t, htmem, htmem2⟩ := rolle_theorem hc (lt_trans hmem.1 hsmem.1 ) hs.symm
          refine hd t ?_ htmem2
          exact ⟨le_of_lt htmem.1, le_of_lt (lt_trans htmem.2 hsmem.2) ⟩

lemma sign_derivative_of_opposite_sign_neg (hc : IsRealClosedField F) {a b : F}
    {P : F[X]} (hab : a < b) (hsign : (P.eval a) * (P.eval b) < 0)
    (hapos : 0 < P.eval a ) (hd : ∀ x ∈ Icc a b, (derivative P).eval x ≠ 0) :
    ∀ x ∈ Icc a b, (derivative P).eval x < 0  := by
  intro x hxmem
  refine lt_of_le_of_ne ?_ ?_
  · have : P.eval b < P.eval a := by nlinarith
    obtain ⟨c, hcmem, hcp⟩ := mean_value_theorem hc hab (P := P)
    refine nonpos_of_ne_zero_of_exists_neg hc (fun y hy => hd y (mem_Icc_of_Ioo hy) ) (hcmem) ?_ x hxmem
    nlinarith
  · exact hd x hxmem

lemma sign_derivative_of_opposite_pos (hc : IsRealClosedField F) {a b : F}
    {P : F[X]} (hab : a < b) (hsign : (P.eval a) * (P.eval b) < 0)
    (hapos : P.eval a < 0) (hd : ∀ x ∈ Icc a b, (derivative P).eval x ≠ 0) :
    ∀ x ∈ Icc a b, 0 < (derivative P).eval x   := by
  intro x hxmem
  refine lt_of_le_of_ne ?_ ?_
  · have : P.eval a < P.eval b  := by nlinarith
    obtain ⟨c, hcmem, hcp⟩ := mean_value_theorem hc hab (P := P)
    refine nonneg_of_ne_zero_of_exists_pos hc (fun y hy => hd y (mem_Icc_of_Ioo hy) ) (hcmem) ?_ x hxmem
    nlinarith
  · symm
    exact hd x hxmem

lemma derivative_mul_neg_of_sign_neg_left (hc : IsRealClosedField F) {a b c : F}
    {P : F[X]} (hab : a < b) (hmem : c ∈ Ioo a b) (hr : P.eval c = 0)
    (hur : ∀ x ∈ Icc a b , (P.eval x = 0 → x = c))
    (hd : ∀ x ∈ Icc a b, (derivative P).eval x ≠ 0) :
      (P.eval a) * (derivative P).eval a < 0 := by
  have hnz : P.eval a ≠ 0 := by
    intro heval
    rw [hur a (by simp[le_of_lt hab]) heval] at hmem
    simp at hmem
  have aux := change_sign_of_unique_root_of_squarefree hc hab hmem hr hur hd
  rcases lt_trichotomy (P.eval a) 0 with hn | hz | hpos
  · nlinarith [sign_derivative_of_opposite_pos hc hab aux hn hd a (by simp[le_of_lt hab])]
  · exfalso ; rw [hz] at aux
    contradiction
  · nlinarith [sign_derivative_of_opposite_sign_neg hc hab aux hpos hd a (by simp[le_of_lt hab])]

lemma derivative_mul_neg_of_sign_neg_right (hc : IsRealClosedField F) {a b c : F}
    {P : F[X]} (hab : a < b) (hmem : c ∈ Ioo a b) (hr : P.eval c = 0)
    (hur : ∀ x ∈ Icc a b , (P.eval x = 0 → x = c))
    (hd : ∀ x ∈ Icc a b, (derivative P).eval x ≠ 0) :
      0 < (P.eval b) * (derivative P).eval b := by
  have hnz : P.eval a ≠ 0 := by
    intro heval
    rw [hur a (by simp[le_of_lt hab]) heval] at hmem
    simp at hmem
  have aux := change_sign_of_unique_root_of_squarefree hc hab hmem hr hur hd
  rcases lt_trichotomy (P.eval a) 0 with hn | hz | hpos
  · nlinarith [sign_derivative_of_opposite_pos hc hab aux hn hd b (by simp[le_of_lt hab])]
  · exfalso ; rw [hz] at aux
    contradiction
  · nlinarith [sign_derivative_of_opposite_sign_neg hc hab aux hpos hd b (by simp[le_of_lt hab])]

end IsRealClosedField

section signChanges

section

variable {R : Type*}  [Zero R] [Preorder R] [DecidableLT R] [DecidableEq R]

-- Similar to Coq (residue sequences)
def signChanges' (L : List R) : ℕ :=
  match L  with
  | [] => 0
  | (a :: as) => if SignType.sign a * SignType.sign (as.headD 0) < 0 then 1 + signChanges' as else signChanges' as

def signChanges (L : List R) : ℕ  :=
  signChanges' (List.filter (fun x => if x ≠ 0 then true else false) L)


lemma signChanges_def (L : List R) : signChanges L = signChanges' (List.filter (fun x => if x ≠ 0 then true else false) L) := by
  rfl

lemma signChanges_eq_signChanges' (L : List R) (hz : ∀ x ∈ L, x ≠ 0) : signChanges L = signChanges' L := by
  rw [signChanges_def]
  congr ; simp ; exact hz

end


--set_option trace.profiler true

--#count_heartbeats
--example : SignType.sign (123457738291098765612345773829109876561234577382910987656123457738291098765612345773829109876561234577382910987656 : ℚ)* SignType.sign (-345678998765678912345773829109876561234577382910987656123457738291098765612345773829109876561234577382910987656) < 0 := by decide

-- unseal Rat.mul
-- example : (123457738291098765612345773829109876561234577382910987656123457738291098765612345773829109876561234577382910987656 : ℚ) * (-345678998765678912345773829109876561234577382910987656123457738291098765612345773829109876561234577382910987656) < 0 := by decide



section
variable{R : Type*} [CommRing R] [LinearOrder R]

open SignType

/- The sign changes of a polynomial sequence at `a` is simply the sign changes of the resulting
list when evaluating the polys at `a` -/
def signChangesPolySeq (P : List R[X]) (a : R) : ℕ :=
  signChanges (List.map (fun x => x.eval a) P)

lemma signChangesPolySeq_def (P : List R[X]) (a : R) :
  signChangesPolySeq P a = signChanges (List.map (fun x => x.eval a) P) := rfl

def signChangesInfty (P : List R[X]) : ℕ :=
  signChanges (List.map (fun p => p.leadingCoeff) P)

lemma signChangesInfty_def (P : List R[X]) : signChangesInfty P =
  signChanges (List.map (fun p => p.leadingCoeff) P) := rfl

def signChangesNInfty (P : List R[X]) : ℕ :=
  signChanges (List.map (fun p => (-1) ^ (p.natDegree) * p.leadingCoeff) P)

lemma signChangesNInfty_def (P : List R[X]) : signChangesNInfty P =
    signChanges (List.map (fun p => (-1) ^ (p.natDegree) * p.leadingCoeff) P) := rfl

end

section

variable {R : Type*} [CommRing R]
/-- A list of polynomials is a sturm sequence starting with `p` and `q`
  if it has length at least two, it ends in a non-zero constant polynomial, it has strictly decreasing degree
  and `Pᵢ₊₁ ∣ (e₁ * Pᵢ + fᵢ * Pᵢ₊₂)` with `eᵢ` and `f₁` strictly positive numbers. -/
structure IsSturmSequence [LinearOrder R] (P : List R[X]) (p q : R[X])  where
  hlen : 2 ≤ P.length
  h0 : P[0] = p
  h1 : P[1] = q
  hc : ∃ c : R, c ≠ 0 ∧ P.getLastD 0 = C c
  hmono : ∀ i, ∀ h : i + 1 < P.length , P[i + 1].natDegree < P[i].natDegree
  hrem : ∀ i, ∀ h2 : i + 2 < P.length ,
    (∃ e f : R, ∃ Q : R[X], 0 < e ∧ 0 < f ∧ C e * P[i] = Q * P[i + 1] - C f * P[i + 2] )


lemma sturm_sequence_ne_nil [LinearOrder R] {P : List R[X]} {p q : R[X]}
  (hs : IsSturmSequence P p q) : P ≠ [] := by
  have := hs.hlen
  intro h
  simp only [h, List.length_nil, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero] at this

lemma getLastD_eq_getLast_of_ne_nil {α : Type*} {a : α} {l : List α} (h : l ≠ []) :
  l.getLastD a = l.getLast h := by
  match l with
  | [] => contradiction
  | (b :: bs) =>
    match bs with
    | [] => simp
    | (c :: cs) =>
    rw [List.getLast_eq_getLastD, List.getLastD_cons]

lemma zero_not_member_of_mono {P : List R[X]}
  (hlen : 2 ≤ P.length)
  (hc : ∃ c : R, c ≠ 0 ∧ P.getLastD 0 = C c)
  (hmono : ∀ i, ∀ h : i + 1 < P.length , P[i + 1].natDegree < P[i].natDegree) : ¬ 0 ∈ P := by
  intro h
  rw [List.mem_iff_getElem] at h
  obtain ⟨i, hile, hi⟩ := h
  by_cases hieq : i = P.length - 1
  · simp_rw [hieq] at hi
    have hsl :=hlen
    obtain ⟨c, hcz, hzl⟩ := hc
    rw [← List.getLast_eq_getElem (fun  h => by simp [h] at hsl)] at hi
    rw [getLastD_eq_getLast_of_ne_nil (by grind), hi, Eq.comm,
      Polynomial.C_eq_zero] at hzl
    exact hcz hzl
  · have := hmono i (by omega)
    rw [hi] at this
    simp at this


variable [LinearOrder R]

/-- The zero polynomial is not in a sturm sequence. -/
lemma zero_not_member {P : List R[X]} {p q : R[X]}
    (hs : IsSturmSequence P p q) : ¬ 0 ∈ P := by
  intro h
  rw [List.mem_iff_getElem] at h
  obtain ⟨i, hile, hi⟩ := h
  by_cases hieq : i = P.length - 1
  · simp_rw [hieq] at hi
    have hsl := hs.hlen
    obtain ⟨c, hcz, hzl⟩ := hs.hc
    rw [← List.getLast_eq_getElem (fun  h => by simp [h] at hsl)] at hi
    rw [getLastD_eq_getLast_of_ne_nil (sturm_sequence_ne_nil hs), hi, Eq.comm,
      Polynomial.C_eq_zero] at hzl
    exact hcz hzl
  · have := hs.hmono i (by omega)
    rw [hi] at this
    simp at this

lemma zero_not_member' {P : List R[X]} {p q : R[X]}
  (hs : IsSturmSequence P p q) (i : ℕ) (hi : i < P.length) : P[i] ≠ 0 := by
  intro h
  have : P[i] ∈ P := List.getElem_mem hi
  exact zero_not_member hs (h ▸ this)


lemma p_ne_zero {P : List R[X]} {p q : R[X]}
    (hs : IsSturmSequence P p q) : p ≠ 0 := by
  rw [← hs.h0]
  have hPl := hs.hlen
  have : P[0] ∈ P := by simp
  intro h
  rw [h] at this
  exact zero_not_member hs this

lemma q_ne_zero {P : List R[X]} {p q : R[X]}
    (hs : IsSturmSequence P p q) : q ≠ 0 := by
  rw [← hs.h1]
  have hPl := hs.hlen
  have : P[1] ∈ P := by simp
  intro h
  rw [h] at this
  exact zero_not_member hs this

 lemma IsSturmSequence_map {S : Type*} [CommRing S] [LinearOrder S]  {P : List R[X]}
    {p q : R[X]} (h : IsSturmSequence P p q) (f : R →+* S) (hmono : StrictMono f) :
    IsSturmSequence (List.map (Polynomial.map f) P) (map f p) (map f q) where
  hlen := by simp[h.hlen]
  h0 := by simp [h.h0]
  h1 := by simp only [List.getElem_map]  ; simp_rw [← h.h1]
  hc := by
    obtain ⟨c, hc1, hc2⟩ := h.hc
    use f c
    constructor
    · refine (map_ne_zero_iff f (StrictMono.injective hmono)).mpr hc1
    · rw [getLastD_eq_getLast_of_ne_nil (by simp ; exact sturm_sequence_ne_nil h)]
      simp
      rw[← getLastD_eq_getLast_of_ne_nil (a := 0) (sturm_sequence_ne_nil h), hc2, map_C]
  hmono := by
    intro i hi
    simp at hi
    simp only [List.getElem_map, Polynomial.natDegree_map_eq_of_injective (StrictMono.injective hmono)]
    exact h.hmono i hi
  hrem := by
    intro i hi
    simp at hi
    obtain ⟨e, ft, Q, hepos, hfpos, heq⟩ := h.hrem i hi
    use f e, f ft , map f Q
    refine ⟨?_, ?_, ?_ ⟩
    · convert StrictMono.imp hmono hepos
      rw [map_zero]
    · convert StrictMono.imp hmono hfpos
      rw [map_zero]
    · simp
      rw[← map_C, ← Polynomial.map_mul, heq]
      simp


/-- A sturm sequence evaluated at any element `a` cannot have two consecutive zeros. -/
lemma no_consecutive_zero1 [IsStrictOrderedRing R] (P : List R[X]) (p q : R[X])
    (hs : IsSturmSequence P p q) (a : R) (i : ℕ)
    (hlen : i + 1 < P.length) (hz : P[i + 1].eval a = 0) : P[i].eval a ≠ 0 := by
  revert i
  by_contra! hc
  obtain ⟨i, hle, heval1, heval2⟩ := hc
  have hin : ∀ j, ∀ hj : i + j < P.length , P[i + j].eval a = 0 := by
    intro j hj
    induction j using Nat.strong_induction_on with
    | h j hjin =>
      match j with
      | 0 => exact heval2
      | 1 => exact heval1
      | j + 1 + 1 =>
      have := hjin j (by omega) (by omega)
      have :=  hjin (j + 1) (by omega) (by omega)
      obtain ⟨e, f, Q, hepos, hfpos, hef⟩ := hs.hrem (i + j) (by omega)
      apply_fun (fun (x : R[X]) => x.eval a) at hef
      simp at hef
      simp_rw [ hjin j (by omega) (by omega), add_assoc, hjin (j + 1) (by omega) (by omega)  ] at hef
      simp[Ne.symm (ne_of_lt hfpos)] at hef
      exact hef
  obtain ⟨c, hcz, hzl⟩ := hs.hc
  rw [getLastD_eq_getLast_of_ne_nil (sturm_sequence_ne_nil hs), List.getLast_eq_getElem] at hzl
  have aux := hin (P.length- 1 - i) (by omega)
  have : i + (P.length - 1 - i) = P.length - 1 := by omega
  simp_rw [this, hzl] at aux
  simp only [eval_C] at aux
  exact hcz aux


lemma sturm_sequence_cons (P : List R[X]) (p q : R[X]) (a : R[X]) (hPl : 2 ≤ P.length)
    (hs : IsSturmSequence (a :: P) p q) : IsSturmSequence P q P[1] where
  hlen := hPl
  h0 := by rw [← List.getElem_cons_succ a ] ; exact hs.h1
  h1 := rfl
  hc := by
    have : P ≠ [] := fun h => by rw [h] at hPl ; simp at hPl
    obtain ⟨c, neq, hcl⟩  := hs.hc
    rw [List.getLastD_cons, getLastD_eq_getLast_of_ne_nil this] at hcl
    simp_rw [getLastD_eq_getLast_of_ne_nil this]
    exact ⟨c, neq, hcl⟩
  hmono := by
    intro i h
    have := hs.hmono (i + 1) (by simp ; omega)
    simp at this
    exact this
  hrem := by
    intro i h
    obtain ⟨e, f, Q, hepos, hfpos, heq⟩  := hs.hrem (i + 1) (by simp ; omega)
    simp at heq
    exact ⟨e, f, Q, hepos, hfpos, heq⟩



end

open SignType

variable {R : Type*}

@[simp]
lemma signChanges_nil [Zero R] [Preorder R] [DecidableLT R]  [DecidableEq R]
  : signChanges (R := R) [] = 0 := rfl


@[simp]
lemma signChanges_single' [Zero R] [Preorder R] [DecidableLT R]  (a : R) : signChanges' [a] = 0 := by
  simp[signChanges']

@[simp]
lemma signChanges_single [Zero R] [Preorder R] [DecidableLT R] [DecidableEq R] (a : R)
  : signChanges [a] = 0 := by
  by_cases ha : a ≠ 0
  · simp[signChanges, ha]
  · push Not at ha
    simp [signChanges, signChanges', ha]


lemma signChanges_zero_head [Zero R] [Preorder R] [DecidableLT R] [DecidableEq R]
  (as : List R)  : signChanges (0 :: as) = signChanges as := by
  unfold signChanges
  simp

lemma signChanges_zero_head' [Zero R] [Preorder R] [DecidableLT R] (as : List R) :
  signChanges' (0 :: as) = signChanges' as := by
  simp_rw [signChanges', sign_zero, zero_mul]
  rfl

lemma signChanges_length_two  [DecidableEq R] [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
   (a b : R) (hab : a * b < 0) : signChanges [a, b] = 1 := by
  have : a ≠ 0 ∧ b ≠ 0 := by
    by_contra! hc
    by_cases haz : a = 0
    · simp [haz] at hab
    · simp [hc haz] at hab
  rw [signChanges_eq_signChanges']
  simp [signChanges']
  simp [← sign_mul, hab]
  simp[this]

lemma signChanges_cons_eq_add' [Zero R] [Preorder R] [DecidableLT R] (a b : R) (as : List R) :
  signChanges' (a :: b :: as) = signChanges' [a, b] + signChanges' (b :: as) := by
  by_cases hc : sign a * sign b = -1
  · simp [signChanges', hc]
  · simp [signChanges', hc]

lemma signChanges_cons_eq_add [Zero R] [Preorder R] [DecidableLT R] [DecidableEq R]
  (a b : R) (as : List R) (hb : b ≠ 0) :
  signChanges (a :: b :: as) = signChanges [a, b] + signChanges (b :: as) := by
  have aux : ∀ x y : R, ∀ L : List R,  x :: y :: L = [x, y] ++ L := by simp
  by_cases ha : a ≠ 0
  · have aux2 : (List.filter (fun x ↦ if x ≠ 0 then true else false) [a, b]) = [a, b] := by
      simp[ha, hb]
    unfold signChanges
    rw [aux, List.filter_append, aux2, ← aux, signChanges_cons_eq_add']
    congr ; simp [hb]
  · push Not at ha
    rw [ha]
    simp[signChanges_zero_head, signChanges_single]


lemma signChanges_modify_zero [Zero R] [Preorder R] [DecidableLT R] [DecidableEq R]
  (a : R) (bs : List R) :
  signChanges (a :: 0 :: bs) = signChanges (a :: bs) := by
  by_cases ha : a = 0
  · rw [ha, signChanges_zero_head]
  · have aux : (List.filter (fun x => if x ≠ 0 then true else false)) (a :: 0 :: bs) =
      a :: (List.filter (fun x => if x ≠ 0 then true else false) bs) := by
      simp only [ne_eq, ite_not, Bool.if_true_right, Bool.or_false, ha, decide_false,
        Bool.not_false, List.filter_cons_of_pos, decide_true, Bool.not_true, Bool.false_eq_true,
        not_false_eq_true, List.filter_cons_of_neg]
    simp_rw [signChanges, aux]
    simp[ha]

lemma signChanges_cons [Zero R] [Preorder R] [DecidableLT R] [DecidableEq R]
  {a : R} {as : List R} (ha : a ≠ 0) (hh : as.headD 0 ≠ 0) :
  signChanges (a :: as) = if sign a * sign (as.headD 0) < 0 then 1 + signChanges as else signChanges as := by
  have aux : (List.filter (fun x => if x ≠ 0 then true else false)) (a :: as) =
      a :: (List.filter (fun x => if x ≠ 0 then true else false) as) := by
    simp[ha]
  have aux2 : (List.filter (fun x => if x ≠ 0 then true else false) as).headD 0 = as.headD 0 := by
    match as with
    | [] => simp
    | (b :: bs) =>
    simp at hh
    simp[hh]
  unfold signChanges
  rw [aux]
  nth_rw 1 [signChanges']
  simp_rw [aux2]

lemma signChanges_map' {S : Type*} [Zero R] [Preorder R] [DecidableLT R] [DecidableEq R]
  [Zero S] [Preorder S] [DecidableLT S] [DecidableEq S] (f : R → S)
  (hmono1 : ∀ a , 0 < a ↔ 0 < f a ) (hmono2 : ∀ a , a < 0 ↔ f a < 0 ) (L : List R) :
  signChanges' L = signChanges' (L.map f) := by
  have aux : ∀ x, sign (f x) = sign x := by
    intro x
    simp_rw [sign_apply, hmono1, hmono2]
  induction L with
  | nil => rfl
  | cons a as hi =>
    match as with
    | [] => simp [signChanges']
    | (b :: bs) =>
    simp
    by_cases ha : sign a * sign b = -1
    · have hac := ha
      have ha : sign (f a) * sign (f b) = -1 := by
         rw [aux a, aux b]
         exact ha
      unfold signChanges'
      simp [ha, hac]
      simp[hi]
    · have hac := ha
      have ha : ¬ sign (f a) * sign (f b) = -1 := by
        rw [aux a, aux b]
        exact ha
      unfold signChanges'
      simp [ha, hac]
      simp[hi]

lemma signChanges_map {S : Type*} [Zero R] [LinearOrder R] [DecidableLT R] [DecidableEq R]
  [Zero S] [LinearOrder S] [DecidableLT S] [DecidableEq S] (f : R → S)
  (hmono1 : ∀ a , 0 < a ↔ 0 < f a ) (hmono2 : ∀ a , a < 0 ↔ f a < 0 )
  (L : List R) :
  signChanges L = signChanges (L.map f) := by
  have : ∀ x , f x = 0 ↔ x = 0 := by
    intro x
    constructor
    · intro hx
      rcases lt_trichotomy x 0 with h1 | h2 | h3
      · have := (hmono2 x).1 h1 ; simp [hx] at this
      · exact h2
      · have := (hmono1 x).1 h3 ; simp [hx] at this
    · rintro rfl
      rcases lt_trichotomy (f 0) 0 with h1 | h2 | h3
      · have := (hmono2 0).2 h1
        simp at this
      · exact h2
      · have := (hmono1 0).2 h3
        simp at this
  unfold signChanges
  rw [List.filter_map]
  have : (List.filter ((fun x ↦ if x ≠ 0 then true else false) ∘ f) L) =
    List.filter (fun x ↦ if x ≠ 0 then true else false) L := by
    apply List.filter_congr
    intro x hL
    simp[this x]
  rw [this]
  apply signChanges_map' f hmono1 hmono2



lemma signChanges_eq_map_sign_int [Zero R] [LinearOrder R] [DecidableLT R] [DecidableEq R]
  (L : List R) : signChanges L = signChanges (L.map (fun x ↦ sign x)) := by
  apply signChanges_map _ ?_ ?_ _
  · intro a
    rw [← sign_eq_one_iff]
    constructor
    · intro h ; simp [h]
    · cases sign a  <;> simp
  · intro a
    rw [← sign_eq_neg_one_iff]
    constructor
    · intro h ; simp [h]
    · cases sign a  <;> simp

lemma signChanges_eq_map_sign_int' [Zero R] [LinearOrder R] [DecidableLT R] [DecidableEq R]
  (L : List R) : signChanges' L = signChanges' (L.map (fun x ↦ sign x)) := by
  apply signChanges_map' _ ?_ ?_ _
  · intro a
    rw [← sign_eq_one_iff]
    constructor
    · intro h ; simp [h]
    · cases sign a  <;> simp
  · intro a
    rw [← sign_eq_neg_one_iff]
    constructor
    · intro h ; simp [h]
    · cases sign a  <;> simp

lemma signChanges_congr [Zero R] [LinearOrder R] [DecidableLT R] [DecidableEq R]
  (L₁ L₂ : List R) (hlen : L₁.length = L₂.length)
  (hi : ∀ i, ∀ hi : i < L₁.length, sign (L₁[i]) = sign (L₂[i]) ) :
  signChanges L₁ = signChanges L₂ := by
  refine Eq.trans (b := signChanges (L₁.map (fun x ↦ sign x))) ?_ ?_
  · exact signChanges_eq_map_sign_int L₁
  · rw [signChanges_eq_map_sign_int L₂]
    congr 1
    refine List.ext_get ?_ ?_
    · simp[hlen]
    · intro i hi1 hi2
      simp at hi1 hi2 ⊢
      rw [hi]

lemma signChanges_congr' [Zero R] [LinearOrder R] [DecidableLT R] [DecidableEq R]
  (L₁ L₂ : List R) (hlen : L₁.length = L₂.length)
  (hi : ∀ i, ∀ hi : i < L₁.length, sign (L₁[i]) = sign (L₂[i]) ) :
  signChanges' L₁ = signChanges' L₂ := by
  refine Eq.trans (b := signChanges' (L₁.map (fun x ↦ sign x))) ?_ ?_
  · exact signChanges_eq_map_sign_int' L₁
  · rw [signChanges_eq_map_sign_int' L₂]
    congr 1
    refine List.ext_get ?_ ?_
    · simp[hlen]
    · intro i hi1 hi2
      simp at hi1 hi2 ⊢
      rw [hi]

lemma signChangesPolySeq_map {R S : Type*} [CommRing R] [LinearOrder R] [CommRing S] [LinearOrder S]
  (f : R →+* S) (hmono : StrictMono f) (P : List R[X]) (a : R) :
  signChangesPolySeq P a = signChangesPolySeq (List.map (map f) P) (f a) := by
  simp [signChangesPolySeq]
  rw [signChanges_map f]
  apply signChanges_congr
  · intro i hi
    simp
  · simp
  · rw [← map_zero f]
    exact fun a ↦ Iff.symm (StrictMono.lt_iff_lt hmono)
  · rw [← map_zero f]
    exact fun a ↦ Iff.symm (StrictMono.lt_iff_lt hmono)

lemma signChangesInfty_map {R S : Type*} [CommRing R] [LinearOrder R] [CommRing S] [LinearOrder S]
  (f : R →+* S) (hmono : StrictMono f) (P : List R[X]) :
  signChangesInfty P =  signChangesInfty (List.map (map f) P) := by
  simp [signChangesInfty]
  rw [signChanges_map f]
  apply signChanges_congr
  · intro i hi
    simp
    rw [Polynomial.leadingCoeff_map_of_injective (StrictMono.injective hmono)]
  · simp
  · rw [← map_zero f]
    exact fun a ↦ Iff.symm (StrictMono.lt_iff_lt hmono)
  · rw [← map_zero f]
    exact fun a ↦ Iff.symm (StrictMono.lt_iff_lt hmono)

lemma signChangesNInfty_map {R S : Type*} [CommRing R] [LinearOrder R] [CommRing S] [LinearOrder S]
  (f : R →+* S) (hmono : StrictMono f) (P : List R[X]) :
  signChangesNInfty P =  signChangesNInfty (List.map (map f) P) := by
  simp [signChangesNInfty]
  rw [signChanges_map f]
  apply signChanges_congr
  · intro i hi
    simp only [List.map_map, List.getElem_map, Function.comp_apply, map_mul, map_pow, map_neg,
      map_one]
    rw [Polynomial.natDegree_map_eq_of_injective (StrictMono.injective hmono),
       Polynomial.leadingCoeff_map_of_injective (StrictMono.injective hmono)]
  · simp
  · rw [← map_zero f]
    exact fun a ↦ Iff.symm (StrictMono.lt_iff_lt hmono)
  · rw [← map_zero f]
    exact fun a ↦ Iff.symm (StrictMono.lt_iff_lt hmono)

lemma sign_changes_add [Zero R] [LinearOrder R] [DecidableLT R] (as bs : List R) (b : R) :
  signChanges' (as ++ (b :: bs) ) = signChanges' (as ++ [b]) + signChanges' (b :: bs) := by
  induction as with
  | nil => simp[signChanges']
  | cons c cs hi =>
   match cs with
    | [] =>
    simp [signChanges_cons_eq_add' c b bs]
    | (d :: ds) =>
    by_cases hc : sign c * sign d = -1
    · conv => left ; unfold signChanges' ; simp[hc]
      conv =>  right ; left ; unfold signChanges' ; simp[hc]
      rw [add_assoc, add_right_inj]
      simp at hi
      exact hi
    · conv => left ; unfold signChanges' ; simp[hc]
      conv =>  right ; left ; unfold signChanges' ; simp[hc]
      simp at hi
      exact hi

lemma sign_changes_add_triple [Zero R] [LinearOrder R] [DecidableLT R]  (a b c : R) (as : List R) :
  signChanges' (a :: b :: c :: as) = signChanges' [a, b, c] + signChanges' (c :: as) := by
  exact sign_changes_add [a, b] as c


lemma List.getElem_cons_pred {α : Type* } (a : α) (as : List α) (i : ℕ) (h : i  < (a :: as).length)
  (hi' : i - 1 < as.length) (hi : i ≠ 0) : (a :: as)[i] = as[i - 1] := by
  match i with
  | 0 => contradiction
  | i + 1 => simp

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

lemma signChanges_of_mul_neg [DecidableEq R] {a b c : R}
    (ha : a * c < 0) : signChanges [a, b, c] = 1 := by
    rcases lt_trichotomy b 0 with hb1 | hb2 | hb3
    swap
    · rw [hb2, signChanges_modify_zero, signChanges_length_two _ _ ha]
    · rw [mul_neg_iff] at ha
      rcases ha with hapos | haneg
      · rw [signChanges_eq_signChanges']
        unfold signChanges'
        simp [signChanges', hapos.1, hb1, hapos.2]
        aesop
      · rw [signChanges_eq_signChanges']
        unfold signChanges'
        simp [signChanges', haneg.1, hb1, haneg.2]
        aesop
    · rw [mul_neg_iff] at ha
      rcases ha with hapos | haneg
      · rw [signChanges_eq_signChanges']
        unfold signChanges'
        simp [signChanges', hapos.1, hb3, hapos.2]
        simp ; aesop
      · rw [signChanges_eq_signChanges']
        unfold signChanges'
        simp [signChanges', haneg.1, hb3, haneg.2]
        aesop

lemma aux_induction_three_base (a1 a2 a3 b1 b2 b3 : R)
    (hin : sign a1 = sign b1) (hlast : sign a3 = sign b3)
    (hi : sign a2 ≠ sign b2 → a1 * a3 < 0 ∧ sign a1 = sign b1 ∧ sign a3 = sign b3) :
  signChanges [a1, a2, a3] = signChanges [b1, b2, b3] := by
  by_cases heq : sign a2 ≠ sign b2
  · have := (hi heq)
    have aux : b1 * b3 < 0 := by
      rw [← sign_eq_neg_one_iff, sign_mul, ← this.2.1, ← this.2.2, ← sign_mul ]
      simp[this.1]
    rw [signChanges_of_mul_neg this.1, signChanges_of_mul_neg aux]
  · push Not at heq
    apply signChanges_congr
    · intro i hii
      simp at hii
      interval_cases i
      · exact hin
      · exact heq
      · exact hlast
    · rfl

lemma List.three_le_length_iff {α : Type*} {l : List α} :  3 ≤ l.length ↔ ∃ (a b c : α), ∃ (as : List α) ,
  l = (a :: b :: c :: as) := by
  constructor
  · intro hlen
    match l with
    | [] => simp at hlen
    | [a] => simp at hlen
    | [a, b] => simp at hlen
    | (a :: b :: c :: as) =>
    use a , b, c, as
  · rintro ⟨a, b, c, as, has⟩
    simp [has]


-- If I just case match, the proof is too slow.
lemma aux_induction_list_opposite_sign {n : ℕ}(L₁ L₂ : List R)
  (hzL1 : ∀ x ∈ L₁, x ≠ 0) (hzL2 : ∀ x ∈ L₂, x ≠ 0)
  (hlenn : L₁.length = n)
  (hlen : L₁.length = L₂.length) (hlast : sign (L₁.getLastD 0) = sign (L₂.getLastD 0))
  (hi : ∀ i , ∀ hi : i + 1 < L₁.length , sign (L₁[i]) ≠ sign (L₂[i]) →
    (1 ≤ i ∧ L₁[i - 1] * L₁[i + 1] < 0 ∧ sign (L₁[i - 1]) = sign (L₂[i - 1]) ∧ sign (L₁[i + 1]) = sign (L₂[i + 1]))) :
    signChanges L₁ = signChanges L₂ := by
  rw [signChanges_eq_signChanges' _ hzL2 , signChanges_eq_signChanges' _ hzL1]
  revert L₁ L₂
  induction n using Nat.strong_induction_on with
  | h n hn =>
    by_cases hnz : n < 1
    · simp at hnz
      intro L₁ L₂ hzL1 hzL2 hlenn hlen hlast hi
      rw [hnz] at hlenn
      rw [hlenn] at hlen
      rw [List.length_eq_zero_iff.1 hlenn, List.length_eq_zero_iff.1 hlen.symm]
    · intro L₁ L₂ hzL1 hzL2 hlenn hlen hlast hi
      have hszero : sign (L₁[0]) = sign (L₂[0]) := by
        rcases lt_trichotomy L₁.length 1 with hl0 | hl1 | hl2
        · linarith
        · rw [hl1, Eq.comm] at hlen
          rw [List.length_eq_one_iff] at hlen hl1
          obtain ⟨a, ha⟩ := hl1
          obtain ⟨b, hb⟩ := hlen
          simp [ha, hb] at hlast ⊢
          exact hlast
        · by_contra hcc
          linarith [(hi 0 (by linarith) hcc).1]
      by_cases ht : 3 ≤ n
      · obtain ⟨a1, a2,a3, as, has ⟩:= List.three_le_length_iff.1 (le_of_le_of_eq ht hlenn.symm)
        obtain ⟨b1, b2,b3, bs, hbs ⟩:= List.three_le_length_iff.1 (le_of_le_of_eq ht (Eq.trans hlenn.symm hlen))
        simp_rw [has] at hlenn hlen hlast hi hszero hzL1 ⊢
        simp_rw [hbs] at hlenn hlen hlast hi hszero hzL2 ⊢
        by_cases han : as = []
        · have hbn : bs = [] := by rw [han] at hlen ; simp at hlen ; exact hlen
          simp_rw [han, hbn] at hi hlast ⊢
          simp at hlast
          rw [← signChanges_eq_signChanges', ← signChanges_eq_signChanges']
          apply aux_induction_three_base
          · simp at hszero ; exact hszero
          · exact hlast
          · have := hi 1 (by simp)
            simp at this ; exact this
          · simp[hzL2]
          · simp[hzL1]
        · by_cases hseq : sign a3 = sign b3
          · rw [sign_changes_add_triple, sign_changes_add_triple b1]
            rw [hn (n - 2) (by omega) (a3 :: as) (b3 :: bs) ?_ ?_ ?_ ]
            · congr 1
              rw [← signChanges_eq_signChanges', ← signChanges_eq_signChanges']
              apply aux_induction_three_base
              · exact hszero
              · exact hseq
              · intro hneq
                have := hi 1 (by simp) hneq
                simp at this
                exact this
              simp [hzL2] ; simp [hzL1]
            · simp at hlen ; simp [hlen]
            · exact hlast
            · intro i hii hns
              have higt : 1 ≤ i := by
                by_contra! hcc
                simp [Nat.lt_one_iff.1 hcc, hseq] at hns
              constructor
              · exact higt
              · specialize hi (i + 2) (by simp at hii ⊢ ; exact hii) hns
                simp at hi ; simp
                rw [List.getElem_cons_pred, List.getElem_cons_pred b2] at hi
                exact hi ; exact Nat.ne_zero_of_lt higt ;  exact Nat.ne_zero_of_lt higt
            · simp at hzL1
              simp [hzL1] ; exact hzL1.2.2.2
            · simp at hzL2 ; simp [hzL2] ; exact hzL2.2.2.2
            · simp at hlenn ; simp only [List.length_cons] ; omega
          · have has2 : sign (a2) = sign (b2) := by
              have := hi 2 (by simp ; exact List.length_pos_iff.mpr han) hseq
              simp at this
              rw[this.2.1]
            rw [signChanges_cons_eq_add', signChanges_cons_eq_add' b1]
            rw [hn (n - 1) (by omega) (a2 :: a3 :: as) (b2 :: b3 :: bs) ?_ ?_ ?_ ]
            · congr 1
              rw [signChanges_congr']
              · rfl
              · intro i hii ; simp at hii
                interval_cases i
                exact hszero ; exact has2
            · simp at hlen ⊢ ; exact hlen
            · simp at hlast ⊢ ; exact hlast
            · intro i hii hns
              have higt : 1 ≤ i := by
                by_contra! hcc
                simp [Nat.lt_one_iff.1 hcc] at hns
                exact hns has2
              constructor
              · exact higt
              · specialize hi (i + 1) (by simp at hii ⊢ ; exact hii) hns
                simp at hi ; simp only [List.getElem_cons_succ]
                rw [List.getElem_cons_pred, List.getElem_cons_pred b1] at hi
                exact hi ; exact Nat.ne_zero_of_lt higt ; exact Nat.ne_zero_of_lt higt
            · simp at hzL1 ; simp [hzL1] ; exact hzL1.2.2.2
            · simp at hzL2 ; simp [hzL2] ; exact hzL2.2.2.2
            · simp at hlenn ; simp ; omega
      · push Not at ht hnz
        interval_cases n
        · obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hlenn
          obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 (Eq.trans hlen.symm hlenn)
          rw [ha, hb, signChanges_single', signChanges_single']
        · obtain ⟨a1, a2, ha⟩ := List.length_eq_two.1 hlenn
          obtain ⟨b1, b2, hb⟩ := List.length_eq_two.1 (Eq.trans hlen.symm hlenn)
          simp_rw [ha, hb] at hszero hlast hzL1 hzL2 ⊢
          rw [signChanges_congr']
          · rfl
          · intro i hii
            simp at hii
            interval_cases i
            exact hszero
            exact hlast


lemma signChanges_eq_of_lists_opposite_sign (L₁ L₂ : List R)
  (hzL1 : ∀ x ∈ L₁, x ≠ 0) (hzL2 : ∀ x ∈ L₂, x ≠ 0)
  (hlen : L₁.length = L₂.length) (hlast : sign (L₁.getLastD 0) = sign (L₂.getLastD 0))
  (hi : ∀ i , ∀ hi : i + 1 < L₁.length , sign (L₁[i]) ≠ sign (L₂[i]) →
    (1 ≤ i ∧ L₁[i - 1] * L₁[i + 1] < 0 ∧ sign (L₁[i - 1]) = sign (L₂[i - 1]) ∧ sign (L₁[i + 1]) = sign (L₂[i + 1]))) :
    signChanges L₁ = signChanges L₂ := by
  exact aux_induction_list_opposite_sign L₁ L₂ hzL1 hzL2 rfl hlen hlast hi


variable (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]

open Set IsRealClosedField

lemma polynomial_change_sign_aux (hc : IsRealClosedField F) {a b e f : F} (P0 P1 P2 Q : F[X])
  (hab : a < b) (hpose : 0 < e ) (hposf : 0 < f) (heq : C e * P0 = Q * P1 - C f * P2)
  (hz0 : ∀ x ∈ Icc a b , P0.eval x ≠ 0) (hz2 : ∀ x ∈ Icc a b , P2.eval x ≠ 0)
  (hP1a : P1.eval a ≠ 0) (hP1b : P1.eval b ≠ 0) (hneq : sign (P1.eval a) ≠ sign (P1.eval b)) :
    (P0.eval a) * (P2.eval a) < 0 ∧ sign (P0.eval a) = sign (P0.eval b) ∧
    sign (P2.eval a) = sign (P2.eval b) := by
  have : (P1.eval a) * (P1.eval b) < 0 := by
    rw [← sign_eq_neg_one_iff, sign_mul, ← sign_ne_eq_iff_of_ne_zero (sign_ne_zero.mpr hP1a)
      (sign_ne_zero.mpr hP1b )]
    exact hneq
  obtain ⟨r, hrmem, hrr⟩ := polynomial_has_root_of_mul_neg hc (le_of_lt hab) this
  constructor
  · have aux2 : e * P0.eval r = - f * P2.eval r := by
      rw [← eval_C (x := r) (a := e), ← eval_mul, heq]
      simp[hrr]
    have aux3 : (P0.eval r) * (P2.eval r) < 0 := by
      rw [← (mul_lt_mul_iff_right₀ hpose), ← mul_assoc, aux2]
      simp
      rw [mul_assoc, mul_pos_iff_of_pos_left hposf]
      simp[hz2 _ (mem_Icc_of_Ioo hrmem)]
    refine lt_of_le_of_ne ?_ ?_
    · rw [← eval_mul]
      apply nonpos_of_ne_zero_of_exists_neg hc (P := P0 * P2) ?_ hrmem
      · rw [eval_mul]
        exact aux3
      · simp [le_of_lt hab]
      · simp only [eval_mul, ne_eq, mul_eq_zero, not_or]
        intro x hxmem
        exact ⟨hz0 x (mem_Icc_of_Ioo hxmem), hz2 x (mem_Icc_of_Ioo hxmem)⟩
    · simp
      exact ⟨hz0 a (by simp ; exact le_of_lt hab), hz2 a (by simp ; exact le_of_lt hab)⟩
  · constructor
    · by_contra! hcc
      rw [sign_ne_eq_iff_of_ne_zero, ← sign_mul, sign_eq_neg_one_iff] at hcc
      obtain ⟨c, hcmem, hcr⟩ := polynomial_has_root_of_mul_neg hc (le_of_lt hab) hcc
      exact hz0 c (mem_Icc_of_Ioo hcmem) hcr
      simp [hz0 a (by simp ; exact le_of_lt hab)]
      simp [hz0 b (by simp ; exact le_of_lt hab)]
    · by_contra! hcc
      rw [sign_ne_eq_iff_of_ne_zero, ← sign_mul, sign_eq_neg_one_iff] at hcc
      obtain ⟨c, hcmem, hcr⟩ := polynomial_has_root_of_mul_neg hc (le_of_lt hab) hcc
      exact hz2 c (mem_Icc_of_Ioo hcmem) hcr
      simp [hz2 a (by simp ; exact le_of_lt hab)]
      simp [hz2 b (by simp ; exact le_of_lt hab)]


lemma sturm_sequence_unique_root_ne_p (hc : IsRealClosedField F) {a b : F} (hab : a < b)
   {P : List F[X]} {p q : F[X]} (hs : IsSturmSequence P p q) {c : F} (hcmem : c ∈ Ioo a b)
   (hpnr : p.eval c ≠ 0) (hr : ∀ x ∈ Icc a b,  ∀ i , ∀ h : i < P.length , P[i].eval x = 0 → x = c) :
    signChangesPolySeq P a = signChangesPolySeq P b := by
  have hevala : ∀ i, ∀ h : i < P.length, P[i].eval a ≠ 0 := by
    intro i hi haeval
    rw [← hr a (by simp [le_of_lt hab]) i hi haeval ] at hcmem
    simp at hcmem
  have hevalb : ∀ i, ∀ h : i < P.length, P[i].eval b ≠ 0 := by
    intro i hi hbeval
    rw [← hr b (by simp [le_of_lt hab]) i hi hbeval] at hcmem
    simp at hcmem
  have hlgt := hs.hlen
  have hanenil : (List.map (fun x => x.eval a) P) ≠ [] := by
    simp [sturm_sequence_ne_nil hs]
  have hbnenil : (List.map (fun x => x.eval b) P) ≠ [] := by
    simp [sturm_sequence_ne_nil hs]
  apply signChanges_eq_of_lists_opposite_sign
  · simp_rw [List.mem_iff_getElem]
    simp only [List.getElem_map, List.length_map, ne_eq, forall_exists_index]
    exact fun x i h heq  => by rw[← heq] ; exact hevala i h
  · simp_rw [List.mem_iff_getElem]
    simp only [List.getElem_map, List.length_map, ne_eq, forall_exists_index]
    exact fun x i h heq  => by rw[← heq] ; exact hevalb i h
  · obtain ⟨c, hcnz, hcl⟩ := hs.hc
    rw [getLastD_eq_getLast_of_ne_nil hanenil, getLastD_eq_getLast_of_ne_nil hbnenil,
      List.getLast_map, List.getLast_map]
    rw [getLastD_eq_getLast_of_ne_nil (sturm_sequence_ne_nil hs)] at hcl
    rw [hcl]
    simp
  · simp only [List.length_map, List.getElem_map, ne_eq]
    intro i hi hsneq
    have higt : 1 ≤ i := by
      by_contra! hiz
      simp at hiz
      simp_rw [hiz, hs.h0] at hsneq
      rw [← ne_eq, sign_ne_eq_iff_of_ne_zero ?_ ?_, ← sign_mul, sign_eq_neg_one_iff] at hsneq
      obtain ⟨s, hsmem, hs'⟩ := polynomial_has_root_of_mul_neg hc (le_of_lt hab) hsneq
      rw [← hr s (Set.mem_Icc_of_Ioo hsmem ) 0 (by omega) (by simp_rw [hs.h0] ; exact hs') ] at hpnr
      exact hpnr hs'
      · simp only [ne_eq, sign_eq_zero_iff]
        rw [← hs.h0]
        exact hevala 0 (by omega)
      · simp only [ne_eq, sign_eq_zero_iff]
        rw [← hs.h0]
        exact hevalb 0 (by omega)
    constructor
    · exact higt
    · obtain ⟨r, hrmem, hrr⟩ := polynomial_has_root_of_ne_sign hc (le_of_lt hab)
        hsneq (hevala i (by omega)) ((hevalb i (by omega)))
      have hreqc := hr r (mem_Icc_of_Ioo hrmem) i (by omega) hrr
      rw [hreqc] at hrr
      obtain ⟨e, f, Q, hepos, hfpos, hdvd⟩ := hs.hrem (i - 1) (by omega)
      have aux : i - 1 + 2 = i + 1 := by omega
      have := polynomial_change_sign_aux F hc _ _ _  Q hab hepos hfpos hdvd
      simp_rw [Nat.sub_add_cancel higt, aux] at this
      apply this
      · intro x hxmem heval
        have aux2 := hr x hxmem (i - 1) (by omega) heval
        rw [aux2] at heval
        exact no_consecutive_zero1 P p q hs c (i - 1) (by omega)
          (by simp[Nat.sub_add_cancel higt, hrr]) heval
      · intro x hxmem heval
        have aux2 := hr x hxmem (i + 1) (by omega) heval
        rw [aux2] at heval
        exact no_consecutive_zero1 P p q hs c i (by omega) heval hrr
      · exact hevala i (by omega)
      · exact hevalb i (by omega)
      · exact hsneq
  · simp

lemma signChanges_derivative  (hc : IsRealClosedField F) {a b : F} (hab : a < b) {p : F[X]}
  {c : F} (hcmem : c ∈ Ioo a b) (hpr : p.eval c = 0) (hdc : (derivative p).eval c ≠ 0)
  (hr : ∀ x ∈ Icc a b, ∀ i , ∀ h : i < [p, derivative p].length , [p, derivative p][i].eval x = 0 → x = c) :
  signChangesPolySeq [p, derivative p] a = signChangesPolySeq [p, derivative p] b + 1 := by
  have hpevala : p.eval a ≠ 0 := by
    intro haeval
    rw [hr a (by simp [le_of_lt hab]) 0 (by simp) haeval] at hcmem
    simp at hcmem
  have hpevalb : p.eval b ≠ 0 := by
    intro haeval
    rw [hr b (by simp [le_of_lt hab]) 0 (by simp) haeval] at hcmem
    simp at hcmem
  have hderivn : ∀ x ∈ Icc a b, (derivative p).eval x ≠ 0 := by
    intro x hxmem  heval
    have := hr x hxmem 1 (by simp) heval
    rw [this] at heval
    exact hdc heval
  have hxru : ∀ x ∈ Icc a b, p.eval x = 0 → x = c := by
    intro x hxmem hxeval
    exact hr x hxmem 0 (by simp) hxeval
  unfold signChangesPolySeq
  simp ; rw [signChanges_cons hpevala]
  simp ; rw [signChanges_cons hpevalb]
  simp only [← sign_mul, derivative_mul_neg_of_sign_neg_left hc hab hcmem hpr hxru hderivn,
    sign_neg, ↓reduceIte, List.headD_cons,
    derivative_mul_neg_of_sign_neg_right hc hab hcmem hpr hxru hderivn, sign_pos, neg_iff,
    self_eq_neg_iff, one_ne_zero, signChanges_single, zero_add]
  · simp ; exact hderivn b (by simp[le_of_lt hab] )
  · simp ; exact hderivn a (by simp[le_of_lt hab] )


lemma sturm_sequence_unique_root_p (hc : IsRealClosedField F) {a b : F} (hab : a < b)
   {P : List F[X]} {p : F[X]} (hs : IsSturmSequence P p (derivative p)) {c : F} (hcmem : c ∈ Ioo a b)
   (hpr : p.eval c = 0) (hr : ∀ x ∈ Icc a b, ∀ i , ∀ h : i < P.length , P[i].eval x = 0 → x = c) :
  signChangesPolySeq P a = signChangesPolySeq P b + 1 := by
  have havePl := hs.hlen
  have hdpevala : (derivative p).eval a ≠ 0 := by
    intro haeval
    rw [hr a (by simp [le_of_lt hab]) 1 (by omega) (by erw[hs.h1] ; exact haeval )] at hcmem
    simp at hcmem
  have hdpevalb : (derivative p).eval b ≠ 0 := by
    intro haeval
    rw [hr b (by simp [le_of_lt hab]) 1 (by omega) (by erw[hs.h1] ; exact haeval )] at hcmem
    simp at hcmem
  have hPL : ∃ as , P = (p :: derivative p  :: as) := by
    match P with
    | [] =>
    simp at havePl
    | [a] =>
    simp at havePl
    | (a :: b :: as) =>
      use as
      have aux1 := hs.h0
      have aux2 := hs.h1
      simp at aux1 aux2 ⊢
      exact ⟨aux1, aux2⟩
  obtain ⟨as, has⟩ := hPL
  by_cases hasn : as = []
  · rw [hasn] at has
    simp_rw [has] at *
    apply signChanges_derivative F hc hab hcmem hpr _ hr
    intro hevald
    exact no_consecutive_zero1 [p, derivative p] _ _ hs c 0 (by simp) hevald hpr
  · simp_rw [has] at *
    simp [signChangesPolySeq]
    rw [signChanges_cons_eq_add _ _ _ hdpevala, signChanges_cons_eq_add _ _ _ hdpevalb,
      add_assoc, add_comm _ 1, ← add_assoc]
    congr 1
    · refine signChanges_derivative F hc hab hcmem hpr ?_ ?_
      · intro hevald
        exact no_consecutive_zero1 _ _ _ hs c 0 (by simp) hevald hpr
      · rintro x hxmem i hile hieval
        simp at hile
        interval_cases i
        · exact hr x hxmem 0 (by simp) hieval
        · exact hr x hxmem 1 (by simp) hieval
    · simp_rw [← List.map_cons, ← signChangesPolySeq_def ]
      apply sturm_sequence_unique_root_ne_p F hc hab
        (sturm_sequence_cons (derivative p :: as) p (derivative p) _ ?_ hs) hcmem
      · intro hevald
        exact no_consecutive_zero1 _ _ _ hs c 0 (by simp) hevald hpr
      · rintro x hxmem i hile hieval
        simp at hile
        exact hr x hxmem (i + 1) (by simp ; omega) hieval
      · simp ; by_contra! hc' ; simp[hasn] at hc'


open Finset

lemma roots_of_prod_mem_iff (a b : F) (P : List F[X]) (x : F) (hz : 0 ∉ P) :
  x ∈ (((Multiset.toFinset (P.prod).roots).filter (fun x => x ∈ Icc a b))) ↔
  ∃ i : ℕ , (∃ h : i < P.length, P[i].eval x = 0 ∧ x ∈ Icc a b)  := by
  simp
  have : ∀ x, (Polynomial.aeval x) (P.prod) = (List.map (fun y => y.eval x) P).prod := by
    intro c
    simp [← List.prod_hom]
  rintro hle1 hle2
  simp at this
  simp [this, hz,  List.mem_iff_getElem]

lemma roots_mem_le_roots_prod {P : List F[X]} (hz : 0 ∉ P) {i : ℕ} (hi : i < P.length):
  P[i].roots.toFinset ⊆ P.prod.roots.toFinset := by
  intro x hx
  simp at hx ⊢
  constructor
  · exact hz
  · have : ∀ x, (Polynomial.aeval x) (P.prod) = (List.map (fun y => y.eval x) P).prod := by
      intro c
      simp [← List.prod_hom]
    simp at this
    rw [this]
    simp
    exact ⟨P[i] , by simp[hx.2]⟩


omit [Field F] [IsStrictOrderedRing F]
lemma finset_card_add_interval {a b c : F} (hcmem : c ∈ Icc a b) {S : Finset F} (hcn : c ∉ S)  :
  #(S.filter (fun x => x ∈ Icc a b)) =
    #(S.filter (fun x => x ∈ Icc a c)) + #(S.filter (fun x => x ∈ Icc c b)) := by
  convert Finset.card_union_of_disjoint (α := F) ?_ using 2
  rw [Set.mem_Icc] at hcmem
  · ext x
    simp
    rcases LinearOrder.le_total x c with h1 | h2
    · constructor
      · intro h
        exact Or.inl ⟨h.1, ⟨h.2.1, h1⟩ ⟩
      · intro h
        rcases h with h3 | h4
        · exact ⟨h3.1, ⟨h3.2.1, le_trans h1 hcmem.2⟩ ⟩
        · exact ⟨h4.1, ⟨le_trans hcmem.1 h4.2.1 , h4.2.2⟩⟩
    · constructor
      · intro h
        exact Or.inr ⟨h.1, ⟨h2, h.2.2⟩ ⟩
      · intro h
        rcases h with h3 | h4
        · exact ⟨h3.1, ⟨h3.2.1, le_trans h3.2.2 hcmem.2⟩ ⟩
        · exact ⟨h4.1, ⟨le_trans hcmem.1 h4.2.1 , h4.2.2⟩⟩
  · rw [Finset.disjoint_iff_ne]
    intro u hu w hw
    simp at hu hw
    rcases lt_or_eq_of_le (le_trans hu.2.2  hw.2.1) with hc1 | hc2
    · exact ne_of_lt hc1
    · exfalso
      have aux : c = w := by
        rw [hc2] at hu
        grind
      rw [← aux] at hw
      exact hcn hw.1


lemma finset_sorted_list_cons_cons  {F : Type u_2} [Field F] [LinearOrder F]
    {u v : F} {as : List F} {S : Finset F} (heq : S.sort (fun x y => x ≤ y) = (u :: v :: as)) :
    ∀ x ∈ S , x = u ∨ v ≤ x := by
  have aux1 : List.Pairwise (fun x y => x ≤ y) (u :: v :: as) := by
    rw [← heq]
    simp only [pairwise_sort]
  intro x hxmem
  rw [← Finset.mem_sort (r := fun x y => x ≤ y), heq, List.mem_cons] at hxmem
  simp at hxmem
  rcases hxmem with h1 | h2 | h3
  · left
    exact h1
  · right
    exact le_of_eq (id (Eq.symm h2))
  · right
    simp at aux1
    grind

  lemma u_le_v_of_sort  {u v : F} {as : List F}
    {S : Finset F}  (heqc : (u :: v :: as) = (S.sort (fun x y => x ≤ y))) : u < v := by
    have hauxu := getElem_congr_coll (w := by simp) (i := 0) heqc
    simp at hauxu
    have hauxv := getElem_congr_coll (w := by simp) (i := 1) heqc
    simp at hauxv
    refine lt_of_le_of_ne ?_ ?_
    · simp_rw [hauxu, hauxv]
      rw [Finset.sorted_zero_eq_min']
      refine Finset.min'_le _ _ ?_
      rw [← mem_sort (r := fun x y => x ≤ y) ]
      simp only [List.getElem_mem]
    · have := Finset.sort_nodup S (fun x y => x ≤ y)
      rw [← heqc] at this
      simp at this
      exact this.1.1



lemma not_mem_finset_card_eq_one_of_sorted_mem_interval {a b d u v : F} {as : List F}
  {S : Finset F}  (heqc : (u :: v :: as) = ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)))
  (hle1 : u < d) (hle2 : d < v) : d ∈ Icc a b := by
  have hauxu := getElem_congr_coll (w := by simp) (i := 0) heqc
  simp at hauxu
  have hauxv := getElem_congr_coll (w := by simp) (i := 1) heqc
  simp at hauxv
  have humem : u ∈ ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)) := by
    rw [hauxu]
    simp only [Set.mem_Icc, List.getElem_mem]
  have hwmem : v ∈ ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)) := by
    rw [hauxv]
    simp only [Set.mem_Icc, List.getElem_mem]
  simp at humem hwmem
  constructor
  · refine le_of_lt (lt_of_le_of_lt humem.2.1 hle1)
  · refine le_of_lt (lt_of_lt_of_le hle2 hwmem.2.2)

lemma not_mem_finset_card_eq_one_of_sorted  {a b d u v : F} [Field F] [IsStrictOrderedRing F] {as : List F}
  {S : Finset F} (heqc : (u :: v :: as) = ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)))
  (hle1 : u < d) (hle2 : d < v) (x : F) :
    x ∈ (S.filter (fun x => x ∈ Icc a d)) ↔ x = u := by
  have hauxu := getElem_congr_coll (w := by simp) (i := 0) heqc
  simp at hauxu
  have humem : u ∈ ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)) := by
    rw [hauxu]
    simp only [Set.mem_Icc, List.getElem_mem]
  simp at humem
  have hdmem : d ∈ Icc a b := not_mem_finset_card_eq_one_of_sorted_mem_interval F heqc hle1 hle2
  constructor
  · intro h
    simp at h
    obtain ⟨hxmemS, hxa, hxd⟩ := h
    rcases finset_sorted_list_cons_cons heqc.symm x
      (by simp ; exact ⟨hxmemS, ⟨hxa, le_trans hxd hdmem.2⟩⟩) with h1 | h2
    · exact h1
    · linarith
  · intro heq
    simp [heq]
    exact ⟨humem.1, ⟨humem.2.1, le_of_lt hle1⟩⟩

lemma not_mem_finset_card_eq_one_of_sorted_not_mem  {a b d u v : F} [Field F]
  [IsStrictOrderedRing F] {as : List F}
  {S : Finset F} (heqc : (u :: v :: as) = ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)))
  (hle1 : u < d) (hle2 : d < v) : d ∉ S := by
  intro hc
  have aux1 := not_mem_finset_card_eq_one_of_sorted_mem_interval F heqc hle1 hle2
  have aux2 := not_mem_finset_card_eq_one_of_sorted F heqc hle1 hle2 d
  simp at aux1 aux2
  rw [aux2.1 ⟨hc, aux1.1⟩] at hle1
  simp at hle1


lemma not_mem_finset_card_eq_one_of_sorted_single {a b u : F} {S : Finset F}
  (heq : [u] = ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)) )
  (x : F) : x ∈ (S.filter (fun x => x ∈ Icc a b)) ↔ x = u := by
  rw [← Finset.mem_sort (r := fun x y => x ≤ y) , ← heq]
  simp


lemma sturm_theorem_induction_aux [Field F] [IsStrictOrderedRing F]
    (hc : IsRealClosedField F) {n : ℕ} {a b : F} (hab : a < b)
    {P : List F[X]} {p : F[X]} (hs : IsSturmSequence P p (derivative p))
    (ha : ∀ i , ∀ h : i < P.length , P[i].eval a ≠ 0)
    (hb : ∀ i , ∀ h : i < P.length , P[i].eval b ≠ 0)
    (hi : #(((Multiset.toFinset (P.prod).roots).filter (fun x => x ∈ Icc a b))) = n) :
    #((Multiset.toFinset p.roots).filter (fun x => x ∈ Icc a b))
      + signChangesPolySeq P b = signChangesPolySeq P a := by
  have hPl := hs.hlen
  have auxNz : ∀ i, ∀ h : i < P.length , P[i] ≠ 0 := by
    intro i hi h
    have : P[i] ∈ P := by simp
    rw [h] at this
    exact zero_not_member hs this
  revert a b
  induction n using Nat.case_strong_induction_on with
  | hz =>
    intro a b hab ha hb hnr
    rw [Finset.card_eq_zero] at hnr
    have aux : ∀ i , ∀ h : i < P.length , Finset.filter
      (fun x ↦ x ∈ Set.Icc a b) P[i].roots.toFinset = ∅ := by
      intro i hi
      by_contra! hc
      obtain ⟨c, hc⟩ := Finset.Nonempty.exists_mem hc
      have hcmem : c ∈ filter (fun x ↦ x ∈ Set.Icc a b) P.prod.roots.toFinset := by
        rw [roots_of_prod_mem_iff]
        use i , (by omega)
        simp only [Set.mem_Icc, mem_filter, Multiset.mem_toFinset, mem_roots', ne_eq,
          IsRoot.def] at hc
        simp only [hc, Set.mem_Icc, and_self]
        exact zero_not_member hs
      rw [hnr] at hcmem
      simp at hcmem
    have := aux 0 (by omega)
    rw [hs.h0] at this
    rw [this, Finset.card_empty, Eq.comm, zero_add]
    apply signChanges_congr
    · intro i hi
      simp at hi ⊢
      symm ; by_contra hcc
      obtain ⟨s, hsmem, hsp⟩ := polynomial_has_root_of_ne_sign hc (le_of_lt hab) (Ne.symm hcc)
        (ha i (by omega)) (hb i (by omega))
      have hsroot : s ∈ Finset.filter (fun x ↦ x ∈ Set.Icc a b) P[i].roots.toFinset := by
        simp [hsp]
        refine ⟨auxNz i (by omega), Set.mem_Icc_of_Ioo hsmem⟩
      rw [aux i (by omega)] at hsroot
      simp at hsroot
    · simp
  | hi n hn =>
    intro a b hab ha hb hnr
    have hsubs : ∀ (a b : F) , (Multiset.toFinset p.roots).filter (fun x => x ∈ Icc a b)
      ≤ (Multiset.toFinset (P.prod).roots).filter (fun x => x ∈ Icc a b) := by
      intro a b x hxmem
      rw [roots_of_prod_mem_iff _ _ _ _ _ (zero_not_member hs)]
      use 0 , (by omega)
      rw [hs.h0]
      simp at hxmem
      exact ⟨hxmem.1.2, hxmem.2⟩
    set L := (filter (fun x ↦ x ∈ Set.Icc a b) P.prod.roots.toFinset).sort (fun x y => x ≤ y) with hl
    match L with
    | [] =>
    rw [← length_sort (r := fun x y => x ≤ y), ← hl] at hnr
    simp at hnr
    | [c] =>
    have hcIoo : c ∈ Ioo a b := by
      have aux : c ∈ sort
        (filter (fun x ↦ x ∈ Set.Icc a b) P.prod.roots.toFinset) (fun x y ↦ x ≤ y) := by
        rw [← hl]
        simp only [List.mem_cons, true_or]
      rw [Finset.mem_sort] at aux
      rw [roots_of_prod_mem_iff] at aux
      obtain ⟨i, hi,heval, hcmem⟩ := aux
      rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc hcmem with hc1 | hc2 | hc3
      · exfalso
        rw [hc1] at heval
        exact ha i hi heval
      · exfalso
        rw [hc2] at heval
        exact hb i hi heval
      · exact hc3
      exact zero_not_member hs
    have hlc := hl
    apply_fun (fun x => x.toFinset) at hl
    simp only [List.toFinset_cons, List.toFinset_nil,
      LawfulSingleton.insert_empty_eq, sort_toFinset] at hl
    have hcu : ∀ x ∈ Set.Icc a b, ∀ (i : ℕ) (h : i < P.length), eval x P[i] = 0 → x = c := by
      intro x hx i hi hxeval
      have := (roots_of_prod_mem_iff F _ _ P _ (zero_not_member hs)).2 ⟨i, ⟨hi, ⟨hxeval, hx⟩ ⟩ ⟩
      rw [← hl, Finset.mem_singleton] at this
      exact this
    by_cases hcmem : p.eval c = 0
    · have hfilter : Finset.filter (fun x ↦ x ∈ Set.Icc a b) p.roots.toFinset = {c} := by
        ext x
        constructor
        · intro hx
          simp [(not_mem_finset_card_eq_one_of_sorted_single F hlc _).1 (hsubs a b hx)]
        · intro hx
          simp at hx ⊢
          have := (not_mem_finset_card_eq_one_of_sorted_single F hlc _).2 hx
          simp at this
          exact ⟨ ⟨p_ne_zero hs, hx.symm ▸ hcmem⟩ , this.2⟩
      rw [hfilter, Finset.card_singleton]
      symm
      rw [add_comm]
      apply sturm_sequence_unique_root_p F hc hab hs (c := c) hcIoo hcmem hcu
    · have hfilter : Finset.filter (fun x ↦ x ∈ Set.Icc a b) p.roots.toFinset = ∅ := by
        by_contra! hc
        obtain ⟨x, hx⟩ := hc
        have := hsubs a b hx
        rw [← hl] at this
        simp at this hx
        exact (this.symm ▸ hcmem ) hx.1.2
      rw [hfilter, Finset.card_empty, zero_add, Eq.comm]
      apply sturm_sequence_unique_root_ne_p F hc hab hs hcIoo hcmem hcu
    | (c :: f :: as) =>
      have := u_le_v_of_sort F hl
      obtain ⟨d, hd1, hd2⟩ := exists_between (u_le_v_of_sort F hl)
      have hdnemm := not_mem_finset_card_eq_one_of_sorted_not_mem F hl hd1 hd2
      have hdnp : d ∉ p.roots.toFinset := by
        have := roots_mem_le_roots_prod F (i := 0) (zero_not_member hs) (by omega)
        rw [hs.h0] at this
        intro h
        exact hdnemm (this h)
      have hdmemi : d ∈ Icc a b := not_mem_finset_card_eq_one_of_sorted_mem_interval F hl hd1 hd2
      have hcIcc : c ∈ Icc a b := by
        have aux : c ∈ sort
          (filter (fun x ↦ x ∈ Set.Icc a b) P.prod.roots.toFinset) (fun x y ↦ x ≤ y)  := by
          rw [← hl] ; simp only [List.mem_cons, true_or]
        rw [Finset.mem_sort] at aux
        simp at aux
        exact aux.2
      have hfIcc : f ∈ Icc a b := by
        have aux : f ∈ sort
          (filter (fun x ↦ x ∈ Set.Icc a b) P.prod.roots.toFinset) (fun x y ↦ x ≤ y) := by
          rw [← hl]
          simp only [List.mem_cons, true_or, or_true]
        rw [Finset.mem_sort] at aux
        simp at aux
        exact aux.2
      have hald : a < d := lt_of_le_of_lt hcIcc.1  hd1
      have hdlb : d < b := lt_of_lt_of_le hd2 hfIcc.2
      have had : (filter (fun x ↦ x ∈ Set.Icc a d) P.prod.roots.toFinset) = {c} := by
        ext x
        simp only [Finset.mem_singleton]
        apply not_mem_finset_card_eq_one_of_sorted F hl hd1 hd2
      have hcardaux : #(filter (fun x ↦ x ∈ Set.Icc a d) P.prod.roots.toFinset) = 1 := by
        rw [had] ; simp
      have hcard1 : #(filter (fun x ↦ x ∈ Set.Icc a d) P.prod.roots.toFinset) ≤ n := by
        rw [hcardaux]
        rw [← Finset.length_sort (r := fun x y => x ≤ y), ← hl] at hnr
        simp only [List.length_cons, add_left_inj] at hnr
        linarith
      have hcard2 : #(filter (fun x ↦ x ∈ Set.Icc d b) P.prod.roots.toFinset) ≤ n := by
        have := finset_card_add_interval F hdmemi hdnemm
        rw [hnr, hcardaux] at this
        linarith
      have hdnz : ∀ (i : ℕ) (h : i < P.length), eval d P[i] ≠ 0 := by
        intro i hi heval
        apply hdnemm
        apply roots_mem_le_roots_prod F (zero_not_member hs) hi
        simp [heval]
        · intro h
          exact (zero_not_member hs) (h ▸ List.getElem_mem (l := P) hi)
      rw [finset_card_add_interval F hdmemi hdnp]
      rw [← hn (#(filter (fun x ↦ x ∈ Set.Icc a d) P.prod.roots.toFinset) ) hcard1 hald ha hdnz rfl]
      rw [← hn (#(filter (fun x ↦ x ∈ Set.Icc d b) P.prod.roots.toFinset) ) hcard2 hdlb hdnz hb rfl]
      rw [add_assoc]


/-- `Sturm Theorem` for intervals (we assume that none of the polynomials in the sequence
  have zeros at the extremes of the interval.)-/
theorem sturm_theorem [Field F] [IsStrictOrderedRing F] (hc : IsRealClosedField F) {a b : F} (hab : a < b)
    {P : List F[X]} {p : F[X]} (hs : IsSturmSequence P p (derivative p))
    (ha : ∀ i , ∀ h : i < P.length , P[i].eval a ≠ 0) (hb : ∀ i , ∀ h : i < P.length , P[i].eval b ≠ 0) :
    #((Multiset.toFinset p.roots).filter (fun x => x ∈ Icc a b)) =
      signChangesPolySeq P a - signChangesPolySeq P b := by
  symm
  apply Nat.sub_eq_of_eq_add
  apply Eq.symm (sturm_theorem_induction_aux F hc hab hs ha hb rfl)


-- Sturm over `(-∞ , ∞)`
lemma pos_at_infinity_of_leading_coeff_pos [Field F] [IsStrictOrderedRing F]
  (P : F[X]) (hP : P.leadingCoeff > 0) : ∃ N : F, ∀ x, (N < x → 0 < P.eval x) := by
  have hPnz : P ≠ 0 := by
    intro h
    rw [h] at hP
    simp at hP
  by_cases hdeg : P.natDegree = 0
  · obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.1 hdeg
    rw [← hc] at hP ⊢
    simp at hP ⊢
    use 1 ; simp[hP]
  · let coeffs : Fin (P.natDegree + 1) → F := fun i => |P.coeff i|
    let y := ∑ i, coeffs i
    have aux : ∀ i : (Fin (P.natDegree + 1)), |P.coeff i| ≤ y := by
      intro i
      refine le_trans ?_ (Finset.sum_le_sum (f := fun j => if j = i then |P.coeff i| else 0) ?_ )
      · simp
      · intro j hj
        by_cases heq : j = i
        · simp [heq, coeffs]
        · simp [heq, coeffs]
    have hyn : - y ≤ 0 := by
      rw [Left.neg_nonpos_iff]
      refine le_trans ?_ (aux ⟨0, by simp⟩)
      exact abs_nonneg _
    have auxle : ∀ i < P.natDegree + 1, - y ≤ P.coeff i := by
      intro i hi
      refine le_trans (neg_le_neg (aux ⟨i, hi⟩ )) ?_
      exact neg_abs_le (P.coeff _)
    let N := (max 2 ((natDegree P) * y * (P.leadingCoeff )⁻¹))
    have None : 1 < N := by
      unfold N
      refine lt_of_lt_of_le (one_lt_two) ?_
      exact le_max_left 2 _
    use N
    intro x hx
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, add_comm]
    have :  ∑ i ∈ Finset.range P.natDegree, (- y) * x ^ (P.natDegree - 1)
      ≤  ∑ i ∈ Finset.range P.natDegree, P.coeff i * x ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [mul_comm, mul_comm (P.coeff i)]
      apply mul_le_mul_of_nonneg_of_nonpos
      · refine pow_le_pow_right₀ (le_of_lt (lt_trans None hx)) (by simp at hi ; omega)
      · exact auxle i (by simp at hi ; exact Nat.lt_add_right 1 hi)
      · apply pow_nonneg ; linarith
      · exact hyn
    simp at this
    refine lt_of_lt_of_le ?_ (add_le_add_right this (P.coeff P.natDegree * x ^ P.natDegree))
    simp only [coeff_natDegree, lt_add_neg_iff_add_lt, zero_add]
    nth_rw 3 [← Nat.sub_one_add_one hdeg]
    rw [pow_add, pow_one, mul_comm _ x, ← mul_assoc P.leadingCoeff _, ← mul_assoc]
    refine mul_lt_mul_of_pos_right ?_ (by apply pow_pos ; linarith)
    have hN : (↑P.natDegree * y * P.leadingCoeff⁻¹) ≤ N := by
      unfold N
      exact Std.right_le_max
    suffices (↑P.natDegree * y ≤ P.leadingCoeff * ((↑P.natDegree * y * P.leadingCoeff⁻¹))) by nlinarith
    field_simp
    exact Std.IsPreorder.le_refl y


  lemma neg_at_infinity_of_leading_coeff_neg [Field F] [IsStrictOrderedRing F]
  (P : F[X]) (hP : P.leadingCoeff < 0) : ∃ N : F, ∀ x, (N < x → P.eval x < 0) := by
    have := pos_at_infinity_of_leading_coeff_pos F (-P)
    simp at this
    exact this hP

  lemma pos_at_neg_infinity_of_leading_coeff_mul_pos [Field F] [IsStrictOrderedRing F]
      (P : F[X]) (hP : 0 < (-1) ^ (P.natDegree) * P.leadingCoeff ) :
        ∃ N : F, ∀ x, (x < N → 0 < P.eval x) := by
    have := pos_at_infinity_of_leading_coeff_pos F (P.comp (-X))
    simp at this
    obtain ⟨M, hM⟩ := this hP
    use  - M
    intro x hx
    specialize hM (-x) (lt_neg_of_lt_neg hx)
    rw [neg_neg] at hM
    exact hM

  lemma neg_at_neg_infinity_of_leading_coef_mul_neg [Field F] [IsStrictOrderedRing F]
     (P : F[X]) (hP : (-1) ^ (P.natDegree) * P.leadingCoeff < 0) :
      ∃ N : F, ∀ x, (x < N → P.eval x < 0) := by
    have := pos_at_neg_infinity_of_leading_coeff_mul_pos F (-P)
    simp at this
    exact this hP


lemma sign_at_infinity_eq_sign_leading_coeff [Field F] [IsStrictOrderedRing F]
  (P : F[X]) (hn : P ≠ 0) : ∃ N : F, ∀ x, N < x  →
    sign (P.eval x) = sign (P.leadingCoeff) ∧ P.eval x ≠ 0 := by
  rcases lt_trichotomy (P.leadingCoeff) 0 with h1 | h2 | h3
  · obtain ⟨N, hn⟩ :=  neg_at_infinity_of_leading_coeff_neg F P h1
    use N
    intro x hx
    specialize hn x hx
    simp [hn, h1]
    exact ne_of_lt hn
  · rw [← Polynomial.leadingCoeff_ne_zero] at hn ; contradiction
  · obtain ⟨N, hn⟩ := pos_at_infinity_of_leading_coeff_pos F P h3
    use N
    intro x hx
    specialize hn x hx
    simp [hn, h3]
    exact ne_of_gt hn

lemma sign_at_neg_infinity_eq_sign_leading_coeff_mul [Field F] [IsStrictOrderedRing F]
  (P : F[X]) (hn : P ≠ 0) : ∃ N : F, ∀ x, x < N  →
    sign (P.eval x) = sign ((-1) ^ (P.natDegree) * P.leadingCoeff) ∧ P.eval x ≠ 0 := by
  rcases lt_trichotomy ((-1) ^ (P.natDegree) * (P.leadingCoeff)) 0 with h1 | h2 | h3
  · obtain ⟨N, hn⟩ :=  neg_at_neg_infinity_of_leading_coef_mul_neg  F P h1
    use N
    intro x hx
    specialize hn x hx
    simp [hn, h1]
    exact ne_of_lt hn
  · simp at h2 ; contradiction
  · obtain ⟨N, hn⟩ := pos_at_neg_infinity_of_leading_coeff_mul_pos F P h3
    use N
    intro x hx
    specialize hn x hx
    simp [hn, h3]
    exact ne_of_gt hn

/--  Sturm's theorem over (-∞, + ∞)
    Count the total number of distinct roots.  -/

theorem sturm_theorem_total [Field F] [IsStrictOrderedRing F]  (hc : IsRealClosedField F)
    {P : List F[X]} {p : F[X]} (hs : IsSturmSequence P p (derivative p)) :
    #(Multiset.toFinset p.roots) = signChangesNInfty P - signChangesInfty P  := by
  have hlenP := hs.hlen
  let f : F[X] → F := fun q => if h : q ≠ 0 then
    (sign_at_infinity_eq_sign_leading_coeff F q h).choose else 0
  let M := List.maximum_of_length_pos (l := List.map f P) (by simp ; linarith)
  let g : F[X] → F := fun q => if h : q ≠ 0 then
    (sign_at_neg_infinity_eq_sign_leading_coeff_mul F q h).choose else 0
  let N := min M (List.minimum_of_length_pos (l := List.map g P) (by simp ; linarith))
  have hnz : ∀ i : ℕ , ∀ h : i < P.length, P[i] ≠ 0 := by
    intro i hi
    exact zero_not_member' hs i hi
  have aux1 : ∀ i : ℕ , ∀ h : i < P.length ,
    ∀ x, M < x → sign (P[i].eval x) = sign (P[i].leadingCoeff) ∧ P[i].eval x ≠ 0 := by
    intro i hi x hx
    have hile : i < (List.map f P).length := by simp[hi]
    have aux2 : (List.map f P)[i] ≤ M := List.getElem_le_maximum_of_length_pos _ _
    simp[f, hnz] at aux2
    exact (sign_at_infinity_eq_sign_leading_coeff F P[i] (hnz i hi)).choose_spec x (lt_of_le_of_lt aux2 hx)
  have aux2 : ∀ i : ℕ , ∀ h : i < P.length ,
    ∀ x, x < N → sign (P[i].eval x) = sign ((-1) ^ (P[i].natDegree) * P[i].leadingCoeff) ∧ P[i].eval x ≠ 0  := by
    intro i hi x hx
    have hile : i < (List.map g P).length := by simp[hi]
    have aux2 : N ≤ (List.map g P)[i] := le_trans  (min_le_right _ _)
      (List.minimum_of_length_pos_le_getElem _ _)
    simp[g, hnz] at aux2
    exact (sign_at_neg_infinity_eq_sign_leading_coeff_mul F P[i] (hnz i hi)).choose_spec x (lt_of_lt_of_le hx aux2)
  have hseteq : (Multiset.toFinset p.roots).filter (fun x => x ∈ Icc (N - 1) (M + 1)) =
    (Multiset.toFinset p.roots) := by
    refine subset_antisymm ?_ ?_
    · exact Finset.filter_subset _ _
    · intro x hx
      simp only [Set.mem_Icc, mem_filter, hx, tsub_le_iff_right, true_and]
      simp at hx ; rw [← hs.h0] at hx
      by_contra hcc
      rw [Classical.not_and_iff_not_or_not] at hcc
      push Not at hcc
      rcases hcc with h1 | h2
      · exact (aux2 0 (by omega) x (by linarith)).2 hx.2
      · exact (aux1 0 (by omega) x (by linarith)).2 hx.2
  have hb : ∀ i , ∀ h : i < P.length , P[i].eval (M + 1) ≠ 0 := by
    intro i hi heval
    exact (aux1 i hi (M + 1) (by linarith)).2 heval
  have ha : ∀ i , ∀ h : i < P.length , P[i].eval (N - 1) ≠ 0 := by
    intro i hi heval
    exact (aux2 i hi (N - 1) (by linarith)).2 heval
  have hleN : N - 1 < M + 1 := by
    have : N ≤ M := by simp[N]
    linarith
  rw [← hseteq, sturm_theorem F hc hleN hs ha hb]
  congr
  · apply signChanges_congr
    · intro i hi
      simp at hi ⊢
      exact (aux2 i hi (N - 1) (by linarith)).1
    · simp
  · apply signChanges_congr
    · intro i hi
      simp at hi ⊢
      exact (aux1 i hi (M + 1) (by linarith)).1
    · simp


/-- We can compute over a subring of the real closed field. -/
theorem sturm_theorem_map {R : Type*} [Field F] [IsStrictOrderedRing F]
  [CommRing R] [LinearOrder R]
   (hc : IsRealClosedField F) (f : R →+* F) (hmono : StrictMono f) {a b : R} (hab : a < b)
    {P : List R[X]} {p : R[X]} (hs : IsSturmSequence P p (derivative p))
    (ha : ∀ i , ∀ h : i < P.length , P[i].eval a ≠ 0) (hb : ∀ i , ∀ h : i < P.length , P[i].eval b ≠ 0) :
    #((Multiset.toFinset (map f p).roots).filter (fun x => x ∈ Icc (f a) (f b))) =
      signChangesPolySeq P a - signChangesPolySeq P b := by
  have := IsSturmSequence_map hs f hmono
  rw [← Polynomial.derivative_map] at this
  rw [sturm_theorem F hc (hmono.imp hab) this]
  · simp_rw [signChangesPolySeq_map f hmono]
  · intro i hi
    simp_rw [List.getElem_map]
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
    refine (map_ne_zero_iff f (StrictMono.injective hmono)).mpr (ha i (List.length_map (Polynomial.map f) ▸ hi))
  · intro i hi
    simp_rw [List.getElem_map]
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
    refine (map_ne_zero_iff f (StrictMono.injective hmono)).mpr (hb i (List.length_map (Polynomial.map f) ▸ hi))


theorem sturm_theorem_total_map {R : Type*} [Field F] [IsStrictOrderedRing F]
    [CommRing R] [LinearOrder R] (hc : IsRealClosedField F)
    (f : R →+* F) (hmono : StrictMono f) {P : List R[X]} {p : R[X]} (hs : IsSturmSequence P p (derivative p)) :
    #(Multiset.toFinset (map f p).roots) = signChangesNInfty P - signChangesInfty P := by
  have := IsSturmSequence_map hs f hmono
  rw [← Polynomial.derivative_map] at this
  rw [sturm_theorem_total F hc this]
  · rw [signChangesInfty_map f hmono, signChangesNInfty_map f hmono]



section SturmOfList

variable {R : Type*}  [CommRing R] [LinearOrder R]


structure SturmBuilderOfList (P : List (List R)) (p : List R) (q : List R) where
  hlen : 2 ≤ P.length
  h0 : P[0] = p
  h1 : P[1] = q
  hlast : (P.getLastD []).length = 1
  hdrop : ∀ i , ∀ h : i < P.length, P[i] = (P[i]).dropTrailingZeros'
  hmono :  ∀ i , ∀ h : i + 1 < P.length, P[i + 1].length < P[i].length
  e : List R
  epos : ∀ {i : ℕ}, ∀ h : i < e.length , 0 < e[i]
  f : List R
  fpos : ∀ {i : ℕ}, ∀ h : i < f.length, 0 < f[i]
  Q : List (List R)
  hel : P.length ≤ e.length + 2
  hfl : P.length ≤ f.length + 2
  hQl : P.length ≤ Q.length + 2
  hrem : ∀ i, ∀ h2 : i + 2 < P.length ,
    P[i].mulPointwise e[i] = Q[i] * P[i + 1] - P[i + 2].mulPointwise (f[i])

lemma SturmBuilderOfList_ne_nil {P : List (List R)} {p : List R} {q : List R}
  (h : SturmBuilderOfList P p q) : P ≠ [] := by
  have := h.hlen
  rintro ⟨h, rfl⟩
  simp at this

lemma SturmBuilderOfList_not_mem_nil {P : List (List R)} {p : List R} {q : List R}
  (h : SturmBuilderOfList P p q) (i : ℕ) (hio : i < P.length) : P[i] ≠ [] := by
  intro hi
  by_cases hieq : i = P.length - 1
  · simp_rw [hieq] at hi
    rw [← List.getLast_eq_getElem (SturmBuilderOfList_ne_nil h), ← getLastD_eq_getLast_of_ne_nil (a := [])] at hi
    have := hi ▸ h.hlast
    simp at this
  · have := h.hmono i (by omega)
    rw [hi] at this
    simp at this


lemma SturmBuilderOfList_isSturm {P : List (List R)} {p : List R} {q : List R}
  (h : SturmBuilderOfList P p q) :
    IsSturmSequence (List.map (ofList) P) (ofList p) (ofList q) where
  hlen := by
    simp ; exact h.hlen
  h0 := by
    simp ; rw [h.h0]
  h1 := by
    simp ; erw [h.h1]
  hc := by
    have := h.hlen
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.1 h.hlast
    rw [getLastD_eq_getLast_of_ne_nil (SturmBuilderOfList_ne_nil h)] at hc
    use c
    constructor
    · rw [List.getLast_eq_getElem] at hc
      intro hcc
      have := hcc ▸ hc ▸ (h.hdrop (P.length -1) (by omega))
      simp [List.dropTrailingZeros'] at this
    · rw [getLastD_eq_getLast_of_ne_nil, List.getLast_map, hc]
      · simp
      · simp[(SturmBuilderOfList_ne_nil h)]
  hmono := by
    intro i hi
    simp at hi
    rw [List.getElem_map, List.getElem_map, ← Nat.succ_lt_succ_iff, Nat.succ_eq_add_one,
      Nat.succ_eq_add_one, natDegree_ofList _ (SturmBuilderOfList_not_mem_nil h i (by omega)),
      natDegree_ofList _ (SturmBuilderOfList_not_mem_nil h (i + 1) (by omega)) ]
    · exact h.hmono i hi
    · rw [dropTrailingZeros_eq_dropTrailingZeros']
      exact h.hdrop (i + 1) (by omega)
    · rw [dropTrailingZeros_eq_dropTrailingZeros']
      exact h.hdrop i (by omega)
  hrem := by
    intro i hi
    simp at hi
    have := h.hel ; have := h.hfl ; have := h.hQl
    use h.e[i], h.f[i], ofList (h.Q[i]), (h.epos (by omega)), (h.fpos (by omega))
    simp
    rw [← ofList_mulPointwise_eq_C_mul, h.hrem i hi]
    simp

def signChangesInftyOfList (P : List (List R)) :=
    signChanges (List.map (fun x => if h : x ≠ [] then x.getLast h else 0) P)

def signChangesNInftyOfList (P : List (List R)) :=
  signChanges (List.map (fun x => if h : x ≠ [] then ((-1 : R) ^ (x.length - 1)) * x.getLast h else 0) P)

def signChangesSeqOfList (P : List (List R)) (a : R) :=
  signChanges (List.map (fun x => x.eval a) P)

lemma signChangesInftyOfList_eq_signChangesInfty  {P : List (List R)} {p : List R} {q : List R}
  (h : SturmBuilderOfList P p q) :  signChangesInftyOfList P = signChangesInfty (List.map (ofList) P) := by
  unfold signChangesInfty signChangesInftyOfList
  congr 1
  simp[List.mem_iff_getElem]
  intro a i hi hia
  have hal : ¬ a = [] := by
    intro this
    rw [this] at hia
    exact SturmBuilderOfList_not_mem_nil h i hi hia
  simp [hal]
  rw [ofList_leadingCoeff a hal ?_ ]
  rw [← hia, dropTrailingZeros_eq_dropTrailingZeros']
  exact h.hdrop i hi


lemma signChangesNInftyOfList_eq_signChangesNInfty  {P : List (List R)} {p : List R} {q : List R}
  (h : SturmBuilderOfList P p q) :  signChangesNInftyOfList P = signChangesNInfty (List.map (ofList) P) := by
  unfold signChangesNInfty signChangesNInftyOfList
  congr 1
  simp[List.mem_iff_getElem]
  intro a i hi hia
  have hal : ¬ a = [] := by
    intro this
    rw [this] at hia
    exact SturmBuilderOfList_not_mem_nil h i hi hia
  simp [hal]
  rw [ofList_leadingCoeff a hal ?_ ]
  swap
  · rw [← hia, dropTrailingZeros_eq_dropTrailingZeros']
    exact h.hdrop i hi
  · congr
    rw [← natDegree_ofList _ hal]
    · simp
    · rw [← hia, dropTrailingZeros_eq_dropTrailingZeros']
      exact h.hdrop i hi

lemma signChangesSeqOfList_eq_signChangesPolySeq {P : List (List R)}
    (a : R) : signChangesSeqOfList P a = signChangesPolySeq (List.map (ofList) P) a := by
  unfold signChangesSeqOfList signChangesPolySeq
  congr 1
  simp [eval_of_list_eq_eval]


lemma sturm_theorem_map_ofList {R : Type*} [Field F] [IsStrictOrderedRing F]
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  (hc : IsRealClosedField F) (f : R →+* F) (hmono : StrictMono f) {a b : R} (hab : a < b)
  {P : List (List R)} {p : List R}
  (h : SturmBuilderOfList P p (List.derivative p).dropTrailingZeros)
  (ha : ∀ i , ∀ h : i < P.length , P[i].eval a ≠ 0)
  (hb : ∀ i , ∀ h : i < P.length , P[i].eval b ≠ 0) :
  #((Multiset.toFinset (map f (ofList p)).roots).filter (fun x => x ∈ Icc (f a) (f b))) =
      signChangesSeqOfList P a - signChangesSeqOfList P b := by
  rw [signChangesSeqOfList_eq_signChangesPolySeq, signChangesSeqOfList_eq_signChangesPolySeq,
    sturm_theorem_map F hc f hmono hab]
  · rw [← ofList_derivative_eq_derivative, ← ofList_dropTrailingZeros_eq_ofList p.derivative]
    exact SturmBuilderOfList_isSturm h
  · simp [eval_of_list_eq_eval]
    exact ha
  · simp [eval_of_list_eq_eval]
    exact hb


lemma sturm_theorem_total_map_ofList {R : Type*} [Field F] [IsStrictOrderedRing F]
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (hc : IsRealClosedField F)
    (f : R →+* F) (hmono : StrictMono f) {P : List (List R)} {p : List R}
    (h : SturmBuilderOfList P p (List.derivative p).dropTrailingZeros) :
  #(Multiset.toFinset (map f (ofList p)).roots) = signChangesNInftyOfList P - signChangesInftyOfList P := by
  rw [signChangesInftyOfList_eq_signChangesInfty h, signChangesNInftyOfList_eq_signChangesNInfty h,
    sturm_theorem_total_map F hc f hmono]
  · rw [← ofList_derivative_eq_derivative, ← ofList_dropTrailingZeros_eq_ofList p.derivative]
    exact SturmBuilderOfList_isSturm h



/-- EXAMPLE 1:  `X ^ 5 - 3 * X ^ 3 + 9 * X - 8` -/

@[reducible]
def P1 : List (List ℤ):= [[-8, 9, 0, -3, 0, 1], [9, 0, -9, 0, 5], [20, -18, 0, 3],
    [-27, 100, -63], [-4752, 3103], [1]]

def SturmBuilderExample1 : SturmBuilderOfList [[-8, 9, 0, -3, 0, 1], [9, 0, -9, 0, 5], [20, -18, 0, 3],
    [-27, 100, -63], [-4752, 3103], [1]] [-8, 9, 0, -3, 0, 1] [9, 0, -9, 0, 5] where
  hlen := by decide
  h0 := by decide
  h1 := by decide
  hlast := by decide
  hdrop := by decide
  hmono := by
    dsimp
    intro i hic
    have hi : i < 5 := by omega
    interval_cases i <;> (dsimp ; decide)
  e := [25, 9, 3969, 9628609]
  f := [10, 3, 15, 208061595]
  epos := by decide
  fpos := by decide
  Q := [[0, 5], [0, 15], [-300, -189], [10924, -195489]]
  hel := by decide
  hfl := by decide
  hQl := by decide
  hrem := by
    dsimp
    intro i hi
    have hi : i < 4 := by omega
    interval_cases i <;> dsimp <;> decide


/-- The polynomial `X ^ 5 - 3 * X ^ 3 + 9 * X - 8` has exactly `1` real root -/
theorem real_roots1 :
    #(Multiset.toFinset (X ^ 5 - 3 * X ^ 3 + 9 * X - 8 : ℝ[X]).roots) = 1 := by
  have hd : (List.derivative [-8, 9, 0, -3, 0, 1]).dropTrailingZeros = [9, 0, -9, 0, 5] := by decide
  have hpoly : (X ^ 5 - 3 * X ^ 3 + 9 * X - 8 : ℝ[X]) =
      map (algebraMap ℤ ℝ) (ofList [-8, 9, 0, -3, 0, 1]) := by
    rw [ofList_map]
    simp only [List.map_cons, List.map_nil, ofList_cons, ofList_nil, eq_intCast,
      Polynomial.C_eq_intCast]
    push_cast
    ring
  rw [hpoly]
  exact (sturm_theorem_total_map_ofList ℝ Real.IsRealClosedField (algebraMap ℤ ℝ)
    Int.cast_strictMono (hd ▸ SturmBuilderExample1)).trans (by decide)


/-- EXAMPLE 2:  `X^8 - X^7 - 3*X^6 + 3*X^5 + 3*X^4 - 6*X^3 - 2*X^2 + 3*X + 1` -/

@[reducible]
def P2 : List (List ℤ):= [[1, 3, -2, -6, 3, 3, -3, -1, 1], [3, -4, -18, 12, 15, -18, -7, 8],
  [-67, -164, 114, 228, -111, -54, 55], [-191, -392, -193, 384, 777, 48], [971, 1944, 821, -2032, -3741],
  [-14243, -38910, 11875, 48646], [-11255, 808, 33203], [1649, 3522], [1]]

def SturmBuilderExample2 : SturmBuilderOfList P2 [1, 3, -2, -6, 3, 3, -3, -1, 1]
  [3, -4, -18, 12, 15, -18, -7, 8] where
  hlen := by decide
  h0 := by decide
  h1 := by decide
  hlast := by decide
  hdrop := by decide
  hmono := by
    unfold P2 ; dsimp
    intro i hic
    have hi : i < 8 := by omega
    interval_cases i <;> norm_num
  e := [64, 3025, 2304, 13995081, 2366433316, 1102439209, 12404484]
  f := [1, 64, 9075, 3840, 135285783, 7099299948, 54019521241]
  epos := by decide
  fpos := by decide
  Q := [[-1, 8], [47, 440], [-45327, 2640], [-2809221, -179568],
  [-54424297, -181984686], [354979657, 1615193138], [-51905971, 116940966]]
  hel := by decide
  hfl := by decide
  hQl := by decide
  hrem := by
    unfold P2 ; dsimp
    intro i hi
    have hi : i < 7 := by omega
    interval_cases i <;> dsimp <;> decide


/-- The polynomial `X^8 - X^7 - 3*X^6 + 3*X^5 + 3*X^4 - 6*X^3 - 2*X^2 + 3*X + 1` has exactly `4` real root -/
theorem real_roots2 :
    #(Multiset.toFinset (X^8 - X^7 - 3*X^6 + 3*X^5 + 3*X^4 - 6*X^3 - 2*X^2 + 3*X + 1 : ℝ[X]).roots) = 4 := by
  have hd : (List.derivative [1, 3, -2, -6, 3, 3, -3, -1, 1]).dropTrailingZeros =
    [3, -4, -18, 12, 15, -18, -7, 8] := by decide
  have hpoly : (X^8 - X^7 - 3*X^6 + 3*X^5 + 3*X^4 - 6*X^3 - 2*X^2 + 3*X + 1 : ℝ[X]) =
      map (algebraMap ℤ ℝ) (ofList [1, 3, -2, -6, 3, 3, -3, -1, 1]) := by
    rw [ofList_map]
    simp only [List.map_cons, List.map_nil, ofList_cons, ofList_nil, eq_intCast,
      Polynomial.C_eq_intCast]
    push_cast
    ring
  rw [hpoly]
  exact (sturm_theorem_total_map_ofList ℝ Real.IsRealClosedField (algebraMap ℤ ℝ)
    Int.cast_strictMono (hd ▸ SturmBuilderExample2)).trans (by decide)
