import Mathlib.RingTheory.Polynomial.GaussNorm

/-!
# Gauss norms of products of polynomials

At a nonarchimedean absolute value `v` and a radius `c > 0`, Mathlib's Gauss norm
`‖P‖ = max_j v(P_j) c ^ j` of polynomials is a nonarchimedean absolute value
(`Polynomial.gaussNorm_isAbsoluteValue`), multiplicative by Gauss's lemma. So it does not change
when a polynomial of smaller Gauss norm is added. This file proves that a product of polynomials
changes by less than its Gauss norm when each factor does (`Polynomial.gaussNorm_prod_sub_prod_lt`).
-/

open Finset

namespace Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R] {v : AbsoluteValue R ℝ} {c : ℝ}

/-- **A product of polynomials changes by less than its Gauss norm when each factor does**: for a
nonarchimedean absolute value `v` on `R`, a real `c > 0` and polynomials `F_i`, `F'_i` with
`‖F'_i - F_i‖ < ‖F_i‖` for the Gauss norm `‖P‖ = max_j v(P_j) c ^ j`, the products satisfy
`‖∏ F'_i - ∏ F_i‖ < ‖∏ F_i‖`, by the multiplicativity of the Gauss norm (Gauss's lemma). -/
lemma gaussNorm_prod_sub_prod_lt (hc : 0 < c) (hv : IsNonarchimedean v) {ι : Type*} (A : Finset ι)
    (F F' : ι → R[X]) (hF : ∀ i ∈ A, (F' i - F i).gaussNorm v c < (F i).gaussNorm v c) :
    (∏ i ∈ A, F' i - ∏ i ∈ A, F i).gaussNorm v c < (∏ i ∈ A, F i).gaussNorm v c := by
  classical
  have : IsAbsoluteValue (gaussNorm v c) := gaussNorm_isAbsoluteValue hv hc
  induction A using Finset.induction_on with
  | empty =>
    rw [prod_empty, prod_empty, sub_self, gaussNorm_zero, ← C_1, gaussNorm_C, map_one]
    exact zero_lt_one
  | insert i A hi ih =>
    have ih' : (∏ j ∈ A, F' j - ∏ j ∈ A, F j).gaussNorm v c < (∏ j ∈ A, F j).gaussNorm v c :=
      ih fun j hj ↦ hF j (mem_insert_of_mem hj)
    have hFi : (F' i - F i).gaussNorm v c < (F i).gaussNorm v c :=
      hF i (mem_insert_self i A)
    have hpos : 0 < (∏ j ∈ A, F j).gaussNorm v c :=
      (gaussNorm_nonneg v _ hc.le).trans_lt ih'
    have hposi : 0 < (F i).gaussNorm v c :=
      (gaussNorm_nonneg v _ hc.le).trans_lt hFi
    have hA' : (∏ j ∈ A, F' j).gaussNorm v c = (∏ j ∈ A, F j).gaussNorm v c := by
      rw [← add_sub_cancel (∏ j ∈ A, F j) (∏ j ∈ A, F' j)]
      exact (isNonarchimedean_gaussNorm v hv hc.le).add_eq_left_of_lt
        (IsAbsoluteValue.abv_neg (gaussNorm v c)) ih'
    have heq : ∏ j ∈ insert i A, F' j - ∏ j ∈ insert i A, F j =
        (F' i - F i) * ∏ j ∈ A, F' j + F i * (∏ j ∈ A, F' j - ∏ j ∈ A, F j) := by
      rw [prod_insert hi, prod_insert hi]
      ring1
    rw [heq, prod_insert hi, gaussNorm_mul hv hc]
    refine (isNonarchimedean_gaussNorm v hv hc.le _ _).trans_lt (max_lt ?_ ?_)
    · rw [gaussNorm_mul hv hc, hA']
      exact mul_lt_mul_of_pos_right hFi hpos
    · rw [gaussNorm_mul hv hc]
      exact mul_lt_mul_of_pos_left ih' hposi

end Polynomial
