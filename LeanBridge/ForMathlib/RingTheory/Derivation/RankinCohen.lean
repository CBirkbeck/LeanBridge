import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# The Rankin–Cohen brackets in a differential ring

Let `A` be a commutative ring with a derivation `a ↦ a′`, and let `k` and `ℓ` be integers. The
`n`-th Rankin–Cohen bracket of `u, v ∈ A` in weights `k` and `ℓ` is
`[u, v]ₙ = ∑_{r + s = n} (-1)^r C(k + n - 1, s) C(ℓ + n - 1, r) u^(r) v^(s)`, where `u^(r)` is the
`r`-th derivative. This file proves the algebraic identity behind Cohen's theorem that the brackets
of modular forms are modular forms: if `x ∈ A` satisfies `x′ = -x²` and the derivative of an
element `a` of weight `w` is replaced by its covariant derivative `a′ + w x a`, of weight `w + 2`,
then the bracket does not change. For modular forms, `x` is the function `c / (cz + d)` and the
covariant derivatives of `f ∣[k] γ` are the slashes of the derivatives of `f`.

The proof makes `x` a formal variable. In `A[X]`, with the derivation extending that of `A` by
`X′ = -X²`, the iterated covariant derivatives `Θ_k^r u` of `u` are polynomials in `X`, whose
derivative in `X` is `r (k + r - 1) Θ_k^(r - 1) u`. So the bracket of these polynomials has
derivative `0` in `X`: the terms cancel in pairs, by `(j + 1) C(a, j + 1) = (a - j) C(a, j)`. If
`A` has no additive torsion, the bracket is then a constant polynomial, and its values at `X = x`
and at `X = 0` agree.

## Main definitions

* `Differential.weightDerivPoly`: the iterated covariant derivatives `Θ_k^r u`, as polynomials in
  the formal variable.
* `Differential.rankinCohenPoly`: the Rankin–Cohen bracket of these polynomials.
* `Differential.rankinCohenBracket`: the `n`-th Rankin–Cohen bracket `[u, v]ₙ`.

## Main results

* `Differential.derivative_weightDerivPoly_succ`: the derivative of `Θ_k^(r + 1) u` in the formal
  variable is `(r + 1) (k + r) Θ_k^r u`.
* `Differential.aeval_weightDerivPoly_succ`: at an `x` with `x′ = -x²`, the polynomials `Θ_k^r u`
  take the iterated covariant derivatives of `u` as values.
* `Differential.derivative_rankinCohenPoly`: the bracket of the polynomials `Θ_k^r u` and
  `Θ_ℓ^s v` has derivative `0` in the formal variable.
* `Differential.aeval_rankinCohenPoly`: the bracket of the covariant derivatives is `[u, v]ₙ`.

## References

* H. Cohen, *Sums involving the values at negative integers of L-functions of quadratic
  characters*, Math. Ann. 217 (1975), 271–285.
* D. Zagier, *Modular forms and differential operators*, Proc. Indian Acad. Sci. Math. Sci. 104
  (1994), 57–75.
-/

open Finset Polynomial

open scoped Differential

namespace Differential

variable {A : Type*} [CommRing A] [Differential A] (k l : ℤ) (u v x : A) (n r : ℕ) (p : A[X])

lemma derivative_mapCoeffs : derivative (mapCoeffs p) = mapCoeffs (derivative p) := by
  ext i
  simp [coeff_derivative, mul_comm]

lemma derivative_implicitDeriv_neg_sq : derivative (implicitDeriv (-X ^ 2) p) =
    implicitDeriv (-X ^ 2) (derivative p) - 2 • (X * derivative p) := by
  simp [implicitDeriv, derivative_mapCoeffs]
  ring1

/-- The polynomial `Θ_k^r u ∈ A[X]`: the `r`-th iterated covariant derivative of an element `u` of
weight `k` of a differential ring `A`, for a formal variable `X` with `X′ = -X²`. It is given by
`Θ_k^0 u = u` and `Θ_k^(r + 1) u = (Θ_k^r u)′ + (k + 2r) X Θ_k^r u`, the covariant derivative of
weight `k + 2r`. -/
noncomputable def weightDerivPoly : ℕ → A[X]
  | 0 => C u
  | r + 1 => implicitDeriv (-X ^ 2) (weightDerivPoly r) + (k + 2 * r : ℤ) • (X * weightDerivPoly r)

lemma weightDerivPoly_zero : weightDerivPoly k u 0 = C u :=
  rfl

lemma weightDerivPoly_succ : weightDerivPoly k u (r + 1) =
    implicitDeriv (-X ^ 2) (weightDerivPoly k u r) +
      (k + 2 * r : ℤ) • (X * weightDerivPoly k u r) :=
  rfl

/-- **The lowering relation**: the derivative of `Θ_k^(r + 1) u` in the formal variable `X` is
`(r + 1) (k + r) Θ_k^r u`. -/
lemma derivative_weightDerivPoly_succ :
    derivative (weightDerivPoly k u (r + 1)) = ((r + 1) * (k + r) : ℤ) • weightDerivPoly k u r := by
  induction r with
  | zero => simp [weightDerivPoly]
  | succ r ih =>
    rw [weightDerivPoly_succ, map_add, derivative_implicitDeriv_neg_sq, map_zsmul, derivative_mul,
      derivative_X, ih, map_zsmul, weightDerivPoly_succ]
    push_cast
    ring1

variable {x} in
/-- **The values of `Θ_k^r u` are the iterated covariant derivatives**: if `x′ = -x²`, then the
value of `Θ_k^(r + 1) u` at `x` is `a′ + (k + 2r) x a`, where `a` is the value of `Θ_k^r u`. -/
lemma aeval_weightDerivPoly_succ (hx : x′ = -x ^ 2) : aeval x (weightDerivPoly k u (r + 1)) =
    (aeval x (weightDerivPoly k u r))′ +
      (k + 2 * r : ℤ) • (x * aeval x (weightDerivPoly k u r)) := by
  rw [weightDerivPoly_succ, map_add, map_zsmul, map_mul, aeval_X,
    ← deriv_aeval_eq_implicitDeriv x (-X ^ 2) (by simpa using hx)]

lemma aeval_zero_weightDerivPoly :
    aeval (0 : A) (weightDerivPoly k u r) = (deriv : A → A)^[r] u := by
  induction r with
  | zero => simp [weightDerivPoly]
  | succ r ih =>
    rw [aeval_weightDerivPoly_succ k u r (by simp), ih, zero_mul, smul_zero, add_zero,
      Function.iterate_succ_apply']

private lemma succ_mul_choose_succ :
    (r + 1) * Ring.choose k (r + 1) = (k - r) * Ring.choose k r := by
  have h : (r + 1).choose r • Ring.choose k (r + 1) = Ring.choose k r * Ring.choose (k - r) 1 := by
    simpa using Ring.choose_smul_choose k (Nat.le_succ r)
  rw [Nat.choose_succ_self_right, Ring.choose_one_right, nsmul_eq_mul] at h
  push_cast at h
  linear_combination h

/-- The `n`-th Rankin–Cohen bracket of the polynomials `Θ_k^r u` and `Θ_ℓ^s v` of `A[X]`:
`∑_{r + s = n} (-1)^r C(k + n - 1, s) C(ℓ + n - 1, r) Θ_k^r u Θ_ℓ^s v`. -/
noncomputable def rankinCohenPoly : A[X] :=
  ∑ p ∈ antidiagonal n,
    ((-1) ^ p.1 * Ring.choose (k + n - 1) p.2 * Ring.choose (l + n - 1) p.1 : ℤ) •
      (weightDerivPoly k u p.1 * weightDerivPoly l v p.2)

/-- The **`n`-th Rankin–Cohen bracket**
`[u, v]ₙ = ∑_{r + s = n} (-1)^r C(k + n - 1, s) C(ℓ + n - 1, r) u^(r) v^(s)` of elements `u` and
`v` of a differential ring, taken in weights `k` and `ℓ`, where `u^(r)` is the `r`-th derivative. -/
noncomputable def rankinCohenBracket : A :=
  ∑ p ∈ antidiagonal n,
    ((-1) ^ p.1 * Ring.choose (k + n - 1) p.2 * Ring.choose (l + n - 1) p.1 : ℤ) •
      ((deriv : A → A)^[p.1] u * (deriv : A → A)^[p.2] v)

lemma aeval_zero_rankinCohenPoly :
    aeval (0 : A) (rankinCohenPoly k l u v n) = rankinCohenBracket k l u v n := by
  simp only [rankinCohenPoly, map_sum, map_zsmul, map_mul, aeval_zero_weightDerivPoly,
    rankinCohenBracket]

/-- **The bracket of the polynomials `Θ_k^r u` and `Θ_ℓ^s v` does not depend on the formal
variable**: its derivative in `X` is `0`. -/
lemma derivative_rankinCohenPoly : derivative (rankinCohenPoly k l u v n) = 0 := by
  rcases n with _ | m
  · simp [rankinCohenPoly, weightDerivPoly_zero]
  rw [rankinCohenPoly]
  simp only [map_sum, map_zsmul, derivative_mul, smul_add, sum_add_distrib]
  rw [Nat.sum_antidiagonal_succ, Nat.sum_antidiagonal_succ']
  simp only [derivative_weightDerivPoly_succ, weightDerivPoly_zero, derivative_C, zero_mul,
    mul_zero, smul_zero, zero_add]
  rw [← sum_add_distrib]
  refine sum_eq_zero fun p hp ↦ ?_
  rw [mem_antidiagonal] at hp
  subst hp
  have h1 : ((p.1 : ℤ) + 1) * Ring.choose (l + (p.1 + p.2 + 1 : ℕ) - 1) (p.1 + 1) =
      (l + p.2) * Ring.choose (l + (p.1 + p.2 + 1 : ℕ) - 1) p.1 := by
    rw [succ_mul_choose_succ]
    push_cast
    ring1
  have h2 : ((p.2 : ℤ) + 1) * Ring.choose (k + (p.1 + p.2 + 1 : ℕ) - 1) (p.2 + 1) =
      (k + p.1) * Ring.choose (k + (p.1 + p.2 + 1 : ℕ) - 1) p.2 := by
    rw [succ_mul_choose_succ]
    push_cast
    ring1
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul, ← add_smul]
  convert zero_smul ℤ _
  linear_combination (-1) ^ (p.1 + 1) * Ring.choose (k + (p.1 + p.2 + 1 : ℕ) - 1) p.2 *
    (k + p.1) * h1 + (-1) ^ p.1 * Ring.choose (l + (p.1 + p.2 + 1 : ℕ) - 1) p.1 * (l + p.2) * h2

variable [HasUniqueDiv A] in
/-- **The Rankin–Cohen bracket is unchanged by covariant derivatives**: in a differential ring
without additive torsion, the bracket of the polynomials `Θ_k^r u` and `Θ_ℓ^s v` takes the value
`[u, v]ₙ` at every `x`. At an `x` with `x′ = -x²` the values of these polynomials are the iterated
covariant derivatives of `u` and `v` (`aeval_weightDerivPoly_succ`). -/
lemma aeval_rankinCohenPoly :
    aeval x (rankinCohenPoly k l u v n) = rankinCohenBracket k l u v n := by
  rw [← aeval_zero_rankinCohenPoly,
    eq_C_of_derivative_eq_zero (derivative_rankinCohenPoly k l u v n), aeval_C, aeval_C]

end Differential
