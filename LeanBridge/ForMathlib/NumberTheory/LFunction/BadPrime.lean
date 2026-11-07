import LeanBridge.ForMathlib.NumberTheory.LFunction.Primitive

/-!
# The bad primes of an analytic L-function

The bad primes of an analytic L-function are the primes that divide its conductor `N`. They are
determined by the L-function itself, although the conductor is part of its Selberg data: the Euler
factor `Fₚ` at a prime `p` has degree at most the degree `d` of the L-function, with equality
exactly when `p ∤ N`, so `p ∣ N` exactly when the coefficient of `x ^ d` of `Fₚ` vanishes, and both
`Fₚ` (the inverse of `∑ₖ a_{pᵏ} xᵏ`) and `d` are determined by the Dirichlet coefficients `aₙ`.
This rests on the axiom `AnalyticLFunction.exists_eulerFactor` on the degrees of the Euler factors,
the shape of the Euler product that the LMFDB only expects (LMFDB `lfunction.euler_product`), and so
holds for the analytic L-functions in the sense of `AnalyticLFunction`.

## Main definitions

* `AnalyticLFunction.badPrimes` (LMFDB `lfunction.bad_prime`): the bad primes of an analytic
  L-function.

## Main results

* `AnalyticLFunction.dvd_conductor_iff`: a prime divides the conductor exactly when the coefficient
  of `x ^ d` of its Euler factor vanishes.
* `AnalyticLFunction.badPrimes_eq_of_coeff_eq`: the bad primes are determined by the Dirichlet
  coefficients.
* `AnalyticLFunction.badPrimes_eq_of_toFun_eq`: the bad primes are determined by the L-function on
  the half-plane `re s > 1`.
-/

open Filter

namespace AnalyticLFunction

variable (L : AnalyticLFunction) {L' : AnalyticLFunction} {p : ℕ}

/-- The **bad primes** (LMFDB `lfunction.bad_prime`) of an analytic L-function: the primes that
divide its conductor. By the axiom `exists_eulerFactor` on the degrees of the Euler factors, they
are determined by the Dirichlet coefficients (`badPrimes_eq_of_coeff_eq`), hence by the L-function
(`badPrimes_eq_of_toFun_eq`). -/
def badPrimes : Finset ℕ :=
  L.conductor.primeFactors

lemma mem_badPrimes : p ∈ L.badPrimes ↔ p.Prime ∧ p ∣ L.conductor := by
  simp [badPrimes, conductor, L.selbergData.conductor_pos.ne']

/-- A prime divides the conductor exactly when the coefficient of `x ^ d` of its Euler factor
vanishes, where `d` is the degree. -/
lemma dvd_conductor_iff (hp : p.Prime) :
    p ∣ L.conductor ↔ PowerSeries.coeff L.degree (L.eulerFactor p) = 0 := by
  refine ⟨L.coeff_degree_eulerFactor_of_dvd hp, fun h ↦ not_not.mp fun hpN ↦ ?_⟩
  rcases L.exists_eulerFactor p hp with ⟨F, -, hFN, hF⟩
  rw [L.eulerFactor_eq hF, Polynomial.coeff_coe, degree, ← hFN.mpr hpN,
    Polynomial.coeff_natDegree, Polynomial.leadingCoeff_eq_zero] at h
  simp [h] at hF

/-- **The bad primes are determined by the Dirichlet coefficients**: two analytic L-functions with
the same coefficients `aₙ` (`n ≥ 1`) have the same bad primes, although their conductors are given
by their Selberg data. The proof uses the axiom `exists_eulerFactor` on the degrees of the Euler
factors. -/
lemma badPrimes_eq_of_coeff_eq (h : ∀ n ≠ 0, L.coeff n = L'.coeff n) :
    L.badPrimes = L'.badPrimes := by
  ext p
  rw [mem_badPrimes, mem_badPrimes]
  refine and_congr_right fun hp ↦ ?_
  rw [L.dvd_conductor_iff hp, L'.dvd_conductor_iff hp, L.degree_eq_of_coeff_eq h, eulerFactor,
    eulerFactor, funext fun k ↦ h (p ^ k) (pow_ne_zero k hp.ne_zero)]

lemma abscissaOfAbsConv_coeff_lt_top : LSeries.abscissaOfAbsConv L.coeff < ⊤ :=
  (L.LSeriesSummable_coeff (s := 2) (by simp)).abscissaOfAbsConv_le.trans_lt (by simp)

lemma coeff_eq_of_toFun_eq (h : ∀ s : ℂ, 1 < s.re → L.toFun s = L'.toFun s) {n : ℕ} (hn : n ≠ 0) :
    L.coeff n = L'.coeff n := by
  refine LSeries.eq_of_LSeries_eventually_eq L.abscissaOfAbsConv_coeff_lt_top
    L'.abscissaOfAbsConv_coeff_lt_top ?_ hn
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hx' : 1 < (x : ℂ).re := by
    simpa using hx
  rw [← L.toFun_eq_LSeries hx', ← L'.toFun_eq_LSeries hx', h x hx']

/-- **The bad primes are determined by the L-function**: two analytic L-functions that agree on
the half-plane `re s > 1` have the same bad primes. -/
lemma badPrimes_eq_of_toFun_eq (h : ∀ s : ℂ, 1 < s.re → L.toFun s = L'.toFun s) :
    L.badPrimes = L'.badPrimes :=
  L.badPrimes_eq_of_coeff_eq fun _ hn ↦ L.coeff_eq_of_toFun_eq h hn

end AnalyticLFunction
