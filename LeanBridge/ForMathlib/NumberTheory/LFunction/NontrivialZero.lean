import LeanBridge.ForMathlib.NumberTheory.LFunction.Completed
import LeanBridge.ForMathlib.NumberTheory.LFunction.CriticalStrip

/-!
# The nontrivial zeros of an analytic L-function lie in the closed critical strip

The nontrivial zeros of an analytic L-function are its zeros that are not trivial zeros, that is,
not at poles of its gamma factor. Off those poles and `s = 0, 1`, the completed L-function is
`Λ(s) = N ^ (s / 2) L_∞(s) L(s)` (`AnalyticLFunction.completed_eq_of_notMem_gammaPoles`), so a
nontrivial zero of `L` other than `0` and `1` is a zero of `Λ`, and the zeros of `Λ` lie in the
closed strip `0 ≤ re s ≤ 1`: to the right of the critical strip the Dirichlet series and the Euler
product converge absolutely and `L` does not vanish, and the functional equation reflects this to
the left. In the arithmetic normalisation of weight `w`, the L-function `s ↦ L(s - w / 2)`, the
Dirichlet series and the Euler product converge absolutely to the right of the critical strip
`w / 2 < re s < w / 2 + 1`, and the nontrivial zeros are the translates by `w / 2`, so they lie in
its closure.

These are statements about the analytic L-functions in the sense of `AnalyticLFunction`, whose
axioms include the absolute convergence of the Dirichlet series for `re s > 1`, Euler factors that
are inverses of polynomials (`AnalyticLFunction.exists_eulerFactor`), the holomorphy of `L` and `Λ`
and the functional equation.

## Main results

* `AnalyticLFunction.hasProd_tsum_term_arithmeticCoeff_prime_pow` and
  `AnalyticLFunction.summable_norm_tsum_term_arithmeticCoeff_prime_pow_sub_one`: in the arithmetic
  normalisation, to the right of its critical strip, an analytic L-function is the product of its
  Euler factors, which converges absolutely.
* `AnalyticLFunction.zeros_diff_trivialZeros_subset_closure_criticalStrip` (LMFDB
  `lfunction.critical_strip`): the nontrivial zeros lie in the closure of the critical strip.
* `AnalyticLFunction.mem_closure_arithmeticCriticalStrip` (LMFDB `lfunction.critical_strip`): in
  the arithmetic normalisation, the nontrivial zeros lie in the closure of the critical strip.
-/

open Complex Set TauCeti LSeries

namespace AnalyticLFunction

variable (L : AnalyticLFunction) {w : ℕ} {s : ℂ}

lemma closure_arithmeticCriticalStrip :
    closure (arithmeticCriticalStrip w) = re ⁻¹' Icc (w / 2) (w / 2 + 1) := by
  rw [arithmeticCriticalStrip, closure_preimage_re, closure_Ioo (by linarith)]

lemma term_arithmeticCoeff (n : ℕ) :
    term (L.arithmeticCoeff w) s n = term L.coeff (s - w / 2) n := by
  rw [sub_eq_add_neg, ← term_mul_natCast_cpow_neg, neg_neg]
  rfl

lemma one_lt_re_sub (hs : w / 2 + 1 < s.re) : 1 < (s - w / 2).re := by
  rw [sub_re, div_ofNat_re, natCast_re]
  linarith

/-- In the arithmetic normalisation of weight `w`, to the right of its critical strip, an analytic
L-function is the product of its Euler factors `∑ₖ a_{pᵏ} p ^ (k w / 2) p ^ (-k s)`. -/
lemma hasProd_tsum_term_arithmeticCoeff_prime_pow (hs : w / 2 + 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ ∑' e : ℕ, term (L.arithmeticCoeff w) s (p ^ e))
      (L.arithmeticNormalization w s) := by
  simp_rw [term_arithmeticCoeff]
  exact L.hasProd_tsum_term_prime_pow <| one_lt_re_sub hs

/-- In the arithmetic normalisation of weight `w`, to the right of its critical strip, the Euler
product of an analytic L-function converges absolutely: the series `∑ₚ |Lₚ(s) - 1|` over the primes
converges, where `Lₚ(s)` is the Euler factor `∑ₖ a_{pᵏ} p ^ (k w / 2) p ^ (-k s)`. -/
lemma summable_norm_tsum_term_arithmeticCoeff_prime_pow_sub_one (hs : w / 2 + 1 < s.re) :
    Summable fun p : Nat.Primes ↦ ‖∑' e : ℕ, term (L.arithmeticCoeff w) s (p ^ e) - 1‖ := by
  simp_rw [term_arithmeticCoeff]
  exact L.summable_norm_tsum_term_prime_pow_sub_one <| one_lt_re_sub hs

/-- **The nontrivial zeros of an analytic L-function lie in the closure of its critical strip**
(LMFDB `lfunction.critical_strip`): its zeros that are not trivial zeros, at poles of its gamma
factor, satisfy `0 ≤ re ρ ≤ 1`. Off the poles and `0` and `1` they are zeros of the completed
L-function `Λ(s) = N ^ (s / 2) L_∞(s) L(s)`, which does not vanish outside the closed strip. -/
lemma zeros_diff_trivialZeros_subset_closure_criticalStrip :
    L.zeros \ L.trivialZeros ⊆ closure criticalStrip := by
  rintro ρ ⟨hρ, hρt⟩
  rcases eq_or_ne ρ 0 with rfl | hρ₀
  · simp [closure_criticalStrip]
  rcases eq_or_ne ρ 1 with rfl | hρ₁
  · simp [closure_criticalStrip]
  refine L.mem_closure_criticalStrip_of_completed_eq_zero ?_
  rw [L.completed_eq_of_notMem_gammaPoles (fun h ↦ hρt ⟨hρ, h⟩) hρ₀ hρ₁,
    (L.mem_zeros_iff hρ₁).mp hρ, mul_zero]

/-- **In the arithmetic normalisation, the nontrivial zeros lie in the closure of the critical
strip** (LMFDB `lfunction.critical_strip`): the nontrivial zeros of the arithmetic normalisation
`s ↦ L(s - w / 2)` of weight `w`, the `s` with `s - w / 2` a nontrivial zero of `L`, satisfy
`w / 2 ≤ re s ≤ w / 2 + 1`. -/
lemma mem_closure_arithmeticCriticalStrip (hs : s - w / 2 ∈ L.zeros \ L.trivialZeros) :
    s ∈ closure (arithmeticCriticalStrip w) := by
  have h : s - w / 2 ∈ closure criticalStrip :=
    L.zeros_diff_trivialZeros_subset_closure_criticalStrip hs
  rw [closure_criticalStrip, mem_preimage, sub_re, div_ofNat_re, natCast_re, mem_Icc] at h
  rw [closure_arithmeticCriticalStrip, mem_preimage, mem_Icc]
  constructor <;> linarith [h.1, h.2]

end AnalyticLFunction
