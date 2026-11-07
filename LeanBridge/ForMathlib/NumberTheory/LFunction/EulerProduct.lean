import LeanBridge.ForMathlib.NumberTheory.LFunction.CriticalStrip
import LeanBridge.ForMathlib.NumberTheory.LFunction.SymmetricPower

/-!
# The shape of the Euler product of an analytic L-function

For `re s > 1`, an analytic L-function `L` of degree `d` and conductor `N` is the product
`L(s) = ∏ₚ L_p(s)` of its Euler factors (or local factors) `L_p(s) = ∑ₖ a_{pᵏ} p ^ (-k s)`
(`AnalyticLFunction.hasProd_tsum_term_prime_pow`). Each Euler factor is
`L_p(s) = ∏ₙ (1 - αₙ(p) p ^ (-s))⁻¹`, the product over the `d_p` reciprocal roots `αₙ(p)` of the
polynomial Euler factor (`AnalyticLFunction.satakeParameters`), where `d_p = d` for `p ∤ N` and
`d_p < d` for `p ∣ N`.

The degrees `d_p` come from the axiom `AnalyticLFunction.exists_eulerFactor`, which builds this
shape of the Euler product, without bounds on the `αₙ(p)`, into the definition of an analytic
L-function, whereas the LMFDB only expects it. The LMFDB moreover expects `|αₙ(p)| = 1` for `p ∤ N`
and `|αₙ(p)| ≤ 1` for `p ∣ N`. These are the Ramanujan conjectures for `L`, open in general, and
they are not formalised here.

## Main results

* `AnalyticLFunction.card_satakeParameters_lt`: at a prime dividing the conductor there are fewer
  than `d` reciprocal roots.
* `AnalyticLFunction.tsum_term_prime_pow_eq_prod`: the Euler factor is
  `L_p(s) = ∏ₙ (1 - αₙ(p) p ^ (-s))⁻¹` for `re s > 1`.
* `AnalyticLFunction.hasProd_prod_satakeParameters` (LMFDB `lfunction.euler_product`): the Euler
  product `L(s) = ∏ₚ ∏ₙ (1 - αₙ(p) p ^ (-s))⁻¹` for `re s > 1`.
-/

open Complex Polynomial TauCeti LSeries

namespace AnalyticLFunction

variable (L : AnalyticLFunction) {p : ℕ} {s : ℂ}

/-- **At a prime dividing the conductor there are fewer than `d` reciprocal roots**, `d` the
degree: the Euler factor then has degree `d_p < d`. -/
lemma card_satakeParameters_lt (hp : p.Prime) (hpN : p ∣ L.conductor) :
    (L.satakeParameters p).card < L.degree := by
  rcases L.exists_eulerFactor p hp with ⟨F, hFd, hFN, hF⟩
  rw [satakeParameters, Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree,
    eulerPolynomial_eq hp hF]
  exact hFd.lt_of_ne fun h ↦ hFN.mp h hpN

/-- **The Euler factor is `L_p(s) = ∏ₙ (1 - αₙ(p) p ^ (-s))⁻¹`** for `re s > 1`, the product over
the reciprocal roots `αₙ(p)` of the polynomial Euler factor. -/
lemma tsum_term_prime_pow_eq_prod (hs : 1 < s.re) (hp : p.Prime) :
    ∑' e : ℕ, term L.coeff s (p ^ e) =
      ((L.satakeParameters p).map fun α ↦ (1 - α * (p : ℂ) ^ (-s))⁻¹).prod := by
  rcases L.exists_eulerFactor p hp with ⟨F, -, -, hF⟩
  have hsum : Summable fun e : ℕ ↦ ‖term L.coeff s (p ^ e)‖ :=
    (L.LSeriesSummable_coeff hs).norm.comp_injective (Nat.pow_right_injective hp.two_le)
  simp_rw [term_pow _ hp.ne_zero] at hsum ⊢
  rw [Multiset.prod_map_inv, eq_inv_of_mul_eq_one_right (eval_mul_tsum_eq_one hF hsum),
    ← L.eulerPolynomial_eq hp hF, ← prod_one_sub_C_mul_X_satakeParameters, eval_multiset_prod,
    Multiset.map_map]
  simp

/-- **The Euler product of an analytic L-function** (LMFDB `lfunction.euler_product`): for
`re s > 1`, `L(s) = ∏ₚ L_p(s)` with Euler factors `L_p(s) = ∏ₙ (1 - αₙ(p) p ^ (-s))⁻¹`, the
product over the `d_p` reciprocal roots `αₙ(p)` of the polynomial Euler factor, where `d_p` is the
degree `d` for `p` not dividing the conductor (`card_satakeParameters`) and `d_p < d` otherwise
(`card_satakeParameters_lt`). The bounds `|αₙ(p)| = 1` for `p ∤ N` and `|αₙ(p)| ≤ 1` for `p ∣ N`
that the LMFDB expects are the Ramanujan conjectures, which are not formalised. -/
lemma hasProd_prod_satakeParameters (hs : 1 < s.re) : HasProd (fun p : Nat.Primes ↦
    ((L.satakeParameters p).map fun α ↦ (1 - α * (p : ℂ) ^ (-s))⁻¹).prod) (L.toFun s) :=
  (L.hasProd_tsum_term_prime_pow hs).congr_fun fun p ↦
    (L.tsum_term_prime_pow_eq_prod hs p.prop).symm

end AnalyticLFunction
