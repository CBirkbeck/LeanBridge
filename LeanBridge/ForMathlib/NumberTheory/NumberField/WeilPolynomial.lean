import Mathlib.NumberTheory.MahlerMeasure

/-!
# Weil polynomials

A Weil `q`-polynomial is a monic integer polynomial all of whose complex roots have absolute value
`√q`. The characteristic polynomial of the Frobenius endomorphism of an abelian variety over `𝔽_q`
is one, by Weil's Riemann hypothesis for abelian varieties; which Weil polynomials arise in this way
is the subject of Honda–Tate theory, which this file does not touch.

## Main definitions

* `Polynomial.IsWeilPolynomial` (LMFDB `nf.weil_polynomial`).

## Main results

* `Polynomial.finite_setOf_isWeilPolynomial`: there are only finitely many Weil `q`-polynomials of
  each degree. The Mahler measure of a Weil `q`-polynomial of degree `d` is at most
  `max 1 √q ^ d`, so this is an instance of Northcott's theorem
  `Polynomial.finite_mahlerMeasure_le`.
-/

namespace Polynomial

variable (q : ℕ) {P : ℤ[X]}

variable (P) in
/-- A **Weil `q`-polynomial** (LMFDB `nf.weil_polynomial`) is a monic polynomial with integer
coefficients whose complex roots all have absolute value `√q`.

The LMFDB considers prime powers `q`, the cardinalities of finite fields; the definition makes sense
for every natural number `q`. -/
def IsWeilPolynomial : Prop :=
  P.Monic ∧ ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots, ‖z‖ = √q

lemma Monic.mahlerMeasure_map_le (hP : P.Monic) {R : ℝ}
    (h : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots, ‖z‖ ≤ R) :
    (P.map (Int.castRingHom ℂ)).mahlerMeasure ≤ max 1 R ^ P.natDegree := by
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, (hP.map _).leadingCoeff, norm_one, one_mul]
  refine (Multiset.prod_map_le_prod_map₀ _ (fun _ ↦ max 1 R)
    (fun _ _ ↦ zero_le_one.trans (le_max_left _ _)) fun z hz ↦ max_le_max_left 1 (h z hz)).trans ?_
  rw [Multiset.map_const', Multiset.prod_replicate]
  exact pow_le_pow_right₀ (le_max_left 1 _) ((card_roots' _).trans natDegree_map_le)

variable {q} in
lemma IsWeilPolynomial.mahlerMeasure_le (hP : P.IsWeilPolynomial q) :
    (P.map (Int.castRingHom ℂ)).mahlerMeasure ≤ max 1 √q ^ P.natDegree :=
  hP.1.mahlerMeasure_map_le fun z hz ↦ (hP.2 z hz).le

/-- There are only finitely many Weil `q`-polynomials of each degree. -/
lemma finite_setOf_isWeilPolynomial (d : ℕ) :
    {P : ℤ[X] | P.natDegree = d ∧ P.IsWeilPolynomial q}.Finite :=
  (finite_mahlerMeasure_le d ⟨max 1 √q ^ d, by positivity⟩).subset fun _ hP ↦
    ⟨hP.1.le, hP.1 ▸ hP.2.mahlerMeasure_le⟩

end Polynomial
