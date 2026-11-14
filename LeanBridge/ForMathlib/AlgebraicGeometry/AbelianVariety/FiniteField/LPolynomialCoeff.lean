import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.FiniteField.WeilPolynomial

/-!
# The constant term of the L-polynomial of an abelian variety over a finite field

The L-polynomial `L_A(t) = det(1 - t F | T_ℓ A)` of an abelian variety `A` over a finite field
(LMFDB `av.fq.l-polynomial`) has constant term `1`, the value of `det(1 - t F)` at `t = 0`. This is
why the LMFDB's search by the initial coefficients of the L-polynomial (LMFDB
`av.fq.initial_coefficients`) leaves out this term: the coefficients are listed in increasing order
of degree, starting with the coefficient of `t`. The L-polynomial is the reverse of the Weil
polynomial, and its constant term is the leading coefficient of the Weil polynomial.

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.HasLPolynomial.coeff_zero_eq_one` (LMFDB
  `av.fq.initial_coefficients`): the L-polynomial has constant term `1`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.HasWeilPolynomial.coeff_zero_reverse`: the reverse of
  the Weil polynomial has constant term `1`.
-/

open Polynomial

namespace TauCeti.AlgebraicGeometry.AbelianVariety

variable {K : Type*} [Field K] [Fintype K] {A : AbelianVariety K} {h L : ℤ[X]}

/-- **The L-polynomial of an abelian variety over a finite field has constant term `1`** (LMFDB
`av.fq.initial_coefficients`): `det(1 - t F)` takes the value `1` at `t = 0`. -/
lemma HasLPolynomial.coeff_zero_eq_one (hL : A.HasLPolynomial L) : L.coeff 0 = 1 :=
  of_forall_prime_natCast_ne_zero K fun ℓ _ hℓ ↦ by
    rcases hL ℓ hℓ with ⟨_, _, hb⟩
    have h₀ : ((L.coeff 0 : ℤ) : ℤ_[ℓ]) = 1 := by
      rw [← eq_intCast (Int.castRingHom ℤ_[ℓ]), ← coeff_map, ← hb, coeff_zero_eq_eval_zero,
        Matrix.eval_charpolyRev]
    exact_mod_cast h₀

/-- **The reverse of the Weil polynomial of an abelian variety over a finite field has constant
term `1`**: it is the L-polynomial. -/
lemma HasWeilPolynomial.coeff_zero_reverse (hh : A.HasWeilPolynomial h) : h.reverse.coeff 0 = 1 :=
  hh.hasLPolynomial_reverse.coeff_zero_eq_one

end TauCeti.AlgebraicGeometry.AbelianVariety
