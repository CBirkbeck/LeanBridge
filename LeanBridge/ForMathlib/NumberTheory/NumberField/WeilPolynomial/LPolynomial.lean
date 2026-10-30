import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial

/-!
# The L-polynomial of a Weil polynomial

The L-polynomial `L_A(t) = det(1 - t F_q | H¹(A_{𝔽̄_q}, ℚ_ℓ))` of an abelian variety `A` of
dimension `g` over `𝔽_q` (LMFDB `av.fq.l-polynomial`) is the reverse `t^{2g} P_A(1/t)` of its Weil
polynomial `P_A(t) = det(t - F | T_ℓ A)` (LMFDB `av.fq.weil_polynomial`), a Weil `q`-polynomial of
degree `2g` by Weil's theorem. This file proves the properties of the reverse of a Weil
`q`-polynomial `h` that the knowl states: its constant term is `1`, its degree is that of `h` when
`q ≠ 0`, and its complex roots have absolute value `q^{-1/2}`; and `h` is the reverse of its
reverse, so that the L-polynomial determines the Weil polynomial. The L-polynomial of an abelian
variety itself, relative to its Tate modules, is
`TauCeti.AlgebraicGeometry.AbelianVariety.HasLPolynomial`.

## Main results

* `Polynomial.reverse_reverse`: a polynomial with nonzero constant term is the reverse of its
  reverse.
* `Polynomial.IsWeilPolynomial.coeff_zero_reverse`: the reverse of a Weil polynomial has constant
  term `1`.
* `Polynomial.IsWeilPolynomial.coeff_zero_ne_zero`: a Weil `q`-polynomial, `q ≠ 0`, has a nonzero
  constant term.
* `Polynomial.IsWeilPolynomial.natDegree_reverse`: the reverse of a Weil `q`-polynomial, `q ≠ 0`,
  has the same degree.
* `Polynomial.IsWeilPolynomial.norm_eq_inv_sqrt_of_mem_roots_reverse`: the complex roots of the
  reverse of a Weil `q`-polynomial have absolute value `q^{-1/2}`.
-/

namespace Polynomial

variable {R S : Type*} [Semiring R] [Semiring S] {f : R[X]} {q : ℕ} {h : ℤ[X]}

/-- **A polynomial with nonzero constant term is the reverse of its reverse**: reversing does not
lower its degree, as its trailing degree is `0`. -/
lemma reverse_reverse (hf : f.coeff 0 ≠ 0) : f.reverse.reverse = f := by
  rw [reverse, reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hf), Nat.sub_zero, reverse,
    reflect_reflect]

lemma reverse_map_of_injective {φ : R →+* S} (hφ : Function.Injective φ) :
    (f.map φ).reverse = f.reverse.map φ := by
  rw [reverse, reverse, natDegree_map_eq_of_injective hφ, reflect_map]

namespace IsWeilPolynomial

/-- **The L-polynomial has constant term `1`** (LMFDB `av.fq.l-polynomial`): the reverse of a Weil
polynomial, a monic polynomial, has constant term `1`. -/
lemma coeff_zero_reverse (hh : h.IsWeilPolynomial q) : h.reverse.coeff 0 = 1 :=
  h.coeff_zero_reverse.trans hh.1.leadingCoeff

/-- **A Weil `q`-polynomial, `q ≠ 0`, has a nonzero constant term**: `0` is not one of its complex
roots, which have absolute value `√q`. -/
lemma coeff_zero_ne_zero (hh : h.IsWeilPolynomial q) (hq : q ≠ 0) : h.coeff 0 ≠ 0 := by
  intro h0
  have hr : (0 : ℂ) ∈ (h.map (Int.castRingHom ℂ)).roots := by
    rw [mem_roots (hh.1.map _).ne_zero, IsRoot, ← coeff_zero_eq_eval_zero, coeff_map, h0, map_zero]
  have h₁ : √(q : ℝ) = 0 := (hh.2 0 hr).symm.trans norm_zero
  exact hq <| Nat.cast_eq_zero.mp <| (Real.sqrt_eq_zero (Nat.cast_nonneg q)).mp h₁

/-- **The L-polynomial has the degree of the Weil polynomial** (LMFDB `av.fq.l-polynomial`): the
reverse of a Weil `q`-polynomial, `q ≠ 0`, has the same degree, `2g` for the Weil polynomial of an
abelian variety of dimension `g`. -/
lemma natDegree_reverse (hh : h.IsWeilPolynomial q) (hq : q ≠ 0) :
    h.reverse.natDegree = h.natDegree := by
  rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr (hh.coeff_zero_ne_zero hq)),
    Nat.sub_zero]

/-- **The complex roots of the L-polynomial have absolute value `q^{-1/2}`** (LMFDB
`av.fq.l-polynomial`): they are the inverses of the complex roots of the Weil `q`-polynomial. -/
lemma norm_eq_inv_sqrt_of_mem_roots_reverse (hh : h.IsWeilPolynomial q) {z : ℂ}
    (hz : z ∈ (h.reverse.map (Int.castRingHom ℂ)).roots) : ‖z‖ = (√q)⁻¹ := by
  have hz₀ : z ≠ 0 := by
    rintro rfl
    have h₁ : (h.reverse.map (Int.castRingHom ℂ)).IsRoot 0 := (mem_roots'.mp hz).2
    rw [IsRoot, ← coeff_zero_eq_eval_zero, coeff_map, hh.coeff_zero_reverse, map_one] at h₁
    exact one_ne_zero h₁
  let i : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz₀)
  have h₁ : eval₂ (Int.castRingHom ℂ) (⅟z⁻¹) h.reverse = 0 := by
    rw [invOf_eq_inv, inv_inv, ← eval_map]
    exact (mem_roots'.mp hz).2
  have h₂ : z⁻¹ ∈ (h.map (Int.castRingHom ℂ)).roots := by
    rw [mem_roots (hh.1.map _).ne_zero, IsRoot, eval_map]
    exact (eval₂_reverse_eq_zero_iff _ _ _).mp h₁
  rw [← inv_inv z, norm_inv, hh.2 _ h₂]

end IsWeilPolynomial

end Polynomial
