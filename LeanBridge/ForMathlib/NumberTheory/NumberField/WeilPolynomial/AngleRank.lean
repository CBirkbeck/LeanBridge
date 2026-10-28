import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.NumberTheory.NumberField.Basic
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial

/-!
# Frobenius angles, angle rank and number field of a Weil polynomial

The complex roots `α₁, …, α_{2g}` of a Weil `q`-polynomial have absolute value `√q`, so they are
determined by their arguments, the Frobenius angles. The angle rank of a set of nonzero complex
numbers is the dimension of the `ℚ`-span of their normalised arguments `Arg(αᵢ) / 2π` and `1`,
minus `1`, and the angle corank of a Weil polynomial of degree `2g` is `g` minus its angle rank. An
irreducible Weil polynomial defines a number field.

The LMFDB attaches these to an isogeny class of abelian varieties over `𝔽_q` through its Weil
polynomial (LMFDB `av.fq.weil_polynomial`), the characteristic polynomial of its Frobenius, which is
not available here; they are defined in terms of the polynomial, as the LMFDB computes them. That
the angle rank `δ` of the Weil polynomial of an abelian variety of dimension `g` satisfies
`0 ≤ δ ≤ g`, with `δ = 0` if and only if the abelian variety is supersingular, is not formalised.

## Main definitions

* `Polynomial.frobeniusAngles` (LMFDB `av.fq.frobenius_angles`).
* `Complex.angleRank` and `Polynomial.angleRank` (LMFDB `av.fq.angle_rank`).
* `Polynomial.angleCorank` (LMFDB `av.fq.angle_rank`).
* `Polynomial.WeilNumberField` (LMFDB `av.fq.number_field`).

## Main results

* `Polynomial.IsWeilPolynomial.sqrt_mul_exp_arg_mul_I`: a complex root of a Weil `q`-polynomial is
  determined by its Frobenius angle, as `√q exp(i Arg α)`.
-/

open Complex

namespace Complex

/-- The **angle rank** (LMFDB `av.fq.angle_rank`) of a set `S` of nonzero complex numbers: the
dimension of the `ℚ`-span of `1` and the normalised arguments `Arg(α) / 2π` of the `α ∈ S`, minus
`1`.

The LMFDB considers finite sets of nonzero complex numbers; the definition makes sense for every set
of complex numbers, and is `0` when the span is infinite-dimensional. -/
noncomputable def angleRank (S : Set ℂ) : ℕ :=
  Module.finrank ℚ (Submodule.span ℚ (insert 1 ((fun α ↦ α.arg / (2 * Real.pi)) '' S))) - 1

end Complex

namespace Polynomial

variable {q : ℕ} (h : ℤ[X])

/-- The **Frobenius angles** (LMFDB `av.fq.frobenius_angles`) of a polynomial `h ∈ ℤ[x]`: the
multiset of the arguments `Arg(αᵢ) ∈ (-π, π]` of its complex roots `αᵢ`, with multiplicity. When `h`
is a Weil `q`-polynomial, such as the Weil polynomial of an isogeny class of abelian varieties over
`𝔽_q`, its roots have absolute value `√q` and are determined by their Frobenius angles
(`Polynomial.IsWeilPolynomial.sqrt_mul_exp_arg_mul_I`). -/
noncomputable def frobeniusAngles : Multiset ℝ :=
  (h.map (Int.castRingHom ℂ)).roots.map arg

/-- The **angle rank** (LMFDB `av.fq.angle_rank`) of a polynomial `h ∈ ℤ[x]`: the angle rank
(`Complex.angleRank`) of the set of its nonzero complex roots. -/
noncomputable def angleRank : ℕ :=
  Complex.angleRank {α : ℂ | α ∈ (h.map (Int.castRingHom ℂ)).roots ∧ α ≠ 0}

/-- The **angle corank** (LMFDB `av.fq.angle_rank`) of a polynomial `h ∈ ℤ[x]` of degree `2g`: the
difference `g - δ` between `g` and its angle rank `δ` (`Polynomial.angleRank`). The LMFDB defines it
for the Weil polynomial of an abelian variety of dimension `g`, which has degree `2g`. -/
noncomputable def angleCorank : ℕ :=
  h.natDegree / 2 - h.angleRank

/-- The **number field** (LMFDB `av.fq.number_field`) of an irreducible polynomial `h ∈ ℤ[x]`: the
extension `ℚ[x] / (h)` of `ℚ` that it defines, a number field when `h` is irreducible over `ℚ`. The
LMFDB attaches it to an isogeny class of abelian varieties over `𝔽_q` with irreducible Weil
polynomial `h`. -/
abbrev WeilNumberField : Type :=
  AdjoinRoot (h.map (Int.castRingHom ℚ))

variable {h}

/-- A complex root `α` of a Weil `q`-polynomial is determined by its Frobenius angle: it is
`√q exp(i Arg α)`. -/
lemma IsWeilPolynomial.sqrt_mul_exp_arg_mul_I (hh : h.IsWeilPolynomial q) {α : ℂ}
    (hα : α ∈ (h.map (Int.castRingHom ℂ)).roots) : (√q : ℂ) * exp (α.arg * I) = α := by
  rw [← hh.2 α hα, norm_mul_exp_arg_mul_I]

end Polynomial
