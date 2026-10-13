/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanBridge.IdealArithmetic.DedekindProject.Discriminant.Discriminant
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Separable

/-!
# Separability of the reduction of an integer polynomial modulo a prime

We prove `separable_map_of_discr_ne_zero`: if a prime `p` does not divide the discriminant of a
monic integer polynomial `f` (equivalently, the image of `f.discr` in `ZMod p` is nonzero), then
the reduction `f mod p` is a separable polynomial over the field `ZMod p`.

This fills an API gap needed for the Dedekind cycle-type theorem (`L_b3`).

## Implementation notes

The mathematical statement is true even when `p ∣ f.natDegree`, but in that case the derivative of
`f mod p` has strictly smaller degree than `f.natDegree - 1`, so the naive
`discr (f.map φ) = φ f.discr` identity from `discriminant_map''` does not apply (its side condition
`φ (derivative f).leadingCoeff ≠ 0` fails). We avoid this by working with the *explicit-degree*
resultant `resultant · · n (n-1)`, which mathlib's `Polynomial.resultant_deriv` relates to `discr`
over any commutative ring using only `0 < degree`, and which commutes with `Polynomial.map` on the
nose (`Polynomial.resultant_map_map`). Coprimality of the reduction with its derivative is then
extracted from `Polynomial.exists_mul_add_mul_eq_C_resultant`, whose hypotheses are mere degree
*upper* bounds and hence insensitive to the degree drop.
-/

namespace IdealArithmetic.Galois

open Polynomial

variable {K : Type*} [Field K]

/-- If a ring hom `φ : ℤ →+* K` into a field sends the discriminant of a monic integer polynomial `f`
to a nonzero element, then `f.map φ` is separable. Two uses in the Galois-certificate layer:
`φ = algebraMap ℤ ℚ` gives `disc f ≠ 0 ⟹ f` separable over `ℚ` (whence `IsGalois` of the splitting
field); `φ = Int.castRingHom (ZMod p)` gives `p ∤ disc f ⟹ f mod p` separable (the `hsepf` of R3). -/
theorem separable_map_of_discr_ne_zero (f : Polynomial ℤ) (hf : f.Monic)
    (hdeg : f.natDegree ≠ 0) (φ : ℤ →+* K) (hdisc : φ f.discr ≠ 0) :
    (f.map φ).Separable := by
  have hn0 : 0 < f.natDegree := Nat.pos_of_ne_zero hdeg
  have hdegf : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hn0
  -- The resultant of `f mod p` with its derivative, computed with the *formal* degrees `n, n-1`,
  -- is nonzero: it equals `± φ f.discr` by naturality of the resultant and `resultant_deriv`.
  have hne : resultant (f.map φ) (derivative (f.map φ)) f.natDegree (f.natDegree - 1) ≠ 0 := by
    rw [derivative_map, resultant_map_map, resultant_deriv hdegf, hf.leadingCoeff, mul_one]
    simp only [map_mul, map_pow, map_neg, map_one]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hdisc
  -- The reduction is monic of the same degree.
  have hgdeg : (f.map φ).natDegree = f.natDegree := hf.natDegree_map φ
  -- A Bézout combination witnessing coprimality of `f mod p` with its derivative.
  obtain ⟨a, b, -, -, hab⟩ :=
    exists_mul_add_mul_eq_C_resultant (f := f.map φ) (g := derivative (f.map φ))
      (m := f.natDegree) (n := f.natDegree - 1) (le_of_eq hgdeg)
      (by rw [← hgdeg]; exact natDegree_derivative_le _) (Or.inl hdeg)
  set c := resultant (f.map φ) (derivative (f.map φ)) f.natDegree (f.natDegree - 1) with hc
  rw [separable_def']
  refine ⟨C c⁻¹ * a, C c⁻¹ * b, ?_⟩
  calc (C c⁻¹ * a) * (f.map φ) + (C c⁻¹ * b) * (derivative (f.map φ))
      = C c⁻¹ * ((f.map φ) * a + (derivative (f.map φ)) * b) := by ring
    _ = C c⁻¹ * C c := by rw [hab]
    _ = C (c⁻¹ * c) := by rw [← C_mul]
    _ = 1 := by rw [inv_mul_cancel₀ hne, C_1]

end IdealArithmetic.Galois
