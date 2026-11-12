import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Eisenstein polynomials are irreducible over the fraction field

The LMFDB (`lf.eisenstein_polynomial`) calls a polynomial `a_n x^n + ⋯ + a_0` over a domain `D`
Eisenstein at a prime ideal `P` if `a_n ∉ P`, `a_i ∈ P` for `i < n` and `a_0 ∉ P²`, which is
Mathlib's `Polynomial.IsEisensteinAt`, and states that it is then irreducible over the fraction
field `F` of `D`. This needs a positive degree, since a constant outside `P` is Eisenstein of
degree `0`, and a hypothesis on `D`: over `D = k[t², t³]`, with `P = (t², t³)`, the polynomial
`x² - t²` is Eisenstein but is `(x - t)(x + t)` over `k(t)`. Mathlib proves the irreducibility in
`D[x]` of a primitive Eisenstein polynomial of positive degree,
`Polynomial.IsEisensteinAt.irreducible`. This file proves the two standard correct versions over
`F`.

Over a GCD domain, such as a unique factorization domain, an Eisenstein polynomial of positive
degree is irreducible over `F`, whatever its content: the content divides the leading coefficient,
so it lies outside `P`, and the primitive part is again Eisenstein, so it is irreducible in `D[x]`,
and then over `F` by Gauss's lemma,
`Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map`.

Over an integrally closed domain, a monic Eisenstein polynomial of positive degree is irreducible
over `F`, by Gauss's lemma for monic polynomials,
`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`. Monicity cannot be dropped: over
the normal domain `k[x, y, z]/(xy - z²)`, for `k` of characteristic not `2`, the polynomial
`yT² + 2zT + x` is primitive and Eisenstein at the prime `(x, z)`, but it is `y (T + z/y)²` over
the fraction field.

## Main results

* `Polynomial.IsEisensteinAt.irreducible_map` (LMFDB `lf.eisenstein_polynomial`): over a GCD
  domain, an Eisenstein polynomial of positive degree is irreducible over the fraction field.
* `Polynomial.IsEisensteinAt.irreducible_map_of_monic` (LMFDB `lf.eisenstein_polynomial`): over an
  integrally closed domain, a monic Eisenstein polynomial of positive degree is irreducible over
  the fraction field.
-/

namespace Polynomial

variable {R : Type*} [CommRing R] {P : Ideal R} {f : R[X]}

lemma isEisensteinAt_C {a : R} (ha : a ∉ P) : (C a).IsEisensteinAt P where
  leading := by
    rwa [leadingCoeff_C]
  mem h := by
    simp at h
  notMem h := ha <| Ideal.pow_le_self two_ne_zero <| by rwa [coeff_C_zero] at h

variable [IsDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- **An Eisenstein polynomial over a GCD domain is irreducible over the fraction field**
(LMFDB `lf.eisenstein_polynomial`): over a GCD domain `R` with fraction field `K`, such as a unique
factorization domain, a polynomial of positive degree that is Eisenstein at a prime ideal is
irreducible over `K`, whatever its content. -/
lemma IsEisensteinAt.irreducible_map [IsGCDMonoid R] (hf : f.IsEisensteinAt P) (hP : P.IsPrime)
    (hd : 0 < f.natDegree) : Irreducible (f.map (algebraMap R K)) := by
  let _ : NormalizedGCDMonoid R := Classical.arbitrary _
  have hc : f.content ∉ P := fun h ↦ hf.leading <| P.mem_of_dvd (content_dvd_coeff _) h
  have hg : f.primPart.IsEisensteinAt P := by
    refine ⟨fun h ↦ hf.leading ?_, fun {n} hn ↦ (hP.mem_or_mem ?_).resolve_left hc,
      fun h ↦ hf.notMem ?_⟩
    · rw [f.eq_C_content_mul_primPart, leadingCoeff_mul, leadingCoeff_C]
      exact P.mul_mem_left _ h
    · rw [← coeff_C_mul, ← f.eq_C_content_mul_primPart]
      exact hf.mem <| f.natDegree_primPart ▸ hn
    · rw [f.eq_C_content_mul_primPart, coeff_C_mul]
      exact (P ^ 2).mul_mem_left _ h
  have hc₀ : algebraMap R K f.content ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr <|
      content_eq_zero_iff.not.mpr <| ne_zero_of_natDegree_gt hd
  rw [f.eq_C_content_mul_primPart, Polynomial.map_mul, map_C, irreducible_isUnit_mul <|
    isUnit_C.mpr hc₀.isUnit, ← f.isPrimitive_primPart.irreducible_iff_irreducible_map_fraction_map]
  exact hg.irreducible hP f.isPrimitive_primPart <| f.natDegree_primPart.symm ▸ hd

/-- **A monic Eisenstein polynomial over an integrally closed domain is irreducible over the
fraction field** (LMFDB `lf.eisenstein_polynomial`): over an integrally closed domain `R` with
fraction field `K`, a monic polynomial of positive degree that is Eisenstein at a prime ideal is
irreducible over `K`. -/
lemma IsEisensteinAt.irreducible_map_of_monic [IsIntegrallyClosed R] (hf : f.IsEisensteinAt P)
    (hP : P.IsPrime) (hm : f.Monic) (hd : 0 < f.natDegree) : Irreducible (f.map (algebraMap R K)) :=
  hm.irreducible_iff_irreducible_map_fraction_map.mp <| hf.irreducible hP hm.isPrimitive hd

end Polynomial
