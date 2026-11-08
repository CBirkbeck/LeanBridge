import LeanBridge.ForMathlib.RingTheory.Polynomial.EisensteinForm
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Polynomials of Eisenstein form are irreducible

A polynomial `f = ν ^ e + g_{e - 1} ν ^ (e - 1) + ⋯ + g_0` of Eisenstein form over a local domain
`R` (LMFDB `lf.eisenstein_form`) reduces to the power `ν̄ ^ e` of the irreducible reduction of `ν`,
and its remainder modulo `ν` is `g_0`, which is not zero modulo `𝔪 ^ 2`. By Mathlib's generalised
Schönemann–Eisenstein criterion `Polynomial.generalizedEisenstein`, `f` is irreducible in `R[X]`,
and so, by Gauss's lemma, in `F[X]` for the fraction field `F` of an integrally closed `R`, such as
the ring of integers of a `p`-adic field.

## Main theorems

* `Polynomial.IsEisensteinForm.irreducible_map` (LMFDB `lf.eisenstein_form`): a polynomial of
  Eisenstein form over an integrally closed local domain is irreducible over its fraction field.
-/

open IsLocalRing Finset

namespace Polynomial

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsDomain R] {f : R[X]}

open Ideal in
lemma IsEisensteinForm.irreducible (hf : f.IsEisensteinForm) : Irreducible f := by
  rcases hf with ⟨hfm, ν, e, g, hν, hνirr, he, hg, hdeg, ⟨n, hn⟩, hfeq⟩
  have hres : algebraMap R (ResidueField R) = residue R := ResidueField.algebraMap_eq R
  have hmap : f.map (residue R) = ν.map (residue R) ^ e := by
    have hgi (i : ℕ) (hi : i ∈ range e) : (g i * ν ^ i).map (residue R) = 0 := by
      have hzero : (g i).map (residue R) = 0 := by
        ext m
        rw [coeff_map, coeff_zero, residue_eq_zero_iff]
        exact hg i (mem_range.1 hi) m
      rw [Polynomial.map_mul, hzero, zero_mul]
    rw [hfeq, Polynomial.map_add, Polynomial.map_sum, sum_eq_zero hgi, add_zero, Polynomial.map_pow]
  have hmod : f %ₘ ν = g 0 := by
    rcases Nat.exists_eq_succ_of_ne_zero he.ne' with ⟨e', rfl⟩
    refine (div_modByMonic_unique (ν ^ e' + ∑ i ∈ range e', g (i + 1) * ν ^ i) (g 0) hν
      ⟨?_, hdeg 0 he⟩).2
    rw [hfeq, sum_range_succ', mul_add, mul_sum, pow_succ', pow_zero, mul_one]
    simp_rw [mul_left_comm ν, ← pow_succ']
    ring1
  refine generalizedEisenstein (K := ResidueField R) (q := ν) (p := e) (hres ▸ hνirr) hν
    hfm.isPrimitive ((Nat.mul_pos he hνirr.natDegree_pos).trans_le ?_) ?_ ?_ ?_
  · rw [← (hν.map (residue R)).natDegree_pow, ← hmap]
    exact natDegree_map_le
  · rw [hfm.leadingCoeff, map_one]
    exact one_ne_zero
  · rw [hres, hmap, hfm.leadingCoeff, map_one, C_1, one_mul]
  · rw [hmod, hres, ker_residue]
    intro h
    apply hn
    rw [← Quotient.eq_zero_iff_mem, ← coeff_map, h, coeff_zero]

variable (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F] [IsIntegrallyClosed R]

/-- **A polynomial of Eisenstein form is irreducible** (LMFDB `lf.eisenstein_form`): over an
integrally closed local domain `R` with fraction field `F`, such as the ring of integers of a
`p`-adic field, a polynomial of Eisenstein form is irreducible in `F[X]`. -/
lemma IsEisensteinForm.irreducible_map (hf : f.IsEisensteinForm) :
    Irreducible (f.map (algebraMap R F)) :=
  (hf.1.irreducible_iff_irreducible_map_fraction_map).1 hf.irreducible

end Polynomial
