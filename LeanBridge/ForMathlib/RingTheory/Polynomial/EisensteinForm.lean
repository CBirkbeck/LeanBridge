import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
# Polynomials of Eisenstein form

A monic polynomial `f` over the ring of integers `𝒪_K` of a `p`-adic field is of Eisenstein form
if `f = ν ^ e + g_{e - 1} ν ^ (e - 1) + ⋯ + g_1 ν + g_0` for a monic `ν` irreducible modulo the
maximal ideal, with all `g_i` divisible by a uniformiser, of degree less than `deg ν`, and with
`g_0` of minimal coefficient valuation one. Eisenstein polynomials are the case `ν = X`.

## Main definitions

* `Polynomial.IsEisensteinForm` (LMFDB `lf.eisenstein_form`).

## Main theorems

* `Polynomial.IsEisensteinAt.isEisensteinForm`: a monic Eisenstein polynomial of positive degree is
  of Eisenstein form, with `ν = X`.
-/

open IsLocalRing Finset

namespace Polynomial

variable {R : Type*} [CommRing R] [IsLocalRing R] {f : R[X]}

/-- A polynomial `f` over a local ring `R` (the LMFDB takes `R = 𝒪_K` for a `p`-adic field `K`)
is of **Eisenstein form** (LMFDB `lf.eisenstein_form`) if it is monic and there are a monic `ν`
irreducible modulo the maximal ideal `𝔪`, an integer `e ≥ 1` and polynomials `g_0, …, g_{e - 1}`
with coefficients in `𝔪` and of degree less than `deg ν`, such that
`f = ν ^ e + ∑_{i < e} g_i ν ^ i` and some coefficient of `g_0` is not in `𝔪 ^ 2`, i.e. for a
discrete valuation ring the minimal valuation of the coefficients of `g_0` is one. -/
def IsEisensteinForm (f : R[X]) : Prop :=
  f.Monic ∧ ∃ (ν : R[X]) (e : ℕ) (g : ℕ → R[X]), ν.Monic ∧ Irreducible (ν.map (residue R)) ∧
    0 < e ∧ (∀ i < e, ∀ n, (g i).coeff n ∈ maximalIdeal R) ∧ (∀ i < e, (g i).degree < ν.degree) ∧
    (∃ n, (g 0).coeff n ∉ maximalIdeal R ^ 2) ∧ f = ν ^ e + ∑ i ∈ range e, g i * ν ^ i

/-- A monic Eisenstein polynomial of positive degree is of Eisenstein form, with `ν = X`,
`e = deg f` and `g_i` the constant coefficients of `f`. -/
lemma IsEisensteinAt.isEisensteinForm (hf : f.IsEisensteinAt (maximalIdeal R)) (hm : f.Monic)
    (hd : 0 < f.natDegree) : f.IsEisensteinForm := by
  refine ⟨hm, X, f.natDegree, fun i ↦ C (f.coeff i), monic_X, ?_, hd, fun i hi n ↦ ?_,
    fun i _ ↦ ?_, ⟨0, ?_⟩, hm.as_sum⟩
  · rw [Polynomial.map_X]
    exact irreducible_X
  · rw [coeff_C]
    split_ifs
    · exact hf.mem hi
    · exact zero_mem _
  · rw [degree_X]
    exact degree_C_le.trans_lt zero_lt_one
  · rw [coeff_C_zero]
    exact hf.notMem

end Polynomial
