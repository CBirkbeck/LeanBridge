import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# The Eisenstein series `E_k`, `F_k` and `G_k`

In the theory of elliptic functions and of elliptic curves over `ℂ`, the functions that arise
naturally are the Eisenstein series `E_k`, or their alternately normalised counterparts `F_k` and
`G_k`, the quasi-modular Eisenstein series `E₂`, the discriminant function `Δ` and the elliptic
modular invariant `j` (LMFDB `mf.gl2.history.elliptic`). The knowl defines neither `F_k` nor
`G_k`. Here `E_k` is Mathlib's normalised Eisenstein series `ModularForm.E`, with constant term
`1`, and the other two are read as follows.

* `G_k(τ) = ∑_{(m, n) ≠ (0, 0)} (mτ + n)^{-k}` is the sum over the lattice `ℤτ + ℤ`, the
  Eisenstein series of the theory of elliptic functions. It is `2 ζ(k) E_k(τ)` for `k ≥ 3`.
* `F_k(τ) = -B_k/(2k) + ∑_{n ≥ 1} σ_{k-1}(n) qⁿ` is the normalisation with first Fourier
  coefficient `1`, written `F_k` by Cohen and Strömberg. It is `-(B_k/(2k)) E_k(τ)` for even
  `k ≥ 4`.

The quasi-modularity of `E₂` is LeanBridge's `ModularForm.isQuasiModularForm_E2`, and the
invariance of `j = E₄³/Δ` under `SL(2, ℤ)` is Tau Ceti's `TauCeti.ModularForm.j_smul`.

The elliptic curve of the lattice `ℤτ + ℤ` is on Tau Ceti's main branch, not at LeanBridge's pin,
and is not repeated here. There `UpperHalfPlane.periodPair` is the period pair `(τ, 1)`,
`UpperHalfPlane.G_periodPair` says that `G_k(τ)` is Mathlib's lattice sum `PeriodPair.G`,
`PeriodPair.weierstrassCurve` is the curve `y² = x³ - (g₂/4) x - g₃/4`,
`PeriodPair.equation_weierstrassP` puts `(℘(z), ℘'(z)/2)` on it, and
`UpperHalfPlane.weierstrassCurve_Δ_periodPair` and `UpperHalfPlane.weierstrassCurve_j_periodPair`
say that its discriminant is `(2π)¹² Δ(τ)` and its `j`-invariant is `j(τ)`.

## Main definitions

* `ModularForm.eisensteinF` (LMFDB `mf.gl2.history.elliptic`): the Eisenstein series `F_k`.

## Main results

* `ModularForm.eisensteinF_eq`: `F_k = -(B_k/(2k)) E_k` for even `k ≥ 4`.
* `ModularForm.tsum_eisSummand_eq_two_mul_riemannZeta_mul_E`: `G_k = 2 ζ(k) E_k` for `k ≥ 3`.

## References

* H. Cohen and F. Strömberg, *Modular forms: a classical approach*, Graduate Studies in
  Mathematics 179, AMS, 2017, Chapters 3 and 5.
* J.-P. Serre, *A course in arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
  Chapter VII.
-/

open Complex ModularForm EisensteinSeries ArithmeticFunction

open UpperHalfPlane hiding I

open scoped Real

private lemma bernoulli_ne_zero_of_even {k : ℕ} (hk : k ≠ 0) (hk2 : Even k) : bernoulli k ≠ 0 := by
  rcases hk2 with ⟨m, rfl⟩
  have hm : m ≠ 0 := by
    omega
  have hζ : riemannZeta (2 * m : ℕ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_cast; omega)
  intro hB
  rw [← two_mul] at hB
  apply hζ
  push_cast
  simp [riemannZeta_two_mul_nat hm, hB]

namespace ModularForm

variable (k : ℕ) (τ : ℍ)

/-- The Eisenstein series `F_k(τ) = -B_k/(2k) + ∑_{n ≥ 1} σ_{k-1}(n) qⁿ`, `q = e^{2πiτ}` (LMFDB
`mf.gl2.history.elliptic`): the normalisation of the Eisenstein series of weight `k` with first
Fourier coefficient `1`, written `F_k` by Cohen and Strömberg. For even `k ≥ 4` it is
`-(B_k/(2k)) E_k` (`ModularForm.eisensteinF_eq`). -/
noncomputable def eisensteinF : ℂ :=
  -(bernoulli k / (2 * k)) + ∑' n : ℕ+, sigma (k - 1) n * cexp (2 * π * I * τ) ^ (n : ℤ)

variable {k}

/-- **`F_k` is an alternately normalised `E_k`** (LMFDB `mf.gl2.history.elliptic`): for even
`k ≥ 4`, `F_k = -(B_k/(2k)) E_k`. -/
lemma eisensteinF_eq (hk : 3 ≤ k) (hk2 : Even k) :
    eisensteinF k τ = -(bernoulli k / (2 * k)) * E hk τ := by
  have hB : (bernoulli k : ℂ) ≠ 0 := Rat.cast_ne_zero.mpr (bernoulli_ne_zero_of_even (by omega) hk2)
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [eisensteinF, q_expansion_bernoulli hk hk2 τ]
  field_simp
  ring1

/-- **`G_k` is an alternately normalised `E_k`** (LMFDB `mf.gl2.history.elliptic`): the Eisenstein
series `G_k(τ) = ∑_{(m, n) ≠ (0, 0)} (mτ + n)^{-k}` of the lattice `ℤτ + ℤ` is `2 ζ(k) E_k(τ)` for
`k ≥ 3`, the term of `(m, n) = (0, 0)` in the sum over `ℤ²` being `0`. -/
lemma tsum_eisSummand_eq_two_mul_riemannZeta_mul_E (hk : 3 ≤ k) :
    ∑' v : Fin 2 → ℤ, eisSummand k v τ = 2 * riemannZeta k * E hk τ := by
  have hE : E hk τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 k τ :=
    rfl
  rw [tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk, hE, eisensteinSeriesSIF_apply,
    smul_eq_mul]
  ring1

end ModularForm
