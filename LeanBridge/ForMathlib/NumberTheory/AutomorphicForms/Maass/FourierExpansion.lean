import LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselK
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.PNat.Basic

/-!
# Fourier expansions of Maass forms

A Maass form `f` of spectral parameter `r` on a non-cocompact group has a Fourier expansion
`f(z) = ∑_{n ∈ ℤ} a(n) √y K_{ir}(2π|n|y) e^{2πinx}` at infinity, which for even and odd forms
becomes a cosine or sine expansion `∑_{n ≥ 1} c(n) √y K_{ir}(2πny) cos(2πnx)` or `sin(2πnx)`.

## Main definitions

* `UpperHalfPlane.HasMaassFourierExpansion` (LMFDB `mf.maass.mwf.fourierexpansion`).
* `UpperHalfPlane.HasMaassCosineExpansion`, `UpperHalfPlane.HasMaassSineExpansion` (LMFDB
  `mf.maass.mwf.fourierexpansion`, `mf.maass.mwf.coefficients`).
-/

open Real

namespace UpperHalfPlane

variable (f : ℂ → ℂ) (r : ℂ)

/-- A function `f` on the upper half-plane, given on `ℂ`, has the **Fourier expansion** (LMFDB
`mf.maass.mwf.fourierexpansion`) `f(z) = ∑_{n ∈ ℤ} a(n) √y K_{ir}(2π|n|y) e^{2πinx}` at `z = x + iy`
for every `z ∈ ℍ`, with `K` the `K`-Bessel function. A square-integrable Maass form on `Γ₀(N)` of
spectral parameter `r` whose constant term at `∞` vanishes has such an expansion
(`exists_hasMaassFourierExpansion_of_mem_maassSpace` in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CuspNewformExpansion`, and
`exists_hasMaassFourierExpansion` in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.FourierExpansionExists` for a smooth
periodic eigenfunction of moderate growth). The term `n = 0` is as in the knowl, where `K_{ir}(0)`
is undefined (its integral diverges and `Complex.besselK` gives it the junk value `0`): the
expansion as written is that of cusp forms, whose constant term vanishes. -/
def HasMaassFourierExpansion (a : ℤ → ℂ) : Prop :=
  ∀ z : ℍ, HasSum (fun n : ℤ ↦ a n * √z.im * (Complex.I * r).besselK (2 * π * |n| * z.im) *
    Complex.exp (2 * π * Complex.I * n * z.re)) (f z)

/-- A function `f` on the upper half-plane has the **cosine expansion** (LMFDB
`mf.maass.mwf.fourierexpansion`, `mf.maass.mwf.coefficients`)
`f(z) = ∑_{n ≥ 1} c(n) √y K_{ir}(2πny) cos(2πnx)` for every `z = x + iy ∈ ℍ`: the Fourier
expansion of an even Maass form. For a Maass newform of weight `0` on `Γ₀(N)` with even symmetry,
the `c(n)` are its **coefficients**, used for its `L`-function `∑ c(n) n^{-s}`. They are unique
(`HasMaassCosineExpansion.unique`). For `N ≠ 0` they exist for a cusp newform
(`IsMaassCuspNewform.hasMaassCosineExpansion`) and for a newform with real spectral parameter
(`IsMaassNewform.hasMaassCosineExpansion_ofReal`), but not for the constant `1` of level `1`
(`not_hasMaassCosineExpansion_const_one`); when they exist, `c(1) ≠ 0` and the coefficients
`c(n) / c(1)` of the newform normalised by `c(1) = 1` are real
(`IsMaassNewform.coeff_one_ne_zero_of_cosine`, `IsMaassNewform.conj_coeff_div_of_cosine`). -/
def HasMaassCosineExpansion (c : ℕ+ → ℂ) : Prop :=
  ∀ z : ℍ, HasSum (fun n : ℕ+ ↦ c n * √z.im * (Complex.I * r).besselK (2 * π * n * z.im) *
    cos (2 * π * n * z.re)) (f z)

/-- A function `f` on the upper half-plane has the **sine expansion** (LMFDB
`mf.maass.mwf.fourierexpansion`, `mf.maass.mwf.coefficients`)
`f(z) = ∑_{n ≥ 1} c(n) √y K_{ir}(2πny) sin(2πnx)` for every `z = x + iy ∈ ℍ`: the Fourier
expansion of an odd Maass form, whose `c(n)` are its coefficients as for
`HasMaassCosineExpansion`. -/
def HasMaassSineExpansion (c : ℕ+ → ℂ) : Prop :=
  ∀ z : ℍ, HasSum (fun n : ℕ+ ↦ c n * √z.im * (Complex.I * r).besselK (2 * π * n * z.im) *
    sin (2 * π * n * z.re)) (f z)

end UpperHalfPlane
