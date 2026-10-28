import LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselK
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

/-!
# The Fourier–Bessel expansion of weight 2 Bianchi modular forms

A weight 2 Bianchi modular form `F : ℋ₃ → ℂ³` over an imaginary quadratic field `K` of discriminant
`Δ` has a Fourier–Bessel expansion
`F(x, y) = Σ_{0 ≠ α ∈ 𝓞_K} c(α) y² 𝕂(4π|α|y / √|Δ|) ψ(αx / √Δ)`, where `ψ(z) = e^{2πi(z + z̄)}`
and `𝕂(t) = (-(i/2) K₁(t), K₀(t), (i/2) K₁(t))`.

## Main definitions

* `HyperbolicThreeSpace.bianchiBesselVector` (LMFDB `mf.bianchi.fourierbessell`): the vector
  `𝕂(t)` of `K`-Bessel functions.
* `HyperbolicThreeSpace.bianchiFourierBesselTerm` (LMFDB `mf.bianchi.fourierbessell`): the terms of
  the expansion.
* `HyperbolicThreeSpace.HasBianchiFourierBesselExpansion` (LMFDB `mf.bianchi.fourierbessell`): `F`
  has the Fourier–Bessel expansion with coefficients `c`.
-/

open Complex NumberField Real
open scoped ComplexConjugate

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] [NumberField K] (σ : K →+* ℂ) (δ : ℂ)

/-- The vector **`𝕂(t) = (-(i/2) K₁(t), K₀(t), (i/2) K₁(t))`** of `K`-Bessel functions (LMFDB
`mf.bianchi.fourierbessell`), where `K_ν` is `Complex.besselK`. -/
noncomputable def bianchiBesselVector (t : ℝ) : Fin 3 → ℂ :=
  ![-(I / 2) * besselK 1 t, besselK 0 t, I / 2 * besselK 1 t]

/-- The term `c(α) y² 𝕂(4π|α|y / √|Δ|) ψ(αx / δ)` at `(x, y)` of the **Fourier–Bessel expansion**
(LMFDB `mf.bianchi.fourierbessell`) of a weight 2 Bianchi modular form over `K`, embedded in `ℂ`
by `σ`, with coefficients `c`, where `Δ` is the discriminant of `K`, `δ` is the chosen square root
`√Δ` and `ψ(z) = e^{2πi(z + z̄)} = e^{4πi Re z}`.

The LMFDB writes `ψ(z) = e^{2π(z + z̄)}`, which is not a character of `ℂ / 𝓞_K`; the factor `i` is
restored here, as in Cremona's normalisation. The term is only meaningful for `α ≠ 0`. -/
noncomputable def bianchiFourierBesselTerm (c : 𝓞 K → ℂ) (p : ℂ × ℝ) (α : 𝓞 K) : Fin 3 → ℂ :=
  letI a : ℂ := σ α
  (c α * (p.2 : ℂ) ^ 2 * exp (2 * π * I * (a * p.1 / δ + conj (a * p.1 / δ)))) •
    bianchiBesselVector (4 * π * ‖a‖ * p.2 / √|(discr K : ℝ)|)

/-- A function `F : ℋ₃ → ℂ³`, given on `ℂ × ℝ`, has the **Fourier–Bessel expansion** (LMFDB
`mf.bianchi.fourierbessell`) `F(x, y) = Σ_{0 ≠ α ∈ 𝓞_K} c(α) y² 𝕂(4π|α|y / √|Δ|) ψ(αx / √Δ)` over
the imaginary quadratic field `K` embedded in `ℂ` by `σ`, with coefficients `c` and the square root
`δ` of `Δ`, the series converging (unconditionally) at every point of `ℋ₃`.

The hypothesis `δ ^ 2 = Δ` is left to the user. That every weight 2 Bianchi cusp form has such an
expansion is a theorem, not proved here (harmonicity is not formalised). -/
def HasBianchiFourierBesselExpansion (F : ℂ × ℝ → Fin 3 → ℂ) (c : 𝓞 K → ℂ) : Prop :=
  ∀ p : ℂ × ℝ, 0 < p.2 →
    HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦ bianchiFourierBesselTerm σ δ c p α) (F p)

end HyperbolicThreeSpace
