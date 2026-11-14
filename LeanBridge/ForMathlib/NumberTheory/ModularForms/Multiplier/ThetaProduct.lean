import LeanBridge.ForMathlib.NumberTheory.ModularForms.JacobiTheta.EtaQuotient
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ThetaMultiplier

/-!
# The product expansion of the theta function of level 4 and its eta quotients

The theta function `θ(z) = ∑_{n ∈ ℤ} e^{2πin²z}` (`ModularForm.thetaSeries`), the modular form of
weight `1/2` and level `4` of the LMFDB knowl `mf.half_integral_weight.theta`, has the product
expansion

`θ(z) = ∏_{n ≥ 1} (1 + q^(2n-1))² (1 - q^(2n))`, where `q = e^{2πiz}`,

by the Jacobi triple product identity, and is a quotient of values of the Dedekind eta function
`η` in two ways:

`θ(z) = η(2z)⁵ / (η(z)² η(4z)²) = η(z + 1/2)² / η(2z + 1)`.

The knowl writes `θ(z) = ∑ e^{πizn²}`, which is `θ(z/2)` and is not of level `4`, with the product
`∏_{n ≥ 1} (1 + q^(n-1/2))² (1 - qⁿ)` and the quotients `η(z)⁵ / (η(z/2)² η(2z)²)` and
`η((z + 1)/2)² / η(z + 1)`. These are the formulas above at `z/2`; they are proved for that
function, Mathlib's `jacobiTheta`, in
`LeanBridge.ForMathlib.NumberTheory.ModularForms.JacobiTheta.EtaQuotient`
(`jacobiTheta_eq_tprod_half`, `jacobiTheta_eq_eta_pow_five_div`, `jacobiTheta_eq_eta_sq_div`), and
this file restates them for the theta function of level `4`.

## Main results

* `ModularForm.hasProd_thetaSeries` (LMFDB `mf.half_integral_weight.theta`): the product
  expansion of `θ`, which converges to `θ(z)`.
* `ModularForm.thetaSeries_eq_tprod` (LMFDB `mf.half_integral_weight.theta`): the product
  expansion of `θ` as an equation.
* `ModularForm.thetaSeries_eq_eta_pow_five_div` (LMFDB `mf.half_integral_weight.theta`):
  `θ(z) = η(2z)⁵ / (η(z)² η(4z)²)`.
* `ModularForm.thetaSeries_eq_eta_sq_div` (LMFDB `mf.half_integral_weight.theta`):
  `θ(z) = η(z + 1/2)² / η(2z + 1)`.
-/

open Complex

open scoped Real

open UpperHalfPlane hiding I

namespace ModularForm

variable (z : ℍ)

/-- **The product expansion of the theta function** (LMFDB `mf.half_integral_weight.theta`): the
product `∏_{n ≥ 1} (1 + q^(2n-1))² (1 - q^(2n))` converges to `θ(z)`, where `q = e^{2πiz}`. -/
lemma hasProd_thetaSeries : HasProd (fun n : ℕ ↦ (1 + cexp (2 * π * I * z) ^ (2 * n + 1)) ^ 2 *
    (1 - cexp (2 * π * I * z) ^ (2 * (n + 1)))) (thetaSeries z) := by
  have h : (π : ℂ) * I * (2 * z) = 2 * π * I * z := by
    ring1
  rw [thetaSeries_eq, ← h]
  exact (hasProd_jacobiTheta (by simpa using z.im_pos)).congr_fun fun n ↦ mul_comm _ _

/-- **The product expansion of the theta function** (LMFDB `mf.half_integral_weight.theta`):
`θ(z) = ∏_{n ≥ 1} (1 + q^(2n-1))² (1 - q^(2n))`, where `q = e^{2πiz}`. -/
lemma thetaSeries_eq_tprod : thetaSeries z =
    ∏' n : ℕ, (1 + cexp (2 * π * I * z) ^ (2 * n + 1)) ^ 2 *
        (1 - cexp (2 * π * I * z) ^ (2 * (n + 1))) :=
  (hasProd_thetaSeries z).tprod_eq.symm

/-- **The theta function as an eta quotient** (LMFDB `mf.half_integral_weight.theta`):
`θ(z) = η(2z)⁵ / (η(z)² η(4z)²)`. -/
lemma thetaSeries_eq_eta_pow_five_div :
    thetaSeries z = η (2 * z) ^ 5 / (η z ^ 2 * η (4 * z) ^ 2) := by
  have h₁ : (2 : ℂ) * z / 2 = z := mul_div_cancel_left₀ _ two_ne_zero
  have h₂ : (2 : ℂ) * (2 * z) = 4 * z := by
    ring1
  rw [thetaSeries_eq, jacobiTheta_eq_eta_pow_five_div (by simpa using z.im_pos), h₁, h₂]

/-- **The theta function as an eta quotient** (LMFDB `mf.half_integral_weight.theta`):
`θ(z) = η(z + 1/2)² / η(2z + 1)`. -/
lemma thetaSeries_eq_eta_sq_div : thetaSeries z = η (z + 1 / 2) ^ 2 / η (2 * z + 1) := by
  have h : ((2 : ℂ) * z + 1) / 2 = z + 1 / 2 := by
    ring1
  rw [thetaSeries_eq, jacobiTheta_eq_eta_sq_div (by simpa using z.im_pos), h]

end ModularForm
