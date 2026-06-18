import LeanBridge.ForMathlib.QExpansion.Compute

/-!
# Examples: computing and certifying q-expansion coefficients of level-1 forms

This file demonstrates the two user-facing tools from `Compute.lean`:

* `#qexp` — a query command that *prints* q-expansion coefficients of an `E₄/E₆` polynomial
  (like `#eval`, no proof obligation). A polynomial is given as `[(a, b, c), …] : List (ℕ × ℕ × ℚ)`,
  meaning `Σ c · E₄^a · E₆^b`.
* `qexp_coeff` — a tactic that *proves* `(coeff n) (qExpansion 1 (f : ℍ → ℂ)) = v` for a form `f`
  defined as a sum of `(c : ℂ) • mkMonomForm a b k _`. It auto-derives the `evalEisPS` bridge and
  discharges the coefficient by `decide +kernel` (no `native_decide`, no per-form bridge lemma).
-/

namespace LeanBridge.QExpansion.ComputeExamples

set_option maxHeartbeats 0

open LeanBridge.QExpansion ModularForm EisensteinSeries PowerSeries UpperHalfPlane
open scoped MatrixGroups

/-! ## `#qexp` — printing coefficients (no proof) -/

-- E₄ = 1 + 240q + 2160q² + 6720q³ + 17520q⁴ + 30240q⁵ + …
#qexp [(1, 0, (1 : ℚ))] precision 6

-- E₆ = 1 - 504q - 16632q² - 122976q³ - 532728q⁴ - 1575504q⁵ - …
#qexp [(0, 1, (1 : ℚ))] precision 6

-- Δ = (E₄³ - E₆²)/1728 = q - 24q² + 252q³ - … : the Ramanujan τ values
#qexp [(3, 0, (1 : ℚ) / 1728), (0, 2, ((-1 : ℚ) / 1728))] precision 8

-- A single coefficient: the 100th coefficient of E₄³⁷ (weight 148)
#qexp [(37, 0, (1 : ℚ))] coeff 100

/-! ## `qexp_coeff` — certifying coefficients (kernel-checked proofs)

Each form is defined as a sum of `(c : ℂ) • mkMonomForm a b k _`, where `4a + 6b = k`. -/

/-- `E₄²`, a weight-8 form (equal to `E₈`). -/
noncomputable def E4sq : ModularForm 𝒮ℒ 8 := (1 : ℂ) • mkMonomForm 2 0 8 (by decide)

-- E₄² = 1 + 480q + 61920q² + 1050240q³ + 7926240q⁴ + 37500480q⁵ + …
example : (PowerSeries.coeff (R := ℂ) 1) (qExpansion 1 (E4sq : ℍ → ℂ)) = 480 := by
  qexp_coeff E4sq [(2, 0, (1 : ℚ))] 6 1 480

example : (PowerSeries.coeff (R := ℂ) 5) (qExpansion 1 (E4sq : ℍ → ℂ)) = 37500480 := by
  qexp_coeff E4sq [(2, 0, (1 : ℚ))] 6 5 37500480

/-- `E₄ · E₆`, a weight-10 form (equal to `E₁₀`). -/
noncomputable def E4E6 : ModularForm 𝒮ℒ 10 := (1 : ℂ) • mkMonomForm 1 1 10 (by decide)

-- E₄·E₆ = 1 - 264q - 135432q² - …
example : (PowerSeries.coeff (R := ℂ) 1) (qExpansion 1 (E4E6 : ℍ → ℂ)) = -264 := by
  qexp_coeff E4E6 [(1, 1, (1 : ℚ))] 6 1 (-264)

/-- `Δ = (E₄³ - E₆²)/1728`, the weight-12 cusp form. Its coefficients are the Ramanujan τ values. -/
noncomputable def Δ : ModularForm 𝒮ℒ 12 :=
  ((1 : ℚ) / 1728 : ℂ) • mkMonomForm 3 0 12 (by decide) +
  ((-1 : ℚ) / 1728 : ℂ) • mkMonomForm 0 2 12 (by decide)

-- τ(1) = 1, τ(2) = -24, τ(5) = 4830
example : (PowerSeries.coeff (R := ℂ) 1) (qExpansion 1 (Δ : ℍ → ℂ)) = 1 := by
  qexp_coeff Δ [(3, 0, (1 : ℚ) / 1728), (0, 2, ((-1 : ℚ) / 1728))] 6 1 1

example : (PowerSeries.coeff (R := ℂ) 2) (qExpansion 1 (Δ : ℍ → ℂ)) = -24 := by
  qexp_coeff Δ [(3, 0, (1 : ℚ) / 1728), (0, 2, ((-1 : ℚ) / 1728))] 6 2 (-24)

example : (PowerSeries.coeff (R := ℂ) 5) (qExpansion 1 (Δ : ℍ → ℂ)) = 4830 := by
  qexp_coeff Δ [(3, 0, (1 : ℚ) / 1728), (0, 2, ((-1 : ℚ) / 1728))] 6 5 4830

/-- `E₄³⁷`, a weight-148 form. -/
noncomputable def E4pow37 : ModularForm 𝒮ℒ 148 := (1 : ℂ) • mkMonomForm 37 0 148 (by decide)

-- coefficient 5 of E₄³⁷
example : (PowerSeries.coeff (R := ℂ) 5) (qExpansion 1 (E4pow37 : ℍ → ℂ)) = 355011912721118880 := by
  qexp_coeff E4pow37 [(37, 0, (1 : ℚ))] 6 5 355011912721118880

end LeanBridge.QExpansion.ComputeExamples
