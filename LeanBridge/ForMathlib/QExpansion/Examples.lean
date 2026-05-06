import LeanBridge.ForMathlib.QExpansion.DeltaBridge

/-!
# Examples: certifying q-expansion coefficients for several level-1 modular forms

This file demonstrates the generic framework on several level-1 modular forms beyond `Δ`:

* `E₄` itself (weight 4), polynomial encoding `[(1, 0, 1)]`.
* `E₆` itself (weight 6), polynomial encoding `[(0, 1, 1)]`.
* `E₄² = E₈` (weight 8, since `dim M₈ = 1`), polynomial encoding `[(2, 0, 1)]`.
* `E₄ · E₆ = E₁₀` (weight 10, since `dim M₁₀ = 1`), polynomial encoding `[(1, 1, 1)]`.
* `Δ` (weight 12), polynomial encoding `[(3, 0, 1/1728), (0, 2, -1/1728)]`.

For each form we define:
* `<form>_polyData : List (ℕ × ℕ × ℚ)` — the polynomial in `E₄, E₆`.
* `<form>_qExpansion_eq_evalEisPS` — the bridge lemma.
* `<form>_qExpansion_coeff` — the coefficient corollary, derived via `qexp_coeff_via_E4E6`.

A single unified `qexp_certify` macro handles all forms uniformly.
-/

namespace LeanBridge.QExpansion

open ModularForm EisensteinSeries PowerSeries UpperHalfPlane
open scoped MatrixGroups

/-! ## Unified `qexp_certify` macro

Bundles the rewrite + `decide +kernel` + cast pattern for any form expressible as a
polynomial in `E₄`, `E₆`. The user supplies:

* `thm` — the per-form coefficient theorem (built from `qexp_coeff_via_E4E6`),
* `poly` — the polynomial encoding,
* `precision` / `idx` / `value` — as before.
-/

/-- Positional syntax: `qexp_certify <thm> <poly> <precision> <idx> <value>`. -/
syntax "qexp_certify" term:max term:max num num term:max : tactic

macro_rules
  | `(tactic| qexp_certify $thm:term $poly:term $N:num $n:num $v:term) =>
    `(tactic|
        (rw [$thm $N $n (by decide),
             show (evalEisList $poly $N).getD $n 0 = ($v : ℚ) from by decide +kernel]
         push_cast; rfl))

/-! ## E₄ -/

/-- E₄ as a polynomial in `(E₄, E₆)`: just `1 · E₄¹ · E₆⁰`. -/
def E4_polyData : List (ℕ × ℕ × ℚ) := [(1, 0, 1)]

lemma E4_qExpansion_eq_evalEisPS :
    qExpansion 1 (↑E₄ : ℍ → ℂ) = evalEisPS E4_polyData := by
  unfold evalEisPS E4_polyData monomialEisPS
  simp

theorem E4_qExpansion_coeff (N n : ℕ) (hn : n < N) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (↑E₄ : ℍ → ℂ))
      = ((evalEisList E4_polyData N).getD n 0 : ℚ) :=
  qexp_coeff_via_E4E6 E4_polyData _ E4_qExpansion_eq_evalEisPS N n hn

/-- E₄ q-expansion: `1 + 240q + 2160q² + 6720q³ + 17520q⁴ + 30240q⁵`. -/
example : (PowerSeries.coeff (R := ℂ) 0) (qExpansion 1 (↑E₄ : ℍ → ℂ)) = 1 := by
  qexp_certify E4_qExpansion_coeff E4_polyData
    6 0 (1)

example : (PowerSeries.coeff (R := ℂ) 1) (qExpansion 1 (↑E₄ : ℍ → ℂ)) = 240 := by
  qexp_certify E4_qExpansion_coeff E4_polyData
    6 1 (240)

example : (PowerSeries.coeff (R := ℂ) 2) (qExpansion 1 (↑E₄ : ℍ → ℂ)) = 2160 := by
  qexp_certify E4_qExpansion_coeff E4_polyData
    6 2 (2160)

example : (PowerSeries.coeff (R := ℂ) 5) (qExpansion 1 (↑E₄ : ℍ → ℂ)) = 30240 := by
  qexp_certify E4_qExpansion_coeff E4_polyData
    6 5 (30240)

/-! ## E₆ -/

/-- E₆ as a polynomial in `(E₄, E₆)`: just `1 · E₄⁰ · E₆¹`. -/
def E6_polyData : List (ℕ × ℕ × ℚ) := [(0, 1, 1)]

lemma E6_qExpansion_eq_evalEisPS :
    qExpansion 1 (↑E₆ : ℍ → ℂ) = evalEisPS E6_polyData := by
  unfold evalEisPS E6_polyData monomialEisPS
  simp

theorem E6_qExpansion_coeff (N n : ℕ) (hn : n < N) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (↑E₆ : ℍ → ℂ))
      = ((evalEisList E6_polyData N).getD n 0 : ℚ) :=
  qexp_coeff_via_E4E6 E6_polyData _ E6_qExpansion_eq_evalEisPS N n hn

/-- E₆ q-expansion: `1 - 504q - 16632q² - 122976q³ - 532728q⁴ - 1575504q⁵`. -/
example : (PowerSeries.coeff (R := ℂ) 0) (qExpansion 1 (↑E₆ : ℍ → ℂ)) = 1 := by
  qexp_certify E6_qExpansion_coeff E6_polyData
    6 0 (1)

example : (PowerSeries.coeff (R := ℂ) 1) (qExpansion 1 (↑E₆ : ℍ → ℂ)) = -504 := by
  qexp_certify E6_qExpansion_coeff E6_polyData
    6 1 (-504)

example : (PowerSeries.coeff (R := ℂ) 5) (qExpansion 1 (↑E₆ : ℍ → ℂ)) = -1575504 := by
  qexp_certify E6_qExpansion_coeff E6_polyData
    6 5 (-1575504)

/-! ## E₄² (a weight-8 form, equal to E₈) -/

/-- The level-1 modular form `E₄²` of weight 8. Up to normalization this is `E₈`. -/
noncomputable def E4Sq : ModularForm 𝒮ℒ 8 := ModularForm.mcast (by decide) (E₄.pow 2)

lemma E4Sq_apply (z : ℍ) : E4Sq z = E₄ z ^ 2 := by
  change ⇑(E₄.pow 2) z = _
  rw [coe_pow]; rfl

/-- E₄² as a polynomial in `(E₄, E₆)`: just `1 · E₄² · E₆⁰`. -/
def E4Sq_polyData : List (ℕ × ℕ × ℚ) := [(2, 0, 1)]

lemma E4Sq_qExpansion_eq_evalEisPS :
    qExpansion 1 (E4Sq : ℍ → ℂ) = evalEisPS E4Sq_polyData := by
  show qExpansion 1 ⇑(ModularForm.mcast (by decide) (E₄.pow 2)) = _
  change qExpansion 1 ⇑(E₄.pow 2) = _
  rw [ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₄ 2]
  unfold evalEisPS E4Sq_polyData monomialEisPS
  simp

theorem E4Sq_qExpansion_coeff (N n : ℕ) (hn : n < N) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (E4Sq : ℍ → ℂ))
      = ((evalEisList E4Sq_polyData N).getD n 0 : ℚ) :=
  qexp_coeff_via_E4E6 E4Sq_polyData _ E4Sq_qExpansion_eq_evalEisPS N n hn

/-- E₄² q-expansion: `1 + 480q + 61920q² + 1050240q³ + …`.
Compare to `E₈ = 1 + 480 σ₇(n) q^n`: c₂ = `480 · σ₇(2) = 480 · 129 = 61920`. -/
example : (PowerSeries.coeff (R := ℂ) 0) (qExpansion 1 (E4Sq : ℍ → ℂ)) = 1 := by
  qexp_certify E4Sq_qExpansion_coeff E4Sq_polyData
    5 0 (1)

example : (PowerSeries.coeff (R := ℂ) 1) (qExpansion 1 (E4Sq : ℍ → ℂ)) = 480 := by
  qexp_certify E4Sq_qExpansion_coeff E4Sq_polyData
    5 1 (480)

example : (PowerSeries.coeff (R := ℂ) 2) (qExpansion 1 (E4Sq : ℍ → ℂ)) = 61920 := by
  qexp_certify E4Sq_qExpansion_coeff E4Sq_polyData
    5 2 (61920)

example : (PowerSeries.coeff (R := ℂ) 3) (qExpansion 1 (E4Sq : ℍ → ℂ)) = 1050240 := by
  qexp_certify E4Sq_qExpansion_coeff E4Sq_polyData
    5 3 (1050240)

/-! ## E₄ · E₆ (a weight-10 form, equal to E₁₀) -/

/-- The level-1 modular form `E₄ · E₆` of weight 10. Up to normalization this is `E₁₀`. -/
noncomputable def E4MulE6 : ModularForm 𝒮ℒ 10 := ModularForm.mcast (by decide) (E₄.mul E₆)

lemma E4MulE6_apply (z : ℍ) : E4MulE6 z = E₄ z * E₆ z := by
  change ⇑(E₄.mul E₆) z = _
  rfl

/-- E₄ · E₆ as a polynomial in `(E₄, E₆)`: `1 · E₄¹ · E₆¹`. -/
def E4MulE6_polyData : List (ℕ × ℕ × ℚ) := [(1, 1, 1)]

lemma E4MulE6_qExpansion_eq_evalEisPS :
    qExpansion 1 (E4MulE6 : ℍ → ℂ) = evalEisPS E4MulE6_polyData := by
  show qExpansion 1 ⇑(ModularForm.mcast (by decide) (E₄.mul E₆)) = _
  change qExpansion 1 ⇑(E₄.mul E₆) = _
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL E₄ E₆]
  unfold evalEisPS E4MulE6_polyData monomialEisPS
  simp

theorem E4MulE6_qExpansion_coeff (N n : ℕ) (hn : n < N) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (E4MulE6 : ℍ → ℂ))
      = ((evalEisList E4MulE6_polyData N).getD n 0 : ℚ) :=
  qexp_coeff_via_E4E6 E4MulE6_polyData _ E4MulE6_qExpansion_eq_evalEisPS N n hn

/-- E₄ · E₆ q-expansion: `1 - 264q - 135432q² - 5196576q³ - …`.
Compare to `E₁₀ = 1 - 264 σ₉(n) q^n`: c₂ = `-264 · σ₉(2) = -264 · 513 = -135432`. -/
example : (PowerSeries.coeff (R := ℂ) 0) (qExpansion 1 (E4MulE6 : ℍ → ℂ)) = 1 := by
  qexp_certify E4MulE6_qExpansion_coeff E4MulE6_polyData
    5 0 (1)

example : (PowerSeries.coeff (R := ℂ) 1) (qExpansion 1 (E4MulE6 : ℍ → ℂ)) = -264 := by
  qexp_certify E4MulE6_qExpansion_coeff E4MulE6_polyData
    5 1 (-264)

example : (PowerSeries.coeff (R := ℂ) 2) (qExpansion 1 (E4MulE6 : ℍ → ℂ)) = -135432 := by
  qexp_certify E4MulE6_qExpansion_coeff E4MulE6_polyData
    5 2 (-135432)

example : (PowerSeries.coeff (R := ℂ) 3) (qExpansion 1 (E4MulE6 : ℍ → ℂ)) = -5196576 := by
  qexp_certify E4MulE6_qExpansion_coeff E4MulE6_polyData
    5 3 (-5196576)

/-! ## Δ — same unified macro -/

/-- Same as `discriminant_qExpansion_coeff_via_generic` but going through the unified macro. -/
example : (PowerSeries.coeff (R := ℂ) 5)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = 4830 := by
  qexp_certify discriminant_qExpansion_coeff_via_generic Delta_polyData
    12 5 (4830)

example : (PowerSeries.coeff (R := ℂ) 11)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = 534612 := by
  qexp_certify discriminant_qExpansion_coeff_via_generic Delta_polyData
    12 11 (534612)

end LeanBridge.QExpansion
