import LeanBridge.ForMathlib.QExpansion.Generic
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# Bridge: list-based Δ q-expansion ↔ mathlib's `qExpansion 1 ModularForm.discriminant`

The general bridge theorem: for any `n < N`, the `n`-th coefficient of the q-expansion of the
modular discriminant equals the `n`-th entry of `Delta_qexpList N` (cast to `ℂ`).
-/

namespace LeanBridge.QExpansion

open ModularForm EisensteinSeries PowerSeries UpperHalfPlane
open scoped MatrixGroups

/-! ## A `ModularForm`-level construction of `(E₄³ - E₆²) / 1728` -/

/-- `(E₄³ - E₆²)` viewed as a level-1 modular form of weight 12. -/
noncomputable def E₄CubeSubE₆SqForm' : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)

/-- Pointwise value of `E₄CubeSubE₆SqForm'`. -/
lemma E₄CubeSubE₆SqForm'_apply (z : ℍ) :
    E₄CubeSubE₆SqForm' z = E₄ z ^ 3 - E₆ z ^ 2 := by
  change ⇑(E₄.pow 3) z - ⇑(E₆.pow 2) z = _
  rw [coe_pow, coe_pow]
  rfl

/-- The `(E₄³ - E₆²) / 1728` form as a level-1 weight-12 modular form. -/
noncomputable def deltaForm : ModularForm 𝒮ℒ 12 :=
  (1 / 1728 : ℂ) • E₄CubeSubE₆SqForm'

lemma deltaForm_apply (z : ℍ) :
    deltaForm z = (1 / 1728 : ℂ) * (E₄ z ^ 3 - E₆ z ^ 2) := by
  change (1 / 1728 : ℂ) * E₄CubeSubE₆SqForm' z = _
  rw [E₄CubeSubE₆SqForm'_apply]

/-- `deltaForm` agrees pointwise with `ModularForm.discriminant`. -/
lemma deltaForm_eq_discriminant :
    (deltaForm : ℍ → ℂ) = ModularForm.discriminant := by
  funext z
  rw [deltaForm_apply, discriminant_eq_E₄_cube_sub_E₆_sq z]
  ring

/-! ## qExpansion of `deltaForm` factors through E₄, E₆ qExpansions -/

lemma qExpansion_deltaForm :
    qExpansion 1 (deltaForm : ℍ → ℂ) =
      (1 / 1728 : ℂ) • ((qExpansion 1 (E₄ : ℍ → ℂ)) ^ 3 - (qExpansion 1 (E₆ : ℍ → ℂ)) ^ 2) := by
  unfold deltaForm
  rw [ModularForm.IsGLPos.coe_smul E₄CubeSubE₆SqForm' (1 / 1728 : ℂ),
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
  congr 1
  unfold E₄CubeSubE₆SqForm'
  rw [ModularForm.coe_sub,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]
  -- Now: qExpansion 1 ⇑(mcast _ (E₄.pow 3)) - qExpansion 1 ⇑(mcast _ (E₆.pow 2))
  -- mcast preserves the function, so unfold it
  change qExpansion 1 ⇑(E₄.pow 3) - qExpansion 1 ⇑(E₆.pow 2) = _
  rw [ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₄ 3,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₆ 2]

/-- The qExpansion of the discriminant equals `(1/1728) • ((qE₄)^3 - (qE₆)^2)` as
a power series. -/
lemma discriminant_qExpansion_eq :
    qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) =
      (1 / 1728 : ℂ) • ((qExpansion 1 (E₄ : ℍ → ℂ)) ^ 3 - (qExpansion 1 (E₆ : ℍ → ℂ)) ^ 2) := by
  rw [← deltaForm_eq_discriminant, qExpansion_deltaForm]

/-! ## Main bridge theorem -/

/-- For any `n < N`, the `n`-th coefficient of `qExpansion 1 ModularForm.discriminant`
equals the `n`-th entry of `Delta_qexpList N` (cast to ℂ). -/
theorem discriminant_qExpansion_coeff_eq_Delta_qexpList (N : ℕ) (n : ℕ) (hn : n < N) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ))
      = ((Delta_qexpList N).getD n 0 : ℚ) := by
  rw [discriminant_qExpansion_eq,
    show (1 / 1728 : ℂ) = (((1 / 1728 : ℚ) : ℂ)) from by push_cast; rfl]
  unfold Delta_qexpList
  exact approxTo_smul_C (1 / 1728)
    (approxTo_sub
      (approxTo_pow (approxTo_E4 N) 3)
      (approxTo_pow (approxTo_E6 N) 2)) n hn

/-! ## Sanity checks: tau(n) for small n via the general bridge -/

example : (PowerSeries.coeff (R := ℂ) 5)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = 4830 := by
  rw [discriminant_qExpansion_coeff_eq_Delta_qexpList 7 5 (by decide),
    show (Delta_qexpList 7).getD 5 0 = (4830 : ℚ) from by decide +kernel]
  push_cast; rfl

example : (PowerSeries.coeff (R := ℂ) 6)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = -6048 := by
  rw [discriminant_qExpansion_coeff_eq_Delta_qexpList 7 6 (by decide),
    show (Delta_qexpList 7).getD 6 0 = (-6048 : ℚ) from by decide +kernel]
  push_cast; rfl

/-! ## The same result via the generic `evalEisPS` framework

We re-derive Δ's q-expansion certificate using the generic `qexp_coeff_via_E4E6` theorem
applied with the polynomial encoding `[(3, 0, 1/1728), (0, 2, -1/1728)]`. This is the
shape of certificate the upcoming tactic will generate. -/

/-- The polynomial encoding of `Δ = (1/1728) · E₄³ - (1/1728) · E₆²`. -/
def Delta_polyData : List (ℕ × ℕ × ℚ) := [(3, 0, 1 / 1728), (0, 2, -(1 / 1728))]

/-- The Δ q-expansion expressed in the generic `evalEisPS` form. -/
lemma discriminant_qExpansion_eq_evalEisPS :
    qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) = evalEisPS Delta_polyData := by
  rw [discriminant_qExpansion_eq]
  unfold evalEisPS Delta_polyData monomialEisPS
  simp only [List.foldr_cons, List.foldr_nil, pow_zero, mul_one, one_mul, add_zero]
  push_cast
  module

/-- Δ's q-expansion coefficients via the generic theorem. Same shape as the per-form version
above, but built from the reusable `qexp_coeff_via_E4E6`. -/
theorem discriminant_qExpansion_coeff_via_generic (N n : ℕ) (hn : n < N) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ))
      = ((evalEisList Delta_polyData N).getD n 0 : ℚ) :=
  qexp_coeff_via_E4E6 Delta_polyData _ discriminant_qExpansion_eq_evalEisPS N n hn

/-- Same sanity check as before, now via the generic framework. -/
example : (PowerSeries.coeff (R := ℂ) 5)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = 4830 := by
  rw [discriminant_qExpansion_coeff_via_generic 7 5 (by decide),
    show (evalEisList Delta_polyData 7).getD 5 0 = (4830 : ℚ) from by decide +kernel]
  push_cast; rfl

end LeanBridge.QExpansion
