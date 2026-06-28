import LeanBridge.ForMathlib.QExpansion.Generic
import LeanBridge.ForMathlib.QExpansion.Examples  -- for `qexp_certify` macro

/-!
# LMFDB level-1 modular form `1.12.a.a`

The unique normalized cusp form of weight 12 (the modular discriminant Δ).

Polynomial in `(E₄, E₆)`, computed by Sage:
  `(1/1728) · E₄³ · E₆⁰ + (-1/1728) · E₄⁰ · E₆²`

Sturm bound for weight 12: `⌊12/12⌋ + 1 = 2`. Verifying agreement on the first 2
q-coefficients with the LMFDB-published expansion would, by Sturm + injectivity of
`evalE₄E₆`, identify this form as THE LMFDB form `1.12.a.a`.
-/

namespace LeanBridge.QExpansion

open ModularForm EisensteinSeries PowerSeries UpperHalfPlane
open scoped MatrixGroups

/-- Polynomial encoding of `1.12.a.a` in `(E₄, E₆)`. -/
def lmfdb_1_12_a_a_polyData : List (ℕ × ℕ × ℚ) :=
  [(3, 0, 1 / 1728), (0, 2, -(1 / 1728))]

/-- The level-1 modular form `1.12.a.a`, defined as the polynomial in `E₄, E₆`. -/
noncomputable def lmfdb_1_12_a_a : ModularForm 𝒮ℒ 12 :=
  (1 / 1728 : ℂ) • mkMonomForm 3 0 12 (by decide) +
  (-(1 / 1728) : ℂ) • mkMonomForm 0 2 12 (by decide)

lemma lmfdb_1_12_a_a_qExpansion_eq_evalEisPS :
    qExpansion 1 (lmfdb_1_12_a_a : ℍ → ℂ) = evalEisPS lmfdb_1_12_a_a_polyData := by
  unfold lmfdb_1_12_a_a
  rw [ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL,
    ModularForm.IsGLPos.coe_smul, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    qExpansion_mkMonomForm, qExpansion_mkMonomForm]
  unfold evalEisPS lmfdb_1_12_a_a_polyData monomialEisPS
  simp only [List.foldr_cons, List.foldr_nil, add_zero]
  push_cast
  module

theorem lmfdb_1_12_a_a_qExpansion_coeff (N n : ℕ) (hn : n < N) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (lmfdb_1_12_a_a : ℍ → ℂ))
      = ((evalEisList lmfdb_1_12_a_a_polyData N).getD n 0 : ℚ) :=
  qexp_coeff_via_E4E6 lmfdb_1_12_a_a_polyData _
    lmfdb_1_12_a_a_qExpansion_eq_evalEisPS N n hn

/-! ## Sturm-bound certificates

Sturm bound for weight 12 is 2. The first 2 q-coefficients of the LMFDB form `1.12.a.a` are
`[0, 1]` (the form is normalized so that `q¹` coefficient is 1, and constant term is 0). -/

/-- Constant term: 0 (cusp form). -/
example : (PowerSeries.coeff (R := ℂ) 0)
    (qExpansion 1 (lmfdb_1_12_a_a : ℍ → ℂ)) = 0 := by
  qexp_certify lmfdb_1_12_a_a_qExpansion_coeff lmfdb_1_12_a_a_polyData 2 0 (0)

/-- First Hecke eigenvalue: 1 (normalized form). -/
example : (PowerSeries.coeff (R := ℂ) 1)
    (qExpansion 1 (lmfdb_1_12_a_a : ℍ → ℂ)) = 1 := by
  qexp_certify lmfdb_1_12_a_a_qExpansion_coeff lmfdb_1_12_a_a_polyData 2 1 (1)

/- By the Sturm bound (and injectivity of `evalE₄E₆` from PR #38813), `lmfdb_1_12_a_a`
above equals the LMFDB form labelled `1.12.a.a` (the modular discriminant Δ). -/

end LeanBridge.QExpansion
