import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.HeckeOperator
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Scalar matrices in `GSp(4, ℚ)⁺`

For a positive integer `s`, the scalar matrix `s 1₄` is central in `GL(4, ℚ)` and is a symplectic
similitude of multiplier `s²`. It fixes every point of the Siegel upper half-space `ℋ₂`, with
automorphy factor `s 1₂`, so that in scalar weight `det^k` its slash operator
`SiegelUpperHalfSpace.gspSlash`, which carries the factor `r^(2k - 3)`, is the multiplication by
`(s²)^(2k - 3) det(s 1₂)^(-k) = (s²)^(k - 3)`.

## Main definitions

* `SiegelUpperHalfSpace.scalarGL`: scalar matrices in `GL(4, ℚ)`.
* `SiegelUpperHalfSpace.scalarGSp`: scalar matrices in `GSp(4, ℚ)⁺`.

## Main results

* `SiegelUpperHalfSpace.heckeMonoidSlash_scalarGSp`: in weight `det^k`, the slash operator of `s 1₄`
  is the multiplication by `(s²)^(k - 3)`.
-/

open Matrix hiding inv_zpow'

namespace SiegelUpperHalfSpace

variable (k : ℤ) (s : ℕ+) (τ : SiegelUpperHalfSpace (Fin 2))

/-- The scalar matrix `s` in `GL(4, ℚ)`, for a positive integer `s`. -/
def scalarGL : GL (Fin 2 ⊕ Fin 2) ℚ :=
  GeneralLinearGroup.scalar _ (Units.mk0 (s : ℚ) (Nat.cast_ne_zero.mpr s.ne_zero))

lemma coe_scalarGL : (scalarGL s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = (s : ℚ) • 1 :=
  (scalar_apply _).trans (smul_one_eq_diagonal _).symm

lemma scalarGL_mul_comm (g : GL (Fin 2 ⊕ Fin 2) ℚ) : scalarGL s * g = g * scalarGL s :=
  (Subgroup.mem_center_iff.mp
    (GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨_, rfl⟩) g).symm

lemma transpose_scalarGL_mul_J_mul : (scalarGL s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)ᵀ *
    J (Fin 2) ℚ * scalarGL s = (s : ℚ) ^ 2 • J (Fin 2) ℚ := by
  rw [coe_scalarGL, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one, smul_smul, sq]

/-- The scalar matrix `s` in `GSp(4, ℚ)⁺`, of multiplier `s²`. -/
def scalarGSp : gspPlusGL (Fin 2) :=
  ⟨scalarGL s, (s : ℚ) ^ 2, by positivity, transpose_scalarGL_mul_J_mul s⟩

lemma multiplier_scalarGSp : multiplier (submonoidToGSpPlus (scalarGSp s)) = (s : ℚ) ^ 2 :=
  multiplier_eq _ (transpose_scalarGL_mul_J_mul s)

lemma gspDenom_scalarGSp : gspDenom (submonoidToGSpPlus (scalarGSp s)) τ = (s : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gspDenom, submonoidToGSpPlus, scalarGSp, coe_scalarGL, toBlocks₂₁, toBlocks₂₂,
      Matrix.mul_apply]

lemma gspSmul_scalarGSp : gspSmul (submonoidToGSpPlus (scalarGSp s)) τ = τ := by
  have hs : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr s.ne_zero
  have hinv : ((s : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹ = (s : ℂ)⁻¹ • 1 :=
    inv_eq_left_inv <| by
      rw [smul_mul_smul_comm, Matrix.one_mul, inv_mul_cancel₀ hs, one_smul]
  have hnum : gspNum (submonoidToGSpPlus (scalarGSp s)) τ = (s : ℂ) • τ.val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gspNum, submonoidToGSpPlus, scalarGSp, coe_scalarGL, toBlocks₁₁, toBlocks₁₂,
        Matrix.mul_apply]
  refine SiegelUpperHalfSpace.ext ?_
  rw [gspSmul_val, gspDenom_scalarGSp, hnum, hinv, smul_mul_smul_comm, Matrix.mul_one,
    mul_inv_cancel₀ hs, one_smul]

lemma slashExponent_detPowerRep : slashExponent (TauCeti.detPowerRep ℂ 2 k) = 2 * k - 3 := by
  rw [slashExponent, Representation.highestWeight_detPowerRep]
  simp

/-- **Scalar matrices act by scalars**: in weight `det^k`, the slash operator of `s 1₄ ∈ GSp(4, ℚ)⁺`
is the multiplication by `(s²)^(k - 3)`, as `s 1₄` fixes every point of `ℋ₂`, with multiplier `s²`
and automorphy factor `s 1₂`. -/
lemma heckeMonoidSlash_scalarGSp (F : SiegelUpperHalfSpace (Fin 2) → ℂ) :
    heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 k) (scalarGSp s) F = ((s : ℂ) ^ 2) ^ (k - 3) • F := by
  have hs : (s : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr s.ne_zero)
  ext τ
  simp only [heckeMonoidSlash, LinearMap.coe_mk, AddHom.coe_mk, gspSlash, slashExponent_detPowerRep,
    multiplier_scalarGSp, Rat.cast_pow, Rat.cast_natCast, gspSmul_scalarGSp,
    TauCeti.detPowerRep_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val,
    GeneralLinearGroup.val_det_apply, coe_gspDenomGL, gspDenom_scalarGSp, det_smul,
    Fintype.card_fin, det_one, mul_one, smul_eq_mul]
  rw [inv_zpow', ← mul_assoc, ← zpow_add₀ hs]
  congr 2
  ring1

end SiegelUpperHalfSpace
