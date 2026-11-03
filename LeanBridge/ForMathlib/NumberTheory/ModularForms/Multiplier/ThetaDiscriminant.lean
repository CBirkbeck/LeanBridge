import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraSeed
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ThetaMultiplier
import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# A cusp form of half-integral weight: `θ Δ`

The product of the theta function `θ ∈ M_{1/2}(4, 1)` and the discriminant `Δ` of weight `12` is a
nonzero cusp form of weight `25/2` on `Γ₀(4)`, an element of the domain of the Shimura
correspondence (LMFDB `cmf.shimura_correspondence`).

## Main results

* `ModularForm.thetaSeries_mul_discriminant_mem_halfIntegralWeightCuspSpace`:
  `θ Δ ∈ S_{25/2}(4, 1)`.
* `ModularForm.thetaSeries_mul_discriminant_ne_zero`: `θ Δ ≠ 0`.
-/

open Complex CongruenceSubgroup Filter Matrix SpecialLinearGroup ModularGroup SlashInvariantForm

open scoped MatrixGroups Manifold ModularForm

open UpperHalfPlane hiding I I_re I_im

namespace ModularForm

private lemma discriminant_smul (γ : SL(2, ℤ)) (z : ℍ) :
    discriminant (γ • z) = denom γ z ^ 12 * discriminant z := by
  have h : (discriminant ∣[(12 : ℤ)] γ) z = discriminant z :=
    congrFun (slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant γ) z
  rw [SL_slash_apply] at h
  have hd : denom γ z ≠ 0 := denom_ne_zero γ z
  have e : denom γ z ^ (-(12 : ℤ)) = (denom γ z ^ 12)⁻¹ := by
    rw [zpow_neg (denom γ z)]
    rfl
  rw [e] at h
  rw [← h]
  field_simp

private lemma norm_discriminant_smul (γ : SL(2, ℤ)) (z : ℍ) :
    ‖denom γ z‖ ^ (-(12 : ℝ)) * ‖discriminant (γ • z)‖ = ‖discriminant z‖ := by
  have hd : 0 < ‖denom γ z‖ := norm_pos_iff.mpr (denom_ne_zero γ z)
  have e : ‖denom γ z‖ ^ (-(12 : ℝ)) = (‖denom γ z‖ ^ 12)⁻¹ := by
    rw [Real.rpow_neg hd.le]
    norm_num
  rw [discriminant_smul, norm_mul, norm_pow, e]
  field_simp

private lemma isZeroAtImInfty_slash_thetaSeries_mul_discriminant (γ : SL(2, ℤ)) : IsZeroAtImInfty
    (halfIntegralWeightSlash (2 * ((12 : ℕ) : ℤ) + 1) γ (thetaSeries * discriminant)) := by
  have hθ : IsBoundedAtImInfty (halfIntegralWeightSlash 1 γ thetaSeries) :=
    thetaSeries_mem_halfIntegralWeightSpace.2.2 γ
  have hΔ : Tendsto discriminant atImInfty (nhds 0) := discriminant_isZeroAtImInfty
  have h1 : Tendsto (fun z : ℍ ↦ ‖discriminant z‖ * ‖halfIntegralWeightSlash 1 γ thetaSeries z‖)
      atImInfty (nhds 0) :=
    (tendsto_zero_iff_norm_tendsto_zero.mp hΔ).zero_mul_isBoundedUnder_le
      hθ.norm_left.isBoundedUnder_le
  refine squeeze_zero_norm (fun z ↦ le_of_eq ?_) h1
  have hd : 0 < ‖denom γ z‖ := norm_pos_iff.mpr (denom_ne_zero γ z)
  have e : ‖denom γ z‖ ^ (-(((2 * ((12 : ℕ) : ℤ) + 1 : ℤ) : ℝ) / 2)) =
      ‖denom γ z‖ ^ (-(12 : ℝ)) * ‖denom γ z‖ ^ (-(((1 : ℤ) : ℝ) / 2)) := by
    rw [← Real.rpow_add hd]
    congr 1
    push_cast
    norm_num
  simp only [halfIntegralWeightSlash, Pi.mul_apply, norm_mul, norm_real]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), e,
    ← norm_discriminant_smul γ z]
  ring1

/-- **`θ Δ` is a cusp form of half-integral weight**: `θ Δ ∈ S_{25/2}(4, 1)`, for `θ` the theta
function and `Δ` the discriminant. So the domain of the Shimura correspondence
(LMFDB `cmf.shimura_correspondence`) is not zero. -/
lemma thetaSeries_mul_discriminant_mem_halfIntegralWeightCuspSpace : thetaSeries * discriminant ∈
    halfIntegralWeightCuspSpace (1 : DirichletCharacter ℂ 4) (2 * ((12 : ℕ) : ℤ) + 1) := by
  refine ⟨⟨mdifferentiable_thetaSeries.mul CuspForm.discriminant.holo', fun γ hγ z ↦ ?_,
    fun γ ↦ (isZeroAtImInfty_slash_thetaSeries_mul_discriminant γ).isBoundedAtImInfty⟩,
      isZeroAtImInfty_slash_thetaSeries_mul_discriminant⟩
  have hθ : thetaSeries (γ • z) = (1 : DirichletCharacter ℂ 4) ((γ 1 1 : ℤ) : ZMod 4) *
      weightFactor 1 γ z * thetaSeries z :=
    thetaSeries_mem_halfIntegralWeightSpace.2.1 γ hγ z
  have hw1 : weightFactor 1 γ z = thetaFactor γ z := by
    simp [weightFactor]
  have hunit : IsUnit ((γ 1 1 : ℤ) : ZMod 4) := by
    have hc : ((4 : ℕ) : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
    rcases hc with ⟨c, hc⟩
    exact (ZMod.coe_int_isUnit_iff_isCoprime _ _).mpr ⟨-γ 0 1 * c, γ 0 0, by
      linear_combination γ.fin_two_mul_sub_mul_eq_one + γ 0 1 * hc⟩
  have hε : (thetaEpsilon (γ 1 1))⁻¹ ^ (2 * 12) = 1 := by
    rw [thetaEpsilon]
    split_ifs
    · simp
    · have e : I ^ (4 * 6) = 1 := by
        rw [pow_mul, I_pow_four, one_pow]
      rw [inv_pow]
      norm_num at e ⊢
  rw [Pi.mul_apply, Pi.mul_apply, discriminant_smul, weightFactor_two_mul_add_one,
    MulChar.one_apply hunit, one_mul, hε, mul_one]
  rw [MulChar.one_apply hunit, one_mul, hw1] at hθ
  rw [hθ]
  ring1

/-- **`θ Δ` is not zero** (LMFDB `cmf.shimura_correspondence`). -/
lemma thetaSeries_mul_discriminant_ne_zero : thetaSeries * discriminant ≠ 0 := by
  intro h
  refine thetaSeries_ne_zero (funext fun z ↦ ?_)
  have h1 : (thetaSeries * discriminant) z = (0 : ℍ → ℂ) z := congrFun h z
  rw [Pi.mul_apply] at h1
  exact (mul_eq_zero.mp h1).resolve_right (discriminant_ne_zero z)

end ModularForm
