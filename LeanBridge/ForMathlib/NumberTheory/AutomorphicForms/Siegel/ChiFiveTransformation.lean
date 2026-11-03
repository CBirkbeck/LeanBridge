import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.IbukiyamaGamma0

/-!
# The transformation of `χ₅` under the partial inversion and `ι₁(1, 0; 2k, 1)`

The form `χ₅ = ∏ θ_m`, the product of the ten even theta constants of degree 2, is the generator
of weight 5 of the ring of Siegel modular forms on `Γ[2]` (LMFDB `mf.siegel.family.gamma_2`). Its
law under the partial inversion `J₁` comes from the law of the single theta constants
(`SiegelUpperHalfSpace.thetaConstant_eq_partialInversion`),
`θ_{μ,ν}(Ω) = (-iτ)^{-1/2} e^{πiμ₁ν₁/2} θ_{(ν₁, μ₂), (μ₁, ν₂)}(J₁Ω)`: the exchange of `μ₁` and `ν₁`
permutes the ten even characteristics, the ten square roots multiply to `(-iτ)^{-5}`, with no
ambiguity of branch, and the phases to `e^{πi/2} = i`, from the characteristic `1111` alone. Hence
`χ₅(J₁Ω) = -τ⁵ χ₅(Ω)`, that is `χ₅ ∣₅ J₁ = -χ₅`. The translations `ι₁(1, 2k; 0, 1)` fix `χ₅`, so
`J₁ ι₁(1, 0; 2k, 1) = ι₁(1, -2k; 0, 1) J₁` gives `χ₅(γΩ) = det(CΩ + D)⁵ χ₅(Ω)` for
`γ = ι₁(1, 0; 2k, 1) ∈ Γ[2]`. Together with the law of `χ₅` under the Siegel parabolic subgroup,
these laws make `χ₅` a modular form of weight 5 on `Γ[2]` (the field `chi5_mem` of
`SiegelUpperHalfSpace.IgusaLevelTwo.IgusaLevelTwoStructure`), which is proved in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ChiFiveLevelTwo`.

## Main results

* `SiegelUpperHalfSpace.Ibukiyama.chi5_partialInversion_smul`: `χ₅(J₁Ω) = -τ⁵ χ₅(Ω)` for
  `Ω = (τ, z; z, ω)`.
* `SiegelUpperHalfSpace.Ibukiyama.slash_partialInversion_chi5`: `χ₅ ∣₅ J₁ = -χ₅`.
* `SiegelUpperHalfSpace.Ibukiyama.chi5_embedFirst_lowerUnipotent_smul`:
  `χ₅(γΩ) = det(CΩ + D)⁵ χ₅(Ω)` for `γ = ι₁(1, 0; 2k, 1)`.
-/

open Complex Matrix Real SymplecticGroup

open SpecialLinearGroup (lowerUnipotent)

namespace SiegelUpperHalfSpace.Ibukiyama

variable (Ω : SiegelUpperHalfSpace (Fin 2)) (k : ℤ)

lemma theta_eq_partialInversion (a b c d : ℤ) : theta a b c d Ω =
    1 / (-I * Ω.val 0 0) ^ (1 / 2 : ℂ) * cexp (π * I * (a * c : ℤ) / 2) *
      theta c b a d (map (Int.castRingHom ℝ) partialInversion • Ω) := by
  have hμ : ![c, b] = ![-c, b] + 2 • ![c, 0] := by
    ext i
    fin_cases i <;> simp
    ring1
  rw [theta, thetaConstant_eq_partialInversion, theta, hμ, thetaConstant_add_two_smul_left]
  simp

/-- **The law of `χ₅` under the partial inversion**: `χ₅(J₁Ω) = -τ⁵ χ₅(Ω)` for `Ω = (τ, z; z, ω)`.
The ten square roots `(-iτ)^{-1/2}` of the laws of the theta constants multiply to `(-iτ)^{-5}`,
their phases `e^{πiμ₁ν₁/2}` to `i`, and the exchange of `μ₁` and `ν₁` permutes the ten even
characteristics. -/
lemma chi5_partialInversion_smul :
    chi5 (map (Int.castRingHom ℝ) partialInversion • Ω) = -Ω.val 0 0 ^ 5 * chi5 Ω := by
  have hτ : Ω.val 0 0 ≠ 0 := val_zero_zero_ne_zero Ω
  have hw : (-I * Ω.val 0 0) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    simp [hτ]
  have hs : ((-I * Ω.val 0 0) ^ (1 / 2 : ℂ)) ^ 10 = -I * Ω.val 0 0 ^ 5 := by
    rw [show (10 : ℕ) = 2 * 5 by rfl, pow_mul, ← cpow_nat_mul]
    norm_num
    linear_combination -I * Ω.val 0 0 ^ 5 * (I ^ 2 - 1) * I_sq
  have hI : cexp (π * I * ((1 * 1 : ℤ) : ℂ) / 2) = I := by
    rw [show π * I * ((1 * 1 : ℤ) : ℂ) / 2 = π / 2 * I by push_cast; ring1, exp_pi_div_two_mul_I]
  simp only [chi5, Pi.mul_apply]
  rw [theta_eq_partialInversion Ω 0 0 0 0, theta_eq_partialInversion Ω 0 0 0 1,
    theta_eq_partialInversion Ω 0 0 1 0, theta_eq_partialInversion Ω 0 0 1 1,
    theta_eq_partialInversion Ω 0 1 0 0, theta_eq_partialInversion Ω 0 1 1 0,
    theta_eq_partialInversion Ω 1 0 0 0, theta_eq_partialInversion Ω 1 0 0 1,
    theta_eq_partialInversion Ω 1 1 0 0, theta_eq_partialInversion Ω 1 1 1 1, hI]
  simp only [mul_zero, Int.cast_zero, zero_div, Complex.exp_zero, mul_one]
  generalize (-I * Ω.val 0 0) ^ (1 / 2 : ℂ) = w at hw hs ⊢
  field_simp
  rw [hs]
  ring1

/-- **`χ₅ ∣₅ J₁ = -χ₅`**: the law of `χ₅` under the partial inversion `J₁`, whose automorphy factor
is `det(CΩ + D) = τ`, in slash form. -/
lemma slash_partialInversion_chi5 :
    slash (TauCeti.detPowerRep ℂ 2 5) (map (Int.castRingHom ℝ) partialInversion) chi5 = -chi5 := by
  rw [← neg_one_smul ℂ chi5, slash_eq_smul_iff]
  intro τ
  rw [chi5_partialInversion_smul, detPowerRep_denomGL, det_denom_partialInversion, zpow_ofNat,
    smul_eq_mul]
  ring1

lemma chi5_embedFirst_upperUnipotent_smul :
    chi5 (map (Int.castRingHom ℝ) (embedFirst (upperUnipotent (2 * k))) • Ω) = chi5 Ω := by
  have h : chi5 (map (Int.castRingHom ℝ) (embedFirst (upperUnipotent (2 * k))) • Ω) =
      cexp (π * I * k / 2) ^ 4 * chi5 Ω := by
    simp only [chi5, Pi.mul_apply, thetaConstant_embedFirst_upperUnipotent_smul]
    simp
    ring1
  have he : cexp (π * I * k / 2) ^ 4 = 1 := by
    rw [← Complex.exp_nat_mul]
    exact Complex.exp_eq_one_iff.mpr ⟨k, by push_cast; ring1⟩
  rw [h, he, one_mul]

/-- **The law of `χ₅` under `ι₁(1, 0; 2k, 1)`**: `χ₅(γΩ) = det(CΩ + D)⁵ χ₅(Ω)` for
`γ = ι₁(1, 0; 2k, 1)`, from `J₁ γ = ι₁(1, -2k; 0, 1) J₁`, the law under `J₁` at `Ω` and at `γΩ`,
and the invariance of `χ₅` under the translation `ι₁(1, -2k; 0, 1)`. -/
lemma chi5_embedFirst_lowerUnipotent_smul :
    chi5 (map (Int.castRingHom ℝ) (embedFirst (lowerUnipotent (2 * k))) • Ω) =
      (denom (map (Int.castRingHom ℝ) (embedFirst (lowerUnipotent (2 * k)))) Ω.val).det ^ 5 *
        chi5 Ω := by
  have h : chi5 (map (Int.castRingHom ℝ) partialInversion •
      map (Int.castRingHom ℝ) (embedFirst (lowerUnipotent (2 * k))) • Ω) =
        -((denom (map (Int.castRingHom ℝ) (embedFirst (lowerUnipotent (2 * k)))) Ω.val).det *
          (map (Int.castRingHom ℝ) (embedFirst (lowerUnipotent (2 * k))) • Ω).val 0 0) ^ 5 *
            chi5 Ω := by
    rw [← mul_smul, map_partialInversion_mul_embedFirst_lowerUnipotent, mul_smul, ← mul_neg 2 k,
      chi5_embedFirst_upperUnipotent_smul, chi5_partialInversion_smul,
      det_denom_embedFirst_lowerUnipotent_mul_val]
  refine mul_left_cancel₀ (pow_ne_zero 5 (val_zero_zero_ne_zero
    (map (Int.castRingHom ℝ) (embedFirst (lowerUnipotent (2 * k))) • Ω))) ?_
  linear_combination chi5_partialInversion_smul
    (map (Int.castRingHom ℝ) (embedFirst (lowerUnipotent (2 * k))) • Ω) - h

end SiegelUpperHalfSpace.Ibukiyama
