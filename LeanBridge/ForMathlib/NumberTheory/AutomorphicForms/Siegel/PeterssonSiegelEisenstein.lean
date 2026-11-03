import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SiegelParabolicDomain

/-!
# The Siegel Eisenstein series are orthogonal to the cusp forms

The Siegel Eisenstein series `ψ_k`, for even `k > 3`, is the series `∑_{δ ∈ P \ Sp(4, ℤ)} f₀ ∣ δ` of
the constant function `f₀`, with `P` the Siegel parabolic subgroup. The series of absolute values is
bounded on the Siegel set, since the constant `siegelK` of the Plücker comparison is. So `⟨ψ_k, G⟩`
unfolds to the integral of `b(ρ(Y) f₀, G(Z))` over a fundamental domain of `P`, for a cusp form `G`.
This fundamental domain can be chosen so that its translates by `T_u : Z ↦ Z + u E₁₁` are again
fundamental domains of `P` (`SiegelUpperHalfSpace.parabolicDomain`), which gives `⟨ψ_k, G⟩ = 0` by
averaging over `u`.

## Main results

* `SiegelUpperHalfSpace.siegelK_le`: the constant of the Plücker comparison is bounded on the Siegel
  set.
* `SiegelUpperHalfSpace.isPeterssonOrthogonal_siegelEisensteinKJ`: `⟨ψ_k, G⟩ = 0` for a cusp form
  `G`.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open Complex MeasureTheory Module Real Set SymplecticGroup

open scoped ComplexConjugate ENNReal TensorProduct

namespace SiegelUpperHalfSpace

/-- **The constant `K(Z)` of the Plücker comparison is bounded on the Siegel set.** -/
lemma siegelK_le {Z : SiegelUpperHalfSpace (Fin 2)} (hZ : Z ∈ siegelSet) : siegelK Z.val ≤ 225 := by
  have hZs : Z.val 1 0 = Z.val 0 1 := congrFun (congrFun Z.transpose_val 0) 1
  have h₀ : 4 / 5 ≤ (Z.val 0 0).im := four_fifths_le_im_zero_zero hZ
  have h₁ : 4 / 5 ≤ (Z.val 1 1).im := four_fifths_le_im_one_one hZ
  have h₂ : |(Z.val 0 1).im| ≤ (Z.val 0 0).im := abs_im_zero_one_le hZ
  have h₃ : (Z.val 0 0).im ≤ (Z.val 1 1).im := hZ.2.2.1
  have hd : (Z.val.map im).det = (Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im ^ 2 := by
    simp [det_fin_two, hZs, pow_two]
  have h₄ : 3 / 4 * ((Z.val 0 0).im * (Z.val 1 1).im) ≤ (Z.val.map im).det := mul_le_det_im hZ
  rw [hd] at h₄
  have hx₀ : |(Z.val 0 0).re| ≤ 1 / 2 := hZ.1 0 0
  have hx₁ : |(Z.val 0 1).re| ≤ 1 / 2 := hZ.1 0 1
  have hx₂ : |(Z.val 1 1).re| ≤ 1 / 2 := hZ.1 1 1
  have hA : 4 * (1 + |(Z.val 0 0).re| + |(Z.val 0 1).re| + |(Z.val 1 1).re|) ^ 2 ≤ 25 := by
    have hB : (1 + |(Z.val 0 0).re| + |(Z.val 0 1).re| + |(Z.val 1 1).re|) ^ 2 ≤ (5 / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    linarith
  have hD : 0 < (Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im ^ 2 := by
    nlinarith
  have hC : (1 + (Z.val 0 0).im + (Z.val 1 1).im + |(Z.val 0 1).im|) /
      ((Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im ^ 2) ≤ 8 := by
    rw [div_le_iff₀ hD]
    nlinarith
  have hC₀ : 0 ≤ (1 + (Z.val 0 0).im + (Z.val 1 1).im + |(Z.val 0 1).im|) /
      ((Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im ^ 2) :=
    div_nonneg (by linarith [abs_nonneg (Z.val 0 1).im]) hD.le
  rw [siegelK]
  linarith [mul_le_mul hA (show 1 + _ ≤ (9 : ℝ) by linarith) (by linarith) (by norm_num)]

private lemma ker_le_siegelParabolic : integralTransformation.ker ≤ siegelParabolic (Fin 2) ℤ := by
  intro γ hγ
  rcases exists_units_eq_of_mem_ker hγ with ⟨v, hv⟩
  ext i j
  simp [toBlocks₂₁, hv]

variable {k : ℤ} {c : Sym[ℂ]^0 (Fin 2 → ℂ) →ₗ[ℂ] Sym[ℂ]^0 (Fin 2 → ℂ) →ₗ⋆[ℂ] ℂ}
    {G : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^0 (Fin 2 → ℂ)}

/-- The constant seed of the Siegel Eisenstein series. -/
noncomputable def siegelSeed : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^0 (Fin 2 → ℂ) :=
  fun _ ↦ ⨂ₛ[ℂ] _ : Fin 0, Pi.single 0 1

private lemma slash_siegelSeed (δ : symplecticGroup (Fin 2) ℤ) (Z : SiegelUpperHalfSpace (Fin 2)) :
    slash (rhoKJ k 0) (SymplecticGroup.map (Int.castRingHom ℝ) δ) siegelSeed Z =
      siegelEisensteinTerm k Z δ • siegelSeed Z := by
  rw [slash_apply, rhoKJ_denomGL_inv_apply, symPowerRep_zero, siegelEisensteinTerm]
  rfl

private lemma slash_siegelSeed_of_mem (hk' : Even k) {p : symplecticGroup (Fin 2) ℤ}
    (hp : p ∈ siegelParabolic (Fin 2) ℤ) :
    slash (rhoKJ k 0) (SymplecticGroup.map (Int.castRingHom ℝ) p) siegelSeed = siegelSeed := by
  funext Z
  have h : siegelEisensteinTerm k Z (p * 1) = siegelEisensteinTerm k Z 1 :=
    siegelEisensteinTerm_mul k Z 1 hk' ⟨p, hp⟩
  have h₁ : siegelEisensteinTerm k Z (1 : symplecticGroup (Fin 2) ℤ) = 1 := by
    rw [siegelEisensteinTerm, map_one, det_denom_one, one_zpow]
  rw [mul_one, h₁] at h
  rw [slash_siegelSeed, h, one_smul]

private lemma continuous_dual_siegelSeed (φ : Dual ℂ (Sym[ℂ]^0 (Fin 2 → ℂ))) :
    Continuous fun τ ↦ φ (siegelSeed τ) := by
  unfold siegelSeed
  exact continuous_const

private lemma lintegral_tsum_siegelSeed_lt_top (hadm : IsAdmissibleForm (rhoKJ k 0) c) (hk : 3 < k)
    (hG : G ∈ cuspFormsKJ k 0 (integral (Fin 2))) : ∫⁻ τ in siegelSet,
      ∑' x : SiegelParabolicCosets (Fin 2),
        ‖peterssonIntegrand (rhoKJ k 0) c siegelSeed G (integralTransformation x.out • τ)‖ₑ
        ∂invariantMeasure (Fin 2) < ∞ := by
  have hb : IsModerateForm (rhoKJ k 0) c := isModerateForm_rhoKJ k c
  have hk₀ : 0 < k := by
    linarith
  rcases exists_norm_peterssonIntegrand_le (f := siegelSeed) (g := G)
    (A := fun τ ↦ rexp (-π * ((τ.val 0 0).im + (τ.val 1 1).im))) hb (fun φ ψ ↦ by
      rcases exists_norm_dual_le_of_mem_cuspForms hG ψ with ⟨C₂, hC₂, h₂⟩
      refine ⟨‖φ (⨂ₛ[ℂ] _ : Fin 0, Pi.single 0 1)‖ * C₂, fun τ hτ ↦ ?_⟩
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (h₂ τ hτ) (norm_nonneg _)) with ⟨C₁, N, hC₁⟩
  have hS : Summable fun x : SiegelParabolicCosets (Fin 2) ↦ ‖siegelPlucker x.out‖ ^ (-k) :=
    summable_norm_siegelPlucker_zpow hk
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_siegelSet fun τ hτ ↦ ?_)
    (lintegral_siegelSet_mul_pow_lt_top
      (|C₁| * 225 ^ k * ∑' x : SiegelParabolicCosets (Fin 2), ‖siegelPlucker x.out‖ ^ (-k)) N
        Real.pi_pos)
  have hP : 1 ≤ 1 + (τ.val 0 0).im + (τ.val 1 1).im := by
    linarith [four_fifths_le_im_zero_zero hτ, four_fifths_le_im_one_one hτ]
  have hC₂ : ‖peterssonIntegrand (rhoKJ k 0) c siegelSeed G τ‖ ≤
      |C₁| * rexp (-π * ((τ.val 0 0).im + (τ.val 1 1).im)) *
        (1 + (τ.val 0 0).im + (τ.val 1 1).im) ^ N :=
    (hC₁ τ hτ).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C₁) (Real.exp_nonneg _))
        (pow_nonneg (by linarith) N))
  generalize hE : |C₁| * rexp (-π * ((τ.val 0 0).im + (τ.val 1 1).im)) *
    (1 + (τ.val 0 0).im + (τ.val 1 1).im) ^ N = E at hC₂
  have hE₀ : 0 ≤ E := (norm_nonneg _).trans hC₂
  have hterm (x : SiegelParabolicCosets (Fin 2)) :
      ‖peterssonIntegrand (rhoKJ k 0) c siegelSeed G (integralTransformation x.out • τ)‖ₑ ≤
        ENNReal.ofReal (E * (225 ^ k * ‖siegelPlucker x.out‖ ^ (-k))) := by
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [peterssonIntegrand_smul_eq_slash τ hadm hG.1, slash_siegelSeed, map_smul, map_smul,
      LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_comm]
    refine mul_le_mul hC₂ ?_ (norm_nonneg _) hE₀
    refine (norm_siegelEisensteinTerm_le x.out τ hk₀).trans ?_
    exact mul_le_mul_of_nonneg_right (zpow_le_zpow_left₀ hk₀.le (siegelK_pos τ).le (siegelK_le hτ))
      (zpow_nonneg (norm_nonneg _) _)
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun x ↦ by positivity) ((hS.mul_left _).mul_left _),
    tsum_mul_left, tsum_mul_left]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [← hE]
  ring1

/-- **The Siegel Eisenstein series are orthogonal to the cusp forms** (LMFDB
`mf.siegel.subspace.degree.two`): `⟨ψ_k, G⟩ = 0` for even `k > 3`, a cusp form
`G ∈ S_{k,0}(Sp(4, ℤ))` and an admissible form `c`. -/
lemma isPeterssonOrthogonal_siegelEisensteinKJ (hadm : IsAdmissibleForm (rhoKJ k 0) c) (hk : 3 < k)
    (hk' : Even k) (hG : G ∈ cuspFormsKJ k 0 (integral (Fin 2))) :
    IsPeterssonOrthogonal (integral (Fin 2)) (rhoKJ k 0) c (siegelEisensteinKJ k) G := by
  have hb : IsModerateForm (rhoKJ k 0) c := isModerateForm_rhoKJ k c
  have hs : IsFundamentalDomain (transformationGroup (integral (Fin 2)))
      (fundamentalDomain (integral (Fin 2))) (invariantMeasure (Fin 2)) :=
    isFundamentalDomain_fundamentalDomain (isArithmetic_integral (Fin 2))
  refine ⟨integrableOn_peterssonIntegrand hb hadm (siegelEisensteinKJ_mem_modularFormsKJ hk hk') hG
    hs, ?_⟩
  have hf₀ (p : symplecticGroup (Fin 2) ℤ) (hp : p ∈ siegelParabolic (Fin 2) ℤ) :
      slash (rhoKJ k 0) (SymplecticGroup.map (Int.castRingHom ℝ) p) siegelSeed = siegelSeed :=
    slash_siegelSeed_of_mem hk' hp
  have hF (Z : SiegelUpperHalfSpace (Fin 2)) (φ : Dual ℂ (Sym[ℂ]^0 (Fin 2 → ℂ))) :
      HasSum (fun x : SiegelParabolicCosets (Fin 2) ↦ φ (slash (rhoKJ k 0)
        (SymplecticGroup.map (Int.castRingHom ℝ) x.out) siegelSeed Z))
          (φ (siegelEisensteinKJ k Z)) :=
    isVectorSiegelEisensteinSeries_siegelEisensteinKJ hk Z φ
  rw [peterssonProduct, setIntegral_peterssonIntegrand_eq_of_series hb hadm hG.1
    ker_le_siegelParabolic hf₀ continuous_dual_siegelSeed hF
      (lintegral_tsum_siegelSeed_lt_top hadm hk hG) hs (isFundamentalDomain_parabolicDomain 0)]
  refine setIntegral_peterssonIntegrand_eq_zero_of_cornerTranslation hb hG (fun _ _ ↦ rfl)
    continuous_dual_siegelSeed (isFundamentalDomain_parabolicDomain 0) (fun u _ ↦ ?_)
    (peterssonIntegrand_map_integralTransformation_smul hadm hG.1 hf₀)
    (integrableOn_seed_of_lintegral_tsum hb hadm hG.1 ker_le_siegelParabolic hf₀
      continuous_dual_siegelSeed (lintegral_tsum_siegelSeed_lt_top hadm hk hG)
        (isFundamentalDomain_parabolicDomain 0))
  rw [cornerTranslation_smul_parabolicDomain]
  exact isFundamentalDomain_parabolicDomain u

end SiegelUpperHalfSpace
