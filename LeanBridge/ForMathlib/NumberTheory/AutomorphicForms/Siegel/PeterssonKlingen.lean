import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PeterssonUnfolding

/-!
# The Klingen–Eisenstein series are orthogonal to the cusp forms

The vector-valued Klingen–Eisenstein series `E(f)` of weight `ρ_{k,j}`, for even `k > 4`, is the
series `∑_{δ ∈ Q \ Sp(4, ℤ)} f₀ ∣ δ` of the function `f₀(Z) = f(z₀₀) e₁^j`, with `Q` the Klingen
parabolic subgroup. The translations `T_u : Z ↦ Z + u E₁₁` lie in the centre of the unipotent
radical of `Q(ℝ)` and commute with `Q(ℤ)`, so they permute the fundamental domains of `Q`, and they
fix `f₀`. So `⟨E(f), G⟩` vanishes for a cusp form `G`, by unfolding and averaging. The absolute
convergence on the Siegel set follows from the estimate of the terms of `E(f)`
(`SiegelUpperHalfSpace.norm_dual_vectorKlingenTerm_le`), whose constant `klingenConst` is bounded on
the Siegel set.

## Main results

* `SiegelUpperHalfSpace.klingenConst_le`: the constant of the estimate is bounded on the Siegel set.
* `SiegelUpperHalfSpace.map_mul_cornerTranslation`: the translations `T_u` commute with the Klingen
  parabolic subgroup of `Sp(4, ℤ)`.
* `SiegelUpperHalfSpace.isPeterssonOrthogonal_vectorKlingenEisenstein`: `⟨E(f), G⟩ = 0` for a cusp
  form `G`.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open Complex MeasureTheory Module Real Set SymplecticGroup

open scoped ComplexConjugate ENNReal MatrixGroups ModularForm Pointwise TensorProduct UpperHalfPlane

namespace SiegelUpperHalfSpace

/-! ### The constant on the Siegel set -/

section Constant

variable {Z : SiegelUpperHalfSpace (Fin 2)}

private lemma im_sum_div_det_le (hZ : Z ∈ siegelSet) :
    (|(Z.val 0 0).im| + |(Z.val 0 1).im| + |(Z.val 1 1).im|) /
      ((Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im * (Z.val 1 0).im) ≤ 5 := by
  have hZs : Z.val 1 0 = Z.val 0 1 := Z.val_one_zero
  have h₀ : 4 / 5 ≤ (Z.val 0 0).im := four_fifths_le_im_zero_zero hZ
  have h₁ : 4 / 5 ≤ (Z.val 1 1).im := four_fifths_le_im_one_one hZ
  have h₂ : |(Z.val 0 1).im| ≤ (Z.val 0 0).im := abs_im_zero_one_le hZ
  have h₃ : (Z.val 0 0).im ≤ (Z.val 1 1).im := hZ.2.2.1
  have hd :
      (Z.val.map im).det = (Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im * (Z.val 1 0).im := by
    simp [det_fin_two]
  have h₄ : 3 / 4 * ((Z.val 0 0).im * (Z.val 1 1).im) ≤ (Z.val.map im).det := mul_le_det_im hZ
  rw [hd] at h₄
  have hpos : 0 < (Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im * (Z.val 1 0).im := by
    nlinarith
  rw [div_le_iff₀ hpos, abs_of_nonneg (show 0 ≤ (Z.val 0 0).im by linarith),
    abs_of_nonneg (show 0 ≤ (Z.val 1 1).im by linarith)]
  nlinarith

private lemma abs_re_le (hZ : Z ∈ siegelSet) (i j : Fin 2) : |(Z.val i j).re| ≤ 1 / 2 :=
  hZ.1 i j

private lemma imK_le (hZ : Z ∈ siegelSet) : imK Z.val ≤ 27 / 2 := by
  have h₁ : (|(Z.val 0 0).im| + |(Z.val 0 1).im| + |(Z.val 1 1).im|) /
      ((Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im * (Z.val 1 0).im) ≤ 5 :=
    im_sum_div_det_le hZ
  have h₂ : |(Z.val 0 0).re| ≤ 1 / 2 := abs_re_le hZ 0 0
  have h₃ : |(Z.val 0 1).re| ≤ 1 / 2 := abs_re_le hZ 0 1
  have h₄ : |(Z.val 1 1).re| ≤ 1 / 2 := abs_re_le hZ 1 1
  have h₅ : 1 + (|(Z.val 0 0).re| + |(Z.val 0 1).re| + |(Z.val 1 1).re|) ≤ 5 / 2 := by
    linarith
  have h₆ : 0 ≤ (|(Z.val 0 0).im| + |(Z.val 0 1).im| + |(Z.val 1 1).im|) /
      ((Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im * (Z.val 1 0).im) :=
    div_nonneg (by positivity) (det_im_pos Z).le
  rw [imK]
  nlinarith [mul_le_mul h₅ h₁ h₆ (by norm_num)]

private lemma half_le_imLam (hZ : Z ∈ siegelSet) : 1 / 2 ≤ imLam Z.val := by
  have hZs : Z.val 1 0 = Z.val 0 1 := Z.val_one_zero
  have h₀ : 4 / 5 ≤ (Z.val 0 0).im := four_fifths_le_im_zero_zero hZ
  have h₁ : 4 / 5 ≤ (Z.val 1 1).im := four_fifths_le_im_one_one hZ
  have h₃ : (Z.val 0 0).im ≤ (Z.val 1 1).im := hZ.2.2.1
  have hd :
      (Z.val.map im).det = (Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im * (Z.val 1 0).im := by
    simp [det_fin_two]
  have h₄ : 3 / 4 * ((Z.val 0 0).im * (Z.val 1 1).im) ≤ (Z.val.map im).det := mul_le_det_im hZ
  rw [hd] at h₄
  refine Real.le_sqrt_of_sq_le ?_
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- **The constant of the estimate of the Klingen–Eisenstein series is bounded on the Siegel
set.** -/
lemma klingenConst_le (j : ℕ) {k : ℤ} (hk : 0 ≤ k) (hZ : Z ∈ siegelSet) :
    klingenConst j k Z.val ≤ 2 ^ j * 27 ^ k := by
  have h₁ : 1 / 2 ≤ imLam Z.val := half_le_imLam hZ
  have h₂ : imK Z.val ≤ 27 / 2 := imK_le hZ
  have hL : 0 < imLam Z.val := imLam_pos Z
  have hK : 0 < imK Z.val := imK_pos Z
  rw [klingenConst]
  refine mul_le_mul ?_ ?_ (zpow_nonneg (div_pos hK hL).le _) (by positivity)
  · rw [zpow_neg, zpow_natCast, ← inv_pow]
    refine pow_le_pow_left₀ (inv_pos.mpr hL).le ?_ j
    rw [inv_le_comm₀ hL two_pos]
    linarith
  · refine zpow_le_zpow_left₀ hk (div_pos hK hL).le ?_
    rw [div_le_iff₀ hL]
    linarith

end Constant

/-! ### The translations commute with the Klingen parabolic subgroup -/

variable {γ : symplecticGroup (Fin 2) ℤ}

private lemma coe_cornerTranslation (u : ℝ) :
    (cornerTranslation u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) = 1 +
      u • single (.inl 1) (.inr 1) 1 := by
  ext (x | x) (y | y) <;> fin_cases x <;> fin_cases y <;>
    simp [cornerTranslation, coe_symTranslation]

private lemma apply_inl_one_inl_one_of_mem (hγ : γ ∈ klingenParabolicTwo) :
    γ.1 (.inl 1) (.inl 1) = γ.1 (.inr 1) (.inr 1) := by
  rcases id hγ with ⟨v, hv⟩
  have h : (γ.1 * J (Fin 2) ℤ * γ.1ᵀ) (.inl 1) (.inr 1) = J (Fin 2) ℤ (.inl 1) (.inr 1) :=
    congrFun (congrFun (mem_iff.mp γ.2) (.inl 1)) (.inr 1)
  have e : (γ.1 * J (Fin 2) ℤ * γ.1ᵀ) (.inl 1) (.inr 1) = -(γ.1 (.inl 1) (.inl 1) * (v : ℤ)) := by
    simp [Matrix.mul_apply, J, hv]
  have h₁ : J (Fin 2) ℤ (.inl 1) (.inr 1) = -1 := by
    simp [J]
  rw [e, h₁, neg_inj] at h
  have h₂ : γ.1 (.inr 1) (.inr 1) = (v : ℤ) := by
    simpa using hv (.inr 1)
  rw [h₂]
  rcases Int.units_eq_one_or v with rfl | rfl
  · simpa using h
  · simp only [Units.val_neg, Units.val_one] at h
    simp only [Units.val_neg, Units.val_one]
    omega

/-- **The translations `T_u` commute with the Klingen parabolic subgroup of `Sp(4, ℤ)`.** -/
lemma map_mul_cornerTranslation (hγ : γ ∈ klingenParabolicTwo) (u : ℝ) :
    SymplecticGroup.map (Int.castRingHom ℝ) γ * cornerTranslation u =
      cornerTranslation u * SymplecticGroup.map (Int.castRingHom ℝ) γ := by
  rcases id hγ with ⟨v, hv⟩
  have hdiag : γ.1 (.inl 1) (.inl 1) = γ.1 (.inr 1) (.inr 1) := apply_inl_one_inl_one_of_mem hγ
  refine Subtype.ext ?_
  rw [Submonoid.coe_mul, Submonoid.coe_mul, coe_cornerTranslation, SymplecticGroup.coe_map_apply,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  congr 2
  ext x y
  by_cases hy : y = .inr 1
  · subst hy
    by_cases hx : x = .inl 1
    · subst hx
      simp [hdiag]
    · have h₁ : γ.1 x (.inl 1) = 0 := apply_inl_one_of_mem hγ hx
      rw [mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ hx]
      simp [h₁]
  · have h₂ : γ.1 (.inr 1) y = 0 := by
      simp [hv, hy]
    rw [mul_single_apply_of_ne _ _ _ _ _ hy]
    by_cases hx : x = .inl 1
    · subst hx
      rw [single_mul_apply_same]
      simp [h₂]
    · rw [single_mul_apply_of_ne _ _ _ _ _ hx]

lemma cornerTranslation_smul_comm (hγ : γ ∈ klingenParabolicTwo) (u : ℝ)
    (x : SiegelUpperHalfSpace (Fin 2)) : cornerTranslation u • integralTransformation γ • x =
      integralTransformation γ • cornerTranslation u • x := by
  rw [integralTransformation_smul, integralTransformation_smul, ← mul_smul, ← mul_smul,
    map_mul_cornerTranslation hγ]

/-! ### The Klingen parabolic subgroup and the kernel -/

private lemma ker_le_klingenParabolicTwo : integralTransformation.ker ≤ klingenParabolicTwo := by
  intro γ hγ
  rcases exists_units_eq_of_mem_ker hγ with ⟨v, hv⟩
  exact ⟨v, fun x ↦ by
    rw [hv]
    simp [eq_comm]⟩

/-! ### Orthogonality -/

variable {k : ℤ} {j : ℕ} (f : CuspForm 𝒮ℒ (k + j))
    {c : Sym[ℂ]^j (Fin 2 → ℂ) →ₗ[ℂ] Sym[ℂ]^j (Fin 2 → ℂ) →ₗ⋆[ℂ] ℂ}
    {G : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)}

/-- The seed `f₀(Z) = f(z₀₀) e₁^j` of the Klingen–Eisenstein series of `f`. -/
private noncomputable def klingenSeed : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ) :=
  fun Z ↦ vectorKlingenTerm Z k j f 1

private lemma slash_klingenSeed (δ : symplecticGroup (Fin 2) ℤ) (Z : SiegelUpperHalfSpace (Fin 2)) :
    slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) δ) (klingenSeed f) Z =
      vectorKlingenTerm Z k j f δ := by
  rw [slash_apply, klingenSeed, vectorKlingenTerm_one, vectorKlingenTerm, map_smul]

private lemma slash_klingenSeed_of_mem (hk' : Even k) {δ : symplecticGroup (Fin 2) ℤ}
    (hδ : δ ∈ klingenParabolicTwo) :
    slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) δ) (klingenSeed f) =
      klingenSeed f := by
  funext Z
  have h : vectorKlingenTerm Z k j f (δ * 1) = vectorKlingenTerm Z k j f 1 :=
    vectorKlingenTerm_mul Z (δ := 1) hk' (cuspForm_apply_smul f) hδ
  rw [mul_one] at h
  rw [slash_klingenSeed, h]
  rfl

private lemma klingenSeed_cornerTranslation_smul (u : ℝ) (Z : SiegelUpperHalfSpace (Fin 2)) :
    klingenSeed f (cornerTranslation u • Z) = klingenSeed f Z := by
  have h : topLeft (cornerTranslation u • Z) = topLeft Z := by
    ext
    simp [coe_topLeft, val_cornerTranslation_smul]
  simp only [klingenSeed, vectorKlingenTerm_one, h]

private lemma continuous_dual_klingenSeed (φ : Dual ℂ (Sym[ℂ]^j (Fin 2 → ℂ))) :
    Continuous fun τ ↦ φ (klingenSeed f τ) := by
  have h : Continuous fun τ : SiegelUpperHalfSpace (Fin 2) ↦ f (topLeft τ) :=
    (isHolomorphic_topLeft (u := f) f.holo').continuous_dual LinearMap.id
  have e (τ : SiegelUpperHalfSpace (Fin 2)) :
      φ (klingenSeed f τ) = f (topLeft τ) * φ (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1) := by
    rw [klingenSeed, vectorKlingenTerm_one, map_smul, smul_eq_mul]
  simp only [e]
  exact h.mul continuous_const

private lemma lintegral_tsum_klingenSeed_lt_top (hadm : IsAdmissibleForm (rhoKJ k j) c) (hk : 4 < k)
    (hG : G ∈ cuspFormsKJ k j (integral (Fin 2))) : ∫⁻ τ in siegelSet, ∑' x : KlingenCosetsTwo,
      ‖peterssonIntegrand (rhoKJ k j) c (klingenSeed f) G (integralTransformation x.out • τ)‖ₑ
        ∂invariantMeasure (Fin 2) < ∞ := by
  have hb : IsModerateForm (rhoKJ k j) c := isModerateForm_rhoKJ k c
  have hk₀ : 0 < k := by
    linarith
  rcases exists_nonneg_bound f with ⟨C, hC, hf⟩
  have h₁ (r : Fin j → Fin 2) : ∃ (C₁ : ℝ) (N : ℕ), ∀ τ ∈ siegelSet,
      ‖c (rhoKJ k j (imGL τ) (⨂ₛ[ℂ] i, Pi.single (r i) 1)) (G τ)‖ ≤
        C₁ * rexp (-π * ((τ.val 0 0).im + (τ.val 1 1).im)) *
          (1 + (τ.val 0 0).im + (τ.val 1 1).im) ^ N :=
    exists_norm_peterssonIntegrand_le hb fun φ ψ ↦ by
      rcases exists_norm_dual_le_of_mem_cuspForms hG ψ with ⟨C₂, hC₂, h₂⟩
      refine ⟨‖φ (⨂ₛ[ℂ] i, Pi.single (r i) 1)‖ * C₂, fun τ hτ ↦ ?_⟩
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (h₂ τ hτ) (norm_nonneg _)
  choose C₁ N₁ hC₁ using h₁
  let N : ℕ := ∑ r, N₁ r
  let D : ℝ := C * (∑ r, |C₁ r|) * (2 ^ j * 27 ^ k)
  have hS : Summable fun x : KlingenCosetsTwo ↦ ‖bottomRow x.out‖ ^ (-k) :=
    summable_norm_bottomRow_zpow hk
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_siegelSet fun τ hτ ↦ ?_)
    (lintegral_siegelSet_mul_pow_lt_top
      (D * ∑' x : KlingenCosetsTwo, ‖bottomRow x.out‖ ^ (-k)) N Real.pi_pos)
  have hP : 1 ≤ 1 + (τ.val 0 0).im + (τ.val 1 1).im := by
    linarith [four_fifths_le_im_zero_zero hτ, four_fifths_le_im_one_one hτ]
  generalize hE : rexp (-π * ((τ.val 0 0).im + (τ.val 1 1).im)) *
    (1 + (τ.val 0 0).im + (τ.val 1 1).im) ^ N = E
  have hE₀ : 0 ≤ E := by
    rw [← hE]
    positivity
  have hdual : dualBound ((c.flip (G τ)) ∘ₗ rhoKJ k j (imGL τ)) ≤ (∑ r, |C₁ r|) * E := by
    rw [dualBound, Finset.sum_mul]
    refine Finset.sum_le_sum fun r _ ↦ ?_
    refine (hC₁ r τ hτ).trans ?_
    rw [← hE, mul_assoc]
    refine mul_le_mul (le_abs_self _) (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _))
      (by positivity) (abs_nonneg _)
    exact pow_le_pow_right₀ hP (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ r))
  have hterm (x : KlingenCosetsTwo) :
      ‖peterssonIntegrand (rhoKJ k j) c (klingenSeed f) G (integralTransformation x.out • τ)‖ₑ ≤
        ENNReal.ofReal (D * E * ‖bottomRow x.out‖ ^ (-k)) := by
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [peterssonIntegrand_smul_eq_slash τ hadm hG.1, slash_klingenSeed]
    refine (norm_dual_vectorKlingenTerm_le τ ((c.flip (G τ)) ∘ₗ rhoKJ k j (imGL τ)) x.out hC hf
      hk₀).trans ?_
    have h₃ : klingenConst j k τ.val ≤ 2 ^ j * 27 ^ k := klingenConst_le j hk₀.le hτ
    have h₄ : 0 ≤ ‖bottomRow x.out‖ ^ (-k) := zpow_nonneg (norm_nonneg _) _
    refine mul_le_mul_of_nonneg_right ?_ h₄
    have h₅ : 0 ≤ klingenConst j k τ.val :=
      mul_nonneg (zpow_nonneg (imLam_pos τ).le _)
        (zpow_nonneg (div_pos (imK_pos τ) (imLam_pos τ)).le _)
    refine (mul_le_mul (mul_le_mul_of_nonneg_left hdual hC) h₃ h₅ (by positivity)).trans_eq ?_
    simp only [D]
    ring1
  have hD : 0 ≤ D := by
    positivity
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun x ↦ by positivity) (hS.mul_left _), tsum_mul_left]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [← hE]
  ring1

/-- **The Klingen–Eisenstein series are orthogonal to the cusp forms** (LMFDB
`mf.siegel.subspace.degree.two`): `⟨E(f), G⟩ = 0` for even `k > 4`, a cusp form `f` of weight
`k + j` on `SL(2, ℤ)`, a cusp form `G ∈ S_{k,j}(Sp(4, ℤ))` and an admissible form `c`. -/
lemma isPeterssonOrthogonal_vectorKlingenEisenstein (hadm : IsAdmissibleForm (rhoKJ k j) c)
    (hk : 4 < k) (hk' : Even k) (hG : G ∈ cuspFormsKJ k j (integral (Fin 2))) :
    IsPeterssonOrthogonal (integral (Fin 2)) (rhoKJ k j) c (vectorKlingenEisenstein k j f) G := by
  have hb : IsModerateForm (rhoKJ k j) c := isModerateForm_rhoKJ k c
  have hs : IsFundamentalDomain (transformationGroup (integral (Fin 2)))
      (fundamentalDomain (integral (Fin 2))) (invariantMeasure (Fin 2)) :=
    isFundamentalDomain_fundamentalDomain (isArithmetic_integral (Fin 2))
  refine ⟨integrableOn_peterssonIntegrand hb hadm
    (vectorKlingenEisenstein_mem_modularFormsKJ f hk hk') hG hs, ?_⟩
  have hF' : IsFundamentalDomain (klingenParabolicTwo.map integralTransformation)
      (⋃ x : KlingenCosetsTwo, integralTransformation x.out • fundamentalDomain (integral (Fin 2)))
        (invariantMeasure (Fin 2)) :=
    hs.iUnion_smul_of_transversal (fun _ ↦ hs.nullMeasurableSet_smul _)
      (bijective_integralTransformation_out _ ker_le_klingenParabolicTwo)
  have hf₀ (p : symplecticGroup (Fin 2) ℤ) (hp : p ∈ klingenParabolicTwo) :
      slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) p) (klingenSeed f) =
        klingenSeed f :=
    slash_klingenSeed_of_mem f hk' hp
  have hF (Z : SiegelUpperHalfSpace (Fin 2)) (φ : Dual ℂ (Sym[ℂ]^j (Fin 2 → ℂ))) :
      HasSum (fun x : KlingenCosetsTwo ↦ φ (slash (rhoKJ k j)
        (SymplecticGroup.map (Int.castRingHom ℝ) x.out) (klingenSeed f) Z))
          (φ (vectorKlingenEisenstein k j f Z)) :=
    (hasSum_dual_vectorKlingenEisenstein f Z φ hk).congr_fun fun x ↦ by
      rw [slash_klingenSeed]
  rw [peterssonProduct, setIntegral_peterssonIntegrand_eq_of_series hb hadm hG.1
    ker_le_klingenParabolicTwo hf₀ (continuous_dual_klingenSeed f) hF
      (lintegral_tsum_klingenSeed_lt_top f hadm hk hG) hs hF']
  refine setIntegral_peterssonIntegrand_eq_zero_of_cornerTranslation hb hG
    (klingenSeed_cornerTranslation_smul f) (continuous_dual_klingenSeed f) hF'
    (fun u _ ↦ hF'.smul_of_forall_smul_comm fun g x ↦ ?_)
    (peterssonIntegrand_map_integralTransformation_smul hadm hG.1 hf₀)
    (integrableOn_seed_of_lintegral_tsum hb hadm hG.1 ker_le_klingenParabolicTwo hf₀
      (continuous_dual_klingenSeed f) (lintegral_tsum_klingenSeed_lt_top f hadm hk hG) hF')
  rcases g with ⟨_, p, hp, rfl⟩
  exact cornerTranslation_smul_comm hp u x

end SiegelUpperHalfSpace
