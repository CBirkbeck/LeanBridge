import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.CuspCriterion
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.VectorKlingenEisenstein
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.VectorSiegelEisensteinVanishing

/-!
# The Siegel operator on `M_{k,j}(Sp(4, ℤ))`

For `F ∈ M_{k,j}(Sp(4, ℤ))` of weight `ρ_{k,j} = det^k ⊗ Sym^j` with Fourier coefficients `a`, the
limit `Φ(F)(τ') = lim_{t → ∞} F(diag(τ', it))` exists and is `∑_{n₁₁ = 0} a(n) e^{2πi n₀₀ τ'}`. By
Koecher's principle such an `n` is `diag(m, 0)`, which is fixed by `n ↦ D n Dᵀ` for
`D = (1, 1; 0, 1)`, so `a(n)` is fixed by `ρ_{k,j}(D)`, hence it is a multiple of `e₁^j`:
`Φ(F) = u e₁^j` for a function `u` on the upper half-plane. The transformation law of `F` under the
embedding of `SL(2, ℤ)` makes `u` a modular form of weight `k + j` on `SL(2, ℤ)`. For `j > 0` it is
a cusp form, the constant coefficient `a(0)` being fixed by `ρ_{k,j}(GL(2, ℤ))`, hence `0`.

## Main definitions

* `SiegelUpperHalfSpace.siegelOperatorSeries`: the series of `u`.
* `SiegelUpperHalfSpace.siegelOperatorKJ` (LMFDB `mf.siegel.phi`): the modular form `u = Φ(F)`.
* `SiegelUpperHalfSpace.siegelOperatorCuspKJ`: the cusp form `u = Φ(F)`, if `a(0)` vanishes.

## Main results

* `SiegelUpperHalfSpace.apply_eq_smul_tprod`: `a(n)` is a multiple of `e₁^j` for `n₁₁ = 0`.
* `SiegelUpperHalfSpace.apply_zero_eq_zero`: `a(0) = 0` for `j > 0`.
* `SiegelUpperHalfSpace.differentiableAt_tsum_phiTerm`: the series is holomorphic.
* `SiegelUpperHalfSpace.isBoundedAtImInfty_tsum_phiTerm`: the series is bounded at `i∞`.
* `SiegelUpperHalfSpace.tendsto_tsum_phiTerm_atImInfty`: the series tends to `d(0)` at `i∞`.
* `SiegelUpperHalfSpace.tendsto_dual_diagPoint_siegelOperatorSeries`,
  `SiegelUpperHalfSpace.tendsto_dual_diagPoint_siegelOperatorKJ` (LMFDB `mf.siegel.phi`):
  `F(diag(τ', it)) → u(τ') e₁^j` as `t → ∞`.
* `SiegelUpperHalfSpace.siegelOperatorSeries_smul`: the transformation law of `u`.
* `SiegelUpperHalfSpace.symConstCoeff_apply_zero_eq_zero`: if `u` is a cusp form, the coefficient of
  `e₁^j` in `a(0)` vanishes.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open Complex Filter Metric Module Real SymplecticGroup TauCeti Topology

open GeneralLinearGroup (transposeGL)

open scoped Manifold MatrixGroups ModularForm TensorProduct UpperHalfPlane

namespace SiegelUpperHalfSpace

variable {k : ℤ} {j : ℕ}

/-! ### The highest weight line -/

private lemma rhoKJ_diag_tprod {w : ℂ} {g : GL (Fin 2) ℂ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = !![w, 0; 0, 1]) (hw : w ≠ 0) :
    rhoKJ k j g (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1) = w ^ (k + j) • ⨂ₛ[ℂ] _ : Fin j,
      (Pi.single 0 1 : Fin 2 → ℂ) := by
  have h₁ : (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ (Pi.single 0 1 : Fin 2 → ℂ) =
      w • (Pi.single 0 1 : Fin 2 → ℂ) := by
    rw [hg]
    ext a
    fin_cases a <;> simp
  rw [rhoKJ_tprod, h₁, tprod_smul, smul_smul, Units.val_zpow_eq_zpow_val,
    GeneralLinearGroup.val_det_apply, hg, det_fin_two_of, zpow_add₀ hw]
  simp

/-! ### The Fourier coefficients of `n` with `n₁₁ = 0` -/

variable {F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)}
    {b : dualLattice (integral (Fin 2)) → Sym[ℂ]^j (Fin 2 → ℂ)}

lemma posSemidef_of_apply_ne_zero (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) (n : dualLattice (integral (Fin 2)))
    (hn : b n ≠ 0) : (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef :=
  koecherPrinciple (rhoKJ k j) (isArithmetic_integral (Fin 2)) (by simp) F hF b hb n hn

/-- **The Fourier coefficient `a(n)` is a multiple of `e₁^j` for `n₁₁ = 0`**: such an `n` is
`diag(m, 0)` by Koecher's principle, it is fixed by `n ↦ D n Dᵀ` for `D = (1, 1; 0, 1)`, so that
`a(n)` is fixed by `ρ_{k,j}(D)`. -/
lemma apply_eq_smul_tprod (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) {n : dualLattice (integral (Fin 2))}
    (hn : (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0) :
    b n = symConstCoeff j (b n) • ⨂ₛ[ℂ] _ : Fin j, (Pi.single 0 1 : Fin 2 → ℂ) := by
  by_cases h : b n = 0
  · simp [h]
  refine eq_smul_tprod_of_symPowerRep_eq ?_
  have h01 : (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = 0 :=
    apply_zero_one_eq_zero (posSemidef_of_apply_ne_zero hF hb n h) hn
  have h10 : (n : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := by
    rw [← h01]
    exact congrFun (congrFun n.2.1 0) 1
  have hU : ((transposeGL (ModularGroup.T : GL (Fin 2) ℤ) : GL (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 1, 1] := by
    ext a c
    fin_cases a <;> fin_cases c <;> simp [transposeGL]
  have hfix :
      dualLevi (transposeGL (ModularGroup.T : GL (Fin 2) ℤ)) (leviRat_mem_integral _) n = n :=
    Subtype.ext <| by
      rw [coe_dualLevi, hU]
      ext a c
      fin_cases a <;> fin_cases c <;> simp [Matrix.mul_apply, hn, h01, h10]
  have h₁ : b (dualLevi (transposeGL (ModularGroup.T : GL (Fin 2) ℤ)) (leviRat_mem_integral _) n) =
      rhoKJ k j (GeneralLinearGroup.map (Int.castRingHom ℂ) (ModularGroup.T : GL (Fin 2) ℤ))
        (b n) :=
    apply_dualLevi_transposeGL (rhoKJ k j) n (ModularGroup.T : GL (Fin 2) ℤ)
      (leviRat_mem_integral _) (isArithmetic_integral (Fin 2)) hF hb
  rw [hfix, rhoKJ_eq_symPowerRep] at h₁
  exact h₁.symm

/-- **The constant Fourier coefficient is fixed by `ρ_{k,j}(GL(2, ℤ))`**, so it vanishes for
`j > 0`. -/
lemma apply_zero_eq_zero (hj : j ≠ 0) (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) : b 0 = 0 := by
  refine eq_zero_of_isGLIntInvariant k hj fun D ↦ ?_
  have h₁ : b (dualLevi (transposeGL D) (leviRat_mem_integral _) 0) =
      rhoKJ k j (GeneralLinearGroup.map (Int.castRingHom ℂ) D) (b 0) :=
    apply_dualLevi_transposeGL (rhoKJ k j) 0 D (leviRat_mem_integral _)
      (isArithmetic_integral (Fin 2)) hF hb
  have hfix : dualLevi (transposeGL D) (leviRat_mem_integral _) 0 = 0 := Subtype.ext <| by
    rw [coe_dualLevi]
    simp
  rw [hfix] at h₁
  exact h₁.symm

/-! ### The series `∑ d(n) e^{2πi n₀₀ z}` -/

variable {Γ : Subgroup (symplecticGroup (Fin 2) ℚ)} {d : dualLattice Γ → ℂ}

private lemma norm_cexp_mul_I (q : ℚ) (z : ℂ) :
    ‖cexp (2 * π * I * ((q : ℂ) * z))‖ = rexp (-(2 * π * ((q : ℝ) * z.im))) := by
  rw [Complex.norm_exp]
  congr 1
  simp

private lemma norm_phiTerm_anti (hpsd : ∀ n, d n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef)
    (n : dualLattice Γ) {z w : ℂ} (h : z.im ≤ w.im) : ‖phiTerm d w n‖ ≤ ‖phiTerm d z n‖ := by
  by_cases hn : (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0
  · rw [phiTerm, phiTerm, ite_eq_left hn, ite_eq_left hn, norm_mul, norm_mul]
    by_cases hd : d n = 0
    · simp [hd]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [norm_cexp_mul_I, norm_cexp_mul_I]
    have h₀ : (0 : ℝ) ≤ ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) := by
      exact_mod_cast (hpsd n hd).diag_nonneg
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_le_mul_of_nonneg_left h h₀, Real.pi_pos]
  · simp [phiTerm, hn]

/-- **The series `∑ d(n) e^{2πi n₀₀ z}` is holomorphic on the upper half-plane.** -/
lemma differentiableAt_tsum_phiTerm (hs : ∀ τ, Summable fun n ↦ fourierExp n τ * d n)
    (hpsd : ∀ n, d n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    DifferentiableAt ℂ (fun z ↦ ∑' n, phiTerm d z n) z₀ := by
  let τ₁ : ℍ := ⟨(z₀.im / 2 : ℝ) * I, by simpa using half_pos hz₀⟩
  refine differentiableAt_tsum_of_bound (summable_phiTerm τ₁ hs).norm (div_pos hz₀ (by norm_num :
    (0 : ℝ) < 6)) (fun n ↦ ?_) (fun n z hz ↦ norm_phiTerm_anti hpsd n ?_)
  · by_cases hn : (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0
    · simp only [phiTerm, ite_eq_left hn]
      fun_prop
    · simp only [phiTerm, ite_eq_right hn]
      exact differentiableOn_const _
  · have h₁ : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
      simpa using abs_im_le_norm (z - z₀)
    have h₂ : ‖z - z₀‖ < 3 * (z₀.im / 6) := by
      simpa [dist_eq_norm] using hz
    have h₃ : (τ₁ : ℂ).im = z₀.im / 2 := by
      simp [τ₁]
    rw [h₃]
    have h₄ : -(3 * (z₀.im / 6)) < z.im - z₀.im := (abs_lt.mp (h₁.trans_lt h₂)).1
    linarith

/-- **The series `∑ d(n) e^{2πi n₀₀ τ'}` is bounded at `i∞`.** -/
lemma isBoundedAtImInfty_tsum_phiTerm (hs : ∀ τ, Summable fun n ↦ fourierExp n τ * d n)
    (hpsd : ∀ n, d n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) :
    UpperHalfPlane.IsBoundedAtImInfty fun τ' : ℍ ↦ ∑' n, phiTerm d τ' n := by
  refine UpperHalfPlane.isBoundedAtImInfty_iff.mpr ⟨∑' n, ‖phiTerm d UpperHalfPlane.I n‖, 1,
    fun τ hτ ↦ ?_⟩
  have h₁ : Summable fun n ↦ ‖phiTerm d UpperHalfPlane.I n‖ :=
    (summable_phiTerm UpperHalfPlane.I hs).norm
  have hle (n : dualLattice Γ) : ‖phiTerm d τ n‖ ≤ ‖phiTerm d UpperHalfPlane.I n‖ :=
    norm_phiTerm_anti hpsd n (by simpa using hτ)
  have h₂ : Summable fun n ↦ ‖phiTerm d τ n‖ :=
    h₁.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
  exact (norm_tsum_le_tsum_norm h₂).trans (h₂.tsum_le_tsum hle h₁)

/-- **The series `∑ d(n) e^{2πi n₀₀ τ'}` tends to `d(0)` at `i∞`**, by dominated convergence, for
`n ≠ 0` positive semidefinite with `n₁₁ = 0` has `n₀₀ > 0`. -/
lemma tendsto_tsum_phiTerm_atImInfty (hs : ∀ τ, Summable fun n ↦ fourierExp n τ * d n)
    (hpsd : ∀ n, d n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) :
    Tendsto (fun τ : ℍ ↦ ∑' n, phiTerm d τ n) UpperHalfPlane.atImInfty (𝓝 (d 0)) := by
  classical
  have him : Tendsto (fun τ : ℍ ↦ τ.im) UpperHalfPlane.atImInfty atTop := tendsto_comap
  have hlim (n : dualLattice Γ) : Tendsto (fun τ : ℍ ↦ phiTerm d τ n) UpperHalfPlane.atImInfty
      (𝓝 (if n = 0 then d 0 else 0)) := by
    split_ifs with hn₀
    · subst hn₀
      simp [phiTerm]
    by_cases hn : (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0
    · by_cases hd : d n = 0
      · simp [phiTerm, hd]
      have h01 : (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = 0 :=
        apply_zero_one_eq_zero (hpsd n hd) hn
      have h10 : (n : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := by
        rw [← h01]
        exact congrFun (congrFun n.2.1 0) 1
      have h00 : (n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 ≠ 0 := fun h ↦ hn₀ <| Subtype.ext <| by
        ext a c
        fin_cases a <;> fin_cases c <;> simp [h, h01, h10, hn]
      have hpos : (0 : ℝ) < ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) := by
        exact_mod_cast lt_of_le_of_ne (hpsd n hd).diag_nonneg (Ne.symm h00)
      refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
      simp only [phiTerm, ite_eq_left hn, norm_mul, norm_cexp_mul_I]
      have h₁ : Tendsto (fun τ : ℍ ↦ rexp (-(2 * π * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) *
          (τ : ℂ).im)))) UpperHalfPlane.atImInfty (𝓝 0) :=
        Real.tendsto_exp_atBot.comp <| tendsto_neg_atTop_atBot.comp <|
          (him.const_mul_atTop hpos).const_mul_atTop two_pi_pos
      simpa using h₁.mul_const ‖d n‖
    · simp [phiTerm, hn]
  have hb : ∀ᶠ τ : ℍ in UpperHalfPlane.atImInfty, ∀ n : dualLattice Γ,
      ‖phiTerm d τ n‖ ≤ ‖phiTerm d UpperHalfPlane.I n‖ := by
    filter_upwards [him.eventually_ge_atTop 1] with τ hτ n
    exact norm_phiTerm_anti hpsd n (by simpa using hτ)
  have key : Tendsto (fun τ : ℍ ↦ ∑' n, phiTerm d τ n) UpperHalfPlane.atImInfty
      (𝓝 (∑' n : dualLattice Γ, if n = 0 then d 0 else 0)) :=
    tendsto_tsum_of_dominated_convergence (summable_phiTerm UpperHalfPlane.I hs).norm hlim hb
  rwa [tsum_ite_eq] at key

/-! ### The modular form `Φ(F)` -/

variable (g : SL(2, ℤ)) (τ' : ℍ)

lemma smul_diagPoint_embedFirst (t : Set.Ioi (0 : ℝ)) :
    SymplecticGroup.map (Int.castRingHom ℝ) (embedFirst g) • diagPoint τ' t =
      diagPoint (g • τ') t := by
  have hw : (g 1 0 : ℂ) * τ' + (g 1 1 : ℂ) ≠ 0 := by
    have h : UpperHalfPlane.denom (g : GL (Fin 2) ℝ) τ' ≠ 0 :=
      UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) τ'
    simpa [UpperHalfPlane.denom] using h
  have hd : denom (SymplecticGroup.map (Int.castRingHom ℝ) (embedFirst g)) (diagPoint τ' t).val =
      !![(g 1 0 : ℂ) * τ' + (g 1 1 : ℂ), 0; 0, 1] := by
    ext a c
    fin_cases a <;> fin_cases c <;>
      simp [denom, diagPoint, embedFirst, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply]
  have hn : num (SymplecticGroup.map (Int.castRingHom ℝ) (embedFirst g)) (diagPoint τ' t).val =
      !![(g 0 0 : ℂ) * τ' + (g 0 1 : ℂ), 0; 0, (t : ℝ) * I] := by
    ext a c
    fin_cases a <;> fin_cases c <;>
      simp [num, diagPoint, embedFirst, toBlocks₁₁, toBlocks₁₂, Matrix.mul_apply]
  have hi : (!![(g 1 0 : ℂ) * τ' + (g 1 1 : ℂ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ =
      !![((g 1 0 : ℂ) * τ' + (g 1 1 : ℂ))⁻¹, 0; 0, 1] := by
    refine inv_eq_right_inv ?_
    ext a c
    fin_cases a <;> fin_cases c <;> simp [hw]
  have hc :
      ((g • τ' : ℍ) : ℂ) = ((g 0 0 : ℂ) * τ' + (g 0 1 : ℂ)) / ((g 1 0 : ℂ) * τ' + (g 1 1 : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp
  have e : (diagPoint (g • τ') t).val = !![((g 0 0 : ℂ) * τ' + (g 0 1 : ℂ)) /
      ((g 1 0 : ℂ) * τ' + (g 1 1 : ℂ)), 0; 0, (t : ℝ) * I] := by
    rw [← hc]
    rfl
  refine SiegelUpperHalfSpace.ext ?_
  rw [val_smul, hd, hn, hi, e]
  ext a c
  fin_cases a <;> fin_cases c <;> simp [div_eq_mul_inv]

lemma coe_denomGL_embedFirst (t : Set.Ioi (0 : ℝ)) :
    (denomGL (SymplecticGroup.map (Int.castRingHom ℝ) (embedFirst g)) (diagPoint τ' t) :
      Matrix (Fin 2) (Fin 2) ℂ) = !![(g 1 0 : ℂ) * τ' + (g 1 1 : ℂ), 0; 0, 1] := by
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [denom, diagPoint, embedFirst, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply]

variable (b) in
/-- The series `u(z) = ∑_{n₁₁ = 0} ψ(a(n)) e^{2πi n₀₀ z}` of the Fourier coefficients `a` of a
function `F : ℋ₂ → Sym^j(ℂ²)`, with `ψ(e₁^j) = 1`. -/
noncomputable def siegelOperatorSeries (z : ℂ) : ℂ :=
  ∑' n, phiTerm (fun n ↦ symConstCoeff j (b n)) z n

/-- **The Siegel operator on `M_{k,j}(Sp(4, ℤ))`**: `F(diag(τ', it)) → u(τ') e₁^j` as `t → ∞`. -/
lemma tendsto_dual_diagPoint_siegelOperatorSeries (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) (φ : Dual ℂ (Sym[ℂ]^j (Fin 2 → ℂ))) :
    Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ φ (F (diagPoint τ' t))) atTop
      (𝓝 (siegelOperatorSeries b τ' * φ (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1))) := by
  have h : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ φ (F (diagPoint τ' t))) atTop
      (𝓝 (∑' n, phiTerm (fun n ↦ φ (b n)) τ' n)) :=
    tendsto_dual_diagPoint τ' φ hb (posSemidef_of_apply_ne_zero hF hb)
  have e : ∑' n, phiTerm (fun n ↦ φ (b n)) τ' n =
      siegelOperatorSeries b τ' * φ (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1) := by
    rw [siegelOperatorSeries, ← tsum_mul_right]
    refine tsum_congr fun n ↦ ?_
    by_cases hn : (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0
    · simp only [phiTerm, ite_eq_left hn]
      conv_lhs => rw [apply_eq_smul_tprod hF hb hn]
      rw [map_smul, smul_eq_mul]
      ring1
    · simp [phiTerm, hn]
  rwa [e] at h

private lemma summable_fourierExp_mul (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b)
    (τ : SiegelUpperHalfSpace (Fin 2)) : Summable fun n ↦ fourierExp n τ * symConstCoeff j (b n) :=
  (hb τ _).summable

private lemma posSemidef_of_symConstCoeff_ne_zero (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) (n : dualLattice (integral (Fin 2)))
    (hn : symConstCoeff j (b n) ≠ 0) : (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef :=
  posSemidef_of_apply_ne_zero hF hb n fun h ↦ hn (by rw [h, map_zero])

private lemma siegelOperatorSeries_eq_lim (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) : Tendsto
    (fun t : Set.Ioi (0 : ℝ) ↦ symConstCoeff j (F (diagPoint τ' t))) atTop
      (𝓝 (siegelOperatorSeries b τ')) := by
  simpa [symConstCoeff_tprod_single] using
    tendsto_dual_diagPoint_siegelOperatorSeries τ' hF hb (symConstCoeff j)

/-- **The transformation law of `Φ(F)`**: `u(gτ') = (cτ' + d)^{k + j} u(τ')` for `g ∈ SL(2, ℤ)`,
from the transformation law of `F` under `(diag(a, 1), diag(b, 0); diag(c, 0), diag(d, 1))`. -/
lemma siegelOperatorSeries_smul (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) : siegelOperatorSeries b (g • τ' : ℍ) =
    ((g 1 0 : ℂ) * τ' + (g 1 1 : ℂ)) ^ (k + j) * siegelOperatorSeries b τ' := by
  have hw : (g 1 0 : ℂ) * τ' + (g 1 1 : ℂ) ≠ 0 := by
    have h : UpperHalfPlane.denom (g : GL (Fin 2) ℝ) τ' ≠ 0 :=
      UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) τ'
    simpa [UpperHalfPlane.denom] using h
  let D : GL (Fin 2) ℂ := denomGL (SymplecticGroup.map (Int.castRingHom ℝ) (embedFirst g))
    (diagPoint τ' tOne)
  have hD : (D : Matrix (Fin 2) (Fin 2) ℂ) = !![(g 1 0 : ℂ) * τ' + (g 1 1 : ℂ), 0; 0, 1] :=
    coe_denomGL_embedFirst g τ' _
  have hdG (t : Set.Ioi (0 : ℝ)) :
      denomGL (SymplecticGroup.map (Int.castRingHom ℝ) (embedFirst g)) (diagPoint τ' t) = D :=
    Units.ext <| (coe_denomGL_embedFirst g τ' t).trans hD.symm
  have hF₁ (t : Set.Ioi (0 : ℝ)) : F (diagPoint (g • τ') t) = rhoKJ k j D (F (diagPoint τ' t)) := by
    have h : F (SymplecticGroup.map (algebraMap ℚ ℝ) (SymplecticGroup.map (Int.castRingHom ℚ)
        (embedFirst g)) • diagPoint τ' t) = ((1 : (integral (Fin 2)) →* ℂˣ)
          ⟨_, embedFirst g, trivial, rfl⟩ : ℂ) • rhoKJ k j (denomGL (SymplecticGroup.map
            (algebraMap ℚ ℝ) (SymplecticGroup.map (Int.castRingHom ℚ) (embedFirst g)))
              (diagPoint τ' t)) (F (diagPoint τ' t)) :=
      hF.2 ⟨_, embedFirst g, trivial, rfl⟩ (diagPoint τ' t)
    simp only [map_algebraMap_map_intCast, MonoidHom.one_apply, Units.val_one, one_smul,
      smul_diagPoint_embedFirst, hdG t] at h
    exact h
  have h₁ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ (symConstCoeff j ∘ₗ rhoKJ k j D)
      (F (diagPoint τ' t))) atTop (𝓝 (siegelOperatorSeries b τ' *
        (symConstCoeff j ∘ₗ rhoKJ k j D) (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1))) :=
    tendsto_dual_diagPoint_siegelOperatorSeries τ' hF hb _
  have h₂ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ symConstCoeff j (F (diagPoint (g • τ') t))) atTop
      (𝓝 (siegelOperatorSeries b (g • τ' : ℍ))) :=
    siegelOperatorSeries_eq_lim (g • τ') hF hb
  simp only [hF₁] at h₂
  have h₃ : siegelOperatorSeries b (g • τ' : ℍ) = _ := tendsto_nhds_unique h₂ h₁
  rw [h₃, LinearMap.comp_apply, rhoKJ_diag_tprod hD hw, map_smul, symConstCoeff_tprod_single,
    smul_eq_mul, mul_one, mul_comm]

private lemma slash_siegelOperatorSeries (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) :
    (fun τ' : ℍ ↦ siegelOperatorSeries b τ') ∣[k + j] g = fun τ' : ℍ ↦
      siegelOperatorSeries b τ' := by
  ext τ'
  have hw : UpperHalfPlane.denom g τ' ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ'
  have e : UpperHalfPlane.denom g τ' = (g 1 0 : ℂ) * τ' + (g 1 1 : ℂ) := by
    simp [UpperHalfPlane.denom]
  rw [ModularForm.SL_slash_apply, siegelOperatorSeries_smul _ _ hF hb, ← e, zpow_neg, mul_comm,
    ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hw), one_mul]

private lemma mdifferentiable_siegelOperatorSeries (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) :
    MDiff (fun τ' : ℍ ↦ siegelOperatorSeries b τ') := by
  refine UpperHalfPlane.mdifferentiable_iff.mpr fun z hz ↦ ?_
  refine ((differentiableAt_tsum_phiTerm (summable_fourierExp_mul hb)
    (posSemidef_of_symConstCoeff_ne_zero hF hb) hz).differentiableWithinAt).congr (fun w hw ↦ ?_) ?_
  · simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    rfl
  · simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    rfl

variable (k j F b) in
/-- **The image of `F ∈ M_{k,j}(Sp(4, ℤ))` under the Siegel operator**: the modular form
`u(τ') = ∑ ψ(a(n)) e^{2πi n₀₀ τ'}` of weight `k + j` on `SL(2, ℤ)`, with `Φ(F) = u e₁^j`. -/
noncomputable def siegelOperatorKJ (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) : ModularForm 𝒮ℒ (k + j) where
  toFun τ' := siegelOperatorSeries b τ'
  slash_action_eq' := fun _ ⟨g, hg⟩ ↦ hg ▸ slash_siegelOperatorSeries g hF hb
  holo' := mdifferentiable_siegelOperatorSeries hF hb
  bdd_at_cusps' hc := (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun g _ ↦
    (slash_siegelOperatorSeries g hF hb).symm ▸ isBoundedAtImInfty_tsum_phiTerm
      (summable_fourierExp_mul hb) (posSemidef_of_symConstCoeff_ne_zero hF hb)

lemma coe_siegelOperatorKJ (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) :
    siegelOperatorKJ k j F b hF hb τ' = siegelOperatorSeries b τ' :=
  rfl

/-- **The Siegel operator on `M_{k,j}(Sp(4, ℤ))`**: `F(diag(τ', it)) → Φ(F)(τ') e₁^j` as `t → ∞`,
with `Φ(F)` a modular form of weight `k + j` on `SL(2, ℤ)`. -/
lemma tendsto_dual_diagPoint_siegelOperatorKJ (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) (φ : Dual ℂ (Sym[ℂ]^j (Fin 2 → ℂ))) :
    Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ φ (F (diagPoint τ' t))) atTop
      (𝓝 (siegelOperatorKJ k j F b hF hb τ' * φ (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1))) :=
  tendsto_dual_diagPoint_siegelOperatorSeries τ' hF hb φ

private lemma tendsto_siegelOperatorSeries_atImInfty
    (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) : Tendsto
    (fun τ' : ℍ ↦ siegelOperatorSeries b τ') UpperHalfPlane.atImInfty (𝓝 (symConstCoeff j (b 0))) :=
  tendsto_tsum_phiTerm_atImInfty (summable_fourierExp_mul hb)
    (posSemidef_of_symConstCoeff_ne_zero hF hb)

/-- The image of `F ∈ M_{k,j}(Sp(4, ℤ))` under the Siegel operator, as a cusp form, when the
constant Fourier coefficient vanishes. This is the case for `j > 0`, as `a(0) = 0`. -/
noncomputable def siegelOperatorCuspKJ (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) (h₀ : symConstCoeff j (b 0) = 0) :
    CuspForm 𝒮ℒ (k + j) where
  toFun τ' := siegelOperatorSeries b τ'
  slash_action_eq' := fun _ ⟨g, hg⟩ ↦ hg ▸ slash_siegelOperatorSeries g hF hb
  holo' := mdifferentiable_siegelOperatorSeries hF hb
  zero_at_cusps' hc := (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr fun g _ ↦
    (slash_siegelOperatorSeries g hF hb).symm ▸ (by
      have h : Tendsto (fun τ' : ℍ ↦ siegelOperatorSeries b τ') UpperHalfPlane.atImInfty
          (𝓝 (symConstCoeff j (b 0))) :=
        tendsto_siegelOperatorSeries_atImInfty hF hb
      rw [h₀] at h
      exact h)

lemma coe_siegelOperatorCuspKJ (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) (h₀ : symConstCoeff j (b 0) = 0) :
    siegelOperatorCuspKJ hF hb h₀ τ' = siegelOperatorSeries b τ' :=
  rfl

/-- **The constant coefficient of a Siegel modular form whose Siegel operator is a cusp form
vanishes.** -/
lemma symConstCoeff_apply_zero_eq_zero (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) (f : CuspForm 𝒮ℒ (k + j))
    (hf : ∀ τ' : ℍ, siegelOperatorSeries b τ' = f τ') : symConstCoeff j (b 0) = 0 := by
  have h₁ : Tendsto (fun τ' : ℍ ↦ siegelOperatorSeries b τ') UpperHalfPlane.atImInfty
      (𝓝 (symConstCoeff j (b 0))) :=
    tendsto_siegelOperatorSeries_atImInfty hF hb
  have h₂ : Tendsto (fun τ' : ℍ ↦ f τ') UpperHalfPlane.atImInfty (𝓝 0) :=
    CuspFormClass.zero_at_infty f
  exact tendsto_nhds_unique (h₁.congr hf) h₂

end SiegelUpperHalfSpace
