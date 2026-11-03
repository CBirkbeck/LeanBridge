import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PeterssonConvergence

/-!
# Cusp forms of degree 2 on arithmetic subgroups have positive definite support

A cusp form `F` on an arithmetic subgroup `Γ` of `Sp(4, ℚ)`, with Fourier coefficients `a`, has
`a(n) ≠ 0` only for positive definite `n`, and so it decays exponentially on the Siegel set.

For `U ∈ GL(2, ℤ)` and `n` with `n' = Uᵀ n U`, the term of `n` in the Fourier expansion of `F` at
`U Z Uᵀ` is the exponential of `2πi tr(n' Z)`. Along `Z = diag(τ', it)`, the terms with `n'₁₁ > 0`
tend to `0`, and those with `n'₁₁ = 0` are `e^{2πi n'₀₀ τ'}`, by Koecher's principle. Since
`Φ(F ∣ U)` vanishes, the sum of these terms vanishes, for every `τ'`. For `n'₁₁ = 0`,
`e^{2πi n'₀₀ τ'} = e^{2πi tr(n Z)}` when `τ'` is the corner of `U⁻¹ Z U⁻ᵀ`, so this sum is a Fourier
series on all of `ℋ₂`, whose coefficients vanish by the uniqueness of Fourier expansions. Every
singular positive semidefinite `n` has `n'₁₁ = 0` for some `U`.

## Main results

* `SiegelUpperHalfSpace.posDef_of_forall_siegelOperatorVanishes_slash_levi`: the support of a form
  whose Siegel operator vanishes after `GL(2, ℤ)` is positive definite.
* `SiegelUpperHalfSpace.posDef_of_mem_cuspForms`: the support of a cusp form on an arithmetic
  subgroup is positive definite.
* `SiegelUpperHalfSpace.exists_norm_dual_le_of_mem_cuspForms_of_isArithmetic`: a cusp form on an
  arithmetic subgroup decays exponentially on the Siegel set.
* `SiegelUpperHalfSpace.exists_norm_dual_le_of_mem_modularForms_of_isArithmetic`: a modular form on
  an arithmetic subgroup is bounded on the Siegel set.
-/

open Complex Filter Matrix Module Real SymplecticGroup Topology

open scoped UpperHalfPlane

namespace SiegelUpperHalfSpace

variable {Γ : Subgroup (symplecticGroup (Fin 2) ℚ)} {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin 2) ℂ) V} {F : SiegelUpperHalfSpace (Fin 2) → V}
    {a : dualLattice Γ → V} (U : GL (Fin 2) ℤ)

/-- The matrix `Uᵀ n U`. -/
private def leviConj (n : Matrix (Fin 2) (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  ((U : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ))ᵀ * n *
    (U : Matrix (Fin 2) (Fin 2) ℤ).map Int.cast

private lemma fourierExp_smul_levi' (n : dualLattice Γ) (τ : SiegelUpperHalfSpace (Fin 2)) :
    fourierExp n (SymplecticGroup.map (Int.castRingHom ℝ) (levi (Fin 2) ℤ U) • τ) =
      cexp (2 * π * I * ((leviConj U n).map ((↑) : ℚ → ℂ) * τ.val).trace) := by
  have hc : (Rat.castHom ℂ) ∘ (Int.cast : ℤ → ℚ) = (Int.cast : ℤ → ℂ) :=
    funext fun z ↦ map_intCast (Rat.castHom ℂ) z
  rw [fourierExp, val_smul_levi, leviConj]
  congr 2
  rw [← Rat.coe_castHom, Matrix.map_mul, Matrix.map_mul, transpose_map, Matrix.map_map, hc]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm ((U : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℂ))ᵀ]
  simp only [Matrix.mul_assoc]

private lemma posSemidef_leviConj {n : Matrix (Fin 2) (Fin 2) ℚ} (hn : n.PosSemidef) :
    (leviConj U n).PosSemidef := by
  have h : ((U : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ))ᴴ * n *
      (U : Matrix (Fin 2) (Fin 2) ℤ).map Int.cast |>.PosSemidef := hn.conjTranspose_mul_mul_same _
  rwa [conjTranspose_eq_transpose_of_trivial] at h

private lemma cexp_trace_diagPoint (M : Matrix (Fin 2) (Fin 2) ℚ) (τ' : ℍ) (t : Set.Ioi (0 : ℝ)) :
    cexp (2 * π * I * (M.map ((↑) : ℚ → ℂ) * (diagPoint τ' t).val).trace) =
      cexp (2 * π * I * ((M 0 0 : ℚ) * τ')) * rexp (-(2 * π * (0 + t * (M 1 1 : ℝ)))) := by
  rw [ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [trace, diag_apply, Matrix.mul_apply, diagPoint]
  simp
  linear_combination (2 * π * ((M 1 1 : ℂ) * (t : ℝ)) : ℂ) * I_mul_I

private lemma cexp_trace_of_apply_one_one_eq_zero {M : Matrix (Fin 2) (Fin 2) ℚ} (hM : M.PosSemidef)
    (h₁ : M 1 1 = 0) (Z : SiegelUpperHalfSpace (Fin 2)) :
    cexp (2 * π * I * (M.map ((↑) : ℚ → ℂ) * Z.val).trace) =
      cexp (2 * π * I * ((M 0 0 : ℚ) * topLeft Z)) := by
  have h₂ : M 0 1 = 0 := apply_zero_one_eq_zero hM h₁
  have h₃ : M 1 0 = 0 := by
    rw [← h₂]
    simpa using congrFun (congrFun hM.isHermitian 0) 1
  congr 2
  simp [trace, Matrix.mul_apply, h₁, h₂, h₃, coe_topLeft]

variable [FiniteDimensional ℂ V]

private lemma apply_eq_zero_of_siegelOperatorVanishes_slash_levi (hΓ : IsArithmetic Γ)
    (hF : F ∈ modularForms ρ Γ 1) (ha : HasSiegelFourierExpansion Γ F a)
    (hv : SiegelOperatorVanishes (slash ρ (SymplecticGroup.map (Int.castRingHom ℝ)
      (levi (Fin 2) ℤ U)) F)) {n : dualLattice Γ} (hn : leviConj U n 1 1 = 0) : a n = 0 := by
  classical
  have hpsd : ∀ m, a m ≠ 0 → (m : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef :=
    koecherPrinciple ρ hΓ (by simp) F hF a ha
  generalize hg : SymplecticGroup.map (Int.castRingHom ℝ) (levi (Fin 2) ℤ U) = g at hv
  have hterm (φ : Dual ℂ V) (τ' : ℍ) (t : Set.Ioi (0 : ℝ)) (m : dualLattice Γ) :
      fourierExp m (g • diagPoint τ' t) * φ (a m) =
        cexp (2 * π * I * ((leviConj U m 0 0 : ℚ) * τ')) *
          rexp (-(2 * π * (0 + t * (leviConj U m 1 1 : ℝ)))) * φ (a m) := by
    rw [← hg, fourierExp_smul_levi', cexp_trace_diagPoint]
  have hsummable (φ : Dual ℂ V) (τ' : ℍ) : Summable fun m : dualLattice Γ ↦
      if leviConj U m 1 1 = 0 then cexp (2 * π * I * ((leviConj U m 0 0 : ℚ) * τ')) * φ (a m)
      else 0 := by
    refine (ha (g • diagPoint τ' tOne) φ).summable.norm.of_norm_bounded fun m ↦ ?_
    rw [hterm]
    split_ifs with h
    · simp [h]
    · simp
  have hsum (φ : Dual ℂ V) (τ' : ℍ) : ∑' m : dualLattice Γ,
      (if leviConj U m 1 1 = 0 then cexp (2 * π * I * ((leviConj U m 0 0 : ℚ) * τ')) * φ (a m)
        else 0) = 0 := by
    have h₁ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ ∑' m, fourierExp m (g • diagPoint τ' t) * φ (a m))
        atTop (𝓝 (∑' m : dualLattice Γ, if leviConj U m 1 1 = 0 then
          cexp (2 * π * I * ((leviConj U m 0 0 : ℚ) * τ')) * φ (a m) else 0)) := by
      refine tendsto_tsum_of_dominated_convergence (ha (g • diagPoint τ' tOne) φ).summable.norm
        (fun m ↦ ?_) (eventually_atTop.mpr ⟨tOne, fun t ht m ↦ ?_⟩)
      · simp only [hterm]
        split_ifs with h
        · simp [h]
        · by_cases hc : a m = 0
          · simp [hc]
          have h₀ : (0 : ℝ) < (leviConj U m 1 1 : ℝ) := by
            exact_mod_cast (posSemidef_leviConj U (hpsd m hc)).diag_nonneg.lt_of_ne (Ne.symm h)
          refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
          simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
          simpa only [mul_zero, zero_mul] using
            ((tendsto_rexp_mul h₀).const_mul _).mul_const ‖φ (a m)‖
      · rw [hterm, hterm]
        by_cases hc : a m = 0
        · simp [hc]
        have h₀ : (0 : ℝ) ≤ (leviConj U m 1 1 : ℝ) := by
          exact_mod_cast (posSemidef_leviConj U (hpsd m hc)).diag_nonneg
        simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (rexp_mul_le h₀ ht)
          (norm_nonneg _)) (norm_nonneg _)
    have h₂ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ ∑' m, fourierExp m (g • diagPoint τ' t) * φ (a m))
        atTop (𝓝 0) := by
      have hD (Z : SiegelUpperHalfSpace (Fin 2)) : denomGL g Z = denomGL g (diagPoint τ' tOne) :=
        Units.ext <| by
          rw [coe_denomGL, coe_denomGL, ← hg, denom_map_levi, denom_map_levi]
      refine (hv τ' (φ ∘ₗ ρ (denomGL g (diagPoint τ' tOne)))).congr fun t ↦ ?_
      rw [(ha _ φ).tsum_eq, LinearMap.comp_apply, slash_apply, hD (diagPoint τ' t), ← End.mul_apply,
        ← map_mul, mul_inv_cancel, map_one, End.one_apply]
    exact tendsto_nhds_unique h₁ h₂
  refine (forall_dual_apply_eq_zero_iff ℂ _).mp fun φ ↦ ?_
  have hc : (fun m : dualLattice Γ ↦ if leviConj U m 1 1 = 0 then φ (a m) else 0) = 0 := by
    refine eq_zero_of_hasSum_fourierExp (Nat.factorial_ne_zero _)
      (smul_mem_translationLattice_of_isArithmetic · · hΓ) fun Z ↦ ?_
    have hZ : g • g⁻¹ • Z = Z := smul_inv_smul g Z
    have h₁ : HasSum (fun m : dualLattice Γ ↦ if leviConj U m 1 1 = 0 then
        cexp (2 * π * I * ((leviConj U m 0 0 : ℚ) * topLeft (g⁻¹ • Z))) * φ (a m) else 0) 0 :=
      (hsummable φ (topLeft (g⁻¹ • Z))).hasSum_iff.mpr (hsum φ (topLeft (g⁻¹ • Z)))
    refine h₁.congr_fun fun m ↦ ?_
    split_ifs with h
    · by_cases hcm : a m = 0
      · simp [hcm]
      rw [← hZ, ← hg, fourierExp_smul_levi', hg, inv_smul_smul,
        cexp_trace_of_apply_one_one_eq_zero (posSemidef_leviConj U (hpsd m hcm)) h]
    · simp
  simpa [hn] using congrFun hc n

/-- **A form whose Siegel operator vanishes after `GL(2, ℤ)` has positive definite support**: for a
modular form `F` on an arithmetic `Γ`, with Fourier coefficients `a` and with `Φ(F ∣ U) = 0` for
every `U ∈ GL(2, ℤ)`, one has `a(n) ≠ 0` only for positive definite `n`. A singular positive
semidefinite `n` has `(Uᵀ n U)₁₁ = 0` for some `U`, and `Φ(F ∣ U) = 0` gives `a(n) = 0`. -/
lemma posDef_of_forall_siegelOperatorVanishes_slash_levi (hΓ : IsArithmetic Γ)
    (hF : F ∈ modularForms ρ Γ 1) (ha : HasSiegelFourierExpansion Γ F a)
    (hv : ∀ U : GL (Fin 2) ℤ, SiegelOperatorVanishes
      (slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) (levi (Fin 2) ℤ U)) F)) (n : dualLattice Γ)
    (hn : a n ≠ 0) : (n : Matrix (Fin 2) (Fin 2) ℚ).PosDef := by
  have hpsd : (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef :=
    koecherPrinciple ρ hΓ (by simp) F hF a ha n hn
  refine hpsd.posDef_iff_det_ne_zero.mpr fun hd ↦ hn ?_
  have hs : (n : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 :=
    congrFun (congrFun n.2.1 0) 1
  have hd' : (n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 * (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 =
      (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 * (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 := by
    rwa [det_fin_two, hs, sub_eq_zero] at hd
  rcases exists_isCoprime_quad_eq_zero hd' with ⟨x, y, hxy, hq⟩
  rcases ModularGroup.bottom_row_surj (a := ![x, y]) (by simpa using hxy) with ⟨g, -, hg⟩
  let W : GL (Fin 2) ℤ := (SpecialLinearGroup.transpose g : SpecialLinearGroup (Fin 2) ℤ)
  have hW₀ : (W : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = x :=
    congrFun hg 0
  have hW₁ : (W : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = y :=
    congrFun hg 1
  refine apply_eq_zero_of_siegelOperatorVanishes_slash_levi W hΓ hF ha (hv W) ?_
  simp [leviConj, Matrix.mul_apply, hW₀, hW₁, hs]
  linear_combination hq

/-- **The support of a cusp form on an arithmetic subgroup is positive definite.** -/
lemma posDef_of_mem_cuspForms (hΓ : IsArithmetic Γ) (hF : F ∈ cuspForms ρ Γ 1)
    (ha : HasSiegelFourierExpansion Γ F a) (n : dualLattice Γ) (hn : a n ≠ 0) :
    (n : Matrix (Fin 2) (Fin 2) ℚ).PosDef :=
  posDef_of_forall_siegelOperatorVanishes_slash_levi hΓ hF.1 ha (fun U ↦ by
    rw [← map_algebraMap_map_intCast]
    exact hF.2 _) n hn

/-- **A cusp form on an arithmetic subgroup decays exponentially on the Siegel set**, through every
linear form: the support of its Fourier expansion is positive definite, and the entries of an
element of the dual lattice lie in `(2 N)⁻¹ ℤ`, for `N` the factorial of the index of
`Γ ∩ Sp(4, ℤ)` in `Sp(4, ℤ)`. -/
lemma exists_norm_dual_le_of_mem_cuspForms_of_isArithmetic (hΓ : IsArithmetic Γ)
    (hF : F ∈ cuspForms ρ Γ 1) : ∃ c : ℝ, 0 < c ∧ ∀ φ : Dual ℂ V, ∃ C, 0 ≤ C ∧ ∀ Z ∈ siegelSet,
      ‖φ (F Z)‖ ≤ C * rexp (-c * ((Z.val 0 0).im + (Z.val 1 1).im)) := by
  rcases exists_hasSiegelFourierExpansion ρ hΓ hF.1 with ⟨a, ha⟩
  have hpd (n : dualLattice Γ) (hn : a n ≠ 0) : (n : Matrix (Fin 2) (Fin 2) ℚ).PosDef :=
    posDef_of_mem_cuspForms hΓ hF ha n hn
  generalize hN : (Γ.relIndex (integral (Fin 2))).factorial = N
  have hN₀ : 0 < N := hN ▸ Nat.factorial_pos _
  have hn (n : dualLattice Γ) (hn : a n ≠ 0) (i : Fin 2) :
      (1 / (2 * N) : ℚ) ≤ (n : Matrix (Fin 2) (Fin 2) ℚ) i i := by
    rcases exists_intCast_eq (N := N) (fun i j ↦ hN ▸ smul_mem_translationLattice_of_isArithmetic
      i j hΓ) n (i, i) with ⟨z, hz⟩
    have h₀ : 0 < (n : Matrix (Fin 2) (Fin 2) ℚ) i i := (hpd n hn).diag_pos
    have hz₀ : (0 : ℚ) < z := hz ▸ by positivity
    have hz₁ : (1 : ℚ) ≤ z := by
      exact_mod_cast (by exact_mod_cast hz₀ : 0 < z)
    rw [div_le_iff₀ (by positivity), mul_comm]
    exact hz₁.trans_eq hz
  have hε : (0 : ℝ) < ((1 / (2 * N) : ℚ) : ℝ) := by
    push_cast
    positivity
  refine ⟨π * ((1 / (2 * N) : ℚ) : ℝ), mul_pos Real.pi_pos hε, fun φ ↦ ?_⟩
  exact exists_norm_dual_le_of_posDef ha (fun n hn ↦ (hpd n hn).posSemidef) (fun n h ↦ hn n h 0)
    (fun n h ↦ hn n h 1) φ

/-- **A modular form on an arithmetic subgroup is bounded on the Siegel set**, through every linear
form, by Koecher's principle. -/
lemma exists_norm_dual_le_of_mem_modularForms_of_isArithmetic (hΓ : IsArithmetic Γ)
    (hF : F ∈ modularForms ρ Γ 1) (φ : Dual ℂ V) : ∃ C, 0 ≤ C ∧ ∀ Z ∈ siegelSet, ‖φ (F Z)‖ ≤ C := by
  rcases exists_hasSiegelFourierExpansion ρ hΓ hF with ⟨a, ha⟩
  exact exists_norm_dual_le_of_posSemidef ha (koecherPrinciple ρ hΓ (by simp) F hF a ha) φ

end SiegelUpperHalfSpace
