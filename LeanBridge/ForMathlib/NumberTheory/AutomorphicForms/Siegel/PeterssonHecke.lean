import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PeterssonUnfolding
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.VectorHeckeStability

/-!
# The adjoints of the Hecke operators for the Petersson product on `Sp(4, ℤ)`

Let `Γ = Sp(4, ℤ)`. An element `x` of the semigroup `S = GSp(4, ℚ)⁺ ∩ M₄(ℤ)`, with multiplier
`r(x)`, has the adjoint `x^* = r(x) x⁻¹ = J⁻¹ xᵀ J` in `S`, and `[f ∣ x, g](τ) = [f, g ∣ x^*](x τ)`
for the Petersson integrand of an admissible form. So the terms of `[T_D F, G]`, for the double
coset `D = Γ x Γ`, and those of `[F, T_{D^*} G]`, for `D^* = Γ x^* Γ`, are all translates of the
single function `[F, G ∣ x^*]`. They are indexed by the transversals of the two stabilisers
`Γ ∩ x⁻¹ Γ x` and `Γ ∩ x Γ x⁻¹` in `Γ`, which `x` conjugates into each other, and this gives the
adjoint formula `∫ [T_D F, G] = ∫ [F, T_{D^*} G]` over a fundamental domain of `Γ`.

The integrals converge since `G ∣ x` decays exponentially on the Siegel set for a cusp form `G`: by
Iwasawa decomposition `x = g p diag(r, r, 1, 1)`, with `g ∈ Γ` and `p` in the rational Siegel
parabolic subgroup, `G ∣ x` is `G` at a point whose imaginary part is a multiple of `A (Im Z) Aᵀ`,
and the Fourier expansion of `G` is supported on positive definite matrices.

As the Hecke operators preserve the cusp forms, they preserve the Petersson orthogonal complement
`N_{j,k}(Γ₂)` of the cusp forms, in every weight (LMFDB `mf.siegel.subspace.degree.two`).

## Main definitions

* `SiegelUpperHalfSpace.heckeAdjoint`: the adjoint `x^*` of `x`.
* `SiegelUpperHalfSpace.heckeAdjointCoset`: the double coset of the adjoint of a representative.

## Main results

* `SiegelUpperHalfSpace.exists_norm_dual_heckeMonoidSlash_le`: `G ∣ x` decays exponentially on the
  Siegel set, for a cusp form `G`.
* `SiegelUpperHalfSpace.tendsto_dual_heckeMonoidSlash_scalarPoint`: `G ∣ x` tends to `0` along
  `diag(it, it)`, for a modular form `G` with vanishing constant term.
* `SiegelUpperHalfSpace.toSp_mul_eq_one`: if `β' β` is scalar then `β'` acts as the inverse of `β`.
* `SiegelUpperHalfSpace.peterssonIntegrand_gspSlash`: `[f ∣ β, g](τ) = [f, g ∣ β'](β τ)`.
* `SiegelUpperHalfSpace.coe_eq_or_eq_neg_of_forall_smul_eq`: two elements of `Sp(4, ℝ)` acting in
  the same way on `ℋ₂` agree up to sign.
* `SiegelUpperHalfSpace.setIntegral_peterssonIntegrand_heckeOperator`: the adjoint formula on a
  fundamental domain, for a moderate admissible form.
* `SiegelUpperHalfSpace.heckeAdjointCoset_mk`: `D^*` does not depend on the representative of `D`.
* `SiegelUpperHalfSpace.heckeAdjointCoset_mk_of_transpose_eq`: the double coset of a symmetric
  element is its own adjoint, and so are those of the knowl's generators
  (`SiegelUpperHalfSpace.heckeAdjointCoset_heckeT`,
  `SiegelUpperHalfSpace.heckeAdjointCoset_heckeTi`).
* `SiegelUpperHalfSpace.peterssonProduct_heckeOperator`: `⟨T_D F, G⟩ = ⟨F, T_{D^*} G⟩` on
  `M_{j,k}(Γ₂)`.
* `SiegelUpperHalfSpace.peterssonProduct_heckeT`: `T(p)` is self-adjoint.
* `SiegelUpperHalfSpace.heckeOperator_mem_cuspFormsOrthogonalKJ`: the Hecke operators preserve
  `N_{j,k}(Γ₂)`.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open Complex Equiv MeasureTheory Module Real Set SymplecticGroup DoubleCoset

open scoped ComplexConjugate ENNReal Pointwise TensorProduct

namespace SiegelUpperHalfSpace

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin 2) ℂ) V}
    {b : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

/-! ### The slash of a cusp form by an element of the Hecke monoid on the Siegel set -/

section Decay

variable {G : SiegelUpperHalfSpace (Fin 2) → V}

private lemma exists_heckeMonoidSlash_eq (x : heckeMonoid (Fin 2)) :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℚ) (s : ℚ)
      (T : SiegelUpperHalfSpace (Fin 2) → SiegelUpperHalfSpace (Fin 2)) (L : V →ₗ[ℂ] V), A.det ≠ 0 ∧
      0 < s ∧ (∀ Z i j, ((T Z).val i j).im =
        s * ∑ k, ∑ l, (A i k : ℝ) * (Z.val k l).im * (A j l : ℝ)) ∧
      ∀ G ∈ modularForms ρ (integral (Fin 2)) 1, ∀ Z, heckeMonoidSlash ρ x G Z = L (G (T Z)) := by
  rcases exists_eq_thetaPrimeDiag_mul x with ⟨r, γ, hx⟩
  rcases exists_mem_integral_inv_mul_mem_siegelParabolic (thetaPrimeDiagConj r γ) with ⟨g, hg, hp⟩
  generalize hγ₂ : thetaPrimeDiagConj r γ = γ₂ at hp
  have hx' : (x : GL (Fin 2 ⊕ Fin 2) ℚ) = spRatToGL (Fin 2) γ₂ *
      (thetaPrimeDiag r : GL (Fin 2 ⊕ Fin 2) ℚ) := by
    rw [hx, ← hγ₂, spRatToGL_thetaPrimeDiagConj, inv_mul_cancel_right]
  generalize hp' : g⁻¹ * γ₂ = p at hp
  generalize hP : SymplecticGroup.map (algebraMap ℚ ℝ) p = P
  have hPm : P ∈ siegelParabolic (Fin 2) ℝ := hP ▸ map_mem_siegelParabolic hp
  have hP₀ : P.1.toBlocks₂₁ = 0 := hPm
  have hd (Z : SiegelUpperHalfSpace (Fin 2)) : denomGL P Z = denomGL P (scalarPoint tOne) :=
    Units.ext <| by
      simp only [coe_denomGL, denom, hP₀, Matrix.map_zero _ ofReal_zero, Matrix.zero_mul]
  have hden (τ : SiegelUpperHalfSpace (Fin 2)) :
      gspDenomGL (submonoidToGSpPlus (thetaPrimeDiag r)) τ = 1 :=
    Units.ext <| by rw [coe_gspDenomGL, gspDenom_thetaPrimeDiag, Units.val_one]
  have hA : p.1.toBlocks₁₁.det ≠ 0 := by
    have h : (p.1.toBlocks₁₁ * p.1.toBlocks₂₂ᵀ).det = det 1 :=
      congrArg det (toBlocks₁₁_mul_transpose_toBlocks₂₂ hp)
    rw [det_mul, det_one] at h
    exact left_ne_zero_of_mul_eq_one h
  have hT (Z : SiegelUpperHalfSpace (Fin 2)) (i j : Fin 2) :
      ((P • gspSmul (submonoidToGSpPlus (thetaPrimeDiag r)) Z).val i j).im =
        (((r : ℕ) : ℚ) : ℝ) * ∑ k, ∑ l, (p.1.toBlocks₁₁ i k : ℝ) * (Z.val k l).im *
          (p.1.toBlocks₁₁ j l : ℝ) := by
    rw [im_smul_of_mem_siegelParabolic hPm, ← hP]
    simp [gspSmul_thetaPrimeDiag, toBlocks₁₁]
    ring1
  refine ⟨_, _, _, ((multiplier (submonoidToGSpPlus (thetaPrimeDiag r)) : ℂ) ^ slashExponent ρ) •
    ρ (denomGL P (scalarPoint tOne))⁻¹, hA, by positivity, hT, fun G hG Z ↦ ?_⟩
  have hG' : slash ρ (SymplecticGroup.map (algebraMap ℚ ℝ) g) G = G := by
    simpa using ((mem_modularForms_iff_slash ρ G _ 1).mp hG).2 ⟨g, hg⟩
  have e₁ : heckeMonoidSlash ρ x G = heckeMonoidSlash ρ (thetaPrimeDiag r) (slash ρ P G) := by
    have e₂ : heckeMonoidSlash ρ x G = heckeMonoidSlash ρ (spToGSpPlusGL γ₂ * thetaPrimeDiag r) G :=
      congrArg (gspSlash ρ · G) (Subtype.ext (congrArg Units.val hx'))
    have e₃ : slash ρ (SymplecticGroup.map (algebraMap ℚ ℝ) γ₂) G = slash ρ P G := by
      rw [← hP, ← hp']
      conv_lhs => rw [← mul_inv_cancel_left g γ₂, map_mul, slash_mul, hG']
    rw [e₂, heckeMonoidSlash_mul, heckeMonoidSlash_eq_slash ρ _ (coe_spToGSpPlusGL γ₂), e₃]
  rw [e₁]
  simp [heckeMonoidSlash, gspSlash, hden, slash_apply, hd]

variable [FiniteDimensional ℂ V]

/-- **The slash of a cusp form on `Sp(4, ℤ)` by an element of the Hecke monoid decays exponentially
on the Siegel set**, for `x ∈ GSp(4, ℚ)⁺ ∩ M₄(ℤ)`. -/
lemma exists_norm_dual_heckeMonoidSlash_le (hG : G ∈ cuspForms ρ (integral (Fin 2)) 1)
    (x : heckeMonoid (Fin 2)) : ∃ ε : ℝ, 0 < ε ∧ ∀ ψ : Dual ℂ V, ∃ C, 0 ≤ C ∧ ∀ Z ∈ siegelSet,
      ‖ψ (heckeMonoidSlash ρ x G Z)‖ ≤ C * rexp (-ε * ((Z.val 0 0).im + (Z.val 1 1).im)) := by
  rcases exists_heckeMonoidSlash_eq (ρ := ρ) x with ⟨A, s, T, L, hA, hs, hT, hL⟩
  rcases exists_hasSiegelFourierExpansion ρ (isArithmetic_integral (Fin 2)) hG.1 with ⟨a, ha⟩
  have hv : SiegelOperatorVanishes G := by
    have h : SiegelOperatorVanishes (slash ρ (SymplecticGroup.map (algebraMap ℚ ℝ) 1) G) := hG.2 1
    rwa [map_one, slash_one] at h
  rcases exists_norm_dual_comp_le_of_posDef ha vecMulVec_mem_translationLattice
    (posDef_of_siegelOperatorVanishes hG.1 ha hv) hA hs hT with ⟨ε, hε, h⟩
  refine ⟨ε, hε, fun ψ ↦ ?_⟩
  rcases h (ψ ∘ₗ L) with ⟨C, hC, h⟩
  refine ⟨C, hC, fun Z hZ ↦ ?_⟩
  rw [hL G hG.1 Z]
  exact h Z hZ

/-- **The slash of a modular form on `Sp(4, ℤ)` with vanishing constant term by an element of the
Hecke monoid tends to `0` along `diag(it, it)`.** -/
lemma tendsto_dual_heckeMonoidSlash_scalarPoint (hG : G ∈ modularForms ρ (integral (Fin 2)) 1)
    {a : dualLattice (integral (Fin 2)) → V} (ha : HasSiegelFourierExpansion (integral (Fin 2)) G a)
    (h₀ : a 0 = 0) (x : heckeMonoid (Fin 2)) (ψ : Dual ℂ V) :
    Filter.Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ ψ (heckeMonoidSlash ρ x G (scalarPoint t)))
      Filter.atTop (nhds 0) := by
  rcases exists_heckeMonoidSlash_eq (ρ := ρ) x with ⟨A, s, T, L, hA, hs, hT, hL⟩
  simpa only [hL G hG, LinearMap.comp_apply, h₀, map_zero] using tendsto_dual_comp_scalarPoint ha
    (koecherPrinciple ρ (isArithmetic_integral (Fin 2)) (by simp) G hG a ha) hA hs hT (ψ ∘ₗ L)

end Decay

/-! ### The Petersson integrand of a slash by `GSp(4, ℚ)⁺` -/

variable {β β' : gspPlus (Fin 2)}

private lemma multiplier_eq_of_mul
    (h : ((β' * β : gspPlus (Fin 2)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) =
      multiplier β • 1) : multiplier β' = multiplier β := by
  have h₁ : multiplier (β' * β) = multiplier β * multiplier β :=
    multiplier_eq _ <| by
      rw [h, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, smul_smul]
  rw [multiplier_mul] at h₁
  exact mul_right_cancel₀ (multiplier_pos β).ne' h₁

/-- **`β' β` scalar means that `β'` acts as the inverse of `β`.** -/
lemma toSp_mul_eq_one (h : ((β' * β : gspPlus (Fin 2)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) =
    multiplier β • 1) : toSp β' * toSp β = 1 := by
  rw [← toSp_mul]
  ext a c
  have hm : multiplier (β' * β) = multiplier β * multiplier β := by
    rw [multiplier_mul, multiplier_eq_of_mul h]
  have hr : (0 : ℝ) < (multiplier β : ℝ) := Rat.cast_pos.mpr (multiplier_pos β)
  have hs : √((multiplier (β' * β) : ℚ) : ℝ) = (multiplier β : ℝ) := by
    rw [hm, Rat.cast_mul, Real.sqrt_mul_self hr.le]
  simp only [toSp, hs, h]
  have h₁ : ((1 : symplecticGroup (Fin 2) ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) = 1 := rfl
  rw [h₁]
  by_cases hac : a = c
  · subst hac
    simp [hr.ne']
  · simp [one_apply_ne hac]

/-- **Moving a slash across the Petersson integrand**: if `β' β = r(β)` is scalar, then
`[f ∣ β, g](τ) = [f, g ∣ β'](β τ)` for an admissible form. -/
lemma peterssonIntegrand_gspSlash (hadm : IsAdmissibleForm ρ b)
    (h : ((β' * β : gspPlus (Fin 2)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) =
      multiplier β • 1) (f g : SiegelUpperHalfSpace (Fin 2) → V)
    (τ : SiegelUpperHalfSpace (Fin 2)) : peterssonIntegrand ρ b (gspSlash ρ β f) g τ =
      peterssonIntegrand ρ b f (gspSlash ρ β' g) (toSp β • τ) := by
  have hm : multiplier β' = multiplier β := multiplier_eq_of_mul h
  have hδ : toSp β' * toSp β = 1 := toSp_mul_eq_one h
  have hr : (√(multiplier β : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr <| Real.sqrt_ne_zero'.mpr <| Rat.cast_pos.mpr <| multiplier_pos β
  let c : GL (Fin 2) ℂ := GeneralLinearGroup.scalar (Fin 2) (Units.mk0 _ hr)
  have hc (α : gspPlus (Fin 2)) (hα : multiplier α = multiplier β)
      (τ' : SiegelUpperHalfSpace (Fin 2)) : gspDenomGL α τ' = c * denomGL (toSp α) τ' :=
    Units.ext <| by
      rw [Units.val_mul, coe_gspDenomGL, gspDenom_eq, coe_denomGL, GeneralLinearGroup.coe_scalar,
        scalar_apply, ← smul_eq_diagonal_mul, hα]
      rfl
  have hstar : star c = c :=
    Units.ext <| by
      rw [Units.coe_star, GeneralLinearGroup.coe_scalar, star_eq_conjTranspose, scalar_apply,
        diagonal_conjTranspose]
      congr 1
      funext i
      simp
  have hτ : toSp β' • toSp β • τ = τ := by
    rw [← mul_smul, hδ, one_smul]
  have hj : denomGL (toSp β') (toSp β • τ) = (denomGL (toSp β) τ)⁻¹ := by
    have h₁ : denomGL (toSp β' * toSp β) τ = denomGL (toSp β') (toSp β • τ) * denomGL (toSp β) τ :=
      denomGL_mul (toSp β') (toSp β) τ
    rw [hδ, denomGL_one] at h₁
    exact eq_inv_of_mul_eq_one_left h₁.symm
  have hY : star (denomGL (toSp β) τ) * imGL (toSp β • τ) * denomGL (toSp β) τ = imGL τ :=
    star_denomGL_mul_imGL_smul_mul_denomGL τ (toSp β)
  have hconj :
      conj ((multiplier β : ℂ) ^ slashExponent ρ) = (multiplier β : ℂ) ^ slashExponent ρ := by
    simp
  have hcomm (x : GL (Fin 2) ℂ) : c⁻¹ * x = x * c⁻¹ :=
    Commute.inv_left (GeneralLinearGroup.scalar_commute _ x)
  have hkey : imGL τ * (c * denomGL (toSp β) τ)⁻¹ =
      star (c * (denomGL (toSp β) τ)⁻¹)⁻¹ * imGL (toSp β • τ) := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, star_mul, star_inv, hstar, hcomm, mul_assoc, ← hY,
      mul_assoc (star _ * _), mul_inv_cancel_left, mul_assoc, hcomm]
  have h₅ : b (ρ (star (c * (denomGL (toSp β) τ)⁻¹)⁻¹) (ρ (imGL (toSp β • τ)) (f (toSp β • τ))))
      (g τ) = b (ρ (imGL (toSp β • τ)) (f (toSp β • τ)))
        (ρ (star (star (c * (denomGL (toSp β) τ)⁻¹)⁻¹)) (g τ)) :=
    hadm _ _ (g τ)
  rw [star_star] at h₅
  rw [peterssonIntegrand_apply, peterssonIntegrand_apply]
  simp only [gspSlash, gspSmul]
  rw [hc β rfl τ, hc β' hm (toSp β • τ), hτ, hj, hm, map_smul, map_smul, LinearMap.smul_apply,
    LinearMap.map_smulₛₗ, hconj, ← h₅, ← End.mul_apply, ← End.mul_apply, ← map_mul,
    ← map_mul, hkey]

/-! ### The adjoint of an element of the Hecke monoid -/

/-- The matrix `J⁻¹ Aᵀ J`, as `J⁻¹ = -J`. -/
private def adjointMatrix (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ :=
  -J (Fin 2) ℚ * Aᵀ * J (Fin 2) ℚ

variable (x : heckeMonoid (Fin 2))

private lemma adjointMatrix_mul : adjointMatrix (x : GL (Fin 2 ⊕ Fin 2) ℚ) *
    (x : GL (Fin 2 ⊕ Fin 2) ℚ) = multiplier (submonoidToGSpPlus x) • 1 := by
  have hx : ((x : GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)ᵀ * J (Fin 2) ℚ *
      (x : GL (Fin 2 ⊕ Fin 2) ℚ) = multiplier (submonoidToGSpPlus x) • J (Fin 2) ℚ :=
    transpose_mul_J_mul (submonoidToGSpPlus x)
  rw [adjointMatrix, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (J (Fin 2) ℚ), hx,
    Matrix.mul_smul, Matrix.neg_mul, J_squared, neg_neg]

private lemma adjointMatrix_mul_smul : adjointMatrix (x : GL (Fin 2 ⊕ Fin 2) ℚ) *
    ((multiplier (submonoidToGSpPlus x))⁻¹ • (x : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = 1 := by
  rw [Matrix.mul_smul, adjointMatrix_mul, smul_smul, inv_mul_cancel₀ (multiplier_pos _).ne',
    one_smul]

private lemma mul_adjointMatrix : ((x : GL (Fin 2 ⊕ Fin 2) ℚ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) * adjointMatrix (x : GL (Fin 2 ⊕ Fin 2) ℚ) =
      multiplier (submonoidToGSpPlus x) • 1 := by
  have h : ((multiplier (submonoidToGSpPlus x))⁻¹ • (x : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) * adjointMatrix (x : GL (Fin 2 ⊕ Fin 2) ℚ) = 1 :=
    mul_eq_one_comm.mp (adjointMatrix_mul_smul x)
  rw [Matrix.smul_mul] at h
  rw [← one_smul ℚ (_ * _), ← mul_inv_cancel₀ (multiplier_pos (submonoidToGSpPlus x)).ne',
    mul_smul, h]

private lemma adjointMatrix_mem :
    adjointMatrix (x : GL (Fin 2 ⊕ Fin 2) ℚ) ∈ integralGSpPlus (Fin 2) := by
  refine ⟨⟨_, multiplier_pos (submonoidToGSpPlus x), ?_⟩, ?_⟩
  · have e : (adjointMatrix (x : GL (Fin 2 ⊕ Fin 2) ℚ))ᵀ * J (Fin 2) ℚ *
        adjointMatrix (x : GL (Fin 2 ⊕ Fin 2) ℚ) = J (Fin 2) ℚ *
          (((x : GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) *
            adjointMatrix (x : GL (Fin 2 ⊕ Fin 2) ℚ)) := by
      simp only [adjointMatrix, transpose_mul, transpose_neg, Matrix.neg_mul, Matrix.mul_neg,
        Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (J (Fin 2) ℚ) (J (Fin 2) ℚ), J_squared]
      simp
    rw [e, mul_adjointMatrix, Matrix.mul_smul, Matrix.mul_one]
  · rcases x.2.2 with ⟨A, hA⟩
    refine ⟨-J (Fin 2) ℤ * Aᵀ * J (Fin 2) ℤ, ?_⟩
    have hA' : A.map (Int.castRingHom ℚ) =
        ((x : GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :=
      hA
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul, Matrix.map_neg _ (map_neg _),
      transpose_map, hA', map_J]
    rfl

/-- The **adjoint** `x^* = r(x) x⁻¹ = J⁻¹ xᵀ J` of an element `x` of the semigroup
`S = GSp(4, ℚ)⁺ ∩ M₄(ℤ)`, with multiplier `r(x)`. -/
noncomputable def heckeAdjoint : heckeMonoid (Fin 2) :=
  ⟨⟨adjointMatrix (x : GL (Fin 2 ⊕ Fin 2) ℚ),
    (multiplier (submonoidToGSpPlus x))⁻¹ • (x : GL (Fin 2 ⊕ Fin 2) ℚ),
    adjointMatrix_mul_smul x, mul_eq_one_comm.mp (adjointMatrix_mul_smul x)⟩, adjointMatrix_mem x⟩

lemma coe_heckeAdjoint_mul : (((submonoidToGSpPlus (heckeAdjoint x) * submonoidToGSpPlus x :
    gspPlus (Fin 2))) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) =
      multiplier (submonoidToGSpPlus x) • 1 :=
  adjointMatrix_mul x

lemma toSp_heckeAdjoint_mul :
    toSp (submonoidToGSpPlus (heckeAdjoint x)) * toSp (submonoidToGSpPlus x) = 1 :=
  toSp_mul_eq_one (coe_heckeAdjoint_mul x)

/-! ### The stabilisers and the transversals -/

/-- **Two elements of `Sp(4, ℝ)` acting in the same way on `ℋ₂` agree up to sign.** -/
lemma coe_eq_or_eq_neg_of_forall_smul_eq {γ γ' : symplecticGroup (Fin 2) ℝ}
    (h : ∀ τ : SiegelUpperHalfSpace (Fin 2), γ • τ = γ' • τ) :
    (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) = γ' ∨
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) = -(γ' : Matrix _ _ ℝ) := by
  have h₁ (τ : SiegelUpperHalfSpace (Fin 2)) : (γ'⁻¹ * γ) • τ = τ := by
    rw [mul_smul, h, inv_smul_smul]
  rcases exists_eq_smul_one_of_forall_smul_eq h₁ with ⟨s, hs⟩
  have hsym : ((γ'⁻¹ * γ : symplecticGroup (Fin 2) ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ)ᵀ *
      J (Fin 2) ℝ * ((γ'⁻¹ * γ : symplecticGroup (Fin 2) ℝ) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) = J (Fin 2) ℝ :=
    SymplecticGroup.mem_iff'.mp (γ'⁻¹ * γ).2
  rw [hs] at hsym
  have h₂ : s * s = 1 := by
    simpa [J] using congrFun (congrFun hsym (.inr 0)) (.inl 0)
  have hγ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) = s • (γ' : Matrix _ _ ℝ) := by
    have e : γ = γ' * (γ'⁻¹ * γ) := (mul_inv_cancel_left _ _).symm
    rw [e, Submonoid.coe_mul, hs, Matrix.mul_smul, Matrix.mul_one]
  rcases mul_self_eq_one_iff.mp h₂ with rfl | rfl
  · exact .inl (by simpa using hγ)
  · exact .inr (by simpa using hγ)

variable (g : symplecticGroup (Fin 2) ℤ) {δ δ' : symplecticGroup (Fin 2) ℝ}

/-- The element of the semigroup `S = GSp(4, ℚ)⁺ ∩ M₄(ℤ)` given by an element of `Sp(4, ℤ)`. -/
private def gammaToMonoid : heckeMonoid (Fin 2) :=
  ⟨spToGL (Fin 2) g, heckeGamma_le_heckeMonoid ⟨g, trivial, rfl⟩⟩

private lemma heckeMonoidSlash_gammaToMonoid (f : SiegelUpperHalfSpace (Fin 2) → V) :
    heckeMonoidSlash ρ (gammaToMonoid g) f =
      slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) g) f := by
  rw [heckeMonoidSlash_eq_slash ρ f (γ := SymplecticGroup.map (Int.castRingHom ℚ) g)
    (Units.ext rfl), map_algebraMap_map_intCast]

private lemma slash_eq_of_mem_slashInvariants {F : SiegelUpperHalfSpace (Fin 2) → V}
    (hF : F ∈ slashInvariants ρ) : slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) g) F = F := by
  rw [← heckeMonoidSlash_gammaToMonoid]
  exact hF _ ⟨g, trivial, rfl⟩

variable (δ) in
/-- The subgroup of the transformations `g` of `ℋ₂` induced by `Sp(4, ℤ)` with `δ g δ⁻¹` also
induced by `Sp(4, ℤ)`. -/
private noncomputable def conjStab : Subgroup (transformationGroup (integral (Fin 2))) :=
  ((transformationGroup (integral (Fin 2))).comap
    (MulAut.conj (MulAction.toPerm δ)).toMonoidHom).subgroupOf _

private lemma mem_conjStab_iff_mem {h : transformationGroup (integral (Fin 2))} : h ∈ conjStab δ ↔
    MulAction.toPerm δ * h.1 * (MulAction.toPerm δ)⁻¹ ∈ transformationGroup (integral (Fin 2)) :=
  Iff.rfl

private lemma coe_eq_smul_of_toSp_eq {A B : gspPlus (Fin 2)} (hm : multiplier A = multiplier B)
    {ε : ℚ}
    (h : (toSp A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) = (ε : ℝ) • (toSp B : Matrix _ _ ℝ)) :
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = ε • (B : Matrix _ _ ℚ) := by
  have hr : (√(multiplier A : ℝ))⁻¹ ≠ 0 :=
    inv_ne_zero <| Real.sqrt_ne_zero'.mpr <| Rat.cast_pos.mpr <| multiplier_pos A
  refine Matrix.map_injective (algebraMap ℚ ℝ).injective ?_
  refine smul_right_injective _ hr ?_
  have h₁ : (toSp A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) = (√(multiplier A : ℝ))⁻¹ •
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ).map (algebraMap ℚ ℝ) :=
    rfl
  have h₂ : (toSp B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) = (√(multiplier A : ℝ))⁻¹ •
      (B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ).map (algebraMap ℚ ℝ) := by
    rw [hm]
    rfl
  dsimp only
  rw [← h₁, h, h₂, smul_comm]
  congr 1
  ext a c
  simp

private lemma toSp_mul_ofSp (y : gspPlus (Fin 2)) :
    toSp (y * ofSp (SymplecticGroup.map (Int.castRingHom ℚ) g)) =
      toSp y * SymplecticGroup.map (Int.castRingHom ℝ) g := by
  rw [toSp_mul, toSp_ofSp, map_algebraMap_map_intCast]

private lemma toSp_ofSp_mul (y : gspPlus (Fin 2)) :
    toSp (ofSp (SymplecticGroup.map (Int.castRingHom ℚ) g) * y) =
      SymplecticGroup.map (Int.castRingHom ℝ) g * toSp y := by
  rw [toSp_mul, toSp_ofSp, map_algebraMap_map_intCast]

private lemma mem_conjStab_iff : integralTransformation g ∈ conjStab (toSp (submonoidToGSpPlus x)) ↔
    (x : GL (Fin 2 ⊕ Fin 2) ℚ) * spToGL (Fin 2) g * (x : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ ∈
      heckeGamma (Fin 2) := by
  generalize hx : submonoidToGSpPlus x = y
  have hy : (y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = (x : GL (Fin 2 ⊕ Fin 2) ℚ) := by
    rw [← hx]
    rfl
  rw [mem_conjStab_iff_mem]
  constructor
  · intro h
    rcases surjective_integralTransformation (⟨_, h⟩ : transformationGroup (integral (Fin 2))) with
      ⟨g₁, hg₁⟩
    have h₁ (τ : SiegelUpperHalfSpace (Fin 2)) :
        toSp (y * ofSp (SymplecticGroup.map (Int.castRingHom ℚ) g)) • τ =
          toSp (ofSp (SymplecticGroup.map (Int.castRingHom ℚ) g₁) * y) • τ := by
      have h₂ : SymplecticGroup.map (Int.castRingHom ℝ) g₁ • toSp y • τ = toSp y •
          SymplecticGroup.map (Int.castRingHom ℝ) g • (MulAction.toPerm (toSp y))⁻¹ (toSp y • τ) :=
        congrArg (fun p : transformationGroup (integral (Fin 2)) ↦ p.1 (toSp y • τ)) hg₁
      have e : (MulAction.toPerm (toSp y))⁻¹ (toSp y • τ) = τ :=
        (MulAction.toPerm (toSp y)).symm_apply_apply τ
      rw [e] at h₂
      rw [toSp_mul_ofSp, toSp_ofSp_mul, mul_smul, mul_smul]
      exact h₂.symm
    have hmA : multiplier (y * ofSp (SymplecticGroup.map (Int.castRingHom ℚ) g)) =
        multiplier (ofSp (SymplecticGroup.map (Int.castRingHom ℚ) g₁) * y) := by
      rw [multiplier_mul, multiplier_mul, multiplier_ofSp, multiplier_ofSp, mul_one, one_mul]
    rcases coe_eq_or_eq_neg_of_forall_smul_eq h₁ with h₄ | h₄
    · have h₅ : ((y * ofSp (SymplecticGroup.map (Int.castRingHom ℚ) g) : gspPlus (Fin 2)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = (1 : ℚ) •
            ((ofSp (SymplecticGroup.map (Int.castRingHom ℚ) g₁) * y : gspPlus (Fin 2)) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :=
        coe_eq_smul_of_toSp_eq hmA (by simpa using h₄)
      refine ⟨g₁, trivial, ?_⟩
      rw [eq_mul_inv_iff_mul_eq]
      refine Units.ext ?_
      rw [one_smul, Submonoid.coe_mul, Submonoid.coe_mul, hy] at h₅
      exact h₅.symm
    · have h₅ : ((y * ofSp (SymplecticGroup.map (Int.castRingHom ℚ) g) : gspPlus (Fin 2)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = (-1 : ℚ) •
            ((ofSp (SymplecticGroup.map (Int.castRingHom ℚ) g₁) * y : gspPlus (Fin 2)) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :=
        coe_eq_smul_of_toSp_eq hmA (by simpa using h₄)
      refine ⟨negOneSp * g₁, trivial, ?_⟩
      rw [eq_mul_inv_iff_mul_eq]
      refine Units.ext ?_
      rw [neg_one_smul, Submonoid.coe_mul, Submonoid.coe_mul, hy] at h₅
      have e : ((spToGL (Fin 2) (negOneSp * g₁) : GL (Fin 2 ⊕ Fin 2) ℚ) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) =
            -((ofSp (SymplecticGroup.map (Int.castRingHom ℚ) g₁) : gspPlus (Fin 2)) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :=
        (congrArg (Int.castRingHom ℚ).mapMatrix
          (neg_one_mul (g₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ))).trans (map_neg _ _)
      rw [Units.val_mul, Units.val_mul, e, Matrix.neg_mul]
      exact h₅.symm
  · rintro ⟨g₁, -, hg₁⟩
    have h₃ : y * ofSp (SymplecticGroup.map (Int.castRingHom ℚ) g) =
        ofSp (SymplecticGroup.map (Int.castRingHom ℚ) g₁) * y := by
      refine Subtype.ext ?_
      rw [eq_mul_inv_iff_mul_eq] at hg₁
      rw [Submonoid.coe_mul, Submonoid.coe_mul, hy]
      exact (congrArg Units.val hg₁).symm
    have h₄ : toSp y * SymplecticGroup.map (Int.castRingHom ℝ) g =
        SymplecticGroup.map (Int.castRingHom ℝ) g₁ * toSp y := by
      rw [← toSp_mul_ofSp, ← toSp_ofSp_mul, h₃]
    have e : MulAction.toPerm (toSp y) * ((integralTransformation g :
        transformationGroup (integral (Fin 2))) : Equiv.Perm (SiegelUpperHalfSpace (Fin 2))) *
          (MulAction.toPerm (toSp y))⁻¹ = ((integralTransformation g₁ :
            transformationGroup (integral (Fin 2))) : Equiv.Perm (SiegelUpperHalfSpace (Fin 2))) :=
      Perm.ext fun τ : SiegelUpperHalfSpace (Fin 2) ↦ by
        have e₂ : (toSp y * SymplecticGroup.map (Int.castRingHom ℝ) g) • (toSp y)⁻¹ • τ =
            (SymplecticGroup.map (Int.castRingHom ℝ) g₁ * toSp y) • (toSp y)⁻¹ • τ := by
          rw [h₄]
        simp only [mul_smul, smul_inv_smul] at e₂
        exact e₂
    rw [e]
    exact (integralTransformation g₁).2

variable {x g} in
private lemma slash_heckeMonoidSlash_eq {F : SiegelUpperHalfSpace (Fin 2) → V}
    (hF : F ∈ slashInvariants ρ)
    (hg : integralTransformation g ∈ conjStab (toSp (submonoidToGSpPlus x))) :
    slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) g) (heckeMonoidSlash ρ x F) =
      heckeMonoidSlash ρ x F := by
  rcases (mem_conjStab_iff x g).mp hg with ⟨g₁, -, hg₁⟩
  rw [eq_mul_inv_iff_mul_eq] at hg₁
  have h : x * gammaToMonoid g = gammaToMonoid g₁ * x :=
    Subtype.ext hg₁.symm
  rw [← heckeMonoidSlash_gammaToMonoid, ← heckeMonoidSlash_mul, h, heckeMonoidSlash_mul,
    heckeMonoidSlash_gammaToMonoid, slash_eq_of_mem_slashInvariants g₁ hF]

/-- The isomorphism from `Sp(4, ℤ)` to its image in `GL(4, ℚ)`. -/
private noncomputable def heckeGammaEquiv : symplecticGroup (Fin 2) ℤ ≃* heckeGamma (Fin 2) :=
  Subgroup.topEquiv.symm.trans (Subgroup.equivMapOfInjective _ _ (spToGL_injective _))

private lemma coe_heckeGammaEquiv :
    ((heckeGammaEquiv g : heckeGamma (Fin 2)) : GL (Fin 2 ⊕ Fin 2) ℚ) = spToGL (Fin 2) g :=
  rfl

private lemma bijective_mk_out {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (K : Subgroup A) (H : Subgroup B) (hK : ∀ a, a ∈ K ↔ f a ∈ H) :
    Function.Bijective fun v : A ⧸ K ↦ (QuotientGroup.mk (f v.out) : B ⧸ H) := by
  refine ⟨fun v w hvw ↦ ?_, fun q ↦ ?_⟩
  · have h₁ : (f v.out)⁻¹ * f w.out ∈ H := QuotientGroup.eq.mp hvw
    rw [← map_inv, ← map_mul, ← hK] at h₁
    rw [← QuotientGroup.out_eq' v, ← QuotientGroup.out_eq' w]
    exact QuotientGroup.eq.mpr h₁
  · rcases QuotientGroup.mk_surjective q with ⟨b, rfl⟩
    rcases hf b with ⟨a, rfl⟩
    refine ⟨QuotientGroup.mk a, QuotientGroup.eq.mpr ?_⟩
    rw [← map_inv, ← map_mul, ← hK]
    exact QuotientGroup.eq.mp (QuotientGroup.out_eq' _)

variable (v : DecompQuotient (heckeGamma (Fin 2)) (heckeGamma (Fin 2)) (x : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹)

/-- The element of `Sp(4, ℤ)` representing a class in the quotient indexing the right cosets
`Sp(4, ℤ) x τ` of the double coset of `x`. -/
private noncomputable def gOut : symplecticGroup (Fin 2) ℤ :=
  heckeGammaEquiv.symm v.out

private lemma spToGL_gOut : spToGL (Fin 2) (gOut x v) = (v.out : GL (Fin 2 ⊕ Fin 2) ℚ) := by
  rw [← coe_heckeGammaEquiv, gOut, MulEquiv.apply_symm_apply]

private lemma bijective_mk_gOut : Function.Bijective fun v : DecompQuotient (heckeGamma (Fin 2))
    (heckeGamma (Fin 2)) (x : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ ↦
      (QuotientGroup.mk (integralTransformation (gOut x v)) :
        transformationGroup (integral (Fin 2)) ⧸ conjStab (toSp (submonoidToGSpPlus x))) := by
  refine bijective_mk_out (integralTransformation.comp heckeGammaEquiv.symm.toMonoidHom)
    (surjective_integralTransformation.comp heckeGammaEquiv.symm.surjective) _ _ fun a ↦ ?_
  rcases heckeGammaEquiv.surjective a with ⟨g, rfl⟩
  have e : (integralTransformation.comp heckeGammaEquiv.symm.toMonoidHom) (heckeGammaEquiv g) =
      integralTransformation g := by
    simp
  rw [e, mem_conjStab_iff, Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ← ConjAct.toConjAct_inv, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, inv_inv,
    coe_heckeGammaEquiv]

private lemma toPerm_eq_inv (h : δ' * δ = 1) :
    (MulAction.toPerm δ' : Equiv.Perm (SiegelUpperHalfSpace (Fin 2))) = (MulAction.toPerm δ)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| Perm.ext fun τ : SiegelUpperHalfSpace (Fin 2) ↦ by
    have h₁ : δ' • δ • τ = τ := by
      rw [← mul_smul, h, one_smul]
    exact h₁

/-- The isomorphism between the stabilisers of `δ` and of its inverse, by conjugation. -/
private noncomputable def conjStabEquiv (h : δ' * δ = 1) : conjStab δ ≃ conjStab δ' where
  toFun g := ⟨⟨_, g.2⟩, mem_conjStab_iff_mem.mpr (by simp [toPerm_eq_inv h, mul_assoc])⟩
  invFun g := ⟨⟨_, g.2⟩, mem_conjStab_iff_mem.mpr (by simp [toPerm_eq_inv h, mul_assoc])⟩
  left_inv g := Subtype.ext <| Subtype.ext <| by simp [toPerm_eq_inv h, mul_assoc]
  right_inv g := Subtype.ext <| Subtype.ext <| by simp [toPerm_eq_inv h, mul_assoc]

private lemma smul_smul_eq_conjStabEquiv (h : δ' * δ = 1) (u : conjStab δ)
    (τ : SiegelUpperHalfSpace (Fin 2)) : δ • u • τ = conjStabEquiv h u • δ • τ := by
  have e : conjStabEquiv h u • δ • τ = (MulAction.toPerm δ * u.1.1 * (MulAction.toPerm δ)⁻¹ :
      Equiv.Perm (SiegelUpperHalfSpace (Fin 2))) (δ • τ) :=
    rfl
  have e₂ : (MulAction.toPerm δ : Equiv.Perm (SiegelUpperHalfSpace (Fin 2)))⁻¹ (δ • τ) = τ :=
    (MulAction.toPerm δ).symm_apply_apply τ
  rw [e, Perm.coe_mul, Perm.coe_mul, Function.comp_apply, Function.comp_apply, e₂]
  rfl

/-! ### The adjoint formula -/

section Formula

attribute [local instance] Fintype.ofFinite

/-- The right coset representative `x τ⁻¹` of the double coset of `x`. -/
private noncomputable def heckeTerm : heckeMonoid (Fin 2) :=
  x * gammaToMonoid (gOut x v)⁻¹

private lemma coe_heckeTerm :
    (heckeTerm x v : GL (Fin 2 ⊕ Fin 2) ℚ) = x * (v.out : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ := by
  have h : ((gammaToMonoid (gOut x v)⁻¹ : heckeMonoid (Fin 2)) : GL (Fin 2 ⊕ Fin 2) ℚ) =
      (v.out : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ := by
    rw [← spToGL_gOut, ← map_inv]
    rfl
  rw [heckeTerm, Submonoid.coe_mul, h]

private lemma heckeRep_eq_heckeTerm
    (D : HeckeCoset (heckeMonoid (Fin 2)) (heckeGamma (Fin 2)) (heckeGamma (Fin 2)))
    (w : DecompQuotient (heckeGamma (Fin 2)) (heckeGamma (Fin 2))
      (D.out : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹) : heckeRep D w = heckeTerm D.out w :=
  Subtype.ext <| (rightCosetRep_def D w).trans (coe_heckeTerm D.out w).symm

private lemma coe_heckeOperator_mk (F : slashInvariants ρ) :
    (heckeOperator ρ (HeckeCoset.mk _ _ x) F : SiegelUpperHalfSpace (Fin 2) → V) =
      ∑ v, heckeMonoidSlash ρ (heckeTerm x v) F := by
  refine heckeOperator_eq_sum ρ _ (heckeTerm x) ?_ ?_ F
  · rw [← HeckeCoset.rep_def, HeckeCoset.doubleCoset_rep_mk]
    simp only [coe_heckeTerm]
    exact doubleCoset_eq_iUnion_rightCosets _ _ _
  · simp only [coe_heckeTerm]
    exact op_mul_out_inv_smul_injective _ _ _

private lemma peterssonIntegrand_sum_left {ι : Type*} (t : Finset ι)
    (f : ι → SiegelUpperHalfSpace (Fin 2) → V) (u : SiegelUpperHalfSpace (Fin 2) → V)
    (τ : SiegelUpperHalfSpace (Fin 2)) :
    peterssonIntegrand ρ b (∑ i ∈ t, f i) u τ = ∑ i ∈ t, peterssonIntegrand ρ b (f i) u τ := by
  simp [peterssonIntegrand_apply]

private lemma peterssonIntegrand_sum_right {ι : Type*} (t : Finset ι)
    (f : SiegelUpperHalfSpace (Fin 2) → V) (u : ι → SiegelUpperHalfSpace (Fin 2) → V)
    (τ : SiegelUpperHalfSpace (Fin 2)) :
    peterssonIntegrand ρ b f (∑ i ∈ t, u i) τ = ∑ i ∈ t, peterssonIntegrand ρ b f (u i) τ := by
  simp [peterssonIntegrand_apply]

/-- The inverse of the transformation of `gOut x v`, the transversal of the stabiliser of `x`. -/
private noncomputable def heckeTransversal : transformationGroup (integral (Fin 2)) :=
  (integralTransformation (gOut x v))⁻¹

private lemma bijective_heckeTransversal :
    Function.Bijective fun w ↦ (QuotientGroup.mk (heckeTransversal x w)⁻¹ :
      transformationGroup (integral (Fin 2)) ⧸ conjStab (toSp (submonoidToGSpPlus x))) := by
  simpa only [heckeTransversal, inv_inv] using bijective_mk_gOut x

private lemma heckeTransversal_smul (τ : SiegelUpperHalfSpace (Fin 2)) :
    heckeTransversal x v • τ = SymplecticGroup.map (Int.castRingHom ℝ) (gOut x v)⁻¹ • τ := by
  rw [heckeTransversal, ← map_inv, integralTransformation_smul]

variable {F G : slashInvariants ρ}

private lemma peterssonIntegrand_heckeTerm_right (hadm : IsAdmissibleForm ρ b)
    (τ : SiegelUpperHalfSpace (Fin 2)) :
    peterssonIntegrand ρ b F (heckeMonoidSlash ρ (heckeTerm x v) G) τ =
      peterssonIntegrand ρ b F (heckeMonoidSlash ρ x G) (heckeTransversal x v • τ) := by
  have h : peterssonIntegrand ρ b (slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) (gOut x v)⁻¹) F)
      (slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) (gOut x v)⁻¹) (heckeMonoidSlash ρ x G)) τ =
      peterssonIntegrand ρ b F (heckeMonoidSlash ρ x G)
        (SymplecticGroup.map (Int.castRingHom ℝ) (gOut x v)⁻¹ • τ) :=
    peterssonIntegrand_slash hadm F (heckeMonoidSlash ρ x G) _ τ
  rw [slash_eq_of_mem_slashInvariants _ F.2] at h
  rw [heckeTerm, heckeMonoidSlash_mul, heckeMonoidSlash_gammaToMonoid, h, heckeTransversal_smul]

private lemma peterssonIntegrand_heckeTerm_left (hadm : IsAdmissibleForm ρ b)
    (τ : SiegelUpperHalfSpace (Fin 2)) :
    peterssonIntegrand ρ b (heckeMonoidSlash ρ (heckeTerm x v) F) G τ =
      peterssonIntegrand ρ b F (heckeMonoidSlash ρ (heckeAdjoint x) G)
        (toSp (submonoidToGSpPlus x) • heckeTransversal x v • τ) := by
  have h : peterssonIntegrand ρ b
      (slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) (gOut x v)⁻¹) (heckeMonoidSlash ρ x F))
        (slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) (gOut x v)⁻¹) G) τ =
          peterssonIntegrand ρ b (heckeMonoidSlash ρ x F) G
            (SymplecticGroup.map (Int.castRingHom ℝ) (gOut x v)⁻¹ • τ) :=
    peterssonIntegrand_slash hadm (heckeMonoidSlash ρ x F) G _ τ
  rw [slash_eq_of_mem_slashInvariants _ G.2] at h
  rw [heckeTerm, heckeMonoidSlash_mul, heckeMonoidSlash_gammaToMonoid, h, heckeTransversal_smul]
  exact peterssonIntegrand_gspSlash hadm (coe_heckeAdjoint_mul x) F G _

private lemma peterssonIntegrand_heckeMonoidSlash_smul (hadm : IsAdmissibleForm ρ b)
    (h : conjStab (toSp (submonoidToGSpPlus x))) (τ : SiegelUpperHalfSpace (Fin 2)) :
    peterssonIntegrand ρ b F (heckeMonoidSlash ρ x G) (h • τ) =
      peterssonIntegrand ρ b F (heckeMonoidSlash ρ x G) τ := by
  rcases h with ⟨h, hh⟩
  rcases surjective_integralTransformation h with ⟨u, rfl⟩
  have e : peterssonIntegrand ρ b (slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) u) F)
      (slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) u) (heckeMonoidSlash ρ x G)) τ =
        peterssonIntegrand ρ b F (heckeMonoidSlash ρ x G)
          (SymplecticGroup.map (Int.castRingHom ℝ) u • τ) :=
    peterssonIntegrand_slash hadm F (heckeMonoidSlash ρ x G) _ τ
  rw [slash_eq_of_mem_slashInvariants _ F.2, slash_heckeMonoidSlash_eq G.2 hh] at e
  exact e.symm

variable [FiniteDimensional ℂ V]

private lemma lintegral_siegelSet_peterssonIntegrand_lt_top (hb : IsModerateForm ρ b)
    (hF : (F : SiegelUpperHalfSpace (Fin 2) → V) ∈ modularForms ρ (integral (Fin 2)) 1)
    (hG : (G : SiegelUpperHalfSpace (Fin 2) → V) ∈ cuspForms ρ (integral (Fin 2)) 1) :
    ∫⁻ τ in siegelSet, ‖peterssonIntegrand ρ b F (heckeMonoidSlash ρ x G) τ‖ₑ
      ∂invariantMeasure (Fin 2) < ∞ := by
  rcases exists_norm_dual_heckeMonoidSlash_le hG x with ⟨ε, hε, h⟩
  rcases exists_norm_peterssonIntegrand_le (f := F) (g := heckeMonoidSlash ρ x G)
    (A := fun τ ↦ rexp (-ε * ((τ.val 0 0).im + (τ.val 1 1).im))) hb (fun φ ψ ↦ by
      rcases exists_norm_dual_le_of_mem_modularForms hF φ with ⟨C₁, hC₁, h₁⟩
      rcases h ψ with ⟨C₂, hC₂, h₂⟩
      refine ⟨C₁ * C₂, fun τ hτ ↦ ?_⟩
      rw [mul_assoc]
      exact mul_le_mul (h₁ τ hτ) (h₂ τ hτ) (norm_nonneg _) hC₁) with ⟨C, N, hC⟩
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_siegelSet fun τ hτ ↦ ?_)
    (lintegral_siegelSet_mul_pow_lt_top C N hε)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hC τ hτ)

private lemma integrableOn_peterssonIntegrand_heckeMonoidSlash
    (hρ : ∀ α f, IsHolomorphic f → IsHolomorphic (gspSlash ρ α f)) (hb : IsModerateForm ρ b)
    (hadm : IsAdmissibleForm ρ b)
    (hF : (F : SiegelUpperHalfSpace (Fin 2) → V) ∈ modularForms ρ (integral (Fin 2)) 1)
    (hG : (G : SiegelUpperHalfSpace (Fin 2) → V) ∈ cuspForms ρ (integral (Fin 2)) 1)
    {t : Set (SiegelUpperHalfSpace (Fin 2))} (ht : IsFundamentalDomain
      (conjStab (toSp (submonoidToGSpPlus x))) t (invariantMeasure (Fin 2))) :
    IntegrableOn (peterssonIntegrand ρ b F (heckeMonoidSlash ρ x G)) t
      (invariantMeasure (Fin 2)) := by
  have hc : Continuous (peterssonIntegrand ρ b F (heckeMonoidSlash ρ x G)) :=
    continuous_peterssonIntegrand hb hF.1 (hρ _ _ hG.1.1)
  refine ht.integrableOn_of_setLIntegral_tsum_lt_top (t := siegelSet)
    (bijective_heckeTransversal x).surjective hc.aestronglyMeasurable (fun v ↦ ?_)
    (peterssonIntegrand_heckeMonoidSlash_smul x hadm)
    (.of_forall exists_smul_mem_siegelSet_transformationGroup) ?_
  · exact (hc.comp (continuous_const_smul _)).enorm.aemeasurable
  · have hm (a : heckeMonoid (Fin 2)) : AEMeasurable
        (fun τ ↦ ‖peterssonIntegrand ρ b F (heckeMonoidSlash ρ a G) τ‖ₑ)
          ((invariantMeasure (Fin 2)).restrict siegelSet) :=
      (continuous_peterssonIntegrand hb hF.1 (hρ _ _ hG.1.1)).enorm.aemeasurable
    simp only [tsum_fintype, ← peterssonIntegrand_heckeTerm_right x _ hadm]
    rw [lintegral_finsetSum' _ fun v _ ↦ hm (heckeTerm x v)]
    exact ENNReal.sum_lt_top.mpr fun v _ ↦ lintegral_siegelSet_peterssonIntegrand_lt_top _ hb hF hG

/-- The double coset of the adjoint `x^* = r(x) x⁻¹` of a representative `x` of a double coset
`D`. It does not depend on the representative (`SiegelUpperHalfSpace.heckeAdjointCoset_mk`). -/
noncomputable def heckeAdjointCoset
    (D : HeckeCoset (heckeMonoid (Fin 2)) (heckeGamma (Fin 2)) (heckeGamma (Fin 2))) :
    HeckeCoset (heckeMonoid (Fin 2)) (heckeGamma (Fin 2)) (heckeGamma (Fin 2)) :=
  HeckeCoset.mk _ _ (heckeAdjoint D.out)

private lemma adjointMatrix_mul_adjointMatrix (A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :
    adjointMatrix (A * B) = adjointMatrix B * adjointMatrix A := by
  simp only [adjointMatrix, transpose_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (J (Fin 2) ℚ) (J (Fin 2) ℚ), J_squared]
  simp

private lemma heckeAdjoint_mul (y : heckeMonoid (Fin 2)) :
    heckeAdjoint (x * y) = heckeAdjoint y * heckeAdjoint x :=
  Subtype.ext <| Units.ext <| adjointMatrix_mul_adjointMatrix _ _

private lemma heckeAdjoint_gammaToMonoid : heckeAdjoint (gammaToMonoid g) = gammaToMonoid g⁻¹ := by
  have hm : multiplier (submonoidToGSpPlus (gammaToMonoid g)) = 1 :=
    multiplier_eq _ <| by
      rw [one_smul, ← SymplecticGroup.mem_iff']
      exact (SymplecticGroup.map (Int.castRingHom ℚ) g).2
  have h : (heckeAdjoint (gammaToMonoid g) : GL (Fin 2 ⊕ Fin 2) ℚ) * spToGL (Fin 2) g = 1 :=
    Units.ext <| (adjointMatrix_mul (gammaToMonoid g)).trans <| by
      rw [hm, one_smul]
      rfl
  exact Subtype.ext <| (eq_inv_of_mul_eq_one_left h).trans (map_inv (spToGL (Fin 2)) g).symm

/-- **The double coset of the adjoint does not depend on the representative**:
`(γ₁ x γ₂)^* = γ₂⁻¹ x^* γ₁⁻¹` for `γ₁, γ₂ ∈ Sp(4, ℤ)`. -/
lemma heckeAdjointCoset_mk :
    heckeAdjointCoset (HeckeCoset.mk _ _ x) = HeckeCoset.mk _ _ (heckeAdjoint x) := by
  rcases DoubleCoset.rel_iff.mp (Quotient.mk_out (s := HeckeCoset.setoid (heckeMonoid (Fin 2))
    (heckeGamma (Fin 2)) (heckeGamma (Fin 2))) x) with ⟨_, ⟨a, -, rfl⟩, _, ⟨b, -, rfl⟩, hx⟩
  refine Quotient.sound <| DoubleCoset.rel_iff.mpr
    ⟨_, ⟨b⁻¹, trivial, rfl⟩, _, ⟨a⁻¹, trivial, rfl⟩, ?_⟩
  have h : x = gammaToMonoid a * (HeckeCoset.mk (heckeGamma (Fin 2)) (heckeGamma (Fin 2)) x).out *
      gammaToMonoid b :=
    Subtype.ext hx
  conv_lhs => rw [h, heckeAdjoint_mul, heckeAdjoint_mul, heckeAdjoint_gammaToMonoid,
    heckeAdjoint_gammaToMonoid]
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← mul_assoc]
  rfl

/-- **The double coset of a symmetric element is its own adjoint**: `x^* = J⁻¹ x J` lies in the
double coset of `x`, as `J ∈ Sp(4, ℤ)`. -/
lemma heckeAdjointCoset_mk_of_transpose_eq
    (hx : ((x : GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)ᵀ =
      (x : GL (Fin 2 ⊕ Fin 2) ℚ)) :
    heckeAdjointCoset (HeckeCoset.mk _ _ x) = HeckeCoset.mk _ _ x := by
  rw [heckeAdjointCoset_mk]
  refine Quotient.sound (DoubleCoset.rel_iff.mpr ⟨_, ⟨symJ (Fin 2) ℤ, trivial, rfl⟩, _,
    ⟨(symJ (Fin 2) ℤ)⁻¹, trivial, rfl⟩, ?_⟩)
  have hJ : ((spToGL (Fin 2) (symJ (Fin 2) ℤ) : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = J (Fin 2) ℚ :=
    map_J _ (Int.castRingHom ℚ)
  have e : (((heckeAdjoint x : heckeMonoid (Fin 2)) : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = adjointMatrix (x : GL (Fin 2 ⊕ Fin 2) ℚ) :=
    rfl
  rw [map_inv, eq_mul_inv_iff_mul_eq]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hJ, e, adjointMatrix, hx, Matrix.neg_mul, Matrix.neg_mul,
    Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, J_squared]
  simp

/-- **The Hecke operator `T(p)` is its own adjoint**, its double coset having a diagonal
representative. -/
lemma heckeAdjointCoset_heckeT (p : ℕ) (hp : p.Prime) :
    heckeAdjointCoset (heckeT (Fin 2) p hp) = heckeT (Fin 2) p hp := by
  refine heckeAdjointCoset_mk_of_transpose_eq _ ?_
  exact diagonal_transpose _

/-- **The Hecke operator `T_i(p²)` is its own adjoint**, its double coset having a diagonal
representative. -/
lemma heckeAdjointCoset_heckeTi (i p : ℕ) (hp : p.Prime) :
    heckeAdjointCoset (heckeTi i p hp) = heckeTi i p hp := by
  refine heckeAdjointCoset_mk_of_transpose_eq _ ?_
  exact diagonal_transpose _

/-- **The adjoint of a Hecke operator for the Petersson product on `Sp(4, ℤ)`**: for a moderate
admissible form, a modular form `F` and a cusp form `G`, and a fundamental domain `s` of `Sp(4, ℤ)`,
`∫_s [T_D F, G] = ∫_s [F, T_{D^*} G]`, with `D^* = Γ r(x) x⁻¹ Γ` for `D = Γ x Γ`. -/
lemma setIntegral_peterssonIntegrand_heckeOperator
    (hρ : ∀ α f, IsHolomorphic f → IsHolomorphic (gspSlash ρ α f)) (hb : IsModerateForm ρ b)
    (hadm : IsAdmissibleForm ρ b)
    (D : HeckeCoset (heckeMonoid (Fin 2)) (heckeGamma (Fin 2)) (heckeGamma (Fin 2)))
    (hF : (F : SiegelUpperHalfSpace (Fin 2) → V) ∈ modularForms ρ (integral (Fin 2)) 1)
    (hG : (G : SiegelUpperHalfSpace (Fin 2) → V) ∈ cuspForms ρ (integral (Fin 2)) 1)
    {s : Set (SiegelUpperHalfSpace (Fin 2))} (hs : IsFundamentalDomain
      (transformationGroup (integral (Fin 2))) s (invariantMeasure (Fin 2))) :
    ∫ τ in s, peterssonIntegrand ρ b (heckeOperator ρ D F) G τ ∂invariantMeasure (Fin 2) =
      ∫ τ in s, peterssonIntegrand ρ b F (heckeOperator ρ (heckeAdjointCoset D) G) τ
        ∂invariantMeasure (Fin 2) := by
  have hL (τ : SiegelUpperHalfSpace (Fin 2)) : peterssonIntegrand ρ b (heckeOperator ρ D F) G τ =
      ∑' v, peterssonIntegrand ρ b F (heckeMonoidSlash ρ (heckeAdjoint D.out) G)
        (toSp (submonoidToGSpPlus D.out) • heckeTransversal D.out v • τ) := by
    rw [tsum_fintype, coe_heckeOperator, peterssonIntegrand_sum_left]
    simp only [heckeRep_eq_heckeTerm, peterssonIntegrand_heckeTerm_left _ _ hadm]
  have hR (τ : SiegelUpperHalfSpace (Fin 2)) :
      peterssonIntegrand ρ b F (heckeOperator ρ (heckeAdjointCoset D) G) τ =
        ∑' w, peterssonIntegrand ρ b F (heckeMonoidSlash ρ (heckeAdjoint D.out) G)
          (heckeTransversal (heckeAdjoint D.out) w • τ) := by
    rw [tsum_fintype, heckeAdjointCoset, coe_heckeOperator_mk, peterssonIntegrand_sum_right]
    simp only [peterssonIntegrand_heckeTerm_right _ _ hadm]
  simp only [hL, hR]
  have hF₂ : IsFundamentalDomain (conjStab (toSp (submonoidToGSpPlus (heckeAdjoint D.out))))
      (⋃ w, heckeTransversal (heckeAdjoint D.out) w • s) (invariantMeasure (Fin 2)) :=
    hs.iUnion_smul_of_transversal (fun w ↦ hs.nullMeasurableSet_smul _)
      (bijective_heckeTransversal (heckeAdjoint D.out))
  exact hs.setIntegral_tsum_smul_smul_eq hF₂ (bijective_heckeTransversal D.out)
    (bijective_heckeTransversal (heckeAdjoint D.out))
    (conjStabEquiv (toSp_heckeAdjoint_mul D.out))
    (smul_smul_eq_conjStabEquiv (toSp_heckeAdjoint_mul D.out))
    (peterssonIntegrand_heckeMonoidSlash_smul _ hadm)
    (integrableOn_peterssonIntegrand_heckeMonoidSlash _ hρ hb hadm hF hG hF₂)

end Formula

/-! ### Weight `ρ_{k,j}` -/

variable {k : ℤ} {j : ℕ} {c : Sym[ℂ]^j (Fin 2 → ℂ) →ₗ[ℂ] Sym[ℂ]^j (Fin 2 → ℂ) →ₗ⋆[ℂ] ℂ}

/-- **The adjoint of a Hecke operator on `M_{j,k}(Γ₂)`** (LMFDB `mf.siegel.subspace.degree.two`):
`⟨T_D F, G⟩ = ⟨F, T_{D^*} G⟩` for a modular form `F`, a cusp form `G` and an admissible form `c`. -/
lemma peterssonProduct_heckeOperator (hadm : IsAdmissibleForm (rhoKJ k j) c)
    (D : HeckeCoset (heckeMonoid (Fin 2)) (heckeGamma (Fin 2)) (heckeGamma (Fin 2)))
    {F G : slashInvariants (rhoKJ k j)}
    (hF : (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      modularFormsKJ k j (integral (Fin 2)))
    (hG : (G : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      cuspFormsKJ k j (integral (Fin 2))) :
    peterssonProduct (integral (Fin 2)) (rhoKJ k j) c (heckeOperator (rhoKJ k j) D F) G =
      peterssonProduct (integral (Fin 2)) (rhoKJ k j) c F
        (heckeOperator (rhoKJ k j) (heckeAdjointCoset D) G) :=
  setIntegral_peterssonIntegrand_heckeOperator (fun α _ hf ↦ isHolomorphic_gspSlash_rhoKJ k j α hf)
    (isModerateForm_rhoKJ k c) hadm D hF hG
    (isFundamentalDomain_fundamentalDomain (isArithmetic_integral (Fin 2)))

/-- **The Hecke operator `T(p)` is self-adjoint on `M_{j,k}(Γ₂)`**:
`⟨T(p) F, G⟩ = ⟨F, T(p) G⟩` for a modular form `F`, a cusp form `G` and an admissible form `c`. -/
lemma peterssonProduct_heckeT (hadm : IsAdmissibleForm (rhoKJ k j) c) (p : ℕ) (hp : p.Prime)
    {F G : slashInvariants (rhoKJ k j)}
    (hF : (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      modularFormsKJ k j (integral (Fin 2)))
    (hG : (G : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      cuspFormsKJ k j (integral (Fin 2))) : peterssonProduct (integral (Fin 2)) (rhoKJ k j) c
        (heckeOperator (rhoKJ k j) (heckeT _ p hp) F) G =
      peterssonProduct (integral (Fin 2)) (rhoKJ k j) c F
        (heckeOperator (rhoKJ k j) (heckeT _ p hp) G) := by
  rw [peterssonProduct_heckeOperator hadm _ hF hG, heckeAdjointCoset_heckeT]

/-- **The Hecke operators preserve `N_{j,k}(Γ₂)`** (LMFDB `mf.siegel.subspace.degree.two`), in
every weight: `⟨T_D F, G⟩ = ⟨F, T_{D^*} G⟩ = 0` for `F ∈ N_{j,k}(Γ₂)` and a cusp form `G`, the Hecke
operators preserving the cusp forms. -/
lemma heckeOperator_mem_cuspFormsOrthogonalKJ (hadm : IsAdmissibleForm (rhoKJ k j) c)
    (D : HeckeCoset (heckeMonoid (Fin 2)) (heckeGamma (Fin 2)) (heckeGamma (Fin 2)))
    {F : slashInvariants (rhoKJ k j)}
    (hF : (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      cuspFormsOrthogonalKJ (integral (Fin 2)) k j c) :
    (heckeOperator (rhoKJ k j) D F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      cuspFormsOrthogonalKJ (integral (Fin 2)) k j c := by
  have hF₁ : (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      modularFormsKJ k j (integral (Fin 2)) := hF.1
  have hT : (heckeOperator (rhoKJ k j) D F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      modularFormsKJ k j (integral (Fin 2)) :=
    heckeOperator_mem_modularFormsKJ k j D hF₁
  refine ⟨hT, fun G hG ↦ ?_⟩
  have hG' : G ∈ slashInvariants (rhoKJ k j) :=
    ((mem_modularForms_iff_slashInvariants _ G).mp hG.1).2
  refine ⟨integrableOn_peterssonIntegrand (isModerateForm_rhoKJ k c) hadm hT hG
    (isFundamentalDomain_fundamentalDomain (isArithmetic_integral (Fin 2))), ?_⟩
  rw [peterssonProduct_heckeOperator hadm D (G := ⟨G, hG'⟩) hF₁ hG]
  exact (hF.2 _ (heckeOperator_mem_cuspFormsKJ k j _ hG)).2

end SiegelUpperHalfSpace
