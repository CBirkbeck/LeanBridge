import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.LevelTwoVectorRepresentation
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularLevelRaisingThetaPrime

/-!
# The Hecke operators on vector-valued Siegel modular and cusp forms of degree 2

The LMFDB knowl `mf.siegel.subspace.degree.two` says that the decomposition
`M_{j,k}(Γ₂) = S_{j,k}(Γ₂) ⊕ N_{j,k}(Γ₂)` is stable under the Hecke operators. This file proves the
stability of `M_{j,k}(Γ₂)` and of `S_{j,k}(Γ₂)`. An element `α` of the monoid
`GSp(4, ℚ)⁺ ∩ M₄(ℤ)` of Hecke operators has multiplier a positive integer `r`, and
`α = diag(r, r, 1, 1) γ` with `γ ∈ Sp(4, ℚ)`, so the slash operator of `α` is the composite of those
of `diag(r, r, 1, 1)` and of `γ`, which preserve cusp forms. The stability of `N_{j,k}(Γ₂)`, which
needs the adjoints of the Hecke operators for the Petersson product, is not proved here.

## Main results

* `SiegelUpperHalfSpace.isHolomorphic_gspSlash_rhoKJ`: the slash operator of `GSp(4, ℚ)⁺` of weight
  `ρ_{k,j}` preserves holomorphy.
* `SiegelUpperHalfSpace.exists_eq_thetaPrimeDiag_mul`: the decomposition `α = diag(r, r, 1, 1) γ`.
* `SiegelUpperHalfSpace.IsCuspForm.heckeMonoidSlash_of_mem`: the slash operators of the Hecke
  operators preserve the cusp forms.
* `SiegelUpperHalfSpace.heckeOperator_mem_modularFormsKJ`: the Hecke operators preserve
  `M_{j,k}(Γ₂)`.
* `SiegelUpperHalfSpace.heckeOperator_mem_cuspFormsKJ`: the Hecke operators preserve `S_{j,k}(Γ₂)`.
-/

open Complex Module

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open scoped TensorProduct

namespace SiegelUpperHalfSpace

variable (k : ℤ) (j : ℕ)
    (E : HeckeCoset (heckeMonoid (Fin 2)) (heckeGamma (Fin 2)) (heckeGamma (Fin 2)))
    {F : slashInvariants (rhoKJ k j)}

/-- **The slash operator of `GSp(4, ℚ)⁺` of weight `ρ_{k,j}` preserves holomorphy**: it is a fixed
invertible linear map composed with the slash operator of the real symplectic matrix
`r(β)^(-1/2) β`, since `gspDenom β τ` is the scalar `√r(β)` times `denom (toSp β) τ`. -/
lemma isHolomorphic_gspSlash_rhoKJ (β : gspPlus (Fin 2))
    {f : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)} (hf : IsHolomorphic f) :
    IsHolomorphic (gspSlash (rhoKJ k j) β f) := by
  have hr : (√(multiplier β : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr <| Real.sqrt_ne_zero'.mpr <| Rat.cast_pos.mpr <| multiplier_pos β
  let c : GL (Fin 2) ℂ := GeneralLinearGroup.scalar (Fin 2) (Units.mk0 _ hr)
  have hc (τ : SiegelUpperHalfSpace (Fin 2)) :
      gspDenomGL β τ = c * denomGL (toSp β) τ :=
    Units.ext <| by
      rw [Units.val_mul, coe_gspDenomGL, gspDenom_eq, coe_denomGL, GeneralLinearGroup.coe_scalar,
        scalar_apply, ← smul_eq_diagonal_mul]
      rfl
  have hcomm (τ : SiegelUpperHalfSpace (Fin 2)) :
      (denomGL (toSp β) τ)⁻¹ * c⁻¹ = c⁻¹ * (denomGL (toSp β) τ)⁻¹ := by
    have h₀ : c * denomGL (toSp β) τ = denomGL (toSp β) τ * c :=
      Units.ext <| by
        rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply,
          ← smul_eq_diagonal_mul, ← smul_eq_mul_diagonal]
    rw [← mul_inv_rev, ← mul_inv_rev, h₀]
  refine fun φ ↦ ?_
  have e : φ ∘ gspSlash (rhoKJ k j) β f =
      (((multiplier β : ℂ) ^ slashExponent (rhoKJ k j)) • (φ ∘ₗ rhoKJ k j c⁻¹)) ∘
        slash (rhoKJ k j) (toSp β) f := by
    funext τ
    simp only [Function.comp_apply, gspSlash, slash_apply, hc, mul_inv_rev, hcomm, map_mul,
      End.mul_apply, map_smul, LinearMap.smul_apply, LinearMap.comp_apply, gspSmul]
  rw [e]
  exact hf.slash_rhoKJ k (toSp β) _

/-- **The Hecke operators preserve `M_{j,k}(Γ₂)`.** -/
lemma heckeOperator_mem_modularFormsKJ
    (hF : (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      modularFormsKJ k j (SymplecticGroup.integral (Fin 2))) :
    (heckeOperator (rhoKJ k j) E F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      modularFormsKJ k j (SymplecticGroup.integral (Fin 2)) :=
  heckeOperator_mem_modularForms _ E (fun α _ hf ↦ isHolomorphic_gspSlash_rhoKJ k j α hf) hF

private lemma coe_thetaPrimeDiag_inv (p : ℕ+) :
    (((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) =
        diagonal (Sum.elim ![(p : ℚ)⁻¹, (p : ℚ)⁻¹] ![1, 1]) :=
  Units.inv_eq_of_mul_eq_one_right <| by
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [thetaPrimeDiag, diagSimilitude]

/-- **An element of `GSp(4, ℚ)⁺ ∩ M₄(ℤ)` is `diag(r, r, 1, 1) γ`** for a positive integer `r`, its
multiplier, and `γ ∈ Sp(4, ℚ)`. -/
lemma exists_eq_thetaPrimeDiag_mul (x : heckeMonoid (Fin 2)) :
    ∃ (r : ℕ+) (γ : symplecticGroup (Fin 2) ℚ), (x : GL (Fin 2 ⊕ Fin 2) ℚ) =
      (thetaPrimeDiag r : GL (Fin 2 ⊕ Fin 2) ℚ) * spRatToGL (Fin 2) γ := by
  rcases x with ⟨x, ⟨r, hr, hx⟩, A, hA⟩
  have hx' : (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)ᵀ * J (Fin 2) ℚ * x = r • J (Fin 2) ℚ :=
    hx
  have hA' : A.map (Int.castRingHom ℚ) = (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :=
    hA
  have hrZ : r = ((Aᵀ * J (Fin 2) ℤ * A) (.inr 0) (.inl 0) : ℤ) := by
    have e₁ : (Aᵀ * J (Fin 2) ℤ * A).map (Int.castRingHom ℚ) = r • J (Fin 2) ℚ := by
      rw [Matrix.map_mul, Matrix.map_mul, transpose_map, hA', map_J]
      exact hx'
    have e₂ : ((Aᵀ * J (Fin 2) ℤ * A).map (Int.castRingHom ℚ)) (.inr 0) (.inl 0) =
        (r • J (Fin 2) ℚ) (.inr 0) (.inl 0) :=
      congrFun (congrFun e₁ (.inr 0)) (.inl 0)
    simpa [J] using e₂.symm
  generalize (Aᵀ * J (Fin 2) ℤ * A) (.inr 0) (.inl 0) = n at hrZ
  have hn : 0 < n := by
    rw [hrZ] at hr
    exact_mod_cast hr
  let p : ℕ+ := ⟨n.toNat, by omega⟩
  have hp : (p : ℚ) = r := by
    have e : ((p : ℕ) : ℤ) = n :=
      Int.toNat_of_nonneg hn.le
    rw [hrZ, ← e]
    simp
  have hp₀ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.ne_zero
  have hE : (((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)ᵀ * J (Fin 2) ℚ *
        ((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) =
      (p : ℚ)⁻¹ • J (Fin 2) ℚ := by
    rw [coe_thetaPrimeDiag_inv]
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [J, Matrix.mul_apply]
  have hγ : ((((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ * x : GL (Fin 2 ⊕ Fin 2) ℚ)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) ∈ symplecticGroup (Fin 2) ℚ := by
    rw [SymplecticGroup.mem_iff', Units.val_mul, transpose_mul]
    have e : (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)ᵀ *
        (((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)ᵀ * J (Fin 2) ℚ *
          (((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) * x) =
        (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)ᵀ *
          ((((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)ᵀ * J (Fin 2) ℚ *
              ((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ)) * x := by
      simp only [Matrix.mul_assoc]
    rw [e, hE, Matrix.mul_smul, Matrix.smul_mul, hx', hp, smul_smul, inv_mul_cancel₀ (hp ▸ hp₀),
      one_smul]
  have e : spRatToGL (Fin 2) ⟨_, hγ⟩ = (thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ * x :=
    Units.ext rfl
  exact ⟨p, ⟨_, hγ⟩, (mul_inv_cancel_left _ x).symm.trans (congrArg _ e.symm)⟩

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) ℂ) V)
    {f : SiegelUpperHalfSpace (Fin 2) → V}

/-- **The slash operators of the Hecke operators preserve the cusp forms**: for
`α = diag(r, r, 1, 1) γ`, `F ∣ α = (F ∣ diag(r, r, 1, 1)) ∣ γ`. -/
lemma IsCuspForm.heckeMonoidSlash_of_mem (hf : IsCuspForm ρ f) (x : heckeMonoid (Fin 2)) :
    IsCuspForm ρ (heckeMonoidSlash ρ x f) := by
  rcases exists_eq_thetaPrimeDiag_mul x with ⟨r, γ, hx⟩
  have e : heckeMonoidSlash ρ x f =
      heckeMonoidSlash ρ (thetaPrimeDiag r * spToGSpPlusGL γ) f :=
    congrArg (gspSlash ρ · f) (Subtype.ext (congrArg Units.val hx))
  rw [e, heckeMonoidSlash_mul, heckeMonoidSlash_eq_slash ρ _ (coe_spToGSpPlusGL γ)]
  exact (hf.heckeMonoidSlash_thetaPrimeDiag ρ r).slash ρ γ

/-- **The Hecke operators preserve `S_{j,k}(Γ₂)`.** -/
lemma heckeOperator_mem_cuspFormsKJ
    (hF : (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      cuspFormsKJ k j (SymplecticGroup.integral (Fin 2))) :
    (heckeOperator (rhoKJ k j) E F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      cuspFormsKJ k j (SymplecticGroup.integral (Fin 2)) := by
  refine ⟨heckeOperator_mem_modularFormsKJ k j E hF.1, ?_⟩
  rw [coe_heckeOperator]
  exact Finset.sum_induction _ (IsCuspForm (rhoKJ k j))
    (fun _ _ hg hg' γ ↦ by
      rw [slash_add]
      exact (hg γ).add (hg' γ))
    (fun γ ↦ by
      rw [slash_zero]
      exact siegelOperatorVanishes_zero) fun v _ ↦ hF.2.heckeMonoidSlash_of_mem _ _

end SiegelUpperHalfSpace
