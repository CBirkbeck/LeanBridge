import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.HeckeFourier
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PeterssonRhoKJ
import TauCeti.Data.Matrix.Countable

/-!
# Unfolding the Petersson product on `Sp(4, ℤ)`

Let `P` be a subgroup of `Sp(4, ℤ)` containing `±1`, and `f₀` a function with `f₀ ∣ p = f₀` for
`p ∈ P`. For a Poincaré type series `F = ∑_{δ ∈ P \ Sp(4, ℤ)} f₀ ∣ δ` and a cusp form `G`, the
Petersson integrand is `[F, G](Z) = ∑_δ [f₀, G](δZ)`, so `⟨F, G⟩ = ∫_{𝔉_P} [f₀, G]` for a
fundamental domain `𝔉_P` of `P`, as soon as the sum over `δ` of the absolute values is integrable
on the Siegel set.

The integral over `𝔉_P` is killed by averaging over the translations `T_u : Z ↦ Z + u E₁₁`, with
`E₁₁` the matrix unit in the corner of `z₁₁`: if `T_u 𝔉_P` is again a fundamental domain of `P` for
`u ∈ [0, 1]` and `f₀ ∘ T_u = f₀`, then `⟨F, G⟩` is the integral over `𝔉_P` of the average of
`b(ρ(Y) f₀(Z), G(Z + u E₁₁))` over `u ∈ [0, 1]`, which vanishes, since the Fourier coefficients of
the cusp form `G` are supported on `n` with `n₁₁ ≥ 1`.

## Main definitions

* `SiegelUpperHalfSpace.integralTransformation`: the map from `Sp(2g, ℤ)` to the transformations of
  `ℋ_g`.
* `SiegelUpperHalfSpace.cornerTranslation`: the translation `T_u`.

## Main results

* `SiegelUpperHalfSpace.bijective_integralTransformation_out`: representatives of the right cosets
  of a subgroup of `Sp(2g, ℤ)` give a transversal of its image in the transformations of `ℋ_g`.
* `SiegelUpperHalfSpace.peterssonIntegrand_slash`: `[f ∣ γ, g ∣ γ](τ) = [f, g](γτ)`.
* `SiegelUpperHalfSpace.exists_units_eq_of_mem_ker`: the kernel of the action of `Sp(4, ℤ)` on `ℋ₂`
  consists of `±1`.
* `SiegelUpperHalfSpace.setIntegral_cornerTranslation_eq_zero`: the average of a cusp form over
  `T_u` vanishes.
* `SiegelUpperHalfSpace.peterssonIntegrand_smul_eq_slash`: the Petersson integrand at a translated
  point.
* `SiegelUpperHalfSpace.integrableOn_seed_of_lintegral_tsum`,
  `SiegelUpperHalfSpace.setIntegral_peterssonIntegrand_eq_of_series`: the unfolding of the Petersson
  product.
* `SiegelUpperHalfSpace.setIntegral_peterssonIntegrand_eq_zero_of_cornerTranslation`: the vanishing
  by averaging over `T_u`.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open Complex MeasureTheory Module Real Set SymplecticGroup

open scoped ComplexConjugate ENNReal Pointwise

namespace SiegelUpperHalfSpace

section Group

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- The homomorphism from `Sp(2g, ℤ)` to the group of transformations of `ℋ_g` it induces. -/
noncomputable def integralTransformation :
    symplecticGroup l ℤ →* transformationGroup (integral l) :=
  ((MulAction.toPermHom (symplecticGroup l ℝ) (SiegelUpperHalfSpace l)).comp
    (SymplecticGroup.map (Int.castRingHom ℝ))).codRestrict _ fun γ ↦
      ⟨SymplecticGroup.map (Int.castRingHom ℚ) γ, ⟨γ, trivial, rfl⟩, by
        simp only [MonoidHom.comp_apply, map_algebraMap_map_intCast]⟩

lemma integralTransformation_smul (γ : symplecticGroup l ℤ) (τ : SiegelUpperHalfSpace l) :
    integralTransformation γ • τ = SymplecticGroup.map (Int.castRingHom ℝ) γ • τ :=
  rfl

lemma surjective_integralTransformation :
    Function.Surjective (integralTransformation (l := l)) := by
  rintro ⟨_, _, ⟨γ, -, rfl⟩, rfl⟩
  exact ⟨γ, Subtype.ext rfl⟩

variable (P : Subgroup (symplecticGroup l ℤ))

/-- **Representatives of the right cosets of a subgroup `P` of `Sp(2g, ℤ)` give a transversal of its
image in the transformations of `ℋ_g`**, when `P` contains the kernel. -/
lemma bijective_integralTransformation_out (hP : integralTransformation.ker ≤ P) :
    Function.Bijective fun x : Quotient (QuotientGroup.rightRel P) ↦
      (QuotientGroup.mk (integralTransformation x.out)⁻¹ :
        transformationGroup (integral l) ⧸ P.map integralTransformation) := by
  refine ⟨fun x y hxy ↦ ?_, fun q ↦ ?_⟩
  · have h₁ : ((integralTransformation x.out)⁻¹)⁻¹ * (integralTransformation y.out)⁻¹ ∈
        P.map integralTransformation := QuotientGroup.eq.mp hxy
    rw [inv_inv, ← map_inv, ← map_mul] at h₁
    rcases h₁ with ⟨p, hp, hpe⟩
    have h₂ : p⁻¹ * (x.out * y.out⁻¹) ∈ integralTransformation.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpe, inv_mul_cancel]
    have h₃ : y.out * x.out⁻¹ ∈ P := by
      have h₄ : (p * (p⁻¹ * (x.out * y.out⁻¹)))⁻¹ ∈ P := P.inv_mem (P.mul_mem hp (hP h₂))
      rwa [mul_inv_cancel_left, mul_inv_rev, inv_inv] at h₄
    rw [← Quotient.out_eq x, ← Quotient.out_eq y]
    exact Quotient.sound (QuotientGroup.rightRel_apply.mpr h₃)
  · rcases QuotientGroup.mk_surjective q with ⟨g, rfl⟩
    rcases surjective_integralTransformation g with ⟨γ, rfl⟩
    refine ⟨⟦γ⁻¹⟧, QuotientGroup.eq.mpr ?_⟩
    have h : γ⁻¹ * (⟦γ⁻¹⟧ : Quotient (QuotientGroup.rightRel P)).out⁻¹ ∈ P :=
      QuotientGroup.rightRel_apply.mp (Quotient.mk_out γ⁻¹)
    refine ⟨_, P.inv_mem h, ?_⟩
    simp

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL l ℂ) V}
    {b : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

/-- **The Petersson integrand of slashed functions**: `[f ∣ γ, g ∣ γ](τ) = [f, g](γτ)` for
`γ ∈ Sp(2g, ℝ)` and an admissible form. -/
lemma peterssonIntegrand_slash (hadm : IsAdmissibleForm ρ b) (f g : SiegelUpperHalfSpace l → V)
    (γ : symplecticGroup l ℝ) (τ : SiegelUpperHalfSpace l) :
    peterssonIntegrand ρ b (slash ρ γ f) (slash ρ γ g) τ = peterssonIntegrand ρ b f g (γ • τ) := by
  have h : star (denomGL γ τ)⁻¹ * imGL τ * (denomGL γ τ)⁻¹ = imGL (γ • τ) := by
    conv_lhs => rw [← star_denomGL_mul_imGL_smul_mul_denomGL τ γ]
    simp [mul_assoc]
  have h₁ (x y : V) : b x (ρ (denomGL γ τ)⁻¹ y) = b (ρ (star (denomGL γ τ)⁻¹) x) y := by
    rw [hadm, star_star]
  rw [peterssonIntegrand_apply, peterssonIntegrand_apply, slash_apply, slash_apply, h₁, ← h,
    map_mul, map_mul, End.mul_apply, End.mul_apply]

end Group

/-- **The kernel of the action of `Sp(4, ℤ)` on `ℋ₂` consists of scalar matrices**, in fact `±1`. -/
lemma exists_units_eq_of_mem_ker {γ : symplecticGroup (Fin 2) ℤ}
    (hγ : γ ∈ integralTransformation.ker) :
    ∃ v : ℤˣ, ∀ x y, γ.1 x y = if x = y then (v : ℤ) else 0 := by
  have h₁ (τ : SiegelUpperHalfSpace (Fin 2)) :
      SymplecticGroup.map (Int.castRingHom ℝ) γ • τ = τ := by
    rw [← integralTransformation_smul, MonoidHom.mem_ker.mp hγ, one_smul]
  rcases exists_eq_smul_one_of_forall_smul_eq h₁ with ⟨r, hr⟩
  have h₂ (x y : Fin 2 ⊕ Fin 2) : ((γ.1 x y : ℤ) : ℝ) = if x = y then r else 0 := by
    have h₃ : ((SymplecticGroup.map (Int.castRingHom ℝ) γ : symplecticGroup (Fin 2) ℝ) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) x y =
          (r • 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) x y :=
      congrFun (congrFun hr x) y
    rw [SymplecticGroup.coe_map_apply] at h₃
    simpa [one_apply] using h₃
  have h₄ (x y : Fin 2 ⊕ Fin 2) : γ.1 x y = if x = y then γ.1 (.inl 0) (.inl 0) else 0 := by
    have h₅ : ((γ.1 x y : ℤ) : ℝ) = if x = y then r else 0 := h₂ x y
    have h₆ :
        ((γ.1 (.inl 0) (.inl 0) : ℤ) : ℝ) = if (Sum.inl 0 : Fin 2 ⊕ Fin 2) = .inl 0 then r else 0 :=
      h₂ (.inl 0) (.inl 0)
    rw [ite_eq_left (rfl : (Sum.inl 0 : Fin 2 ⊕ Fin 2) = .inl 0)] at h₆
    rw [← h₆] at h₅
    split_ifs at h₅ ⊢ <;> exact_mod_cast h₅
  have h₇ : (γ.1 * J (Fin 2) ℤ * γ.1ᵀ) (.inl 0) (.inr 0) = J (Fin 2) ℤ (.inl 0) (.inr 0) :=
    congrFun (congrFun (SymplecticGroup.mem_iff.mp γ.2) _) _
  generalize γ.1 (.inl 0) (.inl 0) = v₀ at h₄
  have h₈ : v₀ * v₀ = 1 := by
    simp [Matrix.mul_apply, J, h₄] at h₇
    exact h₇
  rcases IsUnit.of_mul_eq_one _ h₈ with ⟨v, rfl⟩
  exact ⟨v, h₄⟩

/-! ### Averaging a cusp form over translations -/

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin 2) ℂ) V}
    {b : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

/-- The translation `T_u : Z ↦ Z + u E₁₁` of `ℋ₂`, in the corner of `z₁₁`. -/
noncomputable def cornerTranslation (u : ℝ) : symplecticGroup (Fin 2) ℝ :=
  symTranslation (u • single 1 1 1) (by rw [transpose_smul, transpose_single])

variable (u : ℝ) (Z : SiegelUpperHalfSpace (Fin 2))

lemma val_cornerTranslation_smul (i j : Fin 2) :
    (cornerTranslation u • Z).val i j = Z.val i j + if i = 1 ∧ j = 1 then (u : ℂ) else 0 := by
  rw [cornerTranslation, val_smul_symTranslation]
  fin_cases i <;> fin_cases j <;> simp

lemma im_cornerTranslation_smul (i j : Fin 2) :
    ((cornerTranslation u • Z).val i j).im = (Z.val i j).im := by
  rw [val_cornerTranslation_smul]
  split_ifs <;> simp

lemma imGL_cornerTranslation_smul : imGL (cornerTranslation u • Z) = imGL Z :=
  Units.ext <| by
    rw [coe_imGL, coe_imGL]
    ext i j
    simp [im_cornerTranslation_smul]

lemma continuous_cornerTranslation_smul :
    Continuous fun p : ℝ × SiegelUpperHalfSpace (Fin 2) ↦ cornerTranslation p.1 • p.2 := by
  refine continuous_induced_rng.mpr (continuous_pi fun s ↦ ?_)
  induction s using Sym2.ind with
  | _ i j =>
    have e (p : ℝ × SiegelUpperHalfSpace (Fin 2)) : (cornerTranslation p.1 • p.2).toCoords s(i, j) =
        p.2.val i j + if i = 1 ∧ j = 1 then (p.1 : ℂ) else 0 := by
      rw [← val_cornerTranslation_smul]
      exact congrFun (congrFun (ofSymCoords_toCoords _) i) j
    simp only [Function.comp_apply, e]
    refine ((continuous_apply_apply i j).comp (continuous_val.comp continuous_snd)).add ?_
    split_ifs
    · exact continuous_ofReal.comp continuous_fst
    · exact continuous_const

private lemma fourierExp_cornerTranslation_smul {Γ : Subgroup (symplecticGroup (Fin 2) ℚ)}
    (n : dualLattice Γ) : fourierExp n (cornerTranslation u • Z) = fourierExp n Z *
      cexp (2 * π * I * (((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℂ) * u)) := by
  rw [fourierExp, fourierExp, ← Complex.exp_add]
  congr 1
  simp [trace, Matrix.mul_apply, val_cornerTranslation_smul]
  ring1

lemma integral_cexp_int_eq_zero {m : ℤ} (hm : m ≠ 0) :
    ∫ u in Icc (0 : ℝ) 1, cexp (2 * π * I * ((m : ℂ) * u)) = 0 := by
  simp only [← mul_assoc]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    UpperHalfPlane.intervalIntegral_exp_two_pi_I_mul, ite_eq_right hm]

variable {G : SiegelUpperHalfSpace (Fin 2) → V}

lemma slash_eq_of_mem_modularForms (hG : G ∈ modularForms ρ (integral (Fin 2)) 1)
    (γ : symplecticGroup (Fin 2) ℤ) :
    slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) γ) G = G := by
  have h : slash ρ (SymplecticGroup.map (algebraMap ℚ ℝ)
      (SymplecticGroup.map (Int.castRingHom ℚ) γ)) G = G := by
    simpa using ((mem_modularForms_iff_slash ρ G (integral (Fin 2)) 1).mp hG).2
      ⟨_, γ, trivial, rfl⟩
  rwa [map_algebraMap_map_intCast] at h

variable {P : Subgroup (symplecticGroup (Fin 2) ℤ)} {f₀ F : SiegelUpperHalfSpace (Fin 2) → V}

/-- **The Petersson integrand at a translated point**:
`[f₀, G](δZ) = b(ρ(Im Z) (f₀ ∣ δ)(Z), G(Z))` for a modular form `G` on `Sp(4, ℤ)` and
`δ ∈ Sp(4, ℤ)`. -/
lemma peterssonIntegrand_smul_eq_slash (hadm : IsAdmissibleForm ρ b)
    (hG : G ∈ modularForms ρ (integral (Fin 2)) 1) (γ : symplecticGroup (Fin 2) ℤ) :
    peterssonIntegrand ρ b f₀ G (integralTransformation γ • Z) =
      b (ρ (imGL Z) (slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) γ) f₀ Z)) (G Z) := by
  rw [integralTransformation_smul, ← peterssonIntegrand_slash hadm, slash_eq_of_mem_modularForms hG]
  rfl

lemma peterssonIntegrand_map_integralTransformation_smul (hadm : IsAdmissibleForm ρ b)
    (hG : G ∈ modularForms ρ (integral (Fin 2)) 1)
    (hf₀ : ∀ p ∈ P, slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) p) f₀ = f₀)
    (h : P.map integralTransformation) (x : SiegelUpperHalfSpace (Fin 2)) :
    peterssonIntegrand ρ b f₀ G (h • x) = peterssonIntegrand ρ b f₀ G x := by
  rcases h with ⟨_, p, hp, rfl⟩
  exact (peterssonIntegrand_smul_eq_slash x hadm hG p).trans
    (by rw [hf₀ p hp, peterssonIntegrand_apply])

private lemma hasSum_peterssonIntegrand_series (hadm : IsAdmissibleForm ρ b)
    (hG : G ∈ modularForms ρ (integral (Fin 2)) 1)
    (hF : ∀ (Z : SiegelUpperHalfSpace (Fin 2)) (φ : Dual ℂ V),
      HasSum (fun x : Quotient (QuotientGroup.rightRel P) ↦
        φ (slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) x.out) f₀ Z)) (φ (F Z))) :
    HasSum (fun x : Quotient (QuotientGroup.rightRel P) ↦
      peterssonIntegrand ρ b f₀ G (integralTransformation x.out • Z))
        (peterssonIntegrand ρ b F G Z) :=
  (hF Z ((b.flip (G Z)) ∘ₗ ρ (imGL Z))).congr_fun fun x ↦
    peterssonIntegrand_smul_eq_slash Z hadm hG x.out

variable [FiniteDimensional ℂ V]

/-- **The average of a cusp form over the translations `T_u` vanishes**: the Fourier coefficients of
a cusp form on `Sp(4, ℤ)` are supported on `n` with `n₁₁` a nonzero integer, so each term of the
Fourier expansion integrates to `0` over `u ∈ [0, 1]`. -/
lemma setIntegral_cornerTranslation_eq_zero (hG : G ∈ cuspForms ρ (integral (Fin 2)) 1)
    (ψ : Dual ℂ V) : ∫ u in Icc (0 : ℝ) 1, ψ (G (cornerTranslation u • Z)) = 0 := by
  rcases exists_hasSiegelFourierExpansion ρ (isArithmetic_integral (Fin 2)) hG.1 with ⟨a, ha⟩
  have hv : SiegelOperatorVanishes G := by
    have h : SiegelOperatorVanishes (slash ρ (SymplecticGroup.map (algebraMap ℚ ℝ) 1) G) := hG.2 1
    rwa [map_one, slash_one] at h
  have hpd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosDef :=
    posDef_of_siegelOperatorVanishes hG.1 ha hv
  let F (n : dualLattice (integral (Fin 2))) (u : ℝ) : ℂ :=
    fourierExp n (cornerTranslation u • Z) * ψ (a n)
  have hF (n : dualLattice (integral (Fin 2))) (u : ℝ) : F n u = fourierExp n Z * ψ (a n) *
      cexp (2 * π * I * (((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℂ) * u)) := by
    simp only [F, fourierExp_cornerTranslation_smul]
    ring1
  have hcont (n : dualLattice (integral (Fin 2))) : Continuous (F n) := by
    rw [funext (hF n)]
    fun_prop
  have hnorm (n : dualLattice (integral (Fin 2))) (u : ℝ) :
      ‖F n u‖ = ‖fourierExp n Z * ψ (a n)‖ := by
    rw [hF, norm_mul]
    have e : 2 * π * I * (((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℂ) * u) =
        ((2 * π * ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) * u : ℝ) : ℂ) * I := by
      push_cast
      ring1
    rw [e, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hint (n : dualLattice (integral (Fin 2))) :
      Integrable (F n) (volume.restrict (Icc (0 : ℝ) 1)) :=
    (hcont n).integrableOn_Icc
  have hsum : Summable fun n ↦ ∫ u in Icc (0 : ℝ) 1, ‖F n u‖ := by
    simp only [hnorm]
    simpa using (ha Z ψ).summable.norm
  have hzero (n : dualLattice (integral (Fin 2))) : ∫ u in Icc (0 : ℝ) 1, F n u = 0 := by
    by_cases hn : a n = 0
    · simp [F, hn]
    rcases exists_intCast_eq_apply n 1 with ⟨m, hm⟩
    have hm₀ : m ≠ 0 := by
      rintro rfl
      have h₁ : 0 < (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 := (hpd n hn).diag_pos
      rw [hm] at h₁
      simp at h₁
    have e (u : ℝ) : F n u = fourierExp n Z * ψ (a n) * cexp (2 * π * I * ((m : ℂ) * u)) := by
      rw [hF, hm]
      simp
    simp only [e]
    rw [integral_const_mul, integral_cexp_int_eq_zero hm₀, mul_zero]
  have hs : ∑' n, ∫ u in Icc (0 : ℝ) 1, F n u = ∫ u in Icc (0 : ℝ) 1, ∑' n, F n u :=
    integral_tsum_of_summable_integral_norm hint hsum
  have hG' (u : ℝ) : ∑' n, F n u = ψ (G (cornerTranslation u • Z)) :=
    (ha _ ψ).tsum_eq
  simp only [hzero, hG', tsum_zero] at hs
  exact hs.symm

lemma setIntegral_sesquilinear_cornerTranslation_eq_zero (hG : G ∈ cuspForms ρ (integral (Fin 2)) 1)
    (w : V) : ∫ u in Icc (0 : ℝ) 1, b w (G (cornerTranslation u • Z)) = 0 := by
  let ψ : Dual ℂ V :=
    { toFun v := conj (b w v)
      map_add' v v' := by
        simp
      map_smul' a v := by
        simp }
  have h₁ : conj (∫ u in Icc (0 : ℝ) 1, ψ (G (cornerTranslation u • Z))) = conj 0 :=
    congrArg conj (setIntegral_cornerTranslation_eq_zero Z hG ψ)
  rw [← integral_conj, map_zero] at h₁
  simpa [ψ] using h₁

/-! ### The series -/

/-- **Unfolding**: for a series `F = ∑_{δ ∈ P \ Sp(4, ℤ)} f₀ ∣ δ` with `f₀ ∣ p = f₀` for `p ∈ P`,
whose Petersson integrand against `G` converges absolutely in `L¹` on the Siegel set, the integrand
`[f₀, G]` is integrable on every fundamental domain of `P`. -/
lemma integrableOn_seed_of_lintegral_tsum (hb : IsModerateForm ρ b) (hadm : IsAdmissibleForm ρ b)
    (hG : G ∈ modularForms ρ (integral (Fin 2)) 1) (hP : integralTransformation.ker ≤ P)
    (hf₀ : ∀ p ∈ P, slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) p) f₀ = f₀)
    (hf₀c : ∀ φ : Dual ℂ V, Continuous fun τ ↦ φ (f₀ τ))
    (hfin : ∫⁻ τ in siegelSet, ∑' x : Quotient (QuotientGroup.rightRel P),
      ‖peterssonIntegrand ρ b f₀ G (integralTransformation x.out • τ)‖ₑ
        ∂invariantMeasure (Fin 2) < ∞) {F' : Set (SiegelUpperHalfSpace (Fin 2))}
    (hF' : IsFundamentalDomain (P.map integralTransformation) F' (invariantMeasure (Fin 2))) :
    IntegrableOn (peterssonIntegrand ρ b f₀ G) F' (invariantMeasure (Fin 2)) := by
  have hcont : Continuous (peterssonIntegrand ρ b f₀ G) :=
    continuous_peterssonIntegrand_of_dual hb hf₀c hG.1.continuous_dual
  refine hF'.integrableOn_of_setLIntegral_tsum_lt_top (t := siegelSet)
    (bijective_integralTransformation_out P hP).surjective hcont.aestronglyMeasurable
    (fun x ↦ ?_) (peterssonIntegrand_map_integralTransformation_smul hadm hG hf₀)
    (.of_forall exists_smul_mem_siegelSet_transformationGroup) hfin
  have hc : Continuous fun τ : SiegelUpperHalfSpace (Fin 2) ↦
      ‖peterssonIntegrand ρ b f₀ G (integralTransformation x.out • τ)‖ₑ :=
    (hcont.comp (continuous_const_smul (SymplecticGroup.map (Int.castRingHom ℝ) x.out))).enorm
  exact hc.aemeasurable

/-- **Unfolding**: for a series `F = ∑_{δ ∈ P \ Sp(4, ℤ)} f₀ ∣ δ` with `f₀ ∣ p = f₀` for `p ∈ P`,
`⟨F, G⟩ = ∫_{𝔉_P} [f₀, G]` for fundamental domains `𝔉` of `Sp(4, ℤ)` and `𝔉_P` of `P`. -/
lemma setIntegral_peterssonIntegrand_eq_of_series (hb : IsModerateForm ρ b)
    (hadm : IsAdmissibleForm ρ b) (hG : G ∈ modularForms ρ (integral (Fin 2)) 1)
    (hP : integralTransformation.ker ≤ P)
    (hf₀ : ∀ p ∈ P, slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) p) f₀ = f₀)
    (hf₀c : ∀ φ : Dual ℂ V, Continuous fun τ ↦ φ (f₀ τ))
    (hF : ∀ (Z : SiegelUpperHalfSpace (Fin 2)) (φ : Dual ℂ V),
      HasSum (fun x : Quotient (QuotientGroup.rightRel P) ↦
        φ (slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) x.out) f₀ Z)) (φ (F Z)))
    (hfin : ∫⁻ τ in siegelSet, ∑' x : Quotient (QuotientGroup.rightRel P),
      ‖peterssonIntegrand ρ b f₀ G (integralTransformation x.out • τ)‖ₑ
        ∂invariantMeasure (Fin 2) < ∞) {s F' : Set (SiegelUpperHalfSpace (Fin 2))}
    (hs : IsFundamentalDomain (transformationGroup (integral (Fin 2))) s (invariantMeasure (Fin 2)))
    (hF' : IsFundamentalDomain (P.map integralTransformation) F' (invariantMeasure (Fin 2))) :
    ∫ τ in s, peterssonIntegrand ρ b F G τ ∂invariantMeasure (Fin 2) =
      ∫ τ in F', peterssonIntegrand ρ b f₀ G τ ∂invariantMeasure (Fin 2) := by
  rw [← hs.setIntegral_tsum_smul_eq hF' (bijective_integralTransformation_out P hP)
    (peterssonIntegrand_map_integralTransformation_smul hadm hG hf₀)
      (integrableOn_seed_of_lintegral_tsum hb hadm hG hP hf₀ hf₀c hfin hF')]
  exact setIntegral_congr_fun₀ hs.nullMeasurableSet fun τ _ ↦
    (hasSum_peterssonIntegrand_series τ hadm hG hF).tsum_eq.symm

/-- **The Petersson integrand against a cusp form vanishes on a fundamental domain with translated
fundamental domains**: if `f₀` is invariant under `T_u`, and `s` is a fundamental domain of a group
`H` of transformations with `T_u s` a fundamental domain of `H` for `u ∈ [0, 1]`, then
`∫_s [f₀, G] = 0`, for a cusp form `G`. -/
lemma setIntegral_peterssonIntegrand_eq_zero_of_cornerTranslation {H : Type*} [Group H]
    [MulAction H (SiegelUpperHalfSpace (Fin 2))]
    [MeasurableConstSMul H (SiegelUpperHalfSpace (Fin 2))]
    [SMulInvariantMeasure H (SiegelUpperHalfSpace (Fin 2)) (invariantMeasure (Fin 2))] [Countable H]
    (hb : IsModerateForm ρ b) (hG : G ∈ cuspForms ρ (integral (Fin 2)) 1)
    (hf₀ : ∀ u Z, f₀ (cornerTranslation u • Z) = f₀ Z)
    (hf₀c : ∀ φ : Dual ℂ V, Continuous fun τ ↦ φ (f₀ τ)) {s : Set (SiegelUpperHalfSpace (Fin 2))}
    (hs : IsFundamentalDomain H s (invariantMeasure (Fin 2)))
    (hc : ∀ u ∈ Icc (0 : ℝ) 1, IsFundamentalDomain H (cornerTranslation u • s)
      (invariantMeasure (Fin 2)))
    (hf : ∀ (h : H) (x : SiegelUpperHalfSpace (Fin 2)),
      peterssonIntegrand ρ b f₀ G (h • x) = peterssonIntegrand ρ b f₀ G x)
    (hint : IntegrableOn (peterssonIntegrand ρ b f₀ G) s (invariantMeasure (Fin 2))) :
    ∫ τ in s, peterssonIntegrand ρ b f₀ G τ ∂invariantMeasure (Fin 2) = 0 := by
  have hcont : Continuous (peterssonIntegrand ρ b f₀ G) :=
    continuous_peterssonIntegrand_of_dual hb hf₀c hG.1.1.continuous_dual
  refine hs.setIntegral_eq_zero_of_average hc hf hint
    (hcont.comp continuous_cornerTranslation_smul).aestronglyMeasurable fun x ↦ ?_
  have e (u : ℝ) : peterssonIntegrand ρ b f₀ G (cornerTranslation u • x) =
      b (ρ (imGL x) (f₀ x)) (G (cornerTranslation u • x)) := by
    rw [peterssonIntegrand_apply, imGL_cornerTranslation_smul, hf₀]
  simp only [e]
  exact setIntegral_sesquilinear_cornerTranslation_eq_zero x hG _

end SiegelUpperHalfSpace
