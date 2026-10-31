import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.IbukiyamaRings
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ThetaTransformation

/-!
# The generators of Ibukiyama's rings: holomorphy and the parabolic transformation law

The generators `X`, `Y`, `Z`, `K`, `χ₅`, `f₆`, `f₁₁`, `f₂`, `f₁` of the rings of Siegel modular
forms of degree 2 on `Γ₀(2)` and `Γ₀(4)` (LMFDB `mf.siegel.family.gamma0_2`,
`mf.siegel.family.gamma0_4_psi_4`) are polynomials in the theta constants, so they are
holomorphic (`SiegelUpperHalfSpace.isHolomorphic_thetaConstant`).

An element `γ = (A, B; 0, D)` of the Siegel parabolic subgroup `P(ℤ)` of `Sp(4, ℤ)`, which lies in
`Γ₀(N)` for every `N`, sends `θ_{0,ν}` to `θ_{0, Dᵀ(ν + diag(S))}` with `S = BAᵀ`
(`SiegelUpperHalfSpace.thetaConstant_smul_of_mem_siegelParabolic`), and `θ_{0,ν}` only depends on
`ν` modulo 2. So `γ` permutes the four theta constants `θ₀₀₀₀, θ₀₀₀₁, θ₀₀₁₀, θ₀₀₁₁` through the
affine bijection `v ↦ Dᵀ(v + diag(S))` of `(ℤ/2ℤ)²`, and `X` and `Y`, symmetric in them, are
invariant, while `det(cΩ + d) = det D = ±1`. Hence `X` and `Y` are Siegel modular forms of weights
2 and 4 on `P(ℤ)`. Similarly `(A, 2B; 0, D) ∈ P(ℤ)` sends `2Ω` to `2γΩ` and fixes `θ₀₀₀₀`, and
`ψ₄(γ) = det D`, so `f₁(2Ω) = θ₀₀₀₀(2Ω)²` is a form of weight 1 and character `ψ₄` on `P(ℤ)`. The
rest of `Γ₀(2)` and `Γ₀(4)` needs the inversions, whose transformation law is
`SiegelUpperHalfSpace.thetaConstant_eq_partialInversion`, and generators of `Γ₀(2)` and `Γ₀(4)`,
which are not formalised: the modularity on `Γ₀(2)` remains a statement
(`SiegelUpperHalfSpace.Ibukiyama.Gamma0TwoStructure`).

## Main definitions

* `SiegelUpperHalfSpace.Ibukiyama.parabolic`: the Siegel parabolic subgroup of `Sp(4, ℤ)`, in
  `Sp(4, ℚ)`.

## Main results

* `SiegelUpperHalfSpace.Ibukiyama.X_smul_of_mem_siegelParabolic`,
  `SiegelUpperHalfSpace.Ibukiyama.Y_smul_of_mem_siegelParabolic`: `X(γΩ) = X(Ω)` and
  `Y(γΩ) = Y(Ω)` for `γ` in the Siegel parabolic subgroup of `Sp(4, ℤ)`.
* `SiegelUpperHalfSpace.Ibukiyama.X_mem_parabolic`,
  `SiegelUpperHalfSpace.Ibukiyama.Y_mem_parabolic`: `X ∈ M₂(P(ℤ))` and `Y ∈ M₄(P(ℤ))`.
* `SiegelUpperHalfSpace.Ibukiyama.psi4Rat_map_of_mem_siegelParabolic`: `ψ₄(γ) = det D` on `P(ℤ)`.
* `SiegelUpperHalfSpace.Ibukiyama.f1_comp_double_mem_parabolic`: `f₁(2Ω) ∈ M₁(P(ℤ), ψ₄)`.
-/

open Complex Matrix

namespace SiegelUpperHalfSpace.Ibukiyama

lemma isHolomorphic_theta (a b c d : ℤ) : IsHolomorphic (theta a b c d) :=
  isHolomorphic_thetaConstant _ _

lemma isHolomorphic_X : IsHolomorphic X :=
  ((((isHolomorphic_theta 0 0 0 0).pow 4).add ((isHolomorphic_theta 0 0 0 1).pow 4)).add
    ((isHolomorphic_theta 0 0 1 0).pow 4) |>.add ((isHolomorphic_theta 0 0 1 1).pow 4)).div_const 4

lemma isHolomorphic_Y : IsHolomorphic Y :=
  ((((isHolomorphic_theta 0 0 0 0).mul (isHolomorphic_theta 0 0 0 1)).mul
    (isHolomorphic_theta 0 0 1 0)).mul (isHolomorphic_theta 0 0 1 1)).pow 2

lemma isHolomorphic_Z : IsHolomorphic Z :=
  (((isHolomorphic_theta 0 1 0 0).pow 4).sub ((isHolomorphic_theta 0 1 1 0).pow 4) |>.pow 2)
    |>.div_const 16384

lemma isHolomorphic_K : IsHolomorphic K :=
  ((((((isHolomorphic_theta 0 1 0 0).mul (isHolomorphic_theta 0 1 1 0)).mul
    (isHolomorphic_theta 1 0 0 0)).mul (isHolomorphic_theta 1 0 0 1)).mul
      (isHolomorphic_theta 1 1 0 0)).mul (isHolomorphic_theta 1 1 1 1) |>.pow 2).div_const 4096

lemma isHolomorphic_chi5 : IsHolomorphic chi5 :=
  (((((((((isHolomorphic_theta 0 0 0 0).mul (isHolomorphic_theta 0 0 0 1)).mul
    (isHolomorphic_theta 0 0 1 0)).mul (isHolomorphic_theta 0 0 1 1)).mul
      (isHolomorphic_theta 0 1 0 0)).mul (isHolomorphic_theta 0 1 1 0)).mul
        (isHolomorphic_theta 1 0 0 0)).mul (isHolomorphic_theta 1 0 0 1)).mul
          (isHolomorphic_theta 1 1 0 0)).mul (isHolomorphic_theta 1 1 1 1)

lemma isHolomorphic_f6 : IsHolomorphic f6 :=
  ((((isHolomorphic_theta 0 0 0 1).pow 4).sub ((isHolomorphic_theta 0 0 1 0).pow 4)).mul
    (((isHolomorphic_theta 0 0 0 1).pow 4).sub ((isHolomorphic_theta 0 0 1 1).pow 4))).mul
      (((isHolomorphic_theta 0 0 1 0).pow 4).sub ((isHolomorphic_theta 0 0 1 1).pow 4))

lemma isHolomorphic_f11 : IsHolomorphic f11 :=
  isHolomorphic_f6.mul isHolomorphic_chi5

lemma isHolomorphic_f2 : IsHolomorphic f2 :=
  (isHolomorphic_theta 0 0 0 0).pow 4

lemma isHolomorphic_f1 : IsHolomorphic f1 :=
  (isHolomorphic_theta 0 0 0 0).pow 2

variable (Ω : SiegelUpperHalfSpace (Fin 2)) {γ : symplecticGroup (Fin 2) ℤ}

/-- The integral lift `(v₁.val, v₂.val) ∈ {0, 1}²` of a vector `v ∈ (ℤ/2ℤ)²`. -/
private def liftChar (v : Fin 2 → ZMod 2) : Fin 2 → ℤ :=
  fun i ↦ (v i).val

private lemma liftChar_cons (a b : ZMod 2) : liftChar ![a, b] = ![(a.val : ℤ), (b.val : ℤ)] := by
  ext i
  fin_cases i <;> rfl

private lemma univ_zmod_two : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
  decide

private lemma sum_zmod_two (F : (Fin 2 → ZMod 2) → ℂ) :
    ∑ v, F v = F ![0, 0] + F ![0, 1] + F ![1, 0] + F ![1, 1] := by
  rw [← (finTwoArrowEquiv (ZMod 2)).symm.sum_comp, Fintype.sum_prod_type, univ_zmod_two,
    Finset.sum_pair zero_ne_one, Finset.sum_pair zero_ne_one, Finset.sum_pair zero_ne_one]
  simp
  ring1

private lemma prod_zmod_two (F : (Fin 2 → ZMod 2) → ℂ) :
    ∏ v, F v = F ![0, 0] * F ![0, 1] * F ![1, 0] * F ![1, 1] := by
  rw [← (finTwoArrowEquiv (ZMod 2)).symm.prod_comp, Fintype.prod_prod_type, univ_zmod_two,
    Finset.prod_pair zero_ne_one, Finset.prod_pair zero_ne_one, Finset.prod_pair zero_ne_one]
  simp
  ring1

private lemma thetaConstant_zero_eq_liftChar (w : Fin 2 → ℤ) :
    thetaConstant 0 w Ω = thetaConstant 0 (liftChar fun i ↦ (w i : ZMod 2)) Ω := by
  have h : w = liftChar (fun i ↦ (w i : ZMod 2)) + 2 • fun i ↦ w i / 2 := by
    ext i
    rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
    unfold liftChar
    rw [ZMod.val_intCast]
    omega
  conv_lhs => rw [h]
  rw [thetaConstant_add_two_smul_right, zero_dotProduct, zpow_zero, one_mul]

private lemma X_eq_sum : X Ω = (∑ v, thetaConstant 0 (liftChar v) Ω ^ 4) / 4 := by
  rw [sum_zmod_two]
  simp only [liftChar_cons, ZMod.val_one]
  simp [X, theta, ← Matrix.zero_empty]

private lemma Y_eq_prod : Y Ω = (∏ v, thetaConstant 0 (liftChar v) Ω) ^ 2 := by
  rw [prod_zmod_two]
  simp only [liftChar_cons, ZMod.val_one]
  simp [Y, theta, ← Matrix.zero_empty]

private lemma thetaConstant_zero_smul (hγ : γ ∈ SymplecticGroup.siegelParabolic (Fin 2) ℤ)
    (ν : Fin 2 → ℤ) : thetaConstant 0 ν (SymplecticGroup.map (Int.castRingHom ℝ) γ • Ω) =
      thetaConstant 0 ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₂₂ᵀ *ᵥ
        (ν + ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₁₂ *
          (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₁₁ᵀ).diag)) Ω := by
  rw [thetaConstant_smul_of_mem_siegelParabolic 0 ν Ω hγ]
  simp

private lemma thetaConstant_zero_smul_liftChar (hγ : γ ∈ SymplecticGroup.siegelParabolic (Fin 2) ℤ)
    (v : Fin 2 → ZMod 2) :
    thetaConstant 0 (liftChar v) (SymplecticGroup.map (Int.castRingHom ℝ) γ • Ω) =
      thetaConstant 0 (liftChar ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₂₂ᵀ.map
        (Int.castRingHom (ZMod 2)) *ᵥ (v + fun i ↦
          (((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₁₂ *
            (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₁₁ᵀ) i i : ZMod 2)))) Ω := by
  rw [thetaConstant_zero_smul Ω hγ, thetaConstant_zero_eq_liftChar]
  congr 2
  ext i
  rw [← eq_intCast (Int.castRingHom (ZMod 2)), RingHom.map_mulVec]
  congr 1
  ext j
  simp [liftChar]

private lemma toBlocks₁₁_mul_transpose_toBlocks₂₂
    (hγ : γ ∈ SymplecticGroup.siegelParabolic (Fin 2) ℤ) :
    (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₁₁ *
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₂₂ᵀ = 1 := by
  rw [← transpose_transpose (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₁₁,
    ← transpose_mul, toBlocks₂₂_mul_transpose_toBlocks₁₁ hγ, transpose_one]

/-- The permutation `v ↦ Dᵀ(v + diag(S))` of `(ℤ/2ℤ)²`, with `S = BAᵀ`, by which an element
`γ = (A, B; 0, D)` of the Siegel parabolic subgroup of `Sp(4, ℤ)` permutes the characteristics
`(0, v)` of the theta constants; its inverse is `w ↦ Aw - diag(S)`, since `ADᵀ = DᵀA = 1`. -/
private def charPerm (hγ : γ ∈ SymplecticGroup.siegelParabolic (Fin 2) ℤ) :
    (Fin 2 → ZMod 2) ≃ (Fin 2 → ZMod 2) where
  toFun v := (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₂₂ᵀ.map
    (Int.castRingHom (ZMod 2)) *ᵥ (v + fun i ↦
      (((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₁₂ *
        (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₁₁ᵀ) i i : ZMod 2))
  invFun w := (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₁₁.map
    (Int.castRingHom (ZMod 2)) *ᵥ w - fun i ↦
      (((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₁₂ *
        (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₁₁ᵀ) i i : ZMod 2)
  left_inv v := by
    simp only [mulVec_mulVec, ← Matrix.map_mul, toBlocks₁₁_mul_transpose_toBlocks₂₂ hγ,
      Matrix.map_one _ (map_zero _) (map_one _), one_mulVec, add_sub_cancel_right]
  right_inv w := by
    simp only [sub_add_cancel, mulVec_mulVec, ← Matrix.map_mul,
      mul_eq_one_comm.mp (toBlocks₁₁_mul_transpose_toBlocks₂₂ hγ),
      Matrix.map_one _ (map_zero _) (map_one _), one_mulVec]

private lemma charPerm_apply (hγ : γ ∈ SymplecticGroup.siegelParabolic (Fin 2) ℤ)
    (v : Fin 2 → ZMod 2) : charPerm hγ v =
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₂₂ᵀ.map (Int.castRingHom (ZMod 2)) *ᵥ
        (v + fun i ↦ (((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₁₂ *
          (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₁₁ᵀ) i i : ZMod 2)) :=
  rfl

/-- **`X` is invariant under the Siegel parabolic subgroup of `Sp(4, ℤ)`**: `γ = (A, B; 0, D)`
permutes the four theta constants `θ_{0,ν}`, `ν ∈ {0, 1}²`, whose fourth powers `X` sums. -/
lemma X_smul_of_mem_siegelParabolic (hγ : γ ∈ SymplecticGroup.siegelParabolic (Fin 2) ℤ) :
    X (SymplecticGroup.map (Int.castRingHom ℝ) γ • Ω) = X Ω := by
  rw [X_eq_sum, X_eq_sum]
  conv_rhs => rw [← (charPerm hγ).sum_comp]
  refine congrArg (· / 4) (Finset.sum_congr rfl fun v _ ↦ ?_)
  rw [thetaConstant_zero_smul_liftChar Ω hγ, charPerm_apply]

/-- **`Y` is invariant under the Siegel parabolic subgroup of `Sp(4, ℤ)`**: `γ = (A, B; 0, D)`
permutes the four theta constants `θ_{0,ν}`, `ν ∈ {0, 1}²`, whose product `Y` squares. -/
lemma Y_smul_of_mem_siegelParabolic (hγ : γ ∈ SymplecticGroup.siegelParabolic (Fin 2) ℤ) :
    Y (SymplecticGroup.map (Int.castRingHom ℝ) γ • Ω) = Y Ω := by
  rw [Y_eq_prod, Y_eq_prod]
  conv_rhs => rw [← (charPerm hγ).prod_comp]
  refine congrArg (· ^ 2) (Finset.prod_congr rfl fun v _ ↦ ?_)
  rw [thetaConstant_zero_smul_liftChar Ω hγ, charPerm_apply]

/-- The Siegel parabolic subgroup `P(ℤ) = {(A, B; 0, D)}` of `Sp(4, ℤ)`, as a subgroup of `Sp(4, ℚ)`
(`parabolic_le_gamma0`: it lies in `Γ₀(N)` for every `N`). -/
abbrev parabolic : Subgroup (symplecticGroup (Fin 2) ℚ) :=
  (SymplecticGroup.siegelParabolic (Fin 2) ℤ).map (SymplecticGroup.map (Int.castRingHom ℚ))

private lemma siegelParabolic_le_Gamma0 (N : ℕ) :
    SymplecticGroup.siegelParabolic (Fin 2) ℤ ≤ SymplecticGroup.Gamma0 (Fin 2) N := fun γ hγ ↦
  SymplecticGroup.mem_Gamma0_iff.mpr fun i j ↦ by
    rw [show (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr i) (.inl j) = 0 from
      congrFun (congrFun hγ i) j]
    exact dvd_zero _

lemma parabolic_le_gamma0 (N : ℕ) : parabolic ≤ gamma0 N :=
  Subgroup.map_mono <| siegelParabolic_le_Gamma0 N

private lemma map_algebraMap_map_intCast (γ : symplecticGroup (Fin 2) ℤ) :
    SymplecticGroup.map (algebraMap ℚ ℝ) (SymplecticGroup.map (Int.castRingHom ℚ) γ) =
      SymplecticGroup.map (Int.castRingHom ℝ) γ :=
  Subtype.ext <| by
    ext i j
    simp

private lemma det_toBlocks₂₂_eq_one_or (hγ : γ ∈ SymplecticGroup.siegelParabolic (Fin 2) ℤ) :
    (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₂₂.det = 1 ∨
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₂₂.det = -1 :=
  Int.isUnit_iff.mp <| SymplecticGroup.isUnit_det_toBlocks₂₂ ⟨γ, hγ⟩

private lemma det_denom_eq (hγ : γ ∈ SymplecticGroup.siegelParabolic (Fin 2) ℤ) :
    (denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) Ω.val).det =
      ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₂₂.det : ℂ) := by
  rw [denom_of_mem_siegelParabolic Ω hγ]
  exact ((Int.castRingHom ℂ).map_det _).symm

private lemma det_denom_sq (hγ : γ ∈ SymplecticGroup.siegelParabolic (Fin 2) ℤ) :
    (denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) Ω.val).det ^ 2 = 1 := by
  rw [det_denom_eq Ω hγ]
  rcases det_toBlocks₂₂_eq_one_or hγ with h1 | h1 <;> simp [h1]

/-- **`X` is a Siegel modular form of weight 2 on the Siegel parabolic subgroup of `Sp(4, ℤ)`**:
it is holomorphic, invariant under `P(ℤ)`, and `det(cΩ + d)² = (det D)² = 1` there. -/
lemma X_mem_parabolic : X ∈ scalarModularForms 2 parabolic := by
  rw [mem_scalarModularForms_iff]
  refine ⟨isHolomorphic_X, ?_⟩
  rintro ⟨_, γ, hγ, rfl⟩ τ
  rw [map_algebraMap_map_intCast, X_smul_of_mem_siegelParabolic τ hγ, zpow_ofNat,
    det_denom_sq τ hγ, one_mul]

/-- **`Y` is a Siegel modular form of weight 4 on the Siegel parabolic subgroup of `Sp(4, ℤ)`**:
it is holomorphic, invariant under `P(ℤ)`, and `det(cΩ + d)⁴ = (det D)⁴ = 1` there. -/
lemma Y_mem_parabolic : Y ∈ scalarModularForms 4 parabolic := by
  rw [mem_scalarModularForms_iff]
  refine ⟨isHolomorphic_Y, ?_⟩
  rintro ⟨_, γ, hγ, rfl⟩ τ
  rw [map_algebraMap_map_intCast, Y_smul_of_mem_siegelParabolic τ hγ, zpow_ofNat,
    show 4 = 2 * 2 by rfl, pow_mul, det_denom_sq τ hγ, one_pow, one_mul]

/-- For `γ = (A, B; 0, D)` in the Siegel parabolic subgroup of `Sp(4, ℤ)`, the element
`(A, 2B; 0, D)`, which acts on `2Ω` as `γ` acts on `Ω`. -/
private def twiceB (hγ : γ ∈ SymplecticGroup.siegelParabolic (Fin 2) ℤ) :
    symplecticGroup (Fin 2) ℤ :=
  ⟨fromBlocks (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₁₁
    ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₁₂ +
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₁₂) 0
        (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₂₂, by
    rw [SymplecticGroup.mem_iff, J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
    simp [toBlocks₂₂_mul_transpose_toBlocks₁₁ hγ, toBlocks₁₁_mul_transpose_toBlocks₂₂ hγ,
      Matrix.add_mul, Matrix.mul_add, toBlocks₁₂_mul_transpose_toBlocks₁₁ hγ]⟩

private lemma twiceB_mem (hγ : γ ∈ SymplecticGroup.siegelParabolic (Fin 2) ℤ) :
    twiceB hγ ∈ SymplecticGroup.siegelParabolic (Fin 2) ℤ :=
  toBlocks_fromBlocks₂₁ _ _ _ _

private lemma twiceB_smul_double (hγ : γ ∈ SymplecticGroup.siegelParabolic (Fin 2) ℤ) :
    SymplecticGroup.map (Int.castRingHom ℝ) (twiceB hγ) • double Ω =
      double (SymplecticGroup.map (Int.castRingHom ℝ) γ • Ω) := by
  have hd (Ω' : SiegelUpperHalfSpace (Fin 2)) : (double Ω').val = (2 : ℂ) • Ω'.val := rfl
  ext1
  rw [val_smul_of_mem_siegelParabolic _ (twiceB_mem hγ), hd, hd,
    val_smul_of_mem_siegelParabolic Ω hγ]
  simp only [twiceB, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.add_mul, Matrix.mul_add,
    smul_add, two_smul]
  rw [Matrix.map_add _ (map_add _)]

private lemma f1_double_smul (hγ : γ ∈ SymplecticGroup.siegelParabolic (Fin 2) ℤ) :
    f1 (double (SymplecticGroup.map (Int.castRingHom ℝ) γ • Ω)) = f1 (double Ω) := by
  have h0 : (![0, 0] : Fin 2 → ℤ) = 0 := by
    ext i
    fin_cases i <;> rfl
  rw [f1, Pi.pow_apply, Pi.pow_apply, theta, h0, ← twiceB_smul_double Ω hγ,
    thetaConstant_smul_of_mem_siegelParabolic 0 0 _ (twiceB_mem hγ)]
  simp only [twiceB, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂,
    mulVec_zero, zero_dotProduct, Int.cast_zero, zero_div, add_zero, mul_zero, neg_zero,
    Complex.exp_zero, one_mul, zero_add]
  rw [Matrix.add_mul, diag_add, mulVec_add, ← two_smul ℕ, ← zero_add (2 • _),
    thetaConstant_add_two_smul_right, zero_dotProduct, zpow_zero, one_mul]

/-- **The character `ψ₄` on the Siegel parabolic subgroup**: `ψ₄(γ) = (-4 / det D) = det D` for
`γ = (A, B; 0, D)` in the Siegel parabolic subgroup of `Sp(4, ℤ)`, where `det D = ±1`. -/
lemma psi4Rat_map_of_mem_siegelParabolic (hγ : γ ∈ SymplecticGroup.siegelParabolic (Fin 2) ℤ)
    (h : SymplecticGroup.map (Int.castRingHom ℚ) γ ∈ gamma0 4) :
    (SymplecticGroup.psi4Rat (Fin 2) ⟨SymplecticGroup.map (Int.castRingHom ℚ) γ, h⟩ : ℂ) =
      ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₂₂.det : ℂ) := by
  have hmem : γ ∈ SymplecticGroup.Gamma0 (Fin 2) 4 := siegelParabolic_le_Gamma0 4 hγ
  have e : ((SymplecticGroup.Gamma0 (Fin 2) 4).equivMapOfInjective _
      SymplecticGroup.map_intCast_injective).symm ⟨_, h⟩ = ⟨γ, hmem⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext rfl
  have h4 : ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map
      (Int.castRingHom (ZMod 4))).toBlocks₂₂.det =
      (((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₂₂.det : ℤ) : ZMod 4) := by
    rw [← eq_intCast (Int.castRingHom (ZMod 4)), RingHom.map_det]
    rfl
  have hval : ((SymplecticGroup.siegelParabolicDet.comp
      ((SymplecticGroup.map (Int.castRingHom (ZMod 4))).subgroupComap
        (SymplecticGroup.siegelParabolic (Fin 2) (ZMod 4)))
          (⟨γ, hmem⟩ : SymplecticGroup.Gamma0 (Fin 2) 4) : (ZMod 4)ˣ) : ZMod 4) =
      (((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₂₂.det : ℤ) : ZMod 4) := by
    rw [← h4]
    rfl
  have hχ : ZMod.χ₄ (-1) = -1 := by decide
  rw [SymplecticGroup.psi4Rat, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e,
    SymplecticGroup.psi4, MonoidHom.comp_apply, MonoidHom.comp_apply, Units.coe_map,
    MulChar.coe_toUnitHom]
  erw [hval]
  rcases det_toBlocks₂₂_eq_one_or hγ with h1 | h1 <;> simp [h1, hχ]

/-- **`f₁(2Ω)` is a Siegel modular form of weight 1 and character `ψ₄` on the Siegel parabolic
subgroup of `Sp(4, ℤ)`** (LMFDB `mf.siegel.family.gamma0_4_psi_4`): it is holomorphic, the element
`(A, 2B; 0, D)` sends `2Ω` to `2γΩ` and fixes `θ₀₀₀₀`, and `ψ₄(γ) det(cΩ + d) = (det D)² = 1`. -/
lemma f1_comp_double_mem_parabolic : f1 ∘ double ∈ modularForms (TauCeti.detPowerRep ℂ 2 1)
    parabolic ((SymplecticGroup.psi4Rat (Fin 2)).comp
      (Subgroup.inclusion (parabolic_le_gamma0 4))) := by
  refine ⟨isHolomorphic_f1.comp_double, ?_⟩
  rintro ⟨_, γ, hγ, rfl⟩ τ
  have hψ : (((SymplecticGroup.psi4Rat (Fin 2)).comp (Subgroup.inclusion (parabolic_le_gamma0 4)))
      ⟨SymplecticGroup.map (Int.castRingHom ℚ) γ, γ, hγ, rfl⟩ : ℂ) =
      ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).toBlocks₂₂.det : ℂ) :=
    psi4Rat_map_of_mem_siegelParabolic hγ _
  simp only [Function.comp_apply, map_algebraMap_map_intCast]
  rw [f1_double_smul τ hγ, hψ, TauCeti.detPowerRep_apply, zpow_one,
    GeneralLinearGroup.val_det_apply, coe_denomGL, det_denom_eq τ hγ, smul_eq_mul, ← mul_assoc]
  rcases det_toBlocks₂₂_eq_one_or hγ with h1 | h1 <;> simp [h1]

end SiegelUpperHalfSpace.Ibukiyama
