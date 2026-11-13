import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.LevelTwoVectorRepresentation
import Mathlib.NumberTheory.ModularForms.Bounds

/-!
# The terms of the vector-valued Klingen–Eisenstein series of degree 2

The vector-valued Klingen–Eisenstein series of degree `2` and weight `ρ_{k,j} = det^k ⊗ Sym^j` of a
function `f` on the upper half-plane (the classical construction of Klingen in scalar weight; the
proofs here are self-contained) is
`E(f)(Z) = ∑_{δ ∈ P \ Sp(4, ℤ)} f((δZ)₀₀) ρ_{k,j}(CZ + D)⁻¹ e₁^j`, where `δ = (A, B; C, D)`, `e₁` is
the first basis vector of `ℂ²` and `P` is the Klingen parabolic subgroup, of the elements of
`Sp(4, ℤ)` whose last row is `(0, 0, 0, ±1)`. This file defines the terms and proves that they only
depend on the cosets `P δ`, for `f` of weight `k + j` on `SL(2, ℤ)` and `k` even: for
`γ = (a, 0, b, *; *, ±1, *, *; c, 0, d, *; 0, 0, 0, ±1) ∈ P`, the automorphy factor `C_γ W + D_γ` is
upper triangular with diagonal `(c W₀₀ + d, ±1)`, and `(γW)₀₀ = (a W₀₀ + b) / (c W₀₀ + d)`.

## Main definitions

* `SymplecticGroup.klingenParabolicTwo`: the Klingen parabolic subgroup `P` of `Sp(4, ℤ)`.
* `SymplecticGroup.klingenStar`: the element `(a, b; c, d)` of `SL(2, ℤ)` of an element of `P`.
* `SymplecticGroup.bottomRow`: the last row of an element of `Sp(4, ℤ)`.
* `SymplecticGroup.KlingenCosetsTwo`: the right cosets `P \ Sp(4, ℤ)`.
* `SiegelUpperHalfSpace.topLeft`: the upper-left entry `W₀₀ ∈ ℍ` of `W ∈ ℋ₂`.
* `SiegelUpperHalfSpace.vectorKlingenTerm`: the term `f((δZ)₀₀) ρ_{k,j}(CZ + D)⁻¹ e₁^j`.
* `SiegelUpperHalfSpace.klingenCosetsMul`: the right translation of the cosets by `β ∈ Sp(4, ℤ)`.

## Main results

* `SymplecticGroup.apply_inl_one_of_mem`: the second column of an element of `P` is `(0, ±1, 0, 0)`.
* `SymplecticGroup.bottomRow_out_injective`: the cosets of `P` are determined by the last row.
* `SiegelUpperHalfSpace.topLeft_smul_of_mem`: `(γW)₀₀ = γ* W₀₀` for `γ ∈ P`.
* `SiegelUpperHalfSpace.vectorKlingenTerm_mul`: the terms only depend on the cosets of `P`.
* `SiegelUpperHalfSpace.vectorKlingenTerm_smul`: `t_δ(βZ) = ρ_{k,j}(C_β Z + D_β) t_{δβ}(Z)`.
-/

open Complex Module

open Matrix hiding mul_inv_rev inv_zpow' zpow_neg one_zpow

open scoped MatrixGroups TensorProduct UpperHalfPlane

namespace SymplecticGroup

variable {γ δ : symplecticGroup (Fin 2) ℤ}

private lemma mul_apply_of_row {A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ} {v : ℤ}
    (h : ∀ x, A (.inr 1) x = if x = .inr 1 then v else 0) (x : Fin 2 ⊕ Fin 2) :
    (A * B) (.inr 1) x = v * B (.inr 1) x := by
  simp [Matrix.mul_apply, h]

/-- The **Klingen parabolic subgroup** of `Sp(4, ℤ)`: the elements whose last row, of index `f₂` in
the coordinates `(e₁, e₂, f₁, f₂)`, is `(0, 0, 0, ±1)`. Such an element is
`(a, 0, b, *; *, ±1, *, *; c, 0, d, *; 0, 0, 0, ±1)`, with `(a, b; c, d) ∈ SL(2, ℤ)`. -/
def klingenParabolicTwo : Subgroup (symplecticGroup (Fin 2) ℤ) where
  carrier := {γ | ∃ v : ℤˣ, ∀ x, γ.1 (.inr 1) x = if x = .inr 1 then (v : ℤ) else 0}
  mul_mem' {γ δ} := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩
    refine ⟨v * w, fun x ↦ ?_⟩
    rw [Submonoid.coe_mul, mul_apply_of_row hv, hw, Units.val_mul]
    split_ifs <;> simp
  one_mem' := ⟨1, fun x ↦ by simp [one_apply, eq_comm]⟩
  inv_mem' {γ} := by
    rintro ⟨v, hv⟩
    refine ⟨v⁻¹, fun x ↦ ?_⟩
    have h : (v : ℤ) * (γ⁻¹).1 (.inr 1) x = if x = .inr 1 then 1 else 0 := by
      have e : (γ * γ⁻¹).1 (.inr 1) x = (v : ℤ) * (γ⁻¹).1 (.inr 1) x := by
        rw [Submonoid.coe_mul, mul_apply_of_row hv]
      rw [← e, mul_inv_cancel]
      simp [one_apply, eq_comm]
    have hv₁ : (((v⁻¹ : ℤˣ) : ℤ)) * (v : ℤ) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e₁ : (γ⁻¹).1 (.inr 1) x = ((v⁻¹ : ℤˣ) : ℤ) * ((v : ℤ) * (γ⁻¹).1 (.inr 1) x) := by
      rw [← mul_assoc, hv₁, one_mul]
    rw [e₁, h]
    split_ifs <;> simp

/-- **The second column of an element of the Klingen parabolic subgroup is `(0, ±1, 0, 0)`**, by
the symplectic relation `γ J γᵀ = J`. -/
lemma apply_inl_one_of_mem (hγ : γ ∈ klingenParabolicTwo) {x : Fin 2 ⊕ Fin 2} (hx : x ≠ .inl 1) :
    γ.1 x (.inl 1) = 0 := by
  rcases hγ with ⟨v, hv⟩
  have h : (γ.1 * J (Fin 2) ℤ * γ.1ᵀ) x (.inr 1) = J (Fin 2) ℤ x (.inr 1) :=
    congrFun (congrFun (mem_iff.mp γ.2) x) (.inr 1)
  have e : (γ.1 * J (Fin 2) ℤ * γ.1ᵀ) x (.inr 1) = -(γ.1 x (.inl 1) * (v : ℤ)) := by
    simp [Matrix.mul_apply, J, hv]
  have h₀ : J (Fin 2) ℤ x (.inr 1) = 0 := by
    rcases x with x | x <;> fin_cases x <;> simp_all [J]
  rw [e, h₀, neg_eq_zero] at h
  exact (mul_eq_zero.mp h).resolve_right v.ne_zero

/-- The element `γ* = (a, b; c, d)` of `SL(2, ℤ)` of an element
`γ = (a, 0, b, *; *, ±1, *, *; c, 0, d, *; 0, 0, 0, ±1)` of the Klingen parabolic subgroup. -/
def klingenStar (hγ : γ ∈ klingenParabolicTwo) : SL(2, ℤ) :=
  ⟨!![γ.1 (.inl 0) (.inl 0), γ.1 (.inl 0) (.inr 0); γ.1 (.inr 0) (.inl 0),
    γ.1 (.inr 0) (.inr 0)], by
    rcases hγ with ⟨v, hv⟩
    have h : (γ.1ᵀ * J (Fin 2) ℤ * γ.1) (.inl 0) (.inr 0) = J (Fin 2) ℤ (.inl 0) (.inr 0) :=
      congrFun (congrFun (mem_iff'.mp γ.2) _) _
    simp [Matrix.mul_apply, J, hv] at h
    rw [det_fin_two_of]
    linear_combination -h⟩

variable (γ) in
/-- The last row of an element of `Sp(4, ℤ)`, which determines its coset of the Klingen parabolic
subgroup. -/
def bottomRow : Fin 2 ⊕ Fin 2 → ℤ :=
  γ.1 (.inr 1)

lemma mul_inv_mem_of_bottomRow_eq (h : bottomRow δ = bottomRow γ) :
    δ * γ⁻¹ ∈ klingenParabolicTwo := by
  refine ⟨1, fun x ↦ ?_⟩
  have e : (δ * γ⁻¹).1 (.inr 1) x = (γ * γ⁻¹).1 (.inr 1) x := by
    have e₁ (a : Fin 2 ⊕ Fin 2) : δ.1 (.inr 1) a = γ.1 (.inr 1) a :=
      congrFun h a
    simp only [Submonoid.coe_mul, Matrix.mul_apply, e₁]
  rw [e, mul_inv_cancel]
  simp [one_apply, eq_comm]

lemma mem_klingenParabolicTwo_of_row {d : ℤ}
    (h : ∀ x, δ.1 (.inr 1) x = if x = .inr 1 then d else 0) : δ ∈ klingenParabolicTwo := by
  have e : d * (δ⁻¹).1 (.inr 1) (.inr 1) = 1 := by
    have e₁ : (δ * δ⁻¹).1 (.inr 1) (.inr 1) = d * (δ⁻¹).1 (.inr 1) (.inr 1) := by
      rw [Submonoid.coe_mul, mul_apply_of_row h]
    rw [← e₁, mul_inv_cancel]
    simp
  have hd : IsUnit d := IsUnit.of_mul_eq_one _ e
  rcases hd with ⟨v, rfl⟩
  exact ⟨v, h⟩

/-- The right cosets `P γ` of the Klingen parabolic subgroup `P` of `Sp(4, ℤ)`. -/
abbrev KlingenCosetsTwo : Type :=
  Quotient (QuotientGroup.rightRel klingenParabolicTwo)

/-- **Cosets of the Klingen parabolic subgroup are determined by the last row** of a representative,
in particular they inject into `ℤ⁴`. -/
lemma bottomRow_out_injective : Function.Injective fun x : KlingenCosetsTwo ↦ bottomRow x.out := by
  intro x y h
  rw [← Quotient.out_eq x, ← Quotient.out_eq y]
  refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
  exact mul_inv_mem_of_bottomRow_eq (h : bottomRow x.out = bottomRow y.out).symm

end SymplecticGroup

namespace SiegelUpperHalfSpace

open SymplecticGroup

variable (W Z : SiegelUpperHalfSpace (Fin 2))

/-- The upper-left entry `W₀₀` of `W ∈ ℋ₂`, an element of the upper half-plane. -/
def topLeft : ℍ :=
  ⟨W.val 0 0, by simpa using W.posDef_im.diag_pos (i := 0)⟩

lemma coe_topLeft : (topLeft W : ℂ) = W.val 0 0 :=
  rfl

variable {W} {γ : symplecticGroup (Fin 2) ℤ}

private lemma denom_one_zero_of_mem (hγ : γ ∈ klingenParabolicTwo) :
    denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val 1 0 = 0 := by
  rcases hγ with ⟨v, hv⟩
  simp [denom, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, hv]

private lemma denom_one_one_of_mem {v : ℤˣ}
    (hv : ∀ x, γ.1 (.inr 1) x = if x = .inr 1 then (v : ℤ) else 0) :
    denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val 1 1 = (v : ℤ) := by
  simp [denom, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, hv]

private lemma denom_zero_zero_of_mem (hγ : γ ∈ klingenParabolicTwo) :
    denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val 0 0 =
      ((klingenStar hγ) 1 0 : ℂ) * W.val 0 0 + ((klingenStar hγ) 1 1 : ℂ) := by
  have h₁ : γ.1 (.inr 0) (.inl 1) = 0 :=
    apply_inl_one_of_mem hγ (by simp)
  simp [denom, klingenStar, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, h₁]

private lemma num_zero_zero_of_mem (hγ : γ ∈ klingenParabolicTwo) :
    num (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val 0 0 =
      ((klingenStar hγ) 0 0 : ℂ) * W.val 0 0 + ((klingenStar hγ) 0 1 : ℂ) := by
  have h₁ : γ.1 (.inl 0) (.inl 1) = 0 :=
    apply_inl_one_of_mem hγ (by simp)
  simp [num, klingenStar, toBlocks₁₁, toBlocks₁₂, Matrix.mul_apply, h₁]

private lemma det_denom_of_mem {v : ℤˣ} (hγ : γ ∈ klingenParabolicTwo)
    (hv : ∀ x, γ.1 (.inr 1) x = if x = .inr 1 then (v : ℤ) else 0) :
    (denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val).det =
      denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val 0 0 * (v : ℤ) := by
  rw [det_fin_two, denom_one_zero_of_mem hγ, denom_one_one_of_mem hv, mul_zero, sub_zero]

private lemma denom_zero_zero_ne_zero (hγ : γ ∈ klingenParabolicTwo) :
    denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val 0 0 ≠ 0 := by
  rcases id hγ with ⟨v, hv⟩
  intro h
  have h₁ : (denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val).det ≠ 0 :=
    (isUnit_det_denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W).ne_zero
  rw [det_denom_of_mem hγ hv, h, zero_mul] at h₁
  exact h₁ rfl

/-- **The action of the Klingen parabolic subgroup on the upper-left entry**: for `γ` in the Klingen
parabolic subgroup, `(γW)₀₀ = γ* W₀₀`. -/
lemma topLeft_smul_of_mem (hγ : γ ∈ klingenParabolicTwo) :
    topLeft (SymplecticGroup.map (Int.castRingHom ℝ) γ • W) = klingenStar hγ • topLeft W := by
  have hW : (SymplecticGroup.map (Int.castRingHom ℝ) γ • W).val *
      denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val =
        num (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val := by
    rw [val_smul, nonsing_inv_mul_cancel_right _ _ (isUnit_det_denom _ W)]
  have h₀₀ : ((SymplecticGroup.map (Int.castRingHom ℝ) γ • W).val *
      denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val) 0 0 =
        num (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val 0 0 :=
    congrFun (congrFun hW 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_two, denom_one_zero_of_mem hγ, mul_zero, add_zero,
    num_zero_zero_of_mem hγ] at h₀₀
  have hne : denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val 0 0 ≠ 0 :=
    denom_zero_zero_ne_zero hγ
  rw [denom_zero_zero_of_mem hγ] at hne h₀₀
  refine UpperHalfPlane.ext ?_
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, coe_topLeft, coe_topLeft]
  simp only [eq_intCast, ofReal_intCast]
  rw [eq_div_iff hne, h₀₀]

variable (k : ℤ) (j : ℕ)

lemma rhoKJ_tprod (g : GL (Fin 2) ℂ) (u : Fin j → Fin 2 → ℂ) : rhoKJ k j g (⨂ₛ[ℂ] i, u i) =
    ((g.det ^ k : ℂˣ) : ℂ) • ⨂ₛ[ℂ] i, (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ u i :=
  congrArg (((g.det ^ k : ℂˣ) : ℂ) • ·) (symPowerRep_tprod g u)

lemma tprod_smul (c : ℂ) (u : Fin 2 → ℂ) :
    (⨂ₛ[ℂ] _ : Fin j, c • u) = c ^ j • ⨂ₛ[ℂ] _ : Fin j, u := by
  have e : (SymmetricPower.tprod ℂ fun i : Fin j ↦ c • u) =
      (∏ _ : Fin j, c) • SymmetricPower.tprod ℂ fun _ : Fin j ↦ u :=
    (SymmetricPower.tprod ℂ).map_smul_univ (fun _ : Fin j ↦ c) (fun _ ↦ u)
  simpa using e

lemma rhoKJ_denomGL_inv_tprod (g : symplecticGroup (Fin 2) ℝ) (u : Fin 2 → ℂ) :
    rhoKJ k j (denomGL g Z)⁻¹ (⨂ₛ[ℂ] _ : Fin j, u) = (denom g Z.val).det ^ (-k) •
      ⨂ₛ[ℂ] _ : Fin j, (denom g Z.val)⁻¹ *ᵥ u := by
  rw [rhoKJ_tprod, map_inv, inv_zpow', Units.val_zpow_eq_zpow_val, GeneralLinearGroup.val_det_apply,
    coe_units_inv, coe_denomGL]

variable (f : ℍ → ℂ) (δ : symplecticGroup (Fin 2) ℤ)

/-- The term `f((δZ)₀₀) ρ_{k,j}(CZ + D)⁻¹ e₁^j` of the vector-valued Klingen–Eisenstein series of
`f : ℍ → ℂ`, for `δ = (A, B; C, D) ∈ Sp(4, ℤ)`, with values in `Sym^j(ℂ²)`, where `e₁` is the first
basis vector of `ℂ²`. -/
noncomputable def vectorKlingenTerm : Sym[ℂ]^j (Fin 2 → ℂ) :=
  f (topLeft (SymplecticGroup.map (Int.castRingHom ℝ) δ • Z)) •
    rhoKJ k j (denomGL (SymplecticGroup.map (Int.castRingHom ℝ) δ) Z)⁻¹
      (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1)

private lemma inv_mulVec_single_of_mem (hγ : γ ∈ klingenParabolicTwo) :
    (denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val)⁻¹ *ᵥ (Pi.single 0 1 : Fin 2 → ℂ) =
      (denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val 0 0)⁻¹ • Pi.single 0 1 := by
  have h₀ : denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val 0 0 ≠ 0 :=
    denom_zero_zero_ne_zero hγ
  have hM : denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val *ᵥ
      ((denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val 0 0)⁻¹ • Pi.single 0 1) =
        (Pi.single 0 1 : Fin 2 → ℂ) := by
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, denom_one_zero_of_mem hγ, h₀]
  rw [← hM, mulVec_mulVec, nonsing_inv_mul _ (isUnit_det_denom _ W), one_mulVec, hM]

variable {f k j δ}

lemma rhoKJ_denomGL_inv_of_mem (hk : Even k) (hγ : γ ∈ klingenParabolicTwo) :
    rhoKJ k j (denomGL (SymplecticGroup.map (Int.castRingHom ℝ) γ) W)⁻¹
      (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1) =
    (denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val 0 0) ^ (-(k + j)) •
      ⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1 := by
  rcases id hγ with ⟨v, hv⟩
  have h₀ : denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) W.val 0 0 ≠ 0 :=
    denom_zero_zero_ne_zero hγ
  have hv₁ : ((v : ℤ) : ℂ) ^ (-k) = 1 := by
    rcases Int.units_eq_one_or v with rfl | rfl <;> simp [hk.neg.neg_one_zpow]
  rw [rhoKJ_denomGL_inv_tprod, inv_mulVec_single_of_mem hγ, tprod_smul, smul_smul,
    det_denom_of_mem hγ hv, mul_zpow, hv₁, mul_one, zpow_neg, zpow_neg, zpow_add₀ h₀, zpow_natCast,
    mul_inv, inv_pow]

/-- **The terms of the Klingen–Eisenstein series only depend on the coset `P δ`** of the Klingen
parabolic subgroup `P`, for `f` of weight `k + j` on `SL(2, ℤ)` and `k` even: for `γ ∈ P` with
`γ* = (a, b; c, d)` and `W = δZ`, `f((γW)₀₀) = (c W₀₀ + d)^(k + j) f(W₀₀)` and
`ρ_{k,j}(C_γ W + D_γ)⁻¹ e₁^j = (c W₀₀ + d)^(-k - j) e₁^j`. -/
lemma vectorKlingenTerm_mul (hk : Even k)
    (hf : ∀ (g : SL(2, ℤ)) (w : ℍ), f (g • w) = ((g 1 0 : ℂ) * w + (g 1 1 : ℂ)) ^ (k + j) * f w)
    (hγ : γ ∈ klingenParabolicTwo) :
    vectorKlingenTerm Z k j f (γ * δ) = vectorKlingenTerm Z k j f δ := by
  have h₀ : denom (SymplecticGroup.map (Int.castRingHom ℝ) γ)
      (SymplecticGroup.map (Int.castRingHom ℝ) δ • Z).val 0 0 ≠ 0 :=
    denom_zero_zero_ne_zero hγ
  rw [vectorKlingenTerm, vectorKlingenTerm, map_mul, mul_smul, denomGL_mul, mul_inv_rev, map_mul,
    End.mul_apply, rhoKJ_denomGL_inv_of_mem hk hγ, map_smul, smul_smul, topLeft_smul_of_mem hγ, hf]
  congr 1
  rw [coe_topLeft, ← denom_zero_zero_of_mem hγ, mul_right_comm, ← zpow_add₀ h₀, add_neg_cancel,
    zpow_zero, one_mul]

lemma vectorKlingenTerm_out (hk : Even k)
    (hf : ∀ (g : SL(2, ℤ)) (w : ℍ), f (g • w) = ((g 1 0 : ℂ) * w + (g 1 1 : ℂ)) ^ (k + j) * f w) :
    vectorKlingenTerm Z k j f (⟦δ⟧ : KlingenCosetsTwo).out = vectorKlingenTerm Z k j f δ := by
  have h : δ * (⟦δ⟧ : KlingenCosetsTwo).out⁻¹ ∈ klingenParabolicTwo :=
    QuotientGroup.rightRel_apply.mp (Quotient.mk_out δ)
  conv_rhs => rw [← inv_mul_cancel_right δ (⟦δ⟧ : KlingenCosetsTwo).out]
  exact (vectorKlingenTerm_mul Z hk hf h).symm

variable (k j f) in
/-- **The terms of the Klingen–Eisenstein series under `β ∈ Sp(4, ℤ)`**:
`t_δ(βZ) = ρ_{k,j}(C_β Z + D_β) t_{δβ}(Z)`, by the cocycle relation of the automorphy factor. -/
lemma vectorKlingenTerm_smul (β : symplecticGroup (Fin 2) ℤ) :
    vectorKlingenTerm (SymplecticGroup.map (Int.castRingHom ℝ) β • Z) k j f δ =
      rhoKJ k j (denomGL (SymplecticGroup.map (Int.castRingHom ℝ) β) Z)
        (vectorKlingenTerm Z k j f (δ * β)) := by
  rw [vectorKlingenTerm, vectorKlingenTerm, map_mul, mul_smul, denomGL_mul, mul_inv_rev, map_smul,
    ← End.mul_apply, ← map_mul, mul_inv_cancel_left]

/-- The right translation `P δ ↦ P δ β` of the cosets of the Klingen parabolic subgroup. -/
noncomputable def klingenCosetsMul (β : symplecticGroup (Fin 2) ℤ) :
    Equiv.Perm KlingenCosetsTwo :=
  Quotient.congr (Equiv.mulRight β) fun a b ↦ by
    simp [QuotientGroup.rightRel_apply]

lemma vectorKlingenTerm_out_mul (hk : Even k)
    (hf : ∀ (g : SL(2, ℤ)) (w : ℍ), f (g • w) = ((g 1 0 : ℂ) * w + (g 1 1 : ℂ)) ^ (k + j) * f w)
    (β : symplecticGroup (Fin 2) ℤ) (x : KlingenCosetsTwo) : vectorKlingenTerm Z k j f (x.out * β) =
    vectorKlingenTerm Z k j f (klingenCosetsMul β x).out := by
  have e : klingenCosetsMul β x = ⟦x.out * β⟧ := by
    conv_lhs => rw [← Quotient.out_eq x]
    rfl
  rw [e, vectorKlingenTerm_out Z hk hf]

variable (k j f) in
lemma vectorKlingenTerm_one :
    vectorKlingenTerm Z k j f 1 = f (topLeft Z) • ⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1 := by
  rw [vectorKlingenTerm, map_one, one_smul, denomGL_one, inv_one, map_one, End.one_apply]

end SiegelUpperHalfSpace
