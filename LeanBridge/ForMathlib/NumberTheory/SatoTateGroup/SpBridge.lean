import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.SpTensor
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.UspDiagonal
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Lagrange

/-!
# Subspaces of the tensor powers stable under `USp(2g)` and under `𝔰𝔭(2g, ℂ)`

A subspace of a tensor power of the standard module is stable under the compact group `USp(2g)` if
and only if it is stable under the Lie algebra `𝔰𝔭(2g, ℂ)`.

* If it is stable under the Lie algebra, write a matrix `A` of `USp(2g)` as `C D C⁻¹`, with
  `D = exp Λ` diagonal by the spectral theorem. On the tensor power, `A^{⊗P}` is a polynomial in the
  action of `X = C Λ C⁻¹`, the polynomial interpolating `exp` on the eigenvalues of this action.
* If it is stable under the group, then the derivative at `0` of `t ↦ exp(tX)^{⊗P}` preserves it,
  for `X` in the Lie algebra of `USp(2g)`, and this derivative is the action of `X`. The Lie algebra
  `𝔰𝔭(2g, ℂ)` is the complexification of the Lie algebra of `USp(2g)`.

## Main results

* `SatoTateGroup.IsUsp.tensorRep_mulVec_mem`: stability under the Lie algebra implies stability
  under the group.
* `SatoTateGroup.tensorAction_mulVec_mem_of_mem_sp`: stability under the group implies stability
  under the Lie algebra.
-/

open LieAlgebra Matrix Module NormedSpace Polynomial

attribute [local instance 100] LieRing.ofAssociativeRing

namespace SatoTateGroup

section Polynomial

variable {J : Type*} [Fintype J] [DecidableEq J]

lemma aeval_mul_mul {C C' : Matrix J J ℂ} (h : C * C' = 1) (h' : C' * C = 1) (B : Matrix J J ℂ)
    (q : ℂ[X]) : aeval (C * B * C') q = C * aeval B q * C' := by
  have h₁ (n : ℕ) : (C * B * C') ^ n = C * B ^ n * C' := by
    induction n with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, h]
    | succ n ih =>
      have h₂ : C * B ^ n * C' * (C * B * C') = C * (B ^ n * (C' * C) * B) * C' := by
        simp only [Matrix.mul_assoc]
      rw [pow_succ, ih, h₂, h', Matrix.mul_one, pow_succ]
  induction q using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add, map_add, hp, hr, Matrix.mul_add, Matrix.add_mul]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, h₁, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      Matrix.one_mul, smul_mul_assoc, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul]

lemma aeval_diagonal (z : J → ℂ) (q : ℂ[X]) :
    aeval (diagonal z) q = diagonal fun a ↦ q.eval (z a) := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
    rw [map_add, hp, hr, diagonal_add]
    simp only [eval_add]
  | monomial n c =>
    rw [aeval_monomial, diagonal_pow, Matrix.algebraMap_eq_diagonal, diagonal_mul_diagonal]
    simp

lemma aeval_mulVec_mem (U : Submodule ℂ (J → ℂ)) {B : Matrix J J ℂ} (hB : ∀ f ∈ U, B *ᵥ f ∈ U)
    (q : ℂ[X]) {f : J → ℂ} (hf : f ∈ U) : aeval B q *ᵥ f ∈ U := by
  have h₁ (n : ℕ) {f : J → ℂ} (hf : f ∈ U) : (B ^ n) *ᵥ f ∈ U := by
    induction n with
    | zero => rwa [pow_zero, one_mulVec]
    | succ n ih =>
      rw [pow_succ', ← mulVec_mulVec]
      exact hB _ ih
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
    rw [map_add, add_mulVec]
    exact U.add_mem hp hr
  | monomial n c =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_mul, smul_mulVec]
    exact U.smul_mem _ (h₁ n hf)

variable {P I : Type*} [Fintype P] [DecidableEq P] [Fintype I] [DecidableEq I]

lemma exists_tensorRep_eq_aeval {C C' : Matrix I I ℂ} (h : C * C' = 1) (h' : C' * C = 1)
    (z : I → ℂ) : ∃ q : ℂ[X], tensorRep (P := P) (C * diagonal (fun i ↦ Complex.exp (z i)) * C') =
      aeval (tensorAction (C * diagonal z * C')) q := by
  classical
  let w : (P → I) → ℂ := fun a ↦ ∑ p, z (a p)
  let q : ℂ[X] := Lagrange.interpolate (Finset.univ.image w) id Complex.exp
  have hq (a : P → I) : q.eval (w a) = Complex.exp (w a) :=
    Lagrange.eval_interpolate_at_node _ Function.injective_id.injOn
      (Finset.mem_image_of_mem w (Finset.mem_univ a))
  refine ⟨q, ?_⟩
  have h₁ : tensorRep (P := P) C * tensorRep C' = 1 := by
    rw [← tensorRep_mul, h, tensorRep_one]
  have h₂ : tensorRep (P := P) C' * tensorRep C = 1 := by
    rw [← tensorRep_mul, h', tensorRep_one]
  have h₃ : (fun a ↦ ∏ p, Complex.exp (z (a p))) = fun a : P → I ↦ eval (∑ p, z (a p)) q := by
    funext a
    rw [← Complex.exp_sum]
    exact (hq a).symm
  rw [← tensorRep_mul_tensorAction_mul _ h, aeval_mul_mul h₁ h₂, tensorAction_diagonal,
    aeval_diagonal, tensorRep_mul, tensorRep_mul, tensorRep_diagonal, h₃]

end Polynomial

variable {g : ℕ} {P : Type*} [Fintype P] [DecidableEq P]

lemma IsUsp.conj_mem_sp {C Y : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ} (hC : IsUsp C)
    (hY : Y ∈ Symplectic.sp (Fin g) ℂ) : C * Y * Cᴴ ∈ Symplectic.sp (Fin g) ℂ := by
  rw [Symplectic.mem_sp] at hY ⊢
  have h₁ : Cᵀ * J (Fin g) ℂ = J (Fin g) ℂ * Cᴴ := by
    rw [← Matrix.mul_one (Cᵀ * J (Fin g) ℂ), ← hC.mul_conjTranspose, ← Matrix.mul_assoc,
      hC.transpose_mul_J_mul]
  have h₂ : (Cᴴ)ᵀ * J (Fin g) ℂ = J (Fin g) ℂ * C := by
    have h₃ : (Cᴴ)ᵀ * Cᵀ = 1 := by
      rw [← transpose_mul, hC.mul_conjTranspose, transpose_one]
    have h₄ : (Cᴴ)ᵀ * (Cᵀ * J (Fin g) ℂ * C) = J (Fin g) ℂ * C := by
      rw [Matrix.mul_assoc Cᵀ, ← Matrix.mul_assoc (Cᴴ)ᵀ, h₃, Matrix.one_mul]
    rwa [hC.transpose_mul_J_mul] at h₄
  have h₅ : (Cᴴ)ᵀ * (Yᵀ * Cᵀ) * J (Fin g) ℂ = (Cᴴ)ᵀ * ((Yᵀ * J (Fin g) ℂ) * Cᴴ) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc Yᵀ, h₁]
    simp only [Matrix.mul_assoc]
  have h₆ : (Cᴴ)ᵀ * ((J (Fin g) ℂ * Y) * Cᴴ) = ((Cᴴ)ᵀ * J (Fin g) ℂ) * (Y * Cᴴ) := by
    simp only [Matrix.mul_assoc]
  rw [transpose_mul, transpose_mul, h₅, hY, neg_mul, Matrix.mul_neg, h₆, h₂]
  simp only [Matrix.mul_assoc]

/-- **Stability under the Lie algebra implies stability under the group.** -/
lemma IsUsp.tensorRep_mulVec_mem {A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ} (hA : IsUsp A)
    (U : Submodule ℂ ((P → Fin g ⊕ Fin g) → ℂ))
    (hU : ∀ X ∈ Symplectic.sp (Fin g) ℂ, ∀ f ∈ U, tensorAction X *ᵥ f ∈ U)
    {f : (P → Fin g ⊕ Fin g) → ℂ} (hf : f ∈ U) : tensorRep A *ᵥ f ∈ U := by
  rcases hA.exists_mul_eq_mul_diagonal with ⟨C, x, hC, hAC⟩
  let θ : Fin g → ℂ := fun i ↦ Complex.log (x i)
  have hθ (i : Fin g) : Complex.exp (θ i) = x i :=
    Complex.exp_log (Circle.coe_ne_zero _)
  have h₁ : (Sum.elim (fun i ↦ (x i : ℂ)) fun i ↦ ((x i)⁻¹ : Circle)) =
      fun a ↦ Complex.exp (spValue θ a) := by
    funext a
    rcases a with i | i
    · exact (hθ i).symm
    · rw [Sum.elim_inr, spValue_inr, Complex.exp_neg, hθ, Circle.coe_inv]
  have h₂ : A = C * diagonal (fun a ↦ Complex.exp (spValue θ a)) * Cᴴ := by
    rw [← h₁, ← hAC, Matrix.mul_assoc, hC.mul_conjTranspose, Matrix.mul_one]
  rcases exists_tensorRep_eq_aeval (P := P) hC.mul_conjTranspose hC.conjTranspose_mul_self
    (spValue θ) with ⟨q, hq⟩
  rw [h₂, hq]
  exact aeval_mulVec_mem U (hU _ (hC.conj_mem_sp (diagonal_spValue_mem θ))) q hf

lemma isUsp_exp_of_mem_sp {X : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ}
    (hX : X ∈ Symplectic.sp (Fin g) ℂ) (hX' : Xᴴ = -X) : IsUsp (exp X) := by
  have h₁ : exp (-X) * exp X = 1 := by
    rw [Matrix.exp_neg,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp X))]
  refine ⟨?_, ?_⟩
  · rw [← Matrix.exp_conjTranspose, hX', h₁]
  · have hJ : IsUnit (J (Fin g) ℂ) := by
      refine (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_J (Fin g) ℂ)
    have h₂ : Xᵀ = J (Fin g) ℂ * -X * (J (Fin g) ℂ)⁻¹ :=
      (Symplectic.mem_sp_iff_transpose_eq_J_conj_neg X).mp hX
    have h₃ : J (Fin g) ℂ * exp (-X) * (J (Fin g) ℂ)⁻¹ * J (Fin g) ℂ * exp X =
        J (Fin g) ℂ * exp (-X) * ((J (Fin g) ℂ)⁻¹ * J (Fin g) ℂ) * exp X := by
      simp only [Matrix.mul_assoc]
    rw [← Matrix.exp_transpose, h₂, Matrix.exp_conj _ _ hJ, h₃,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hJ), Matrix.mul_one,
      Matrix.mul_assoc, h₁, Matrix.mul_one]

section Derivative

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma hasDerivAt_exp_smul_apply (X : Matrix I I ℂ) (a b : I) :
    HasDerivAt (fun t : ℂ ↦ exp (t • X) a b) (X a b) 0 := by
  let : NormedRing (Matrix I I ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ (Matrix I I ℂ) := Matrix.linftyOpNormedAlgebra
  have h₁ : HasDerivAt (fun t : ℂ ↦ exp (t • X)) (exp ((0 : ℂ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℂ) X 0
  rw [zero_smul, exp_zero, one_mul] at h₁
  let L : Matrix I I ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (entryLinearMap ℂ ℂ a b)
  exact L.hasFDerivAt.comp_hasDerivAt 0 h₁

lemma hasDerivAt_tensorRep_exp_apply (X : Matrix I I ℂ) (a b : P → I) :
    HasDerivAt (fun t : ℂ ↦ tensorRep (P := P) (exp (t • X)) a b) (tensorAction X a b) 0 := by
  have h₁ : HasDerivAt (fun t : ℂ ↦ ∏ p, exp (t • X) (a p) (b p))
      (∑ i, (∏ j ∈ Finset.univ.erase i, exp ((0 : ℂ) • X) (a j) (b j)) • X (a i) (b i)) 0 :=
    HasDerivAt.fun_finsetProd fun p _ ↦ hasDerivAt_exp_smul_apply X (a p) (b p)
  have h₂ : ∑ i, (∏ j ∈ Finset.univ.erase i, exp ((0 : ℂ) • X) (a j) (b j)) • X (a i) (b i) =
      tensorAction X a b := by
    rw [tensorAction, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [kroneckerFamily_oneAt_apply, zero_smul, exp_zero, smul_eq_mul, mul_comm]
  rw [h₂] at h₁
  exact h₁

lemma hasDerivAt_tensorRep_exp_mulVec (X : Matrix I I ℂ) (f : (P → I) → ℂ)
    (φ : Dual ℂ ((P → I) → ℂ)) : HasDerivAt
      (fun t : ℂ ↦ φ (tensorRep (P := P) (exp (t • X)) *ᵥ f)) (φ (tensorAction X *ᵥ f)) 0 := by
  let c : (P → I) → ℂ := fun a ↦ φ fun b ↦ if a = b then 1 else 0
  have hc (h : (P → I) → ℂ) : φ h = ∑ a, h a * c a := by
    rw [LinearMap.pi_apply_eq_sum_univ φ]
    rfl
  simp only [hc]
  refine HasDerivAt.fun_sum fun a _ ↦ HasDerivAt.mul_const ?_ _
  simp only [mulVec]
  exact HasDerivAt.fun_sum fun b _ ↦ (hasDerivAt_tensorRep_exp_apply X a b).mul_const _

end Derivative

lemma tensorAction_mulVec_mem_of_skew (U : Submodule ℂ ((P → Fin g ⊕ Fin g) → ℂ))
    (hU : ∀ A, IsUsp A → ∀ f ∈ U, tensorRep A *ᵥ f ∈ U)
    {X : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ} (hX : X ∈ Symplectic.sp (Fin g) ℂ)
    (hX' : Xᴴ = -X) {f : (P → Fin g ⊕ Fin g) → ℂ} (hf : f ∈ U) : tensorAction X *ᵥ f ∈ U := by
  by_contra hnot
  rcases Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance with ⟨φ, hφ₁, hφ₂⟩
  have h₁ (t : ℝ) : φ (tensorRep (exp ((t : ℂ) • X)) *ᵥ f) = 0 := by
    have hmem : ((t : ℂ) • X) ∈ Symplectic.sp (Fin g) ℂ :=
      (Symplectic.sp (Fin g) ℂ).smul_mem _ hX
    have hskew : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
      rw [conjTranspose_smul, hX', Complex.star_def, Complex.conj_ofReal, smul_neg]
    have h₂ : tensorRep (exp ((t : ℂ) • X)) *ᵥ f ∈ U := hU _ (isUsp_exp_of_mem_sp hmem hskew) f hf
    have h₃ : φ (tensorRep (exp ((t : ℂ) • X)) *ᵥ f) ∈ U.map φ :=
      Submodule.mem_map_of_mem h₂
    rw [hφ₂] at h₃
    exact h₃
  have h₂ :
      HasDerivAt (fun t : ℝ ↦ φ (tensorRep (exp ((t : ℂ) • X)) *ᵥ f)) (φ (tensorAction X *ᵥ f)) 0 :=
    (hasDerivAt_tensorRep_exp_mulVec X f φ).comp_ofReal
  have h₃ : HasDerivAt (fun t : ℝ ↦ φ (tensorRep (exp ((t : ℂ) • X)) *ᵥ f)) (0 : ℂ) 0 := by
    simp only [h₁]
    exact hasDerivAt_const _ _
  exact hφ₁ (h₂.unique h₃)

lemma conjTranspose_mem_sp {X : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ}
    (hX : X ∈ Symplectic.sp (Fin g) ℂ) : Xᴴ ∈ Symplectic.sp (Fin g) ℂ := by
  rw [Symplectic.mem_sp_iff_mul_J_add_J_mul_transpose_eq_zero]
  have h₁ : (Xᵀ * J (Fin g) ℂ)ᴴ = (-(J (Fin g) ℂ * X))ᴴ :=
    congrArg conjTranspose ((Symplectic.mem_sp _).mp hX)
  rw [conjTranspose_mul, conjTranspose_J, conjTranspose_neg, conjTranspose_mul, conjTranspose_J,
    neg_mul, Matrix.mul_neg, neg_inj] at h₁
  have h₂ : (Xᵀ)ᴴ = (Xᴴ)ᵀ := Matrix.ext fun _ _ ↦ rfl
  rw [h₂] at h₁
  rw [h₁, add_neg_cancel]

/-- **Stability under the group implies stability under the Lie algebra.** -/
lemma tensorAction_mulVec_mem_of_mem_sp (U : Submodule ℂ ((P → Fin g ⊕ Fin g) → ℂ))
    (hU : ∀ A, IsUsp A → ∀ f ∈ U, tensorRep A *ᵥ f ∈ U)
    {X : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ} (hX : X ∈ Symplectic.sp (Fin g) ℂ)
    {f : (P → Fin g ⊕ Fin g) → ℂ} (hf : f ∈ U) : tensorAction X *ᵥ f ∈ U := by
  have hX₁ : Xᴴ ∈ Symplectic.sp (Fin g) ℂ := conjTranspose_mem_sp hX
  have key (A B : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ)
      (hA : A ∈ Symplectic.sp (Fin g) ℂ) (hA' : Aᴴ = -A)
      (hB : B ∈ Symplectic.sp (Fin g) ℂ) (hB' : Bᴴ = -B)
      (h : X = A + (-Complex.I) • B) : tensorAction X *ᵥ f ∈ U := by
    rw [h, tensorAction_add_mulVec, tensorAction_smul_mulVec]
    exact U.add_mem (tensorAction_mulVec_mem_of_skew U hU hA hA' hf)
      (U.smul_mem _ (tensorAction_mulVec_mem_of_skew U hU hB hB' hf))
  refine key ((2⁻¹ : ℂ) • (X - Xᴴ)) ((2⁻¹ * Complex.I : ℂ) • (X + Xᴴ))
    ((Symplectic.sp (Fin g) ℂ).smul_mem _
      ((Symplectic.sp (Fin g) ℂ).sub_mem hX hX₁)) ?_
    ((Symplectic.sp (Fin g) ℂ).smul_mem _
      ((Symplectic.sp (Fin g) ℂ).add_mem hX hX₁)) ?_ ?_
  · have h₁ : star (2⁻¹ : ℂ) = 2⁻¹ := by
      simp
    simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, h₁]
    rw [← smul_neg, neg_sub]
  · have h₁ : star (2⁻¹ * Complex.I : ℂ) = -(2⁻¹ * Complex.I) := by
      simp
    simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, h₁]
    rw [add_comm, neg_smul]
  · have h₂ : -Complex.I * (2⁻¹ * Complex.I) = 2⁻¹ := by
      linear_combination (-2⁻¹ : ℂ) * Complex.I_mul_I
    rw [smul_smul, h₂, ← smul_add, sub_add_add_cancel, ← two_smul ℂ X, smul_smul,
      inv_mul_cancel₀ two_ne_zero, one_smul]

end SatoTateGroup
