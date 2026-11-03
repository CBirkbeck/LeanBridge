import LeanBridge.ForMathlib.NumberTheory.ModularForms.GaloisAction.Forms
import LeanBridge.ForMathlib.NumberTheory.ModularForms.GaloisAction.Holomorphic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Vandermonde
import TauCeti.NumberTheory.ModularForms.Norm.Trace

/-!
# A modular form as a polynomial in a primitive element, over level one

Let `𝒢` be a group of finite index in `SL₂(ℤ)`, and `f` and `θ` modular forms of level `𝒢`. Suppose
that the translates `θ ∣ γ`, for `γ` running over representatives of `𝒢 \ SL₂(ℤ)`, are distinct: `θ`
is a primitive element. Then Lagrange interpolation, in the form of the trace dual basis, writes
`f` as a polynomial in `θ` with coefficients in the field of fractions of the level one modular
forms: with the matrix `A = (Tr(θ^(i + j)))` and the vector `y = (Tr(f θ^i))` of traces down to
level one, Cramer's rule gives

`det(A) f = ∑ⱼ det(A with its column j replaced by y) θ^j`.

Here `det(A)` is a nonzero modular form of level one, the discriminant of `θ`.

## Main definitions

* `TauCeti.GaloisAction.traceMatrix`, `TauCeti.GaloisAction.traceVector`: the matrix of the traces
  `Tr(θ^(i + j))` and the vector of the traces `Tr(f θ^i)` down to level one.
* `TauCeti.GaloisAction.discForm`, `TauCeti.GaloisAction.cramerForm`: the level one forms `det(A)`
  and `det(A with its column j replaced by y)`.
* `TauCeti.GaloisAction.discWeight`: the weight of `det(A)`.

## Main results

* `TauCeti.GaloisAction.discForm_mul_quotientFunc`: the relation above, for all the translates of
  `f` and `θ`.
* `TauCeti.GaloisAction.discForm_ne_zero`: the discriminant of a primitive element is not zero.
-/

open UpperHalfPlane SlashInvariantForm Matrix

open scoped MatrixGroups Manifold

namespace TauCeti.GaloisAction

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} {k K w : ℤ}

local notation "𝒬" => 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ

lemma mulVec_cramer_transpose_mul {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) (φ : Fin n → ℂ) :
    V *ᵥ (Vᵀ * V).cramer (Vᵀ *ᵥ φ) = (Vᵀ * V).det • φ := by
  rw [cramer_eq_adjugate_mulVec, mulVec_mulVec, mulVec_mulVec, adjugate_mul_distrib, mul_assoc,
    mul_assoc, adjugate_mul, mul_smul_comm, mul_one, mul_smul_comm, mul_adjugate, smul_smul,
    smul_mulVec, one_mulVec, det_mul, det_transpose]

variable [𝒢.IsFiniteRelIndex 𝒮ℒ]

lemma trace_apply_eq_sum [Fintype 𝒬] {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F 𝒢 w] (g : F)
    (τ : ℍ) : ModularForm.trace 𝒮ℒ g τ = ∑ q : 𝒬, quotientFunc g q τ := by
  rw [ModularForm.coe_trace]
  simp only [Finset.sum_apply]
  congr!

variable [𝒢.HasDetOne]

variable (f : ModularForm 𝒢 k) (θ : ModularForm 𝒢 K) (τ : ℍ)
  (j : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)))
  (e : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ ≃ Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)))

/-- The matrix `(Tr(θ^(i + j)))` of the traces down to level one, for `i` and `j` below the index
of `𝒢`. -/
noncomputable def traceMatrix : Matrix (Fin (Nat.card 𝒬)) (Fin (Nat.card 𝒬)) ℂ :=
  of fun i j ↦ ModularForm.trace 𝒮ℒ (θ.pow (i + j)) τ

/-- The vector `(Tr(f θ^i))` of the traces down to level one, for `i` below the index of `𝒢`. -/
noncomputable def traceVector : Fin (Nat.card 𝒬) → ℂ :=
  fun i ↦ ModularForm.trace 𝒮ℒ (f.mul (θ.pow i)) τ

/-- The **discriminant** of a modular form `θ` of level `𝒢`: the determinant of the matrix
`(Tr(θ^(i + j)))`, a modular form of level one. -/
noncomputable def discForm : ℍ → ℂ :=
  fun z ↦ (traceMatrix θ z).det

/-- The determinant of the matrix `(Tr(θ^(i + j)))` with its column `j` replaced by `(Tr(f θ^i))`,
a modular form of level one. By Cramer's rule, the discriminant of `θ` times `f` is the sum of these
forms times `θ^j`. -/
noncomputable def cramerForm : ℍ → ℂ :=
  fun z ↦ (traceMatrix θ z).cramer (traceVector f θ z) j

variable (𝒢 K) in
/-- The weight of the discriminant of a form of weight `K` and level `𝒢`. -/
noncomputable def discWeight : ℤ :=
  ∑ i : Fin (Nat.card 𝒬), ((i : ℕ) : ℤ) * K + ∑ i : Fin (Nat.card 𝒬), ((i : ℕ) : ℤ) * K

lemma isForm_discForm : IsForm 𝒮ℒ (discWeight 𝒢 K) (discForm θ) := by
  refine IsForm.det fun i j ↦ ?_
  simp only [traceMatrix]
  rw [← add_mul]
  exact_mod_cast isForm_coe (ModularForm.trace 𝒮ℒ (θ.pow (i + j)))

lemma isForm_cramerForm : IsForm 𝒮ℒ (discWeight 𝒢 K + k - (j : ℕ) * K) (cramerForm f θ j) := by
  let c : Fin (Nat.card 𝒬) → ℤ := fun i ↦ ((i : ℕ) : ℤ) * K
  have h : IsForm 𝒮ℒ (∑ i, c i + ∑ l, Function.update c j k l)
      (fun z ↦ ((traceMatrix θ z).updateCol j (traceVector f θ z)).det) := by
    refine IsForm.det fun i l ↦ ?_
    rcases eq_or_ne l j with rfl | hl
    · simp only [updateCol_self, Function.update_self]
      rw [add_comm]
      exact isForm_coe (ModularForm.trace 𝒮ℒ (f.mul (θ.pow i)))
    · simp only [updateCol_ne hl, Function.update_of_ne hl]
      rw [← add_mul]
      exact_mod_cast isForm_coe (ModularForm.trace 𝒮ℒ (θ.pow (i + l)))
  have hs : ∑ l, Function.update c j k l + c j = ∑ l, c l + k := by
    have h₁ : ∑ l ∈ Finset.univ \ {j}, c l + ∑ l ∈ {j}, c l = ∑ l, c l :=
      Finset.sum_sdiff (Finset.subset_univ {j})
    rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
    simp only [Finset.sum_singleton] at h₁
    linarith
  have hc : cramerForm f θ j =
      fun z ↦ ((traceMatrix θ z).updateCol j (traceVector f θ z)).det :=
    funext fun z ↦ cramer_apply _ _ _
  rw [hc]
  refine h.cast ?_
  simp only [discWeight] at hs ⊢
  linarith

lemma traceMatrix_eq : traceMatrix θ τ =
    (vandermonde fun i ↦ quotientFunc θ (e.symm i) τ)ᵀ *
      vandermonde fun i ↦ quotientFunc θ (e.symm i) τ := by
  let : Fintype 𝒬 := Fintype.ofFinite _
  ext i j
  rw [vandermonde_transpose_mul_vandermonde, traceMatrix, of_apply, trace_apply_eq_sum,
    ← e.symm.sum_comp]
  exact Finset.sum_congr rfl fun x _ ↦ by rw [quotientFunc_pow]; rfl

lemma traceVector_eq : traceVector f θ τ =
    (vandermonde fun i ↦ quotientFunc θ (e.symm i) τ)ᵀ *ᵥ fun i ↦ quotientFunc f (e.symm i) τ := by
  let : Fintype 𝒬 := Fintype.ofFinite _
  ext i
  rw [traceVector, trace_apply_eq_sum, ← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [quotientFunc_mul, quotientFunc_pow, Pi.mul_apply, Pi.pow_apply]
  exact mul_comm _ _

/-- **A modular form as a polynomial in a primitive element**: the discriminant of `θ` times a
translate of `f` is the sum of the forms `cramerForm f θ j` times the powers of the same translate
of `θ`. -/
lemma discForm_mul_quotientFunc (q : 𝒬) :
    discForm θ τ * quotientFunc f q τ = ∑ j, cramerForm f θ j τ * quotientFunc θ q τ ^ (j : ℕ) := by
  let e : 𝒬 ≃ Fin (Nat.card 𝒬) := Finite.equivFin 𝒬
  have key : (vandermonde (fun i ↦ quotientFunc θ (e.symm i) τ) *ᵥ
      (traceMatrix θ τ).cramer (traceVector f θ τ)) (e q) =
        ((traceMatrix θ τ).det • fun i ↦ quotientFunc f (e.symm i) τ) (e q) := by
    rw [traceMatrix_eq θ τ e, traceVector_eq f θ τ e, mulVec_cramer_transpose_mul]
  rw [Pi.smul_apply, smul_eq_mul, e.symm_apply_apply] at key
  rw [discForm, ← key]
  simp only [mulVec, vandermonde_apply, e.symm_apply_apply, mul_comm]
  rfl

/-- **The discriminant of a primitive element is not zero**: it is the square of a Vandermonde
determinant in the translates of `θ`, which are distinct holomorphic functions, so they take
distinct values at some point. -/
lemma discForm_ne_zero (hθ : ∀ q q' : 𝒬, q ≠ q' → quotientFunc θ q ≠ quotientFunc θ q') :
    discForm θ ≠ 0 := by
  let e : 𝒬 ≃ Fin (Nat.card 𝒬) := Finite.equivFin 𝒬
  let g : {p : 𝒬 × 𝒬 // p.1 ≠ p.2} → ℍ → ℂ := fun p ↦ quotientFunc θ p.1.1 - quotientFunc θ p.1.2
  have hg : ∀ p, MDiff (g p) := fun p ↦
    (SlashInvariantForm.mdifferentiable_quotientFunc θ _).sub
      (SlashInvariantForm.mdifferentiable_quotientFunc θ _)
  rcases exists_forall_ne_zero hg (fun p ↦ sub_ne_zero.mpr (hθ _ _ p.2)) with ⟨τ, hτ⟩
  intro h
  have hτ₀ : discForm θ τ = 0 := congrFun h τ
  rw [discForm, traceMatrix_eq θ τ e, det_mul, det_transpose, mul_self_eq_zero,
    det_vandermonde_eq_zero_iff] at hτ₀
  rcases hτ₀ with ⟨i, j, hij, hne⟩
  exact hτ ⟨(e.symm i, e.symm j), e.symm.injective.ne hne⟩ (sub_eq_zero.mpr hij)

end TauCeti.GaloisAction
