import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# The spectral theorem for the compact symplectic group

Every matrix of the compact symplectic group `USp(2g)` is conjugate, in `USp(2g)`, to a matrix
`diag(x₁, …, x_g, x₁⁻¹, …, x_g⁻¹)` of the torus. The proof is the usual one: the group commutes
with the quaternionic structure `v ↦ J v̄` of `ℂ^{2g}`, so that the eigenvectors come in pairs `v`,
`J v̄` of orthogonal eigenvectors, and we pick one pair after another.

## Main definitions

* `SatoTateGroup.IsUsp`: the matrices of `USp(2g)`, indexed by `Fin g ⊕ Fin g`.
* `SatoTateGroup.spConj`: the quaternionic structure of `ℂ^{2g}`.

## Main results

* `SatoTateGroup.IsUsp.exists_mul_eq_mul_diagonal`: the spectral theorem for `USp(2g)`.
-/

open Matrix Module

open scoped ComplexConjugate ComplexOrder

namespace SatoTateGroup

variable {g : ℕ}

/-- The matrices of the compact symplectic group `USp(2g)`, indexed by `Fin g ⊕ Fin g`. -/
structure IsUsp (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ) : Prop where
  conjTranspose_mul_self : Aᴴ * A = 1
  transpose_mul_J_mul : Aᵀ * J (Fin g) ℂ * A = J (Fin g) ℂ

/-- The **quaternionic structure** `v ↦ J v̄` of `ℂ^{2g}`. -/
def spConj (v : Fin g ⊕ Fin g → ℂ) : Fin g ⊕ Fin g → ℂ :=
  J (Fin g) ℂ *ᵥ star v

lemma conjTranspose_J : (J (Fin g) ℂ)ᴴ = -J (Fin g) ℂ := by
  rw [← J_transpose]
  ext (i | i) (j | j) <;> simp [J, one_apply]

lemma star_spConj_dotProduct (u v : Fin g ⊕ Fin g → ℂ) :
    star (spConj u) ⬝ᵥ v = -(u ⬝ᵥ J (Fin g) ℂ *ᵥ v) := by
  rw [spConj, star_mulVec, star_star, conjTranspose_J, ← dotProduct_mulVec, neg_mulVec,
    dotProduct_neg]

lemma dotProduct_J_mulVec_comm (x y : Fin g ⊕ Fin g → ℂ) :
    x ⬝ᵥ J (Fin g) ℂ *ᵥ y = -(y ⬝ᵥ J (Fin g) ℂ *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, J_transpose, neg_mulVec, neg_dotProduct,
    dotProduct_comm]

lemma dotProduct_J_mulVec_self (x : Fin g ⊕ Fin g → ℂ) : x ⬝ᵥ J (Fin g) ℂ *ᵥ x = 0 := by
  have h : x ⬝ᵥ J (Fin g) ℂ *ᵥ x = -(x ⬝ᵥ J (Fin g) ℂ *ᵥ x) := dotProduct_J_mulVec_comm x x
  exact self_eq_neg.mp h

lemma spConj_spConj (v : Fin g ⊕ Fin g → ℂ) : spConj (spConj v) = -v := by
  have h₁ : star (J (Fin g) ℂ *ᵥ star v) = J (Fin g) ℂ *ᵥ v := by
    rw [star_mulVec, star_star, conjTranspose_J, ← J_transpose, vecMul_transpose]
  rw [spConj, spConj, h₁, mulVec_mulVec, J_squared, neg_mulVec, one_mulVec]

lemma spConj_smul (c : ℂ) (v : Fin g ⊕ Fin g → ℂ) : spConj (c • v) = conj c • spConj v := by
  rw [spConj, spConj, star_smul, mulVec_smul]
  rfl

lemma star_spConj_dotProduct_spConj (u v : Fin g ⊕ Fin g → ℂ) :
    star (spConj u) ⬝ᵥ spConj v = star v ⬝ᵥ u := by
  rw [star_spConj_dotProduct, spConj, mulVec_mulVec, J_squared, neg_mulVec, one_mulVec,
    dotProduct_neg, neg_neg, dotProduct_comm]

lemma star_dotProduct_spConj_comm (u v : Fin g ⊕ Fin g → ℂ) :
    star u ⬝ᵥ spConj v = -(star v ⬝ᵥ spConj u) :=
  dotProduct_J_mulVec_comm _ _

lemma star_dotProduct_spConj_self (u : Fin g ⊕ Fin g → ℂ) : star u ⬝ᵥ spConj u = 0 :=
  dotProduct_J_mulVec_self _

/-- A family of `k` vectors of `ℂ^{2g}` which, together with their images under the quaternionic
structure, are orthonormal. -/
structure IsSpFrame {k : ℕ} (u : Fin k → Fin g ⊕ Fin g → ℂ) : Prop where
  orthonormal : ∀ i j, star (u i) ⬝ᵥ u j = if i = j then 1 else 0
  orthogonal : ∀ i j, star (u i) ⬝ᵥ spConj (u j) = 0

lemma IsSpFrame.star_spConj_dotProduct {k : ℕ} {u : Fin k → Fin g ⊕ Fin g → ℂ} (hu : IsSpFrame u)
    (i j : Fin k) : star (spConj (u i)) ⬝ᵥ u j = 0 := by
  rw [star_dotProduct, hu.orthogonal, star_zero]

/-- The matrix with columns `u` and their images under the quaternionic structure. -/
def frameMatrix (u : Fin g → Fin g ⊕ Fin g → ℂ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ :=
  of fun a b ↦ Sum.elim u (fun i ↦ spConj (u i)) b a

lemma IsSpFrame.isUsp {u : Fin g → Fin g ⊕ Fin g → ℂ} (hu : IsSpFrame u) :
    IsUsp (frameMatrix u) := by
  refine ⟨?_, ?_⟩
  · ext (i | i) (j | j)
    · exact (hu.orthonormal i j).trans (by simp [one_apply])
    · exact (hu.orthogonal i j).trans (by simp)
    · exact (hu.star_spConj_dotProduct i j).trans (by simp)
    · refine (star_spConj_dotProduct_spConj (u i) (u j)).trans ?_
      rw [hu.orthonormal]
      simp [one_apply, eq_comm]
  · have h₁ (x y : Fin g ⊕ Fin g → ℂ) (c : ℂ) (h : star (spConj x) ⬝ᵥ y = -c) :
        x ⬝ᵥ J (Fin g) ℂ *ᵥ y = c := by
      rw [SatoTateGroup.star_spConj_dotProduct, neg_inj] at h
      exact h
    have h₂ (b b' : Fin g ⊕ Fin g) : ((frameMatrix u)ᵀ * J (Fin g) ℂ * frameMatrix u) b b' =
        Sum.elim u (fun i ↦ spConj (u i)) b ⬝ᵥ
          J (Fin g) ℂ *ᵥ Sum.elim u (fun i ↦ spConj (u i)) b' := by
      rw [Matrix.mul_assoc]
      rfl
    ext (i | i) (j | j)
    · rw [h₂]
      refine h₁ _ _ _ ?_
      rw [Sum.elim_inl, Sum.elim_inl, hu.star_spConj_dotProduct]
      simp [J]
    · rw [h₂]
      refine h₁ _ _ _ ?_
      rw [Sum.elim_inl, Sum.elim_inr, star_spConj_dotProduct_spConj, hu.orthonormal]
      simp [J, one_apply, eq_comm]
    · rw [h₂]
      refine h₁ _ _ _ ?_
      rw [Sum.elim_inr, Sum.elim_inl, spConj_spConj, star_neg, neg_dotProduct, hu.orthonormal]
      simp [J, one_apply]
    · rw [h₂]
      refine h₁ _ _ _ ?_
      rw [Sum.elim_inr, Sum.elim_inr, spConj_spConj, star_neg, neg_dotProduct, hu.orthogonal]
      simp [J]

lemma exists_star_smul_dotProduct_smul_eq_one {w : Fin g ⊕ Fin g → ℂ} (hw : w ≠ 0) :
    ∃ c : ℂ, star (c • w) ⬝ᵥ (c • w) = 1 := by
  rcases Complex.nonneg_iff.mp (dotProduct_star_self_nonneg w) with ⟨h₁, h₁'⟩
  have h₂ : star w ⬝ᵥ w ≠ 0 := dotProduct_star_self_eq_zero.not.mpr hw
  have h₃ : star w ⬝ᵥ w = ((star w ⬝ᵥ w).re : ℂ) :=
    Complex.ext rfl (by simpa using h₁'.symm)
  have hr : 0 < (star w ⬝ᵥ w).re := by
    refine lt_of_le_of_ne h₁ fun h₄ ↦ h₂ ?_
    rw [h₃, ← h₄, Complex.ofReal_zero]
  refine ⟨(((√(star w ⬝ᵥ w).re)⁻¹ : ℝ) : ℂ), ?_⟩
  have h₅ : √(star w ⬝ᵥ w).re * √(star w ⬝ᵥ w).re = (star w ⬝ᵥ w).re := Real.mul_self_sqrt hr.le
  have h₆ : √(star w ⬝ᵥ w).re ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  rw [star_smul, smul_dotProduct, dotProduct_smul, h₃, Complex.ofReal_re]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
  have h₇ (s r : ℝ) (hs : s ≠ 0) (h : s * s = r) : s⁻¹ * (s⁻¹ * r) = 1 := by
    subst h
    field_simp
  exact congrArg _ (h₇ _ _ h₆ h₅)

namespace IsUsp

variable {A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ}

lemma mul_conjTranspose (hA : IsUsp A) : A * Aᴴ = 1 :=
  mul_eq_one_comm.mp hA.conjTranspose_mul_self

lemma star_mulVec_dotProduct_mulVec (hA : IsUsp A) (x y : Fin g ⊕ Fin g → ℂ) :
    star (A *ᵥ x) ⬝ᵥ A *ᵥ y = star x ⬝ᵥ y := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hA.conjTranspose_mul_self, one_mulVec]

lemma mul_J (hA : IsUsp A) : A * J (Fin g) ℂ = J (Fin g) ℂ * (Aᴴ)ᵀ := by
  have h₁ : Aᴴ * J (Fin g) ℂ * (Aᴴ)ᵀ = J (Fin g) ℂ := by
    have h₂ : (Aᵀ * J (Fin g) ℂ * A)ᴴ = (J (Fin g) ℂ)ᴴ :=
      congrArg conjTranspose hA.transpose_mul_J_mul
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_J, neg_mul, Matrix.mul_neg, neg_inj,
      ← Matrix.mul_assoc] at h₂
    exact h₂
  have h₃ : A * (Aᴴ * J (Fin g) ℂ * (Aᴴ)ᵀ) = A * J (Fin g) ℂ := by
    rw [h₁]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA.mul_conjTranspose, Matrix.one_mul] at h₃
  exact h₃.symm

lemma mulVec_spConj (hA : IsUsp A) (v : Fin g ⊕ Fin g → ℂ) : A *ᵥ spConj v = spConj (A *ᵥ v) := by
  rw [spConj, spConj, mulVec_mulVec, hA.mul_J, ← mulVec_mulVec, star_mulVec, mulVec_transpose]

lemma conj_mul_self_of_mulVec_eq (hA : IsUsp A) {u : Fin g ⊕ Fin g → ℂ} {μ : ℂ}
    (hu : star u ⬝ᵥ u = 1) (h : A *ᵥ u = μ • u) : conj μ * μ = 1 := by
  have h₁ : star (A *ᵥ u) ⬝ᵥ A *ᵥ u = star u ⬝ᵥ u := hA.star_mulVec_dotProduct_mulVec u u
  rw [h, star_smul, smul_dotProduct, dotProduct_smul, hu] at h₁
  simpa using h₁

lemma star_dotProduct_mulVec_eq_zero (hA : IsUsp A) {x w : Fin g ⊕ Fin g → ℂ} {ν : ℂ}
    (hx : A *ᵥ x = ν • x) (hν : ν ≠ 0) (hw : star x ⬝ᵥ w = 0) : star x ⬝ᵥ A *ᵥ w = 0 := by
  have h₁ : star (A *ᵥ x) ⬝ᵥ A *ᵥ w = star x ⬝ᵥ w := hA.star_mulVec_dotProduct_mulVec x w
  rw [hx, star_smul, smul_dotProduct, hw] at h₁
  exact (smul_eq_zero.mp h₁).resolve_left (star_ne_zero.mpr hν)

lemma exists_extend (hA : IsUsp A) {k : ℕ} (hk : k < g) {u : Fin k → Fin g ⊕ Fin g → ℂ}
    {μ : Fin k → ℂ} (hu : IsSpFrame u) (hμ : ∀ i, A *ᵥ u i = μ i • u i) :
    ∃ (w : Fin g ⊕ Fin g → ℂ) (ν : ℂ), star w ⬝ᵥ w = 1 ∧ A *ᵥ w = ν • w ∧
      (∀ i, star (u i) ⬝ᵥ w = 0) ∧ ∀ i, star (spConj (u i)) ⬝ᵥ w = 0 := by
  let M : Matrix (Fin k ⊕ Fin k) (Fin g ⊕ Fin g) ℂ :=
    of (Sum.elim (fun i ↦ star (u i)) fun i ↦ star (spConj (u i)))
  have hmem (w : Fin g ⊕ Fin g → ℂ) : w ∈ LinearMap.ker M.mulVecLin ↔
      (∀ i, star (u i) ⬝ᵥ w = 0) ∧ ∀ i, star (spConj (u i)) ⬝ᵥ w = 0 := by
    rw [LinearMap.mem_ker, mulVecLin_apply, funext_iff, Sum.forall]
    rfl
  have hne : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    refine LinearMap.ker_ne_bot_of_finrank_lt ?_
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hμ₀ (i : Fin k) : μ i ≠ 0 := fun h₀ ↦ by
    have h₁ : conj (μ i) * μ i = 1 := hA.conj_mul_self_of_mulVec_eq (by
      rw [hu.orthonormal, ite_eq_left rfl]) (hμ i)
    rw [h₀, mul_zero] at h₁
    exact zero_ne_one h₁
  have hstable : ∀ w ∈ LinearMap.ker M.mulVecLin, A.mulVecLin w ∈ LinearMap.ker M.mulVecLin := by
    intro w hw
    rw [hmem] at hw ⊢
    refine ⟨fun i ↦ hA.star_dotProduct_mulVec_eq_zero (hμ i) (hμ₀ i) (hw.1 i), fun i ↦ ?_⟩
    refine hA.star_dotProduct_mulVec_eq_zero (ν := conj (μ i)) ?_ ?_ (hw.2 i)
    · rw [hA.mulVec_spConj, hμ, spConj_smul]
    · exact (map_ne_zero _).mpr (hμ₀ i)
  have : Nontrivial (LinearMap.ker M.mulVecLin) := Submodule.nontrivial_iff_ne_bot.mpr hne
  rcases End.exists_eigenvalue (A.mulVecLin.restrict hstable) with ⟨ν, hν⟩
  rcases hν.exists_hasEigenvector with ⟨w, hw⟩
  have hw₁ : A *ᵥ (w : Fin g ⊕ Fin g → ℂ) = ν • (w : Fin g ⊕ Fin g → ℂ) :=
    congrArg Subtype.val hw.apply_eq_smul
  have hw₀ : (w : Fin g ⊕ Fin g → ℂ) ≠ 0 := fun h ↦ hw.2 (Subtype.ext h)
  rcases exists_star_smul_dotProduct_smul_eq_one hw₀ with ⟨c, hc⟩
  have hmem' : (∀ i, star (u i) ⬝ᵥ (w : Fin g ⊕ Fin g → ℂ) = 0) ∧
      ∀ i, star (spConj (u i)) ⬝ᵥ (w : Fin g ⊕ Fin g → ℂ) = 0 :=
    (hmem w).mp w.2
  refine ⟨c • (w : Fin g ⊕ Fin g → ℂ), ν, hc, ?_, fun i ↦ ?_, fun i ↦ ?_⟩
  · rw [mulVec_smul, hw₁, smul_comm]
  · rw [dotProduct_smul, hmem'.1 i, smul_zero]
  · rw [dotProduct_smul, hmem'.2 i, smul_zero]

lemma exists_isSpFrame (hA : IsUsp A) (k : ℕ) (hk : k ≤ g) :
    ∃ (u : Fin k → Fin g ⊕ Fin g → ℂ) (μ : Fin k → ℂ), IsSpFrame u ∧ ∀ i, A *ᵥ u i = μ i • u i := by
  induction k with
  | zero => exact ⟨Fin.elim0, Fin.elim0, ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩, fun i ↦ i.elim0⟩
  | succ k ih =>
    rcases ih (by omega) with ⟨u, μ, hu, hμ⟩
    rcases hA.exists_extend (by omega) hu hμ with ⟨w, ν, h₁, h₂, h₃, h₄⟩
    have hsnoc (i : Fin k) : (Fin.snoc u w : Fin (k + 1) → Fin g ⊕ Fin g → ℂ) i.castSucc = u i :=
      Fin.snoc_castSucc ..
    have hlast : (Fin.snoc u w : Fin (k + 1) → Fin g ⊕ Fin g → ℂ) (Fin.last k) = w :=
      Fin.snoc_last ..
    have h₅ (i : Fin k) : star w ⬝ᵥ u i = 0 := by
      rw [star_dotProduct, h₃, star_zero]
    have h₆ (i : Fin k) : star w ⬝ᵥ spConj (u i) = 0 := by
      rw [star_dotProduct, h₄, star_zero]
    have h₇ (i : Fin k) : star (u i) ⬝ᵥ spConj w = 0 := by
      rw [star_dotProduct_spConj_comm, h₆, neg_zero]
    refine ⟨Fin.snoc u w, Fin.snoc μ ν, ⟨fun i j ↦ ?_, fun i j ↦ ?_⟩, fun i ↦ ?_⟩
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rw [hlast, h₁, ite_eq_left rfl]
        | cast j => rw [hlast, hsnoc, h₅, ite_eq_right (Fin.castSucc_lt_last j).ne']
      | cast i =>
        induction j using Fin.lastCases with
        | last => rw [hlast, hsnoc, h₃, ite_eq_right (Fin.castSucc_lt_last i).ne]
        | cast j =>
          rw [hsnoc, hsnoc, hu.orthonormal]
          simp
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rw [hlast, star_dotProduct_spConj_self]
        | cast j => rw [hlast, hsnoc, h₆]
      | cast i =>
        induction j using Fin.lastCases with
        | last => rw [hlast, hsnoc, h₇]
        | cast j => rw [hsnoc, hsnoc, hu.orthogonal]
    · induction i using Fin.lastCases with
      | last => rw [hlast, Fin.snoc_last, h₂]
      | cast i => rw [hsnoc, Fin.snoc_castSucc, hμ]

/-- **The spectral theorem for `USp(2g)`**: every matrix of `USp(2g)` is conjugate in `USp(2g)` to a
matrix `diag(x₁, …, x_g, x₁⁻¹, …, x_g⁻¹)` of the torus. -/
lemma exists_mul_eq_mul_diagonal (hA : IsUsp A) :
    ∃ (P : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ) (x : Fin g → Circle), IsUsp P ∧
      A * P = P * diagonal (Sum.elim (fun i ↦ (x i : ℂ)) fun i ↦ ((x i)⁻¹ : Circle)) := by
  rcases hA.exists_isSpFrame g le_rfl with ⟨u, μ, hu, hμ⟩
  have hμ₁ (i : Fin g) : conj (μ i) * μ i = 1 := hA.conj_mul_self_of_mulVec_eq (by
    rw [hu.orthonormal, ite_eq_left rfl]) (hμ i)
  have hμ₂ (i : Fin g) : ‖μ i‖ = 1 := by
    have h₁ : ‖conj (μ i) * μ i‖ = 1 := by
      rw [hμ₁, norm_one]
    rw [norm_mul, RCLike.norm_conj] at h₁
    exact (mul_self_eq_one_iff.mp h₁).resolve_right (by
      have h₂ : 0 ≤ ‖μ i‖ := norm_nonneg (μ i)
      linarith)
  refine ⟨frameMatrix u, fun i ↦ ⟨μ i, mem_sphere_zero_iff_norm.mpr (hμ₂ i)⟩, hu.isUsp, ?_⟩
  ext a (i | i)
  · rw [mul_diagonal, Sum.elim_inl]
    have h₁ : (A * frameMatrix u) a (.inl i) = (A *ᵥ u i) a := rfl
    rw [h₁, hμ, Pi.smul_apply, smul_eq_mul, mul_comm]
    rfl
  · rw [mul_diagonal, Sum.elim_inr]
    have h₁ : (A * frameMatrix u) a (.inr i) = (A *ᵥ spConj (u i)) a := rfl
    have h₂ :
        (((⟨μ i, mem_sphere_zero_iff_norm.mpr (hμ₂ i)⟩ : Circle)⁻¹ : Circle) : ℂ) = conj (μ i) :=
      Circle.coe_inv_eq_conj _
    rw [h₁, hA.mulVec_spConj, hμ, spConj_smul, Pi.smul_apply, smul_eq_mul, mul_comm, h₂]
    rfl

end IsUsp

end SatoTateGroup
