import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.LocalHecke
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

/-!
# The Cartan decomposition of `GL₂` over a field with a valuation subring

Let `L` be a field with a valuation subring `O`, and `K = GL₂(O)`. Every matrix of `GL₂(L)` lies in
a double coset `K diag(α, β) K`. As a diagonal matrix is its own transpose, the transpose `ᵗy` of a
matrix `y` lies in the double coset `K y K`: this is the fact behind Gelfand's trick.

## Main definitions

* `Matrix.GeneralLinearGroup.transposeGL`: the transpose, an anti-automorphism of `GL_n(R)`.

## Main results

* `ValuationSubring.exists_eq_mul_diagGL_mul`: the Cartan decomposition.
* `ValuationSubring.exists_transposeGL_eq_mul_mul`: `ᵗy ∈ K y K`.
-/

open Matrix hiding mul_inv_rev

open GeneralLinearGroup TauCeti

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The **transpose** `y ↦ ᵗy`, an anti-automorphism of `GL_n(R)`. -/
def transposeGL (y : GL n R) : GL n R where
  val := (y : Matrix n n R)ᵀ
  inv := ((y⁻¹ : GL n R) : Matrix n n R)ᵀ
  val_inv := by
    rw [← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one]
  inv_val := by
    rw [← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]

lemma transposeGL_mul (a b : GL n R) : transposeGL (a * b) = transposeGL b * transposeGL a :=
  Units.ext <| transpose_mul _ _

lemma transposeGL_transposeGL (y : GL n R) : transposeGL (transposeGL y) = y :=
  Units.ext <| transpose_transpose _

lemma transposeGL_diagGL (t : n → Rˣ) : transposeGL (diagGL t) = diagGL t :=
  Units.ext <| diagonal_transpose _

lemma transposeGL_mem_gl {O : Subring R} {k : GL n R} (hk : k ∈ O.gl n) : transposeGL k ∈ O.gl n :=
  fun i j ↦ hk j i

end Matrix.GeneralLinearGroup

namespace ValuationSubring

variable {L : Type*} [Field L] {O : ValuationSubring L} (y : GL (Fin 2) L)

lemma upperRightHom_mem_gl2 {t : L} (ht : t ∈ O) : upperRightHom t ∈ O.gl2 := by
  refine mem_gl2_of_apply_mem_of_det (fun i j ↦ ?_) ?_
  · fin_cases i <;> fin_cases j <;> simp [ht]
  · simp

variable (L) in
/-- The matrix `(0, 1; 1, 0)` of `GL₂(L)`. -/
private def swapGL : GL (Fin 2) L :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by simp [one_fin_two], by simp [one_fin_two]⟩

variable (O) in
private lemma swapGL_mem_gl2 : swapGL L ∈ O.gl2 := by
  refine mem_gl2_of_apply_mem_of_det (fun i j ↦ ?_) ?_
  · fin_cases i <;> fin_cases j <;> simp [swapGL]
  · simp [swapGL]

variable {y} in
private lemma exists_eq_mul_diagGL_mul_of_mem (h₀ : y 0 0 ≠ 0) (h₁ : (y 0 0)⁻¹ * y 0 1 ∈ O)
    (h₂ : (y 0 0)⁻¹ * y 1 0 ∈ O) :
    ∃ k₁ ∈ O.gl2, ∃ k₂ ∈ O.gl2, ∃ α β : Lˣ, y = k₁ * diagGL ![α, β] * k₂ := by
  have hd : y 1 1 - y 1 0 * ((y 0 0)⁻¹ * y 0 1) ≠ 0 := by
    intro h
    refine y.det_ne_zero ?_
    rw [det_fin_two]
    field_simp at h
    linear_combination h
  refine ⟨transposeGL (upperRightHom ((y 0 0)⁻¹ * y 1 0)),
    transposeGL_mem_gl (upperRightHom_mem_gl2 h₂), upperRightHom ((y 0 0)⁻¹ * y 0 1),
    upperRightHom_mem_gl2 h₁, Units.mk0 _ h₀, Units.mk0 _ hd, GeneralLinearGroup.ext fun i j ↦ ?_⟩
  fin_cases i <;> fin_cases j <;> simp [transposeGL, Matrix.mul_apply, h₀]
  · field_simp
  · field_simp
    ring1

variable {y} in
private lemma exists_of_mul_mul {a b : GL (Fin 2) L} (ha : a ∈ O.gl2) (hb : b ∈ O.gl2)
    (h : ∃ k₁ ∈ O.gl2, ∃ k₂ ∈ O.gl2, ∃ α β : Lˣ, a * y * b = k₁ * diagGL ![α, β] * k₂) :
    ∃ k₁ ∈ O.gl2, ∃ k₂ ∈ O.gl2, ∃ α β : Lˣ, y = k₁ * diagGL ![α, β] * k₂ := by
  rcases h with ⟨k₁, hk₁, k₂, hk₂, α, β, h⟩
  refine ⟨a⁻¹ * k₁, O.gl2.mul_mem (O.gl2.inv_mem ha) hk₁, k₂ * b⁻¹,
    O.gl2.mul_mem hk₂ (O.gl2.inv_mem hb), α, β, ?_⟩
  have he : a⁻¹ * k₁ * diagGL ![α, β] * (k₂ * b⁻¹) = a⁻¹ * (k₁ * diagGL ![α, β] * k₂) * b⁻¹ := by
    group
  rw [he, ← h]
  group

/-- **The Cartan decomposition**: every matrix `y` of `GL₂(L)` is `k₁ diag(α, β) k₂` with `k₁` and
`k₂` in `K = GL₂(O)`, for a valuation subring `O` of the field `L`. -/
lemma exists_eq_mul_diagGL_mul :
    ∃ k₁ ∈ O.gl2, ∃ k₂ ∈ O.gl2, ∃ α β : Lˣ, y = k₁ * diagGL ![α, β] * k₂ := by
  rcases Finite.exists_max (fun p : Fin 2 × Fin 2 ↦ O.valuation (y p.1 p.2)) with ⟨⟨i, j⟩, hij⟩
  have hne : y i j ≠ 0 := by
    intro h
    refine y.det_ne_zero ?_
    have h₀ (a b : Fin 2) : y a b = 0 := by
      have hab : O.valuation (y a b) ≤ O.valuation (y i j) := hij (a, b)
      simpa only [h, map_zero, le_zero_iff, map_eq_zero] using hab
    rw [det_fin_two, h₀ 0 0, h₀ 0 1]
    ring1
  have hdiv (a b : Fin 2) : (y i j)⁻¹ * y a b ∈ O := by
    rw [← O.valuation_le_one_iff, map_mul, map_inv₀]
    exact inv_mul_le_one_of_le₀ (hij (a, b)) zero_le
  have hw : swapGL L ∈ O.gl2 := swapGL_mem_gl2 O
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one] at hne hdiv
  · exact exists_eq_mul_diagGL_mul_of_mem hne (hdiv 0 1) (hdiv 1 0)
  · refine exists_of_mul_mul O.gl2.one_mem hw (exists_eq_mul_diagGL_mul_of_mem ?_ ?_ ?_)
    · simpa [swapGL, Matrix.mul_apply] using hne
    · simpa [swapGL, Matrix.mul_apply] using hdiv 0 0
    · simpa [swapGL, Matrix.mul_apply] using hdiv 1 1
  · refine exists_of_mul_mul hw O.gl2.one_mem (exists_eq_mul_diagGL_mul_of_mem ?_ ?_ ?_)
    · simpa [swapGL, Matrix.mul_apply] using hne
    · simpa [swapGL, Matrix.mul_apply] using hdiv 1 1
    · simpa [swapGL, Matrix.mul_apply] using hdiv 0 0
  · refine exists_of_mul_mul hw hw (exists_eq_mul_diagGL_mul_of_mem ?_ ?_ ?_)
    · simpa [swapGL, Matrix.mul_apply, -cons_mul] using hne
    · simpa [swapGL, Matrix.mul_apply, -cons_mul] using hdiv 1 0
    · simpa [swapGL, Matrix.mul_apply, -cons_mul] using hdiv 0 1

/-- **The transpose of a matrix `y` of `GL₂(L)` lies in `K y K`**, for `K = GL₂(O)`. -/
lemma exists_transposeGL_eq_mul_mul : ∃ k₁ ∈ O.gl2, ∃ k₂ ∈ O.gl2, transposeGL y = k₁ * y * k₂ := by
  rcases exists_eq_mul_diagGL_mul (O := O) y with ⟨k₁, hk₁, k₂, hk₂, α, β, rfl⟩
  refine ⟨transposeGL k₂ * k₁⁻¹, O.gl2.mul_mem (transposeGL_mem_gl hk₂) (O.gl2.inv_mem hk₁),
    k₂⁻¹ * transposeGL k₁, O.gl2.mul_mem (O.gl2.inv_mem hk₂) (transposeGL_mem_gl hk₁), ?_⟩
  simp only [transposeGL_mul, transposeGL_diagGL, mul_assoc, inv_mul_cancel_left,
    mul_inv_cancel_left]

lemma IsResidueSystem.exists_mul_heckeRep_none_eq {ι : Type*} {ϖ : Lˣ} {r : ι → L}
    (hr : O.IsResidueSystem ϖ r) (o : Option ι) :
    ∃ k ∈ O.gl2, ∃ w ∈ O.gl2, k * heckeRep ϖ r none = heckeRep ϖ r o * w := by
  cases o with
  | none => exact ⟨1, O.gl2.one_mem, 1, O.gl2.one_mem, by simp⟩
  | some i =>
    refine ⟨upperRightHom (r i) * swapGL L, O.gl2.mul_mem (upperRightHom_mem_gl2 (hr.mem i))
      (swapGL_mem_gl2 O), swapGL L, swapGL_mem_gl2 O, GeneralLinearGroup.ext fun a b ↦ ?_⟩
    fin_cases a <;> fin_cases b <;>
      simp [heckeRep, swapGL, Matrix.mul_apply, -cons_mul]

end ValuationSubring
