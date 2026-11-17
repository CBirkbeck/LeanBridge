import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Trace

/-!
# The symmetric matrix of a linear form on matrices

On the symmetric matrices, a linear form `f` on the real `n × n` matrices is the pairing
`A ↦ ∑ᵢⱼ Aᵢⱼ Yᵢⱼ` with its symmetric matrix `Yᵢⱼ = (f(Eᵢⱼ) + f(Eⱼᵢ)) / 2`, `Eᵢⱼ` the matrix units.
As a self-adjoint map of `ℝⁿ`, `Y` satisfies `⟪Y x, x⟫ = f(x xᵀ)` and has trace `f(1)`, and it is
not zero if `f` does not vanish on the symmetric matrices. Voronoi's characterisation of extreme
lattices (LMFDB `lattice.extreme`) turns linear forms on matrices into self-adjoint maps this way.

## Main definitions

* `Matrix.dualSymmMatrix`: the symmetric matrix of a linear form on the real `n × n` matrices.
-/

open scoped InnerProductSpace

namespace Matrix

variable {ι : Type*} [DecidableEq ι] (f : Matrix ι ι ℝ →ₗ[ℝ] ℝ) {A : Matrix ι ι ℝ}

/-- The **symmetric matrix of a linear form** `f` on the real `n × n` matrices: the matrix `Y`
with entries `Yᵢⱼ = (f(Eᵢⱼ) + f(Eⱼᵢ)) / 2`, `Eᵢⱼ` the matrix units, so that `f A = ∑ᵢⱼ Aᵢⱼ Yᵢⱼ` for
every symmetric matrix `A`. -/
noncomputable def dualSymmMatrix : Matrix ι ι ℝ :=
  .of fun i j ↦ (f (single i j 1) + f (single j i 1)) / 2

lemma isSymm_dualSymmMatrix : (dualSymmMatrix f).IsSymm :=
  Matrix.ext fun i j ↦ by simp [dualSymmMatrix, add_comm]

variable [Fintype ι]

lemma apply_eq_sum_dualSymmMatrix (hA : A.IsSymm) :
    f A = ∑ i, ∑ j, A i j * dualSymmMatrix f i j := by
  have h1 : f A = ∑ i, ∑ j, A i j * f (single i j 1) := by
    conv_lhs => rw [matrix_eq_sum_single A]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    have h : single i j (A i j) = A i j • single i j (1 : ℝ) := by
      rw [smul_single, smul_eq_mul, mul_one]
    rw [h, map_smul, smul_eq_mul]
  have h2 : ∑ i, ∑ j, A i j * f (single j i 1) = ∑ i, ∑ j, A i j * f (single i j 1) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hA.apply i j]
  have h3 : ∑ i, ∑ j, A i j * dualSymmMatrix f i j =
      (∑ i, ∑ j, A i j * f (single i j 1) + ∑ i, ∑ j, A i j * f (single j i 1)) / 2 := by
    simp only [dualSymmMatrix, of_apply, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring1
  rw [h3, h2, ← h1]
  ring1

lemma isSelfAdjoint_toEuclideanCLM_dualSymmMatrix :
    IsSelfAdjoint (toEuclideanCLM (𝕜 := ℝ) (dualSymmMatrix f)) := by
  have h : IsSelfAdjoint (dualSymmMatrix f) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    exact isSymm_dualSymmMatrix f
  exact h.map toEuclideanCLM

lemma inner_toEuclideanCLM_dualSymmMatrix (x : EuclideanSpace ℝ ι) :
    ⟪toEuclideanCLM (𝕜 := ℝ) (dualSymmMatrix f) x, x⟫_ℝ = f (vecMulVec x.ofLp x.ofLp) := by
  rw [real_inner_comm, inner_toEuclideanCLM,
    apply_eq_sum_dualSymmMatrix f (transpose_vecMulVec x.ofLp x.ofLp)]
  simp only [dotProduct, mulVec, Finset.mul_sum, vecMulVec_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring1

lemma trace_toEuclideanCLM_dualSymmMatrix :
    LinearMap.trace ℝ (EuclideanSpace ℝ ι) (toEuclideanCLM (𝕜 := ℝ) (dualSymmMatrix f)) = f 1 := by
  rw [coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanLin_eq_toLin_orthonormal, trace_toLin_eq,
    apply_eq_sum_dualSymmMatrix f isSymm_one]
  simp [Matrix.trace, one_apply]

variable {f} in
lemma toEuclideanCLM_dualSymmMatrix_ne_zero (hA : A.IsSymm) (hfA : f A ≠ 0) :
    toEuclideanCLM (𝕜 := ℝ) (dualSymmMatrix f) ≠ 0 := by
  intro hK
  rw [apply_eq_sum_dualSymmMatrix f hA, EmbeddingLike.map_eq_zero_iff.mp hK] at hfA
  simp at hfA

end Matrix
