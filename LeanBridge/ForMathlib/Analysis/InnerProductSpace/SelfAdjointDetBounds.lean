import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The determinant of `1 + T` for a self-adjoint map `T`

Let `T` be a self-adjoint continuous linear map of a finite-dimensional real inner product space
`E` of dimension `n`. In an orthonormal basis of eigenvectors of `T` the map `1 + T` is diagonal,
so `det (1 + T) = ∏ᵢ (1 + λᵢ)` for the eigenvalues `λᵢ` of `T`, which satisfy `|λᵢ| ≤ ‖T‖`, while
`exp (tr T) = ∏ᵢ exp λᵢ`. Comparing the factors gives two estimates of `det (1 + T)` near the
identity:

* if `‖T‖ < 1` and `T ≠ 0`, then `0 < det (1 + T) < exp (tr T)`, as `1 + λ < exp λ` for `λ ≠ 0`;
* if `‖T‖ ≤ 1 / 2`, then `1 + tr T - 2 n ‖T‖² ≤ det (1 + T)`, as `exp (λ - 2 λ²) ≤ 1 + λ` for
  `λ ≥ -1 / 2`.

They are the expansions of the determinant near the identity that Voronoi's characterisation of
extreme lattices uses (LMFDB `lattice.extreme`).

## Main results

* `ContinuousLinearMap.det_one_add_lt_exp_trace`: `det (1 + T) < exp (tr T)` for a nonzero
  self-adjoint `T` with `‖T‖ < 1`.
* `ContinuousLinearMap.one_add_trace_sub_le_det_one_add`: `1 + tr T - 2 n ‖T‖² ≤ det (1 + T)` for a
  self-adjoint `T` with `‖T‖ ≤ 1 / 2`.
-/

open Module

namespace Real

lemma exp_sub_two_mul_sq_le_one_add {x : ℝ} (hx : -(1 / 2) ≤ x) : exp (x - 2 * x ^ 2) ≤ 1 + x := by
  have h : 0 < 1 + x := by
    linarith
  rw [← le_log_iff_exp_le h]
  have hinv : (1 + x)⁻¹ ≤ 1 - x + 2 * x ^ 2 := by
    rw [inv_le_iff_one_le_mul₀' h]
    nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 + 2 * x)]
  linarith [one_sub_inv_le_log_of_pos h]

end Real

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {T : E →L[ℝ] E} (i : Fin (finrank ℝ E))

lemma det_one_add_eq_prod_eigenvalues (hT : IsSelfAdjoint T) :
    (1 + T).det = ∏ i, (1 + hT.isSymmetric.eigenvalues rfl i) := by
  classical
  rw [det, ← LinearMap.det_toMatrix (hT.isSymmetric.eigenvectorBasis rfl).toBasis,
    toLinearMap_add, toLinearMap_one, map_add, LinearMap.toMatrix_one,
    hT.isSymmetric.toMatrix_eigenvectorBasis, RCLike.ofReal_real_eq_id, Function.id_comp,
    ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.det_diagonal]

lemma abs_eigenvalues_le_norm (hT : IsSelfAdjoint T) :
    |hT.isSymmetric.eigenvalues rfl i| ≤ ‖T‖ := by
  have h :
      ‖T (hT.isSymmetric.eigenvectorBasis rfl i)‖ ≤ ‖T‖ * ‖hT.isSymmetric.eigenvectorBasis rfl i‖ :=
    T.le_opNorm _
  rwa [← coe_coe, hT.isSymmetric.apply_eigenvectorBasis, norm_smul,
    (hT.isSymmetric.eigenvectorBasis rfl).orthonormal.1 i, mul_one, mul_one,
    RCLike.ofReal_real_eq_id, id_eq, Real.norm_eq_abs] at h

lemma exists_eigenvalues_ne_zero (hT : IsSelfAdjoint T) (hT0 : T ≠ 0) :
    ∃ i, hT.isSymmetric.eigenvalues rfl i ≠ 0 := by
  by_contra! h
  refine hT0 (coe_injective ((hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext fun i ↦ ?_))
  rw [OrthonormalBasis.coe_toBasis, hT.isSymmetric.apply_eigenvectorBasis, h i,
    RCLike.ofReal_real_eq_id, id_eq, zero_smul, toLinearMap_zero, LinearMap.zero_apply]

lemma one_add_eigenvalues_pos (hT : IsSelfAdjoint T) (hT1 : ‖T‖ < 1) :
    0 < 1 + hT.isSymmetric.eigenvalues rfl i := by
  linarith [neg_abs_le (hT.isSymmetric.eigenvalues rfl i), abs_eigenvalues_le_norm i hT]

lemma det_one_add_pos (hT : IsSelfAdjoint T) (hT1 : ‖T‖ < 1) : 0 < (1 + T).det := by
  rw [det_one_add_eq_prod_eigenvalues hT]
  exact Finset.prod_pos fun i _ ↦ one_add_eigenvalues_pos i hT hT1

/-- **`det (1 + T) < exp (tr T)`** for a nonzero self-adjoint map `T` of a finite-dimensional real
inner product space with `‖T‖ < 1`: the eigenvalues `λᵢ` of `T` satisfy `1 + λᵢ ≤ exp λᵢ`, with
`1 + λᵢ > 0` and strict inequality for the eigenvalues that are not zero. -/
lemma det_one_add_lt_exp_trace (hT : IsSelfAdjoint T) (hT1 : ‖T‖ < 1) (hT0 : T ≠ 0) :
    (1 + T).det < Real.exp (LinearMap.trace ℝ E T) := by
  rcases exists_eigenvalues_ne_zero hT hT0 with ⟨i, hi⟩
  rw [det_one_add_eq_prod_eigenvalues hT, hT.isSymmetric.trace_eq_sum_eigenvalues rfl,
    RCLike.ofReal_real_eq_id, id_eq, Real.exp_sum]
  refine Finset.prod_lt_prod₀ (fun j _ ↦ one_add_eigenvalues_pos j hT hT1)
    (fun j _ ↦ (add_comm _ _).trans_le (Real.add_one_le_exp _)) ⟨i, Finset.mem_univ i, ?_⟩
  exact (add_comm _ _).trans_lt (Real.add_one_lt_exp hi)

/-- **`1 + tr T - 2 n ‖T‖² ≤ det (1 + T)`** for a self-adjoint map `T` of a real inner product space
of finite dimension `n` with `‖T‖ ≤ 1 / 2`: the eigenvalues `λᵢ` of `T` satisfy
`exp (λᵢ - 2 λᵢ²) ≤ 1 + λᵢ` and `λᵢ² ≤ ‖T‖²`, and `1 + x ≤ exp x`. -/
lemma one_add_trace_sub_le_det_one_add (hT : IsSelfAdjoint T) (hT2 : ‖T‖ ≤ 1 / 2) :
    1 + LinearMap.trace ℝ E T - 2 * finrank ℝ E * ‖T‖ ^ 2 ≤ (1 + T).det := by
  have hsq : ∑ i, hT.isSymmetric.eigenvalues rfl i ^ 2 ≤ finrank ℝ E * ‖T‖ ^ 2 := by
    refine (Finset.sum_le_card_nsmul _ _ (‖T‖ ^ 2) fun i _ ↦ ?_).trans_eq ?_
    · rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_eigenvalues_le_norm i hT) 2
    · rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hκ (i : Fin (finrank ℝ E)) : -(1 / 2) ≤ hT.isSymmetric.eigenvalues rfl i :=
    neg_le_of_abs_le ((abs_eigenvalues_le_norm i hT).trans hT2)
  rw [det_one_add_eq_prod_eigenvalues hT, hT.isSymmetric.trace_eq_sum_eigenvalues rfl,
    RCLike.ofReal_real_eq_id, id_eq]
  refine (Finset.prod_le_prod₀ (fun i _ ↦ (Real.exp_pos _).le) fun i _ ↦
    Real.exp_sub_two_mul_sq_le_one_add (hκ i)).trans' ?_
  rw [← Real.exp_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith [Real.add_one_le_exp (∑ i, hT.isSymmetric.eigenvalues rfl i -
    2 * ∑ i, hT.isSymmetric.eigenvalues rfl i ^ 2)]

end ContinuousLinearMap
