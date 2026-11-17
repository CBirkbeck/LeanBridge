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

The other facts that characterisation uses concern a finite family of vectors `x ∈ s` with weights
`c x` such that `⟪v, v⟫ = ∑ₓ c x ⟪v, x⟫²` for every `v`. By polarisation,
`⟪v, w⟫ = ∑ₓ c x ⟪v, x⟫ ⟪w, x⟫`, and so `tr T = ∑ₓ c x ⟪T x, x⟫` for every self-adjoint `T`. If
moreover the weights are positive and the only self-adjoint `T` with `⟪T x, x⟫ = 0` for all `x ∈ s`
is `0`, the compactness of the unit sphere gives `κ > 0` with `κ ‖T‖ ≤ ∑ₓ c x ⟪T x, x⟫` for every
self-adjoint `T` with `⟪T x, x⟫ ≥ 0` for all `x ∈ s`.

## Main results

* `ContinuousLinearMap.det_one_add_lt_exp_trace`: `det (1 + T) < exp (tr T)` for a nonzero
  self-adjoint `T` with `‖T‖ < 1`.
* `ContinuousLinearMap.one_add_trace_sub_le_det_one_add`: `1 + tr T - 2 n ‖T‖² ≤ det (1 + T)` for a
  self-adjoint `T` with `‖T‖ ≤ 1 / 2`.
-/

open Module

open scoped InnerProductSpace

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

lemma real_inner_eq_sum_of_forall_inner_self_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {s : Finset E} {c : E → ℝ}
    (h : ∀ v, ⟪v, v⟫_ℝ = ∑ x ∈ s, c x * ⟪v, x⟫_ℝ ^ 2) (v w : E) :
    ⟪v, w⟫_ℝ = ∑ x ∈ s, c x * (⟪v, x⟫_ℝ * ⟪w, x⟫_ℝ) := by
  have hvw : 4 * ⟪v, w⟫_ℝ = ⟪v + w, v + w⟫_ℝ - ⟪v - w, v - w⟫_ℝ := by
    rw [real_inner_add_add_self, real_inner_sub_sub_self]
    ring1
  have h4 : 4 * ⟪v, w⟫_ℝ = 4 * ∑ x ∈ s, c x * (⟪v, x⟫_ℝ * ⟪w, x⟫_ℝ) := by
    rw [hvw, h, h, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [inner_add_left, inner_sub_left]
    ring1
  linarith

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {T : E →L[ℝ] E} (i : Fin (finrank ℝ E)) {s : Finset E} {c : E → ℝ}

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

lemma trace_eq_sum_of_forall_inner_self_eq (h : ∀ v, ⟪v, v⟫_ℝ = ∑ x ∈ s, c x * ⟪v, x⟫_ℝ ^ 2)
    (hT : IsSelfAdjoint T) : LinearMap.trace ℝ E T = ∑ x ∈ s, c x * ⟪T x, x⟫_ℝ := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E),
    Finset.sum_congr rfl fun i _ ↦ real_inner_eq_sum_of_forall_inner_self_eq h _ _, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← Finset.mul_sum, real_inner_comm x (T x), ← (stdOrthonormalBasis ℝ E).sum_inner_mul_inner]
  refine congrArg (c x * ·) (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [real_inner_comm x]
  exact congrArg _ (hT.isSymmetric _ _)

lemma exists_pos_forall_mul_norm_le (hc : ∀ x ∈ s, 0 < c x)
    (hs : ∀ H : E →L[ℝ] E, IsSelfAdjoint H → (∀ x ∈ s, ⟪H x, x⟫_ℝ = 0) → H = 0) : ∃ κ > 0,
    ∀ H : E →L[ℝ] E, IsSelfAdjoint H → (∀ x ∈ s, 0 ≤ ⟪H x, x⟫_ℝ) → κ * ‖H‖ ≤
      ∑ x ∈ s, c x * ⟪H x, x⟫_ℝ := by
  have hcont (x : E) : Continuous fun H : E →L[ℝ] E ↦ ⟪H x, x⟫_ℝ :=
    (continuous_id.clm_apply continuous_const).inner continuous_const
  have hsmul (a : ℝ) (H : E →L[ℝ] E) :
      ∑ x ∈ s, c x * ⟪(a • H) x, x⟫_ℝ = a * ∑ x ∈ s, c x * ⟪H x, x⟫_ℝ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [smul_apply, real_inner_smul_left]
    ring1
  let C : Set (E →L[ℝ] E) := {H | IsSelfAdjoint H ∧ (∀ x ∈ s, 0 ≤ ⟪H x, x⟫_ℝ) ∧ ‖H‖ = 1}
  have hmem (H : E →L[ℝ] E) (hH : IsSelfAdjoint H) (hHs : ∀ x ∈ s, 0 ≤ ⟪H x, x⟫_ℝ) (hH0 : H ≠ 0) :
      ‖H‖⁻¹ • H ∈ C := by
    refine ⟨(IsSelfAdjoint.all _).smul hH, fun x hx ↦ ?_, ?_⟩
    · rw [smul_apply, real_inner_smul_left]
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg H)) (hHs x hx)
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hH0)]
  have hpos (H : E →L[ℝ] E) (hH : H ∈ C) : 0 < ∑ x ∈ s, c x * ⟪H x, x⟫_ℝ := by
    rcases hH with ⟨hH, hHs, hH1⟩
    have hnn (x : E) (hx : x ∈ s) : 0 ≤ c x * ⟪H x, x⟫_ℝ :=
      mul_nonneg (hc x hx).le (hHs x hx)
    refine (Finset.sum_nonneg hnn).lt_of_ne fun h0 ↦ ?_
    have hH0 : H = 0 := hs H hH fun x hx ↦ (mul_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0.symm x hx)).resolve_left (hc x hx).ne'
    rw [hH0, norm_zero] at hH1
    exact zero_ne_one hH1
  have hκ : ∃ κ > 0, ∀ H ∈ C, κ ≤ ∑ x ∈ s, c x * ⟪H x, x⟫_ℝ := by
    rcases C.eq_empty_or_nonempty with hC | hC
    · exact ⟨1, one_pos, fun H hH ↦ (hC.subset hH).elim⟩
    have hCc : IsCompact C := by
      refine Metric.isCompact_of_isClosed_isBounded ?_
        (Metric.isBounded_closedBall.subset fun H hH ↦ mem_closedBall_zero_iff.mpr hH.2.2.le)
      have hcl : IsClosed {H : E →L[ℝ] E | ∀ x ∈ s, 0 ≤ ⟪H x, x⟫_ℝ} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦ isClosed_le continuous_const (hcont x)
      exact (isClosed_eq continuous_star continuous_id).inter
        (hcl.inter (isClosed_eq continuous_norm continuous_const))
    rcases hCc.exists_isMinOn hC (continuous_finsetSum _ fun x _ ↦
      continuous_const.mul (hcont x)).continuousOn with ⟨H₀, hH₀, hmin⟩
    exact ⟨_, hpos H₀ hH₀, fun H hH ↦ hmin hH⟩
  rcases hκ with ⟨κ, hκ, hκC⟩
  refine ⟨κ, hκ, fun H hH hHs ↦ ?_⟩
  rcases eq_or_ne H 0 with rfl | hH0
  · simp
  · have h1 : κ ≤ ‖H‖⁻¹ * ∑ x ∈ s, c x * ⟪H x, x⟫_ℝ :=
      (hκC _ (hmem H hH hHs hH0)).trans_eq (hsmul _ _)
    rwa [le_inv_mul_iff₀ (norm_pos_iff.mpr hH0), mul_comm] at h1

end ContinuousLinearMap
