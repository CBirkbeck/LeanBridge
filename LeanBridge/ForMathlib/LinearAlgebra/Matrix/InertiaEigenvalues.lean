import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import TauCeti.LinearAlgebra.Matrix.ToQuadraticForm

/-!
# The indices of inertia of a symmetric matrix

The indices of inertia `sigPos` and `sigNeg` of the quadratic form `x ↦ x ⬝ᵥ A *ᵥ x` of a symmetric
matrix `A`, the largest dimensions of subspaces on which it is positive, respectively negative,
definite, are read off from its eigenvalues and are unchanged by enlarging the field of scalars:

* over `ℝ`, the spectral theorem makes `A` congruent, by an orthogonal matrix, to the diagonal
  matrix of its eigenvalues, so by Sylvester's law of inertia `sigPos` and `sigNeg` are the numbers
  of positive and of negative eigenvalues of `A`, counted with multiplicity, that is, of positive
  and of negative roots of its characteristic polynomial;
* over any field in which `2` is invertible, a symmetric matrix is congruent to a diagonal matrix,
  by an orthogonal basis of its bilinear form, so for an order embedding of ordered fields
  `f : K → L`, such as `ℚ → ℝ`, the matrix `A` and its image `f(A)` have the same indices.

## Main results

* `Matrix.exists_isUnit_det_mul_mul_transpose_eq_diagonal`: a symmetric matrix is congruent to a
  diagonal matrix.
* `Matrix.IsHermitian.equivalent_toQuadraticForm'`: the form of a real symmetric matrix is
  isometric to the weighted sum of squares with its eigenvalues as weights.
* `Matrix.IsHermitian.sigPos_toQuadraticForm'` and `Matrix.IsHermitian.sigNeg_toQuadraticForm'`:
  the indices of inertia of a real symmetric matrix are its numbers of positive and of negative
  eigenvalues.
* `Matrix.IsHermitian.sigPos_toQuadraticForm'_eq_card_filter_roots` and
  `Matrix.IsHermitian.sigNeg_toQuadraticForm'_eq_card_filter_roots`: the same numbers, as the
  numbers of positive and of negative roots of the characteristic polynomial, with multiplicity.
* `Matrix.sigPos_toQuadraticForm'_map` and `Matrix.sigNeg_toQuadraticForm'_map`: the indices of
  inertia of a symmetric matrix are unchanged by an order embedding of ordered fields.
-/

open Module QuadraticMap

open LinearMap (BilinForm)

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A symmetric matrix over a field in which `2` is invertible is congruent to a diagonal
matrix**: `P A Pᵀ` is diagonal for some `P` with unit determinant, whose rows form an orthogonal
basis for the bilinear form of `A`. -/
lemma exists_isUnit_det_mul_mul_transpose_eq_diagonal {K : Type*} [Field K] [Invertible (2 : K)]
    {A : Matrix ι ι K} (hA : A.IsSymm) :
    ∃ P : Matrix ι ι K, IsUnit P.det ∧ ∃ d : ι → K, P * A * Pᵀ = diagonal d := by
  have hB : (toLinearMap₂' K A).IsSymm := by
    refine ⟨fun x y ↦ ?_⟩
    rw [toLinearMap₂'_apply', toLinearMap₂'_apply', RingHom.id_apply, dotProduct_mulVec,
      ← mulVec_transpose, hA.eq, dotProduct_comm]
  rcases BilinForm.exists_orthogonal_basis hB with ⟨v, hv⟩
  let σ : Fin (finrank K (ι → K)) ≃ ι := Fintype.equivOfCardEq (by simp)
  let w : Basis ι K (ι → K) := v.reindex σ
  refine ⟨((Pi.basisFun K ι).toMatrix w)ᵀ, ?_, fun j ↦ toLinearMap₂' K A (w j) (w j), ?_⟩
  · rw [det_transpose, ← Basis.det_apply]
    exact (Pi.basisFun K ι).isUnit_det w
  ext j k
  have h : (((Pi.basisFun K ι).toMatrix w)ᵀ * A * ((Pi.basisFun K ι).toMatrix w)ᵀᵀ) j k =
      toLinearMap₂' K A (w j) (w k) := by
    rw [toLinearMap₂'_apply', dotProduct_mulVec]
    simp [mul_apply, Basis.toMatrix_apply, dotProduct, vecMul]
  rw [h, diagonal_apply]
  split_ifs with hjk
  · rw [hjk]
  · rw [Basis.reindex_apply, Basis.reindex_apply]
    exact hv (σ.symm.injective.ne hjk)

section Real

variable {A : Matrix ι ι ℝ}

section Eigenvalues

variable (hA : A.IsHermitian)

/-- **The form of a real symmetric matrix is isometric to the weighted sum of squares of its
eigenvalues**, by the spectral theorem: `Uᵀ A U` is the diagonal matrix of the eigenvalues for the
orthogonal matrix `U` of eigenvectors. -/
lemma IsHermitian.equivalent_toQuadraticForm' :
    A.toQuadraticForm'.Equivalent (weightedSumSquares ℝ hA.eigenvalues) := by
  have hP : IsUnit (star (hA.eigenvectorUnitary : Matrix ι ι ℝ)).det :=
    isUnit_det_of_right_inverse (Unitary.coe_star_mul_self hA.eigenvectorUnitary)
  have h : star (hA.eigenvectorUnitary : Matrix ι ι ℝ) * A *
      (star (hA.eigenvectorUnitary : Matrix ι ι ℝ))ᵀ = diagonal hA.eigenvalues := by
    rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose, ← Unitary.coe_star,
      ← Unitary.conjStarAlgAut_apply (S := ℝ), hA.conjStarAlgAut_star_eigenvectorUnitary,
      RCLike.ofReal_real_eq_id, Function.id_comp]
  rw [← toQuadraticForm'_diagonal, ← h]
  exact ⟨(isometryEquivCongr hP A).symm⟩

/-- **The positive index of inertia of a real symmetric matrix is its number of positive
eigenvalues**, counted with multiplicity (Sylvester's law of inertia and the spectral theorem). -/
lemma IsHermitian.sigPos_toQuadraticForm' :
    sigPos A.toQuadraticForm' = {i | 0 < hA.eigenvalues i}.ncard :=
  QuadraticForm.sigPos_of_equiv_weightedSumSquares hA.equivalent_toQuadraticForm'

/-- **The negative index of inertia of a real symmetric matrix is its number of negative
eigenvalues**, counted with multiplicity (Sylvester's law of inertia and the spectral theorem). -/
lemma IsHermitian.sigNeg_toQuadraticForm' :
    sigNeg A.toQuadraticForm' = {i | hA.eigenvalues i < 0}.ncard :=
  QuadraticForm.sigNeg_of_equiv_weightedSumSquares hA.equivalent_toQuadraticForm'

end Eigenvalues

/-- **The positive index of inertia of a real symmetric matrix is the number of positive roots of
its characteristic polynomial**, counted with multiplicity. -/
lemma IsHermitian.sigPos_toQuadraticForm'_eq_card_filter_roots (hA : A.IsHermitian) :
    sigPos A.toQuadraticForm' = (A.charpoly.roots.filter (0 < ·)).card := by
  rw [hA.sigPos_toQuadraticForm', hA.roots_charpoly_eq_eigenvalues, Multiset.filter_map,
    Multiset.card_map, RCLike.ofReal_real_eq_id, Function.id_comp, Set.ncard_eq_toFinset_card',
    Set.toFinset_ofPred]
  rfl

/-- **The negative index of inertia of a real symmetric matrix is the number of negative roots of
its characteristic polynomial**, counted with multiplicity. -/
lemma IsHermitian.sigNeg_toQuadraticForm'_eq_card_filter_roots (hA : A.IsHermitian) :
    sigNeg A.toQuadraticForm' = (A.charpoly.roots.filter (· < 0)).card := by
  rw [hA.sigNeg_toQuadraticForm', hA.roots_charpoly_eq_eigenvalues, Multiset.filter_map,
    Multiset.card_map, RCLike.ofReal_real_eq_id, Function.id_comp, Set.ncard_eq_toFinset_card',
    Set.toFinset_ofPred]
  rfl

end Real

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field L] [LinearOrder L]
  [IsStrictOrderedRing L] {A : Matrix ι ι K} {f : K →+* L}

/-- **The positive index of inertia of a symmetric matrix is unchanged by an order embedding of
ordered fields**, such as `ℚ → ℝ`: over `K` the matrix is congruent to a diagonal matrix `D`, and
over `L` its image is congruent to the image of `D`, with as many positive entries. -/
lemma sigPos_toQuadraticForm'_map (hA : A.IsSymm) (hf : StrictMono f) :
    sigPos (A.map f).toQuadraticForm' = sigPos A.toQuadraticForm' := by
  have h2 : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  rcases exists_isUnit_det_mul_mul_transpose_eq_diagonal hA with ⟨P, hP, d, hd⟩
  have hd' : P.map f * A.map f * (P.map f)ᵀ = diagonal (f ∘ d) := by
    rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hd, diagonal_map (map_zero f)]
    rfl
  have hP' : IsUnit (P.map f).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hP.map f
  rw [← (Equivalent.sigPos_eq ⟨isometryEquivCongr hP A⟩), hd,
    ← (Equivalent.sigPos_eq ⟨isometryEquivCongr hP' (A.map f)⟩), hd', toQuadraticForm'_diagonal,
    toQuadraticForm'_diagonal, QuadraticForm.sigPos_weightedSumSquares,
    QuadraticForm.sigPos_weightedSumSquares]
  congr 1
  ext i
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Function.comp_apply, ← map_zero f, hf.lt_iff_lt]

/-- **The negative index of inertia of a symmetric matrix is unchanged by an order embedding of
ordered fields**, such as `ℚ → ℝ`. -/
lemma sigNeg_toQuadraticForm'_map (hA : A.IsSymm) (hf : StrictMono f) :
    sigNeg (A.map f).toQuadraticForm' = sigNeg A.toQuadraticForm' := by
  rw [← sigPos_neg, ← sigPos_neg, ← toQuadraticForm'_neg, ← toQuadraticForm'_neg,
    ← Matrix.map_neg _ (map_neg f), sigPos_toQuadraticForm'_map hA.neg hf]

end Matrix
