import LeanBridge.ForMathlib.LinearAlgebra.Matrix.InertiaEigenvalues
import TauCeti.Data.SignType.Cardinality
import TauCeti.LinearAlgebra.IntegralLattice.Gram
import TauCeti.LinearAlgebra.IntegralLattice.Signature
import TauCeti.NumberTheory.QuadraticForm.Global.Signature

/-!
# The signature of an integral lattice as eigenvalue counts

The signature `(n₊, n₀, n₋)` of an integral lattice `L` (LMFDB `lattice.signature`,
`lattice.nondegenerate`) counts the positive, zero and negative eigenvalues of a Gram matrix of `L`
(LMFDB `lattice.gram`), with multiplicity. Tau Ceti defines it through the rational form of `L`:
`n₊` and `n₋` are the indices of inertia `sigPos` and `sigNeg`, and `n₀` is the dimension of the
radical (`TauCeti.IntegralLattice.signature`). The two agree for every basis of `L`: over `ℚ` the
form of `L` is that of its Gram matrix `G`, the indices of inertia of `G` do not change when `G` is
read over `ℝ` (it is congruent over `ℚ` to a diagonal matrix), and over `ℝ` they count the
eigenvalues of `G` by the spectral theorem and Sylvester's law of inertia. In particular the
eigenvalue counts do not depend on the Gram matrix.

The same indices are those of the real quadratic space `ℝ ⊗ L` at the real place of `ℚ` (Tau
Ceti's `QuadraticForm.realSignature`), so the signature classifies nondegenerate lattices up to
isometry over the real numbers (LMFDB `lattice.signature`), and the triple `(n₊, n₀, n₋)` classifies
all of them, by Tau Ceti's real classification of quadratic forms (Sylvester's law of inertia). For
a nondegenerate lattice of rank `n`, the signature is `(n, 0)` exactly when the lattice is positive
definite, `(0, n)` exactly when it is negative definite, and anything else exactly when it is
indefinite, as the knowl says. The knowl's nondegeneracy, the vanishing of
`{w ∈ L | B(v, w) = 0 for all v ∈ L}`, is Tau Ceti's nondegeneracy of the ambient rational form.

## Main results

* `TauCeti.IntegralLattice.sigPos_eq_ncard_eigenvalues_pos`,
  `TauCeti.IntegralLattice.sigNeg_eq_ncard_eigenvalues_neg` and
  `TauCeti.IntegralLattice.sigNull_eq_ncard_eigenvalues_eq_zero` (LMFDB `lattice.signature`,
  `lattice.nondegenerate`): `n₊`, `n₋` and `n₀` are the numbers of positive, negative and zero
  eigenvalues of the Gram matrix of `L` in any basis.
* `TauCeti.IntegralLattice.realSignature_eq` (LMFDB `lattice.signature`): the signature of `ℝ ⊗ L`
  at the real place of `ℚ` is `(n₊, n₋)`.
* `TauCeti.IntegralLattice.equivalent_atRealPlace_iff` (LMFDB `lattice.signature`): two
  nondegenerate lattices become isometric over `ℝ` exactly when their signatures `(n₊, n₋)` agree.
* `TauCeti.IntegralLattice.equivalent_atRealPlace_iff_signature_eq` (LMFDB `lattice.signature`,
  `lattice.nondegenerate`): two lattices, degenerate or not, become isometric over `ℝ` exactly when
  their signatures `(n₊, n₀, n₋)` agree.
* `TauCeti.IntegralLattice.isPosDef_iff_signature_eq`,
  `TauCeti.IntegralLattice.isNegDef_iff_signature_eq` and
  `TauCeti.IntegralLattice.isIndefinite_iff_signature_ne` (LMFDB `lattice.signature`): a
  nondegenerate lattice of rank `n` is positive definite, negative definite or indefinite exactly
  when its signature is `(n, 0)`, `(0, n)` or neither.
* `TauCeti.IntegralLattice.isNondegenerate_iff_forall_form_eq_zero` (LMFDB
  `lattice.nondegenerate`): `L` is nondegenerate exactly when no nonzero vector of `L` is
  orthogonal to all of `L`.
-/

open Module QuadraticMap Matrix NumberField

open LinearMap (BilinForm BilinMap)

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V) {ι : Type*}
  (e : Basis ι ℤ L) {W : Type*} [AddCommGroup W] [Module ℚ W] (M : IntegralLattice W)
  (w : {w : InfinitePlace ℚ // w.IsReal})

lemma isHermitian_map_gramMatrix : ((L.gramMatrix e).map (Int.cast : ℤ → ℝ)).IsHermitian :=
  isHermitian_iff_isSymm.mpr ((L.isSymm_gramMatrix e).map _)

lemma map_gramMatrix_intCast_real : (L.gramMatrix e).map (Int.cast : ℤ → ℝ) =
    ((L.gramMatrix e).map (Int.cast : ℤ → ℚ)).map (Rat.castHom ℝ) := by
  rw [Matrix.map_map]
  congr 1

section Gram

variable [Fintype ι] [DecidableEq ι]

lemma equivalent_toQuadraticForm'_map_gramMatrix : L.form.toQuadraticMap.Equivalent
    ((L.gramMatrix e).map (Int.cast : ℤ → ℚ)).toQuadraticForm' := by
  have hG : (L.gramMatrix e).map (Int.cast : ℤ → ℚ) =
      BilinForm.toMatrix (e.extendOfIsLattice ℚ) L.form :=
    L.map_gramMatrix e
  refine ⟨{ toLinearEquiv := (e.extendOfIsLattice ℚ).equivFun, map_app' := fun v ↦ ?_ }⟩
  rw [toQuadraticForm'_apply, hG, BilinMap.toQuadraticMap_apply,
    BilinForm.apply_eq_dotProduct_toMatrix_mulVec (e.extendOfIsLattice ℚ)]
  rfl

/-- **The positive index `n₊` of an integral lattice is the number of positive eigenvalues of its
Gram matrix** (LMFDB `lattice.signature`, `lattice.nondegenerate`) in any basis, counted with
multiplicity. -/
lemma sigPos_eq_ncard_eigenvalues_pos :
    L.sigPos = {i | 0 < (L.isHermitian_map_gramMatrix e).eigenvalues i}.ncard := by
  rw [← IsHermitian.sigPos_toQuadraticForm', map_gramMatrix_intCast_real,
    sigPos_toQuadraticForm'_map ((L.isSymm_gramMatrix e).map _) Rat.cast_strictMono]
  exact (L.equivalent_toQuadraticForm'_map_gramMatrix e).sigPos_eq

/-- **The negative index `n₋` of an integral lattice is the number of negative eigenvalues of its
Gram matrix** (LMFDB `lattice.signature`, `lattice.nondegenerate`) in any basis, counted with
multiplicity. -/
lemma sigNeg_eq_ncard_eigenvalues_neg :
    L.sigNeg = {i | (L.isHermitian_map_gramMatrix e).eigenvalues i < 0}.ncard := by
  rw [← IsHermitian.sigNeg_toQuadraticForm', map_gramMatrix_intCast_real,
    sigNeg_toQuadraticForm'_map ((L.isSymm_gramMatrix e).map _) Rat.cast_strictMono]
  exact (L.equivalent_toQuadraticForm'_map_gramMatrix e).sigNeg_eq

/-- **The null index `n₀` of an integral lattice, the dimension of its radical, is the number of
zero eigenvalues of its Gram matrix** (LMFDB `lattice.nondegenerate`) in any basis, counted with
multiplicity. -/
lemma sigNull_eq_ncard_eigenvalues_eq_zero :
    L.sigNull = {i | (L.isHermitian_map_gramMatrix e).eigenvalues i = 0}.ncard := by
  have hsum : L.sigPos + L.sigNull + L.sigNeg = Fintype.card ι := by
    rw [L.signature_sum_eq_finrank, ← L.finrank_carrier, finrank_eq_card_basis e]
  have hcard : {i | (L.isHermitian_map_gramMatrix e).eigenvalues i = 0}.ncard +
      {i | (L.isHermitian_map_gramMatrix e).eigenvalues i < 0}.ncard +
      {i | 0 < (L.isHermitian_map_gramMatrix e).eigenvalues i}.ncard = Fintype.card ι := by
    simpa only [Function.comp_apply, sign_eq_zero_iff, sign_eq_neg_one_iff, sign_eq_one_iff,
      Nat.card_eq_fintype_card]
      using SignType.ncard_fiber_zero_add_ncard_fiber_neg_add_ncard_fiber_pos
        (SignType.sign ∘ (L.isHermitian_map_gramMatrix e).eigenvalues)
  rw [L.sigPos_eq_ncard_eigenvalues_pos e, L.sigNeg_eq_ncard_eigenvalues_neg e] at hsum
  omega

end Gram

/-- **The signature of an integral lattice at the real place of `ℚ`** (LMFDB `lattice.signature`):
the indices of inertia of the real quadratic space `ℝ ⊗ L` are those of `L`. -/
lemma realSignature_eq :
    QuadraticForm.realSignature L.form.toQuadraticMap w = (L.sigPos, L.sigNeg) := by
  have hV : FiniteDimensional ℚ V := L.finiteDimensional
  rcases QuadraticForm.equivalent_weightedSumSquares L.form.toQuadraticMap with ⟨a, ha⟩
  rw [ha.realSignature_eq w, Prod.ext_iff, QuadraticForm.realSignature_fst,
    QuadraticForm.realSignature_snd, QuadraticForm.realPositiveIndex_weightedSumSquares,
    QuadraticForm.realNegativeIndex_weightedSumSquares, sigPos,
    QuadraticForm.sigPos_of_equiv_weightedSumSquares ha, sigNeg,
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares ha]
  simp

/-- **The signature classifies nondegenerate integral lattices up to isometry over the real
numbers** (LMFDB `lattice.signature`): `ℝ ⊗ L` and `ℝ ⊗ M` are isometric exactly when `L` and `M`
have the same signature `(n₊, n₋)`. -/
lemma equivalent_atRealPlace_iff [L.IsNondegenerate] [M.IsNondegenerate] :
    letI : Algebra ℚ ℝ := (InfinitePlace.embedding_of_isReal w.2).toAlgebra
    (QuadraticForm.atRealPlace L.form.toQuadraticMap w).Equivalent
      (QuadraticForm.atRealPlace M.form.toQuadraticMap w) ↔
      (L.sigPos, L.sigNeg) = (M.sigPos, M.sigNeg) := by
  have hV : FiniteDimensional ℚ V := L.finiteDimensional
  have hW : FiniteDimensional ℚ W := M.finiteDimensional
  rw [QuadraticForm.equivalent_atRealPlace_iff_realSignature_eq
    (L.form_nondegenerate.toQuadraticMap L.form_flip)
    (M.form_nondegenerate.toQuadraticMap M.form_flip) w, L.realSignature_eq, M.realSignature_eq]

/-- **The signature `(n₊, n₀, n₋)` classifies integral lattices, degenerate or not, up to isometry
over the real numbers** (LMFDB `lattice.signature`, `lattice.nondegenerate`): `ℝ ⊗ L` and `ℝ ⊗ M`
are isometric exactly when `L` and `M` have the same signature. -/
lemma equivalent_atRealPlace_iff_signature_eq :
    letI : Algebra ℚ ℝ := (InfinitePlace.embedding_of_isReal w.2).toAlgebra
    (QuadraticForm.atRealPlace L.form.toQuadraticMap w).Equivalent
      (QuadraticForm.atRealPlace M.form.toQuadraticMap w) ↔ L.signature = M.signature := by
  let : Algebra ℚ ℝ := (InfinitePlace.embedding_of_isReal w.2).toAlgebra
  have hV : FiniteDimensional ℚ V := L.finiteDimensional
  have hW : FiniteDimensional ℚ W := M.finiteDimensional
  have hL : L.sigPos + L.sigNull + L.sigNeg = finrank ℚ V := L.signature_sum_eq_finrank
  have hM : M.sigPos + M.sigNull + M.sigNeg = finrank ℚ W := M.signature_sum_eq_finrank
  have hLw : QuadraticForm.realSignature L.form.toQuadraticMap w = (L.sigPos, L.sigNeg) :=
    L.realSignature_eq w
  have hMw : QuadraticForm.realSignature M.form.toQuadraticMap w = (M.sigPos, M.sigNeg) :=
    M.realSignature_eq w
  rw [QuadraticForm.realSignature, Prod.mk.injEq] at hLw hMw
  rw [QuadraticForm.equivalent_iff_finrank_eq_and_sigPos_eq_and_sigNeg_eq, finrank_atRealPlace,
    finrank_atRealPlace, hLw.1, hLw.2, hMw.1, hMw.2, signature, signature, Prod.mk.injEq,
    Prod.mk.injEq]
  omega

lemma sigNull_eq_zero [L.IsNondegenerate] : L.sigNull = 0 :=
  Nat.eq_zero_of_not_pos <| L.isDegenerate_iff_sigNull_pos.not.mp <|
    L.isDegenerate_iff_not_nondegenerate.not.mpr <| not_not.mpr L.form_nondegenerate

lemma sigPos_add_sigNeg [L.IsNondegenerate] : L.sigPos + L.sigNeg = finrank ℚ V := by
  have h : L.sigPos + L.sigNull + L.sigNeg = finrank ℚ V := L.signature_sum_eq_finrank
  rw [L.sigNull_eq_zero] at h
  omega

/-- **A nondegenerate integral lattice of rank `n` is positive definite exactly when its signature
is `(n, 0)`** (LMFDB `lattice.signature`). -/
lemma isPosDef_iff_signature_eq [L.IsNondegenerate] :
    L.IsPosDef ↔ (L.sigPos, L.sigNeg) = (finrank ℚ V, 0) := by
  have h : L.sigPos + L.sigNeg = finrank ℚ V := L.sigPos_add_sigNeg
  rw [isPosDef_iff_sigNull_eq_zero_and_sigNeg_eq_zero, L.sigNull_eq_zero, Prod.ext_iff]
  omega

/-- **A nondegenerate integral lattice of rank `n` is negative definite exactly when its signature
is `(0, n)`** (LMFDB `lattice.signature`). -/
lemma isNegDef_iff_signature_eq [L.IsNondegenerate] :
    L.IsNegDef ↔ (L.sigPos, L.sigNeg) = (0, finrank ℚ V) := by
  have h : L.sigPos + L.sigNeg = finrank ℚ V := L.sigPos_add_sigNeg
  rw [isNegDef_iff_sigPos_eq_zero_and_sigNull_eq_zero, L.sigNull_eq_zero, Prod.ext_iff]
  omega

/-- **A nondegenerate integral lattice of rank `n` is indefinite exactly when its signature is
neither `(n, 0)` nor `(0, n)`** (LMFDB `lattice.signature`). -/
lemma isIndefinite_iff_signature_ne [L.IsNondegenerate] : L.IsIndefinite ↔
    (L.sigPos, L.sigNeg) ≠ (finrank ℚ V, 0) ∧ (L.sigPos, L.sigNeg) ≠ (0, finrank ℚ V) := by
  have h : L.sigPos + L.sigNeg = finrank ℚ V := L.sigPos_add_sigNeg
  rw [IsIndefinite, ne_eq, ne_eq, Prod.ext_iff, Prod.ext_iff]
  omega

/-- **An integral lattice is nondegenerate exactly when no nonzero vector of the lattice is
orthogonal to the whole lattice** (LMFDB `lattice.nondegenerate`):
`{w ∈ L | B(v, w) = 0 for all v ∈ L} = 0`. -/
lemma isNondegenerate_iff_forall_form_eq_zero :
    L.IsNondegenerate ↔ ∀ w : L, (∀ v : L, L.form v w = 0) → w = 0 := by
  have h : L.IsNondegenerate ↔ L.integralForm.SeparatingRight :=
    (⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩ : L.IsNondegenerate ↔ L.form.Nondegenerate).trans <|
      L.nondegenerate_integralForm_iff.symm.trans
        L.isSymm_integralForm.isRefl.nondegenerate_iff_separatingRight
  rw [h]
  refine forall_congr' fun w ↦ imp_congr_left (forall_congr' fun v ↦ ?_)
  rw [← L.integralForm_cast, Int.cast_eq_zero]

end TauCeti.IntegralLattice
