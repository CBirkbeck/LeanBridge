import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Order.Sym2
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# The congruence `X ↦ Aᵀ X A` on symmetric matrices

A symmetric complex `g × g` matrix `X` is determined by its `g(g + 1) / 2` entries `X_ij`, `i ≤ j`,
which are indexed without a choice of order by the unordered pairs `s(i, j) ∈ Sym2 l`. In these
coordinates the congruence `X ↦ Aᵀ X A` by a square matrix `A` is a linear map of determinant
`det(A)^{g + 1}`. This is the Jacobian computation behind the invariance of the measure
`det(Y)^{-g-1} dX dY` on the Siegel upper half-space.

## Main definitions

* `SiegelUpperHalfSpace.ofSymCoords`: the symmetric matrix with given coordinates.
* `SiegelUpperHalfSpace.symCoords`: the coordinates of the symmetrisation of a matrix.
* `SiegelUpperHalfSpace.congrSym`: the congruence `X ↦ Aᵀ X A`, in coordinates.

## Main results

* `SiegelUpperHalfSpace.det_congrSym`: the congruence by `A` has determinant `det(A)^{g + 1}`.
-/

open Matrix

namespace SiegelUpperHalfSpace

variable {l : Type*} (h : Sym2 l → ℂ) (M : Matrix l l ℂ) (i j : l) {a : ℂ} (d : l → ℂ)

/-- The symmetric matrix `(h(s(i, j)))_{i,j}` with coordinates `h : Sym2 l → ℂ`. -/
def ofSymCoords : (Sym2 l → ℂ) →ₗ[ℂ] Matrix l l ℂ where
  toFun h := of fun i j ↦ h s(i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coordinates `(M_ij + M_ji) / 2` of the symmetrisation of a square matrix `M`, indexed by
`s(i, j) ∈ Sym2 l`; for a symmetric matrix, its entries `M_ij`. -/
noncomputable def symCoords : Matrix l l ℂ →ₗ[ℂ] Sym2 l → ℂ where
  toFun M := Sym2.lift ⟨fun i j ↦ (M i j + M j i) / 2, fun _ _ ↦ by simp only [add_comm]⟩
  map_add' M N := by
    ext s
    induction s using Sym2.ind
    simp only [Pi.add_apply, Sym2.lift_mk, Matrix.add_apply]
    ring1
  map_smul' c M := by
    ext s
    induction s using Sym2.ind
    simp only [RingHom.id_apply, Pi.smul_apply, Sym2.lift_mk, Matrix.smul_apply]
    ring1

lemma ofSymCoords_apply : ofSymCoords h i j = h s(i, j) :=
  rfl

lemma symCoords_mk : symCoords M s(i, j) = (M i j + M j i) / 2 :=
  rfl

lemma transpose_ofSymCoords : (ofSymCoords h)ᵀ = ofSymCoords h := by
  ext i j
  simp [ofSymCoords_apply, Sym2.eq_swap]

lemma symCoords_ofSymCoords : symCoords (ofSymCoords h) = h := by
  ext s
  induction s using Sym2.ind
  simp [symCoords_mk, ofSymCoords_apply, Sym2.eq_swap]

variable {M} in
lemma ofSymCoords_symCoords (hM : Mᵀ = M) : ofSymCoords (symCoords M) = M := by
  ext i j
  simp [ofSymCoords_apply, symCoords_mk, IsSymm.apply hM i j]

variable [DecidableEq l] {i} in
private lemma update_mul_update (ha : a ≠ 0) (x : l) :
    Function.update (1 : l → ℂ) i a x * Function.update (1 : l → ℂ) i a⁻¹ x = 1 := by
  rcases eq_or_ne x i with rfl | hx <;> simp [*]

variable [Fintype l] (A B : Matrix l l ℂ)

/-- The congruence `X ↦ Aᵀ X A` by a square matrix `A`, on the symmetric matrices `X`, in their
coordinates `Sym2 l → ℂ`. -/
noncomputable def congrSym : (Sym2 l → ℂ) →ₗ[ℂ] Sym2 l → ℂ :=
  symCoords ∘ₗ (LinearMap.mulLeft ℂ Aᵀ ∘ₗ LinearMap.mulRight ℂ A) ∘ₗ ofSymCoords

lemma congrSym_apply : congrSym A h = symCoords (Aᵀ * ofSymCoords h * A) := by
  simp [congrSym, Matrix.mul_assoc]

lemma ofSymCoords_congrSym : ofSymCoords (congrSym A h) = Aᵀ * ofSymCoords h * A := by
  rw [congrSym_apply, ofSymCoords_symCoords]
  rw [transpose_mul, transpose_mul, transpose_transpose, transpose_ofSymCoords, Matrix.mul_assoc]

lemma congrSym_mul : congrSym (A * B) = congrSym B ∘ₗ congrSym A := by
  refine LinearMap.ext fun h ↦ ?_
  rw [LinearMap.comp_apply, congrSym_apply (congrSym A h), ofSymCoords_congrSym, congrSym_apply,
    transpose_mul]
  simp only [Matrix.mul_assoc]

lemma det_congrSym_mul : (congrSym (A * B)).det = (congrSym A).det * (congrSym B).det := by
  rw [congrSym_mul, LinearMap.det_comp, mul_comm]

variable [DecidableEq l]

lemma congrSym_one : congrSym (1 : Matrix l l ℂ) = LinearMap.id := by
  refine LinearMap.ext fun h ↦ ?_
  rw [congrSym_apply, transpose_one, Matrix.one_mul, Matrix.mul_one, symCoords_ofSymCoords,
    LinearMap.id_apply]

private lemma prod_sym2_lift_mul :
    ∏ s : Sym2 l, Sym2.lift ⟨fun i j ↦ d i * d j, fun _ _ ↦ mul_comm _ _⟩ s =
      (∏ i, d i) ^ (Fintype.card l + 1) := by
  let _ : LinearOrder l := LinearOrder.lift' (Fintype.equivFin l) (Fintype.equivFin l).injective
  rw [Fintype.prod_equiv Sym2.sortEquiv _ (fun p ↦ d p.1.1 * d p.1.2) fun s ↦ ?_]
  · rw [Finset.prod_mul_distrib,
      ← Finset.prod_subtype ({p : l × l | p.1 ≤ p.2} : Finset _) (by simp) fun p ↦ d p.1,
      ← Finset.prod_subtype ({p : l × l | p.1 ≤ p.2} : Finset _) (by simp) fun p ↦ d p.2,
      Finset.prod_filter, Finset.prod_filter, Fintype.prod_prod_type, Fintype.prod_prod_type,
      Finset.prod_comm (f := fun i j ↦ if i ≤ j then d j else 1)]
    simp only [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    have hu : ({j | i ≤ j} : Finset l) ∪ ({j | j ≤ i} : Finset l) = Finset.univ := by
      ext j
      simp [le_total]
    have hi : ({j | i ≤ j} : Finset l) ∩ ({j | j ≤ i} : Finset l) = {i} := by
      ext j
      simp [le_antisymm_iff, and_comm]
    rw [← pow_add, ← Finset.card_union_add_card_inter, hu, hi, Finset.card_singleton,
      Finset.card_univ]
  · induction s using Sym2.ind with | _ i j
    rcases le_total i j with hij | hij <;> simp [hij, mul_comm]

lemma congrSym_diagonal : congrSym (diagonal d) =
    toLin' (diagonal fun s ↦ Sym2.lift ⟨fun i j ↦ d i * d j, fun _ _ ↦ mul_comm _ _⟩ s) := by
  refine LinearMap.ext fun h ↦ funext fun s ↦ ?_
  induction s using Sym2.ind with | _ i j
  simp [congrSym_apply, symCoords_mk, ofSymCoords_apply, Sym2.eq_swap, mulVec_diagonal]
  ring1

lemma det_congrSym_diagonal : (congrSym (diagonal d)).det = (∏ i, d i) ^ (Fintype.card l + 1) := by
  rw [congrSym_diagonal, LinearMap.det_toLin', det_diagonal, prod_sym2_lift_mul]

variable {i j}

lemma det_congrSym_transvection (hij : i ≠ j) (c : ℂ) :
    (congrSym (transvection i j c)).det = 1 := by
  have hmul (a b : ℂ) : (congrSym (transvection i j a)).det * (congrSym (transvection i j b)).det =
      (congrSym (transvection i j (a + b))).det := by
    rw [← det_congrSym_mul, transvection_mul_transvection_same _ _ hij]
  have hconj (a : ℂ) (ha : a ≠ 0) :
      (congrSym (transvection i j a)).det = (congrSym (transvection i j 1)).det := by
    have hd : (congrSym (diagonal (Function.update 1 i a))).det *
        (congrSym (diagonal (Function.update 1 i a⁻¹))).det = 1 := by
      rw [← det_congrSym_mul, diagonal_mul_diagonal, funext (update_mul_update ha), diagonal_one,
        congrSym_one, LinearMap.det_id]
    have ht : transvection i j a = diagonal (Function.update 1 i a) * transvection i j 1 *
        diagonal (Function.update 1 i a⁻¹) := by
      rw [TauCeti.diagonal_mul_transvection_mul_diagonal (update_mul_update ha),
        Function.update_self, Function.update_of_ne hij.symm, Pi.one_apply, mul_one, mul_one]
    rw [ht, det_congrSym_mul, det_congrSym_mul, mul_right_comm, hd, one_mul]
  have h0 : (congrSym (transvection i j 1)).det * (congrSym (transvection i j (-1))).det = 1 := by
    rw [hmul, add_neg_cancel, transvection_zero, congrSym_one, LinearMap.det_id]
  have h1 : (congrSym (transvection i j 1)).det = 1 := by
    refine mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h0) ?_
    rw [hmul, mul_one, one_add_one_eq_two, hconj _ two_ne_zero]
  rcases eq_or_ne c 0 with rfl | hc
  · rw [transvection_zero, congrSym_one, LinearMap.det_id]
  · rw [hconj c hc, h1]

/-- **The congruence by `A` on symmetric `g × g` matrices has determinant `det(A)^{g + 1}`**: on the
`g(g + 1) / 2`-dimensional space of symmetric matrices, `X ↦ Aᵀ X A` has determinant
`det(A)^{g + 1}`. It is checked on the diagonal matrices and the transvections, which generate all
square matrices, both sides being multiplicative in `A`. -/
lemma det_congrSym : (congrSym A).det = A.det ^ (Fintype.card l + 1) := by
  refine diagonal_transvection_induction (fun A ↦ (congrSym A).det = A.det ^ (Fintype.card l + 1)) A
    (fun d _ ↦ by rw [det_congrSym_diagonal, det_diagonal]) (fun t ↦ ?_) fun A B hA hB ↦ by
      rw [det_congrSym_mul, hA, hB, det_mul, mul_pow]
  rw [TransvectionStruct.toMatrix, det_congrSym_transvection t.hij,
    det_transvection_of_ne _ _ t.hij, one_pow]

end SiegelUpperHalfSpace
