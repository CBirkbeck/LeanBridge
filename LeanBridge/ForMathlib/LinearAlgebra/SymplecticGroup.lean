import TauCeti.LinearAlgebra.BilinearForm.Isometry
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# Symplectic groups of invertible alternating matrices

The LMFDB (`group.symplectic`) defines the symplectic group `Sp(2n, q)` as the group of invertible
matrices `M` over `𝔽_q` with `Mᵀ Ω M = Ω`, for `Ω` any fixed invertible alternating matrix, for
example `Ω = [[0, I], [-I, 0]]`. Over a commutative ring, the isometry group of a square matrix
`Ω` is the subgroup of `GL` of these matrices. Conjugation by an invertible matrix `P` carries the
isometry group of `Ω` onto that of `Pᵀ Ω P`. Over a field, any two invertible alternating matrices
of the same size are congruent, `Pᵀ Ω P = Ω'`, by Tau Ceti's symplectic basis theorem
`LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J`: both bilinear forms have the matrix `J`
in suitable bases. So up to conjugation in `GL` the group does not depend on the choice of `Ω`.

Mathlib's standard matrix `J = [[0, -I], [I, 0]]` is invertible (Tau Ceti's `Matrix.isUnit_J`) and
alternating, and its isometry group is Tau Ceti's `TauCeti.GLSymplectic`, the subgroup of `GL` of
the matrices in Mathlib's `Matrix.symplecticGroup` (whose condition `M J Mᵀ = J` is equivalent to
`Mᵀ J M = J`). The LMFDB's example is `-J`, which has the same isometry group. Hence, after
reindexing along an equivalence `ι ≃ l ⊕ l`, the isometry group of any invertible alternating
matrix is conjugate to `TauCeti.GLSymplectic l F`, and it is isomorphic to Mathlib's
`Matrix.symplecticGroup l F`.

The LMFDB's "skew-symmetric" must read "alternating": in characteristic `2` the identity matrix
is invertible and skew-symmetric, and its isometry group is an orthogonal group.

## Main definitions

* `Matrix.isometryGroup` (LMFDB `group.symplectic`): the invertible matrices `M` with
  `Mᵀ * Ω * M = Ω`.
* `Matrix.isometryGroupConj`: conjugation by `P`, from the isometry group of `Ω` onto that of
  `Pᵀ * Ω * P`.
* `Matrix.isometryGroupReindex`: reindexing, from the isometry group of `Ω` onto that of the
  reindexed matrix.
* `Matrix.isometryGroupEquivOfIsAlt` (LMFDB `group.symplectic`): an isomorphism, by conjugation,
  between the isometry groups of two invertible alternating matrices of the same size.
* `Matrix.isometryGroupEquivSymplecticGroup` (LMFDB `group.symplectic`): an isomorphism between
  the isometry group of an invertible alternating matrix and Mathlib's `Matrix.symplecticGroup`.

## Main results

* `Matrix.isAlt_toBilin'_J`: Mathlib's `J` is alternating.
* `Matrix.exists_transpose_mul_mul_eq_of_isAlt`: two invertible alternating matrices of the same
  size over a field are congruent.
* `Matrix.exists_map_conj_isometryGroup_eq_of_isAlt` (LMFDB `group.symplectic`): their isometry
  groups are conjugate in `GL`.
* `Matrix.isometryGroup_J`: the isometry group of `J` is `TauCeti.GLSymplectic`.
* `Matrix.isometryGroup_neg_J` (LMFDB `group.symplectic`): so is the isometry group of the LMFDB's
  example `-J`.
* `Matrix.exists_map_conj_map_reindexGL_isometryGroup_eq` (LMFDB `group.symplectic`): after
  reindexing, the isometry group of an invertible alternating matrix is conjugate to
  `TauCeti.GLSymplectic`.

## References

* E. Artin, *Geometric Algebra* (1957), Theorem 3.7.
-/

open LinearMap BilinForm Module TauCeti

namespace Matrix

variable {ι κ l : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype l]
  [DecidableEq l]

section CommRing

variable {R : Type*} [CommRing R] (Ω : Matrix ι ι R) (P : GL ι R) (e : ι ≃ κ) {M : GL ι R}

/-- The **isometry group** of a square matrix `Ω`: the invertible matrices `M` with
`Mᵀ * Ω * M = Ω`, which preserve the bilinear form `(x, y) ↦ xᵀ Ω y`. For an invertible
alternating `Ω` over a field it is the **symplectic group** `Sp(Ω)` (LMFDB `group.symplectic`),
which up to conjugation in `GL` does not depend on `Ω`
(`Matrix.exists_map_conj_isometryGroup_eq_of_isAlt`). -/
def isometryGroup : Subgroup (GL ι R) where
  carrier := {M | (M : Matrix ι ι R)ᵀ * Ω * M = Ω}
  mul_mem' {M N} hM hN := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, transpose_mul, Matrix.mul_assoc] at hM hN ⊢
    rw [← Matrix.mul_assoc Ω, ← Matrix.mul_assoc (M : Matrix ι ι R)ᵀ, hM, hN]
  one_mem' := by
    simp
  inv_mem' {M} hM := by
    rw [Set.mem_ofPred_eq] at hM ⊢
    nth_rw 1 [← hM]
    simp only [← Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.one_mul,
      Units.mul_inv_cancel_right]

@[simp]
lemma mem_isometryGroup : M ∈ Ω.isometryGroup ↔ (M : Matrix ι ι R)ᵀ * Ω * M = Ω :=
  Iff.rfl

lemma transpose_mul_mul_mul {m n o : Type*} [Fintype m] [Fintype n] (A : Matrix m n R)
    (B : Matrix n o R) (X : Matrix m m R) : (A * B)ᵀ * X * (A * B) = Bᵀ * (Aᵀ * X * A) * B := by
  simp only [transpose_mul, Matrix.mul_assoc]

lemma conj_mem_isometryGroup_iff :
    P * M * P⁻¹ ∈ Ω.isometryGroup ↔ M ∈ ((P : Matrix ι ι R)ᵀ * Ω * P).isometryGroup := by
  rw [mem_isometryGroup, mem_isometryGroup, Units.val_mul, Units.val_mul, transpose_mul_mul_mul,
    transpose_mul_mul_mul]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · conv_rhs => rw [← h, ← transpose_mul_mul_mul ((P⁻¹ : GL ι R) : Matrix ι ι R) (P : Matrix ι ι R),
      Units.inv_mul, transpose_one, Matrix.one_mul, Matrix.mul_one]
  · rw [h, ← transpose_mul_mul_mul (P : Matrix ι ι R) ((P⁻¹ : GL ι R) : Matrix ι ι R),
      Units.mul_inv, transpose_one, Matrix.one_mul, Matrix.mul_one]

lemma map_conj_isometryGroup : Ω.isometryGroup.map (MulAut.conj P⁻¹ : GL ι R →* GL ι R) =
    ((P : Matrix ι ι R)ᵀ * Ω * P).isometryGroup := by
  ext M
  rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv,
    conj_mem_isometryGroup_iff]

/-- Conjugation `M ↦ P⁻¹ * M * P` by an invertible matrix `P`, as an isomorphism from the
isometry group of `Ω` onto that of `Pᵀ * Ω * P`. -/
def isometryGroupConj : Ω.isometryGroup ≃* ((P : Matrix ι ι R)ᵀ * Ω * P).isometryGroup :=
  ((MulAut.conj P⁻¹).subgroupMap Ω.isometryGroup).trans <|
    .subgroupCongr <| map_conj_isometryGroup Ω P

@[simp]
lemma coe_isometryGroupConj_apply (g : Ω.isometryGroup) :
    (isometryGroupConj Ω P g : GL ι R) = P⁻¹ * g * P :=
  rfl

@[simp]
lemma isometryGroup_neg : (-Ω).isometryGroup = Ω.isometryGroup := by
  ext M
  simp only [mem_isometryGroup, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

lemma reindexGL_mem_isometryGroup_iff :
    e.reindexGL R M ∈ (Ω.reindex e e).isometryGroup ↔ M ∈ Ω.isometryGroup := by
  rw [mem_isometryGroup, mem_isometryGroup, Equiv.coe_reindexGL, ← reindex_apply, transpose_reindex,
    ← (reindex e e).apply_eq_iff_eq]
  simp only [reindex_apply, submatrix_mul_equiv]

lemma map_reindexGL_isometryGroup :
    Ω.isometryGroup.map (e.reindexGL R : GL ι R →* GL κ R) = (Ω.reindex e e).isometryGroup := by
  ext M
  rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map_equiv, ← reindexGL_mem_isometryGroup_iff Ω e,
    MulEquiv.apply_symm_apply]

/-- Reindexing along an equivalence `e : ι ≃ κ`, as an isomorphism from the isometry group of `Ω`
onto that of `Ω.reindex e e`. -/
def isometryGroupReindex : Ω.isometryGroup ≃* (Ω.reindex e e).isometryGroup :=
  ((e.reindexGL R).subgroupMap Ω.isometryGroup).trans <|
    .subgroupCongr <| map_reindexGL_isometryGroup Ω e

lemma coe_isometryGroupReindex_apply (g : Ω.isometryGroup) :
    (isometryGroupReindex Ω e g : GL κ R) = e.reindexGL R g :=
  rfl

lemma isAlt_toBilin'_reindex (hΩ : Ω.toBilin'.IsAlt) : (Ω.reindex e e).toBilin'.IsAlt := by
  intro x
  simpa [toBilin'_apply, ← e.sum_comp] using hΩ (x ∘ e)

variable (l R) in
/-- **Mathlib's matrix `J` is alternating**: `xᵀ J x = 0` for every vector `x`. -/
lemma isAlt_toBilin'_J : (J l R).toBilin'.IsAlt := by
  intro x
  simp [toBilin'_apply', J, fromBlocks_mulVec, neg_mulVec, dotProduct, mul_comm]

variable (l R) in
/-- **The isometry group of Mathlib's `J` is Tau Ceti's `TauCeti.GLSymplectic`**, the subgroup of
`GL` of the matrices in Mathlib's `Matrix.symplecticGroup`. -/
lemma isometryGroup_J : (J l R).isometryGroup = GLSymplectic l R :=
  Subgroup.ext fun _ ↦ GLSymplectic.mem_iff'.symm

variable (l R) in
/-- **The isometry group of the LMFDB's example `Ω = [[0, I], [-I, 0]]`, which is `-J`, is Tau
Ceti's `TauCeti.GLSymplectic`.** -/
lemma isometryGroup_neg_J : (-J l R).isometryGroup = GLSymplectic l R := by
  rw [isometryGroup_neg, isometryGroup_J]

end CommRing

section Field

variable {F : Type*} [Field F] {Ω Ω' : Matrix ι ι F} (e : ι ≃ l ⊕ l)

/-- **Two invertible alternating matrices of the same size over a field are congruent**: there is
an invertible `P` with `Pᵀ * Ω * P = Ω'`. By Tau Ceti's symplectic basis theorem, both bilinear
forms have the matrix `J` in some bases, and `P` is the matrix of the automorphism carrying one
basis to the other. -/
lemma exists_transpose_mul_mul_eq_of_isAlt (hΩ : Ω.toBilin'.IsAlt) (hΩu : IsUnit Ω)
    (hΩ' : Ω'.toBilin'.IsAlt) (hΩ'u : IsUnit Ω') :
    ∃ P : GL ι F, (P : Matrix ι ι F)ᵀ * Ω * P = Ω' := by
  rcases hΩ.exists_basis_toMatrix_eq_J <| nondegenerate_toBilin'_iff_det_ne_zero.mpr
    ((isUnit_iff_isUnit_det Ω).mp hΩu).ne_zero with ⟨m, b, hb⟩
  rcases hΩ'.exists_basis_toMatrix_eq_J <| nondegenerate_toBilin'_iff_det_ne_zero.mpr
    ((isUnit_iff_isUnit_det Ω').mp hΩ'u).ne_zero with ⟨m', b', hb'⟩
  have hm : m' = m := by
    have h : Fintype.card (Fin m' ⊕ Fin m') = Fintype.card (Fin m ⊕ Fin m) :=
      (finrank_eq_card_basis b').symm.trans (finrank_eq_card_basis b)
    simp only [Fintype.card_sum, Fintype.card_fin] at h
    omega
  subst hm
  let φ : Ω'.toBilin'.IsometryEquiv Ω.toBilin' := b'.isometryEquivOfToMatrixEq b (hb'.trans hb.symm)
  refine ⟨.mk'' (LinearMap.toMatrix' (φ : (ι → F) ≃ₗ[F] ι → F)) ?_, toBilin'.injective ?_⟩
  · rw [LinearMap.det_toMatrix']
    exact (φ : (ι → F) ≃ₗ[F] ι → F).isUnit_det'
  · rw [← toBilin'_comp, GeneralLinearGroup.val_mk'', toLin'_toMatrix']
    exact LinearMap.ext₂ fun x y ↦ φ.map_app y x

/-- **The isometry groups of two invertible alternating matrices of the same size over a field are
conjugate in `GL`**, so the symplectic group `Sp(Ω)` does not depend on the choice of `Ω` (LMFDB
`group.symplectic`). -/
lemma exists_map_conj_isometryGroup_eq_of_isAlt (hΩ : Ω.toBilin'.IsAlt) (hΩu : IsUnit Ω)
    (hΩ' : Ω'.toBilin'.IsAlt) (hΩ'u : IsUnit Ω') :
    ∃ P : GL ι F, Ω.isometryGroup.map (MulAut.conj P : GL ι F →* GL ι F) = Ω'.isometryGroup := by
  rcases exists_transpose_mul_mul_eq_of_isAlt hΩ hΩu hΩ' hΩ'u with ⟨P, hP⟩
  exact ⟨P⁻¹, hP ▸ map_conj_isometryGroup Ω P⟩

/-- An isomorphism between the isometry groups of two invertible alternating matrices of the same
size over a field (LMFDB `group.symplectic`): conjugation by an invertible matrix `P` with
`Pᵀ * Ω * P = Ω'`, chosen by `Matrix.exists_transpose_mul_mul_eq_of_isAlt`. -/
noncomputable def isometryGroupEquivOfIsAlt (hΩ : Ω.toBilin'.IsAlt) (hΩu : IsUnit Ω)
    (hΩ' : Ω'.toBilin'.IsAlt) (hΩ'u : IsUnit Ω') : Ω.isometryGroup ≃* Ω'.isometryGroup :=
  haveI h : ∃ P : GL ι F, (P : Matrix ι ι F)ᵀ * Ω * P = Ω' :=
    exists_transpose_mul_mul_eq_of_isAlt hΩ hΩu hΩ' hΩ'u
  (isometryGroupConj Ω h.choose).trans <| .subgroupCongr <| congrArg isometryGroup h.choose_spec

lemma coe_isometryGroupEquivOfIsAlt_apply (hΩ : Ω.toBilin'.IsAlt) (hΩu : IsUnit Ω)
    (hΩ' : Ω'.toBilin'.IsAlt) (hΩ'u : IsUnit Ω') (g : Ω.isometryGroup) :
    letI P : GL ι F := (exists_transpose_mul_mul_eq_of_isAlt hΩ hΩu hΩ' hΩ'u).choose
    (isometryGroupEquivOfIsAlt hΩ hΩu hΩ' hΩ'u g : GL ι F) = P⁻¹ * g * P :=
  rfl

/-- **After reindexing, the isometry group of an invertible alternating matrix is conjugate to
Mathlib's symplectic group** (LMFDB `group.symplectic`): for an equivalence `e : ι ≃ l ⊕ l`,
reindexing along `e` and then conjugating carry the isometry group of `Ω` onto
`TauCeti.GLSymplectic l F`, the subgroup of `GL` of the matrices in `Matrix.symplecticGroup l F`. -/
lemma exists_map_conj_map_reindexGL_isometryGroup_eq (hΩ : Ω.toBilin'.IsAlt) (hΩu : IsUnit Ω) :
    ∃ P : GL (l ⊕ l) F, (Ω.isometryGroup.map (e.reindexGL F : GL ι F →* GL (l ⊕ l) F)).map
      (MulAut.conj P : GL (l ⊕ l) F →* GL (l ⊕ l) F) = GLSymplectic l F := by
  rw [map_reindexGL_isometryGroup, ← isometryGroup_J]
  exact exists_map_conj_isometryGroup_eq_of_isAlt (isAlt_toBilin'_reindex Ω e hΩ)
    (hΩu.map (reindexAlgEquiv F F e)) (isAlt_toBilin'_J l F) (isUnit_J l F)

/-- An isomorphism between the isometry group of an invertible alternating matrix and Mathlib's
symplectic group `Matrix.symplecticGroup l F` (LMFDB `group.symplectic`), for an equivalence
`e : ι ≃ l ⊕ l`: reindex along `e`, conjugate onto the isometry group of `J`
(`Matrix.isometryGroupEquivOfIsAlt`), which is `TauCeti.GLSymplectic l F`, and apply Tau Ceti's
`TauCeti.GLSymplectic.mulEquivSymplecticGroup`. -/
noncomputable def isometryGroupEquivSymplecticGroup (hΩ : Ω.toBilin'.IsAlt) (hΩu : IsUnit Ω) :
    Ω.isometryGroup ≃* symplecticGroup l F :=
  isometryGroupReindex Ω e
  |>.trans (isometryGroupEquivOfIsAlt (isAlt_toBilin'_reindex Ω e hΩ)
    (hΩu.map (reindexAlgEquiv F F e)) (isAlt_toBilin'_J l F) (isUnit_J l F))
  |>.trans (.subgroupCongr (isometryGroup_J l F))
  |>.trans (GLSymplectic.mulEquivSymplecticGroup l F)

end Field

end Matrix
