import LeanBridge.ForMathlib.LinearAlgebra.AffineSpace.AffineGroup
import Mathlib.GroupTheory.SemidirectProduct

/-!
# The affine general linear group as a semidirect product

The general linear group `GL(n, q)` acts on `𝔽_q^n` by matrix multiplication, and the affine general
linear group is the semidirect product `AGL(n, q) = 𝔽_q^n ⋊ GL(n, q)` for this action (LMFDB
`group.affine_general_linear`). We define, for any commutative ring `R` and finite type `ι`, the
action of `GL(ι, R)` on `R^ι` and the semidirect product `AGL(ι, R) = R^ι ⋊ GL(ι, R)`, and prove
that it is isomorphic to the group `R^ι ≃ᵃ[R] R^ι` of invertible affine transformations of `R^ι`:
the pair `(v, A)` is the transformation `x ↦ A x + v`. For `R = GaloisField p r` with `r ≠ 0` and
`ι = Fin n` this is `AGL(n, q)` with `q = p ^ r`.

## Main definitions

* `Matrix.GeneralLinearGroup.mulVecMulAut` (LMFDB `group.affine_general_linear`): the action of
  `GL(ι, R)` on `R^ι` by matrix multiplication.
* `Matrix.AffineGeneralLinearGroup` (LMFDB `group.affine_general_linear`): the semidirect product
  `AGL(ι, R) = R^ι ⋊ GL(ι, R)`.
* `Matrix.AffineGeneralLinearGroup.linearAffineEquivHom`,
  `Matrix.AffineGeneralLinearGroup.toAffineEquivHom`: the linear automorphism `x ↦ A x` of `A`, and
  the affine automorphism `x ↦ A x + v` of `(v, A)`.
* `Matrix.AffineGeneralLinearGroup.mulEquivAffineEquiv` (LMFDB `group.affine_general_linear`): its
  isomorphism with the group of invertible affine transformations of `R^ι`.
-/

open LinearMap Matrix SemidirectProduct

variable (ι R : Type*) [Fintype ι] [DecidableEq ι] [CommRing R]

namespace Matrix

/-- The **action of `GL(ι, R)` on `R^ι` by matrix multiplication** (LMFDB
`group.affine_general_linear`), `v ↦ A *ᵥ v`, by automorphisms of the additive group `R^ι`, written
multiplicatively. -/
def GeneralLinearGroup.mulVecMulAut : GL ι R →* MulAut (Multiplicative (ι → R)) where
  toFun A :=
    { toFun v := Multiplicative.ofAdd ((A : Matrix ι ι R) *ᵥ v.toAdd)
      invFun v := Multiplicative.ofAdd (((A⁻¹ : GL ι R) : Matrix ι ι R) *ᵥ v.toAdd)
      left_inv v := by simp
      right_inv v := by simp
      map_mul' v w := by simp [mulVec_add] }
  map_one' := by
    ext
    simp
  map_mul' A B := by
    ext
    simp

lemma GeneralLinearGroup.toAdd_mulVecMulAut_apply (A : GL ι R) (v : Multiplicative (ι → R)) :
    (GeneralLinearGroup.mulVecMulAut ι R A v).toAdd = (A : Matrix ι ι R) *ᵥ v.toAdd :=
  rfl

/-- The **affine general linear group** `AGL(ι, R) = R^ι ⋊ GL(ι, R)` (LMFDB
`group.affine_general_linear`), for the action of `GL(ι, R)` on `R^ι` by matrix multiplication;
for `R = GaloisField p r` with `r ≠ 0` and `ι = Fin n` it is `AGL(n, q)` with `q = p ^ r`. -/
abbrev AffineGeneralLinearGroup : Type _ :=
  Multiplicative (ι → R) ⋊[GeneralLinearGroup.mulVecMulAut ι R] GL ι R

end Matrix

namespace Matrix.AffineGeneralLinearGroup

/-- The homomorphism `GL(ι, R) → AGL(R^ι)` sending `A` to the linear automorphism `x ↦ A x`. -/
def linearAffineEquivHom : GL ι R →* ((ι → R) ≃ᵃ[R] (ι → R)) where
  toFun A :=
    (GeneralLinearGroup.generalLinearEquiv R (ι → R) (GeneralLinearGroup.toLin A)).toAffineEquiv
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp

lemma linearAffineEquivHom_apply (A : GL ι R) (x : ι → R) :
    linearAffineEquivHom ι R A x = (A : Matrix ι ι R) *ᵥ x := by
  simp [linearAffineEquivHom]

lemma constVAddHom_comp_mulVecMulAut (A : GL ι R) :
    (AffineEquiv.constVAddHom R (ι → R)).comp (GeneralLinearGroup.mulVecMulAut ι R A).toMonoidHom =
      (MulAut.conj (linearAffineEquivHom ι R A)).toMonoidHom.comp
        (AffineEquiv.constVAddHom R (ι → R)) := by
  ext v x
  simp [← map_inv, linearAffineEquivHom_apply, GeneralLinearGroup.toAdd_mulVecMulAut_apply,
    mulVec_add]

lemma linearMatrixHom_linearAffineEquivHom (A : GL ι R) :
    AffineEquiv.linearMatrixHom (linearAffineEquivHom ι R A) = A :=
  (congrArg GeneralLinearGroup.toLin.symm
    ((GeneralLinearGroup.generalLinearEquiv R (ι → R)).symm_apply_apply _)).trans
      (GeneralLinearGroup.toLin.symm_apply_apply A)

lemma linearMatrixHom_constVAddHom (v : Multiplicative (ι → R)) :
    AffineEquiv.linearMatrixHom (AffineEquiv.constVAddHom R (ι → R) v) = 1 := by
  simp [AffineEquiv.linearMatrixHom, ← LinearEquiv.one_eq_refl]

/-- The homomorphism `AGL(ι, R) → (R^ι ≃ᵃ[R] R^ι)` sending `(v, A)` to `x ↦ A x + v`. -/
def toAffineEquivHom : AffineGeneralLinearGroup ι R →* ((ι → R) ≃ᵃ[R] (ι → R)) :=
  lift _ _ (constVAddHom_comp_mulVecMulAut ι R)

lemma toAffineEquivHom_apply (g : AffineGeneralLinearGroup ι R) (x : ι → R) :
    toAffineEquivHom ι R g x = (g.right : Matrix ι ι R) *ᵥ x + g.left.toAdd := by
  simp [toAffineEquivHom, lift, linearAffineEquivHom_apply, add_comm]

lemma linearMatrixHom_toAffineEquivHom (g : AffineGeneralLinearGroup ι R) :
    AffineEquiv.linearMatrixHom (toAffineEquivHom ι R g) = g.right := by
  have h : toAffineEquivHom ι R g =
      AffineEquiv.constVAddHom R (ι → R) g.left * linearAffineEquivHom ι R g.right :=
    rfl
  rw [h, map_mul, linearMatrixHom_constVAddHom, linearMatrixHom_linearAffineEquivHom, one_mul]

/-- **`AGL(ι, R) = R^ι ⋊ GL(ι, R)` is the group of invertible affine transformations of `R^ι`**
(LMFDB `group.affine_general_linear`): the isomorphism sending `(v, A)` to `x ↦ A x + v`. -/
def mulEquivAffineEquiv : AffineGeneralLinearGroup ι R ≃* ((ι → R) ≃ᵃ[R] (ι → R)) where
  __ := toAffineEquivHom ι R
  invFun f := ⟨Multiplicative.ofAdd (f 0), AffineEquiv.linearMatrixHom f⟩
  left_inv g := by
    refine SemidirectProduct.ext ?_ (linearMatrixHom_toAffineEquivHom ι R g)
    have h : toAffineEquivHom ι R g 0 = g.left.toAdd := by
      rw [toAffineEquivHom_apply, mulVec_zero, zero_add]
    exact congrArg Multiplicative.ofAdd h
  right_inv f := AffineEquiv.ext fun x ↦ (toAffineEquivHom_apply ι R _ x).trans <| by
    rw [AffineEquiv.coe_linearMatrixHom]
    exact (AffineEquiv.apply_eq_mulVec_add f x).symm

lemma mulEquivAffineEquiv_apply (g : AffineGeneralLinearGroup ι R) (x : ι → R) :
    mulEquivAffineEquiv ι R g x = (g.right : Matrix ι ι R) *ᵥ x + g.left.toAdd :=
  toAffineEquivHom_apply ι R g x

end Matrix.AffineGeneralLinearGroup
