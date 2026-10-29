import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.Determinant
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# Affine special linear and affine symplectic groups

The affine general linear group `AGL(V)` of a module `V` over a commutative ring `R` is Mathlib's
group `V ≃ᵃ[R] V` of affine automorphisms of `V` (`AffineEquiv.group`). For `V = R^ι` every affine
automorphism is `x ↦ M x + v`, with `M` the matrix of its linear part and `v` the image of `0`
(`AffineEquiv.apply_eq_mulVec_add`), so for `R = 𝔽_q` and `ι = Fin n` this is the LMFDB's
`AGL(n, q) = 𝔽_q^n ⋊ GL(n, q)`. This file defines two of its subgroups: the affine special linear
group `ASL(V)` of the automorphisms whose linear part has determinant `1`, and the affine symplectic
group `ASp(2m, R)` of the automorphisms of `R^{2m}` whose linear part is symplectic. For `R = 𝔽_q`,
that is `GaloisField p r` with `r ≠ 0` and `q = p ^ r`, these are the LMFDB's `ASL(n, q)` and
`ASp(2m, q)`; as in the LMFDB, the first argument of `ASp` and `Sp` is the dimension, which is even.

## Main definitions

* `AffineEquiv.affineSpecialLinearGroup` (LMFDB `group.affine_special_linear`): `ASL(V)`.
* `AffineEquiv.linearMatrixHom`: the matrix `M` of the linear part, as a homomorphism
  `AGL(R^ι) → GL_ι(R)`.
* `AffineEquiv.affineSymplecticGroup` (LMFDB `group.affine_symplectic`): `ASp(2m, R)`.

## Main results

* `AffineEquiv.apply_eq_mulVec_add`: an affine automorphism of `R^ι` is `x ↦ M x + v`.
* `AffineEquiv.mem_affineSpecialLinearGroup_iff_det`: the automorphism `x ↦ M x + v` lies in `ASL`
  if and only if `det M = 1`.
* `AffineEquiv.mem_affineSymplecticGroup_iff`: the automorphism `x ↦ M x + v` lies in `ASp` if and
  only if `M` lies in the symplectic group `Sp(2m, R)`.
-/

open LinearMap Matrix

namespace AffineEquiv

variable {ι l R V : Type*} [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] [CommRing R]
    [AddCommGroup V] [Module R V] (f : (ι → R) ≃ᵃ[R] (ι → R))

variable (R V) in
/-- The **affine special linear group** `ASL(V)` (LMFDB `group.affine_special_linear`) of a module
`V` over a commutative ring `R`: the subgroup of the affine general linear group `AGL(V)` of the
affine automorphisms `x ↦ M x + v` of `V` whose linear part `M` has determinant `1`, the kernel of
the determinant of the linear part. For `R = GaloisField p r` with `r ≠ 0` and `V = Fin n → R`, it
is `ASL(n, q)` with `q = p ^ r`. Mathlib's determinant `LinearMap.det` is `1` on a module without a
finite basis, so there `ASL(V)` is all of `AGL(V)`. -/
noncomputable def affineSpecialLinearGroup : Subgroup (V ≃ᵃ[R] V) :=
  (LinearEquiv.det.comp linearHom).ker

lemma mem_affineSpecialLinearGroup_iff {g : V ≃ᵃ[R] V} :
    g ∈ affineSpecialLinearGroup R V ↔ LinearMap.det (g.linear : V →ₗ[R] V) = 1 := by
  rw [affineSpecialLinearGroup, MonoidHom.mem_ker, MonoidHom.comp_apply, linearHom_apply,
    Units.ext_iff, LinearEquiv.coe_det, Units.val_one]

/-- **An affine automorphism of `R^ι` is `x ↦ M x + v`**, with `M` the matrix of its linear part
and `v` the image of `0`. -/
lemma apply_eq_mulVec_add (x : ι → R) :
    f x = LinearMap.toMatrix' (f.linear : (ι → R) →ₗ[R] (ι → R)) *ᵥ x + f 0 := by
  rw [LinearMap.toMatrix'_mulVec]
  simpa using f.map_vadd 0 x

/-- The matrix of the linear part of an affine automorphism of `R^ι`, as a homomorphism
`AGL(R^ι) → GL_ι(R)`. -/
def linearMatrixHom : ((ι → R) ≃ᵃ[R] (ι → R)) →* GL ι R :=
  ((GeneralLinearGroup.generalLinearEquiv R (ι → R)).symm.trans
    GeneralLinearGroup.toLin.symm).toMonoidHom.comp linearHom

lemma coe_linearMatrixHom :
    (linearMatrixHom f : Matrix ι ι R) = LinearMap.toMatrix' (f.linear : (ι → R) →ₗ[R] (ι → R)) :=
  rfl

variable {f} in
/-- **The automorphism `x ↦ M x + v` of `R^ι` lies in `ASL` if and only if `det M = 1`** (LMFDB
`group.affine_special_linear`). -/
lemma mem_affineSpecialLinearGroup_iff_det : f ∈ affineSpecialLinearGroup R (ι → R) ↔
    (LinearMap.toMatrix' (f.linear : (ι → R) →ₗ[R] (ι → R))).det = 1 := by
  rw [mem_affineSpecialLinearGroup_iff, LinearMap.det_toMatrix']

variable (l R) in
/-- The **affine symplectic group** `ASp(2m, R)` (LMFDB `group.affine_symplectic`) of
`R^{2m} = R^{l ⊕ l}`, `m` the cardinality of `l`: the subgroup of the affine general linear group
of the affine automorphisms `x ↦ M x + v` whose linear part `M` lies in the symplectic group
`Sp(2m, R)` (Mathlib's `Matrix.symplecticGroup l R`, the matrices with `M J Mᵀ = J`, as Tau Ceti's
subgroup `TauCeti.GLSymplectic l R` of `GL_{2m}(R)`). Mathlib's `J` is minus the LMFDB's example
form `Ω`, and `M J Mᵀ = J` is equivalent to `Mᵀ J M = J`, so this is the LMFDB's condition
`Mᵀ Ω M = Ω`. For `R = GaloisField p r` with `r ≠ 0` and `l = Fin m`, it is the LMFDB's
`ASp(n, q)` with `n = 2m` and `q = p ^ r`. -/
def affineSymplecticGroup : Subgroup ((l ⊕ l → R) ≃ᵃ[R] (l ⊕ l → R)) :=
  (TauCeti.GLSymplectic l R).comap linearMatrixHom

/-- **The automorphism `x ↦ M x + v` of `R^{2m}` lies in `ASp(2m, R)` if and only if `M` lies in
`Sp(2m, R)`** (LMFDB `group.affine_symplectic`). -/
lemma mem_affineSymplecticGroup_iff {g : (l ⊕ l → R) ≃ᵃ[R] (l ⊕ l → R)} :
    g ∈ affineSymplecticGroup l R ↔
      LinearMap.toMatrix' (g.linear : (l ⊕ l → R) →ₗ[R] (l ⊕ l → R)) ∈ symplecticGroup l R :=
  Iff.rfl

end AffineEquiv
