import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.GaloisCoefficients
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RepresentationTheory.Basic
import TauCeti.Algebra.Module.Torsion.TateModule

/-!
# The Galois representations of an abelian variety

Let `A` be an abelian variety over a field `K`, with absolute Galois group `G_K = Gal(Kˢ / K)`,
which acts on the points `A(Kˢ)` of `A` by group automorphisms
(`TauCeti.AlgebraicGeometry.AbelianVariety.PointCoeff`). It acts `ℤ / m`-linearly on the `m`-torsion
`A[m] = A(Kˢ)[m]` (`TauCeti.AlgebraicGeometry.AbelianVariety.TorsionCoeff`): this is the mod-`m`
Galois representation `G_K → Aut(A[m])` of `A`. It acts `ℤ_ℓ`-linearly on the `ℓ`-adic Tate module
`T_ℓ A = lim A[ℓⁿ]` (Tau Ceti's `TauCeti.TateModule` of the group `A(Kˢ)`), the inverse limit along
multiplication by `ℓ`: this is the `ℓ`-adic Galois representation `G_K → Aut(T_ℓ A)` of `A`. These
are the Galois representations attached to `A` (LMFDB `av.galois_rep`), in particular to the
Jacobian of a genus `2` curve (LMFDB `g2c.galois_rep`).

When `m` and `ℓ` are invertible in `K`, `A[m] ≅ (ℤ / m)^{2g}` and `T_ℓ A ≅ ℤ_ℓ^{2g}` for
`g = dim A`, so that in bases these representations take values in `GL_{2g}(ℤ / m)` and
`GL_{2g}(ℤ_ℓ)`, and the Weil pairing of a polarization of degree prime to `m` makes them take values
in the symplectic similitudes `GSp_{2g}`, up to conjugation. None of these facts is formalised here:
the `ℓ`-adic representation is stated basis-free, and the mod-`m` representation both basis-free
and, as a group homomorphism to `GL_n(ℤ / m)`, relative to a given basis of `A[m]` over `ℤ / m`.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.tateModuleRep` (LMFDB `av.galois_rep`,
  `g2c.galois_rep`): the `ℓ`-adic Galois representation of `G_K` on `T_ℓ A`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.torsionRep` (LMFDB `av.galois_rep`, `g2c.galois_rep`):
  the mod-`m` Galois representation of `G_K` on `A[m]`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.torsionRepMatrix` (LMFDB `av.galois_rep`,
  `g2c.galois_rep`): the mod-`m` Galois representation `G_K → GL_n(ℤ / m)` in a basis of `A[m]`.

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.coe_proj_tateModuleRep`: on the level `A[ℓⁿ]`, the
  `ℓ`-adic representation is the action of `G_K` on points.
* `TauCeti.AlgebraicGeometry.AbelianVariety.torsionRepMatrix_apply`: the matrix of `σ ∈ G_K` in a
  basis of `A[m]` is the matrix of its action on `A[m]`.
-/

open AddSubgroup

universe u

namespace TauCeti.AlgebraicGeometry.AbelianVariety

variable {K : Type u} [Field K] (A : AbelianVariety K) {L : Type u} [Field L] [Algebra K L]
  (m ℓ : ℕ) [Fact ℓ.Prime] (σ : AbsoluteGaloisGroup K)

/-- The **`ℓ`-adic Galois representation** (LMFDB `av.galois_rep`, `g2c.galois_rep`) of an abelian
variety `A` over `K`: the representation of the absolute Galois group `G_K = Gal(Kˢ / K)` on the
`ℓ`-adic Tate module `T_ℓ A = lim A(Kˢ)[ℓⁿ]` of `A` (Tau Ceti's `TauCeti.TateModule` of the group
`A(Kˢ)`), by which `σ ∈ G_K` acts on every level `A(Kˢ)[ℓⁿ]` through its action on points. When `ℓ`
is invertible in `K`, `T_ℓ A` is free of rank `2 dim A` over `ℤ_ℓ` (not formalised), so that this
is a representation `G_K → GL_{2 dim A}(ℤ_ℓ)` up to conjugation. -/
noncomputable def tateModuleRep :
    Representation ℤ_[ℓ] (AbsoluteGaloisGroup K) (TateModule ℓ (A.PointCoeff K)) where
  toFun σ := TateModule.mapLinearMap (DistribSMul.toAddMonoidHom (A.PointCoeff K) σ)
  map_one' := LinearMap.ext fun x ↦ TateModule.ext fun n ↦ Subtype.ext <|
    one_smul (AbsoluteGaloisGroup K) (TateModule.proj n x : A.PointCoeff K)
  map_mul' σ τ := LinearMap.ext fun x ↦ TateModule.ext fun n ↦ Subtype.ext <|
    mul_smul σ τ (TateModule.proj n x : A.PointCoeff K)

variable {A ℓ} in
/-- **The `ℓ`-adic representation on the level `A[ℓⁿ]`**: the `n`-th component of `σ x` is the
image of the `n`-th component of `x` under the action of `σ` on points. -/
lemma coe_proj_tateModuleRep (x : TateModule ℓ (A.PointCoeff K)) (n : ℕ) :
    (TateModule.proj n (A.tateModuleRep ℓ σ x) : A.PointCoeff K) =
      σ • (TateModule.proj n x : A.PointCoeff K) :=
  (rfl)

noncomputable instance : Module (ZMod m) (A.TorsionCoeff L m) :=
  torsionBy.zmodModule

/-- The **mod-`m` Galois representation** (LMFDB `av.galois_rep`, `g2c.galois_rep`) of an abelian
variety `A` over `K`: the representation of the absolute Galois group `G_K = Gal(Kˢ / K)` on the
`m`-torsion `A[m] = A(Kˢ)[m]` of the points of `A`, a module over `ℤ / m`. When `m` is invertible
in `K`, `A[m]` is free of rank `2 dim A` over `ℤ / m` (not formalised), so that this is a
representation `G_K → GL_{2 dim A}(ℤ / m)` up to conjugation (`torsionRepMatrix`). -/
noncomputable def torsionRep :
    Representation (ZMod m) (AbsoluteGaloisGroup K) (A.TorsionCoeff K m) where
  toFun σ := (DistribSMul.toAddMonoidHom (A.TorsionCoeff K m) σ).toZModLinearMap m
  map_one' := LinearMap.ext <| one_smul _
  map_mul' σ τ := LinearMap.ext <| mul_smul σ τ

variable {A m} in
lemma torsionRep_apply (x : A.TorsionCoeff K m) : A.torsionRep m σ x = σ • x :=
  rfl

variable {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n (ZMod m) (A.TorsionCoeff K m))

/-- The **mod-`m` Galois representation in a basis** (LMFDB `av.galois_rep`, `g2c.galois_rep`) of
an abelian variety `A` over `K`: the group homomorphism `G_K → GL_n(ℤ / m)` sending `σ` to the
matrix of its action on `A[m] = A(Kˢ)[m]` (`torsionRep`) in a basis `b` of `A[m]` over `ℤ / m`.
When `m` is invertible in `K`, `n = 2 dim A`. Another basis gives a conjugate homomorphism. -/
noncomputable def torsionRepMatrix : AbsoluteGaloisGroup K →* GL n (ZMod m) :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom).comp
    (A.torsionRep m).asGroupHom

variable {A m} in
/-- **The matrix of the mod-`m` Galois representation**: `σ ∈ G_K` goes to the matrix of its action
on `A[m]` in the basis `b`. -/
lemma torsionRepMatrix_apply :
    (A.torsionRepMatrix m b σ : Matrix n n (ZMod m)) = LinearMap.toMatrix b b (A.torsionRep m σ) :=
  rfl

end TauCeti.AlgebraicGeometry.AbelianVariety
