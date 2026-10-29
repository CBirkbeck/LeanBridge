import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Linear groups twisted by field automorphisms

The automorphisms of a commutative `K`-algebra `F` act entrywise on the matrix groups `GL_n(F)` and
`SL_n(F)`. The general and special semilinear groups are the semidirect products
`ΓL_n(F) = GL_n(F) ⋊ Aut(F/K)` and `ΣL_n(F) = SL_n(F) ⋊ Aut(F/K)`, and the projective ones,
`PΓL_n(F)` and `PΣL_n(F)`, are their quotients by their subgroups of scalar matrices `(λ I, 1)`.

For `K = 𝔽_p` and `F = 𝔽_q`, that is `ZMod p` and `GaloisField p r` with `r ≠ 0` and `q = p ^ r`,
these are the LMFDB's `ΓL(n, q)`, `ΣL(n, q)`, `PΓL(n, q)` and `PΣL(n, q)`: every field automorphism
of `𝔽_q` fixes `𝔽_p`, so `Aut(F/K)` is the group `Aut(𝔽_q/𝔽_p)` of field automorphisms of `𝔽_q`.

The scalar matrices of `GL_n(F)` form its centre
(`Matrix.GeneralLinearGroup.center_eq_range_scalar`), and the scalar matrices of `SL_n(F)`, the
`λ I` with `λ ^ n = 1`, form the centre of `SL_n(F)` (`Matrix.SpecialLinearGroup.mem_center_iff`).
So the scalar subgroups of `ΓL_n(F)` and `ΣL_n(F)` are the images of these centres. They are
normal, since the image of a characteristic subgroup of `N` in a semidirect product `N ⋊ G` is
normal.

## Main definitions

* `Matrix.GeneralLinearGroup.entrywiseAut`, `Matrix.SpecialLinearGroup.entrywiseAut`: the
  entrywise actions of `Aut(F/K)` on `GL_n(F)` and `SL_n(F)`.
* `Matrix.GeneralSemilinearGroup` (LMFDB `group.linear_automorphism`): `ΓL_n(F)`.
* `Matrix.SpecialSemilinearGroup` (LMFDB `group.linear_automorphism`): `ΣL_n(F)`.
* `Matrix.ProjectiveGeneralSemilinearGroup` (LMFDB `group.linear_automorphism`): `PΓL_n(F)`.
* `Matrix.ProjectiveSpecialSemilinearGroup` (LMFDB `group.linear_automorphism`): `PΣL_n(F)`.

## Main results

* The instance `(H.map SemidirectProduct.inl).Normal` for a characteristic subgroup `H` of `N`.
-/

open SemidirectProduct (inl)

namespace SemidirectProduct

variable {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}

instance (H : Subgroup N) [hH : H.Characteristic] : (H.map (inl : N →* N ⋊[φ] G)).Normal where
  conj_mem x hx g := by
    rcases hx with ⟨h, hh, rfl⟩
    refine ⟨g.left * φ g.right h * g.left⁻¹, (inferInstance : H.Normal).conj_mem _ ?_ _, ?_⟩
    · exact (hH.fixed (φ g.right)).ge hh
    · ext <;> simp

end SemidirectProduct

namespace Matrix

variable {n K F : Type*} [Fintype n] [DecidableEq n] [CommSemiring K] [CommRing F] [Algebra K F]

/-- The entrywise action `σ • M = (σ (M i j))` of the automorphisms of `F` over `K` on `GL_n(F)`. -/
def GeneralLinearGroup.entrywiseAut : (F ≃ₐ[K] F) →* MulAut (GL n F) where
  toFun σ := Units.mapEquiv σ.mapMatrix.toMulEquiv
  map_one' := by
    ext
    simp
  map_mul' σ τ := by
    ext
    simp

lemma GeneralLinearGroup.coe_entrywiseAut (σ : F ≃ₐ[K] F) (g : GL n F) :
    (entrywiseAut σ g : Matrix n n F) = (g : Matrix n n F).map σ :=
  rfl

/-- The entrywise action `σ • M = (σ (M i j))` of the automorphisms of `F` over `K` on `SL_n(F)`. -/
def SpecialLinearGroup.entrywiseAut : (F ≃ₐ[K] F) →* MulAut (SpecialLinearGroup n F) where
  toFun σ :=
    { toFun := SpecialLinearGroup.map (σ : F →+* F)
      invFun := SpecialLinearGroup.map (σ.symm : F →+* F)
      left_inv M := by
        ext
        simp
      right_inv M := by
        ext
        simp
      map_mul' := map_mul _ }
  map_one' := by
    ext
    simp
  map_mul' σ τ := by
    ext
    simp

variable (n K F)

/-- The **general semilinear group** `ΓL_n(F) = GL_n(F) ⋊ Aut(F/K)` (LMFDB
`group.linear_automorphism`), the automorphisms of `F` over `K` acting entrywise. For `K = ZMod p`
and `F = GaloisField p r` with `r ≠ 0`, it is `ΓL(n, q)` with `q = p ^ r`. -/
abbrev GeneralSemilinearGroup : Type _ :=
  GL n F ⋊[GeneralLinearGroup.entrywiseAut] (F ≃ₐ[K] F)

/-- The **special semilinear group** `ΣL_n(F) = SL_n(F) ⋊ Aut(F/K)` (LMFDB
`group.linear_automorphism`), the automorphisms of `F` over `K` acting entrywise. For `K = ZMod p`
and `F = GaloisField p r` with `r ≠ 0`, it is `ΣL(n, q)` with `q = p ^ r`. -/
abbrev SpecialSemilinearGroup : Type _ :=
  SpecialLinearGroup n F ⋊[SpecialLinearGroup.entrywiseAut] (F ≃ₐ[K] F)

/-- The **projective general semilinear group** `PΓL_n(F)` (LMFDB `group.linear_automorphism`):
the quotient of `ΓL_n(F)` by its subgroup of scalar matrices `(λ I, 1)`, the image of the centre of
`GL_n(F)`. For `K = ZMod p` and `F = GaloisField p r` with `r ≠ 0`, it is `PΓL(n, q)` with
`q = p ^ r`. -/
abbrev ProjectiveGeneralSemilinearGroup : Type _ :=
  GeneralSemilinearGroup n K F ⧸ (Subgroup.center (GL n F)).map inl

/-- The **projective special semilinear group** `PΣL_n(F)` (LMFDB `group.linear_automorphism`):
the quotient of `ΣL_n(F)` by its subgroup of scalar matrices `(λ I, 1)` with `λ ^ n = 1`, the image
of the centre of `SL_n(F)`. For `K = ZMod p` and `F = GaloisField p r` with `r ≠ 0`, it is
`PΣL(n, q)` with `q = p ^ r`. -/
abbrev ProjectiveSpecialSemilinearGroup : Type _ :=
  SpecialSemilinearGroup n K F ⧸ (Subgroup.center (SpecialLinearGroup n F)).map inl

end Matrix
