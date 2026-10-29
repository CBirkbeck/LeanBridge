import LeanBridge.ForMathlib.LinearAlgebra.AffineSpace.AffineGroup
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.SemilinearGroup

/-!
# Affine linear groups twisted by field automorphisms

The automorphisms `σ` of a commutative `K`-algebra `F` act on the affine general linear group
`AGL(F^ι)` of affine automorphisms of `F^ι = ι → F` by conjugation with their coordinatewise action
`x ↦ σ(x)`: the conjugate of `x ↦ M x + v` is `x ↦ σ(M) x + σ(v)`, with `σ` applied to the entries.
This action preserves the affine special linear group `ASL(F^ι)`. The affine general and special
semilinear groups are the semidirect products `AΓL(F^ι) = AGL(F^ι) ⋊ Aut(F/K)` and
`AΣL(F^ι) = ASL(F^ι) ⋊ Aut(F/K)`.

For `K = 𝔽_p` and `F = 𝔽_q`, that is `ZMod p` and `GaloisField p r` with `r ≠ 0` and `q = p ^ r`,
and `ι = Fin n`, these are the LMFDB's `AΓL(n, q)` and `AΣL(n, q)`: every field automorphism of
`𝔽_q` fixes `𝔽_p`, so `Aut(F/K)` is the group `Aut(𝔽_q/𝔽_p)` of field automorphisms of `𝔽_q`.

## Main definitions

* `MonoidHom.restrictMulAut`: the restriction of an action by automorphisms to an invariant
  subgroup.
* `AffineEquiv.conjAlgEquiv`, `AffineEquiv.conjAlgEquivHom`: the action of `Aut(F/K)` on `AGL(F^ι)`.
* `AffineEquiv.AffineGeneralSemilinearGroup` (LMFDB `group.affine_linear_automorphism`):
  `AΓL(F^ι)`.
* `AffineEquiv.AffineSpecialSemilinearGroup` (LMFDB `group.affine_linear_automorphism`):
  `AΣL(F^ι)`.

## Main results

* `AffineEquiv.conjAlgEquiv_apply_eq_mulVec_add`: the conjugate of `x ↦ M x + v` by `σ` is
  `x ↦ σ(M) x + σ(v)`.
* `AffineEquiv.conjAlgEquiv_mem_affineSpecialLinearGroup`: the action preserves `ASL(F^ι)`.
-/

open Matrix

variable {G N : Type*} [Group G] [Group N]

/-- The restriction of an action `φ` of `G` on `N` by automorphisms to a subgroup `H` of `N` that
every `φ g` maps into itself. -/
def MonoidHom.restrictMulAut (φ : G →* MulAut N) (H : Subgroup N) (hH : ∀ g, ∀ n ∈ H, φ g n ∈ H) :
    G →* MulAut H where
  toFun g :=
    { toFun n := ⟨φ g n, hH g n n.2⟩
      invFun n := ⟨(φ g).symm n, by simpa using hH g⁻¹ n n.2⟩
      left_inv n := Subtype.ext <| (φ g).symm_apply_apply (n : N)
      right_inv n := Subtype.ext <| (φ g).apply_symm_apply (n : N)
      map_mul' a b := Subtype.ext <| map_mul (φ g) (a : N) b }
  map_one' := by
    ext
    simp
  map_mul' a b := by
    ext
    simp

namespace AffineEquiv

variable {ι K F : Type*} [CommSemiring K] [CommRing F] [Algebra K F] (σ : F ≃ₐ[K] F)
    (f : (ι → F) ≃ᵃ[F] (ι → F)) (x : ι → F) (i : ι)

/-- The conjugate `x ↦ σ (f (σ⁻¹ x))` of an affine automorphism `f` of `ι → F` by the
coordinatewise action of an automorphism `σ` of `F` over `K`. -/
def conjAlgEquiv : (ι → F) ≃ᵃ[F] (ι → F) :=
  letI e : (ι → F) ≃ₐ[K] (ι → F) := AlgEquiv.piCongrRight fun _ ↦ σ
  { toFun x := e (f (e.symm x))
    invFun x := e (f.symm (e.symm x))
    left_inv x := by
      simp
    right_inv x := by
      simp
    linear :=
      { toFun x := e (f.linear (e.symm x))
        invFun x := e (f.linear.symm (e.symm x))
        map_add' x y := by
          simp
        map_smul' c x := by
          have h₁ (d : F) (y : ι → F) : e (d • y) = σ d • e y :=
            funext fun j ↦ map_mul σ d (y j)
          have h₂ (d : F) (y : ι → F) : e.symm (d • y) = σ.symm d • e.symm y :=
            funext fun j ↦ map_mul σ.symm d (y j)
          simp [h₁, h₂]
        left_inv x := by
          simp
        right_inv x := by
          simp }
    map_vadd' p v := by
      have h (a b : ι → F) : f (a + b) = f.linear a + f b :=
        f.map_vadd b a
      simp [h] }

lemma conjAlgEquiv_apply : f.conjAlgEquiv σ x i = σ (f (fun j ↦ σ.symm (x j)) i) :=
  rfl

lemma conjAlgEquiv_linear_apply :
    (f.conjAlgEquiv σ).linear x i = σ (f.linear (fun j ↦ σ.symm (x j)) i) :=
  rfl

variable (ι K F) in
/-- The action of the automorphisms of `F` over `K` on the affine group of `ι → F`, by conjugation
with their coordinatewise action. -/
def conjAlgEquivHom : (F ≃ₐ[K] F) →* MulAut ((ι → F) ≃ᵃ[F] (ι → F)) where
  toFun σ :=
    { toFun := conjAlgEquiv σ
      invFun := conjAlgEquiv σ.symm
      left_inv f := by
        ext
        simp [conjAlgEquiv_apply]
      right_inv f := by
        ext
        simp [conjAlgEquiv_apply]
      map_mul' f g := by
        ext
        simp [conjAlgEquiv_apply] }
  map_one' := by
    ext
    simp [conjAlgEquiv_apply, ← AlgEquiv.aut_inv]
  map_mul' σ τ := by
    ext
    simp [conjAlgEquiv_apply, ← AlgEquiv.aut_inv]

variable [Fintype ι] [DecidableEq ι]

lemma linearMatrixHom_conjAlgEquiv :
    linearMatrixHom (f.conjAlgEquiv σ) = GeneralLinearGroup.entrywiseAut σ (linearMatrixHom f) := by
  have h (j : ι) : (fun k ↦ σ.symm ((Pi.single j 1 : ι → F) k)) = Pi.single j 1 :=
    funext fun k ↦ (Pi.apply_single (fun _ ↦ σ.symm) (fun _ ↦ map_zero σ.symm) j 1 k).trans <| by
      rw [map_one]
  ext i j
  simp [coe_linearMatrixHom, GeneralLinearGroup.entrywiseAut, conjAlgEquiv_linear_apply, h]

/-- **The conjugate of `x ↦ M x + v` by `σ` is `x ↦ σ(M) x + σ(v)`**, with `σ` applied to the
entries of `M` and `v`. -/
lemma conjAlgEquiv_apply_eq_mulVec_add : f.conjAlgEquiv σ x =
    (LinearMap.toMatrix' (f.linear : (ι → F) →ₗ[F] (ι → F))).map σ *ᵥ x + fun j ↦ σ (f 0 j) := by
  rw [(f.conjAlgEquiv σ).apply_eq_mulVec_add, ← coe_linearMatrixHom, linearMatrixHom_conjAlgEquiv,
    GeneralLinearGroup.coe_entrywiseAut, coe_linearMatrixHom]
  congr 1
  ext j
  simp [conjAlgEquiv_apply, ← Pi.zero_def]

variable {f} in
/-- **The action of `Aut(F/K)` on `AGL(F^ι)` preserves `ASL(F^ι)`**: `det σ(M) = σ(det M)`. -/
lemma conjAlgEquiv_mem_affineSpecialLinearGroup (hf : f ∈ affineSpecialLinearGroup F (ι → F)) :
    f.conjAlgEquiv σ ∈ affineSpecialLinearGroup F (ι → F) := by
  rw [mem_affineSpecialLinearGroup_iff_det, ← coe_linearMatrixHom] at hf ⊢
  rw [linearMatrixHom_conjAlgEquiv, GeneralLinearGroup.coe_entrywiseAut]
  simpa [hf] using ((σ : F →+* F).map_det (linearMatrixHom f : Matrix ι ι F)).symm

variable (ι K F)

/-- The **affine general semilinear group** `AΓL(F^ι) = AGL(F^ι) ⋊ Aut(F/K)` (LMFDB
`group.affine_linear_automorphism`): the semidirect product of the affine general linear group of
affine automorphisms of `ι → F` with the automorphisms of `F` over `K`, acting by conjugation with
their coordinatewise action. The knowl leaves the action implicit; this is the standard one, for
which `(f, σ)` stands for the affine semilinear map `x ↦ f (σ x)`. For `ι = Fin n`, `K = ZMod p`
and `F = GaloisField p r` with `r ≠ 0`, it is `AΓL(n, q)` with `q = p ^ r`. -/
abbrev AffineGeneralSemilinearGroup : Type _ :=
  ((ι → F) ≃ᵃ[F] (ι → F)) ⋊[conjAlgEquivHom ι K F] (F ≃ₐ[K] F)

/-- The **affine special semilinear group** `AΣL(F^ι) = ASL(F^ι) ⋊ Aut(F/K)` (LMFDB
`group.affine_linear_automorphism`): the semidirect product of the affine special linear group of
`ι → F` with the automorphisms of `F` over `K`, acting by conjugation with their coordinatewise
action, which preserves it. For `ι = Fin n`, `K = ZMod p` and `F = GaloisField p r` with `r ≠ 0`,
it is `AΣL(n, q)` with `q = p ^ r`. -/
abbrev AffineSpecialSemilinearGroup : Type _ :=
  affineSpecialLinearGroup F (ι → F) ⋊[(conjAlgEquivHom ι K F).restrictMulAut _
    fun σ _ ↦ conjAlgEquiv_mem_affineSpecialLinearGroup σ] (F ≃ₐ[K] F)

end AffineEquiv
