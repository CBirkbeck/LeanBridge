import Mathlib.LinearAlgebra.Matrix.Basis
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Galois
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Galois

/-!
# The Galois representations attached to an elliptic curve, in matrix form

Let `W` be an elliptic curve over a field `F` and `K` an extension of `F`, typically a separable
closure. Tau Ceti provides the action of `K ≃ₐ[F] K` on the `m`-torsion `E[m]` of `W` over `K`
(`WeierstrassCurve.torsionGaloisAction`, the mod-`m` representation into `Aut(E[m])`) and on its
`ℓ`-adic Tate module (`WeierstrassCurve.tateModuleGaloisRepresentation`). Every additive
automorphism of `E[m]` is `ℤ/mℤ`-linear, so the mod-`m` representation takes values in
`GL_{ℤ/mℤ}(E[m])`; when `E[m]` is free of rank `2` (for `K` separably closed and `m` invertible in
`K`, `WeierstrassCurve.nonempty_basis_torsionBy`) a basis turns it into a homomorphism to
`GL₂(ℤ/mℤ)`, well defined up to conjugation. In the same way a basis of the Tate module turns the
`ℓ`-adic representation into a homomorphism to `GL₂(ℤ_ℓ)`, and bases of all the Tate modules give
the adelic representation, with values in `∏_ℓ GL₂(ℤ_ℓ) = GL₂(ℤ̂)`.

## Main definitions

* `WeierstrassCurve.modGaloisRepresentation` (LMFDB `ec.galois_rep`): the mod-`m` representation,
  into the `ℤ/mℤ`-linear automorphisms of `E[m]`.
* `WeierstrassCurve.modGaloisRepresentationGL` (LMFDB `ec.galois_rep`): the same in a basis of
  `E[m]`, into `GL₂(ℤ/mℤ)`.
* `WeierstrassCurve.tateModuleGaloisRepresentationGL` (LMFDB `ec.galois_rep`): the `ℓ`-adic
  representation in a basis of `T_ℓ E`, into `GL₂(ℤ_ℓ)`.
* `WeierstrassCurve.adelicGaloisRepresentationGL` (LMFDB `ec.galois_rep`): the adelic
  representation, into `∏_ℓ GL₂(ℤ_ℓ) = GL₂(ℤ̂)`.

## Main results

* `Matrix.GeneralLinearGroup.exists_toLin'_symm_eq_conj`: the matrices of an automorphism in two
  bases are conjugate by a single change-of-basis matrix.
* `WeierstrassCurve.exists_modGaloisRepresentationGL_eq_conj`,
  `WeierstrassCurve.exists_tateModuleGaloisRepresentationGL_eq_conj` and
  `WeierstrassCurve.exists_adelicGaloisRepresentationGL_eq_conj`: the matrix representations are
  well defined up to conjugation.
-/

open Matrix TauCeti LinearMap.GeneralLinearGroup WeierstrassCurve.Affine
open scoped WeierstrassCurve

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R] {V : Type*}
  [AddCommGroup V] [Module R V] (b b' : Module.Basis n R V)

lemma coe_toLin'_symm (φ : LinearMap.GeneralLinearGroup R V) :
    ((toLin' b).symm φ : Matrix n n R) = LinearMap.toMatrix b b (φ : V →ₗ[R] V) := by
  have h : ((toLin' b ((toLin' b).symm φ) : LinearMap.GeneralLinearGroup R V) : V →ₗ[R] V) =
      Matrix.toLin b b ((toLin' b).symm φ) := by
    refine LinearMap.ext fun v ↦ ?_
    rw [Matrix.toLin_apply, ← coe_toLinearEquiv, toLin'_apply, Fintype.linearCombination_apply]
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, LinearMap.toMatrix_toLin]

/-- **The matrices of an automorphism in two bases are conjugate**, by the change-of-basis
matrix, which does not depend on the automorphism. -/
lemma exists_toLin'_symm_eq_conj : ∃ P : GL n R, ∀ φ : LinearMap.GeneralLinearGroup R V,
    (toLin' b').symm φ = P * (toLin' b).symm φ * P⁻¹ := by
  refine ⟨⟨b'.toMatrix b, b.toMatrix b', b'.toMatrix_mul_toMatrix_flip b,
    b.toMatrix_mul_toMatrix_flip b'⟩, fun φ ↦ Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, coe_toLin'_symm, coe_toLin'_symm, Units.inv_mk,
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]

end Matrix.GeneralLinearGroup

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K] (W : WeierstrassCurve F)

section Torsion

variable (m : ℕ)
  (b b' : Module.Basis (Fin 2) (ZMod m) (AddSubgroup.torsionBy (W⁄K).toAffine.Point (m : ℤ)))

/-- The **mod-`m` Galois representation** (LMFDB `ec.galois_rep`) of an elliptic curve `W` over
`F`: the action of `K ≃ₐ[F] K` on the `m`-torsion `E[m]` of `W` over `K`, by `ℤ/mℤ`-linear
automorphisms. It is Tau Ceti's `WeierstrassCurve.torsionGaloisAction`, every additive
automorphism of `E[m]` being `ℤ/mℤ`-linear; for `K` an algebraic closure of `F` it is the
representation `Gal(F̄/F) → Aut(E[m])` of the LMFDB. -/
noncomputable def modGaloisRepresentation : (K ≃ₐ[F] K) →* LinearMap.GeneralLinearGroup (ZMod m)
    (AddSubgroup.torsionBy (W⁄K).toAffine.Point (m : ℤ)) where
  toFun σ := ofLinearEquiv
    ((Multiplicative.toAdd (W.torsionGaloisAction (m : ℤ) σ)).toLinearEquiv (ZMod.map_smul _))
  map_one' := by
    ext P
    simp
  map_mul' σ τ := by
    ext P
    simp

lemma modGaloisRepresentation_apply_coe (σ : K ≃ₐ[F] K)
    (P : AddSubgroup.torsionBy (W⁄K).toAffine.Point (m : ℤ)) :
    ((W.modGaloisRepresentation m σ).val P : (W⁄K).toAffine.Point) = Point.map σ.toAlgHom P := by
  simp [modGaloisRepresentation]

/-- The **mod-`m` Galois representation in a basis** (LMFDB `ec.galois_rep`): given a basis `b` of
`E[m]` over `ℤ/mℤ`, the mod-`m` representation as a homomorphism to `GL₂(ℤ/mℤ)`. Another basis
conjugates it (`exists_modGaloisRepresentationGL_eq_conj`). -/
noncomputable def modGaloisRepresentationGL : (K ≃ₐ[F] K) →* GL (Fin 2) (ZMod m) :=
  (GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp (W.modGaloisRepresentation m)

/-- The mod-`m` representation in a basis is **well defined up to conjugation**. -/
lemma exists_modGaloisRepresentationGL_eq_conj : ∃ P : GL (Fin 2) (ZMod m), ∀ σ : K ≃ₐ[F] K,
    W.modGaloisRepresentationGL m b' σ = P * W.modGaloisRepresentationGL m b σ * P⁻¹ := by
  rcases GeneralLinearGroup.exists_toLin'_symm_eq_conj b b' with ⟨P, hP⟩
  exact ⟨P, fun σ ↦ hP _⟩

end Torsion

section TateModule

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (b b' : Module.Basis (Fin 2) ℤ_[ℓ] (TateModule ℓ (W⁄K).toAffine.Point))

/-- The **`ℓ`-adic Galois representation in a basis** (LMFDB `ec.galois_rep`): given a basis `b` of
the Tate module `T_ℓ E` over `ℤ_ℓ`, Tau Ceti's `WeierstrassCurve.tateModuleGaloisRepresentation` as
a homomorphism to `GL₂(ℤ_ℓ)`. Another basis conjugates it
(`exists_tateModuleGaloisRepresentationGL_eq_conj`). -/
noncomputable def tateModuleGaloisRepresentationGL : (K ≃ₐ[F] K) →* GL (Fin 2) ℤ_[ℓ] :=
  (GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp
    (W.tateModuleGaloisRepresentation ℓ).asGroupHom

/-- The `ℓ`-adic representation in a basis is **well defined up to conjugation**. -/
lemma exists_tateModuleGaloisRepresentationGL_eq_conj : ∃ P : GL (Fin 2) ℤ_[ℓ], ∀ σ : K ≃ₐ[F] K,
    W.tateModuleGaloisRepresentationGL ℓ b' σ = P * W.tateModuleGaloisRepresentationGL ℓ b σ *
    P⁻¹ := by
  rcases GeneralLinearGroup.exists_toLin'_symm_eq_conj b b' with ⟨P, hP⟩
  exact ⟨P, fun σ ↦ hP _⟩

end TateModule

variable (b b' : ∀ ℓ : Nat.Primes, Module.Basis (Fin 2) ℤ_[ℓ] (TateModule ℓ (W⁄K).toAffine.Point))

/-- The **adelic Galois representation** (LMFDB `ec.galois_rep`): given a basis `b ℓ` of every
Tate module `T_ℓ E` over `ℤ_ℓ`, the product of the `ℓ`-adic representations, with values in
`∏_ℓ GL₂(ℤ_ℓ)`, which is `GL₂(ℤ̂)` as `ℤ̂ = ∏_ℓ ℤ_ℓ`. This is the inverse limit of the mod-`m`
representations over all `m`, as `lim E[m] = ∏_ℓ T_ℓ E`. Other bases conjugate it
(`exists_adelicGaloisRepresentationGL_eq_conj`). -/
noncomputable def adelicGaloisRepresentationGL :
    (K ≃ₐ[F] K) →* ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ] :=
  MonoidHom.pi fun ℓ ↦ W.tateModuleGaloisRepresentationGL ℓ (b ℓ)

/-- The adelic representation in bases is **well defined up to conjugation** in `∏_ℓ GL₂(ℤ_ℓ)`. -/
lemma exists_adelicGaloisRepresentationGL_eq_conj : ∃ P : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ], ∀ σ,
    W.adelicGaloisRepresentationGL b' σ = P * W.adelicGaloisRepresentationGL b σ * P⁻¹ := by
  choose P hP using fun ℓ : Nat.Primes ↦
    W.exists_tateModuleGaloisRepresentationGL_eq_conj ℓ (b ℓ) (b' ℓ)
  exact ⟨P, fun σ ↦ funext fun ℓ ↦ hP ℓ σ⟩

end WeierstrassCurve
