import LeanBridge.ForMathlib.NumberTheory.ModEllGaloisRep.Frobenius

/-!
# The determinant character of a mod-`ℓ` Galois representation

The determinant character of a mod-`ℓ` Galois representation `ρ : Gal(K̄/K) → GL_n(𝔽_ℓ)` is the
composite `det ρ : Gal(K̄/K) → 𝔽_ℓˣ` of `ρ` with the determinant. For a one-element index type, such
as `Fin 1`, the determinant `GL_1(R) → Rˣ` is an isomorphism, with inverse the scalar matrices.
Through it, `det ρ` is a `1`-dimensional representation `Gal(K̄/K) → GL_1(𝔽_ℓ)`, again a mod-`ℓ`
Galois representation, as its kernel contains the open kernel of `ρ`. When `ρ` itself has dimension
`1`, this representation is `ρ`. As for `MonoidHom.IsModEllGaloisRep`, the representations take
values in `GL_n(𝔽_ℓ)`.

## Main definitions

* `Matrix.GeneralLinearGroup.detEquivOfUnique`: the isomorphism `GL_1(R) ≃* Rˣ` given by the
  determinant.
* `MonoidHom.detCharacter` (LMFDB `modlgal.determinant`): the determinant character of a mod-`ℓ`
  Galois representation.
* `MonoidHom.detCharacterGL` (LMFDB `modlgal.determinant`): the determinant character as a
  `1`-dimensional representation.

## Main results

* `MonoidHom.isModEllGaloisRep_detCharacterGL` (LMFDB `modlgal.determinant`): the determinant
  character is a `1`-dimensional mod-`ℓ` Galois representation.
* `MonoidHom.detCharacterGL_eq_self` (LMFDB `modlgal.determinant`): the determinant character of a
  `1`-dimensional representation is the representation itself.
-/

open Matrix GeneralLinearGroup

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [Unique n] [CommRing R]

/-- For a one-element index type `n`, such as `Fin 1`, the determinant is an isomorphism
`GL n R ≃* Rˣ`, with inverse the scalar matrices: an invertible `1 × 1` matrix is the scalar matrix
of its determinant, its only entry. -/
def detEquivOfUnique : GL n R ≃* Rˣ where
  toFun := det
  invFun := scalar n
  left_inv A := Units.ext <| Matrix.ext fun i j ↦ by
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    simp
  right_inv u := Units.ext <| by simp
  map_mul' := map_mul det

end Matrix.GeneralLinearGroup

namespace MonoidHom

variable {K : Type*} [Field K] {n ℓ : ℕ} (ρ : Gal(AlgebraicClosure K/K) →* GL (Fin n) (ZMod ℓ))

/-- The **determinant character** (LMFDB `modlgal.determinant`) `det ρ : Gal(K̄/K) → 𝔽_ℓˣ` of a
mod-`ℓ` Galois representation `ρ : Gal(K̄/K) → GL_n(𝔽_ℓ)` of a field `K`, such as a number field:
the composite of `ρ` with the determinant `GL_n(𝔽_ℓ) → 𝔽_ℓˣ`. -/
noncomputable def detCharacter : Gal(AlgebraicClosure K/K) →* (ZMod ℓ)ˣ :=
  det.comp ρ

/-- The **determinant character** (LMFDB `modlgal.determinant`) of a mod-`ℓ` Galois representation
`ρ`, as a `1`-dimensional representation `Gal(K̄/K) → GL_1(𝔽_ℓ)` through the isomorphism
`𝔽_ℓˣ ≃* GL_1(𝔽_ℓ)` of `Matrix.GeneralLinearGroup.detEquivOfUnique`. -/
noncomputable def detCharacterGL : Gal(AlgebraicClosure K/K) →* GL (Fin 1) (ZMod ℓ) :=
  detEquivOfUnique.symm.toMonoidHom.comp ρ.detCharacter

/-- **The determinant character of a mod-`ℓ` Galois representation is a `1`-dimensional mod-`ℓ`
Galois representation**: its kernel contains the open kernel of `ρ`. -/
lemma isModEllGaloisRep_detCharacterGL (hρ : ρ.IsModEllGaloisRep) :
    ρ.detCharacterGL.IsModEllGaloisRep where
  prime := hρ.prime
  isOpen_ker := Subgroup.isOpen_mono (fun σ hσ ↦ by
    rw [mem_ker, detCharacterGL, comp_apply, detCharacter, comp_apply, mem_ker.mp hσ, map_one,
      map_one]) hρ.isOpen_ker

/-- **The determinant character of a `1`-dimensional representation is the representation itself**,
through the isomorphism `𝔽_ℓˣ ≃* GL_1(𝔽_ℓ)`. -/
lemma detCharacterGL_eq_self (ρ₁ : Gal(AlgebraicClosure K/K) →* GL (Fin 1) (ZMod ℓ)) :
    ρ₁.detCharacterGL = ρ₁ :=
  ext fun σ ↦ detEquivOfUnique.symm_apply_apply (ρ₁ σ)

end MonoidHom
