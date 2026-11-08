import LeanBridge.ForMathlib.NumberTheory.ModEllGaloisRep.Frobenius
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# The projective representation of a mod-`ℓ` Galois representation

The projective representation of a mod-`ℓ` Galois representation `ρ : Gal(K̄/K) → GL_n(𝔽_ℓ)` is its
composite `ℙρ : Gal(K̄/K) → PGL_n(𝔽_ℓ)` with the projection to Mathlib's
`Matrix.ProjGenLinGroup`, the quotient of `GL_n(𝔽_ℓ)` by its centre, the scalar matrices `𝔽_ℓˣ`
(Mathlib's `Matrix.GeneralLinearGroup.center_eq_range_scalar`). Over a ring with only one unit, such
as `𝔽₂`, there are no non-trivial scalars, so the projection `GL_n → PGL_n` is an isomorphism, and
for `ℓ = 2` the projective representation is the representation itself. As for
`MonoidHom.IsModEllGaloisRep`, the representations take values in `GL_n(𝔽_ℓ)`; for an algebraic
group `G` with an embedding `ι : G ⟶ GL_n`, the projective representation with values in `G(𝔽_ℓ)`
modulo its scalars is `MonoidHom.projectiveRepresentationIn`.

## Main definitions

* `Matrix.ProjGenLinGroup.mulEquivOfSubsingletonUnits`: the isomorphism `GL_n(R) ≃* PGL_n(R)` over a
  ring with only one unit.
* `MonoidHom.projectiveRepresentation` (LMFDB `modlgal.projective_representation`): the projective
  representation of a mod-`ℓ` Galois representation.

## Main results

* `MonoidHom.symm_comp_projectiveRepresentation_two` (LMFDB `modlgal.projective_representation`):
  for `ℓ = 2` the projective representation is the representation itself.
-/

open Matrix ProjGenLinGroup

namespace Matrix.ProjGenLinGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [Subsingleton Rˣ]

lemma mk_injective_of_subsingleton_units :
    Function.Injective (mk : GL n R → ProjGenLinGroup n R) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_mk, GeneralLinearGroup.center_eq_range_scalar,
    MonoidHom.range_eq_bot_iff]
  exact MonoidHom.ext fun u ↦ by rw [Subsingleton.elim u 1, map_one, MonoidHom.one_apply]

/-- Over a commutative ring `R` with only one unit, such as `𝔽₂`, the projection
`GL n R → PGL n R` is an isomorphism, as the centre of `GL n R`, the scalar matrices, is trivial. -/
noncomputable def mulEquivOfSubsingletonUnits : GL n R ≃* ProjGenLinGroup n R :=
  MulEquiv.ofBijective mk ⟨mk_injective_of_subsingleton_units, mk_surjective⟩

end Matrix.ProjGenLinGroup

namespace MonoidHom

variable {K : Type*} [Field K] {n ℓ : ℕ} (ρ : Gal(AlgebraicClosure K/K) →* GL (Fin n) (ZMod ℓ))

/-- The **projective representation** (LMFDB `modlgal.projective_representation`)
`ℙρ : Gal(K̄/K) → PGL_n(𝔽_ℓ)` of a mod-`ℓ` Galois representation `ρ : Gal(K̄/K) → GL_n(𝔽_ℓ)` of a
field `K`, such as a number field: the composite of `ρ` with the projection of `GL_n(𝔽_ℓ)` onto
`PGL_n(𝔽_ℓ) = GL_n(𝔽_ℓ)/𝔽_ℓˣ`, Mathlib's quotient of `GL_n(𝔽_ℓ)` by its centre, the scalar
matrices. -/
noncomputable def projectiveRepresentation :
    Gal(AlgebraicClosure K/K) →* ProjGenLinGroup (Fin n) (ZMod ℓ) :=
  ProjGenLinGroup.mk.comp ρ

/-- **For `ℓ = 2` the projective representation is the representation itself**: transported back
along the isomorphism `GL_n(𝔽₂) ≃* PGL_n(𝔽₂)` given by the projection, `ℙρ` is `ρ`. -/
lemma symm_comp_projectiveRepresentation_two
    (ρ₂ : Gal(AlgebraicClosure K/K) →* GL (Fin n) (ZMod 2)) :
    mulEquivOfSubsingletonUnits.symm.toMonoidHom.comp ρ₂.projectiveRepresentation = ρ₂ :=
  ext fun σ ↦ mulEquivOfSubsingletonUnits.symm_apply_apply (ρ₂ σ)

end MonoidHom
