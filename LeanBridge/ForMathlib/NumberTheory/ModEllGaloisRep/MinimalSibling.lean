import LeanBridge.ForMathlib.NumberTheory.ModEllGaloisRep.Frobenius
import LeanBridge.ForMathlib.NumberTheory.NumberField.MinimalSibling
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# Minimal siblings of the splitting fields of mod-`ℓ` Galois representations

The LMFDB describes a mod-`ℓ` Galois representation `ρ : Gal(ℚ̄/ℚ) → GL_n(𝔽_ℓ)` through number
fields attached to it:

* the minimal sibling of its splitting field (LMFDB `modlgal.min_sib_splitting_field`), the
  minimal sibling (`NumberField.IsMinimalSibling`, LMFDB `nf.minimal_sibling`) of the splitting
  field `L` of `ρ` (LeanBridge's `MonoidHom.splittingField`);
* its projective kernel polynomial (LMFDB `modlgal.projective_kernel_polynomial`), the minimal
  sibling of the splitting field of its projective representation `Pρ : Gal(ℚ̄/ℚ) → PGL_n(𝔽_ℓ)`,
  the composite of `ρ` with the projection `GL_n(𝔽_ℓ) → PGL_n(𝔽_ℓ)` (Mathlib's
  `Matrix.ProjGenLinGroup.mk`, LMFDB `modlgal.projective_representation`). The knowl calls this
  field a polynomial, as the database stores it by its normalised defining polynomial
  (`NumberField.IsMinimalSiblingPolynomial`), which is what is defined here.

Minimal siblings depend on the T-numbers of transitive groups, a numbering of the database that is
not formalised and enters as a parameter `t : NumberField.TNumbering`, as in
`NumberField.IsMinimalSibling`. For every numbering both notions are well defined: the minimal
sibling of the splitting field exists and is unique up to isomorphism, and the projective kernel
polynomial exists and is unique.

## Main definitions

* `MonoidHom.IsMinSibSplittingField` (LMFDB `modlgal.min_sib_splitting_field`): the minimal
  sibling of the splitting field.
* `MonoidHom.projectiveSplittingField` (LMFDB `modlgal.projective_kernel_polynomial`): the
  splitting field of the projective representation.
* `MonoidHom.IsProjectiveKernelPolynomial` (LMFDB `modlgal.projective_kernel_polynomial`): the
  projective kernel polynomial.

## Main results

* `MonoidHom.exists_isMinSibSplittingField` and
  `MonoidHom.IsMinSibSplittingField.nonempty_algEquiv`: the minimal sibling of the splitting field
  exists and is unique up to isomorphism.
* `MonoidHom.projectiveSplittingField_le`: the splitting field of the projective representation
  lies in that of `ρ`.
* `MonoidHom.exists_isProjectiveKernelPolynomial` and `MonoidHom.IsProjectiveKernelPolynomial.eq`:
  the projective kernel polynomial exists and is unique.
-/

open IntermediateField Matrix NumberField Polynomial

namespace MonoidHom

variable (t : TNumbering) {n ℓ : ℕ} {ρ : Gal(AlgebraicClosure ℚ/ℚ) →* GL (Fin n) (ZMod ℓ)}
  (hρ : IsOpen (ρ.ker : Set Gal(AlgebraicClosure ℚ/ℚ))) {F F' : Type*} [Field F] [NumberField F]
  [Field F'] [NumberField F'] {P Q : ℤ[X]}

variable (F) in
/-- `F` is a **minimal sibling of the splitting field** (LMFDB `modlgal.min_sib_splitting_field`) of
a mod-`ℓ` Galois representation `ρ` of `ℚ`, for a numbering `t` of transitive groups: a minimal
sibling (`NumberField.IsMinimalSibling`) of the splitting field of `ρ`, the number field fixed by
its kernel (`splittingField`). It exists (`exists_isMinSibSplittingField`) and is unique up to
isomorphism (`IsMinSibSplittingField.nonempty_algEquiv`). -/
def IsMinSibSplittingField : Prop :=
  IsMinimalSibling t (splittingField ρ hρ) F

/-- **The minimal sibling of the splitting field exists.** -/
lemma exists_isMinSibSplittingField :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F), IsMinSibSplittingField t hρ F :=
  exists_isMinimalSibling t (splittingField ρ hρ)

variable {t hρ} in
/-- **The minimal sibling of the splitting field is unique up to isomorphism.** -/
lemma IsMinSibSplittingField.nonempty_algEquiv (h : IsMinSibSplittingField t hρ F)
    (h' : IsMinSibSplittingField t hρ F') : Nonempty (F ≃ₐ[ℚ] F') :=
  IsMinimalSibling.nonempty_algEquiv h h'

/-- The **splitting field of the projective representation** (LMFDB
`modlgal.projective_kernel_polynomial`) of a mod-`ℓ` Galois representation `ρ` of `ℚ`: the fixed
field of the kernel of its projective representation `Pρ : Gal(ℚ̄/ℚ) → PGL_n(𝔽_ℓ)` (LMFDB
`modlgal.projective_representation`), the composite of `ρ` with the projection
`ProjGenLinGroup.mk`, a finite Galois extension of `ℚ`, as the kernel of `Pρ` contains the open
kernel of `ρ`. -/
noncomputable def projectiveSplittingField : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
  haveI h : IsOpen ((ProjGenLinGroup.mk.comp ρ).ker : Set Gal(AlgebraicClosure ℚ/ℚ)) :=
    Subgroup.isOpen_mono (ρ.ker_le_comap ProjGenLinGroup.mk.ker) hρ
  { toIntermediateField := fixedField (ProjGenLinGroup.mk.comp ρ).ker
    finiteDimensional := (ProjGenLinGroup.mk.comp ρ).finiteDimensional_fixedField_ker h
    isGalois := (ProjGenLinGroup.mk.comp ρ).isGalois_fixedField_ker h }

/-- **The splitting field of the projective representation lies in that of `ρ`**, as the kernel of
`ρ` lies in that of its projective representation. -/
lemma projectiveSplittingField_le :
    (projectiveSplittingField hρ).toIntermediateField ≤ (splittingField ρ hρ).toIntermediateField :=
  fixedField_antitone (ρ.ker_le_comap ProjGenLinGroup.mk.ker)

variable (P) in
/-- `P` is the **projective kernel polynomial** (LMFDB `modlgal.projective_kernel_polynomial`) of a
mod-`ℓ` Galois representation `ρ` of `ℚ`, for a numbering `t` of transitive groups: the normalised
defining polynomial (`NumberField.polredabs`) of the minimal sibling of the splitting field of its
projective representation (`projectiveSplittingField`), by which the LMFDB stores that minimal
sibling. It exists (`exists_isProjectiveKernelPolynomial`) and is unique
(`IsProjectiveKernelPolynomial.eq`). -/
def IsProjectiveKernelPolynomial : Prop :=
  IsMinimalSiblingPolynomial t (projectiveSplittingField hρ) P

/-- **The projective kernel polynomial exists.** -/
lemma exists_isProjectiveKernelPolynomial : ∃ P, IsProjectiveKernelPolynomial t hρ P :=
  exists_isMinimalSiblingPolynomial t (projectiveSplittingField hρ)

variable {t hρ} in
/-- **The projective kernel polynomial is unique.** -/
lemma IsProjectiveKernelPolynomial.eq (hP : IsProjectiveKernelPolynomial t hρ P)
    (hQ : IsProjectiveKernelPolynomial t hρ Q) : P = Q :=
  IsMinimalSiblingPolynomial.eq hP hQ

end MonoidHom
