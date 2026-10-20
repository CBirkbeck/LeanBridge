import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RepresentationTheory.Basic

/-!
# Complex conjugations and the parity of Artin representations

An embedding `ι : ℚ̄ → ℂ` identifies `ℚ̄` with the field of algebraic numbers, which complex
conjugation preserves; the induced automorphism of `ℚ̄` is a complex conjugation of `Gal(ℚ̄/ℚ)`. Any
two embeddings differ by an automorphism of `ℚ̄`, so all complex conjugations are conjugate, and the
determinant of an Artin representation at a complex conjugation, which is `±1`, does not depend on
the choice. Its value is the parity of the representation.

## Main definitions

* `Field.absoluteGaloisGroup.equivAlgebraicClosure`: an embedding `ℚ̄ → ℂ`, as an isomorphism
  onto the field of algebraic numbers.
* `Field.absoluteGaloisGroup.complexConjugation`: the complex conjugation of `Gal(ℚ̄/ℚ)` attached
  to an embedding `ℚ̄ → ℂ`.
* `Representation.IsEven` and `Representation.IsOdd` (LMFDB `artin.parity`): even and odd Artin
  representations.

## Main results

* `Field.absoluteGaloisGroup.apply_complexConjugation`: the complex conjugation attached to `ι`
  is the automorphism `c` with `ι ∘ c = conj ∘ ι`.
* `Field.absoluteGaloisGroup.complexConjugation_mul_self`: complex conjugations are involutions.
* `Field.absoluteGaloisGroup.exists_complexConjugation_eq_conj`: any two complex conjugations are
  conjugate in `Gal(ℚ̄/ℚ)`.
* `Representation.det_complexConjugation_eq`: the determinant at a complex conjugation does not
  depend on the complex conjugation.
* `Representation.det_complexConjugation_eq_one_or_eq_neg_one`: this determinant is `±1`.
* `Representation.isEven_iff` and `Representation.isOdd_iff`: parity can be read off a single
  complex conjugation.
* `Representation.isEven_or_isOdd` and `Representation.not_isEven_and_isOdd`: every
  representation is either even or odd, and not both.
-/

open Algebra Field.absoluteGaloisGroup
open scoped ComplexConjugate

namespace Field.absoluteGaloisGroup

variable (ι ι' : AlgebraicClosure ℚ →+* ℂ) (x : AlgebraicClosure ℚ)

instance : Nonempty (AlgebraicClosure ℚ →+* ℂ) :=
  ⟨(IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ)⟩

/-- An embedding `ι : ℚ̄ → ℂ`, as an isomorphism of `ℚ̄` onto the field of algebraic numbers. -/
noncomputable def equivAlgebraicClosure : AlgebraicClosure ℚ ≃ₐ[ℚ] algebraicClosure ℚ ℂ :=
  letI f : AlgebraicClosure ℚ →ₐ[ℚ] algebraicClosure ℚ ℂ := ι.toRatAlgHom.codRestrict _ fun y ↦
    (map_mem_algebraicClosure_iff ι.toRatAlgHom).mpr <|
      mem_algebraicClosure_iff.mpr (IsAlgebraic.isAlgebraic y)
  AlgEquiv.ofBijective f (IsAlgebraic.algHom_bijective₂ f
    (IsAlgClosure.equiv ℚ (algebraicClosure ℚ ℂ) (AlgebraicClosure ℚ)).toAlgHom).1

/-- The **complex conjugation** of `Gal(ℚ̄/ℚ)` attached to an embedding `ι : ℚ̄ → ℂ`: the
automorphism `c` of `ℚ̄` with `ι (c x) = conj (ι x)`. All complex conjugations are conjugate in
`Gal(ℚ̄/ℚ)` (`Field.absoluteGaloisGroup.exists_complexConjugation_eq_conj`). -/
noncomputable def complexConjugation : Gal(AlgebraicClosure ℚ/ℚ) :=
  (equivAlgebraicClosure ι).trans
    (starRingAut.toRatAlgEquiv.algebraicClosure.trans (equivAlgebraicClosure ι).symm)

@[simp]
lemma coe_equivAlgebraicClosure : (equivAlgebraicClosure ι x : ℂ) = ι x :=
  rfl

/-- **The complex conjugation attached to `ι` is conjugation through `ι`**: `ι ∘ c = conj ∘ ι`. -/
lemma apply_complexConjugation : ι (complexConjugation ι x) = conj (ι x) := by
  rw [← coe_equivAlgebraicClosure, complexConjugation, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AlgEquiv.apply_symm_apply]
  rfl

lemma eq_complexConjugation_iff (σ : Gal(AlgebraicClosure ℚ/ℚ)) :
    σ = complexConjugation ι ↔ ∀ x, ι (σ x) = conj (ι x) := by
  refine ⟨fun h y ↦ h ▸ apply_complexConjugation ι y, fun h ↦ AlgEquiv.ext fun y ↦ ι.injective ?_⟩
  rw [h, apply_complexConjugation]

/-- **Complex conjugations are involutions.** -/
lemma complexConjugation_mul_self : complexConjugation ι * complexConjugation ι = 1 := by
  refine AlgEquiv.ext fun y ↦ ι.injective ?_
  rw [AlgEquiv.mul_apply, apply_complexConjugation, apply_complexConjugation, Complex.conj_conj,
    AlgEquiv.one_apply]

lemma complexConjugation_comp (τ : Gal(AlgebraicClosure ℚ/ℚ)) :
    complexConjugation (ι.comp τ) = τ⁻¹ * complexConjugation ι * τ := by
  refine ((eq_complexConjugation_iff _ _).mpr fun y ↦ ?_).symm
  simp [apply_complexConjugation]

lemma exists_comp_eq : ∃ τ : Gal(AlgebraicClosure ℚ/ℚ), ι.comp τ = ι' := by
  refine ⟨(equivAlgebraicClosure ι').trans (equivAlgebraicClosure ι).symm, RingHom.ext fun y ↦ ?_⟩
  rw [RingHom.comp_apply, ← coe_equivAlgebraicClosure ι]
  simp

/-- **All complex conjugations are conjugate** in `Gal(ℚ̄/ℚ)`. -/
lemma exists_complexConjugation_eq_conj :
    ∃ τ : Gal(AlgebraicClosure ℚ/ℚ), complexConjugation ι' = τ⁻¹ * complexConjugation ι * τ := by
  rcases exists_comp_eq ι ι' with ⟨τ, rfl⟩
  exact ⟨τ, complexConjugation_comp ι τ⟩

end Field.absoluteGaloisGroup

namespace Representation

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ Gal(AlgebraicClosure ℚ/ℚ) V) (ι ι' : AlgebraicClosure ℚ →+* ℂ)

/-- An Artin representation `ρ` of `Gal(ℚ̄/ℚ)` is **even** (LMFDB `artin.parity`) if
`det ρ(c) = 1` for the complex conjugations `c`. This holds for one complex conjugation exactly
when it holds for all of them (`Representation.isEven_iff`). The definition applies to every
representation; on an infinite-dimensional space, `LinearMap.det` is `1` by convention. -/
def IsEven : Prop :=
  ∀ ι : AlgebraicClosure ℚ →+* ℂ, LinearMap.det (ρ (complexConjugation ι)) = 1

/-- An Artin representation `ρ` of `Gal(ℚ̄/ℚ)` is **odd** (LMFDB `artin.parity`) if
`det ρ(c) = -1` for the complex conjugations `c`. This holds for one complex conjugation exactly
when it holds for all of them (`Representation.isOdd_iff`). -/
def IsOdd : Prop :=
  ∀ ι : AlgebraicClosure ℚ →+* ℂ, LinearMap.det (ρ (complexConjugation ι)) = -1

/-- **The determinant at a complex conjugation does not depend on the complex conjugation.** -/
lemma det_complexConjugation_eq :
    LinearMap.det (ρ (complexConjugation ι')) = LinearMap.det (ρ (complexConjugation ι)) := by
  rcases exists_complexConjugation_eq_conj ι ι' with ⟨τ, h⟩
  rw [h, map_mul, map_mul, map_mul, map_mul, mul_right_comm, ← map_mul LinearMap.det, ← map_mul ρ,
    inv_mul_cancel, map_one, map_one, one_mul]

/-- **The determinant at a complex conjugation is `±1`.** -/
lemma det_complexConjugation_eq_one_or_eq_neg_one : LinearMap.det (ρ (complexConjugation ι)) = 1 ∨
    LinearMap.det (ρ (complexConjugation ι)) = -1 := by
  rw [← mul_self_eq_one_iff, ← map_mul, ← map_mul, complexConjugation_mul_self, map_one, map_one]

/-- **Evenness can be read off one complex conjugation.** -/
lemma isEven_iff : ρ.IsEven ↔ LinearMap.det (ρ (complexConjugation ι)) = 1 :=
  ⟨fun h ↦ h ι, fun h ι₁ ↦ (det_complexConjugation_eq ρ ι ι₁).trans h⟩

/-- **Oddness can be read off one complex conjugation.** -/
lemma isOdd_iff : ρ.IsOdd ↔ LinearMap.det (ρ (complexConjugation ι)) = -1 :=
  ⟨fun h ↦ h ι, fun h ι₁ ↦ (det_complexConjugation_eq ρ ι ι₁).trans h⟩

/-- **Every representation of `Gal(ℚ̄/ℚ)` is even or odd.** -/
lemma isEven_or_isOdd : ρ.IsEven ∨ ρ.IsOdd :=
  (det_complexConjugation_eq_one_or_eq_neg_one ρ (Classical.arbitrary _)).imp (isEven_iff ρ _).mpr
    (isOdd_iff ρ _).mpr

/-- **No representation of `Gal(ℚ̄/ℚ)` is both even and odd.** -/
lemma not_isEven_and_isOdd : ¬(ρ.IsEven ∧ ρ.IsOdd) := fun ⟨h, h'⟩ ↦
  absurd ((h (Classical.arbitrary _)).symm.trans (h' _)) (by norm_num)

end Representation
