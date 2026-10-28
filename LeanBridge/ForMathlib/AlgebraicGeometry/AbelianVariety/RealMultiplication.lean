import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.ComplexMultiplication
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Abelian varieties with real multiplication

An abelian variety `A` has real multiplication if its endomorphism algebra `End(A) ⊗ ℚ` is a totally
real number field. The LMFDB usually excludes the trivial case of real multiplication by `ℚ`; both
notions are given.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.HasRealMultiplication`
  (LMFDB `ag.real_multiplication`).
* `TauCeti.AlgebraicGeometry.AbelianVariety.HasNontrivialRealMultiplication`
  (LMFDB `ag.real_multiplication`): real multiplication by a field other than `ℚ`.

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.hasRealMultiplication_congr`: having real
  multiplication only depends on the isomorphism class of the abelian variety.
-/

namespace TauCeti.AlgebraicGeometry.AbelianVariety

open CategoryTheory NumberField

universe u

variable {K : Type u} [Field K] {A B : AbelianVariety K}

variable (A) in
/-- An abelian variety `A` has **real multiplication** (LMFDB `ag.real_multiplication`), or RM, if
its endomorphism algebra `End(A) ⊗ ℚ` is a totally real number field: it is isomorphic as a
`ℚ`-algebra to a totally real number field `F`.

This includes the trivial case `F = ℚ`, which the LMFDB usually excludes; see
`HasNontrivialRealMultiplication`. -/
def HasRealMultiplication : Prop :=
  ∃ (F : Type u) (_ : Field F) (_ : NumberField F), IsTotallyReal F ∧
    Nonempty (A.EndAlgebra ≃ₐ[ℚ] F)

variable (A) in
/-- An abelian variety `A` has **real multiplication** (LMFDB `ag.real_multiplication`) in the
LMFDB's usual sense, excluding the trivial case of RM by `ℚ`: its endomorphism algebra
`End(A) ⊗ ℚ` is isomorphic as a `ℚ`-algebra to a totally real number field `F` with
`[F : ℚ] > 1`. -/
def HasNontrivialRealMultiplication : Prop :=
  ∃ (F : Type u) (_ : Field F) (_ : NumberField F), IsTotallyReal F ∧ 1 < Module.finrank ℚ F ∧
    Nonempty (A.EndAlgebra ≃ₐ[ℚ] F)

lemma HasNontrivialRealMultiplication.hasRealMultiplication
    (hA : A.HasNontrivialRealMultiplication) : A.HasRealMultiplication := by
  rcases hA with ⟨F, _, _, hF, -, hFA⟩
  exact ⟨F, inferInstance, inferInstance, hF, hFA⟩

lemma HasRealMultiplication.of_iso (e : A ≅ B) (hA : A.HasRealMultiplication) :
    B.HasRealMultiplication := by
  rcases hA with ⟨F, _, _, hF, ⟨f⟩⟩
  exact ⟨F, inferInstance, inferInstance, hF, ⟨(EndAlgebra.congr e).symm.trans f⟩⟩

/-- **Having real multiplication only depends on the isomorphism class of the abelian variety.** -/
lemma hasRealMultiplication_congr (e : A ≅ B) : A.HasRealMultiplication ↔ B.HasRealMultiplication :=
  ⟨.of_iso e, .of_iso e.symm⟩

lemma HasNontrivialRealMultiplication.of_iso (e : A ≅ B) (hA : A.HasNontrivialRealMultiplication) :
    B.HasNontrivialRealMultiplication := by
  rcases hA with ⟨F, _, _, hF, hd, ⟨f⟩⟩
  exact ⟨F, inferInstance, inferInstance, hF, hd, ⟨(EndAlgebra.congr e).symm.trans f⟩⟩

end TauCeti.AlgebraicGeometry.AbelianVariety
