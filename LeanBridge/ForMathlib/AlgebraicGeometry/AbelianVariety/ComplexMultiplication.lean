import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.Simple
import TauCeti.AlgebraicGeometry.AbelianVariety.End.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Abelian varieties with complex multiplication

A simple abelian variety of dimension `g` has complex multiplication if its endomorphism algebra
`End(A) ⊗ ℚ` is a CM field of degree `2g`. The endomorphism ring `End(A)` is Tau Ceti's
`TauCeti.AlgebraicGeometry.AbelianVariety.End`.

The LMFDB's equivalent description of complex multiplication, that `End(A)` is an order in a CM
field of degree `2g`, needs `End(A)` to be a finitely generated free `ℤ`-module, which Tau Ceti
does not have yet.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.EndAlgebra`: the endomorphism algebra `End(A) ⊗ ℚ`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.EndAlgebra.congr`: the isomorphism of endomorphism
  algebras induced by an isomorphism of abelian varieties.
* `TauCeti.AlgebraicGeometry.AbelianVariety.HasComplexMultiplication`
  (LMFDB `ag.complex_multiplication`).

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.hasComplexMultiplication_congr`: having complex
  multiplication only depends on the isomorphism class of the abelian variety.
-/

namespace TauCeti.AlgebraicGeometry.AbelianVariety

open CategoryTheory NumberField
open Algebra.TensorProduct renaming congr → tensorCongr
open scoped TensorProduct

universe u

variable {K : Type u} [Field K] {A B : AbelianVariety K} (e : A ≅ B)

variable (A) in
/-- The **endomorphism algebra** `End(A) ⊗ ℚ` of an abelian variety `A`, a `ℚ`-algebra.

It is written `ℚ ⊗[ℤ] End A`, with the rational numbers on the left, so that it is a `ℚ`-algebra
through `Algebra.TensorProduct.leftAlgebra`. -/
abbrev EndAlgebra : Type u :=
  ℚ ⊗[ℤ] End A

include e in
/-- An isomorphism of abelian varieties `A ≅ B` induces an isomorphism of `ℚ`-algebras between
their endomorphism algebras, by conjugation. -/
noncomputable def EndAlgebra.congr : A.EndAlgebra ≃ₐ[ℚ] B.EndAlgebra :=
  tensorCongr AlgEquiv.refl (End.congr e).toIntAlgEquiv

variable (A) in
/-- A simple abelian variety `A` of dimension `g` has **complex multiplication** (LMFDB
`ag.complex_multiplication`), or is CM, if its endomorphism algebra `End(A) ⊗ ℚ` is a CM field of
degree `2g`: it is isomorphic as a `ℚ`-algebra to a CM number field `F` with `[F : ℚ] = 2g`.

Simplicity is simplicity over `K`, `IsSimple`, as the word "simple" of the LMFDB's text says, and
the endomorphisms are those defined over `K`, as in LMFDB `ag.endomorphism_algebra`; the knowl's
link on "simple" points to geometric simplicity, LMFDB `ag.geom_simple`, instead. -/
def HasComplexMultiplication : Prop :=
  A.IsSimple ∧ ∃ (F : Type u) (_ : Field F) (_ : NumberField F), IsCMField F ∧
    (Module.finrank ℚ F : WithBot ℕ∞) = 2 * A.dim ∧ Nonempty (A.EndAlgebra ≃ₐ[ℚ] F)

variable (hA : A.HasComplexMultiplication)

include hA in
lemma HasComplexMultiplication.isSimple : A.IsSimple :=
  hA.1

include e hA in
lemma HasComplexMultiplication.of_iso : B.HasComplexMultiplication := by
  rcases hA with ⟨hA, F, _, _, hF, hdim, ⟨f⟩⟩
  exact ⟨hA.of_iso e, F, inferInstance, inferInstance, hF, dim_eq_of_iso e ▸ hdim,
    ⟨(EndAlgebra.congr e).symm.trans f⟩⟩

include e in
/-- Having complex multiplication only depends on the isomorphism class of the abelian variety. -/
lemma hasComplexMultiplication_congr : A.HasComplexMultiplication ↔ B.HasComplexMultiplication :=
  ⟨.of_iso e, .of_iso e.symm⟩

end TauCeti.AlgebraicGeometry.AbelianVariety
