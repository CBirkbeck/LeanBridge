import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.Isogenous
import TauCeti.AlgebraicGeometry.AbelianVariety.Product
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Simple abelian varieties

An abelian variety is simple if it is nonzero and not isogenous to a product of abelian varieties
of lower dimension, and geometrically simple if it stays simple over an algebraic closure of its
base field.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.IsSimple` (LMFDB `ag.simple`, `av.simple`).
* `TauCeti.AlgebraicGeometry.AbelianVariety.IsGeometricallySimple` (LMFDB `ag.geom_simple`).

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.not_isSimple_trivial`: the trivial abelian variety is
  not simple.
* `TauCeti.AlgebraicGeometry.AbelianVariety.isSimple_congr` and
  `TauCeti.AlgebraicGeometry.AbelianVariety.isGeometricallySimple_congr`: simplicity and geometric
  simplicity only depend on the isomorphism class of the abelian variety.
-/

namespace TauCeti.AlgebraicGeometry.AbelianVariety

open CategoryTheory Limits

universe u

variable {K : Type u} [Field K] {A B : AbelianVariety K} (e : A ≅ B)

variable (A) in
/-- An abelian variety `A` over `K` is **simple** (LMFDB `ag.simple`, `av.simple`) if it is nonzero
and not isogenous to a product `B × C` of abelian varieties of lower dimension.

The LMFDB allows products of any number of factors of lower dimension. Two factors suffice:
isogenous abelian varieties have the same dimension, dimension is additive in products, and a
factor of dimension zero is trivial, so a product of more factors regroups into two. Being
isogenous is symmetric, so the direction of the isogeny `A ⟶ B × C` does not matter either. These
facts are not formalised here. -/
def IsSimple : Prop :=
  ¬IsZero A ∧ ∀ B C : AbelianVariety K, B.dim < A.dim → C.dim < A.dim → ¬IsIsogenous A (B.prod C)

variable (hA : A.IsSimple)

include hA in
lemma IsSimple.not_isZero : ¬IsZero A :=
  hA.1

/-- The trivial abelian variety is not simple. -/
lemma not_isSimple_trivial : ¬(trivial K).IsSimple :=
  fun h ↦ h.not_isZero (isZeroTrivial K)

include e hA in
lemma IsSimple.of_iso : B.IsSimple :=
  ⟨fun hB ↦ hA.1 (hB.of_iso e), fun C D hC hD hBCD ↦ hA.2 C D (dim_eq_of_iso e ▸ hC)
    (dim_eq_of_iso e ▸ hD) ((isIsogenous_congr e (Iso.refl _)).mpr hBCD)⟩

include e in
/-- Simplicity only depends on the isomorphism class of the abelian variety. -/
lemma isSimple_congr : A.IsSimple ↔ B.IsSimple :=
  ⟨.of_iso e, .of_iso e.symm⟩

variable (A) in
/-- An abelian variety `A` over `K` is **geometrically simple** (LMFDB `ag.geom_simple`), or
absolutely simple, if its base change to the algebraic closure of `K` is simple. -/
def IsGeometricallySimple : Prop :=
  (A.baseChange (AlgebraicClosure K)).IsSimple

include e in
lemma IsGeometricallySimple.of_iso (h : A.IsGeometricallySimple) : B.IsGeometricallySimple :=
  IsSimple.of_iso ((baseChangeFunctor (AlgebraicClosure K)).mapIso e) h

include e in
/-- Geometric simplicity only depends on the isomorphism class of the abelian variety. -/
lemma isGeometricallySimple_congr : A.IsGeometricallySimple ↔ B.IsGeometricallySimple :=
  ⟨.of_iso e, .of_iso e.symm⟩

end TauCeti.AlgebraicGeometry.AbelianVariety
