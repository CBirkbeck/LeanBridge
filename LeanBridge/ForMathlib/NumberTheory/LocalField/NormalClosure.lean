import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField

/-!
# The normal closure of an extension of local fields

Let `L / K` be an extension of nonarchimedean local fields. This file defines its normal closure,
inside an algebraic closure of `L`, as a type (`IsNonarchimedeanLocalField.NormalClosure`), with
the structures that make it a finite extension of `K` and of `L`, Galois over `K` when `L / K` is
separable, and a nonarchimedean local field, for Tau Ceti's spectral-norm structure on a finite
intermediate field, whose valuation extends those of `K` and of `L`. So a statement about the
finite Galois extensions of `K` containing `L`, as local fields over both, applies to it.

## Main definitions

* `IsNonarchimedeanLocalField.NormalClosure`: the normal closure of `L / K`, as a type.
-/

open TauCeti

namespace IsNonarchimedeanLocalField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The **normal closure** of a field extension `L / K`, inside the algebraic closure of `L`, as a
type. When `L / K` is an extension of nonarchimedean local fields, it is a finite extension of `K`
and of `L`, Galois over `K` when `L / K` is separable, and a nonarchimedean local field, for Tau
Ceti's spectral-norm structure, whose valuation extends those of `K` and of `L`. -/
def NormalClosure : Type _ :=
  IntermediateField.normalClosure K L (AlgebraicClosure L)

noncomputable instance : Field (NormalClosure K L) :=
  inferInstanceAs (Field (IntermediateField.normalClosure K L (AlgebraicClosure L)))

noncomputable instance : Algebra K (NormalClosure K L) :=
  inferInstanceAs (Algebra K (IntermediateField.normalClosure K L (AlgebraicClosure L)))

noncomputable instance : Algebra L (NormalClosure K L) :=
  inferInstanceAs (Algebra L (IntermediateField.normalClosure K L (AlgebraicClosure L)))

instance : IsScalarTower K L (NormalClosure K L) :=
  inferInstanceAs (IsScalarTower K L (IntermediateField.normalClosure K L (AlgebraicClosure L)))

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

instance : Module.Finite K (NormalClosure K L) :=
  have : Module.Finite K L := finite_of_valuativeExtension K L
  inferInstanceAs (Module.Finite K (IntermediateField.normalClosure K L (AlgebraicClosure L)))

instance : Module.Finite L (NormalClosure K L) :=
  .of_restrictScalars_finite K L _

instance [Algebra.IsSeparable K L] : IsGalois K (NormalClosure K L) :=
  have : Module.Finite K L := finite_of_valuativeExtension K L
  have : IsAlgClosure K (AlgebraicClosure L) := .ofAlgebraic K L (AlgebraicClosure L)
  inferInstanceAs (IsGalois K (IntermediateField.normalClosure K L (AlgebraicClosure L)))

noncomputable instance : ValuativeRel (NormalClosure K L) :=
  haveI : Module.Finite K L := finite_of_valuativeExtension K L
  finiteIntermediateFieldValuativeRel K (AlgebraicClosure L)
    (IntermediateField.normalClosure K L (AlgebraicClosure L))

noncomputable instance : TopologicalSpace (NormalClosure K L) :=
  haveI : Module.Finite K L := finite_of_valuativeExtension K L
  finiteIntermediateFieldTopology K (AlgebraicClosure L)
    (IntermediateField.normalClosure K L (AlgebraicClosure L))

instance : IsNonarchimedeanLocalField (NormalClosure K L) :=
  have : Module.Finite K L := finite_of_valuativeExtension K L
  finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure L)
    (IntermediateField.normalClosure K L (AlgebraicClosure L))

instance : ValuativeExtension K (NormalClosure K L) :=
  have : Module.Finite K L := finite_of_valuativeExtension K L
  finiteIntermediateField_valuativeExtension K (AlgebraicClosure L)
    (IntermediateField.normalClosure K L (AlgebraicClosure L))

instance : ValuativeExtension L (NormalClosure K L) :=
  have : Module.Finite K L := finite_of_valuativeExtension K L
  ⟨(IsScalarTower.toAlgHom K L (NormalClosure K L)).valuativeExtension.vle_iff_vle⟩

end IsNonarchimedeanLocalField
