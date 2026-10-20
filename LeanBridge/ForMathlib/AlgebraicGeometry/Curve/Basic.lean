import LeanBridge.ForMathlib.AlgebraicGeometry.Variety.Basic
import TauCeti.AlgebraicGeometry.Curves.Basic

/-!
# Algebraic curves

An algebraic curve over a field `K` is an algebraic variety over `K` of dimension one, the dimension
of a variety (LMFDB `ag.dimension`) being the maximal length of a chain of irreducible closed
subsets, the topological Krull dimension of the underlying space.

Tau Ceti's `AlgebraicGeometry.Scheme.IsCurveOver` is the narrower notion of an integral scheme that
is proper and of dimension one over `K`.

## Main definitions

* `AlgebraicGeometry.Scheme.IsAlgebraicCurveOver` (LMFDB `ag.curve`).

## Main results

* `AlgebraicGeometry.Scheme.IsAlgebraicCurveOver.isFunctionField`: the function field of an
  algebraic curve over `K` is an algebraic function field of one variable over `K`, Tau Ceti's
  `TauCeti.IsFunctionField`.
* `AlgebraicGeometry.Scheme.isAlgebraicCurveOver_iff_isCurveOver_and_geometricallyIntegral`: the
  proper algebraic curves over `K` are Tau Ceti's curves over `K` that are geometrically integral.
-/

namespace AlgebraicGeometry.Scheme

open TauCeti (IsFunctionField)
open TauCeti.AlgebraicGeometry (isFunctionField_functionField_iff)

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]

variable (K) in
/-- An **algebraic curve** over a field `K` (LMFDB `ag.curve`): an algebraic variety over `K`, that
is a geometrically integral separated scheme of finite type over `K`, of dimension one. Unlike Tau
Ceti's `AlgebraicGeometry.Scheme.IsCurveOver`, it need not be proper over `K`. -/
class IsAlgebraicCurveOver : Prop extends X.IsVarietyOver K where
  /-- An algebraic curve has dimension one. -/
  topologicalKrullDim_eq_one : topologicalKrullDim X = 1

lemma IsCurveOver.isAlgebraicCurveOver [X.IsCurveOver K]
    [GeometricallyIntegral (X ↘ Spec (.of K))] : X.IsAlgebraicCurveOver K where
  topologicalKrullDim_eq_one := IsCurveOver.topologicalKrullDim_eq_one K

variable [X.IsAlgebraicCurveOver K]

/-- The function field of an algebraic curve over `K` is an algebraic function field of one
variable over `K`. -/
lemma IsAlgebraicCurveOver.isFunctionField [IsIntegral X] : IsFunctionField K X.functionField :=
  (isFunctionField_functionField_iff K).mpr (topologicalKrullDim_eq_one K)

variable [IsProper (X ↘ Spec (.of K))]

instance : X.IsCurveOver K where
  toIsIntegral := IsVarietyOver.isIntegral K
  topologicalKrullDim_eq_one := IsAlgebraicCurveOver.topologicalKrullDim_eq_one K

omit [X.IsAlgebraicCurveOver K] in
/-- A proper scheme over `K` is an algebraic curve if and only if it is a curve in the sense of Tau
Ceti, an integral proper scheme of dimension one over `K`, that is geometrically integral. -/
lemma isAlgebraicCurveOver_iff_isCurveOver_and_geometricallyIntegral :
    X.IsAlgebraicCurveOver K ↔ X.IsCurveOver K ∧ GeometricallyIntegral (X ↘ Spec (.of K)) :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ IsCurveOver.isAlgebraicCurveOver⟩

end AlgebraicGeometry.Scheme
