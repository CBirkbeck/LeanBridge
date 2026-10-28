import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Hyperelliptic
import TauCeti.FieldTheory.FunctionField.Elliptic.Basic

/-!
# Bielliptic curves

A smooth projective algebraic curve `X` over a field `k`, of genus `g ≥ 2`, is bielliptic if it
admits a 2-to-1 map `X → E`, defined over the algebraic closure `k̄`, onto an elliptic curve `E`. An
involution `w` of `X` defined over `k` whose quotient `X / ⟨w⟩` has genus one and a `k`-rational
point is a bielliptic involution.

As for hyperelliptic curves (`AlgebraicGeometry.Scheme.IsHyperellipticCurveOver`), projectivity is
stated as properness, and the 2-to-1 map is read off the function field `k̄(X_k̄)` of the base
change of `X` to `k̄`: it contains a subfield `k̄(E)` of index two that is an elliptic function
field, Tau Ceti's `TauCeti.IsEllipticFunctionField` (genus one with a divisor of degree one, equivalently a
rational place). Likewise, automorphisms of `X` over `k` are taken as `k`-automorphisms of the
function field `k(X)` (the two groups are anti-isomorphic for smooth proper curves, which is not
formalised), and the quotient `X / ⟨w⟩` is described by the fixed field of `w`.

The LMFDB states three equivalent conditions for bielliptic curves; the first is the definition
here, and their equivalence (which uses Riemann–Hurwitz and, for the third, the Lefschetz fixed
point formula) is not formalised.

## Main definitions

* `TauCeti.IsBiellipticFunctionField` (LMFDB `ag.bielliptic_curve`).
* `TauCeti.IsBiellipticInvolution` (LMFDB `ag.bielliptic_curve`).
* `AlgebraicGeometry.Scheme.IsBiellipticCurveOver` (LMFDB `ag.bielliptic_curve`).
* `AlgebraicGeometry.Scheme.IsBiellipticInvolution` (LMFDB `ag.bielliptic_curve`).
-/

namespace TauCeti

variable (k : Type*) {F : Type*} [Field k] [Field F] [Algebra k F]

variable (F) in
/-- A field extension `F / k`, such as the function field of a curve over an algebraically closed
field `k`, is **bielliptic** (LMFDB `ag.bielliptic_curve`) if it has genus at least two and
contains an elliptic function field `E` over `k` of index two, the function field of an elliptic
curve onto which the curve maps 2-to-1. -/
def IsBiellipticFunctionField : Prop :=
  2 ≤ genus k F ∧ ∃ E : IntermediateField k F, IsEllipticFunctionField k E ∧ Module.finrank E F = 2

/-- A **bielliptic involution** (LMFDB `ag.bielliptic_curve`) of a field extension `F / k`, such as
the function field of a curve `X` over `k`: an automorphism `w` of `F / k` of order two whose fixed
field, the function field of the quotient curve `X / ⟨w⟩`, is an elliptic function field over `k`
(genus one with a rational place). -/
def IsBiellipticInvolution (w : F ≃ₐ[k] F) : Prop :=
  orderOf w = 2 ∧ IsEllipticFunctionField k (IntermediateField.fixedField (Subgroup.zpowers w))

end TauCeti

namespace AlgebraicGeometry.Scheme

open TauCeti

universe u

variable (K : Type u) [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

/-- A **bielliptic curve** over a field `K` (LMFDB `ag.bielliptic_curve`): a smooth projective
algebraic curve over `K` of genus `g ≥ 2` that admits a 2-to-1 map onto an elliptic curve over the
algebraic closure `K̄` of `K`.

Projectivity is stated as properness, which is equivalent for curves. The genus and the 2-to-1 map
are read off the function field `K̄(X_K̄)` of the base change of `X` to `K̄`: it is bielliptic over
`K̄`, of genus at least two with an elliptic subfield of index two. -/
class IsBiellipticCurveOver : Prop extends X.IsAlgebraicCurveOver K, Smooth (X ↘ Spec (.of K)),
    IsProper (X ↘ Spec (.of K)) where
  /-- The function field of the base change to the algebraic closure is bielliptic. -/
  isBiellipticFunctionField :
    IsBiellipticFunctionField (AlgebraicClosure K) (X.geometricBaseChange K).left.functionField

variable {X} in
/-- A **bielliptic involution** (LMFDB `ag.bielliptic_curve`) of an integral curve `X` over `K`: an
involution `w` of `X` defined over `K`, given as an automorphism of the function field `K(X)` over
`K`, whose quotient `X / ⟨w⟩` has genus one and a `K`-rational point, that is whose fixed field is
an elliptic function field over `K`. -/
def IsBiellipticInvolution [IsIntegral X] (w : X.functionField ≃ₐ[K] X.functionField) : Prop :=
  TauCeti.IsBiellipticInvolution K w

end AlgebraicGeometry.Scheme
