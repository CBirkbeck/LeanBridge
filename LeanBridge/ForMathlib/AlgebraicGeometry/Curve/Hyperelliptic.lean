import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.FieldTheory.FunctionField.Hyperelliptic.Basic

/-!
# Hyperelliptic curves

A hyperelliptic curve over a field `K` is a smooth projective algebraic curve over `K` of genus at
least two that admits a 2-to-1 map to the projective line over an algebraic closure `K̄` of `K`.

A curve over `K` is proper if and only if it is projective, so projectivity is stated as
properness. A 2-to-1 map `X_K̄ ⟶ ℙ¹` from the base change `X_K̄` of `X` to `K̄` is the same as a
rational function `x` on `X_K̄` with `[K̄(X_K̄) : K̄(x)] = 2`, and the genus of `X` is the genus of
the function field `K̄(X_K̄)` over `K̄`; these standard facts about curves are not formalised
here. So the last two conditions say that `K̄(X_K̄)` is a hyperelliptic function field in the sense
of Tau Ceti's `TauCeti.IsHyperellipticFunctionField`, whose separability condition holds
automatically over the perfect field `K̄`.

The function field `K(X)` itself is hyperelliptic over `K`, in Tau Ceti's sense, when the 2-to-1 map
is defined over `K`; away from characteristic two it then has a Weierstrass model `y² = f(x)`,
`TauCeti.IsHyperellipticFunctionField.exists_squarefree_sq_eq_aeval`. The general models
`y² + h(x)y = f(x)` and the conic models in `ℙ³` are not formalised here.

## Main definitions

* `AlgebraicGeometry.Scheme.geometricBaseChange`: the base change `X_K̄` of a scheme `X` over `K`
  to the algebraic closure of `K`.
* `AlgebraicGeometry.Scheme.IsHyperellipticCurveOver` (LMFDB `ag.hyperelliptic_curve`).

## Main results

* `AlgebraicGeometry.Scheme.isHyperellipticCurveOver_iff`: a smooth proper algebraic curve is
  hyperelliptic if and only if `K̄(X_K̄)` has genus at least two and contains a rational function
  field `K̄(x)` of index two.
-/

namespace AlgebraicGeometry.Scheme

open CategoryTheory TauCeti
open scoped IntermediateField

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]

variable (K X) in
/-- The base change `X_K̄ = X ×_K K̄` of a scheme `X` over `K` to the algebraic closure `K̄` of `K`,
as a scheme over `K̄`. -/
noncomputable abbrev geometricBaseChange : Over (Spec (.of (AlgebraicClosure K))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).obj
    (X.asOver (Spec (.of K)))

instance [X.IsVarietyOver K] : IsIntegral (X.geometricBaseChange K).left :=
  IsVarietyOver.isIntegral (AlgebraicClosure K)

variable (K) in
/-- A **hyperelliptic curve** over a field `K` (LMFDB `ag.hyperelliptic_curve`): a smooth projective
algebraic curve over `K` of genus `g ≥ 2` that admits a 2-to-1 map to `ℙ¹` over the algebraic
closure `K̄` of `K`.

Projectivity is stated as properness, which is equivalent for curves. The genus and the 2-to-1 map
are read off the function field `K̄(X_K̄)` of the base change of `X` to `K̄`: it is a hyperelliptic
function field over `K̄`, of genus at least two with a rational subfield `K̄(x)` of index two. -/
class IsHyperellipticCurveOver : Prop extends X.IsAlgebraicCurveOver K, Smooth (X ↘ Spec (.of K)),
    IsProper (X ↘ Spec (.of K)) where
  /-- The function field of the base change to the algebraic closure is hyperelliptic. -/
  isHyperellipticFunctionField :
    IsHyperellipticFunctionField (AlgebraicClosure K) (X.geometricBaseChange K).left.functionField

/-- A smooth proper algebraic curve `X` over `K` is hyperelliptic if and only if the function field
`K̄(X_K̄)` of its base change to the algebraic closure has genus at least two and contains a
rational function field `K̄(x)` of index two, that is `X_K̄` admits a 2-to-1 map to `ℙ¹`. -/
lemma isHyperellipticCurveOver_iff [X.IsAlgebraicCurveOver K] [Smooth (X ↘ Spec (.of K))]
    [IsProper (X ↘ Spec (.of K))] : X.IsHyperellipticCurveOver K ↔ 2 ≤ genus (AlgebraicClosure K)
    (X.geometricBaseChange K).left.functionField ∧ ∃ x : (X.geometricBaseChange
    K).left.functionField, Transcendental (AlgebraicClosure K) x ∧ Module.finrank (AlgebraicClosure
    K)⟮x⟯ (X.geometricBaseChange K).left.functionField = 2 :=
  (Iff.intro (·.isHyperellipticFunctionField) fun h ↦ ⟨h⟩).trans
    isHyperellipticFunctionField_iff_two_le_genus_and_exists_finrank_adjoin_eq_two

end AlgebraicGeometry.Scheme
