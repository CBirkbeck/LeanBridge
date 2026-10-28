import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.Jacobian
import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.Simple

/-!
# Curves with a simple Jacobian

A smooth proper geometrically connected curve, such as a modular curve `X_H` with `det(H) = ℤ̂ˣ`
over `ℚ`, is simple if its Jacobian is a simple abelian variety. The existence of the Jacobian is
not formalised, so a curve is called simple when it has a simple Jacobian; when the curve has a
rational point, its Jacobian is unique up to isomorphism and this says that any Jacobian is simple.
The modular curves `X_H` themselves are not formalised.

## Main definitions

* `AlgebraicGeometry.Scheme.HasSimpleJacobian` (LMFDB `modcurve.simple`): a curve is simple.

## Main results

* `AlgebraicGeometry.Scheme.hasSimpleJacobian_iff`: a curve with a rational point is simple if and
  only if a given Jacobian of it is simple.
-/

open CategoryTheory MonoidalCategory TauCeti AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable {K : Type u} [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]
  [IsProper (X ↘ Spec (.of K))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of K))]
  [GeometricallyConnected (X ↘ Spec (.of K))]

variable (K) in
/-- A smooth proper geometrically connected curve `X` over `K` is **simple** (LMFDB
`modcurve.simple`) if its Jacobian is a simple abelian variety: here, if it has a Jacobian `J` that
is simple. When `X` has a rational point, its Jacobian is unique up to isomorphism, so this means
that every Jacobian of `X` is simple (`hasSimpleJacobian_iff`). -/
def HasSimpleJacobian : Prop :=
  ∃ J : AbelianVariety K, J.IsJacobian X ∧ J.IsSimple

/-- **A curve with a rational point is simple if and only if a given Jacobian of it is simple.** -/
lemma hasSimpleJacobian_iff (x₀ : 𝟙_ (Over (Spec (.of K))) ⟶ X.asOver (Spec (.of K)))
    {J : AbelianVariety K} (hJ : J.IsJacobian X) : X.HasSimpleJacobian K ↔ J.IsSimple := by
  refine ⟨fun ⟨J', hJ', hs⟩ ↦ ?_, fun hs ↦ ⟨J, hJ, hs⟩⟩
  rcases hJ'.nonempty_iso x₀ hJ with ⟨e⟩
  exact (AbelianVariety.isSimple_congr e).mp hs

end AlgebraicGeometry.Scheme
