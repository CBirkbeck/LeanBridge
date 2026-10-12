import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount

/-!
# Supersingular and ordinary Weierstrass curves over finite fields

## Main definitions

* `WeierstrassCurve.IsSupersingular`: the characteristic divides the trace of Frobenius.
* `WeierstrassCurve.IsOrdinary`: not supersingular.

The trace of Frobenius is Tau Ceti's `WeierstrassCurve.frobeniusTrace`, `#F + 1 − #W(F)` with the
point count of the projective model (`WeierstrassCurve.pointCount`). On an elliptic curve it is
`#F + 1 − #E(F)` (`WeierstrassCurve.frobeniusTrace_eq_card_point`).
-/

namespace WeierstrassCurve

variable {F : Type*} [Field F] [Finite F]

/-- A Weierstrass curve over a finite field `F` is **supersingular** if its characteristic divides
its trace of Frobenius. In characteristic `2` and `3` this is not equivalent to the vanishing of the
trace (Silverman, *The Arithmetic of Elliptic Curves*, V.3.1). -/
def IsSupersingular (E : WeierstrassCurve F) : Prop :=
  (ringChar F : ℤ) ∣ E.frobeniusTrace

/-- A Weierstrass curve over a finite field is **ordinary** if it is not supersingular. -/
def IsOrdinary (E : WeierstrassCurve F) : Prop :=
  ¬ E.IsSupersingular

end WeierstrassCurve
