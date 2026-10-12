import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# The Frey–Hellegouarch curve

## Main definitions

* `WeierstrassCurve.freyCurve` (LMFDB `ec.q.frey`).
-/

namespace WeierstrassCurve

/-- The **Frey–Hellegouarch curve** (LMFDB `ec.q.frey`) `y² = x * (x - A) * (x + B)` of a pair
`A B : R`: the Weierstrass curve with `a₂ = B - A`, `a₄ = -A * B` and `a₁ = a₃ = a₆ = 0`. Its
discriminant is `16A²B²(A + B)²`, so over a field of characteristic not `2` it is an elliptic
curve exactly when `A`, `B` and `A + B` are all nonzero (in general, when that discriminant is a
unit). -/
def freyCurve {R : Type*} [CommRing R] (A B : R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := B - A
  a₃ := 0
  a₄ := -(A * B)
  a₆ := 0

end WeierstrassCurve
