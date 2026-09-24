import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Integral points on a Weierstrass curve over `ℚ`

## Main definitions

* `WeierstrassCurve.integralPoints` (LMFDB `ec.q.integral_points`).
-/

namespace WeierstrassCurve

/-- The **integral points** (LMFDB `ec.q.integral_points`) of a Weierstrass curve over `ℚ`: the
affine points whose coordinates are integers. The knowl defines these for a given model, so the
set depends on the chosen model; it is finite by Siegel's theorem, which is not part of this
definition. -/
def integralPoints (W : WeierstrassCurve ℚ) : Set W.toAffine.Point :=
  {P | ∃ (x y : ℤ) (h : W.toAffine.Nonsingular (x : ℚ) (y : ℚ)),
    P = Affine.Point.some (x : ℚ) (y : ℚ) h}

end WeierstrassCurve
