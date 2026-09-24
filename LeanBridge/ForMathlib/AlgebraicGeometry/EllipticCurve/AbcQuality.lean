import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.Radical.NatInt

/-!
# The abc quality of an elliptic curve over `ℚ`

## Main definitions

* `WeierstrassCurve.abcQuality` (LMFDB `ec.q.abc_quality`).
-/

namespace WeierstrassCurve

/-- The **abc quality** (LMFDB `ec.q.abc_quality`) of an elliptic curve over `ℚ`: the quotient
`log max(|a|, |b|, |c|) / log rad(abc)`, where `j / 1728 = a / c` in lowest terms, `b = c - a` and
`rad` is the radical of an integer. The quality is mathematically undefined when `j = 0` or
`j = 1728`: there `abc = 0`, so the denominator `log (rad 0) = log 1` vanishes and the expression
evaluates to `0`, an artifact of division by zero in Lean rather than a meaningful value. -/
noncomputable def abcQuality (E : WeierstrassCurve ℚ) [E.IsElliptic] : ℝ :=
  let a := (E.j / 1728).num
  let c := ((E.j / 1728).den : ℤ)
  let b := c - a
  Real.log ↑(max (max a.natAbs b.natAbs) c.natAbs) /
    Real.log ↑(UniqueFactorizationMonoid.radical (a * b * c).natAbs)

end WeierstrassCurve
