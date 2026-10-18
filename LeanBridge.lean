import LeanBridge.Example
import LeanBridge.Galois
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Reduction
/- LMFDB elliptic-curve knowls formalized in Tau Ceti, which LeanBridge uses instead of its own
copies:
* `ec.global_minimal_model`, `ec.semi_global_minimal_model`: `WeierstrassCurve.IsGlobalMinimal`,
  `WeierstrassCurve.IsSemiGlobalMinimal`.
* `ec.q.minimal_weierstrass_equation`: `WeierstrassCurve.IsReducedMinimal`, and the reduced
  minimal model itself, `WeierstrassCurve.reducedMinimalModel`.
* `ec.local_minimal_discriminant`: `WeierstrassCurve.localMinimalDiscriminant`.
* `ec.minimal_discriminant`: `WeierstrassCurve.minimalDiscriminantIdeal`.
* `ec.semistable`: `WeierstrassCurve.IsSemistable`.
* `ec.potential_good_reduction`: `WeierstrassCurve.HasPotentialGoodReduction`.
* `ec.good_ordinary_reduction`, `ec.good_supersingular_reduction`:
  `WeierstrassCurve.HasGoodOrdinaryReduction`, `WeierstrassCurve.HasGoodSupersingularReduction`,
  whose reductions are `WeierstrassCurve.IsOrdinary`, `WeierstrassCurve.IsSupersingular`.
* `ec.obstruction_class`: `WeierstrassCurve.globalMinimalityClass` (curve-level) and
  `WeierstrassCurve.weierstrassDefectClass` (for an integral equation, via the exponents
  `WeierstrassCurve.obstructionExponentAt`).
* `ec.q.abc_quality`: `WeierstrassCurve.abcQuality`, which assumes `j ≠ 0` and `j ≠ 1728`.
* `ec.q.frey`: `TauCeti.freyCurve`.
* `ec.q.integral_points`: `WeierstrassCurve.integralPoints`, for an integral equation over `ℤ`.
* `ec.q.naive_height`: `WeierstrassCurve.naiveHeight`, on the minimal short model.
* `ec.q.canonical_height`: `WeierstrassCurve.Affine.Point.canonicalHeight`, in LMFDB's
  normalization `lim log max(|Aₙ|, |Dₙ|) / n²`, not the half of it that some sources use.
* The trace of Frobenius: `WeierstrassCurve.frobeniusTrace`. -/
import TauCeti.AlgebraicGeometry.EllipticCurve.AbcQuality
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Integral
import TauCeti.AlgebraicGeometry.EllipticCurve.CanonicalHeight.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.FreyCurve.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Class
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.DiscriminantIdeal
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.LocalDiscriminant
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.OrdinaryReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.PotentialGoodReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Reduced
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Semistable
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalPairModel
import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
import TauCeti.AlgebraicGeometry.EllipticCurve.Supersingular
