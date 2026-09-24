import LeanBridge.Example
import LeanBridge.Galois
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.AbcQuality
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Frey
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.IntegralPoints
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Reduction
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Supersingular
/- LMFDB elliptic-curve knowls formalized in Tau Ceti, which LeanBridge uses instead of its own
copies:
* `ec.global_minimal_model`, `ec.semi_global_minimal_model`: `WeierstrassCurve.IsGlobalMinimal`,
  `WeierstrassCurve.IsSemiGlobalMinimal`.
* `ec.local_minimal_discriminant`: `WeierstrassCurve.localMinimalDiscriminant`.
* `ec.minimal_discriminant`: `WeierstrassCurve.minimalDiscriminantIdeal`.
* `ec.semistable`: `WeierstrassCurve.IsSemistable`.
* `ec.obstruction_class`: `WeierstrassCurve.globalMinimalityClass` (curve-level) and
  `WeierstrassCurve.weierstrassDefectClass` (for an integral equation, via the exponents
  `WeierstrassCurve.obstructionExponentAt`).
* `ec.q.naive_height`: `WeierstrassCurve.naiveHeight`, on the minimal short model.
* `ec.q.canonical_height`: `WeierstrassCurve.Affine.Point.canonicalHeight`, which is half of
  LMFDB's normalization (the knowl notes both conventions).
* The trace of Frobenius: `WeierstrassCurve.frobeniusTrace`. -/
import TauCeti.AlgebraicGeometry.EllipticCurve.CanonicalHeight
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Class
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.DiscriminantIdeal
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.LocalDiscriminant
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Semistable
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalPairModel
