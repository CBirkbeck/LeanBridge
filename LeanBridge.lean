import LeanBridge.Example
import LeanBridge.Galois
import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.ComplexMultiplication
import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.Isogenous
import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.Jacobian
import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.Simple
import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Basic
import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Hyperelliptic
import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Quotient
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.ComplexPeriod
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.FaltingsHeight
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.GlobalPeriod
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.LocalData
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.MordellWeilGenerators
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.Regulator
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.SzpiroRatio
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.Tamagawa
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.TorsionGrowth
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.BSD.Conjecture
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.BSD.LFunction
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.BSD.Sha
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.ComplexMultiplication.Basic
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.AdelicImage
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.Basic
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.Maximal
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.ModEllImage
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Isogeny.Basic
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Isogeny.Class
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Isogeny.ClassDegree
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Isogeny.CyclicDual
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Isogeny.Graph
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Isogeny.Matrix
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Isogeny.QCurve
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Label.LMFDB
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.LevelStructure
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Reduction
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Twist.Basic
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Twist.MinimalTwist
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Twist.QuarticSextic
import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.Automorphism
import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.Curve
import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.Equation
import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.FunctionField
import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.MinimalEquation
import LeanBridge.ForMathlib.AlgebraicGeometry.Variety.Affine
import LeanBridge.ForMathlib.AlgebraicGeometry.Variety.Basic
import LeanBridge.ForMathlib.AlgebraicGeometry.Variety.FieldOfDefinition
import LeanBridge.ForMathlib.AlgebraicGeometry.Variety.Projective
import LeanBridge.ForMathlib.Analysis.Complex.UpperHalfPlane.Completed
import LeanBridge.ForMathlib.GroupTheory.PolycyclicPresentation
import LeanBridge.ForMathlib.GroupTheory.SubnormalSeries
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Borel
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Cartan
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.CartanNormalizer
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Exceptional
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.LeastPrimitiveRoot
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.NonsplitCartan
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.SplitCartan
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.SutherlandLabel
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.SymplecticIsomorphism
import LeanBridge.ForMathlib.NumberTheory.ArithmeticFunction.DivisorFunction
import LeanBridge.ForMathlib.NumberTheory.Artin.Basic
import LeanBridge.ForMathlib.NumberTheory.Artin.Conductor
import LeanBridge.ForMathlib.NumberTheory.Artin.Parity
import LeanBridge.ForMathlib.NumberTheory.DirichletCharacter.GaloisOrbitLabel
import LeanBridge.ForMathlib.NumberTheory.DirichletCharacter.Minimal
import LeanBridge.ForMathlib.NumberTheory.LFunction.AnalyticRank
import LeanBridge.ForMathlib.NumberTheory.LFunction.Basic
import LeanBridge.ForMathlib.NumberTheory.LFunction.RiemannHypothesis
import LeanBridge.ForMathlib.NumberTheory.LFunction.RiemannZeta
import LeanBridge.ForMathlib.NumberTheory.ModularCurve.FullModularCurve
import LeanBridge.ForMathlib.NumberTheory.ModularCurve.FundamentalDomain
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Analytic.AnalyticConductor
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Analytic.Petersson
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Analytic.Satake
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Analytic.SturmBound
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Eisenstein.NewOld
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Eisenstein.Series
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Eisenstein.Subspace
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.CoefficientRing
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.ComplexAutomorphism
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Dimension
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Embedding
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisConjugate
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisOrbit
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.HeckeCharpoly
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Level
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Maximal
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.NewformSubspace
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.TraceBound
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.TraceForm
import LeanBridge.ForMathlib.NumberTheory.ModularForms.SatoTate.GaloisRepresentation
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.Basic
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.InnerTwist
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.Minimal
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.Multiplicity
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.SelfTwist
import LeanBridge.ForMathlib.NumberTheory.NumberField.AbelianConductor
import LeanBridge.ForMathlib.NumberTheory.NumberField.ClassNumberFormula
import LeanBridge.ForMathlib.NumberTheory.NumberField.FieldIndex
import LeanBridge.ForMathlib.NumberTheory.NumberField.FrobeniusCycleType
import LeanBridge.ForMathlib.NumberTheory.NumberField.MaximalCMSubfield
import LeanBridge.ForMathlib.NumberTheory.NumberField.Place
import LeanBridge.ForMathlib.NumberTheory.NumberField.Polredabs
import LeanBridge.ForMathlib.NumberTheory.NumberField.ReflexField
import LeanBridge.ForMathlib.NumberTheory.NumberField.ReflexReflexField
import LeanBridge.ForMathlib.NumberTheory.NumberField.SerreOdlyzkoBound
import LeanBridge.ForMathlib.NumberTheory.NumberField.Sibling
import LeanBridge.ForMathlib.NumberTheory.NumberField.Units.SignatureRank
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeightFunction
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilHeight
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial
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
