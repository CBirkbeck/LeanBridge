import Verso
import VersoManual
import VersoBlueprint
import Mathlib
import Init.Core
import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.ComplexMultiplication
import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.Isogenous
import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.Simple
import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Basic
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.ComplexPeriod
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.FaltingsHeight
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.GlobalPeriod
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.MordellWeilGenerators
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.Regulator
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.SzpiroRatio
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.Tamagawa
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.TorsionGrowth
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.BSD.Conjecture
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.BSD.LFunction
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.BSD.Sha
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.ComplexMultiplication.Basic
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.Basic
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.Maximal
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
import LeanBridge.ForMathlib.NumberTheory.ModularCurve.FundamentalDomain
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Analytic.AnalyticConductor
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Analytic.Petersson
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Analytic.Satake
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Analytic.SturmBound
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Eisenstein.Series
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Eisenstein.Subspace
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.CoefficientRing
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Dimension
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Embedding
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisConjugate
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisOrbit
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.HeckeCharpoly
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Level
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Maximal
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.NewformSubspace
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.TraceForm
import LeanBridge.ForMathlib.NumberTheory.ModularForms.SatoTate.GaloisRepresentation
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.Basic
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.InnerTwist
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.Minimal
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.Multiplicity
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.SelfTwist
import LeanBridge.ForMathlib.NumberTheory.NumberField.AbelianConductor
import LeanBridge.ForMathlib.NumberTheory.NumberField.FieldIndex
import LeanBridge.ForMathlib.NumberTheory.NumberField.FrobeniusCycleType
import LeanBridge.ForMathlib.NumberTheory.NumberField.MaximalCMSubfield
import LeanBridge.ForMathlib.NumberTheory.NumberField.Polredabs
import LeanBridge.ForMathlib.NumberTheory.NumberField.ReflexField
import LeanBridge.ForMathlib.NumberTheory.NumberField.Sibling
import LeanBridge.ForMathlib.NumberTheory.NumberField.Units.SignatureRank
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Over
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Basic.Complex.Basic
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Data.Nat.PrimeFin
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Separable
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IsSubnormal
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.Petersson
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.Order.Atoms
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Radical.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.SetTheory.Cardinal.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Irreducible
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sets.Closeds
import TauCeti.Algebra.Module.Torsion.TateModule
import TauCeti.AlgebraicGeometry.AbelianVariety.Basic
import TauCeti.AlgebraicGeometry.AbelianVariety.End.BaseChange
import TauCeti.AlgebraicGeometry.AbelianVariety.End.Basic
import TauCeti.AlgebraicGeometry.AbelianVariety.Product
import TauCeti.AlgebraicGeometry.Cohomology.Genus
import TauCeti.AlgebraicGeometry.Curves.Basic
import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.AbcQuality
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Galois
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Integral
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.NonsingularReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.CanonicalHeight.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.FreyCurve.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer
import TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.ComplexMultiplication
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Torsion
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Class
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.DiscriminantIdeal
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.LocalDiscriminant
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.ObstructionExponent
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.OrdinaryReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.PotentialGoodReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Reduced
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Semistable
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Valuation
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalPairModel
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.PointModTorsion.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.Regulator.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.RealPeriod
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.OfWeierstrass
import TauCeti.AlgebraicGeometry.EllipticCurve.Supersingular
import TauCeti.AlgebraicGeometry.EllipticCurve.Szpiro
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Curve
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Symbol
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Galois
import TauCeti.AlgebraicGeometry.EllipticCurve.Twist.Cocycle
import TauCeti.AlgebraicGeometry.GroupScheme.Torsion
import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus
import TauCeti.FieldTheory.GaloisGroups.Discriminant.Field
import TauCeti.FieldTheory.GaloisGroups.NormalClosure
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Composite
import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
import TauCeti.NumberTheory.LocalField.RamificationGroup
import TauCeti.NumberTheory.LocalField.UnitFiltration.RamificationGroup
import TauCeti.NumberTheory.LocalField.WildInertia
import TauCeti.NumberTheory.ModularForms.AtkinLehner.Matrix
import TauCeti.NumberTheory.ModularForms.AtkinLehner.Normalized
import TauCeti.NumberTheory.ModularForms.AtkinLehner.Operator
import TauCeti.NumberTheory.ModularForms.AtkinLehner.Sign
import TauCeti.NumberTheory.ModularForms.Conjugate
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.Degeneracy
import TauCeti.NumberTheory.ModularForms.DiamondOperators
import TauCeti.NumberTheory.ModularForms.Fricke.Normalized
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Action
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
import TauCeti.NumberTheory.ModularForms.LFunction.FunctionalEquation
import TauCeti.NumberTheory.ModularForms.Newforms.AnalyticInvariants
import TauCeti.NumberTheory.ModularForms.Newforms.Basic
import TauCeti.NumberTheory.ModularForms.Newforms.Conjugate
import TauCeti.NumberTheory.ModularForms.Newforms.Fields
import TauCeti.NumberTheory.ModularForms.Newforms.Fricke
import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform
import TauCeti.NumberTheory.ModularForms.Newforms.Newform
import TauCeti.NumberTheory.ModularForms.Newforms.NumberField
import TauCeti.NumberTheory.ModularForms.Newforms.OrthogonalBasis
import TauCeti.NumberTheory.ModularForms.Newforms.Satake
import TauCeti.NumberTheory.ModularForms.Newforms.SelfDual
import TauCeti.NumberTheory.ModularForms.Norm.Cusps
import TauCeti.NumberTheory.ModularForms.SturmBound
import TauCeti.NumberTheory.MulChar.GaloisOrbit
import TauCeti.NumberTheory.NumberField.Global.Orders.Basic
import TauCeti.NumberTheory.NumberField.Global.RayClass.Narrow.Kernel
import TauCeti.NumberTheory.NumberField.Index.Basic
import TauCeti.NumberTheory.NumberField.Index.CommonIndexDivisor
import TauCeti.NumberTheory.NumberField.Monogenic
import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Basic
import TauCeti.NumberTheory.NumberField.RamifiedPrimes
import TauCeti.NumberTheory.NumberField.TotallyPositive
import TauCeti.RingTheory.Ideal.RamificationGroup

open Verso Verso.Genre Verso.Genre.Manual Informal

tex_prelude r#"\def\C{\mathbb{C}}
\def\R{\mathbb{R}}
\def\Q{\mathbb{Q}}
\def\Z{\mathbb{Z}}
\def\F{\mathbb{F}}
\def\H{\mathbb{H}}
\def\HH{\mathcal{H}}
\def\integers{\mathcal{O}}
\def\SL{\textrm{SL}}
\def\GL{\textrm{GL}}
\def\PSL{\textrm{PSL}}
\def\PGL{\textrm{PGL}}
\def\ASL{\textrm{ASL}}
\def\AGL{\textrm{AGL}}
\def\ASp{\textrm{ASp}}
\def\Sp{\textrm{Sp}}
\def\PSp{\textrm{PSp}}
\def\SO{\textrm{SO}}
\def\PSO{\textrm{PSO}}
\def\PO{\textrm{PO}}
\def\PGO{\textrm{PO}}
\def\SU{\textrm{SU}}
\def\PSU{\textrm{PSU}}
\def\SOPlus{\textrm{SO}^+}
\def\SOMinus{\textrm{SO}^-}
\def\GO{\textrm{O}}
\def\Orth{\textrm{O}}
\def\GOPlus{\textrm{O}^+}
\def\OPlus{\textrm{O}^+}
\def\OrthPlus{\textrm{O}^+}
\def\GOMinus{\textrm{O}^-}
\def\OrthMinus{\textrm{O}^-}
\def\OMinus{\textrm{O}^-}
\def\GU{\textrm{GU}}
\def\Unitary{\textrm{U}}
\def\CSp{\textrm{GSp}}
\def\GSp{\textrm{GSp}}
\def\CSO{\textrm{GSO}}
\def\GSO{\textrm{GSO}}
\def\CSOPlus{\textrm{GSO}^+}
\def\GSOPlus{\textrm{GSO}^+}
\def\CSOMinus{\textrm{GSO}^-}
\def\GSOMinus{\textrm{GSO}^-}
\def\CSU{\textrm{GSU}}
\def\GSU{\textrm{GSU}}
\def\CO{\textrm{GO}}
\def\GOrth{\textrm{GO}}
\def\COPlus{\textrm{GO}^+}
\def\GOrthPlus{\textrm{GO}^+}
\def\COMinus{\textrm{GO}^-}
\def\GOrthMinus{\textrm{GO}^-}
\def\CU{\textrm{GU}}
\def\GUnitary{\textrm{GU}}
\def\OmegaPlus{\Omega^+}
\def\OmegaMinus{\Omega^-}
\def\Spin{\textrm{Spin}}
\def\SpinPlus{\textrm{Spin}^+}
\def\SpinMinus{\textrm{Spin}^-}
\def\PSOPlus{\textrm{PSO}^+}
\def\POPlus{\textrm{PO}^+}
\def\PGOPlus{\textrm{PO}^+}
\def\PU{\textrm{PU}}
\def\PGU{\textrm{PU}}
\def\PSOMinus{\textrm{PSO}^-}
\def\POMinus{\textrm{PO}^-}
\def\PGOMinus{\textrm{PO}^-}
\def\POmega{\textrm{P}\Omega}
\def\POmegaPlus{\textrm{P}\Omega^+}
\def\POmegaMinus{\textrm{P}\Omega^-}
\def\PGammaL{\textrm{P}\Gamma\textrm{L}}
\def\PSigmaL{\textrm{P}\Sigma\textrm{L}}
\def\PSigmaSp{\textrm{P}\Sigma\textrm{Sp}}
\def\PGammaU{\textrm{P}\Gamma\textrm{U}}
\def\AGammaL{\textrm{A}\Gamma\textrm{L}}
\def\ASigmaL{\textrm{A}\Sigma\textrm{L}}
\def\ASigmaSp{\textrm{A}\Sigma\textrm{Sp}}
\def\Dic{\textrm{Dic}}
\def\SD{\textrm{SD}}
\def\OD{\textrm{OD}}
\def\He{\textrm{He}}
\def\HS{\textrm{HS}}
\def\McL{\textrm{McL}}
\def\Ru{\textrm{Ru}}
\def\Co{\textrm{Co}}
\def\Aut{\operatorname{Aut}}
\def\Out{\operatorname{Out}}
\def\End{\operatorname{End}}
\def\Gal{\operatorname{Gal}}
\def\Hom{\operatorname{Hom}}
\def\Ord{\operatorname{Ord}}
\def\Pic{\operatorname{Pic}}
\def\Reg{\operatorname{Rec}}
\def\Res{\operatorname{Res}}
\def\sgn{\operatorname{sgn}}
\def\Spec{\operatorname{Spec}}
\def\Sym{\operatorname{Sym}}
\def\trace{\operatorname{trace}}
\def\ideal#1{\mathfrak{ #1 }}
\def\classgroup#1{Cl(#1)}
\def\modstar#1#2{\left( #1/#2 \right)^\times}
\def\card#1{\# #1}
\def\Sha{\text{Ш}}
\def\smallsetminus{\setminus}"#
