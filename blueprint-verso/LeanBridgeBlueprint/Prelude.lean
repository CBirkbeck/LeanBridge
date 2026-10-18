import Verso
import VersoManual
import VersoBlueprint
import Mathlib
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Reduction
import TauCeti.Algebra.Module.Torsion.TateModule
import TauCeti.AlgebraicGeometry.AbelianVariety.Basic
import TauCeti.AlgebraicGeometry.AbelianVariety.End.BaseChange
import TauCeti.AlgebraicGeometry.AbelianVariety.End.Basic
import TauCeti.AlgebraicGeometry.Cohomology.Genus
import TauCeti.AlgebraicGeometry.Curves.Basic
import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.AbcQuality
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Integral
import TauCeti.AlgebraicGeometry.EllipticCurve.CanonicalHeight.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.FreyCurve.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.ComplexMultiplication
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
import TauCeti.AlgebraicGeometry.EllipticCurve.RealPeriod
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.OfWeierstrass
import TauCeti.AlgebraicGeometry.EllipticCurve.Supersingular
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Curve
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Symbol
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Galois
import TauCeti.AlgebraicGeometry.GroupScheme.Torsion
import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus
import TauCeti.FieldTheory.GaloisGroups.Discriminant.Field
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Composite
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
import TauCeti.NumberTheory.ModularForms.Newforms.OrthogonalBasis
import TauCeti.NumberTheory.ModularForms.Newforms.SelfDual
import TauCeti.NumberTheory.ModularForms.Norm.Cusps
import TauCeti.NumberTheory.NumberField.Global.Orders.Basic
import TauCeti.NumberTheory.NumberField.Index.Basic
import TauCeti.NumberTheory.NumberField.Index.CommonIndexDivisor
import TauCeti.NumberTheory.NumberField.Monogenic
import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Basic
import TauCeti.NumberTheory.NumberField.RamifiedPrimes
import TauCeti.NumberTheory.NumberField.TotallyPositive

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
