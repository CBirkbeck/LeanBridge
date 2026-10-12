import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Supersingular

/-!
# Reduction types of Weierstrass curves over a discrete valuation ring

LMFDB reduction-type predicates, on top of Mathlib's `IsMinimal`, `HasGoodReduction`,
`HasMultiplicativeReduction`, `HasSplitMultiplicativeReduction` and `HasAdditiveReduction`.

## Main definitions

* `WeierstrassCurve.IsBadReduction` (LMFDB `ec.bad_reduction`).
* `WeierstrassCurve.IsPotentialGoodReduction` (LMFDB `ec.potential_good_reduction`).
* `WeierstrassCurve.IsGoodOrdinaryReduction` (LMFDB `ec.good_ordinary_reduction`).
* `WeierstrassCurve.IsGoodSupersingularReduction` (LMFDB `ec.good_supersingular_reduction`).
* `WeierstrassCurve.IsNonsplitMultiplicativeReduction`
  (LMFDB `ec.nonsplit_multiplicative_reduction`).
* `WeierstrassCurve.ReductionType` (LMFDB `ec.reduction_type`).

Semistability (LMFDB `ec.semistable`) is Tau Ceti's `WeierstrassCurve.IsSemistable`.
-/

namespace WeierstrassCurve

open IsLocalRing

universe u v
variable (R : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A minimal Weierstrass curve over `K` has **bad reduction** (LMFDB `ec.bad_reduction`) if it
does not have good reduction, i.e. its reduction over the residue field of `R` is singular. -/
def IsBadReduction (W : WeierstrassCurve K) [IsMinimal R W] : Prop :=
  ¬ HasGoodReduction R W

/-- An elliptic curve over `K` has **potential good reduction** (LMFDB
`ec.potential_good_reduction`) if it has good reduction over some finite extension of `K`,
formalized via the equivalent condition that its `j`-invariant is integral over `R`
(Silverman, *The Arithmetic of Elliptic Curves*, VII.5.5). -/
def IsPotentialGoodReduction (W : WeierstrassCurve K) [W.IsElliptic] : Prop :=
  ∃ r : R, algebraMap R K r = W.j

/-- A Weierstrass curve over `K` with good reduction has **good ordinary reduction** (LMFDB
`ec.good_ordinary_reduction`) if its reduction over the finite residue field of `R` is
ordinary. -/
def IsGoodOrdinaryReduction [Finite (ResidueField R)] (W : WeierstrassCurve K)
    [HasGoodReduction R W] : Prop :=
  IsOrdinary (W.reduction R)

/-- A Weierstrass curve over `K` with good reduction has **good supersingular reduction** (LMFDB
`ec.good_supersingular_reduction`) if its reduction over the finite residue field of `R` is
supersingular. -/
def IsGoodSupersingularReduction [Finite (ResidueField R)] (W : WeierstrassCurve K)
    [HasGoodReduction R W] : Prop :=
  IsSupersingular (W.reduction R)

/-- A minimal Weierstrass curve over `K` has **non-split multiplicative reduction** (LMFDB
`ec.nonsplit_multiplicative_reduction`) if it has multiplicative reduction that is not split. -/
def IsNonsplitMultiplicativeReduction (W : WeierstrassCurve K) [IsMinimal R W] : Prop :=
  HasMultiplicativeReduction R W ∧ ¬ HasSplitMultiplicativeReduction R W

/-- The **reduction type** (LMFDB `ec.reduction_type`) of an elliptic curve at a prime: **good**,
**multiplicative** (split or non-split), or **additive**. -/
inductive ReductionType
  | good
  | multiplicative (split : Bool)
  | additive

end WeierstrassCurve
