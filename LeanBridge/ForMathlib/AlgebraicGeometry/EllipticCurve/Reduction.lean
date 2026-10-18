import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Reduction types of Weierstrass curves over a discrete valuation ring

LMFDB reduction-type predicates, on top of Mathlib's `IsMinimal`, `HasGoodReduction`,
`HasMultiplicativeReduction`, `HasSplitMultiplicativeReduction` and `HasAdditiveReduction`.

## Main definitions

* `WeierstrassCurve.IsBadReduction` (LMFDB `ec.bad_reduction`).
* `WeierstrassCurve.IsNonsplitMultiplicativeReduction`
  (LMFDB `ec.nonsplit_multiplicative_reduction`).
* `WeierstrassCurve.ReductionType` (LMFDB `ec.reduction_type`).

Semistability (LMFDB `ec.semistable`), potential good reduction (`ec.potential_good_reduction`) and
good ordinary or supersingular reduction (`ec.good_ordinary_reduction`,
`ec.good_supersingular_reduction`) are Tau Ceti's `WeierstrassCurve.IsSemistable`,
`WeierstrassCurve.HasPotentialGoodReduction`, `WeierstrassCurve.HasGoodOrdinaryReduction` and
`WeierstrassCurve.HasGoodSupersingularReduction`.
-/

namespace WeierstrassCurve

universe u v
variable (R : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A minimal Weierstrass curve over `K` has **bad reduction** (LMFDB `ec.bad_reduction`) if it
does not have good reduction, i.e. its reduction over the residue field of `R` is singular. -/
def IsBadReduction (W : WeierstrassCurve K) [IsMinimal R W] : Prop :=
  ¬ HasGoodReduction R W

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
