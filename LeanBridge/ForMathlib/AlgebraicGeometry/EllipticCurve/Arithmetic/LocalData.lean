import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.Tamagawa
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Reduction
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor

/-!
# The local data of an elliptic curve over a number field

The local data of an elliptic curve `E` over a number field `K` at a prime `𝔭` (LMFDB
`ec.local_data`) consists of the Tamagawa number `c_𝔭`, the Kodaira symbol, the reduction type, the
local root number, the conductor valuation `ord_𝔭(𝔑)`, the discriminant valuation `ord_𝔭(𝔇)` and
the valuation `ord_𝔭(j)₋` of the denominator of the `j`-invariant. This file bundles all of them
but the local root number, the sign of the local functional equation, whose definition (the
`ε`-factor of the local Galois representation) is out of reach.

The Tamagawa number is `WeierstrassCurve.tamagawaNumber`, read on the completion at `𝔭`. The other
data are read over the localisation `O_𝔭` of the ring of integers at `𝔭`, as for Tau Ceti's
`WeierstrassCurve.algorithmicConductor`: the Kodaira symbol is Tau Ceti's
`WeierstrassCurve.reductionSymbol`, the symbol at which Tate's algorithm stops, the conductor
valuation is Tau Ceti's `WeierstrassCurve.algorithmicOggExponent`, which is the conductor exponent
by Ogg's formula, an identification not formalised there, and the discriminant valuation is Tau
Ceti's `WeierstrassCurve.localMinimalDiscriminantValuation`. The reduction type, an element of
`WeierstrassCurve.ReductionType`, is read on Mathlib's chosen minimal equation; that type does not
split good reduction into ordinary and supersingular reduction, which are Tau Ceti's
`WeierstrassCurve.HasGoodOrdinaryReduction` and `WeierstrassCurve.HasGoodSupersingularReduction`.

## Main definitions

* `WeierstrassCurve.reductionType`: the reduction type over a discrete valuation ring
  (LMFDB `ec.reduction_type`).
* `WeierstrassCurve.LocalData`: the local data of an elliptic curve at a prime, without the local
  root number (LMFDB `ec.local_data`).
* `WeierstrassCurve.localData`: the local data of an elliptic curve over a number field at a prime
  (LMFDB `ec.local_data`).

## Main results

* `WeierstrassCurve.reductionType_eq_good_iff`,
  `WeierstrassCurve.reductionType_eq_multiplicative_iff` and
  `WeierstrassCurve.reductionType_eq_additive_iff`: the reduction type is good, multiplicative
  (split or not) or additive exactly when a minimal equation has good, multiplicative (split or
  not) or additive reduction.
* `WeierstrassCurve.localData_conductorValuation` and
  `WeierstrassCurve.localData_discriminantValuation`: the conductor and discriminant valuations
  are the exponents of `𝔭` in the algorithmic conductor and in the minimal discriminant ideal.
-/

open IsDedekindDomain NumberField

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K) (R : Type*) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K]

open scoped Classical in
/-- The **reduction type** (LMFDB `ec.reduction_type`) of a Weierstrass curve over the fraction
field of a discrete valuation ring `R`: **good**, **multiplicative**, split or not, or **additive**,
according to the reduction of Mathlib's chosen minimal equation over `R`. Good reduction is not
split into ordinary and supersingular reduction here. -/
noncomputable def reductionType : ReductionType :=
  if (W.minimal R).HasGoodReduction R then .good
  else if (W.minimal R).HasMultiplicativeReduction R then
    .multiplicative (decide ((W.minimal R).HasSplitMultiplicativeReduction R))
  else .additive

/-- **The reduction type is good exactly at good reduction.** -/
lemma reductionType_eq_good_iff : W.reductionType R = .good ↔ (W.minimal R).HasGoodReduction R := by
  unfold reductionType
  split_ifs <;> simp_all

/-- **The reduction type is multiplicative exactly at multiplicative reduction**, and it is split
exactly at split multiplicative reduction. -/
lemma reductionType_eq_multiplicative_iff {b : Bool} : W.reductionType R = .multiplicative b ↔
    (W.minimal R).HasMultiplicativeReduction R ∧ ((W.minimal R).HasSplitMultiplicativeReduction R ↔
    b = true) := by
  unfold reductionType
  split_ifs with h₁ h₂
  · simp [h₁.not_hasMultiplicativeReduction]
  · cases b <;> simp [h₂]
  · simp [h₂]

/-- **The reduction type is additive exactly at additive reduction.** -/
lemma reductionType_eq_additive_iff :
    W.reductionType R = .additive ↔ (W.minimal R).HasAdditiveReduction R := by
  unfold reductionType
  split_ifs with h₁ h₂
  · simp [h₁.not_hasAdditiveReduction]
  · simp [h₂.not_hasAdditiveReduction]
  · exact iff_of_true rfl ((hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction
      R).resolve_left h₁ |>.resolve_left h₂)

/-- The **local data** (LMFDB `ec.local_data`) of an elliptic curve at a prime, without the local
root number: the Tamagawa number, the Kodaira symbol, the reduction type, the conductor valuation,
the discriminant valuation and the valuation of the denominator of the `j`-invariant. -/
structure LocalData where
  /-- The Tamagawa number `c_𝔭`. -/
  tamagawaNumber : ℕ
  /-- The Kodaira symbol. -/
  kodairaSymbol : TauCeti.ReductionSymbol
  /-- The reduction type. -/
  reductionType : ReductionType
  /-- The conductor valuation `ord_𝔭(𝔑)`. -/
  conductorValuation : ℕ
  /-- The discriminant valuation `ord_𝔭(𝔇)`, the valuation of the minimal discriminant. -/
  discriminantValuation : ℕ
  /-- The valuation `ord_𝔭(j)₋` of the denominator of the `j`-invariant. -/
  jDenominatorValuation : ℕ

variable [NumberField K] [W.IsElliptic] (p : HeightOneSpectrum (𝓞 K))

/-- The **local data** (LMFDB `ec.local_data`) of an elliptic curve `W` over a number field at a
prime `𝔭`, without the local root number: the Tamagawa number `c_𝔭(E)`, read on the completion at
`𝔭`, and, read over the localisation of the ring of integers at `𝔭`, the Kodaira symbol at which
Tate's algorithm stops, the reduction type, the algorithmic Ogg exponent `ord_𝔭(𝔑)`, the valuation
`ord_𝔭(𝔇)` of the minimal discriminant, and the valuation `ord_𝔭(j)₋ = max 0 (-ord_𝔭(j))` of the
denominator of the `j`-invariant. -/
noncomputable def localData : LocalData where
  tamagawaNumber := W.tamagawaNumber p
  kodairaSymbol := W.reductionSymbol (Localization.AtPrime p.asIdeal)
  reductionType := W.reductionType (Localization.AtPrime p.asIdeal)
  conductorValuation := W.algorithmicOggExponent (Localization.AtPrime p.asIdeal)
  discriminantValuation := W.localMinimalDiscriminantValuation (Localization.AtPrime p.asIdeal)
  jDenominatorValuation := (-(p.valuation K).ord W.j).toNat

/-- **The conductor valuation is the exponent of `𝔭` in the conductor**, the algorithmic conductor
of Tau Ceti. -/
lemma localData_conductorValuation : (W.localData p).conductorValuation = (Associates.mk
    p.asIdeal).count (Associates.mk (algorithmicConductor (𝓞 K) W)).factors :=
  (count_algorithmicConductor (𝓞 K) W p).symm

/-- **The discriminant valuation is the exponent of `𝔭` in the minimal discriminant ideal.** -/
lemma localData_discriminantValuation : (W.localData p).discriminantValuation = (Associates.mk
    p.asIdeal).count (Associates.mk (minimalDiscriminantIdeal (𝓞 K) W)).factors :=
  (count_minimalDiscriminantIdeal_eq_localMinimalDiscriminantValuation (𝓞 K) W p).symm

end WeierstrassCurve
