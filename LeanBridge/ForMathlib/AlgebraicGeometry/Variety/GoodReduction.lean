import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import TauCeti.AlgebraicGeometry.AbelianVariety.Basic
import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Basic
import TauCeti.RingTheory.DedekindDomain.LocalizationAtPrime

/-!
# Good and bad reduction

A smooth proper variety `X` over a number field `K` has good reduction at a prime `𝔭` of `K` if it
is the generic fibre of a smooth proper scheme over the local ring `𝒪_{K,𝔭}`; otherwise `𝔭` is a
prime of bad reduction. It has potential good reduction at `𝔭` if its base change to some finite extension
`L / K` has good reduction at every prime of `L` above `𝔭`.

Good reduction is defined here for a scheme `X` over the fraction field `K` of any Dedekind domain
`O`, at a height-one prime `v` of `O`, through Tau Ceti's models (`TauCeti.Model`): a flat finitely
presented scheme over the discrete valuation ring `O_v = Localization.AtPrime v` with an
identification of its generic fibre with `X`. Good reduction asks for such a model that is proper
and smooth. The LMFDB's case is `O = 𝒪_K` for a number field `K`.

For an abelian variety `A` of dimension `g` (Tau Ceti's
`TauCeti.AlgebraicGeometry.AbelianVariety`), the LMFDB's primes of bad reduction are those at
which the reduction of `A` is not an abelian variety of dimension `g`; by the theory of Néron
models this is the failure of good reduction in the above sense, which is the definition used
here. The finiteness of the set of primes of bad reduction, its description through the conductor,
and the comparison between a curve and its Jacobian are not formalised.

## Main definitions

* `AlgebraicGeometry.Scheme.HasGoodReductionAt` (LMFDB `ag.good_reduction`).
* `AlgebraicGeometry.Scheme.badReductionPrimes` (LMFDB `ag.good_reduction`): the primes of bad
  reduction.
* `AlgebraicGeometry.Scheme.HasPotentialGoodReductionAt` (LMFDB `ag.potential_good_reduction`).
* `TauCeti.AlgebraicGeometry.AbelianVariety.HasGoodReductionAt` (LMFDB `ag.bad_prime`).
* `TauCeti.AlgebraicGeometry.AbelianVariety.badPrimes` (LMFDB `ag.bad_prime`): the primes of bad
  reduction of an abelian variety.
-/

open AlgebraicGeometry CategoryTheory Limits IsDedekindDomain NumberField

namespace AlgebraicGeometry.Scheme

universe u

variable {O K : Type u} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K] {X : Scheme.{u}} (toK : X ⟶ Spec (.of K))

/-- A scheme `X` over the fraction field `K` of a Dedekind domain `O`, such as a smooth proper
variety over a number field, has **good reduction** (LMFDB `ag.good_reduction`) at a height-one
prime `v` of `O` if it is the generic fibre of a smooth proper scheme over the discrete valuation
ring `O_v`: it has a model over `O_v` (Tau Ceti's `TauCeti.Model`, flat and finitely presented with
an identification of its generic fibre with `X`) that is proper and smooth over `O_v`. -/
def HasGoodReductionAt (v : HeightOneSpectrum O) : Prop :=
  ∃ M : TauCeti.Model (Localization.AtPrime v.asIdeal) K X toK, M.IsProper ∧ Smooth M.toBase

/-- The set of **primes of bad reduction** (LMFDB `ag.good_reduction`) of a scheme `X` over the
fraction field `K` of a Dedekind domain `O`: the height-one primes of `O` at which `X` does not have
good reduction. -/
def badReductionPrimes : Set (HeightOneSpectrum O) :=
  {v | ¬HasGoodReductionAt toK v}

lemma mem_badReductionPrimes {v : HeightOneSpectrum O} :
    v ∈ badReductionPrimes toK ↔ ¬HasGoodReductionAt toK v :=
  Iff.rfl

/-- A scheme `X` over a number field `K`, such as a smooth proper variety, has **potential good
reduction** (LMFDB `ag.potential_good_reduction`) at a prime `𝔭` of `K` if there is a finite
extension `L / K`, a number field, such that the base change `X_L = X ×_K L` has good reduction at
every prime `𝔮` of `L` above `𝔭`. -/
def HasPotentialGoodReductionAt (𝔭 : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
    ∀ 𝔮 : HeightOneSpectrum (𝓞 L), 𝔮.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = 𝔭.asIdeal →
      HasGoodReductionAt (pullback.snd toK (Spec.map (CommRingCat.ofHom (algebraMap K L)))) 𝔮

end AlgebraicGeometry.Scheme

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {O K : Type u} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K] (A : AbelianVariety K)

/-- An abelian variety `A` of dimension `g` over the fraction field `K` of a Dedekind domain `O`,
such as a number field, has **good reduction** at a height-one prime `v` of `O` if it is the generic
fibre of a smooth proper scheme over `O_v`; by the theory of Néron models, this is the case if and
only if the reduction of `A` modulo `v` is an abelian variety of dimension `g`, the condition of
LMFDB `ag.bad_prime`. -/
def HasGoodReductionAt (v : HeightOneSpectrum O) : Prop :=
  Scheme.HasGoodReductionAt A.toOver.hom v

/-- The **primes of bad reduction** (LMFDB `ag.bad_prime`) of an abelian variety `A` over the
fraction field `K` of a Dedekind domain `O`, such as a number field: the height-one primes of `O`
at which `A` does not have good reduction. -/
def badPrimes : Set (HeightOneSpectrum O) :=
  {v | ¬A.HasGoodReductionAt v}

end TauCeti.AlgebraicGeometry.AbelianVariety
