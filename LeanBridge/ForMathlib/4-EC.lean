import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.RingTheory.Radical
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.ClassGroup

/-!
# Elliptic curve definitions for LeanBridge (chapter 4)

Definitions from the LMFDB elliptic-curve knowls that are not (yet) in mathlib, written here in
mathlib style for the LeanBridge blueprint audit.
-/

namespace WeierstrassCurve

open IsLocalRing

section FiniteField

variable {F : Type*} [Field F] [Finite F]

/-- The trace of Frobenius `aₚ = #F + 1 − #E(F)` of an elliptic curve over a finite field `F`.
(`Nat.card` gives the true cardinality since `F` is finite.) -/
noncomputable def traceOfFrobenius (E : WeierstrassCurve F) [E.IsElliptic] : ℤ :=
  (Nat.card F : ℤ) + 1 - Nat.card E.toAffine.Point

/-- An elliptic curve over a finite field is **ordinary** if its characteristic `p` does not divide
its trace of Frobenius `aₚ`. This is the divisibility `p ∤ aₚ`, *not* `aₚ ≠ 0`: for `p ≥ 5` the two
agree, but in characteristic 2 and 3 they differ, and divisibility is the correct criterion
(see `IsSupersingular`). -/
def IsOrdinary (E : WeierstrassCurve F) [E.IsElliptic] : Prop :=
  ¬ (ringChar F : ℤ) ∣ traceOfFrobenius E

/-- An elliptic curve over a finite field is **supersingular** if its characteristic `p` divides its
trace of Frobenius `aₚ`. The criterion is `p ∣ aₚ`, **not** `aₚ = 0`: for `p ≥ 5` these coincide
(Hasse gives `|aₚ| ≤ 2√q < p`), but in characteristic 2 and 3 `|aₚ|` can reach or exceed `p`
(e.g. `aₚ = ±2` at `p = 2`), where `aₚ = 0` would misclassify. `p ∣ aₚ` is correct in all
characteristics (Silverman, *Arithmetic of Elliptic Curves*, V.3.1). -/
def IsSupersingular (E : WeierstrassCurve F) [E.IsElliptic] : Prop :=
  (ringChar F : ℤ) ∣ traceOfFrobenius E

end FiniteField

section Reduction

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A minimal Weierstrass curve over `K` has **additive reduction** (LMFDB `ec.additive_reduction`)
if its reduction over the residue field of `R` has a cuspidal singularity. Equivalently, both the
discriminant `Δ` and the invariant `c₄` of the reduced curve vanish: a singular Weierstrass curve
has a cusp iff `c₄ = 0` and a node iff `c₄ ≠ 0` (Silverman, *Arithmetic of Elliptic Curves*, III),
a criterion that is independent of the residue characteristic. -/
@[mk_iff]
class IsAdditiveReduction (W : WeierstrassCurve K) [IsMinimal R W] : Prop where
  additive : (W.reduction R).Δ = 0 ∧ (W.reduction R).c₄ = 0

/-- A minimal Weierstrass curve over `K` has **bad reduction** (LMFDB `ec.bad_reduction`) if its
reduction over the residue field of `R` is singular — equivalently, it does not have good
reduction. -/
def IsBadReduction (W : WeierstrassCurve K) [IsMinimal R W] : Prop :=
  ¬ IsGoodReduction R W

/-- A minimal Weierstrass curve over `K` has **multiplicative reduction** (LMFDB
`ec.multiplicative_reduction`) if its reduction over the residue field of `R` has a nodal
singularity: the discriminant `Δ` of the reduced curve vanishes but `c₄` does not. -/
@[mk_iff]
class IsMultiplicativeReduction (W : WeierstrassCurve K) [IsMinimal R W] : Prop where
  multiplicative : (W.reduction R).Δ = 0 ∧ (W.reduction R).c₄ ≠ 0

/-- A Weierstrass curve over `K` (with `R` a DVR, `K = Frac R`) has **potential good reduction**
(LMFDB `ec.potential_good_reduction`) if its `j`-invariant is integral, i.e. lies in `R`. By the
knowl / Silverman AEC VII.5.5 this is equivalent to `E` acquiring good reduction over a finite
extension. -/
def IsPotentialGoodReduction (W : WeierstrassCurve K) [W.IsElliptic] : Prop :=
  ∃ r : R, algebraMap R K r = W.j

/-- A minimal Weierstrass curve over `K` (with finite residue field) has **good ordinary reduction**
(LMFDB `ec.good_ordinary_reduction`) if it has good reduction and the reduced elliptic curve is
ordinary. (Ordinary uses `p ∤ aₚ`, the characteristic-independent criterion; see `IsOrdinary`.) -/
def IsGoodOrdinaryReduction [Finite (ResidueField R)] (W : WeierstrassCurve K) [IsMinimal R W] :
    Prop :=
  ∃ h : (W.reduction R).IsElliptic, @IsOrdinary _ _ (W.reduction R) h

/-- A minimal Weierstrass curve over `K` (with finite residue field) has **good supersingular
reduction** (LMFDB `ec.good_supersingular_reduction`) if it has good reduction and the reduced
elliptic curve is supersingular. (Uses `p ∣ aₚ`, not `aₚ = 0` — correct in char 2 and 3; see
`IsSupersingular`.) -/
def IsGoodSupersingularReduction [Finite (ResidueField R)] (W : WeierstrassCurve K)
    [IsMinimal R W] : Prop :=
  ∃ h : (W.reduction R).IsElliptic, @IsSupersingular _ _ (W.reduction R) h

/-- A minimal Weierstrass curve over `K` (with finite residue field) has **split multiplicative
reduction** (LMFDB `ec.split_multiplicative_reduction`) if it has multiplicative reduction whose
reduced curve's nonsingular points form `𝔾ₘ`, i.e. number `#𝔽 − 1`. This point-count criterion is
characteristic-independent: the smooth locus of a nodal cubic is `𝔾ₘ` (split) or the non-split
torus (non-split), of order `#𝔽 ∓ 1` in every characteristic — no tangent-cone analysis is
involved, so the char 2/3 subtleties do not arise. -/
def IsSplitMultiplicativeReduction [Finite (ResidueField R)] (W : WeierstrassCurve K)
    [IsMinimal R W] : Prop :=
  IsMultiplicativeReduction R W ∧
    Nat.card (W.reduction R).toAffine.Point = Nat.card (ResidueField R) - 1

/-- A minimal Weierstrass curve over `K` (with finite residue field) has **non-split multiplicative
reduction** (LMFDB `ec.nonsplit_multiplicative_reduction`) if it has multiplicative reduction with
`#Ẽ_ns(𝔽) = #𝔽 + 1` (the non-split torus). Like `IsSplitMultiplicativeReduction`, this point count
is characteristic-independent. -/
def IsNonsplitMultiplicativeReduction [Finite (ResidueField R)] (W : WeierstrassCurve K)
    [IsMinimal R W] : Prop :=
  IsMultiplicativeReduction R W ∧
    Nat.card (W.reduction R).toAffine.Point = Nat.card (ResidueField R) + 1

/-- The **local minimal discriminant** of `E` at the prime of the DVR `R` (LMFDB
`ec.local_minimal_discriminant`): the ideal `𝔭^e` of `R` generated by the discriminant of a local
minimal model `W.minimal R`, where `e` is that discriminant's valuation at the prime. -/
noncomputable def localMinimalDiscriminant (W : WeierstrassCurve K) : Ideal R :=
  Ideal.span {(integralModel R (W.minimal R)).Δ}

/-- The **reduction type** (LMFDB `ec.reduction_type`) of an elliptic curve at a prime: the
classification realized by the reduction-cluster predicates `IsGoodOrdinaryReduction`,
`IsGoodSupersingularReduction`, `IsSplitMultiplicativeReduction`, `IsNonsplitMultiplicativeReduction`
and `IsAdditiveReduction`. Assigning the type to a given `(curve, prime)` requires the trichotomy
that exactly one of these holds (a classification theorem), which is not provided here. -/
inductive ReductionType
  | goodOrdinary
  | goodSupersingular
  | splitMultiplicative
  | nonsplitMultiplicative
  | additive

end Reduction

section MordellWeil

variable {K : Type*} [Field K] [DecidableEq K]

/-- Given that `E(K)` is finitely generated — the **Mordell–Weil theorem**, taken here as the
hypothesis `[Module.Finite ℤ (Affine.Point W)]` since it is not proven in mathlib — the
**Mordell–Weil generators** (LMFDB `ec.mw_generators`) of `E/K` are a basis of the free part
`E(K) ⧸ torsion`. That quotient is finitely generated and torsion-free over the PID `ℤ`, hence free,
so it has a basis; these are the `rank`-many points generating `E(K)` modulo torsion. -/
noncomputable def mordellWeilGenerators (W : WeierstrassCurve K) [W.IsElliptic]
    [Module.Finite ℤ (Affine.Point W)] :=
  Module.Free.chooseBasis ℤ (Affine.Point W ⧸ Submodule.torsion ℤ (Affine.Point W))

end MordellWeil

section GlobalMinimal

open IsDedekindDomain

variable {O : Type*} [CommRing O] [IsDomain O] [IsDedekindDomain O]

/-- A Weierstrass model over `K = FractionRing O` (with `O` the ring of integers, a Dedekind domain)
is a **global minimal model** (LMFDB `ec.global_minimal_model`) if it is integral over `O` and is a
local minimal model at every nonzero prime of `O`. mathlib only has the *local* minimal-model theory
(`IsMinimal` over one DVR); this is the global assembly over all primes. The localization
`Localization.AtPrime v.asIdeal` of a Dedekind domain at a nonzero prime is a DVR with fraction field
`FractionRing O`, so `IsMinimal` applies at each `v`. -/
def IsGlobalMinimalModel (W : WeierstrassCurve (FractionRing O)) : Prop :=
  IsIntegral O W ∧ ∀ v : HeightOneSpectrum O,
    haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O v.ne_bot _
    IsMinimal (Localization.AtPrime v.asIdeal) W

/-- A Weierstrass model over `K = FractionRing O` is a **semi-global minimal model** (LMFDB
`ec.semi_global_minimal_model`) if it is integral over `O` and a local minimal model at every
nonzero prime of `O` except possibly one. Over a number field of class number greater than one an
elliptic curve may have no `IsGlobalMinimalModel`, but it always has a semi-global one; the
exceptional prime carries the obstruction class. (The knowl further records that at that prime the
discriminant valuation exceeds the minimal-discriminant valuation by `12`; that is a consequence
phrased via the minimal-discriminant ideal, so it is not part of this defining predicate.) -/
def IsSemiGlobalMinimalModel (W : WeierstrassCurve (FractionRing O)) : Prop :=
  IsIntegral O W ∧ ∃ v₀ : HeightOneSpectrum O, ∀ v : HeightOneSpectrum O, v ≠ v₀ →
    haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O v.ne_bot _
    IsMinimal (Localization.AtPrime v.asIdeal) W

/-- The **minimal discriminant ideal** (LMFDB `ec.minimal_discriminant`) of `E` over `O`:
`𝔡_min = ∏_v v ^ e_v`, the product over all nonzero primes `v` of `O` of `v ^ e_v`, where `e_v` is
the valuation of the discriminant of a local minimal model at `v` — the `v`-part of the local
minimal discriminant (cf. `localMinimalDiscriminant`). At a prime of good reduction `e_v = 0`, which
holds for all but finitely many `v`, so the (a priori infinite) product is finite. If `E` has a
`IsGlobalMinimalModel` then `𝔡_min = (Δ)`, the principal ideal of that model's discriminant. -/
noncomputable def minimalDiscriminantIdeal (W : WeierstrassCurve (FractionRing O)) : Ideal O :=
  ∏ᶠ v : HeightOneSpectrum O,
    v.asIdeal ^
      (haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
        IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O v.ne_bot _
      ((IsDiscreteValuationRing.addVal (Localization.AtPrime v.asIdeal))
        ((integralModel _ (W.minimal (Localization.AtPrime v.asIdeal))).Δ)).toNat)

/-- The unique **reduced minimal Weierstrass model** over `ℚ` (LMFDB
`ec.q.minimal_weierstrass_equation`): a global minimal model over `ℤ` whose coefficients are
normalized by `a₁, a₃ ∈ {0, 1}` and `a₂ ∈ {-1, 0, 1}`. These constraints single out the unique
representative among the global minimal models of `E / ℚ` (which differ by the integral variable
changes `[±1, r, s, t]`). The bare minimality is `IsGlobalMinimalModel` at `O := ℤ`; this adds the
canonical normal form. -/
def IsReducedMinimalModel (W : WeierstrassCurve (FractionRing ℤ)) : Prop :=
  IsGlobalMinimalModel W ∧
    (W.a₁ = 0 ∨ W.a₁ = 1) ∧ (W.a₂ = -1 ∨ W.a₂ = 0 ∨ W.a₂ = 1) ∧ (W.a₃ = 0 ∨ W.a₃ = 1)

/-- An elliptic curve over `K = FractionRing O` is **semistable** (LMFDB `ec.semistable`) if it has
no additive reduction at any prime of `O` — equivalently, good or multiplicative reduction
everywhere, i.e. multiplicative reduction at every bad prime. The reduction at `v` is read off the
local minimal model `W.minimal (Localization.AtPrime v.asIdeal)`. -/
def IsSemistable (W : WeierstrassCurve (FractionRing O)) : Prop :=
  ∀ v : HeightOneSpectrum O,
    haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O v.ne_bot _
    ¬ IsAdditiveReduction (Localization.AtPrime v.asIdeal)
        (W.minimal (Localization.AtPrime v.asIdeal))

/-- The **obstruction exponent** `fᵥ = (vᵥ(Δ) − eᵥ)/12` at a prime `v` for an integral model `W`
over `O`: the `v`-adic valuation of this model's discriminant minus the local minimal discriminant
valuation `eᵥ`, divided by `12` (an exact division, since two integral models' discriminant
valuations differ by a multiple of `12`). -/
noncomputable def obstructionExponent (W : WeierstrassCurve O) (v : HeightOneSpectrum O) : ℕ :=
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O v.ne_bot _
  ((IsDiscreteValuationRing.addVal (Localization.AtPrime v.asIdeal)
      (algebraMap O (Localization.AtPrime v.asIdeal) W.Δ)).toNat -
    (IsDiscreteValuationRing.addVal (Localization.AtPrime v.asIdeal)
      (integralModel _
        ((W.baseChange (FractionRing O)).minimal (Localization.AtPrime v.asIdeal))).Δ).toNat) / 12

/-- The **obstruction class** (Silverman's *Weierstrass class*, LMFDB `ec.obstruction_class`) of an
integral model `W` over `O`: the ideal class `[∏ᵥ 𝔭ᵥ^{fᵥ}] ∈ ClassGroup O`, where `𝔞 = ∏ᵥ 𝔭ᵥ^{fᵥ}`
satisfies `𝔞¹² = (Δ)·𝔇_min⁻¹` (Silverman, *The Arithmetic of Elliptic Curves*, VIII.8). It is trivial
iff `E` has a global minimal model. The product is taken inside the non-zero-divisor submonoid, so
each `𝔭ᵥ^{fᵥ}` carries its own nonzero proof (`pow_mem` of the prime `𝔭ᵥ ≠ ⊥`). -/
noncomputable def obstructionClass (W : WeierstrassCurve O) : ClassGroup O :=
  ClassGroup.mk0 (∏ᶠ v : HeightOneSpectrum O,
    (⟨v.asIdeal ^ obstructionExponent W v,
      pow_mem (mem_nonZeroDivisors_of_ne_zero (by simpa using v.ne_bot)) _⟩ :
        nonZeroDivisors (Ideal O)))

end GlobalMinimal

section Height

/-- The **naive height** (LMFDB `ec.q.naive_height`) of an elliptic curve over `ℚ` in short
Weierstrass form `y² = x³ + a₄x + a₆`: the quantity `max (4|a₄|³, 27|a₆|²)`. The `[W.IsShortNF]`
instance enforces the short-form requirement (`a₁ = a₂ = a₃ = 0`); a general curve must first be put
in short form (`W.toShortNF • W`) since the naive height depends on the chosen model. -/
def naiveHeight (W : WeierstrassCurve ℚ) [W.IsShortNF] : ℚ :=
  max (4 * |W.a₄| ^ 3) (27 * |W.a₆| ^ 2)

/-- The **naive height** of a rational point `P ∈ E(ℚ)`: `log max(|num x(P)|, |den x(P)|)`, the
height of its `x`-coordinate (and `0` at the point at infinity). -/
noncomputable def naivePointHeight {W : WeierstrassCurve ℚ} : W.toAffine.Point → ℝ
  | .zero => 0
  | @Affine.Point.some _ _ _ x _ _ => Real.log (max (x.num.natAbs : ℝ) (x.den : ℝ))

open Filter in
/-- The **canonical (Néron–Tate) height** (LMFDB `ec.q.canonical_height`) of a rational point:
`ĥ(P) = limₙ (1/n²) · log max(|Aₙ|, |Dₙ|)` where `x(nP) = Aₙ/Dₙ` in lowest terms — i.e. the limit of
`naivePointHeight (n • P) / n²`. (This is LMFDB's normalization; some sources halve it.) The limit
uses `limUnder`, which returns a junk value if the sequence diverges; convergence (the Néron–Tate
theorem) holds but is *not* proved here, so this definition captures the defining formula and gives
the correct real value, but is inert in proofs until convergence is established. -/
noncomputable def canonicalHeight {W : WeierstrassCurve ℚ} [W.IsElliptic]
    (P : W.toAffine.Point) : ℝ :=
  limUnder atTop (fun n : ℕ => naivePointHeight (n • P) / (n : ℝ) ^ 2)

end Height

section Frey

/-- The **Frey–Hellegouarch curve** (LMFDB `ec.q.frey`) of a pair `A, B` (from a triple with
`A + B = C`): the curve `y² = x(x - A)(x + B)`. Expanding `x(x - A)(x + B) = x³ + (B - A)x² - A*B*x`
gives the Weierstrass coefficients `a₂ = B - A`, `a₄ = -A*B`, with `a₁ = a₃ = a₆ = 0`. Its
discriminant is `Δ = 16*A²*B²*(A + B)²`, so it is an elliptic curve exactly when `A`, `B`, `A + B`
are all nonzero. -/
def freyCurve {R : Type*} [CommRing R] (A B : R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := B - A
  a₃ := 0
  a₄ := -(A * B)
  a₆ := 0

end Frey

section Quality

/-- The **abc quality** (LMFDB `ec.q.abc_quality`) of an elliptic curve over `ℚ`:
`log max(|a|, |b|, |c|) / log rad(abc)`, where `j/1728 = a/c` is in lowest terms and `b = c - a`
(`rad` is the radical, the product of the primes dividing its argument). The quality is undefined at
`j = 0` and `j = 1728`: there `a*b*c = 0`, so `rad = 1`, `log 1 = 0`, and the value is the junk `0`
(Lean's `x / 0 = 0`). Needs `[E.IsElliptic]` for the `j`-invariant. -/
noncomputable def abcQuality (E : WeierstrassCurve ℚ) [E.IsElliptic] : ℝ :=
  let a := (E.j / 1728).num
  let c := ((E.j / 1728).den : ℤ)
  let b := c - a
  Real.log ↑(max (max a.natAbs b.natAbs) c.natAbs) /
    Real.log ↑(UniqueFactorizationMonoid.radical (a * b * c).natAbs)

end Quality

section Points

/-- The **integral points** (LMFDB `ec.q.integral_points`) of a given model `W` of an elliptic curve
over `ℚ`: the affine points `(x, y)` of `W` with integral coordinates `x, y ∈ ℤ`. (The point at
infinity is excluded, having no affine coordinates.) The knowl's "integral points on a minimal model"
is then `integralPoints` of the global minimal model; the set is finite by Siegel's theorem, which is
not part of this definition. -/
def integralPoints (W : WeierstrassCurve ℚ) : Set W.toAffine.Point :=
  {P | ∃ (x y : ℤ) (h : W.toAffine.Nonsingular (x : ℚ) (y : ℚ)), P = Affine.Point.some h}

end Points

end WeierstrassCurve
