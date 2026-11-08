import Mathlib.NumberTheory.NumberField.Basic
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.SemistableNodal
import TauCeti.AlgebraicGeometry.EllipticCurve.CurveX3SubX
import TauCeti.AlgebraicGeometry.EllipticCurve.DeuringNormalForm
import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre

/-!
# Potential good reduction of an elliptic curve over a number field

An elliptic curve `E` over a number field `K` has **everywhere good reduction** if it has good
reduction at every prime of `K`, that is, a minimal equation of `E` over the local ring at every
height-one prime of `𝓞 K` has good reduction. It has **potential good reduction** (LMFDB
`ec.potential_good_reduction`) if it acquires everywhere good reduction over a finite extension of
`K`. This is the global notion of the LMFDB: one extension `L / K` serves every prime of `L`. Tau
Ceti's `WeierstrassCurve.HasPotentialGoodReduction` is the local notion at one discrete valuation
ring, where the extension may depend on the prime.

The knowl states that potential good reduction is equivalent to the integrality of the
`j`-invariant, that is, `j ∈ 𝓞 K`
(`WeierstrassCurve.hasPotentialEverywhereGoodReduction_iff_isInteger_j`). The necessary direction
reads off `j = c₄³ / Δ` at every prime of `L`, where a minimal equation has unit discriminant, so
`j ∈ 𝓞 L`, and then `j ∈ 𝓞 K`. For the sufficient direction one extension is built for all
primes at once, gluing the two local constructions of Tau Ceti over a tower: over a finite
extension `L₁ / K` the curve takes the Legendre form `y² = x (x - 1) (x + B)`
(`WeierstrassCurve.exists_variableChange_smul_baseChange_eq_freyCurve_one`), and over a finite
extension `L / L₁` it also takes the Deuring normal form `y² + a x y + y = x³`
(`WeierstrassCurve.exists_variableChange_smul_baseChange_eq_deuringNormalForm`). With integral
`j`, the Legendre form has good reduction at every prime of `L` not above `2`
(`WeierstrassCurve.hasGoodReduction_freyCurve_one`) and the Deuring form at every prime not above
`3` (`WeierstrassCurve.hasGoodReduction_deuringNormalForm`), and no prime lies above both.

The knowl `ec.reduction` adds that a curve with potential good reduction cannot be semistable
unless it has everywhere good reduction
(`WeierstrassCurve.IsSemistable.hasEverywhereGoodReduction`), because at a prime of
multiplicative reduction the `j`-invariant has a pole.

## Main definitions

* `WeierstrassCurve.HasEverywhereGoodReduction` (LMFDB `ec.good_reduction`): good reduction at
  every height-one prime of a Dedekind domain.
* `WeierstrassCurve.HasPotentialEverywhereGoodReduction` (LMFDB `ec.potential_good_reduction`,
  `ec.reduction`): everywhere good reduction over a finite extension.

## Main results

* `WeierstrassCurve.HasPotentialEverywhereGoodReduction.isInteger_j`: potential good reduction
  makes the `j`-invariant integral.
* `WeierstrassCurve.hasPotentialEverywhereGoodReduction_of_isInteger_j`: an integral
  `j`-invariant gives potential good reduction.
* `WeierstrassCurve.hasPotentialEverywhereGoodReduction_iff_isInteger_j` (LMFDB
  `ec.potential_good_reduction`, `ec.reduction`): the two are equivalent.
* `WeierstrassCurve.IsSemistable.hasEverywhereGoodReduction` (LMFDB `ec.reduction`): a semistable
  curve with potential good reduction has everywhere good reduction.
* `WeierstrassCurve.hasPotentialEverywhereGoodReduction_x_cube_sub_x`: `y² = x³ - x` over `ℚ`,
  with `j = 1728`, has potential good reduction.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.4 and VII.5.5.
-/

open IsDedekindDomain NumberField TauCeti

namespace WeierstrassCurve

universe u

/-- A Weierstrass curve `W` over the fraction field `F` of a Dedekind domain `O` has **everywhere
good reduction** (LMFDB `ec.good_reduction`) if it has good reduction at every height-one prime
`v` of `O`: a minimal equation of `W` over the localisation `Oᵥ` has good reduction. For a number
field `F` and `O = 𝓞 F` these are the primes of `F`. -/
def HasEverywhereGoodReduction (O : Type*) [CommRing O] [IsDedekindDomain O] {F : Type*} [Field F]
    [Algebra O F] [IsFractionRing O F] (W : WeierstrassCurve F) : Prop :=
  ∀ v : HeightOneSpectrum O, (W.minimal (Localization.AtPrime v.asIdeal)).HasGoodReduction
    (Localization.AtPrime v.asIdeal)

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

variable {W} [W.IsElliptic] in
lemma j_eq_algebraMap_of_smul_baseChange_eq {L : Type*} [Field L] [Algebra K L]
    {W' : WeierstrassCurve L} [W'.IsElliptic] {C : VariableChange L}
    (hC : C • W.baseChange L = W') : W'.j = algebraMap K L W.j := by
  subst hC
  rw [variableChange_j]
  exact map_j W (algebraMap K L)

variable [NumberField K]

/-- An elliptic curve `W` over a number field `K` has **potential good reduction** (LMFDB
`ec.potential_good_reduction`, `ec.reduction`) if it has everywhere good reduction over a finite
extension `L` of `K`, which is then a number field: at every prime of `L` a minimal equation of
`W` over the local ring has good reduction. One extension serves every prime of `L`, unlike Tau
Ceti's local `WeierstrassCurve.HasPotentialGoodReduction`. -/
def HasPotentialEverywhereGoodReduction : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
    haveI : NumberField L := .of_module_finite K L
    (W.baseChange L).HasEverywhereGoodReduction (𝓞 L)

variable {W} [W.IsElliptic]

/-- **Potential good reduction makes the `j`-invariant integral**, that is, an element of the ring
of integers `𝓞 K`: over the extension `L`, at every prime a minimal equation has unit discriminant,
so `j = c₄³ / Δ` lies in every local ring of `𝓞 L`, hence in `𝓞 L`, and `j ∈ K` is then integral
over `ℤ`. -/
lemma HasPotentialEverywhereGoodReduction.isInteger_j (h : W.HasPotentialEverywhereGoodReduction) :
    IsLocalization.IsInteger (𝓞 K) W.j := by
  rcases h with ⟨L, _, _, _, hL⟩
  have : NumberField L := .of_module_finite K L
  have hj (v : HeightOneSpectrum (𝓞 L)) :
      IsLocalization.IsInteger (Localization.AtPrime v.asIdeal) (algebraMap K L W.j) := by
    rcases (W.baseChange L).exists_smul_eq_minimal (Localization.AtPrime v.asIdeal) with ⟨C, hC⟩
    have : ((W.baseChange L).minimal (Localization.AtPrime v.asIdeal)).IsElliptic :=
      hC ▸ inferInstance
    exact j_eq_algebraMap_of_smul_baseChange_eq hC ▸ (hL v).isInteger_j _
  rcases HeightOneSpectrum.isInteger_of_forall_isInteger_localizationAtPrime _ hj with ⟨r, hr⟩
  exact ⟨⟨W.j, isIntegral_algebraMap_iff.mp (hr ▸ r.isIntegral_coe)⟩, rfl⟩

lemma hasGoodReduction_minimal_of_smul {L : Type*} [Field L] {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra R L] [IsFractionRing R L] {V : WeierstrassCurve L}
    (C : VariableChange L) (h : (C • V).HasGoodReduction R) : (V.minimal R).HasGoodReduction R :=
  (hasGoodReduction_minimal_smul_iff R C V).mp (h.hasGoodReduction_minimal R)

/-- **An integral `j`-invariant gives potential good reduction**: one finite extension `L` of `K`
serves every prime. Over a finite extension `L₁ / K` the curve takes the Legendre form
`y² = x (x - 1) (x + B)`, and over a finite extension `L / L₁` the Deuring normal form
`y² + a x y + y = x³`. At a prime of `L` not above `2` the Legendre form has good reduction, and at
a prime not above `3` the Deuring form, since `j` stays integral there. -/
lemma hasPotentialEverywhereGoodReduction_of_isInteger_j (hj : IsLocalization.IsInteger (𝓞 K) W.j) :
    W.HasPotentialEverywhereGoodReduction := by
  rcases W.exists_variableChange_smul_baseChange_eq_freyCurve_one two_ne_zero with
    ⟨L₁, _, _, _, -, C₁, B, hB⟩
  have : CharZero L₁ := charZero_of_injective_algebraMap (algebraMap K L₁).injective
  rcases (W.baseChange L₁).exists_variableChange_smul_baseChange_eq_deuringNormalForm
    three_ne_zero with ⟨L, _, _, _, -, C₂, a, ha⟩
  let _ : Algebra K L := ((algebraMap L₁ L).comp (algebraMap K L₁)).toAlgebra
  have : IsScalarTower K L₁ L := .of_algebraMap_eq' rfl
  have : FiniteDimensional K L := Module.Finite.trans L₁ L
  have : NumberField L := .of_module_finite K L
  have hL : (W.baseChange L₁).map (algebraMap L₁ L) = W.baseChange L := rfl
  have hB' : C₁.map (algebraMap L₁ L) • W.baseChange L = freyCurve 1 (algebraMap L₁ L B) := by
    rw [← hL, map_variableChange, hB, map_freyCurve, map_one]
  have ha' : C₂ • W.baseChange L = deuringNormalForm a := ha
  refine ⟨L, inferInstance, inferInstance, inferInstance, fun v ↦ ?_⟩
  have hjv : IsLocalization.IsInteger (Localization.AtPrime v.asIdeal) (algebraMap K L W.j) := by
    rcases hj with ⟨r, hr⟩
    refine ⟨algebraMap (𝓞 L) _ (⟨algebraMap K L W.j,
      (mem_integralClosure_iff ℤ L).mpr (hr ▸ r.isIntegral_coe.algebraMap)⟩ : 𝓞 L), ?_⟩
    exact (IsScalarTower.algebraMap_apply (𝓞 L) (Localization.AtPrime v.asIdeal) L _).symm
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (3 : Localization.AtPrime v.asIdeal) with
    h3 | h2
  · have : (deuringNormalForm a).IsElliptic := ha' ▸ inferInstance
    refine hasGoodReduction_minimal_of_smul C₂ ?_
    rw [ha']
    exact hasGoodReduction_deuringNormalForm _ h3 <| j_eq_algebraMap_of_smul_baseChange_eq ha' ▸ hjv
  · rw [show (1 : Localization.AtPrime v.asIdeal) - 3 = -2 by norm_num, IsUnit.neg_iff] at h2
    have : (freyCurve 1 (algebraMap L₁ L B)).IsElliptic := hB' ▸ inferInstance
    refine hasGoodReduction_minimal_of_smul (C₁.map (algebraMap L₁ L)) ?_
    rw [hB']
    exact hasGoodReduction_freyCurve_one _ h2 <| j_eq_algebraMap_of_smul_baseChange_eq hB' ▸ hjv

/-- **Potential good reduction is the integrality of the `j`-invariant** (LMFDB
`ec.potential_good_reduction`, `ec.reduction`; Silverman VII.5.5 at every prime at once): an
elliptic curve over a number field has everywhere good reduction over a finite extension exactly
when its `j`-invariant is integral, that is, lies in the ring of integers `𝓞 K`, the integral
closure of `ℤ` in `K`. -/
lemma hasPotentialEverywhereGoodReduction_iff_isInteger_j :
    W.HasPotentialEverywhereGoodReduction ↔ IsLocalization.IsInteger (𝓞 K) W.j :=
  ⟨(·.isInteger_j), hasPotentialEverywhereGoodReduction_of_isInteger_j⟩

/-- **A semistable curve with potential good reduction has everywhere good reduction** (LMFDB
`ec.reduction`): its `j`-invariant is integral, while at a prime of multiplicative reduction it has
a pole. -/
lemma IsSemistable.hasEverywhereGoodReduction (h : W.IsSemistable (𝓞 K))
    (hW : W.HasPotentialEverywhereGoodReduction) : W.HasEverywhereGoodReduction (𝓞 K) :=
  h.hasGoodReduction_of_isInteger_j W hW.isInteger_j

/-- **The curve `y² = x³ - x` over `ℚ` has potential good reduction**, its `j`-invariant being
`1728`, although its discriminant is `64`. -/
lemma hasPotentialEverywhereGoodReduction_x_cube_sub_x :
    (CurveX3SubX.curve ℚ).HasPotentialEverywhereGoodReduction := by
  refine hasPotentialEverywhereGoodReduction_of_isInteger_j ⟨1728, ?_⟩
  rw [map_ofNat, eq_comm, j_eq_1728_iff]
  simp [c₆, b₂, b₆]

end WeierstrassCurve
