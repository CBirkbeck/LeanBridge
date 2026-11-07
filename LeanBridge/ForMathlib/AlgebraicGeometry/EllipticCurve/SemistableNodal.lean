import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.NodeCusp
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.PotentialGoodReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Semistable

/-!
# Semistable elliptic curves, nodal reduction and potential good reduction

Let `O` be a Dedekind domain with fraction field `F`, such as the ring of integers of a number field
or `ℤ`, and let `W` be an elliptic curve over `F`. Tau Ceti's `WeierstrassCurve.IsSemistable` says
that at no height-one prime `v` of `O` does a minimal equation over the local ring `Oᵥ` have
additive reduction. The LMFDB calls an elliptic curve semistable if it has multiplicative reduction
at every bad prime (`WeierstrassCurve.isSemistable_iff_forall_hasMultiplicativeReduction`), and
defines multiplicative reduction as a nodal singularity of the reduction, which is
`WeierstrassCurve.hasMultiplicativeReduction_iff_hasNode`: so a curve is semistable exactly when
its reduction at every bad prime has a node (`WeierstrassCurve.isSemistable_iff_forall_hasNode`).

The knowl `ec.reduction` also says that `W` has potential good reduction if its `j`-invariant is
integral, and that such a curve cannot be semistable unless it has good reduction everywhere. Here
the integrality of `j` is proved equivalent to Tau Ceti's local potential good reduction
(`WeierstrassCurve.HasPotentialGoodReduction`, good reduction after a finite extension that may
depend on the prime) at every height-one prime
(`WeierstrassCurve.forall_hasPotentialGoodReduction_iff_isInteger_j`), and a semistable curve with
integral `j`-invariant has good reduction everywhere
(`WeierstrassCurve.IsSemistable.hasGoodReduction_of_isInteger_j`): at a prime of bad reduction a
semistable curve has multiplicative reduction, where `j` has a pole. The potential good reduction
of LMFDB `ec.potential_good_reduction`, everywhere good reduction over one finite extension of `F`,
is not formalised, and neither is its equivalence with the integrality of `j`.

## Main results

* `WeierstrassCurve.isSemistable_iff_forall_hasMultiplicativeReduction` (LMFDB `ec.semistable`,
  `ec.q.semistable`, `ec.reduction`): semistability is multiplicative reduction at every bad prime.
* `WeierstrassCurve.isSemistable_iff_forall_hasNode`: semistability is a node in the reduction at
  every bad prime.
* `WeierstrassCurve.forall_hasPotentialGoodReduction_iff_isInteger_j`: an elliptic curve has
  potential good reduction at every prime, with an extension depending on the prime, exactly when
  its `j`-invariant is integral.
* `WeierstrassCurve.IsSemistable.hasGoodReduction_of_isInteger_j`: a semistable elliptic curve with
  integral `j`-invariant has good reduction everywhere.
-/

open IsDedekindDomain

namespace WeierstrassCurve

section Semistable

variable {O : Type*} [CommRing O] [IsDedekindDomain O] {F : Type*} [Field F] [Algebra O F]
  [IsFractionRing O F] (W : WeierstrassCurve F) [W.IsElliptic]

/-- **An elliptic curve is semistable exactly when it has multiplicative reduction at every bad
prime** (LMFDB `ec.semistable`, `ec.q.semistable`): at every height-one prime `v` at which a
minimal equation over `Oᵥ` has bad reduction, it has multiplicative reduction. -/
lemma isSemistable_iff_forall_hasMultiplicativeReduction : W.IsSemistable O ↔
    ∀ v : HeightOneSpectrum O, (W.minimal (Localization.AtPrime v.asIdeal)).IsBadReduction
      (Localization.AtPrime v.asIdeal) →
        (W.minimal (Localization.AtPrime v.asIdeal)).HasMultiplicativeReduction
          (Localization.AtPrime v.asIdeal) := by
  rw [isSemistable_iff_forall_hasGoodReduction_or_hasMultiplicativeReduction]
  exact forall_congr' fun v ↦ or_iff_not_imp_left

/-- **An elliptic curve is semistable exactly when its reduction at every bad prime has a node**
(LMFDB `ec.semistable`, `ec.q.semistable`, `ec.reduction_type`). -/
lemma isSemistable_iff_forall_hasNode : W.IsSemistable O ↔
    ∀ v : HeightOneSpectrum O, (W.minimal (Localization.AtPrime v.asIdeal)).IsBadReduction
      (Localization.AtPrime v.asIdeal) →
        ((W.minimal (Localization.AtPrime v.asIdeal)).reduction
          (Localization.AtPrime v.asIdeal)).HasNode := by
  rw [isSemistable_iff_forall_hasMultiplicativeReduction]
  exact forall_congr' fun v ↦ imp_congr_right fun _ ↦ hasMultiplicativeReduction_iff_hasNode _

end Semistable

section PotentialGoodReduction

universe u

variable {O : Type u} [CommRing O] [IsDedekindDomain O] {F : Type u} [Field F] [Algebra O F]
  [IsFractionRing O F] (W : WeierstrassCurve F) [W.IsElliptic]

/-- **An elliptic curve has potential good reduction at every prime exactly when its `j`-invariant
is integral**, by Tau Ceti's local criterion
`WeierstrassCurve.hasPotentialGoodReduction_iff_isInteger_j` at each height-one prime. The finite
extension may depend on the prime: this is not the global potential good reduction of LMFDB
`ec.potential_good_reduction`. -/
lemma forall_hasPotentialGoodReduction_iff_isInteger_j :
    (∀ v : HeightOneSpectrum O, W.HasPotentialGoodReduction (Localization.AtPrime v.asIdeal)) ↔
      IsLocalization.IsInteger O W.j := by
  refine ⟨fun h ↦ HeightOneSpectrum.isInteger_of_forall_isInteger_localizationAtPrime _ fun v ↦
    (hasPotentialGoodReduction_iff_isInteger_j _).mp (h v), fun ⟨r, hr⟩ v ↦
      (hasPotentialGoodReduction_iff_isInteger_j _).mpr ⟨algebraMap O _ r, ?_⟩⟩
  rw [← hr, ← IsScalarTower.algebraMap_apply]

/-- **A semistable elliptic curve with integral `j`-invariant has good reduction everywhere**
(LMFDB `ec.reduction`, with potential good reduction read as the integrality of `j`): it cannot be
semistable unless it has good reduction at every prime. -/
lemma IsSemistable.hasGoodReduction_of_isInteger_j (h : W.IsSemistable O)
    (hj : IsLocalization.IsInteger O W.j) (v : HeightOneSpectrum O) :
    (W.minimal (Localization.AtPrime v.asIdeal)).HasGoodReduction
      (Localization.AtPrime v.asIdeal) := by
  rcases (isSemistable_iff_forall_hasGoodReduction_or_hasMultiplicativeReduction W).mp h v with
    hg | hm
  · exact hg
  exfalso
  rcases W.exists_smul_eq_minimal (Localization.AtPrime v.asIdeal) with ⟨C, hC⟩
  have : (W.minimal (Localization.AtPrime v.asIdeal)).IsElliptic := hC ▸ inferInstance
  refine hm.not_hasPotentialGoodReduction _ ?_
  rw [← hC, hasPotentialGoodReduction_smul]
  exact (forall_hasPotentialGoodReduction_iff_isInteger_j W).mpr hj v

end PotentialGoodReduction

end WeierstrassCurve
