import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import TauCeti.AlgebraicGeometry.Birational.RationalMap
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
import TauCeti.FieldTheory.FunctionField.Differential.CanonicalDivisor

/-!
# The canonical map and the canonical model of a curve

Let `X` be a regular proper curve over a field `k`, such as a smooth projective geometrically
integral curve, with function field `F = k(X)`, of which `k` is the exact constant field, and genus
`g`. For a divisor `D` of `F / k` with nonzero Riemann–Roch space `L(D) ⊆ F`, the complete linear
system `|D|` defines a `k`-morphism `X → ℙ(L(D))` to `ℙ(L(D)) = Proj (Sym_k L(D))`, the projective
space of hyperplanes of `L(D)`, `ℙ^{n - 1}` for `n = ℓ(D)`: in a basis `f_1, …, f_n` of `L(D)` it
is `P ↦ [f_1(P) : ⋯ : f_n(P)]`. It is the unique `k`-morphism whose generic point has homogeneous
coordinates the inclusion `L(D) ⊆ F`, the `F`-point `[f_1 : ⋯ : f_n]`, which on the chart
`D₊(s)` of any nonzero `s ∈ L(D)` has affine coordinates the `f_i / s`; it exists because the local
rings of `X` are valuation rings and `ℙ(L(D))` is proper (Tau Ceti's
`AlgebraicGeometry.Scheme.homOfFunctionField`).

The canonical map is the morphism of the complete linear system of a canonical divisor `K`, a
divisor in Tau Ceti's canonical class, here the divisor of a chosen nonzero Weil differential.
Since `ℓ(K) = g`, it is a morphism `X → ℙ^{g - 1}`, defined for `g ≥ 1`; another canonical divisor
`K + div h` gives the same map up to the isomorphism `L(K + div h) ≅ L(K)`, `f ↦ h f`. The canonical
model is its image, the scheme-theoretic image `Scheme.Hom.image`, a closed subscheme of
`ℙ^{g - 1}`. The LMFDB uses this name for non-hyperelliptic curves of genus `g ≥ 2`, for which the
canonical map is a closed immersion onto a projectively normal curve (Noether's theorem); this is
not proved here.

The local rings of a smooth curve at its points of codimension one are regular of dimension one,
hence discrete valuation rings, so the definitions apply to LeanBridge's smooth proper algebraic
curves (`AlgebraicGeometry.Scheme.IsAlgebraicCurveOver`). That `k` is the exact constant field is a
hypothesis, which Tau Ceti's
`TauCeti.AlgebraicGeometry.isIntegrallyClosedIn_functionField_of_geometricallyIntegral` supplies
for geometrically integral curves, such as these; only `g ≥ 1` then remains to be assumed.

## Main definitions

* `TauCeti.canonicalDivisor`: a canonical divisor of an algebraic function field.
* `AlgebraicGeometry.Scheme.genericLinearSystemPoint`: the `F`-point of `ℙ(L(D))` with homogeneous
  coordinates the inclusion `L(D) ⊆ F`.
* `AlgebraicGeometry.Scheme.linearSystemMap`: the morphism `X → ℙ(L(D))` of the complete linear
  system `|D|`.
* `AlgebraicGeometry.Scheme.canonicalMap` (LMFDB `ag.canonical_model`): the canonical map
  `X → ℙ^{g - 1}`.
* `AlgebraicGeometry.Scheme.canonicalModel` (LMFDB `ag.canonical_model`): the canonical model.

## Main results

* `TauCeti.divisorClass_canonicalDivisor`: a canonical divisor represents the canonical class.
* `TauCeti.finrank_riemannRochSpace_canonicalDivisor`: `ℓ(K) = g`, so the canonical map goes to
  `ℙ^{g - 1}`.
* `AlgebraicGeometry.Scheme.fromSpecStalk_linearSystemMap`: the generic point of `X` is sent to the
  point with homogeneous coordinates `L(D) ⊆ F`, read on the chart of any nonzero `s ∈ L(D)`.
* `AlgebraicGeometry.Scheme.eq_linearSystemMap_iff`: the morphism of `|D|` is the only
  `k`-morphism doing so.
-/

open CategoryTheory TauCeti AlgebraicGeometry HomogeneousLocalization SetLike

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (hF : IsFunctionField k F)
  (hex : IsIntegrallyClosedIn k F)

/-- A **canonical divisor** of an algebraic function field `F / k` with exact constant field: the
divisor of a chosen nonzero Weil differential, a divisor in the canonical class
`TauCeti.canonicalClass` (`divisorClass_canonicalDivisor`). -/
noncomputable def canonicalDivisor : Divisor k F :=
  haveI h : ∃ ω ∈ weilDifferentialSpace k F, ω ≠ 0 :=
    (Submodule.ne_bot_iff _).mp (weilDifferentialSpace_ne_bot hF hex)
  weilDifferentialDivisor hF hex h.choose_spec.1 h.choose_spec.2

/-- **A canonical divisor represents the canonical class.** -/
lemma divisorClass_canonicalDivisor :
    (Place.orderSystem hF).divisorClass (canonicalDivisor hF hex) = canonicalClass hF hex :=
  rfl

/-- **The Riemann–Roch space of a canonical divisor has dimension the genus**, `ℓ(K) = g`. -/
lemma finrank_riemannRochSpace_canonicalDivisor :
    Module.finrank k (riemannRochSpace (canonicalDivisor hF hex)) = genus k F :=
  dim_weilDifferentialDivisor hF hex _ _

lemma riemannRochSpace_canonicalDivisor_ne_bot (hg : genus k F ≠ 0) :
    riemannRochSpace (canonicalDivisor hF hex) ≠ ⊥ :=
  fun h ↦ hg <| by rw [← finrank_riemannRochSpace_canonicalDivisor hF hex, h, finrank_bot]

end TauCeti

namespace AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

variable [X.IsAlgebraicCurveOver k] [Smooth (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] in
instance (y : CodimensionOnePoint X) : IsDiscreteValuationRing (X.presheaf.stalk (y : X)) :=
  have : IsRegularLocalRing (X.presheaf.stalk (y : X)) :=
    isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k)) y
  inferInstance

variable [X.IsCurveOver k] (D : Divisor k X.functionField) {s t : X.functionField}
  (hs : s ∈ riemannRochSpace D) (hs0 : s ≠ 0)

instance : FiniteDimensional k (riemannRochSpace D) :=
  finiteDimensional_riemannRochSpace IsCurveOver.isFunctionField D

/-- The `k`-algebra map `Sym_k L(D) → F` extending the inclusion of the Riemann–Roch space
`L(D) ⊆ F` of a divisor `D` of the function field `F` of a curve: the homogeneous coordinates of the
generic point of the morphism of the complete linear system `|D|`. -/
noncomputable def linearSystemCoordinates :
    SymmetricAlgebra k (riemannRochSpace D) →ₐ[k] X.functionField :=
  SymmetricAlgebra.lift (riemannRochSpace D).subtype

lemma isUnit_linearSystemCoordinates_iff :
    IsUnit ((linearSystemCoordinates D).toRingHom (SymmetricAlgebra.ι k _ ⟨s, hs⟩)) ↔ s ≠ 0 := by
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, linearSystemCoordinates,
    SymmetricAlgebra.lift_ι_apply]
  exact isUnit_iff_ne_zero

/-- The `F`-point of `ℙ(L(D)) = Proj (Sym_k L(D))` with homogeneous coordinates the inclusion
`L(D) ⊆ F`, for `D` a divisor of the function field `F` of a curve: the point `[f_1 : ⋯ : f_n]` for
a basis `f_1, …, f_n` of `L(D)`, read on the chart `D₊(s)` of a nonzero `s ∈ L(D)`, where it has
affine coordinates the `f_i / s`. It does not depend on `s` (`genericLinearSystemPoint_eq`). -/
noncomputable def genericLinearSystemPoint :
    Spec X.functionField ⟶ Proj (SymmetricAlgebra.homogeneousSubmodule k (riemannRochSpace D)) :=
  Spec.map (CommRingCat.ofHom (Away.lift (SymmetricAlgebra.homogeneousSubmodule k _)
    (linearSystemCoordinates D).toRingHom ((isUnit_linearSystemCoordinates_iff D hs).mpr hs0))) ≫
    Proj.awayι (SymmetricAlgebra.homogeneousSubmodule k _) _
      (SymmetricAlgebra.ι_mem_homogeneousSubmodule k (riemannRochSpace D) ⟨s, hs⟩) one_pos

lemma genericLinearSystemPoint_comp_over : genericLinearSystemPoint D hs hs0 ≫
    Proj (SymmetricAlgebra.homogeneousSubmodule k (riemannRochSpace D)) ↘ Spec (.of k) =
    X.fromSpecStalk _ ≫ X ↘ Spec (.of k) := by
  have h : CommRingCat.ofHom ((fromZeroRingHom (SymmetricAlgebra.homogeneousSubmodule k _)
      (Submonoid.powers (SymmetricAlgebra.ι k (riemannRochSpace D) ⟨s, hs⟩))).comp
        (algebraMap k (SymmetricAlgebra.homogeneousSubmodule k (riemannRochSpace D) 0))) ≫
      CommRingCat.ofHom (Away.lift (SymmetricAlgebra.homogeneousSubmodule k _)
        (linearSystemCoordinates D).toRingHom ((isUnit_linearSystemCoordinates_iff D hs).mpr hs0)) =
      CommRingCat.ofHom (algebraMap k X.functionField) := by
    ext c
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, RingHom.comp_apply,
      RingHom.comp_apply, ← algebraMap_eq, Away.lift_algebraMap, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, GradeZero.coe_algebraMap, AlgHom.commutes, CommRingCat.hom_ofHom]
  rw [genericLinearSystemPoint, Category.assoc, SymmetricAlgebra.over_eq_projToSpec,
    SymmetricAlgebra.awayι_projToSpec, fromSpecStalk_genericPoint_comp_over, ← h, Spec.map_comp]
  rfl

lemma genericLinearSystemPoint_eq (ht : t ∈ riemannRochSpace D) (ht0 : t ≠ 0) :
    genericLinearSystemPoint D hs hs0 = genericLinearSystemPoint D ht ht0 :=
  Proj.SpecMap_awayLift_awayι_eq _ _ one_pos _ one_pos _ _

variable [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  (hD : riemannRochSpace D ≠ ⊥)

/-- The **morphism of the complete linear system** `|D|` of a divisor `D` with nonzero Riemann–Roch
space `L(D)` of the function field `F` of a regular proper curve `X` over `k`: the `k`-morphism
`X → ℙ(L(D)) = Proj (Sym_k L(D))`, `P ↦ [f_1(P) : ⋯ : f_n(P)]` for a basis `f_1, …, f_n` of `L(D)`,
extending the point `genericLinearSystemPoint` of the generic point
(`fromSpecStalk_linearSystemMap`, `eq_linearSystemMap_iff`), which exists because the local rings of
`X` are valuation rings. -/
noncomputable def linearSystemMap :
    X ⟶ Proj (SymmetricAlgebra.homogeneousSubmodule k (riemannRochSpace D)) :=
  haveI h : ∃ x ∈ riemannRochSpace D, x ≠ 0 := (Submodule.ne_bot_iff _).mp hD
  homOfFunctionField (IsCurveOver.valuationRing_stalk k X)
    (genericLinearSystemPoint D h.choose_spec.1 h.choose_spec.2)
    (genericLinearSystemPoint_comp_over D _ _)

/-- **The morphism of `|D|` sends the generic point to the point with homogeneous coordinates the
inclusion `L(D) ⊆ F`**, read on the chart of any nonzero `s ∈ L(D)`. -/
lemma fromSpecStalk_linearSystemMap :
    X.fromSpecStalk (genericPoint X) ≫ linearSystemMap D hD = genericLinearSystemPoint D hs hs0 :=
  (fromSpecStalk_homOfFunctionField _ _ _).trans (genericLinearSystemPoint_eq D _ _ hs hs0)

instance : (linearSystemMap D hD).IsOver (Spec (.of k)) :=
  isOver_homOfFunctionField _ _ _

variable {D} in
/-- **The morphism of `|D|` is the only `k`-morphism `X → ℙ(L(D))` sending the generic point to the
point with homogeneous coordinates the inclusion `L(D) ⊆ F`.** -/
lemma eq_linearSystemMap_iff
    (f : X ⟶ Proj (SymmetricAlgebra.homogeneousSubmodule k (riemannRochSpace D)))
    [f.IsOver (Spec (.of k))] : f = linearSystemMap D hD ↔ X.fromSpecStalk (genericPoint X) ≫ f =
    genericLinearSystemPoint D hs hs0 :=
  (eq_homOfFunctionField_iff _ _ _ f).trans <| Eq.congr_right <|
    genericLinearSystemPoint_eq D _ _ hs hs0

variable (hex : IsIntegrallyClosedIn k X.functionField) (hg : genus k X.functionField ≠ 0)

/-- The **canonical map** (LMFDB `ag.canonical_model`) of a regular proper curve `X` over `k`, such
as a smooth projective curve, whose function field `F` has exact constant field `k` and genus
`g ≥ 1`: the morphism `X → ℙ^{g - 1}` defined by the canonical class, that is the morphism
`linearSystemMap` of the complete linear system of the canonical divisor `K` of
`TauCeti.canonicalDivisor`, to `Proj (Sym_k L(K))` with `ℓ(K) = g`
(`TauCeti.finrank_riemannRochSpace_canonicalDivisor`). In a basis `f_1, …, f_g` of `L(K)`, whose
elements correspond to the regular differentials `f_i ω` for the differential `ω` of divisor `K`,
it is `P ↦ [f_1(P) : ⋯ : f_g(P)]`. -/
noncomputable def canonicalMap : X ⟶ Proj (SymmetricAlgebra.homogeneousSubmodule k
    (riemannRochSpace (canonicalDivisor IsCurveOver.isFunctionField hex))) :=
  linearSystemMap _ (riemannRochSpace_canonicalDivisor_ne_bot _ hex hg)

/-- The **canonical model** (LMFDB `ag.canonical_model`) of a regular proper curve `X` over `k`,
such as a smooth projective curve, whose function field has exact constant field `k` and genus
`g ≥ 1`: the image of its canonical map `X → ℙ^{g - 1}`, the scheme-theoretic image
`Scheme.Hom.image`, a closed subscheme of `ℙ^{g - 1}` by `Scheme.Hom.imageι`. The LMFDB uses this
name when `X` is not hyperelliptic and `g ≥ 2`, the canonical map being then a closed immersion
onto a projectively normal curve (not proved here). -/
noncomputable abbrev canonicalModel : Scheme.{u} :=
  (canonicalMap hex hg).image

end AlgebraicGeometry.Scheme
