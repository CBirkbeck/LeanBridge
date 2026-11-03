import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.NodalReduction
import LeanBridge.ForMathlib.AlgebraicGeometry.Scheme.PointClosure
import TauCeti.AlgebraicGeometry.Normalization.Basic
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus

/-!
# Semistable reduction of curves

A curve `C` over a local field `K` has semistable reduction (LMFDB `g2c.semistable_reduction`) if it
has a model over the ring of integers `𝒪_K` whose special fibre is semistable: a geometrically
reduced curve with at most nodal singularities, each of whose components of geometric genus zero has
at least two singular points, counted with multiplicity.

The components, their genera and the count are read on the geometric special fibre `X`, the base
change of the model to an algebraic closure `F` of the residue field. An irreducible component `Z`
of `X`, with generic point `η`, has function field the residue field `κ(η)`:

* the normalisation of `Z` is the relative normalisation of `X` in `Spec κ(η)`, an integral scheme
  mapping onto `Z`;
* the geometric genus of `Z` is the genus of its function field over `F`, which is an algebraic
  function field of one variable as soon as `X` is syntomic of relative dimension one over `F`, so
  that this genus is not a junk value;
* the singular points of `X` are the points of the support of the relative singular locus
  `Fitt₁(Ω_{X/F})`, and the singular points of `Z`, counted with multiplicity, are the points of the
  normalisation of `Z` above them, so that a node at which both branches of `X` lie on `Z` counts
  twice.

The knowl states its condition on the special fibre alone, and this is how it is formalised here.
A model whose structure morphism is nodal, Tau Ceti's `AffineAtWorstNodalOfRelativeDimensionOne`,
has a nodal geometric special fibre. The comparison with the elliptic curve case (LMFDB
`ec.semistable`), for which the knowl says that this is the equivalent notion, is not proved.

The knowl's condition excludes the projective line with its smooth model, since a smooth curve has
no singular points. So it is meant for curves of positive genus, as the curves of genus two of the
knowl's section, for which it differs from `AlgebraicGeometry.Scheme.HasNodalReduction` by the
contraction of rational tails. This is also the convention of the Stacks Project (Definition
109.21.2, Tag 0E6X), where a prestable family of curves of genus zero is never semistable.

## Main definitions

* `AlgebraicGeometry.Scheme.componentGenericPoint`: the generic point of an irreducible component.
* `AlgebraicGeometry.Scheme.componentNormalization`: the normalisation of an irreducible component.
* `AlgebraicGeometry.Scheme.componentGenus`: the geometric genus of an irreducible component.
* `AlgebraicGeometry.Scheme.singularPoints`: the singular points of a curve over a field.
* `AlgebraicGeometry.Scheme.componentSingularPointCount`: the number of singular points of an
  irreducible component, counted with multiplicity.
* `AlgebraicGeometry.Scheme.IsSemistableOver`: a semistable curve over a field.
* `TauCeti.Model.geometricSpecialFiber`: the geometric special fibre of a model.
* `AlgebraicGeometry.Scheme.HasSemistableReduction` (LMFDB `g2c.semistable_reduction`).

## Main results

* `AlgebraicGeometry.Scheme.range_componentNormalizationι`: the normalisation of a component maps
  onto it.
* `AlgebraicGeometry.Scheme.nonempty_algEquiv_functionField_componentNormalization`: the function
  field of the normalisation of a component is the residue field at its generic point.
* `AlgebraicGeometry.Scheme.isFunctionField_component`: the function field of a component of a
  curve is an algebraic function field of one variable.
* `AlgebraicGeometry.Scheme.isSemistableOver_iff_of_smooth`: a smooth curve is semistable exactly
  when none of its components has genus zero.
* `TauCeti.Model.atWorstNodal_geometricSpecialFiber`: the geometric special fibre of a nodal model
  is nodal.
* `AlgebraicGeometry.Scheme.HasSemistableReduction.of_nodal`: a nodal model satisfying the condition
  on the components of genus zero gives semistable reduction.
* `AlgebraicGeometry.Scheme.HasSemistableReduction.of_smooth`: good reduction with no component of
  genus zero gives semistable reduction.
-/

open CategoryTheory TauCeti AlgebraicGeometry Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (Z : irreducibleComponents X)

/-- The generic point of an irreducible component of a scheme. -/
noncomputable def componentGenericPoint : X :=
  Z.2.1.genericPoint

lemma closure_componentGenericPoint : closure {componentGenericPoint Z} = Z.1 :=
  Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)

/-- The **normalisation of an irreducible component** `Z` of a scheme `X`: the relative
normalisation of `X` in the spectrum of the residue field `κ(η)` at the generic point `η` of `Z`,
which is the function field of `Z`. Over an affine open `Spec A` of `X` containing `η`, with `η`
the prime `𝔭` of `A`, it is the spectrum of the integral closure of `A / 𝔭` in its fraction field
`κ(η)`, and over an affine open not containing `η` it is empty. -/
noncomputable def componentNormalization : Scheme :=
  (X.fromSpecResidueField (componentGenericPoint Z)).normalization

/-- The morphism from the normalisation of an irreducible component of `X` to `X`. -/
noncomputable def componentNormalizationι : componentNormalization Z ⟶ X :=
  (X.fromSpecResidueField (componentGenericPoint Z)).fromNormalization

instance : IsIntegral (componentNormalization Z) :=
  inferInstanceAs (IsIntegral (X.fromSpecResidueField (componentGenericPoint Z)).normalization)

instance : IsIntegralHom (componentNormalizationι Z) :=
  inferInstanceAs
    (IsIntegralHom (X.fromSpecResidueField (componentGenericPoint Z)).fromNormalization)

/-- **The normalisation of an irreducible component `Z` maps onto `Z`.** -/
lemma range_componentNormalizationι : Set.range (componentNormalizationι Z) = Z.1 := by
  let f : Spec (X.residueField (componentGenericPoint Z)) ⟶ X :=
    X.fromSpecResidueField (componentGenericPoint Z)
  have hc : IsClosedMap f.fromNormalization := f.fromNormalization.isClosedMap
  have hd : closure (Set.range f.toNormalization) = Set.univ :=
    f.toNormalization.denseRange.closure_range
  have hf : f.fromNormalization '' Set.range f.toNormalization = Set.range f := by
    rw [← Set.range_comp]
    congr 1
    funext x
    rw [Function.comp_apply, ← Hom.comp_apply, f.toNormalization_fromNormalization]
  have hZ : closure (Set.range f) = Z.1 := by
    rw [range_fromSpecResidueField]
    exact closure_componentGenericPoint Z
  refine (Eq.trans ?_ (congrArg closure hf)).trans hZ
  rw [hc.closure_image_eq_of_continuous f.fromNormalization.continuous, hd, Set.image_univ]
  rfl

variable (F : Type u) [Field F] [X.Over (Spec (.of F))]

noncomputable instance : (componentNormalization Z).Over (Spec (.of F)) :=
  ⟨componentNormalizationι Z ≫ X ↘ Spec (.of F)⟩

/-- **The function field of the normalisation of an irreducible component `Z` is the residue field
at the generic point of `Z`**, which is the function field of `Z`
(`AlgebraicGeometry.Scheme.residueFieldEquivFunctionField`). -/
lemma nonempty_algEquiv_functionField_componentNormalization :
    Nonempty ((componentNormalization Z).functionField ≃ₐ[F]
      X.residueField (componentGenericPoint Z)) := by
  let f : Spec (X.residueField (componentGenericPoint Z)) ⟶ X :=
    X.fromSpecResidueField (componentGenericPoint Z)
  let g : Spec (X.residueField (componentGenericPoint Z)) ⟶ componentNormalization Z :=
    f.toNormalization
  have hgν : g ≫ componentNormalizationι Z = f := f.toNormalization_fromNormalization
  have hf : f ≫ X ↘ Spec (.of F) = Spec.map (CommRingCat.ofHom (algebraMap F
      (X.residueField (componentGenericPoint Z)))) := by
    have hf₀ : f = Spec.map (X.residue _) ≫ X.fromSpecStalk (componentGenericPoint Z) := rfl
    rw [hf₀, Category.assoc, Scheme.fromSpecStalk_comp_over, ← Spec.map_comp]
    rfl
  have hg : g ≫ componentNormalization Z ↘ Spec (.of F) = Spec.map (CommRingCat.ofHom (algebraMap F
      (X.residueField (componentGenericPoint Z)))) := by
    rw [← hf, ← hgν, Category.assoc]
    rfl
  have hs : Function.Surjective (fieldPointMap g) := by
    have key (f' : Spec (X.residueField (componentGenericPoint Z)) ⟶ X)
        (hf' : g ≫ componentNormalizationι Z = f') (h : Function.Surjective (fieldPointMap f')) :
        Function.Surjective (fieldPointMap g) := fun z ↦ by
      subst hf'
      rcases h z with ⟨w, hw⟩
      exact ⟨_, (fieldPointMap_comp g (componentNormalizationι Z) w).symm.trans hw⟩
    exact key f hgν (fieldPointMap_fromSpecResidueField_bijective _).2
  have hb : Function.Bijective (fieldPointAlgHom F g hg) :=
    ⟨(fieldPointAlgHom F g hg).toRingHom.injective, hs⟩
  have hy : g (IsLocalRing.closedPoint (X.residueField (componentGenericPoint Z))) =
      genericPoint (componentNormalization Z) := by
    have hd : closure (Set.range g) = Set.univ := f.toNormalization.denseRange.closure_range
    have hr :
        Set.range g = {g (IsLocalRing.closedPoint (X.residueField (componentGenericPoint Z)))} := by
      refine Set.ext fun x ↦ ⟨?_, ?_⟩
      · rintro ⟨q, rfl⟩
        rw [Subsingleton.elim q (IsLocalRing.closedPoint _)]
        rfl
      · rintro rfl
        exact ⟨_, rfl⟩
    rw [hr] at hd
    exact IsGenericPoint.eq hd (genericPoint_spec _)
  have key (y : componentNormalization Z) (hy' : y = genericPoint (componentNormalization Z))
      (Θ : (componentNormalization Z).residueField y →ₐ[F]
        X.residueField (componentGenericPoint Z)) (hΘ : Function.Bijective Θ) :
      Nonempty ((componentNormalization Z).functionField ≃ₐ[F]
        X.residueField (componentGenericPoint Z)) := by
    subst hy'
    let r : (componentNormalization Z).functionField →ₐ[F] (componentNormalization Z).residueField
        (genericPoint (componentNormalization Z)) :=
      { ((componentNormalization Z).residue _).hom with commutes' := fun c ↦ rfl }
    have hr : Function.Bijective r :=
      ⟨r.toRingHom.injective, (componentNormalization Z).residue_surjective _⟩
    exact ⟨(AlgEquiv.ofBijective r hr).trans (AlgEquiv.ofBijective Θ hΘ)⟩
  exact key _ hy _ hb

/-- The **geometric genus** of an irreducible component `Z` of a scheme over a field `F`: the genus
over `F` of its function field, the function field of the closure of its generic point with the
reduced scheme structure, which is the function field of the normalisation of `Z`
(`AlgebraicGeometry.Scheme.nonempty_algEquiv_functionField_componentNormalization`). It is used for
`F` algebraically closed, the geometric special fibre, so that `F` is the exact constant field of
the function field, as the value of Tau Ceti's `TauCeti.genus` requires. -/
noncomputable def componentGenus : ℕ :=
  genus F (pointClosure (componentGenericPoint Z)).functionField

/-- **The function field of an irreducible component of a curve is an algebraic function field of
one variable**, so that its genus is not a junk value. -/
lemma isFunctionField_component [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of F))] :
    IsFunctionField F (pointClosure (componentGenericPoint Z)).functionField := by
  have : LocallyOfFinitePresentation (X ↘ Spec (.of F)) :=
    SyntomicOfRelativeDimension.locallyOfFinitePresentation 1 (X ↘ Spec (.of F))
  refine (isFunctionField_functionField_iff F).mpr ?_
  have hp : IsPureDimensional 1 X :=
    ((pureRelativeDimension_iff_of_field (X ↘ Spec (.of F))).mp
      (PureRelativeDimension.of_syntomicOfRelativeDimension _)).2
  have hZ : topologicalKrullDim ↥(closure {componentGenericPoint Z}) = 1 := by
    rw [closure_componentGenericPoint]
    exact hp Z.1 Z.2
  rw [(pointClosureHomeomorph _).isHomeomorph.topologicalKrullDim_eq, hZ]

variable (X) [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of F))] in
/-- The set of **singular points** of a scheme `X` syntomic of relative dimension one over a field
`F`: the support of the relative singular locus `Fitt₁(Ω_{X/F})`. -/
noncomputable def singularPoints : Set X :=
  haveI : Flat (X ↘ Spec (.of F)) := SyntomicOfRelativeDimension.flat 1 (X ↘ Spec (.of F))
  haveI : LocallyOfFinitePresentation (X ↘ Spec (.of F)) :=
    SyntomicOfRelativeDimension.locallyOfFinitePresentation 1 (X ↘ Spec (.of F))
  haveI : PureRelativeDimension 1 (X ↘ Spec (.of F)) :=
    PureRelativeDimension.of_syntomicOfRelativeDimension (X ↘ Spec (.of F))
  (X.singularLocus F).support

variable [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of F))] in
/-- The number of **singular points of an irreducible component `Z`, counted with multiplicity**:
the number of points of the normalisation of `Z` above a singular point of `X`, so that a node at
which both branches of `X` lie on `Z` counts twice. -/
noncomputable def componentSingularPointCount : ℕ∞ :=
  (componentNormalizationι Z ⁻¹' X.singularPoints F).encard

lemma componentSingularPointCount_eq_zero [SmoothOfRelativeDimension 1 (X ↘ Spec (.of F))] :
    componentSingularPointCount Z F = 0 := by
  have hs : X.singularPoints F = ∅ := by
    rw [singularPoints, X.singularLocus_eq_top F]
    rfl
  rw [componentSingularPointCount, hs, Set.preimage_empty, Set.encard_empty]

variable (X)

/-- A scheme `X` over a field `F`, algebraically closed in the applications, is a **semistable
curve** (LMFDB `g2c.semistable_reduction`) if it is reduced with at most nodal singularities, and
each irreducible component of geometric genus zero has at least two singular points, counted with
multiplicity. The first condition is Tau Ceti's criterion
`AffineAtWorstNodalOfRelativeDimensionOne`: syntomic of relative dimension one, with singular
subscheme unramified over `F`. Reducedness is not a separate condition, since it is part of this
criterion: a syntomic scheme over a field has no embedded points, and the generic point of a
component that is not generically reduced would lie in the singular subscheme, which is discrete
over `F`. That implication is not proved here (its Cohen--Macaulay input is on Tau Ceti's main). -/
structure IsSemistableOver : Prop where
  /-- The curve has at most nodal singularities. -/
  nodal : AffineAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of F))
  /-- Each component of geometric genus zero has at least two singular points, counted with
  multiplicity. -/
  two_le_componentSingularPointCount (Z : irreducibleComponents X) :
    haveI : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of F)) := nodal.syntomic
    componentGenus Z F = 0 → 2 ≤ componentSingularPointCount Z F

/-- **A smooth curve is semistable exactly when none of its components has genus zero.** In
particular, the projective line is not semistable, while a smooth curve of positive genus is. -/
lemma isSemistableOver_iff_of_smooth [SmoothOfRelativeDimension 1 (X ↘ Spec (.of F))] :
    X.IsSemistableOver F ↔ ∀ Z : irreducibleComponents X, componentGenus Z F ≠ 0 := by
  refine ⟨fun h Z hZ ↦ ?_, fun h ↦ ⟨AffineAtWorstNodalOfRelativeDimensionOne.of_smooth,
    fun Z hZ ↦ (h Z hZ).elim⟩⟩
  have hZ₂ : 2 ≤ componentSingularPointCount Z F := h.two_le_componentSingularPointCount Z hZ
  rw [componentSingularPointCount_eq_zero] at hZ₂
  exact absurd hZ₂ (by simp)

end AlgebraicGeometry.Scheme

namespace TauCeti.Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)} (M : Model R K C toK)

/-- The **geometric special fibre** of a model `M` over a discrete valuation ring `R`: its base
change to an algebraic closure of the residue field of `R`. -/
noncomputable def geometricSpecialFiber : Scheme.{u} :=
  pullback M.toBase (Spec.map (CommRingCat.ofHom
    (algebraMap R (AlgebraicClosure (ResidueField R)))))

noncomputable instance :
    M.geometricSpecialFiber.Over (Spec (.of (AlgebraicClosure (ResidueField R)))) :=
  ⟨pullback.snd M.toBase (Spec.map (CommRingCat.ofHom
    (algebraMap R (AlgebraicClosure (ResidueField R)))))⟩

lemma isPullback_geometricSpecialFiber :
    IsPullback (pullback.fst M.toBase (Spec.map (CommRingCat.ofHom
      (algebraMap R (AlgebraicClosure (ResidueField R))))))
      (M.geometricSpecialFiber ↘ Spec (.of (AlgebraicClosure (ResidueField R)))) M.toBase
      (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure (ResidueField R))))) :=
  IsPullback.of_hasPullback _ _

variable {M} in
/-- **The geometric special fibre of a nodal model is nodal.** -/
lemma atWorstNodal_geometricSpecialFiber (hM : AffineAtWorstNodalOfRelativeDimensionOne M.toBase) :
    AffineAtWorstNodalOfRelativeDimensionOne
      (M.geometricSpecialFiber ↘ Spec (.of (AlgebraicClosure (ResidueField R)))) := by
  let _ : M.total.Over (Spec (.of R)) := ⟨M.toBase⟩
  exact AffineAtWorstNodalOfRelativeDimensionOne.of_isPullback
    M.isPullback_geometricSpecialFiber hM

instance [SmoothOfRelativeDimension 1 M.toBase] : SmoothOfRelativeDimension 1
    (M.geometricSpecialFiber ↘ Spec (.of (AlgebraicClosure (ResidueField R)))) :=
  MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
    M.isPullback_geometricSpecialFiber inferInstance

end TauCeti.Model

namespace AlgebraicGeometry.Scheme

variable (R : Type u) {K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] {C : Scheme.{u}} (toK : C ⟶ Spec (.of K))

/-- A curve `C` over the fraction field `K` of a discrete valuation ring `R`, such as the ring of
integers of a local field, has **semistable reduction** (LMFDB `g2c.semistable_reduction`) if it has
a proper model over `R` (Tau Ceti's `TauCeti.Model`) whose special fibre is semistable, that is,
whose geometric special fibre is a reduced curve with at most nodal singularities, each of whose
components of geometric genus zero has at least two singular points, counted with multiplicity. -/
def HasSemistableReduction : Prop :=
  ∃ M : Model R K C toK, M.IsProper ∧
    M.geometricSpecialFiber.IsSemistableOver (AlgebraicClosure (ResidueField R))

variable {R toK}

/-- **A nodal model satisfying the condition on the components of genus zero gives semistable
reduction**: this is the proper at worst nodal model of `HasNodalReduction`, with the additional
condition of the knowl. -/
lemma HasSemistableReduction.of_nodal (M : Model R K C toK) (hM : M.IsProper)
    (hn : AffineAtWorstNodalOfRelativeDimensionOne M.toBase)
    (h : ∀ Z : irreducibleComponents M.geometricSpecialFiber,
      haveI : SyntomicOfRelativeDimension 1
          (M.geometricSpecialFiber ↘ Spec (.of (AlgebraicClosure (ResidueField R)))) :=
        (Model.atWorstNodal_geometricSpecialFiber hn).syntomic
      componentGenus Z (AlgebraicClosure (ResidueField R)) = 0 →
        2 ≤ componentSingularPointCount Z (AlgebraicClosure (ResidueField R))) :
    HasSemistableReduction R toK :=
  ⟨M, hM, Model.atWorstNodal_geometricSpecialFiber hn, h⟩

/-- **Good reduction with no component of genus zero implies semistable reduction**: a curve with a
proper smooth model of relative dimension one, no component of whose geometric special fibre has
genus zero, has semistable reduction. -/
lemma HasSemistableReduction.of_smooth (M : Model R K C toK) (hM : M.IsProper)
    [SmoothOfRelativeDimension 1 M.toBase] (h : ∀ Z : irreducibleComponents M.geometricSpecialFiber,
      componentGenus Z (AlgebraicClosure (ResidueField R)) ≠ 0) : HasSemistableReduction R toK :=
  ⟨M, hM, (M.geometricSpecialFiber.isSemistableOver_iff_of_smooth _).mpr h⟩

end AlgebraicGeometry.Scheme
