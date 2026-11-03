import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
import TauCeti.AlgebraicGeometry.Scheme.FunctionField

/-!
# The closure of a point of a scheme

The closure of a point `x` of a scheme `X`, with the reduced induced scheme structure, is an
integral closed subscheme of `X` with generic point `x`, and its function field is the residue
field `κ(x)` of `x`. So, for `X` locally of finite type over a field `k`, the dimension of the
closure of `x` is the transcendence degree of `κ(x)` over `k`.

A point of `Y` with values in a field `K`, a morphism `g : Spec K ⟶ Y`, embeds the residue field of
its image in `K`. This embedding is computed here when `g` factors through an open affine chart
`Spec C` of `Y`: its image consists of the quotients of the elements of the image of `C` in `K`.

The reducedness and integrality of the closure of a point and the dimension formula are on Tau
Ceti's main, but not at the pinned version, as
`AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal`,
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure_singleton`,
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure_singleton`
and `TauCeti.AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField`:
they should replace the versions here after a bump.

## Main definitions

* `AlgebraicGeometry.Scheme.pointClosure`: the closure of a point, as an integral scheme.
* `AlgebraicGeometry.Scheme.residueFieldEquivFunctionField`: the function field of the closure of a
  point is its residue field.
* `AlgebraicGeometry.Scheme.fieldPointMap`, `AlgebraicGeometry.Scheme.fieldPointAlgHom`: the
  embedding into `K` of the residue field of the image of a `K`-point.

## Main results

* `AlgebraicGeometry.Scheme.topologicalKrullDim_closure_singleton`: the dimension of the closure of
  a point is the transcendence degree of its residue field.
* `AlgebraicGeometry.Scheme.range_fieldPointMap_specMap_comp`: the image in `K` of the residue field
  of a `K`-point factoring through an open affine chart `Spec C` consists of the quotients of the
  elements of the image of `C`.
* The instance `IsReduced (IdealSheafData.vanishingIdeal Z).subscheme`: the reduced induced scheme
  structure on a closed subset is reduced.
-/

open CategoryTheory TauCeti AlgebraicGeometry TopologicalSpace Topology

namespace AlgebraicGeometry.Scheme

universe u

variable {X Y Y' : Scheme.{u}}

instance (Z : Closeds X) : IsReduced (IdealSheafData.vanishingIdeal Z).subscheme :=
  have (U : X.affineOpens) :
      IsReduced ((Spec (.of (Γ(X, U) ⧸ (IdealSheafData.vanishingIdeal Z).ideal U))) : Scheme) :=
    (affine_isReduced_iff _).mpr <|
      (Ideal.isRadical_iff_quotient_reduced _).mp (PrimeSpectrum.isRadical_vanishingIdeal _)
  have : ∀ i, IsReduced ((IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.X i) :=
    fun (U : X.affineOpens) ↦ inferInstanceAs
      (IsReduced ((Spec (.of (Γ(X, U) ⧸ (IdealSheafData.vanishingIdeal Z).ideal U))) : Scheme))
  .of_openCover _ (IdealSheafData.vanishingIdeal Z).subschemeCover.openCover

variable (x : X)

/-- The closure of a point `x` of a scheme, with the reduced induced scheme structure. -/
noncomputable def pointClosure : Scheme.{u} :=
  (IdealSheafData.vanishingIdeal (Closeds.closure {x})).subscheme

/-- The inclusion of the closure of a point. -/
noncomputable def pointClosureι : pointClosure x ⟶ X :=
  (IdealSheafData.vanishingIdeal (Closeds.closure {x})).subschemeι

instance : IsClosedImmersion (pointClosureι x) :=
  inferInstanceAs (IsClosedImmersion (IdealSheafData.vanishingIdeal _).subschemeι)

lemma range_pointClosureι : Set.range (pointClosureι x) = closure {x} :=
  (IdealSheafData.vanishingIdeal (Closeds.closure {x})).range_subschemeι.trans <| by
    rw [IdealSheafData.coe_support_vanishingIdeal]
    rfl

/-- The closed subscheme `AlgebraicGeometry.Scheme.pointClosure` is homeomorphic to the closure of
the point. -/
noncomputable def pointClosureHomeomorph : pointClosure x ≃ₜ closure ({x} : Set X) :=
  (pointClosureι x).isEmbedding.toHomeomorph.trans (.setCongr (range_pointClosureι x))

instance : IrreducibleSpace (pointClosure x) := by
  have : IrreducibleSpace (closure ({x} : Set X)) :=
    Subtype.irreducibleSpace isIrreducible_singleton.closure
  have h : IsIrreducible ((pointClosureHomeomorph x).symm '' Set.univ) :=
    (IrreducibleSpace.isIrreducible_univ (closure ({x} : Set X))).image _
      (pointClosureHomeomorph x).symm.continuous.continuousOn
  rw [Set.image_univ, Homeomorph.range_coe] at h
  exact (irreducibleSpace_def _).mpr h

instance : IsIntegral (pointClosure x) :=
  have : IsReduced (pointClosure x) := inferInstanceAs (IsReduced (IdealSheafData.subscheme _))
  isIntegral_of_irreducibleSpace_of_isReduced _

lemma pointClosureι_genericPoint : pointClosureι x (genericPoint (pointClosure x)) = x := by
  have h : IsGenericPoint (pointClosureι x (genericPoint (pointClosure x)))
      (closure (pointClosureι x '' Set.univ)) :=
    (genericPoint_spec (pointClosure x)).image (pointClosureι x).continuous
  rw [Set.image_univ, range_pointClosureι, closure_closure] at h
  exact h.eq isGenericPoint_closure

variable (k : Type u) [Field k] [X.Over (Spec (.of k))] (c : k)

noncomputable instance : (pointClosure x).Over (Spec (.of k)) :=
  ⟨pointClosureι x ≫ X ↘ Spec (.of k)⟩

lemma pointClosure_over : pointClosure x ↘ Spec (.of k) = pointClosureι x ≫ X ↘ Spec (.of k) :=
  rfl

instance [LocallyOfFiniteType (X ↘ Spec (.of k))] :
    LocallyOfFiniteType (pointClosure x ↘ Spec (.of k)) := by
  rw [pointClosure_over]
  infer_instance

lemma stalkMap_algebraMap [Y.Over (Spec (.of k))] (f : Y ⟶ X) [f.IsOver (Spec (.of k))] (y : Y) :
    f.stalkMap y (algebraMap k (X.presheaf.stalk (f y)) c) =
      algebraMap k (Y.presheaf.stalk y) c := by
  have h₁ : f.appTop (Modules.baseRingToGlobalSections k X c) =
      Modules.baseRingToGlobalSections k Y c := by
    rw [Modules.baseRingToGlobalSections_apply, Modules.baseRingToGlobalSections_apply,
      ← comp_over f (Spec (.of k)), Hom.comp_appTop]
    rfl
  rw [Scheme.algebraMap_stalk_eq_baseRingToStalk, Scheme.algebraMap_stalk_eq_baseRingToStalk,
    Scheme.baseRingToStalk_apply, Scheme.baseRingToStalk_apply, ← h₁]
  exact f.germ_stalkMap_apply ⊤ y trivial _

/-- The map from the residue field of `x'` to the function field of the closure of `x`, where
`x' = x` is the image of the generic point. -/
noncomputable def residueFieldToFunctionField :
    X.residueField (pointClosureι x (genericPoint (pointClosure x))) ⟶
      .of (pointClosure x).functionField :=
  X.descResidueField ((pointClosureι x).stalkMap (genericPoint (pointClosure x)))

lemma residueFieldToFunctionField_residue (a : X.presheaf.stalk _) :
    residueFieldToFunctionField x (X.residue _ a) =
      (pointClosureι x).stalkMap (genericPoint (pointClosure x)) a :=
  rfl

lemma residueFieldToFunctionField_bijective :
    Function.Bijective (residueFieldToFunctionField x) := by
  refine ⟨(residueFieldToFunctionField x).hom.injective, fun a ↦ ?_⟩
  rcases (pointClosureι x).stalkMap_surjective (genericPoint (pointClosure x)) a with ⟨b, rfl⟩
  exact ⟨X.residue _ b, residueFieldToFunctionField_residue x b⟩

instance : (pointClosureι x).IsOver (Spec (.of k)) :=
  ⟨rfl⟩

lemma residueFieldToFunctionField_algebraMap :
    residueFieldToFunctionField x (algebraMap k (X.residueField _) c) =
      algebraMap k (pointClosure x).functionField c :=
  (residueFieldToFunctionField_residue x _).trans
    (stalkMap_algebraMap k c (pointClosureι x) (genericPoint (pointClosure x)))

/-- **The function field of the closure of a point is its residue field.** -/
noncomputable def residueFieldEquivFunctionField :
    X.residueField (pointClosureι x (genericPoint (pointClosure x))) ≃ₐ[k]
      (pointClosure x).functionField :=
  AlgEquiv.ofBijective
    { (residueFieldToFunctionField x).hom with
      commutes' := residueFieldToFunctionField_algebraMap x k }
    (residueFieldToFunctionField_bijective x)

lemma trdeg_residueField_eq_trdeg_functionField :
    Algebra.trdeg k (X.residueField x) = Algebra.trdeg k (pointClosure x).functionField := by
  have h (y : X) (hy : y = x) :
      Algebra.trdeg k (X.residueField y) = Algebra.trdeg k (X.residueField x) := by
    subst hy
    rfl
  rw [← h _ (pointClosureι_genericPoint x)]
  exact (residueFieldEquivFunctionField x k).trdeg_eq

variable [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- **The dimension of the closure of a point is the transcendence degree of its residue field**,
for a scheme locally of finite type over a field. -/
lemma topologicalKrullDim_closure_singleton :
    topologicalKrullDim (closure ({x} : Set X)) = (Algebra.trdeg k (X.residueField x)).toNat := by
  rw [trdeg_residueField_eq_trdeg_functionField,
    ← topologicalKrullDim_eq_toNat_trdeg_functionField k (X := pointClosure x)]
  exact (pointClosureHomeomorph x).isHomeomorph.topologicalKrullDim_eq.symm

lemma trdeg_residueField_lt_aleph0 : Algebra.trdeg k (X.residueField x) < Cardinal.aleph0 := by
  rw [trdeg_residueField_eq_trdeg_functionField]
  exact trdeg_lt_aleph0 k (pointClosure x).functionField

lemma topologicalKrullDim_closure_singleton_eq_toENat :
    topologicalKrullDim (closure ({x} : Set X)) =
      ((Algebra.trdeg k (X.residueField x)).toENat : ℕ∞) := by
  rw [topologicalKrullDim_closure_singleton x k]
  rcases Cardinal.lt_aleph0.mp (trdeg_residueField_lt_aleph0 x k) with ⟨n, hn⟩
  rw [hn]
  simp

variable {K : Type u} [Field K]

lemma exists_mul_evaluation_eq {U : Y.Opens} (hU : IsAffineOpen U) {y : Y} (hy : y ∈ U)
    (z : Y.residueField y) : ∃ a b : Γ(Y, U), Y.evaluation U y hy b ≠ 0 ∧
      z * Y.evaluation U y hy b = Y.evaluation U y hy a := by
  let _ : Algebra Γ(Y, U) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk ⟨y, hy⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  rcases Y.residue_surjective y z with ⟨s, rfl⟩
  rcases IsLocalization.surj (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl s with ⟨⟨a, b⟩, h⟩
  refine ⟨a, b, ?_, ?_⟩
  · exact ((IsLocalization.map_units (Y.presheaf.stalk y) b).map (Y.residue y).hom).ne_zero
  · exact (map_mul (Y.residue y).hom _ _).symm.trans (congrArg _ h)

variable (g : Spec (.of K) ⟶ Y)

/-- The embedding into `K` of the residue field of the image of a `K`-point `g`. -/
noncomputable def fieldPointMap : Y.residueField (g (IsLocalRing.closedPoint K)) ⟶ .of K :=
  Y.descResidueField (stalkClosedPointTo g)

lemma fieldPointMap_residue (a : Y.presheaf.stalk _) :
    fieldPointMap g (Y.residue _ a) = stalkClosedPointTo g a :=
  rfl

lemma fieldPointMap_injective : Function.Injective (fieldPointMap g) :=
  (fieldPointMap g).hom.injective

lemma fieldPointMap_comp (j : Y ⟶ Y') (z : Y'.residueField ((g ≫ j) (IsLocalRing.closedPoint K))) :
    fieldPointMap (g ≫ j) z = fieldPointMap g (j.residueFieldMap _ z) := by
  rcases Y'.residue_surjective _ z with ⟨a, rfl⟩
  rw [fieldPointMap_residue, stalkClosedPointTo_comp]
  exact (congrArg (fieldPointMap g) (ConcreteCategory.congr_hom
    (residue_residueFieldMap j (g (IsLocalRing.closedPoint K))) a)).symm

variable {C : CommRingCat.{u}} (Ψ : C ⟶ .of K)

lemma fieldPointMap_specMap_evaluation (a : C) :
    fieldPointMap (Spec.map Ψ) ((Spec C).evaluation ⊤ _ trivial ((ΓSpecIso C).inv a)) = Ψ a := by
  refine (ConcreteCategory.congr_hom (germ_stalkClosedPointTo_Spec Ψ) ((ΓSpecIso C).inv a)).trans ?_
  rw [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]

/-- **The residue field of a point in an open affine chart `Spec C`, seen in `K` through a
`K`-point of the chart given by `Ψ : C → K`, consists of the quotients of elements of `Ψ(C)`.** -/
lemma range_fieldPointMap_specMap_comp (j : Spec C ⟶ Y) [IsOpenImmersion j] (a : K) :
    a ∈ Set.range (fieldPointMap (Spec.map Ψ ≫ j)) ↔ ∃ b c : C, Ψ c ≠ 0 ∧ a = Ψ b / Ψ c := by
  let x₀ : Spec C := Spec.map Ψ (IsLocalRing.closedPoint K)
  let ev (c : C) : (Spec C).residueField x₀ := (Spec C).evaluation ⊤ x₀ trivial ((ΓSpecIso C).inv c)
  have hev (c : C) : fieldPointMap (Spec.map Ψ) (ev c) = Ψ c :=
    fieldPointMap_specMap_evaluation Ψ c
  have hbij : Function.Bijective (j.residueFieldMap x₀) :=
    ConcreteCategory.bijective_of_isIso _
  constructor
  · rintro ⟨z, rfl⟩
    rcases exists_mul_evaluation_eq (isAffineOpen_top (Spec C)) (y := x₀) trivial
      (j.residueFieldMap x₀ z) with ⟨b, c, hc, h⟩
    have hb (r : Γ(Spec C, ⊤)) : (Spec C).evaluation ⊤ x₀ trivial r = ev ((ΓSpecIso C).hom r) := by
      simp only [ev, Iso.hom_inv_id_apply]
    rw [hb, hb] at h
    rw [hb] at hc
    have hc' : fieldPointMap (Spec.map Ψ) (ev ((ΓSpecIso C).hom c)) ≠ 0 := fun h₀ ↦
      hc (fieldPointMap_injective _ (h₀.trans (map_zero _).symm))
    refine ⟨(ΓSpecIso C).hom b, (ΓSpecIso C).hom c, (hev _).symm.trans_ne hc', ?_⟩
    rw [fieldPointMap_comp, ← hev, ← hev, eq_div_iff hc', ← map_mul, h]
  · rintro ⟨b, c, hc, rfl⟩
    rcases hbij.2 (ev b / ev c) with ⟨z, hz⟩
    exact ⟨z, (fieldPointMap_comp (Spec.map Ψ) j z).trans (by rw [hz, map_div₀, hev, hev])⟩

lemma fieldPointMap_fromSpecResidueField_bijective (y : Y) :
    Function.Bijective (fieldPointMap (Y.fromSpecResidueField y)) := by
  have hy : Y.fromSpecResidueField y (IsLocalRing.closedPoint (Y.residueField y)) = y :=
    Set.mem_singleton_iff.mp <| (range_fromSpecResidueField y) ▸ Set.mem_range_self _
  have hp : Mono (Y.fromSpecResidueField
      (Y.fromSpecResidueField y (IsLocalRing.closedPoint (Y.residueField y)))) := inferInstance
  have h₃ : fieldPointMap (Y.fromSpecResidueField y) = (Y.residueFieldCongr hy).hom :=
    Spec.map_injective (hp.right_cancellation _ _
      ((descResidueField_stalkClosedPointTo_fromSpecResidueField (Y.residueField y) Y
        (Y.fromSpecResidueField y)).trans (residueFieldCongr_fromSpecResidueField hy).symm))
  rw [h₃]
  exact (Y.residueFieldCongr hy).commRingCatIsoToRingEquiv.bijective

variable [Y.Over (Spec (.of k))] [Algebra k K]

lemma fieldPointMap_algebraMap
    (hg : g ≫ Y ↘ Spec (.of k) = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    fieldPointMap g (algebraMap k (Y.residueField (g (IsLocalRing.closedPoint K))) c) =
      algebraMap k K c := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap k
      (Y.presheaf.stalk (g (IsLocalRing.closedPoint K)))) ≫ stalkClosedPointTo g) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [Spec.map_comp, ← fromSpecStalk_comp_over, ← hg, ← Category.assoc,
      Spec_stalkClosedPointTo_fromSpecStalk]
  have h₁ : algebraMap k (Y.residueField (g (IsLocalRing.closedPoint K))) c =
      Y.residue _ (algebraMap k (Y.presheaf.stalk (g (IsLocalRing.closedPoint K))) c) :=
    rfl
  have h₃ : CommRingCat.ofHom (algebraMap k
      (Y.presheaf.stalk (g (IsLocalRing.closedPoint K)))) ≫ stalkClosedPointTo g =
      CommRingCat.ofHom (algebraMap k K) := Spec.map_injective h
  have h₂ : stalkClosedPointTo g
      (algebraMap k (Y.presheaf.stalk (g (IsLocalRing.closedPoint K))) c) = algebraMap k K c := by
    rw [← CommRingCat.ofHom_apply (algebraMap k _) c, ← ConcreteCategory.comp_apply, h₃]
    rfl
  rw [h₁, fieldPointMap_residue]
  exact h₂

variable (hg : g ≫ Y ↘ Spec (.of k) = Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- The embedding into `K` of the residue field of the image of a `K`-point `g` over `k`, as a
`k`-algebra homomorphism. -/
noncomputable def fieldPointAlgHom : Y.residueField (g (IsLocalRing.closedPoint K)) →ₐ[k] K :=
  letI f : Y.residueField (g (IsLocalRing.closedPoint K)) →+* K := (fieldPointMap g).hom
  AlgHom.mk f fun c ↦ fieldPointMap_algebraMap k c g hg

lemma trdeg_residueField_eq_trdeg_fieldRange :
    Algebra.trdeg k (Y.residueField (g (IsLocalRing.closedPoint K))) =
      Algebra.trdeg k (fieldPointAlgHom k g hg).fieldRange :=
  (AlgEquiv.ofInjectiveField (fieldPointAlgHom k g hg)).trdeg_eq

end AlgebraicGeometry.Scheme
