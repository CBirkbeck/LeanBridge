import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.StableAffineOpen
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Affine

/-!
# The invariant quotient of a scheme with two stable affine charts

Let a finite group `G` act on a scheme `X` covered by two stable affine opens `W₁` and `W₂` whose
intersection `V` is affine. The invariant quotient of `X` is the scheme obtained by gluing
`Spec Γ(X, W₁)ᴳ` and `Spec Γ(X, W₂)ᴳ` along the open subscheme `Spec Γ(X, V)ᴳ`, a pushout of open
immersions. It has the projection from `X` glued from those of the charts. This is the construction
of the quotient curve (LMFDB `ag.quotient_curve`), as every algebraic curve has such a cover, by
`LeanBridge.ForMathlib.AlgebraicGeometry.Curve.QuotientExistence`.

The universal property, the description of the fibres and the integrality of the projection are
checked on the charts, using Tau Ceti's `TauCeti.AffineInvariantQuotient`. The square formed by the
projection, the projection of a chart and the inclusions of the chart is a pullback since a point of
`X` mapping to the invariant quotient of a chart lies in that chart: its orbit meets the chart, and
so does the orbit of a point of the intersection, which is stable.

## Main definitions

* `AlgebraicGeometry.Scheme.StableAffineOpen.TwoChartCover`: a cover by two stable affine opens with
  affine intersection.
* `AlgebraicGeometry.Scheme.StableAffineOpen.TwoChartCover.quotient`: the invariant quotient.
* `AlgebraicGeometry.Scheme.StableAffineOpen.TwoChartCover.proj`: the projection onto it.
* `AlgebraicGeometry.Scheme.StableAffineOpen.TwoChartCover.desc`: the morphism on the invariant
  quotient induced by an invariant morphism.

## Main results

* `AlgebraicGeometry.Scheme.isSeparated_of_comp_of_surjective`: a scheme that a surjective
  universally closed morphism from a separated scheme maps onto is separated.
* `AlgebraicGeometry.Scheme.StableAffineOpen.TwoChartCover.hom_proj`: the projection is invariant.
* `AlgebraicGeometry.Scheme.StableAffineOpen.TwoChartCover.proj_desc`: an invariant morphism factors
  through the projection.
* `AlgebraicGeometry.Scheme.StableAffineOpen.TwoChartCover.isPullback_ι`: over a chart, the
  projection is the projection of the chart.
* `AlgebraicGeometry.Scheme.StableAffineOpen.TwoChartCover.proj_eq_iff`: the fibres of the
  projection are the orbits.
* The instances `IsIntegralHom C.proj` and `Surjective C.proj`: the projection is integral and
  surjective.
-/

open CategoryTheory Limits WidePushoutShape AlgebraicGeometry TopologicalSpace TauCeti
  AffineInvariantQuotient

namespace AlgebraicGeometry.Scheme

universe u v

/-- **A scheme that a surjective universally closed morphism from a separated scheme maps onto is
separated.** The diagonal of the target is an immersion, and its range is the image of the range of
the diagonal of the source under a universally closed morphism, so it is closed. -/
lemma isSeparated_of_comp_of_surjective {X Y S : Scheme.{u}} (π : X ⟶ Y) (q : Y ⟶ S) [Surjective π]
    [UniversallyClosed π] [IsSeparated (π ≫ q)] : IsSeparated q := by
  let Φ : pullback (π ≫ q) (π ≫ q) ⟶ pullback q q :=
    pullback.map (π ≫ q) (π ≫ q) q q π π (𝟙 S) ((Category.comp_id _).trans rfl)
      ((Category.comp_id _).trans rfl)
  have hΦ : UniversallyClosed Φ :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) ‹_› ‹_› rfl rfl
  have hcomm : π ≫ pullback.diagonal q = pullback.diagonal (π ≫ q) ≫ Φ := by
    ext <;> simp [Φ]
  have hrange : Set.range (pullback.diagonal q) = Φ '' Set.range (pullback.diagonal (π ≫ q)) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      rcases π.surjective y with ⟨x, rfl⟩
      refine ⟨pullback.diagonal (π ≫ q) x, ⟨x, rfl⟩, ?_⟩
      rw [← Hom.comp_apply, ← hcomm, Hom.comp_apply]
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨π x, ?_⟩
      rw [← Hom.comp_apply, hcomm, Hom.comp_apply]
  have hclosed : IsClosed (Set.range (pullback.diagonal q)) :=
    hrange ▸ Φ.isClosedMap _ (pullback.diagonal (π ≫ q)).isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩

namespace StableAffineOpen

variable {X : Scheme.{u}} {G : Type v} [Group G]

/-- A cover of a scheme by two affine opens stable under the action `ρ` of a group, whose
intersection is affine. -/
structure TwoChartCover (ρ : G →* Aut X) where
  /-- The two charts. -/
  W : Bool → StableAffineOpen ρ
  /-- The intersection of the two charts. -/
  V : StableAffineOpen ρ
  /-- The intersection of the two charts is indeed their intersection. -/
  inf_eq : V.carrier = (W true).carrier ⊓ (W false).carrier
  /-- The two charts cover the scheme. -/
  sup_eq : (W true).carrier ⊔ (W false).carrier = ⊤

namespace TwoChartCover

variable {ρ : G →* Aut X} (C : TwoChartCover ρ) (b c : Bool) {x : X}

lemma le : C.V.carrier ≤ (C.W b).carrier := by
  rw [C.inf_eq]
  cases b
  exacts [inf_le_right, inf_le_left]

variable {b c} in
lemma mem_V (hbc : b ≠ c) (hb : x ∈ (C.W b).carrier) (hc : x ∈ (C.W c).carrier) :
    x ∈ C.V.carrier := by
  rw [C.inf_eq]
  cases b <;> cases c
  exacts [(hbc rfl).elim, ⟨hc, hb⟩, ⟨hb, hc⟩, (hbc rfl).elim]

variable (x) in
lemma exists_mem : ∃ b, x ∈ (C.W b).carrier := by
  have h₁ : x ∈ (C.W true).carrier ⊔ (C.W false).carrier := C.sup_eq ▸ trivial
  rcases (Opens.mem_sup.mp h₁) with h₂ | h₂
  exacts [⟨_, h₂⟩, ⟨_, h₂⟩]

/-- The open cover of the scheme by the spectra of the two charts. -/
noncomputable def cover : X.OpenCover :=
  Cover.mkOfCovers Bool (fun b ↦ Spec Γ(X, (C.W b).carrier)) (fun b ↦ (C.W b).fromSpec) fun x ↦ by
    rcases C.exists_mem x with ⟨b, hb⟩
    rcases (C.W b).exists_fromSpec_eq hb with ⟨y, hy⟩
    exact ⟨b, y, hy⟩

variable {T : Scheme.{u}} (φ : ∀ b, Spec Γ(X, (C.W b).carrier) ⟶ T)

lemma pullback_fst_comp_eq (hφ : ∀ b c, Spec.map (C.V.res (C.W b) (C.le b)) ≫ φ b =
    Spec.map (C.V.res (C.W c) (C.le c)) ≫ φ c) :
    pullback.fst (C.W b).fromSpec (C.W c).fromSpec ≫ φ b =
      pullback.snd (C.W b).fromSpec (C.W c).fromSpec ≫ φ c := by
  by_cases hbc : b = c
  · subst hbc
    have h₁ : pullback.fst (C.W b).fromSpec (C.W b).fromSpec = pullback.snd _ _ :=
      (cancel_mono (C.W b).fromSpec).mp pullback.condition
    rw [h₁]
  have hr : Set.range (pullback.fst (C.W b).fromSpec (C.W c).fromSpec ≫ (C.W b).fromSpec) ⊆
      Set.range C.V.fromSpec := by
    rw [C.V.isAffineOpen.range_fromSpec]
    rintro _ ⟨t, rfl⟩
    refine C.mem_V hbc ((C.W b).fromSpec_apply_mem _) ?_
    rw [pullback.condition, Hom.comp_apply]
    exact (C.W c).fromSpec_apply_mem _
  let l : pullback (C.W b).fromSpec (C.W c).fromSpec ⟶ Spec Γ(X, C.V.carrier) :=
    IsOpenImmersion.lift C.V.fromSpec _ hr
  have hl : l ≫ C.V.fromSpec = pullback.fst (C.W b).fromSpec (C.W c).fromSpec ≫ (C.W b).fromSpec :=
    IsOpenImmersion.lift_fac _ _ _
  have h₁ : l ≫ Spec.map (C.V.res (C.W b) (C.le b)) = pullback.fst _ _ :=
    (cancel_mono (C.W b).fromSpec).mp (by rw [Category.assoc, specMap_res_fromSpec, hl])
  have h₂ : l ≫ Spec.map (C.V.res (C.W c) (C.le c)) = pullback.snd _ _ :=
    (cancel_mono (C.W c).fromSpec).mp (by
      rw [Category.assoc, specMap_res_fromSpec, hl, pullback.condition])
  rw [← h₁, ← h₂, Category.assoc, Category.assoc, hφ b c]

variable (hφ : ∀ b c, Spec.map (C.V.res (C.W b) (C.le b)) ≫ φ b =
  Spec.map (C.V.res (C.W c) (C.le c)) ≫ φ c)

/-- Morphisms on the spectra of the two charts agreeing on the spectrum of the intersection glue to
a morphism on the scheme. -/
noncomputable def glue : X ⟶ T :=
  C.cover.glueMorphisms φ fun b c ↦ C.pullback_fst_comp_eq b c φ hφ

@[reassoc]
lemma fromSpec_glue : (C.W b).fromSpec ≫ C.glue φ hφ = φ b :=
  C.cover.ι_glueMorphisms φ _ b

lemma hom_ext {f₁ f₂ : X ⟶ T} (h : ∀ b, (C.W b).fromSpec ≫ f₁ = (C.W b).fromSpec ≫ f₂) : f₁ = f₂ :=
  C.cover.hom_ext _ _ h

variable (f : X ⟶ T) (g : G)

lemma specComap_fromSpec_comp (hf : ∀ g, (ρ g).asIso.hom ≫ f = f) :
    specComap Γ(X, (C.W b).carrier) G g ≫ (C.W b).fromSpec ≫ f = (C.W b).fromSpec ≫ f := by
  rw [← Category.assoc, specComap_fromSpec, Category.assoc, hf]

variable [Finite G]

/-- The **invariant quotient** of a scheme with a two-chart cover (LMFDB `ag.quotient_curve`): the
invariant quotients of the two charts glued along the invariant quotient of their intersection. -/
noncomputable def quotient : Scheme.{u} :=
  pushout (C.V.qMap (C.W true) (C.le true)) (C.V.qMap (C.W false) (C.le false))

/-- The open immersion of the invariant quotient of a chart into the quotient. -/
noncomputable def ι : ∀ b, (C.W b).Q ⟶ C.quotient
  | true => pushout.inl _ _
  | false => pushout.inr _ _

instance : IsOpenImmersion (C.ι b) := by
  cases b
  · exact inferInstanceAs (IsOpenImmersion (pushout.inr _ _))
  · exact inferInstanceAs (IsOpenImmersion (pushout.inl _ _))

@[reassoc]
lemma qMap_ι : C.V.qMap (C.W b) (C.le b) ≫ C.ι b = C.V.qMap (C.W c) (C.le c) ≫ C.ι c := by
  have h₁ : C.V.qMap (C.W true) (C.le true) ≫ C.ι true =
      C.V.qMap (C.W false) (C.le false) ≫ C.ι false := pushout.condition
  cases b <;> cases c
  exacts [rfl, h₁.symm, h₁, rfl]

lemma exists_ι_eq (y : C.quotient) : ∃ b q, C.ι b q = y := by
  rcases IsLocallyDirected.ι_jointly_surjective (span _ _) y with ⟨i, q, rfl⟩
  rcases i with _ | _ | _
  · refine ⟨true, C.V.qMap (C.W true) (C.le true) q, ?_⟩
    rw [← Hom.comp_apply, ← colimit.w (span _ _) (Hom.init .left)]
    rfl
  · exact ⟨true, q, rfl⟩
  · exact ⟨false, q, rfl⟩

variable {b c} in
lemma exists_of_ι_eq (hbc : b ≠ c) {q : (C.W b).Q} {q' : (C.W c).Q} (h : C.ι b q = C.ι c q') :
    ∃ w : C.V.Q, C.V.qMap (C.W b) (C.le b) w = q ∧ C.V.qMap (C.W c) (C.le c) w = q' := by
  let D : WalkingSpan ⥤ Scheme.{u} :=
    span (C.V.qMap (C.W true) (C.le true)) (C.V.qMap (C.W false) (C.le false))
  cases b <;> cases c
  · exact (hbc rfl).elim
  · have hp : colimit.ι D WalkingSpan.right q = colimit.ι D WalkingSpan.left q' := h
    rcases (IsLocallyDirected.ι_eq_ι_iff _).mp hp with ⟨j, fp, fq, z, rfl, rfl⟩
    rcases j with _ | _ | _
    · cases fq
      cases fp
      exact ⟨z, rfl, rfl⟩
    · cases fp
    · cases fq
  · have hp : colimit.ι D WalkingSpan.left q = colimit.ι D WalkingSpan.right q' := h
    rcases (IsLocallyDirected.ι_eq_ι_iff _).mp hp with ⟨j, fp, fq, z, rfl, rfl⟩
    rcases j with _ | _ | _
    · cases fq
      cases fp
      exact ⟨z, rfl, rfl⟩
    · cases fq
    · cases fp
  · exact (hbc rfl).elim

/-- The **projection** onto the invariant quotient. -/
noncomputable def proj : X ⟶ C.quotient :=
  C.glue (fun b ↦ (C.W b).proj ≫ C.ι b) fun b c ↦ by
    rw [← Category.assoc, ← Category.assoc, ← proj_qMap, ← proj_qMap, Category.assoc,
      Category.assoc, C.qMap_ι b c]

@[reassoc]
lemma fromSpec_proj : (C.W b).fromSpec ≫ C.proj = (C.W b).proj ≫ C.ι b :=
  C.fromSpec_glue b _ _

lemma proj_fromSpec_apply (v : Spec Γ(X, (C.W b).carrier)) :
    C.proj ((C.W b).fromSpec v) = C.ι b ((C.W b).proj v) :=
  congr($(C.fromSpec_proj b) v)

/-- **The projection is invariant.** -/
lemma hom_proj : (ρ g).asIso.hom ≫ C.proj = C.proj := by
  refine C.hom_ext fun b ↦ ?_
  have h₁ : specComap Γ(X, (C.W b).carrier) G g⁻¹ ≫ (C.W b).fromSpec =
      (C.W b).fromSpec ≫ (ρ g⁻¹⁻¹).asIso.hom := (C.W b).specComap_fromSpec g⁻¹
  rw [inv_inv] at h₁
  rw [← Category.assoc, ← h₁, Category.assoc, fromSpec_proj, ← Category.assoc,
    specComap_projection]

variable (hf : ∀ g, (ρ g).asIso.hom ≫ f = f)

/-- The morphism on the invariant quotient of a chart induced by an invariant morphism. -/
noncomputable def descChart : (C.W b).Q ⟶ T :=
  descOfFinite ((C.W b).fromSpec ≫ f) (fun g ↦ C.specComap_fromSpec_comp b f g hf)

@[reassoc]
lemma proj_descChart : (C.W b).proj ≫ C.descChart b f hf = (C.W b).fromSpec ≫ f :=
  projection_descOfFinite _ _

lemma qMap_descChart : C.V.qMap (C.W b) (C.le b) ≫ C.descChart b f hf =
    C.V.qMap (C.W c) (C.le c) ≫ C.descChart c f hf := by
  refine (cancel_epi C.V.proj).mp ?_
  rw [← Category.assoc, ← Category.assoc, proj_qMap, proj_qMap, Category.assoc, Category.assoc,
    proj_descChart, proj_descChart, specMap_res_fromSpec_assoc, specMap_res_fromSpec_assoc]

/-- The morphism on the invariant quotient induced by an invariant morphism. -/
noncomputable def desc : C.quotient ⟶ T :=
  pushout.desc (C.descChart true f hf) (C.descChart false f hf) (C.qMap_descChart true false f hf)

@[reassoc]
lemma ι_desc : C.ι b ≫ C.desc f hf = C.descChart b f hf := by
  cases b
  · exact pushout.inr_desc _ _ _
  · exact pushout.inl_desc _ _ _

/-- **An invariant morphism factors through the projection.** -/
@[reassoc]
lemma proj_desc : C.proj ≫ C.desc f hf = f := by
  refine C.hom_ext fun b ↦ ?_
  rw [fromSpec_proj_assoc, ι_desc, proj_descChart]

lemma hom_ext_quotient {f₁ f₂ : C.quotient ⟶ T} (h : C.proj ≫ f₁ = C.proj ≫ f₂) : f₁ = f₂ := by
  have h₁ (b : Bool) : C.ι b ≫ f₁ = C.ι b ≫ f₂ := by
    refine (cancel_epi (C.W b).proj).mp ?_
    rw [← fromSpec_proj_assoc, ← fromSpec_proj_assoc, h]
  exact pushout.hom_ext (h₁ true) (h₁ false)

variable {b} in
lemma mem_of_proj_mem (h : C.proj x ∈ Set.range (C.ι b)) : x ∈ (C.W b).carrier := by
  rcases C.exists_mem x with ⟨c, hc⟩
  by_cases hbc : b = c
  · exact hbc ▸ hc
  rcases h with ⟨q, hq⟩
  rcases (C.W c).exists_fromSpec_eq hc with ⟨v, rfl⟩
  rw [proj_fromSpec_apply] at hq
  rcases C.exists_of_ι_eq hbc hq with ⟨w, -, hw⟩
  rcases C.V.proj_surjective w with ⟨u, rfl⟩
  rw [qMap_proj_apply, (C.W c).proj_eq_iff] at hw
  rcases hw with ⟨g, hg⟩
  have h₁ : (C.W c).fromSpec v = (ρ g⁻¹).asIso.hom (C.V.fromSpec u) := by
    rw [← C.V.specMap_res_fromSpec (C.W c) (C.le c), hg, ← Hom.comp_apply,
      specComap_fromSpec, Hom.comp_apply, Hom.comp_apply]
  rw [h₁]
  exact C.le b ((C.V.hom_apply_mem_iff g⁻¹).mpr (C.V.fromSpec_apply_mem u))

/-- **Over a chart, the projection is the projection of the chart.** -/
lemma isPullback_ι : IsPullback (C.W b).proj (C.W b).fromSpec (C.ι b) C.proj := by
  refine IsOpenImmersion.isPullback _ _ _ _ (C.fromSpec_proj b)
    (Opens.ext (Set.ext fun x ↦ ⟨fun h ↦ ?_, ?_⟩))
  · exact (C.W b).exists_fromSpec_eq (C.mem_of_proj_mem h)
  · rintro ⟨v, rfl⟩
    exact ⟨(C.W b).proj v, (C.proj_fromSpec_apply b v).symm⟩

/-- The open cover of the invariant quotient by the invariant quotients of the two charts. -/
noncomputable def quotientCover : C.quotient.OpenCover :=
  Cover.mkOfCovers Bool (fun b ↦ (C.W b).Q) C.ι C.exists_ι_eq

instance : IsIntegralHom C.proj := by
  have : IsZariskiLocalAtTarget @IsIntegralHom :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ IsIntegralHom.hasAffineProperty
  refine IsZariskiLocalAtTarget.of_openCover C.quotientCover fun b ↦ ?_
  have h₁ : IsIntegralHom ((C.isPullback_ι b).flip.isoPullback.inv ≫ (C.W b).proj) := inferInstance
  rw [(C.isPullback_ι b).flip.isoPullback_inv_snd] at h₁
  exact h₁

instance : Surjective C.proj := by
  refine ⟨fun y ↦ ?_⟩
  rcases C.exists_ι_eq y with ⟨b, q, rfl⟩
  rcases (C.W b).proj_surjective q with ⟨v, rfl⟩
  exact ⟨(C.W b).fromSpec v, C.proj_fromSpec_apply b v⟩

variable (x) in
/-- **The fibres of the projection are the orbits of the group.** -/
lemma proj_eq_iff (x' : X) : C.proj x = C.proj x' ↔ ∃ g : G, x' = (ρ g).asIso.hom x := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases C.exists_mem x with ⟨b, hb⟩
    rcases (C.W b).exists_fromSpec_eq hb with ⟨v, rfl⟩
    have hx' : x' ∈ (C.W b).carrier :=
      C.mem_of_proj_mem (h ▸ ⟨(C.W b).proj v, (C.proj_fromSpec_apply b v).symm⟩)
    rcases (C.W b).exists_fromSpec_eq hx' with ⟨v', rfl⟩
    rw [proj_fromSpec_apply, proj_fromSpec_apply] at h
    rcases ((C.W b).proj_eq_iff v v').mp ((C.ι b).isOpenEmbedding.injective h) with ⟨g, rfl⟩
    refine ⟨g⁻¹, ?_⟩
    rw [← Hom.comp_apply, specComap_fromSpec, Hom.comp_apply]
  · rintro ⟨g, rfl⟩
    rw [← Hom.comp_apply, hom_proj]

end TwoChartCover

end StableAffineOpen

end AlgebraicGeometry.Scheme
