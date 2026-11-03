import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.FiniteSetAffineOpen
import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Quotient
import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.TwoChartQuotient
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.AlgebraicGeometry.Geometrically.Integral
import TauCeti.AlgebraicGeometry.Morphisms.Separated
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension
import TauCeti.RingTheory.KrullDimension.Integral

/-!
# Existence of quotient curves

Every algebraic curve `X` over a field `K`, proper or not, regular or not, has a quotient curve
`X / H` (LMFDB `ag.quotient_curve`) by every finite subgroup `H` of its automorphism group, and the
projection `X ⟶ X / H` is surjective with the `H`-orbits as fibres. Together with the universal
property of `AlgebraicGeometry.Scheme.IsQuotientCurve`, this gives the whole knowl for all curves.

A curve has a cover by two `H`-stable affine opens: the intersection of the translates of a nonempty
affine open is a stable affine open, whose complement is a finite stable set of closed points, which
lies in an affine open by `LeanBridge.ForMathlib.AlgebraicGeometry.Curve.FiniteSetAffineOpen`, and
then in the intersection of its translates. The quotient curve is the invariant quotient of this
cover, from `LeanBridge.ForMathlib.AlgebraicGeometry.Curve.TwoChartQuotient`. It is of finite type
over `K` by the Artin--Tate lemma and of dimension one since the charts of `X` are integral over the
charts of the quotient. Separatedness descends along the surjective integral projection, and so do
geometric reducedness and irreducibility, the projection being surjective and its base changes along
field extensions scheme-theoretically dominant.

Tau Ceti's main, which is not at the pinned version, has the finiteness of invariants
(`TauCeti.FixedPoints.finiteType_subalgebra`) and the invariant quotient of a scheme affine over a
base with the group acting over that base (`CategoryTheory.CommMon.invariantSubalgebraPresheaf`). A
curve is not presented in that form: the base would have to be constructed first, and neither a
base nor the affine open subsets used here are available there.

## Main definitions

* `AlgebraicGeometry.Scheme.StableAffineOpen.ofIsAffineOpen`: the intersection of the translates of
  an affine open of a separated scheme by a finite group.
* `AlgebraicGeometry.Scheme.StableAffineOpen.TwoChartCover.toOver`: the invariant quotient of a
  two-chart cover of a scheme over `K`, as a scheme over `K`.
* `AlgebraicGeometry.Scheme.StableAffineOpen.TwoChartCover.projOver`: the projection onto it.

## Main results

* `AlgebraicGeometry.Scheme.geometricallyReduced_of_comp`: the target of a surjective morphism from
  a geometrically reduced scheme, if reduced, is geometrically reduced.
* `AlgebraicGeometry.Scheme.geometricallyIrreducible_of_comp`: the target of a surjective morphism
  from a geometrically irreducible scheme is geometrically irreducible.
* `AlgebraicGeometry.Scheme.StableAffineOpen.exists_twoChartCover`: a curve with an action of a
  finite group has a cover by two stable affine opens.
* `AlgebraicGeometry.Scheme.StableAffineOpen.TwoChartCover.isQuotientCurve_projOver`: the invariant
  quotient of a two-chart cover of an algebraic curve is a quotient curve.
* `AlgebraicGeometry.Scheme.exists_isQuotientCurve`: every algebraic curve has a quotient curve by
  every finite subgroup of its automorphism group.
* `AlgebraicGeometry.Scheme.IsQuotientCurve.surjective_left`: the projection onto a quotient curve
  is surjective.
* `AlgebraicGeometry.Scheme.IsQuotientCurve.left_apply_eq_iff`: the fibres of the projection onto a
  quotient curve are the orbits.
-/

open CategoryTheory Limits Over TopologicalSpace Opens TauCeti AlgebraicGeometry
  AffineInvariantQuotient

namespace AlgebraicGeometry.Scheme

universe u v

variable {K : Type u} [Field K]

section

variable {A : Type u} [CommRing A] {G : Type v} [Group G] [Finite G] [MulSemiringAction G A]
  (p : quotient A G ⟶ Spec (.of K)) [LocallyOfFiniteType (projection A G ≫ p)]

open Algebra in
lemma finiteType_specPreimage : (Spec.preimage p).hom.FiniteType := by
  let R : Subring A := FixedPoints.subring A G
  let ψ : CommRingCat.of K ⟶ CommRingCat.of R := Spec.preimage p
  let ψ' : CommRingCat.of K ⟶ CommRingCat.of A := ψ ≫ CommRingCat.ofHom (algebraMap R A)
  have h₁ : Spec.map ψ' = projection A G ≫ p := by
    rw [Spec.map_comp, Spec.map_preimage]
    rfl
  have h₂ : LocallyOfFiniteType (Spec.map ψ') := h₁ ▸ inferInstance
  have h₃ : ψ'.hom.FiniteType := HasRingHomProperty.Spec_iff.mp h₂
  let _ : Algebra K R := ψ.hom.toAlgebra
  let _ : Algebra K A := ψ'.hom.toAlgebra
  have : IsScalarTower K R A := .of_algebraMap_eq' rfl
  have hft : Algebra.FiniteType K A := h₃
  have : Algebra.IsIntegral R A := IsInvariant.isIntegral R A G
  have : Algebra.FiniteType R A := .of_restrictScalars_finiteType K R A
  have hfin : Module.Finite R A := IsIntegral.finite
  exact ⟨fg_of_fg_of_fg K R A hft.out hfin.fg_top Subtype.val_injective⟩

lemma locallyOfFiniteType_of_projection_comp : LocallyOfFiniteType p := by
  rw [← Spec.map_preimage p]
  exact HasRingHomProperty.Spec_iff.mpr (finiteType_specPreimage p)

variable {X Y : Scheme.{u}} (π : X ⟶ Y) [Surjective π]

lemma isReduced_of_isPullback [QuasiCompact π] [IsReduced Y] {W W' : Scheme.{u}} {f : W' ⟶ X}
    {r : W' ⟶ W} {g : W ⟶ Y} (hP : IsPullback f r π g) [Flat g] [IsReduced W'] : IsReduced W := by
  have hdom : IsSchemeTheoreticallyDominant π := .of_isDominant _
  have hr : IsSchemeTheoreticallyDominant r := .of_isPullback hP
  have hrc : QuasiCompact r := MorphismProperty.of_isPullback hP inferInstance
  exact IsSchemeTheoreticallyDominant.isReduced r

variable (q : Y ⟶ Spec (.of K))

/-- **The target of a surjective morphism from a geometrically reduced scheme, if reduced, is
geometrically reduced.** -/
lemma geometricallyReduced_of_comp [QuasiCompact π] [IsReduced Y] [GeometricallyReduced (π ≫ q)] :
    GeometricallyReduced q := by
  refine ⟨fun L _ y W fst snd h ↦ ?_⟩
  have hX : IsPullback (pullback.fst (π ≫ q) y) (pullback.snd _ y) (π ≫ q) y :=
    IsPullback.of_hasPullback _ _
  have hred : IsReduced (pullback (π ≫ q) y) :=
    GeometricallyReduced.geometrically_isReduced y _ _ (IsPullback.of_hasPullback _ _)
  have hflat : Flat fst := MorphismProperty.of_isPullback h.flip inferInstance
  exact isReduced_of_isPullback π (IsPullback.of_bot' hX h)

/-- **The target of a surjective morphism from a geometrically irreducible scheme is geometrically
irreducible.** -/
lemma geometricallyIrreducible_of_comp [GeometricallyIrreducible (π ≫ q)] :
    GeometricallyIrreducible q := by
  refine ⟨fun L _ y Z fst snd h ↦ ?_⟩
  have hW : IsPullback (pullback.fst (π ≫ q) y) (pullback.snd _ y) (π ≫ q) y :=
    IsPullback.of_hasPullback _ _
  have hirr : IrreducibleSpace ↥(pullback (π ≫ q) y) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace y _ _ (IsPullback.of_hasPullback _ _)
  exact (MorphismProperty.of_isPullback (IsPullback.of_bot' hW h)
    (inferInstance : Surjective π)).surj.irreducibleSpace (Hom.continuous _)

end

namespace StableAffineOpen

variable {X : Scheme.{u}} {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)

lemma mem_iInf_preimage {U : X.Opens} {x : X} :
    x ∈ (⨅ g, (ρ g).asIso.hom ⁻¹ᵁ U) ↔ ∀ g, (ρ g).asIso.hom x ∈ U := by
  rw [← SetLike.mem_coe, coe_iInf, Set.mem_iInter]
  rfl

/-- The stable affine open obtained by intersecting the translates of an affine open of a separated
scheme by a finite group. -/
noncomputable def ofIsAffineOpen [X.IsSeparated] {U : X.Opens} (hU : IsAffineOpen U) :
    StableAffineOpen ρ where
  carrier := ⨅ g, (ρ g).asIso.hom ⁻¹ᵁ U
  isAffineOpen := IsAffineOpen.iInf fun _ ↦ hU.preimage_of_isIso _
  preimage_eq g := by
    refine Opens.ext (Set.ext fun x ↦ ?_)
    have h₁ :
        (∀ h : G, (ρ h).asIso.hom ((ρ g).asIso.hom x) ∈ U) ↔ ∀ h : G, (ρ h).asIso.hom x ∈ U := by
      refine ⟨fun h₂ h ↦ ?_, fun h₂ h ↦ ?_⟩
      · have h₃ : (ρ (h * g⁻¹)).asIso.hom ((ρ g).asIso.hom x) ∈ U := h₂ (h * g⁻¹)
        rwa [← hom_mul_apply, inv_mul_cancel_right] at h₃
      · rw [← hom_mul_apply]
        exact h₂ _
    exact (mem_iInf_preimage ρ).trans (h₁.trans (mem_iInf_preimage ρ).symm)

variable (K) in
/-- **A curve with an action of a finite group has a cover by two stable affine opens.** -/
lemma exists_twoChartCover [X.Over (Spec (.of K))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [CompactSpace X] [IsSeparated (X ↘ Spec (.of K))]
    (hX : topologicalKrullDim X = 1) : ∃ C : TwoChartCover ρ, Nonempty (C.W true).carrier := by
  rcases X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X))
    isOpen_univ with ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have : IsNoetherian X := {}
  have : X.IsSeparated := .of_isSeparated (X ↘ Spec (.of K))
  let W₁ : StableAffineOpen ρ := ofIsAffineOpen ρ hU
  have hη : genericPoint X ∈ W₁.carrier := (mem_iInf_preimage ρ).mpr fun g ↦ by
    rw [genericPoint_eq_of_isOpenImmersion]
    exact hηU
  have hT : ((W₁.carrier : Set X)ᶜ).Finite :=
    finite_of_isClosed_of_genericPoint_notMem hX W₁.carrier.isOpen.isClosed_compl (not_not.mpr hη)
  rcases exists_isAffineOpen_forall_mem K hX hT (not_not.mpr hη) with ⟨U₂, hU₂, hTU₂⟩
  let W₂ : StableAffineOpen ρ := ofIsAffineOpen ρ hU₂
  have hT₂ : (W₁.carrier : Set X)ᶜ ⊆ W₂.carrier := fun x hx ↦
    (mem_iInf_preimage ρ).mpr fun g ↦ hTU₂ fun h₁ ↦ hx ((W₁.hom_apply_mem_iff g).mp h₁)
  refine ⟨⟨fun b ↦ bif b then W₁ else W₂, W₁.inf W₂, rfl, ?_⟩, ⟨⟨_, hη⟩⟩⟩
  refine top_le_iff.mp fun x _ ↦ ?_
  by_cases hx : x ∈ W₁.carrier
  · exact mem_sup.mpr (Or.inl hx)
  · exact mem_sup.mpr (Or.inr (hT₂ hx))

namespace TwoChartCover

variable {ρ} (C : TwoChartCover ρ)

instance [IsReduced X] : IsReduced C.quotient := by
  refine @isReduced_of_isReduced_stalk _ fun p ↦ ?_
  rcases C.exists_ι_eq p with ⟨b, q, rfl⟩
  have : IsReduced (C.W b).Q :=
    (affine_isReduced_iff _).mpr (isReduced_of_injective
      (FixedPoints.subring Γ(X, (C.W b).carrier) G).subtype Subtype.val_injective)
  exact isReduced_of_injective _ (asIso ((C.ι b).stalkMap q)).commRingCatIsoToRingEquiv.injective

instance [IsIntegral X] : IsIntegral C.quotient :=
  have : IrreducibleSpace C.quotient := C.proj.surjective.irreducibleSpace C.proj.continuous
  isIntegral_of_irreducibleSpace_of_isReduced _

variable (q : C.quotient ⟶ Spec (.of K)) [LocallyOfFiniteType (C.proj ≫ q)] (b : Bool)

lemma locallyOfFiniteType_proj_comp : LocallyOfFiniteType ((C.W b).proj ≫ C.ι b ≫ q) := by
  rw [← C.fromSpec_proj_assoc]
  infer_instance

lemma locallyOfFiniteType_ι_comp : LocallyOfFiniteType (C.ι b ≫ q) := by
  have h₁ : LocallyOfFiniteType ((C.W b).proj ≫ C.ι b ≫ q) := C.locallyOfFiniteType_proj_comp q b
  exact locallyOfFiniteType_of_projection_comp (C.ι b ≫ q)

lemma locallyOfFiniteType_of_proj_comp : LocallyOfFiniteType q := by
  have : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  exact IsZariskiLocalAtSource.of_openCover C.quotientCover (C.locallyOfFiniteType_ι_comp q)

open Algebra in
lemma topologicalKrullDim_quotient [IsIntegral X] (p : C.quotient ⟶ Spec (.of K))
    [LocallyOfFiniteType (C.proj ≫ p)] (hne : Nonempty (C.W true).carrier) :
    topologicalKrullDim C.quotient = topologicalKrullDim X := by
  have : LocallyOfFiniteType p := C.locallyOfFiniteType_of_proj_comp p
  rcases hne with ⟨x⟩
  have : Nonempty (C.W true).carrier := ⟨x⟩
  rcases (C.W true).exists_fromSpec_eq x.2 with ⟨v, -⟩
  have : Nonempty (Spec Γ(X, (C.W true).carrier)) := ⟨v⟩
  have : Nonempty (C.W true).Q := ⟨(C.W true).proj v⟩
  have h₁ : topologicalKrullDim (C.W true).Q = topologicalKrullDim C.quotient :=
    topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType p (C.ι true).isOpenEmbedding
  have h₂ : topologicalKrullDim (Spec Γ(X, (C.W true).carrier)) = topologicalKrullDim X :=
    topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType (C.proj ≫ p)
      (C.W true).fromSpec.isOpenEmbedding
  rw [← h₁, ← h₂]
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans
    (Eq.trans ?_ (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm)
  have : Algebra.IsIntegral (FixedPoints.subring Γ(X, (C.W true).carrier) G)
      Γ(X, (C.W true).carrier) := IsInvariant.isIntegral _ _ G
  have : FaithfulSMul (FixedPoints.subring Γ(X, (C.W true).carrier) G) Γ(X, (C.W true).carrier) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  exact ringKrullDim_eq_of_isIntegral_of_faithfulSMul.symm

end TwoChartCover

end StableAffineOpen

variable {X : Over (Spec (.of K))} {H : Subgroup (Aut X)}

variable (H) in
/-- The action of a group of automorphisms of a scheme over `K` on the underlying scheme. -/
noncomputable def schemeAction : H →* Aut X.left :=
  ((Over.forget _).mapAut X).comp H.subtype

namespace StableAffineOpen.TwoChartCover

variable [Finite H] (C : TwoChartCover (schemeAction H))

/-- The structure morphism of the invariant quotient of a two-chart cover of a scheme over `K`. -/
noncomputable def structureHom : C.quotient ⟶ Spec (.of K) :=
  C.desc X.hom fun h ↦ Over.w (h : Aut X).asIso.hom

lemma proj_structureHom : C.proj ≫ C.structureHom = X.hom :=
  C.proj_desc _ _

/-- The invariant quotient of a two-chart cover, as a scheme over `K`. -/
noncomputable def toOver : Over (Spec (.of K)) :=
  Over.mk C.structureHom

/-- The projection onto the invariant quotient of a two-chart cover, over `K`. -/
noncomputable def projOver : X ⟶ C.toOver :=
  Over.homMk C.proj C.proj_structureHom

lemma desc_comp_hom {Z : Over (Spec (.of K))} (f : X ⟶ Z)
    (hf : ∀ h : H, (schemeAction H h).asIso.hom ≫ f.left = f.left) :
    C.desc f.left hf ≫ Z.hom = C.structureHom := by
  refine C.hom_ext_quotient ?_
  rw [proj_desc_assoc, C.proj_structureHom]
  exact Over.w f

variable [X.left.IsAlgebraicCurveOver K]

lemma isAlgebraicCurveOver_toOver (hne : Nonempty (C.W true).carrier) :
    C.toOver.left.IsAlgebraicCurveOver K := by
  have hX : IsIntegral X.left := IsVarietyOver.isIntegral K
  have hcomp : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace (X.left ↘ Spec (.of K))
  have hq : CompactSpace C.quotient := C.proj.surjective.compactSpace C.proj.continuous
  have hp : X.left ↘ Spec (.of K) = C.proj ≫ C.structureHom := C.proj_structureHom.symm
  have hsep : IsSeparated (C.proj ≫ C.structureHom) :=
    hp ▸ inferInstanceAs (IsSeparated (X.left ↘ Spec (.of K)))
  have hlft : LocallyOfFiniteType (C.proj ≫ C.structureHom) :=
    hp ▸ inferInstanceAs (LocallyOfFiniteType (X.left ↘ Spec (.of K)))
  have hgr : GeometricallyReduced (C.proj ≫ C.structureHom) :=
    hp ▸ inferInstanceAs (GeometricallyReduced (X.left ↘ Spec (.of K)))
  have hgi : GeometricallyIrreducible (C.proj ≫ C.structureHom) :=
    hp ▸ inferInstanceAs (GeometricallyIrreducible (X.left ↘ Spec (.of K)))
  have hr : GeometricallyReduced C.structureHom := geometricallyReduced_of_comp C.proj _
  have hi : GeometricallyIrreducible C.structureHom := geometricallyIrreducible_of_comp C.proj _
  have hs : IsSeparated C.structureHom := isSeparated_of_comp_of_surjective C.proj _
  have hl : LocallyOfFiniteType C.structureHom := C.locallyOfFiniteType_of_proj_comp _
  have : IsLocallyNoetherian C.quotient := LocallyOfFiniteType.isLocallyNoetherian C.structureHom
  have : IsNoetherian C.quotient := {}
  have hc : QuasiCompact C.structureHom := inferInstance
  have hg : GeometricallyIntegral C.structureHom :=
    .of_geometricallyReduced_of_geometricallyIrreducible _
  have hv : C.toOver.left.IsVarietyOver K :=
    { toGeometricallyIntegral := hg
      toIsSeparated := hs
      toLocallyOfFiniteType := hl
      toQuasiCompact := hc }
  exact { toIsVarietyOver := hv
          topologicalKrullDim_eq_one := (C.topologicalKrullDim_quotient C.structureHom hne).trans
            (IsAlgebraicCurveOver.topologicalKrullDim_eq_one K) }

/-- **The invariant quotient of a two-chart cover of an algebraic curve is a quotient curve.** -/
lemma isQuotientCurve_projOver (hne : Nonempty (C.W true).carrier) :
    IsQuotientCurve H C.projOver where
  isAlgebraicCurveOver_left := inferInstance
  finite := inferInstance
  isAlgebraicCurveOver_right := C.isAlgebraicCurveOver_toOver hne
  hom_comp h hh := OverMorphism.ext (C.hom_proj ⟨h, hh⟩)
  existsUnique_comp_eq Z f hf := by
    have hf' (h : H) : (schemeAction H h).asIso.hom ≫ f.left = f.left :=
      congrArg (fun k ↦ k.left) (hf h h.2)
    refine ⟨Over.homMk (C.desc f.left hf') (C.desc_comp_hom f hf'),
      OverMorphism.ext (C.proj_desc _ _), fun g hg ↦ OverMorphism.ext (C.hom_ext_quotient ?_)⟩
    exact (congrArg (fun k ↦ k.left) hg).trans (C.proj_desc f.left hf').symm

end StableAffineOpen.TwoChartCover

lemma exists_twoChartCover_schemeAction [Finite H] [X.left.IsAlgebraicCurveOver K] :
    ∃ C : StableAffineOpen.TwoChartCover (schemeAction H), Nonempty (C.W true).carrier := by
  have hX : IsIntegral X.left := IsVarietyOver.isIntegral K
  have hcomp : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace (X.left ↘ Spec (.of K))
  exact StableAffineOpen.exists_twoChartCover K (schemeAction H)
    (IsAlgebraicCurveOver.topologicalKrullDim_eq_one K)

variable (H) in
/-- **Existence of quotient curves** (LMFDB `ag.quotient_curve`): every algebraic curve over `K` has
a quotient curve by every finite subgroup of its automorphism group. -/
lemma exists_isQuotientCurve [Finite H] [X.left.IsAlgebraicCurveOver K] :
    ∃ (Y : Over (Spec (.of K))) (π : X ⟶ Y), IsQuotientCurve H π := by
  rcases exists_twoChartCover_schemeAction (H := H) with ⟨C, hne⟩
  exact ⟨_, _, C.isQuotientCurve_projOver hne⟩

namespace IsQuotientCurve

variable {Y : Over (Spec (.of K))} {π : X ⟶ Y}

/-- **The projection onto a quotient curve is surjective** (LMFDB `ag.quotient_curve`). -/
lemma surjective_left (hπ : IsQuotientCurve H π) : Surjective π.left := by
  have : Finite H := hπ.finite
  have : X.left.IsAlgebraicCurveOver K := hπ.isAlgebraicCurveOver_left
  rcases exists_twoChartCover_schemeAction (H := H) with ⟨C, hne⟩
  rw [← (C.isQuotientCurve_projOver hne).comp_uniqueUpToIso_hom hπ, Over.comp_left]
  have : Surjective C.projOver.left := inferInstanceAs (Surjective C.proj)
  infer_instance

/-- **The fibres of the projection onto a quotient curve are the orbits** (LMFDB
`ag.quotient_curve`): the quotient curve identifies the points of each orbit, and no others. -/
lemma left_apply_eq_iff (hπ : IsQuotientCurve H π) {x y : X.left} :
    π.left x = π.left y ↔ ∃ σ ∈ H, σ.asIso.hom.left x = y := by
  have : Finite H := hπ.finite
  have : X.left.IsAlgebraicCurveOver K := hπ.isAlgebraicCurveOver_left
  rcases exists_twoChartCover_schemeAction (H := H) with ⟨C, hne⟩
  have h₀ : IsQuotientCurve H C.projOver := C.isQuotientCurve_projOver hne
  let e : C.toOver ≅ Y := h₀.uniqueUpToIso hπ
  have he (z : X.left) : π.left z = e.hom.left (C.proj z) :=
    (congrArg (fun g ↦ g.left z) (h₀.comp_uniqueUpToIso_hom hπ)).symm
  rw [he, he]
  refine (e.hom.left.isOpenEmbedding.injective.eq_iff.trans (C.proj_eq_iff x y)).trans
    ⟨fun ⟨g, hg⟩ ↦ ⟨g, g.2, hg.symm⟩, fun ⟨σ, hσ, h⟩ ↦ ⟨⟨σ, hσ⟩, h.symm⟩⟩

end IsQuotientCurve

end AlgebraicGeometry.Scheme
