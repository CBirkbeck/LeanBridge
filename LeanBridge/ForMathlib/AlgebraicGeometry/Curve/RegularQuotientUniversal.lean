import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.RegularQuotient
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# The universal property of the quotient of a regular proper curve among all schemes

Let `X` be a regular proper curve over a field `k`, such as a smooth projective curve, and `H` a
finite group of automorphisms of `X`, with quotient curve `π : X ⟶ X / H` (LMFDB
`ag.quotient_curve`), the regular proper curve whose function field is `k(X)^H`
(`TauCeti.AlgebraicGeometry.RegularProperCurveCat.quotient`). This file shows that `π` is a
categorical quotient in the category of all schemes: every morphism of schemes `f : X ⟶ Z`
invariant under `H`, to an arbitrary scheme `Z`, factors uniquely through `π`, and the
factorization is a morphism over `k` when `f` is. This is the universal property by which
`AlgebraicGeometry.Scheme.IsQuotientCurve` characterizes the quotient curve (D. Mumford, *Abelian
Varieties*, §7, Theorem 1, for quotients by finite groups).

The morphism `g : X / H ⟶ Z` is built directly as a morphism of locally ringed spaces.
* On points, `π` is a topological quotient map, being closed and surjective, and `f` is constant on
  its fibres, which are the `H`-orbits; so `f` descends to a continuous map `g`, with
  `π⁻¹ (g⁻¹ O) = f⁻¹ O` for every open `O` of `Z`.
* On sections, the pullback `f^* s` of a section `s` of `𝒪_Z` over `O` is invariant under `H`, so
  its germ lies in `k(X)^H`; as `𝒪_{X/H} = (π_* 𝒪_X)^H`, it is the pullback along `π` of a unique
  section of `𝒪_{X/H}` over `g⁻¹ O`, which is `g^* s`.
* The stalk maps of `g` are local because those of `f` are: the stalk map of `f` at `x` is that of
  `g` at `π x` followed by that of `π` at `x`.

Uniqueness holds because `π` is an epimorphism of schemes.

The quotient of a geometrically reduced curve is geometrically reduced, over any field `k`: after a
base change along `Spec L ⟶ Spec k`, the base change of `π` is scheme-theoretically dominant, since
`π` is dominant and quasi-compact with a reduced target and `Spec L ⟶ Spec k` is flat, so the base
change of `X / H` is reduced because that of `X` is. With the geometric irreducibility of the
quotient of a geometrically irreducible curve
(`TauCeti.AlgebraicGeometry.RegularProperCurveCat.geometricallyIrreducible_quotient`), the
quotient of a geometrically integral curve is geometrically integral.

## Main definitions

* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.descBase`: the continuous map `X / H → Z`
  induced by a morphism `f : X ⟶ Z` invariant under `H`.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.descApp`: its maps on sections.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.descC`: its morphism of structure presheaves.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.desc` (LMFDB `ag.quotient_curve`): the morphism
  of schemes `X / H ⟶ Z` through which `f` factors.

## Main results

* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.isQuotientMap_toQuotient`: the projection
  `X ⟶ X / H` is a topological quotient map.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.toQuotient_comp_desc`: a morphism invariant
  under `H` factors through the projection.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.eq_desc_iff`: the factorization is unique.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.desc_comp_over`: the factorization of a
  morphism over `k` is a morphism over `k`.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.geometricallyReduced_quotient`: the quotient of
  a geometrically reduced curve is geometrically reduced.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.geometricallyIntegral_quotient`: the quotient of
  a geometrically integral curve is geometrically integral.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme IntermediateField TopCat Presheaf
  Topology TopologicalSpace

namespace TauCeti.AlgebraicGeometry.RegularProperCurveCat

universe u

variable {k : Type u} [Field k] {X : RegularProperCurveCat k} {H : Subgroup (Aut X)}
  {Z : Scheme.{u}} {f : X.toScheme ⟶ Z} (O : Z.Opens) (s : Γ(Z, O))

lemma germToFunctionField_appLE_mem_fixedField (hf : ∀ σ ∈ H, σ.asIso.hom.hom ≫ f = f)
    (V : X.toScheme.Opens) [Nonempty V] (e : V ≤ f ⁻¹ᵁ O) :
    X.toScheme.germToFunctionField V (f.appLE O V e s) ∈ fixedField (functionFieldSubgroup H) := by
  rw [mem_fixedField_iff]
  rintro _ ⟨σ, hσ, rfl⟩
  have hne : Nonempty (f ⁻¹ᵁ O) := ⟨⟨_, e (Classical.arbitrary V).2⟩⟩
  have hσf : σ.asIso.inv.hom ≫ f = f := hf σ⁻¹ (inv_mem hσ)
  have hgerm : X.toScheme.germToFunctionField V (f.appLE O V e s) =
      X.toScheme.germToFunctionField (f ⁻¹ᵁ O) (f.app O s) := by
    rw [Hom.appLE, CommRingCat.comp_apply]
    exact germ_res_apply _ _ _ _ _
  rw [hgerm, autToAlgEquiv_apply, Hom.functionFieldAlgHom_apply, ← CommRingCat.comp_apply,
    Hom.germToFunctionField_functionFieldMap, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply (f.app O), ← Hom.comp_app, Hom.congr_app hσf]
  exact germ_res_apply _ _ _ _ _

variable [Finite H] (U : (quotient H).toScheme.Opens)

instance : UniversallyClosed (toQuotient H).hom := by
  have hcomp : UniversallyClosed ((toQuotient H).hom ≫ (quotient H).toScheme ↘ Spec (.of k)) := by
    rw [comp_over]
    infer_instance
  exact .of_comp_of_isSeparated _ ((quotient H).toScheme ↘ Spec (.of k))

variable (H) in
/-- **The projection onto the quotient curve is a topological quotient map**: it is surjective, and
closed because `X` is proper and `X / H` is separated over `k`. -/
lemma isQuotientMap_toQuotient : IsQuotientMap (toQuotient H).hom :=
  (toQuotient H).hom.isClosedMap.isQuotientMap (toQuotient H).hom.continuous
    (surjective_toQuotient H).surj

variable (H) in
lemma injective_app_toQuotient : Function.Injective ((toQuotient H).hom.app U) := by
  rcases isEmpty_or_nonempty U with hU | hU
  · have hbot : U = ⊥ := eq_bot_iff.mpr fun x hx ↦ (hU.false ⟨x, hx⟩).elim
    subst hbot
    exact Function.injective_of_subsingleton _
  · exact app_toQuotient_injective U

lemma apply_eq_of_toQuotient_apply_eq (hf : ∀ σ ∈ H, σ.asIso.hom.hom ≫ f = f) {x y : X.toScheme}
    (h : (toQuotient H).hom x = (toQuotient H).hom y) : f x = f y := by
  rcases toQuotient_apply_eq_iff.mp h with ⟨σ, hσ, rfl⟩
  rw [← Hom.comp_apply, hf σ hσ]

lemma appLE_mem_range_app_toQuotient (hf : ∀ σ ∈ H, σ.asIso.hom.hom ≫ f = f)
    (e : (toQuotient H).hom ⁻¹ᵁ U ≤ f ⁻¹ᵁ O) :
    f.appLE O _ e s ∈ ((toQuotient H).hom.app U).hom.range := by
  rcases isEmpty_or_nonempty U with hU | hU
  · have hbot : U = ⊥ := eq_bot_iff.mpr fun x hx ↦ (hU.false ⟨x, hx⟩).elim
    subst hbot
    have hsub : Subsingleton Γ(X.toScheme, (toQuotient H).hom ⁻¹ᵁ ⊥) :=
      inferInstanceAs (Subsingleton Γ(X.toScheme, ⊥))
    exact ⟨0, Subsingleton.elim _ _⟩
  have hmem : X.toScheme.germToFunctionField _ (f.appLE O _ e s) ∈
      Set.range (X.toScheme.germToFunctionField ((toQuotient H).hom ⁻¹ᵁ U)) ∩
        fixedField (functionFieldSubgroup H) :=
    ⟨⟨_, rfl⟩, germToFunctionField_appLE_mem_fixedField O s hf _ e⟩
  rw [← range_germToFunctionField_quotient] at hmem
  rcases hmem with ⟨t, ht⟩
  refine ⟨t, X.toScheme.germToFunctionField_injective _ ?_⟩
  rw [← ht]
  exact (functionFieldAlgHom_toQuotient_germToFunctionField U t).symm

lemma isReduced_of_isPullback_toQuotient {W W' : Scheme.{u}} {p : W' ⟶ X.toScheme} {q : W' ⟶ W}
    {g : W ⟶ (quotient H).toScheme} (hP : IsPullback p q (toQuotient H).hom g) [Flat g]
    [IsReduced W'] : IsReduced W := by
  have hdom : IsSchemeTheoreticallyDominant (toQuotient H).hom := .of_isDominant _
  have hq : IsSchemeTheoreticallyDominant q := .of_isPullback hP
  have hqc : QuasiCompact q := MorphismProperty.of_isPullback hP inferInstance
  exact IsSchemeTheoreticallyDominant.isReduced q

variable (H) in
/-- **The quotient of a geometrically reduced curve is geometrically reduced**, over any field `k`:
after a base change along `Spec L ⟶ Spec k`, the base change of the projection `X ⟶ X / H` is
scheme-theoretically dominant, as `Spec L ⟶ Spec k` is flat, so the base change of `X / H` is
reduced because that of `X` is. -/
lemma geometricallyReduced_quotient [GeometricallyReduced (X.toScheme ↘ Spec (.of k))] :
    GeometricallyReduced ((quotient H).toScheme ↘ Spec (.of k)) := by
  refine ⟨fun L _ y W fst snd h ↦ ?_⟩
  have hX : IsPullback (pullback.fst (X.toScheme ↘ Spec (.of k)) y) (pullback.snd _ y)
      ((toQuotient H).hom ≫ (quotient H).toScheme ↘ Spec (.of k)) y := by
    rw [comp_over]
    exact IsPullback.of_hasPullback _ _
  have hred : IsReduced (pullback (X.toScheme ↘ Spec (.of k)) y) :=
    GeometricallyReduced.geometrically_isReduced y _ _ (IsPullback.of_hasPullback _ _)
  have hflat : Flat fst := MorphismProperty.of_isPullback h.flip inferInstance
  exact isReduced_of_isPullback_toQuotient (IsPullback.of_bot' hX h)

variable (H) in
/-- **The quotient of a geometrically integral curve is geometrically integral**: it is
geometrically reduced (`geometricallyReduced_quotient`) and geometrically irreducible. -/
lemma geometricallyIntegral_quotient [GeometricallyIntegral (X.toScheme ↘ Spec (.of k))] :
    GeometricallyIntegral ((quotient H).toScheme ↘ Spec (.of k)) := by
  have hred : GeometricallyReduced ((quotient H).toScheme ↘ Spec (.of k)) :=
    geometricallyReduced_quotient H
  have hirr : GeometricallyIrreducible ((quotient H).toScheme ↘ Spec (.of k)) :=
    geometricallyIrreducible_quotient H
  exact .of_geometricallyReduced_of_geometricallyIrreducible _

variable (hf : ∀ σ ∈ H, σ.asIso.hom.hom ≫ f = f)

/-- The **continuous map `X / H → Z` induced by a morphism `f : X ⟶ Z` invariant under `H`**, along
the topological quotient map `X → X / H`: the map on points of the factorization of `f` through
the quotient curve (LMFDB `ag.quotient_curve`). -/
noncomputable def descBase : (quotient H).toScheme.carrier ⟶ Z.carrier :=
  TopCat.ofHom <| (isQuotientMap_toQuotient H).lift f.base.hom fun _ _ ↦
    apply_eq_of_toQuotient_apply_eq hf

lemma descBase_apply (x : X.toScheme) : descBase hf ((toQuotient H).hom x) = f x :=
  DFunLike.congr_fun ((isQuotientMap_toQuotient H).lift_comp f.base.hom fun _ _ ↦
    apply_eq_of_toQuotient_apply_eq hf) x

lemma preimage_descBase : (toQuotient H).hom ⁻¹ᵁ (Opens.map (descBase hf)).obj O = f ⁻¹ᵁ O :=
  Opens.ext <| Set.ext fun x ↦ iff_of_eq <| congrArg (· ∈ O) (descBase_apply hf x)

/-- The **map on sections `Γ(Z, O) → Γ(X / H, g⁻¹ O)`** of the morphism `g : X / H ⟶ Z` induced by
a morphism `f : X ⟶ Z` invariant under `H`, for the quotient curve (LMFDB `ag.quotient_curve`):
the pullback `f^* s` of a section over `O` is a section over `π⁻¹ g⁻¹ O = f⁻¹ O` invariant under
`H`, so it is the pullback along the projection `π : X ⟶ X / H` of a unique section over
`g⁻¹ O`. -/
noncomputable def descApp : Γ(Z, O) ⟶ Γ((quotient H).toScheme, (Opens.map (descBase hf)).obj O) :=
  CommRingCat.ofHom <| (RingEquiv.ofLeftInverse (Function.leftInverse_invFun
    (injective_app_toQuotient H _))).symm.toRingHom.comp <|
    (f.appLE O _ (preimage_descBase O hf).le).hom.codRestrict _ fun t ↦
      appLE_mem_range_app_toQuotient O t _ hf (preimage_descBase O hf).le

lemma app_descApp :
    (toQuotient H).hom.app _ (descApp O hf s) = f.appLE O _ (preimage_descBase O hf).le s :=
  congrArg Subtype.val <| (RingEquiv.ofLeftInverse <| Function.leftInverse_invFun <|
    injective_app_toQuotient H _).apply_symm_apply
      ⟨_, appLE_mem_range_app_toQuotient O s _ hf (preimage_descBase O hf).le⟩

/-- The **morphism of structure presheaves `𝒪_Z → g_* 𝒪_{X / H}`** of the morphism `g : X / H ⟶ Z`
induced by a morphism `f : X ⟶ Z` invariant under `H`, for the quotient curve (LMFDB
`ag.quotient_curve`), made of the maps `descApp` on sections. -/
noncomputable def descC : Z.presheaf ⟶ (descBase hf) _* (quotient H).toScheme.presheaf where
  app W := descApp W.unop hf
  naturality W W' i := by
    ext t
    refine injective_app_toQuotient H _ ?_
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, app_descApp, ← CommRingCat.comp_apply,
      Hom.map_appLE, pushforward_obj_map, ← CommRingCat.comp_apply, Hom.naturality,
      CommRingCat.comp_apply, app_descApp, ← CommRingCat.comp_apply, Hom.appLE_map]

lemma descC_app : (descC hf).app (op O) = descApp O hf :=
  rfl

/-- The **morphism out of the quotient curve** `g : X / H ⟶ Z` (LMFDB `ag.quotient_curve`) through
which a morphism of schemes `f : X ⟶ Z` invariant under `H` factors, to an arbitrary scheme `Z`:
the morphism of locally ringed spaces with underlying continuous map `descBase` and morphism of
structure presheaves `descC`. Its stalk maps are local because those of `f` are. -/
noncomputable def desc : (quotient H).toScheme ⟶ Z where
  base := descBase hf
  c := descC hf
  prop y := by
    rcases (surjective_toQuotient H).surj y with ⟨x, rfl⟩
    refine ⟨fun a ha ↦ ?_⟩
    rcases Z.presheaf.exists_germ_eq a with ⟨W, hW, t, rfl⟩
    have hfx : f x ∈ W := descBase_apply hf x ▸ hW
    have hπx : (toQuotient H).hom x ∈ (Opens.map (descBase hf)).obj W := hW
    have heq : (toQuotient H).hom.stalkMap x ((quotient H).toScheme.presheaf.germ
        ((Opens.map (descBase hf)).obj W) ((toQuotient H).hom x) hπx (descApp W hf t)) =
          f.stalkMap x (Z.presheaf.germ W (f x) hfx t) := by
      rw [Hom.germ_stalkMap_apply, Hom.germ_stalkMap_apply, app_descApp, Hom.appLE,
        CommRingCat.comp_apply]
      exact germ_res_apply _ _ _ _ _
    rw [PresheafedSpace.stalkMap_germ_apply, descC_app] at ha
    have hu : IsUnit (Z.presheaf.germ W (f x) hfx t) :=
      (isUnit_map_iff (f.stalkMap x).hom _).mp (heq ▸ ha.map ((toQuotient H).hom.stalkMap x).hom)
    have key : ∀ z (hz : z ∈ W), z = f x → IsUnit (Z.presheaf.germ W z hz t) := by
      rintro z hz rfl
      exact hu
    exact key _ hW (descBase_apply hf x)

lemma preimage_toQuotient_comp_desc : ((toQuotient H).hom ≫ desc hf) ⁻¹ᵁ O = f ⁻¹ᵁ O :=
  preimage_descBase O hf

lemma toQuotient_comp_desc_app_apply : ((toQuotient H).hom ≫ desc hf).app O s =
    f.appLE O (((toQuotient H).hom ≫ desc hf) ⁻¹ᵁ O) (preimage_toQuotient_comp_desc O hf).le s :=
  app_descApp O s hf

/-- **A morphism invariant under `H` factors through the quotient curve**: if `f : X ⟶ Z` is a
morphism of schemes with `σ ≫ f = f` for every `σ ∈ H`, then `π ≫ desc hf = f` for the
projection `π : X ⟶ X / H`. -/
lemma toQuotient_comp_desc : (toQuotient H).hom ≫ desc hf = f := by
  have hbase : ((toQuotient H).hom ≫ desc hf).base = f.base := TopCat.ext (descBase_apply hf)
  refine ((toQuotient H).hom ≫ desc hf).ext hbase fun W ↦ ?_
  ext t
  rw [CommRingCat.comp_apply, toQuotient_comp_desc_app_apply, ← CommRingCat.comp_apply,
    Hom.appLE_map, Hom.appLE_eq_app]

/-- **The factorization through the quotient curve is unique**: a morphism `g : X / H ⟶ Z` is
`desc hf` exactly when `π ≫ g = f`, since the projection `π` is an epimorphism of schemes. -/
lemma eq_desc_iff {g : (quotient H).toScheme ⟶ Z} : g = desc hf ↔ (toQuotient H).hom ≫ g = f := by
  have hπ : Epi (toQuotient H).hom := epi_toQuotient H
  rw [← cancel_epi (toQuotient H).hom, toQuotient_comp_desc]

variable [Z.Over (Spec (.of k))] [f.IsOver (Spec (.of k))]

/-- **The factorization of a morphism over `k` through the quotient curve is a morphism over
`k`.** -/
lemma desc_comp_over : desc hf ≫ Z ↘ Spec (.of k) = (quotient H).toScheme ↘ Spec (.of k) :=
  (epi_toQuotient H).left_cancellation _ _ <| by
    rw [← Category.assoc, toQuotient_comp_desc, comp_over, comp_over]

instance : (desc hf).IsOver (Spec (.of k)) :=
  ⟨desc_comp_over hf⟩

end TauCeti.AlgebraicGeometry.RegularProperCurveCat
