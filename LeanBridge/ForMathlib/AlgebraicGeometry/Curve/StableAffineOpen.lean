import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.UniversalProperty

/-!
# Invariant quotients of stable affine opens

Let a group `G` act on a scheme `X`. An affine open subset `W` of `X` stable under the action has
the invariant quotient `Spec Γ(X, W)ᴳ`, Tau Ceti's `TauCeti.AffineInvariantQuotient.quotient`. For
a finite group, an inclusion `V ≤ W` of stable affine opens induces an open immersion
`Spec Γ(X, V)ᴳ ⟶ Spec Γ(X, W)ᴳ`, even though `V` need not be a basic open subset of `W`, so that the
invariant quotients of a stable affine cover can be glued. This is the local input of the quotient
curve (LMFDB `ag.quotient_curve`).

The orbits of `G` on `W` are the fibres of the projection `Spec Γ(X, W) ⟶ Spec Γ(X, W)ᴳ`, which is
a closed map, and `G` acts on `Γ(X, W)` by `g • a = a ∘ g⁻¹`. Around a point of `Spec Γ(X, V)ᴳ`,
there is a basic open subset `D(r)` of `W` inside `V` for an invariant section `r`, by these two
facts, and `Spec Γ(X, D(r))ᴳ` is a basic open subset of both `Spec Γ(X, V)ᴳ` and `Spec Γ(X, W)ᴳ`, as
taking invariants commutes with localisation (Tau Ceti's `TauCeti.FixedPoints.isLocalization`).

## Main definitions

* `AlgebraicGeometry.Scheme.StableAffineOpen`: an affine open subset stable under a group action.
* `AlgebraicGeometry.Scheme.StableAffineOpen.Q`: its invariant quotient `Spec Γ(X, W)ᴳ`.
* `AlgebraicGeometry.Scheme.StableAffineOpen.qMap`: the morphism of invariant quotients induced by
  an inclusion of stable affine opens.
* `AlgebraicGeometry.Scheme.StableAffineOpen.basicOpen`: the basic open subset of an invariant
  section.
* `AlgebraicGeometry.Scheme.StableAffineOpen.inf`: the intersection of two stable affine opens of a
  separated scheme.

## Main results

* `AlgebraicGeometry.Scheme.StableAffineOpen.isLocalization_away_fixedPoints`: invariants commute
  with localisation away from an invariant element. Tau Ceti's main has the more general
  `TauCeti.FixedPoints.isLocalization_of_mem_range_iff`, which is not at the pinned version.
* The instance `IsOpenImmersion (V.qMap W h)`: the morphism of invariant quotients induced by an
  inclusion of stable affine opens is an open immersion.
-/

open CategoryTheory AlgebraicGeometry TauCeti AffineInvariantQuotient

namespace AlgebraicGeometry.Scheme

universe u v

variable {X : Scheme.{u}} {G : Type v} [Group G] (ρ : G →* Aut X)

lemma hom_mul_apply (g h : G) (x : X) :
    (ρ (g * h)).asIso.hom x = (ρ g).asIso.hom ((ρ h).asIso.hom x) := by
  rw [map_mul]
  exact Hom.comp_apply _ _ _

/-- An affine open subset of a scheme `X` stable under an action `ρ` of a group `G` on `X`. -/
structure StableAffineOpen where
  /-- The underlying open subset. -/
  carrier : X.Opens
  /-- The open subset is affine. -/
  isAffineOpen : IsAffineOpen carrier
  /-- The open subset is stable under the action. -/
  preimage_eq (g : G) : (ρ g).asIso.hom ⁻¹ᵁ carrier = carrier

namespace StableAffineOpen

variable {ρ} (V W : StableAffineOpen ρ) (g : G)

lemma hom_mul_inv (h : G) : (ρ (g * h)⁻¹).asIso.hom = (ρ g⁻¹).asIso.hom ≫ (ρ h⁻¹).asIso.hom := by
  rw [mul_inv_rev, map_mul]
  rfl

lemma hom_one_inv : (ρ (1 : G)⁻¹).asIso.hom = 𝟙 X := by
  rw [inv_one, map_one]
  rfl

/-- The action of `G` on the sections over a stable affine open `W`: `g • a = a ∘ g⁻¹`. -/
noncomputable instance : MulSemiringAction G Γ(X, W.carrier) where
  smul g a := (ρ g⁻¹).asIso.hom.appLE W.carrier W.carrier (W.preimage_eq _).ge a
  one_smul a := by
    have h₁ : (ρ (1 : G)⁻¹).asIso.hom.appLE W.carrier W.carrier (W.preimage_eq _).ge = 𝟙 _ := by
      simp only [hom_one_inv]
      exact (Category.id_comp _).trans (X.presheaf.map_id _)
    exact ConcreteCategory.congr_hom h₁ a
  mul_smul g h a := by
    have h₁ : (ρ (g * h)⁻¹).asIso.hom.appLE W.carrier W.carrier (W.preimage_eq _).ge =
        (ρ h⁻¹).asIso.hom.appLE W.carrier W.carrier (W.preimage_eq _).ge ≫
          (ρ g⁻¹).asIso.hom.appLE W.carrier W.carrier (W.preimage_eq _).ge := by
      simp only [hom_mul_inv, Hom.appLE_comp_appLE]
    exact ConcreteCategory.congr_hom h₁ a
  smul_zero g := map_zero _
  smul_add g a b := map_add _ a b
  smul_one g := map_one _
  smul_mul g a b := map_mul _ a b

lemma smul_def (a : Γ(X, W.carrier)) :
    g • a = (ρ g⁻¹).asIso.hom.appLE W.carrier W.carrier (W.preimage_eq _).ge a :=
  rfl

/-- The open immersion `Spec Γ(X, W) ⟶ X`. -/
noncomputable abbrev fromSpec : Spec Γ(X, W.carrier) ⟶ X :=
  W.isAffineOpen.fromSpec

/-- The invariant quotient `Spec Γ(X, W)ᴳ` of a stable affine open `W`. -/
noncomputable abbrev Q : Scheme.{u} :=
  quotient Γ(X, W.carrier) G

/-- The projection `Spec Γ(X, W) ⟶ Spec Γ(X, W)ᴳ`. -/
noncomputable abbrev proj : Spec Γ(X, W.carrier) ⟶ W.Q :=
  projection Γ(X, W.carrier) G

lemma specComap_fromSpec :
    specComap Γ(X, W.carrier) G g ≫ W.fromSpec = W.fromSpec ≫ (ρ g⁻¹).asIso.hom :=
  IsAffineOpen.SpecMap_appLE_fromSpec _ W.isAffineOpen W.isAffineOpen (W.preimage_eq _).ge

lemma fromSpec_apply_mem (y : Spec Γ(X, W.carrier)) : W.fromSpec y ∈ W.carrier := by
  have h₁ : W.fromSpec y ∈ Set.range W.fromSpec := ⟨y, rfl⟩
  rwa [W.isAffineOpen.range_fromSpec] at h₁

lemma exists_fromSpec_eq {x : X} (hx : x ∈ W.carrier) : ∃ y, W.fromSpec y = x := by
  have h₁ : x ∈ (W.carrier : Set X) := hx
  rwa [← W.isAffineOpen.range_fromSpec] at h₁

lemma hom_apply_mem_iff {x : X} : (ρ g).asIso.hom x ∈ W.carrier ↔ x ∈ W.carrier := by
  conv_rhs => rw [← W.preimage_eq g]
  rfl

variable (h : V.carrier ≤ W.carrier)

/-- The restriction of sections from a stable affine open `W` to a smaller one `V`. -/
noncomputable abbrev res : Γ(X, W.carrier) ⟶ Γ(X, V.carrier) :=
  X.presheaf.map (homOfLE h).op

lemma smul_res (a : Γ(X, W.carrier)) : g • V.res W h a = V.res W h (g • a) := by
  rw [smul_def, smul_def, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    Hom.map_appLE, Hom.appLE_map]

/-- The restriction of invariant sections from a stable affine open `W` to a smaller one `V`. -/
noncomputable def invRes :
    FixedPoints.subring Γ(X, W.carrier) G →+* FixedPoints.subring Γ(X, V.carrier) G :=
  (V.res W h).hom.comp (FixedPoints.subring Γ(X, W.carrier) G).subtype |>.codRestrict _ fun a g ↦
    (smul_res V W g h a).trans (congrArg _ (a.2 g))

@[simp]
lemma coe_invRes (a : FixedPoints.subring Γ(X, W.carrier) G) :
    (V.invRes W h a : Γ(X, V.carrier)) = V.res W h (a : Γ(X, W.carrier)) :=
  rfl

/-- The morphism of invariant quotients induced by an inclusion of stable affine opens. -/
noncomputable def qMap : V.Q ⟶ W.Q :=
  Spec.map (CommRingCat.ofHom (V.invRes W h))

@[reassoc]
lemma proj_qMap : V.proj ≫ V.qMap W h = Spec.map (V.res W h) ≫ W.proj := by
  have h₁ : V.proj ≫ V.qMap W h = Spec.map (CommRingCat.ofHom (V.invRes W h) ≫
      CommRingCat.ofHom (algebraMap (FixedPoints.subring Γ(X, V.carrier) G) Γ(X, V.carrier))) :=
    (Spec.map_comp _ _).symm
  have h₂ : Spec.map (V.res W h) ≫ W.proj = Spec.map (CommRingCat.ofHom
      (algebraMap (FixedPoints.subring Γ(X, W.carrier) G) Γ(X, W.carrier)) ≫ V.res W h) :=
    (Spec.map_comp _ _).symm
  rw [h₁, h₂]
  rfl

lemma qMap_proj_apply (v : Spec Γ(X, V.carrier)) :
    V.qMap W h (V.proj v) = W.proj (Spec.map (V.res W h) v) :=
  congr($(V.proj_qMap W h) v)

@[reassoc]
lemma specMap_res_fromSpec : Spec.map (V.res W h) ≫ W.fromSpec = V.fromSpec :=
  W.isAffineOpen.map_fromSpec V.isAffineOpen _

lemma specComap_specMap_res : specComap Γ(X, V.carrier) G g ≫ Spec.map (V.res W h) =
    Spec.map (V.res W h) ≫ specComap Γ(X, W.carrier) G g := by
  rw [specComap_def, specComap_def, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact smul_res V W g h a

/-- **Invariants commute with localisation away from an invariant element.** If `B` is the
localisation of `A` away from an invariant `r`, compatibly with actions of a finite group, then `Bᴳ`
is the localisation of `Aᴳ` away from `r`: this is Tau Ceti's `TauCeti.FixedPoints.isLocalization`
for `B` presented abstractly, a case of `TauCeti.FixedPoints.isLocalization_of_mem_range_iff` on
Tau Ceti's main. -/
lemma isLocalization_away_fixedPoints {A B : Type*} [CommRing A] [CommRing B]
    [MulSemiringAction G A] [MulSemiringAction G B] [Finite G] [Algebra A B]
    (r : FixedPoints.subring A G) [IsLocalization.Away (r : A) B]
    (hφ : ∀ (g : G) (a : A), g • algebraMap A B a = algebraMap A B (g • a))
    (ψ : FixedPoints.subring A G →+* FixedPoints.subring B G)
    (hψ : ∀ a, (ψ a : B) = algebraMap A B a) :
    letI : Algebra (FixedPoints.subring A G) (FixedPoints.subring B G) := ψ.toAlgebra
    IsLocalization.Away r (FixedPoints.subring B G) := by
  let _ : Algebra (FixedPoints.subring A G) (FixedPoints.subring B G) := ψ.toAlgebra
  let N : Submonoid A := Algebra.algebraMapSubmonoid A (Submonoid.powers r)
  have hN : N = Submonoid.powers (r : A) := Submonoid.map_powers _ r
  have hB : IsLocalization N B := hN ▸ ‹IsLocalization.Away (r : A) B›
  let e : Localization N ≃ₐ[A] B := IsLocalization.algEquiv N _ B
  have he (g : G) (x : Localization N) : e (g • x) = g • e x := by
    have h₁ : e.toRingHom.comp (MulSemiringAction.toRingHom G _ g) =
        (MulSemiringAction.toRingHom G B g).comp e.toRingHom := by
      refine IsLocalization.ringHom_ext N (RingHom.ext fun a ↦ ?_)
      have h₂ : e (g • algebraMap A (Localization N) a) = g • algebraMap A B a := by
        rw [FixedPoints.smul_algebraMap_localization, AlgEquiv.commutes, hφ]
      exact h₂.trans (congrArg (g • ·) (e.commutes a).symm)
    exact congr($h₁ x)
  let e₀ : FixedPoints.subring (Localization N) G ≃+* FixedPoints.subring B G :=
    { toFun := fun x ↦ ⟨e x, fun g ↦ (he g x).symm.trans (congrArg e (x.2 g))⟩
      invFun := fun y ↦ ⟨e.symm y, fun g ↦ e.injective (by
        rw [he, e.apply_symm_apply, y.2 g])⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y ↦ Subtype.ext (e.apply_symm_apply y)
      map_mul' := fun x y ↦ Subtype.ext (map_mul e (x : Localization N) y)
      map_add' := fun x y ↦ Subtype.ext (map_add e (x : Localization N) y) }
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers r) (AlgEquiv.ofRingEquiv
    (f := e₀) fun a ↦ Subtype.ext ((e.commutes (a : A)).trans (hψ a).symm))

/-- The intersection of two stable affine opens of a separated scheme. -/
noncomputable def inf [X.IsSeparated] : StableAffineOpen ρ where
  carrier := V.carrier ⊓ W.carrier
  isAffineOpen := V.isAffineOpen.inf W.isAffineOpen
  preimage_eq g := by
    rw [Hom.preimage_inf, V.preimage_eq, W.preimage_eq]

/-- The basic open of an invariant section over a stable affine open, as a stable affine open. -/
noncomputable def basicOpen (r : FixedPoints.subring Γ(X, W.carrier) G) : StableAffineOpen ρ where
  carrier := X.basicOpen (r : Γ(X, W.carrier))
  isAffineOpen := W.isAffineOpen.basicOpen _
  preimage_eq g := by
    have h₁ : (ρ g).asIso.hom.appLE W.carrier W.carrier (W.preimage_eq g).ge r =
        (r : Γ(X, W.carrier)) := by
      have h₂ : g⁻¹ • (r : Γ(X, W.carrier)) = r := r.2 g⁻¹
      simpa only [smul_def, inv_inv] using h₂
    have h₃ : X.basicOpen ((ρ g).asIso.hom.appLE W.carrier W.carrier (W.preimage_eq g).ge r) =
        W.carrier ⊓ (ρ g).asIso.hom ⁻¹ᵁ X.basicOpen (r : Γ(X, W.carrier)) := by
      rw [Hom.appLE, ConcreteCategory.comp_apply, basicOpen_res, Hom.preimage_basicOpen]
    rw [h₁] at h₃
    have h₄ : (ρ g).asIso.hom ⁻¹ᵁ X.basicOpen (r : Γ(X, W.carrier)) ≤ W.carrier :=
      ((ρ g).asIso.hom.preimage_mono (X.basicOpen_le _)).trans (W.preimage_eq g).le
    exact le_antisymm ((le_inf h₄ le_rfl).trans h₃.ge) (h₃.le.trans inf_le_right)

variable [Finite G]

lemma isLocalization_invRes (r : FixedPoints.subring Γ(X, W.carrier) G)
    (hr : V.carrier = X.basicOpen (r : Γ(X, W.carrier))) :
    letI : Algebra (FixedPoints.subring Γ(X, W.carrier) G)
        (FixedPoints.subring Γ(X, V.carrier) G) := (V.invRes W h).toAlgebra
    IsLocalization.Away r (FixedPoints.subring Γ(X, V.carrier) G) := by
  let _ : Algebra Γ(X, W.carrier) Γ(X, V.carrier) := (V.res W h).hom.toAlgebra
  have : IsLocalization.Away (r : Γ(X, W.carrier)) Γ(X, V.carrier) :=
    W.isAffineOpen.isLocalization_of_eq_basicOpen _ (homOfLE h) hr
  exact isLocalization_away_fixedPoints r (fun g ↦ smul_res V W g h) (V.invRes W h) fun _ ↦ rfl

lemma isOpenImmersion_qMap_of_eq_basicOpen (r : FixedPoints.subring Γ(X, W.carrier) G)
    (hr : V.carrier = X.basicOpen (r : Γ(X, W.carrier))) : IsOpenImmersion (V.qMap W h) := by
  let _ : Algebra (FixedPoints.subring Γ(X, W.carrier) G) (FixedPoints.subring Γ(X, V.carrier) G) :=
    (V.invRes W h).toAlgebra
  have : IsLocalization.Away r (FixedPoints.subring Γ(X, V.carrier) G) :=
    isLocalization_invRes V W h r hr
  exact IsOpenImmersion.of_isLocalization r

lemma range_qMap_of_eq_basicOpen (r : FixedPoints.subring Γ(X, W.carrier) G)
    (hr : V.carrier = X.basicOpen (r : Γ(X, W.carrier))) :
    Set.range (V.qMap W h) = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum _)) := by
  let _ : Algebra (FixedPoints.subring Γ(X, W.carrier) G) (FixedPoints.subring Γ(X, V.carrier) G) :=
    (V.invRes W h).toAlgebra
  have : IsLocalization.Away r (FixedPoints.subring Γ(X, V.carrier) G) :=
    isLocalization_invRes V W h r hr
  exact PrimeSpectrum.localization_away_comap_range _ r

lemma proj_eq_iff (x y : Spec Γ(X, W.carrier)) :
    W.proj x = W.proj y ↔ ∃ g : G, y = specComap Γ(X, W.carrier) G g x := by
  refine (projection_eq_iff_exists_smul Γ(X, W.carrier) G x y).trans ⟨?_, ?_⟩
  · rintro ⟨g, hg⟩
    exact ⟨g⁻¹, hg.trans ((specComap_base_apply _ G g⁻¹ x).trans (by rw [inv_inv])).symm⟩
  · rintro ⟨g, hg⟩
    exact ⟨g⁻¹, hg.trans (specComap_base_apply _ G g x)⟩

lemma proj_surjective : Function.Surjective W.proj :=
  Surjective.surj (f := W.proj)

lemma qMap_injective : Function.Injective (V.qMap W h) := by
  intro x x' hx
  rcases V.proj_surjective x with ⟨v, rfl⟩
  rcases V.proj_surjective x' with ⟨v', rfl⟩
  rw [qMap_proj_apply, qMap_proj_apply, W.proj_eq_iff] at hx
  rcases hx with ⟨g, hg⟩
  have h₁ : Spec.map (V.res W h) ≫ W.fromSpec = V.fromSpec := V.specMap_res_fromSpec W h
  have hinj : Function.Injective (Spec.map (V.res W h)) := fun a b hab ↦
    V.isAffineOpen.fromSpec.isOpenEmbedding.injective <|
      congr($h₁ a).symm.trans ((congrArg W.fromSpec hab).trans congr($h₁ b))
  have hv : v' = specComap Γ(X, V.carrier) G g v := hinj <| hg.trans <| by
    rw [← Hom.comp_apply, ← Hom.comp_apply, specComap_specMap_res]
  exact (V.proj_eq_iff v v').mpr ⟨g, hv⟩

lemma exists_basicOpen_le (x : V.Q) : ∃ r : FixedPoints.subring Γ(X, W.carrier) G,
    V.qMap W h x ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum _)) ∧
      X.basicOpen (r : Γ(X, W.carrier)) ≤ V.carrier := by
  let Z : Set (Spec Γ(X, W.carrier)) := W.fromSpec ⁻¹' (V.carrier : Set X)ᶜ
  have hZ : IsClosed Z := V.carrier.isOpen.isClosed_compl.preimage W.fromSpec.continuous
  have hc : IsClosed (W.proj '' Z) := W.proj.isClosedMap Z hZ
  have hy : V.qMap W h x ∉ W.proj '' Z := by
    rintro ⟨z, hz, hzx⟩
    rcases V.proj_surjective x with ⟨v, rfl⟩
    rw [qMap_proj_apply, W.proj_eq_iff] at hzx
    rcases hzx with ⟨g, hg⟩
    refine hz ?_
    have h₁ : V.fromSpec v = (ρ g⁻¹).asIso.hom (W.fromSpec z) := by
      rw [← V.specMap_res_fromSpec W h, Hom.comp_apply, hg, ← Hom.comp_apply, specComap_fromSpec,
        Hom.comp_apply]
    have h₂ : (ρ g⁻¹).asIso.hom (W.fromSpec z) ∈ (V.carrier : Set X) := by
      rw [← h₁, ← V.isAffineOpen.range_fromSpec]
      exact ⟨v, rfl⟩
    have h₃ : W.fromSpec z ∈ (ρ g⁻¹).asIso.hom ⁻¹ᵁ V.carrier := h₂
    rwa [V.preimage_eq] at h₃
  rcases PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy
    hc.isOpen_compl with ⟨_, ⟨r, rfl⟩, hxr, hrZ⟩
  refine ⟨r, hxr, fun p hp ↦ ?_⟩
  by_contra hpV
  have hpW : p ∈ Set.range W.fromSpec := W.isAffineOpen.range_fromSpec ▸ X.basicOpen_le _ hp
  rcases hpW with ⟨q, rfl⟩
  have hq : q ∈ (PrimeSpectrum.basicOpen (r : Γ(X, W.carrier)) : Set (PrimeSpectrum _)) := by
    rw [← W.isAffineOpen.fromSpec_preimage_basicOpen]
    exact hp
  exact hrZ hq ⟨q, hpV, rfl⟩

instance : IsOpenImmersion (V.qMap W h) := by
  refine IsOpenImmersion.of_forall_source_exists _ (qMap_injective V W h) fun x ↦ ?_
  rcases exists_basicOpen_le V W h x with ⟨r, hr, hle⟩
  let D : StableAffineOpen ρ := W.basicOpen r
  have hDV : D.carrier ≤ V.carrier := hle
  have hDW : D.carrier ≤ W.carrier := X.basicOpen_le _
  have hcomp : D.qMap V hDV ≫ V.qMap W h = D.qMap W hDW := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    refine CommRingCat.hom_ext (RingHom.ext fun a ↦ Subtype.ext ?_)
    exact (ConcreteCategory.comp_apply _ _ _).symm.trans
      (ConcreteCategory.congr_hom (X.presheaf.map_comp _ _).symm _)
  let r' : FixedPoints.subring Γ(X, V.carrier) G := V.invRes W h r
  have hr' : D.carrier = X.basicOpen (r' : Γ(X, V.carrier)) :=
    (inf_eq_right.mpr hDV).symm.trans (X.basicOpen_res _ _).symm
  have : IsOpenImmersion (D.qMap V hDV) := isOpenImmersion_qMap_of_eq_basicOpen D V hDV r' hr'
  have : IsOpenImmersion (D.qMap W hDW) := isOpenImmersion_qMap_of_eq_basicOpen D W hDW r rfl
  refine ⟨D.Q, D.qMap V hDV, inferInstance, ?_, hcomp ▸ inferInstance⟩
  have hrange : Set.range (D.qMap V hDV) = (PrimeSpectrum.basicOpen r' : Set (PrimeSpectrum _)) :=
    range_qMap_of_eq_basicOpen D V hDV r' hr'
  exact hrange.ge hr

end StableAffineOpen

end AlgebraicGeometry.Scheme
