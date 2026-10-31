import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import TauCeti.AlgebraicGeometry.Curves.HomOfAlgHom
import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.AntiEquivalence
import TauCeti.AlgebraicGeometry.Modules.RationalFunctions
import TauCeti.AlgebraicGeometry.Morphisms.Epi
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
import TauCeti.AlgebraicGeometry.Scheme.Place.Hom
import TauCeti.AlgebraicGeometry.Scheme.Place.Injective
import TauCeti.AlgebraicGeometry.Scheme.Regular
import TauCeti.FieldTheory.FunctionField.Automorphism.FixedField
import TauCeti.FieldTheory.FunctionField.Place.Extension.Galois
import TauCeti.FieldTheory.FunctionField.Place.Map
import TauCeti.FieldTheory.Galois.FixedField

/-!
# The quotient of a regular proper curve by a finite group of automorphisms

Let `X` be a regular proper curve over a field `k`, such as a smooth projective curve, and `H` a
finite group of automorphisms of `X`. The quotient curve `X / H` (LMFDB `ag.quotient_curve`) is
constructed here as the regular proper curve whose function field is the fixed field `k(X)^H`,
through Tau Ceti's anti-equivalence between regular proper curves and algebraic function fields
(`TauCeti.AlgebraicGeometry.RegularProperCurveCat.equivFunctionFieldCat`): it is the two-chart
model of `k(X)^H`, and the projection `X ⟶ X / H` is the morphism corresponding to the inclusion
`k(X)^H ⊆ k(X)`. The projection is invariant under `H`, surjective, and universal among the
morphisms of regular proper curves (the dominant morphisms over `k`) invariant under `H`, and its
fibres are the `H`-orbits, so that `X / H` is obtained from `X` by identifying the points of each
`H`-orbit, as in the knowl. The fibres are computed through the dictionary between the closed
points of a regular proper curve and the places of its function field: the places of `k(X)` over a
place of `k(X)^H` form one orbit of the Galois group `Gal(k(X) / k(X)^H) = H`.

The structure sheaf of `X / H` is the sheaf of `H`-invariant functions on `X`,
`𝒪_{X/H} = (π_* 𝒪_X)^H`, and the projection is an epimorphism of schemes, which is the uniqueness
half of the universal property of the quotient among all schemes over `k` by which
`AlgebraicGeometry.Scheme.IsQuotientCurve` characterizes the quotient curve of an algebraic curve.
The existence half of that universal property, which needs a morphism of schemes to be glued from
the invariant sections, is not formalised. Of the geometric integrality of `X / H` that
`AlgebraicGeometry.Scheme.IsQuotientCurve` also asks for, geometric irreducibility is proved, but
not geometric reducedness, which needs the separability of `k(X)^H` over `k`. The quotient of a
curve that is not proper or not regular is not formalised either.

## Main definitions

* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.autToAlgEquiv`: the action of the automorphisms
  of `X` on the function field `k(X)`.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.quotient` (LMFDB `ag.quotient_curve`): the
  quotient curve `X / H`.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.toQuotient` (LMFDB `ag.quotient_curve`): the
  projection `X ⟶ X / H`.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.quotientFunctionFieldEquiv`: the function field
  of `X / H` is the fixed field `k(X)^H`.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.orbitEquivQuotient` (LMFDB `ag.quotient_curve`):
  the points of `X / H` are the `H`-orbits of the points of `X`, for the action
  `MulAction (Aut X) X.toScheme` of the automorphisms of `X` on its points.

## Main results

* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.fieldRange_functionFieldAlgHom_toQuotient`: the
  pullback of rational functions along the projection identifies `k(X / H)` with `k(X)^H`.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.hom_comp_toQuotient`: the projection is
  invariant under `H`.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.existsUnique_toQuotient_comp_eq`: every morphism
  of regular proper curves from `X` invariant under `H` factors uniquely through the projection.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.surjective_toQuotient`: the projection is
  surjective.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.toQuotient_apply_eq_iff`: the fibres of the
  projection are the `H`-orbits.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.range_germToFunctionField_quotient`: the
  sections of `𝒪_{X/H}` over an open `V` are the `H`-invariant sections of `𝒪_X` over `π⁻¹ V`.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.epi_toQuotient`: the projection is an
  epimorphism of schemes.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.geometricallyIrreducible_quotient`: the
  quotient of a geometrically irreducible curve is geometrically irreducible.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme IntermediateField TopCat Presheaf
  MulAction

namespace TauCeti.AlgebraicGeometry.RegularProperCurveCat

universe u

variable {k : Type u} [Field k] {X Y Z : RegularProperCurveCat k} (f : X ⟶ Y) (σ : Aut X)
  {x : X.toScheme} (a : X.toScheme.functionField)

lemma functionFieldAlgHom_comp_hom (g : Y ⟶ Z) : (f ≫ g).hom.functionFieldAlgHom k =
    (f.hom.functionFieldAlgHom k).comp (g.hom.functionFieldAlgHom k) :=
  f.hom.functionFieldAlgHom_comp k g.hom

lemma functionFieldAlgHom_id_hom : (𝟙 X : X ⟶ X).hom.functionFieldAlgHom k = AlgHom.id k _ :=
  Hom.functionFieldAlgHom_id k

/-- The action of the automorphisms of a regular proper curve `X` over `k` on its function field
`k(X)`: an automorphism `σ` acts by pulling back rational functions along `σ⁻¹`, so that
`σ • f = f ∘ σ⁻¹`. -/
noncomputable def autToAlgEquiv :
    Aut X →* (X.toScheme.functionField ≃ₐ[k] X.toScheme.functionField) where
  toFun σ := .ofAlgHom (σ.asIso.inv.hom.functionFieldAlgHom k)
    (σ.asIso.hom.hom.functionFieldAlgHom k)
    (by rw [← functionFieldAlgHom_comp_hom, σ.asIso.inv_hom_id, functionFieldAlgHom_id_hom])
    (by rw [← functionFieldAlgHom_comp_hom, σ.asIso.hom_inv_id, functionFieldAlgHom_id_hom])
  map_one' := by
    ext a
    simp
  map_mul' σ τ := by
    ext a
    simp

lemma autToAlgEquiv_apply : autToAlgEquiv σ a = σ.asIso.inv.hom.functionFieldAlgHom k a :=
  rfl

lemma autToAlgEquiv_inv_apply : autToAlgEquiv σ⁻¹ a = σ.asIso.hom.hom.functionFieldAlgHom k a :=
  rfl

variable (H : Subgroup (Aut X))

/-- A group `H` of automorphisms of a regular proper curve `X`, as a group of automorphisms of the
function field `k(X)` through `TauCeti.AlgebraicGeometry.RegularProperCurveCat.autToAlgEquiv`. -/
noncomputable abbrev functionFieldSubgroup :
    Subgroup (X.toScheme.functionField ≃ₐ[k] X.toScheme.functionField) :=
  H.map autToAlgEquiv

variable {H f} in
lemma functionFieldAlgHom_mem_fixedField (hf : ∀ σ ∈ H, σ.asIso.hom ≫ f = f)
    (z : Y.toScheme.functionField) :
    f.hom.functionFieldAlgHom k z ∈ fixedField (functionFieldSubgroup H) := by
  rw [mem_fixedField_iff]
  rintro _ ⟨σ, hσ, rfl⟩
  have hσf : σ.asIso.inv ≫ f = f := hf σ⁻¹ (inv_mem hσ)
  rw [autToAlgEquiv_apply, ← AlgHom.comp_apply, ← functionFieldAlgHom_comp_hom, hσf]

variable [Finite H]

instance : Finite (functionFieldSubgroup H) :=
  .of_surjective _ (autToAlgEquiv.subgroupMap_surjective H)

/-- The fixed field `k(X)^H` of a finite group `H` of automorphisms of a regular proper curve `X`,
as an algebraic function field over `k`. -/
noncomputable abbrev quotientFunctionField : FunctionFieldCat k :=
  @FunctionFieldCat.of k _ (fixedField (functionFieldSubgroup H)) _
    (fixedField (functionFieldSubgroup H)).algebra'
    (IsCurveOver.isFunctionField.fixedField (functionFieldSubgroup H))

/-- The **quotient curve** `X / H` (LMFDB `ag.quotient_curve`) of a regular proper curve `X` over
`k` by a finite group `H` of automorphisms of `X`: the regular proper curve whose function field is
the fixed field `k(X)^H`, the two-chart model of `k(X)^H` given by Tau Ceti's anti-equivalence
between regular proper curves and algebraic function fields. -/
noncomputable def quotient : RegularProperCurveCat k :=
  (twoChartModelFunctor k).obj (op (quotientFunctionField H))

/-- The **function field of the quotient curve** `X / H` is the fixed field `k(X)^H`. -/
noncomputable def quotientFunctionFieldEquiv :
    (quotient H).toScheme.functionField ≃ₐ[k] fixedField (functionFieldSubgroup H) :=
  twoChartModel.functionFieldEquiv (transcendental_modelGenerator (quotientFunctionField H))

/-- The **projection** `X ⟶ X / H` (LMFDB `ag.quotient_curve`) of a regular proper curve onto its
quotient curve by a finite group `H` of automorphisms: the morphism of regular proper curves whose
pullback of rational functions is the inclusion of `k(X / H) = k(X)^H` in `k(X)`. -/
noncomputable def toQuotient : X ⟶ quotient H :=
  homOfAlgHom <| (fixedField (functionFieldSubgroup H)).val.comp
    (quotientFunctionFieldEquiv H).toAlgHom

lemma functionFieldAlgHom_toQuotient : (toQuotient H).hom.functionFieldAlgHom k =
    (fixedField (functionFieldSubgroup H)).val.comp (quotientFunctionFieldEquiv H).toAlgHom :=
  functionFieldAlgHom_homOfAlgHom _

lemma functionFieldAlgHom_toQuotient_apply (b : (quotient H).toScheme.functionField) :
    (toQuotient H).hom.functionFieldAlgHom k b = quotientFunctionFieldEquiv H b := by
  rw [functionFieldAlgHom_toQuotient]
  rfl

/-- **The function field of the quotient curve is the fixed field**: the pullback of rational
functions along the projection `X ⟶ X / H` maps `k(X / H)` onto the fixed field `k(X)^H`. -/
lemma fieldRange_functionFieldAlgHom_toQuotient :
    ((toQuotient H).hom.functionFieldAlgHom k).fieldRange =
      fixedField (functionFieldSubgroup H) := by
  ext a
  rw [AlgHom.mem_fieldRange]
  refine ⟨?_, fun ha ↦ ?_⟩
  · rintro ⟨b, rfl⟩
    rw [functionFieldAlgHom_toQuotient_apply]
    exact SetLike.coe_mem _
  · refine ⟨(quotientFunctionFieldEquiv H).symm ⟨a, ha⟩, ?_⟩
    rw [functionFieldAlgHom_toQuotient_apply, AlgEquiv.apply_symm_apply]

variable {H} (V : (quotient H).toScheme.Opens) [Nonempty V]

variable {σ} in
/-- **The projection onto the quotient curve is invariant under `H`**: `σ ≫ π = π` for `σ ∈ H`,
since the pullback of rational functions along `π` lands in the fixed field `k(X)^H`. -/
lemma hom_comp_toQuotient (hσ : σ ∈ H) : σ.asIso.hom ≫ toQuotient H = toQuotient H := by
  refine functionFieldAlgHom_injective (AlgHom.ext fun a ↦ ?_)
  have hmem : autToAlgEquiv σ⁻¹ ∈ functionFieldSubgroup H := Subgroup.mem_map_of_mem _ (inv_mem hσ)
  beta_reduce
  rw [functionFieldAlgHom_comp_hom, AlgHom.comp_apply, ← autToAlgEquiv_inv_apply,
    functionFieldAlgHom_toQuotient_apply]
  exact (mem_fixedField_iff _ _).mp (quotientFunctionFieldEquiv H a).2 _ hmem

/-- **The universal property of the quotient curve among regular proper curves**: a morphism of
regular proper curves `f : X ⟶ Y`, that is a dominant morphism of schemes over `k`, invariant
under `H` factors uniquely through the projection `X ⟶ X / H`. -/
lemma existsUnique_toQuotient_comp_eq (hf : ∀ σ ∈ H, σ.asIso.hom ≫ f = f) :
    ∃! g : quotient H ⟶ Y, toQuotient H ≫ g = f := by
  let ψ : Y.toScheme.functionField →ₐ[k] (quotient H).toScheme.functionField :=
    (quotientFunctionFieldEquiv H).symm.toAlgHom.comp <| (f.hom.functionFieldAlgHom k).codRestrict
      (fixedField (functionFieldSubgroup H)).toSubalgebra (functionFieldAlgHom_mem_fixedField hf)
  have hψ : ∀ z, (toQuotient H).hom.functionFieldAlgHom k (ψ z) = f.hom.functionFieldAlgHom k z :=
    fun z ↦ by
      rw [functionFieldAlgHom_toQuotient_apply]
      exact congrArg Subtype.val ((quotientFunctionFieldEquiv H).apply_symm_apply _)
  refine ⟨homOfAlgHom ψ, functionFieldAlgHom_injective (AlgHom.ext fun z ↦ ?_), fun g hg ↦ ?_⟩
  · beta_reduce
    rw [functionFieldAlgHom_comp_hom, AlgHom.comp_apply, functionFieldAlgHom_homOfAlgHom, hψ]
  · rw [← homOfAlgHom_functionFieldAlgHom g]
    refine congrArg homOfAlgHom (AlgHom.ext fun z ↦
      ((toQuotient H).hom.functionFieldAlgHom k).injective ?_)
    have h : (toQuotient H).hom.functionFieldAlgHom k (g.hom.functionFieldAlgHom k z) =
        (toQuotient H).hom.functionFieldAlgHom k (ψ z) := by
      rw [hψ, ← AlgHom.comp_apply, ← functionFieldAlgHom_comp_hom, hg]
    exact h

variable (H) in
/-- **The projection onto the quotient curve is surjective**: it is a closed map, as `X` is proper
and `X / H` is separated over `k`, and its image is dense, as it is dominant. -/
lemma surjective_toQuotient : Surjective (toQuotient H).hom := by
  have hcomp : UniversallyClosed ((toQuotient H).hom ≫ (quotient H).toScheme ↘ Spec (.of k)) := by
    rw [comp_over]
    infer_instance
  have hπ : UniversallyClosed (toQuotient H).hom :=
    .of_comp_of_isSeparated _ ((quotient H).toScheme ↘ Spec (.of k))
  exact ⟨Set.range_eq_univ.mp <| (toQuotient H).hom.isClosedMap.isClosed_range.closure_eq.symm.trans
    (toQuotient H).hom.denseRange.closure_range⟩

lemma isDiscreteValuationRing_stalk_of_ne_genericPoint (hx : x ≠ genericPoint X.toScheme) :
    IsDiscreteValuationRing (X.toScheme.presheaf.stalk x) :=
  X.isDiscreteValuationRing_stalk ⟨x, (Scheme.coheight_eq_one_iff_ne_genericPoint
    (IsCurveOver.topologicalKrullDim_eq_one k).le).mpr hx⟩

variable (x) in
lemma inv_hom_apply_hom_hom_apply : σ.asIso.inv.hom (σ.asIso.hom.hom x) = x := by
  rw [← Hom.comp_apply, ← comp_hom, σ.asIso.hom_inv_id, id_hom]
  rfl

variable (x) in
lemma toPlace_hom_hom_apply [IsDiscreteValuationRing (X.toScheme.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.toScheme.presheaf.stalk (σ.asIso.hom.hom x))] :
    X.toScheme.toPlace (σ.asIso.hom.hom x) = (X.toScheme.toPlace x).map (autToAlgEquiv σ) := by
  refine (Place.eq_of_integers_le (IsConcreteLE.le_iff.mpr fun g hg ↦ ?_)).symm
  rw [Place.mem_integers_map_iff] at hg
  rcases (X.toScheme.mem_toPlace_integers_iff_exists_stalk x _).mp hg with ⟨a, ha⟩
  rcases exists_germ_eq X.toScheme.presheaf a with ⟨U, hU, s, rfl⟩
  have hne : Nonempty U := ⟨⟨_, hU⟩⟩
  rw [algebraMap_germ_eq_germToFunctionField] at ha
  have hmem : autToAlgEquiv σ (X.toScheme.germToFunctionField U s) ∈
      (X.toScheme.toPlace (k := k) (σ.asIso.hom.hom x)).integers :=
    σ.asIso.inv.hom.functionFieldMap_germToFunctionField_mem_toPlace_integers _
      ((inv_hom_apply_hom_hom_apply σ x).symm ▸ hU) s
  rwa [ha, AlgEquiv.apply_symm_apply] at hmem

lemma restrict_toPlace_eq_map {z : (quotient H).toScheme} (hz : (toQuotient H).hom x = z)
    [IsDiscreteValuationRing (X.toScheme.presheaf.stalk x)]
    [IsDiscreteValuationRing ((quotient H).toScheme.presheaf.stalk z)] :
    (X.toScheme.toPlace (k := k) x).restrict k (fixedField (functionFieldSubgroup H)) =
      ((quotient H).toScheme.toPlace z).map (quotientFunctionFieldEquiv H) := by
  subst hz
  refine (Place.restrict_eq_iff_integers_le k _ _ _).mpr fun f hf ↦ ?_
  rw [Place.mem_integers_map_iff] at hf
  rcases ((quotient H).toScheme.mem_toPlace_integers_iff_exists_stalk _ _).mp hf with ⟨a, ha⟩
  have hmem : (toQuotient H).hom.functionFieldAlgHom k ((quotientFunctionFieldEquiv H).symm f) ∈
      (X.toScheme.toPlace (k := k) x).integers :=
    ha ▸ (toQuotient H).hom.functionFieldMap_algebraMap_mem_toPlace_integers x a
  rwa [functionFieldAlgHom_toQuotient_apply, AlgEquiv.apply_symm_apply] at hmem

variable (H) in
lemma toQuotient_apply_ne_genericPoint (hx : x ≠ genericPoint X.toScheme) :
    (toQuotient H).hom x ≠ genericPoint (quotient H).toScheme := by
  have hdvr : IsDiscreteValuationRing (X.toScheme.presheaf.stalk x) :=
    isDiscreteValuationRing_stalk_of_ne_genericPoint hx
  intro hπx
  refine ((X.toScheme.toPlace (k := k) x).restrict k
    (fixedField (functionFieldSubgroup H))).integers_ne_top (eq_top_iff.mpr fun w _ ↦ ?_)
  refine (Place.mem_integers_restrict_iff k _ _ w).mpr (by_contra fun hw ↦ ?_)
  refine (toQuotient H).hom.ne_genericPoint_of_functionFieldMap_notMem_toPlace_integers (k := k)
    x (z := (quotientFunctionFieldEquiv H).symm w) ?_ hπx
  have hπw : (toQuotient H).hom.functionFieldAlgHom k ((quotientFunctionFieldEquiv H).symm w) =
      algebraMap (fixedField (functionFieldSubgroup H)) X.toScheme.functionField w := by
    rw [functionFieldAlgHom_toQuotient_apply, AlgEquiv.apply_symm_apply]
    rfl
  exact hπw ▸ hw

/-- **The fibres of the projection onto the quotient curve are the `H`-orbits**: two points of `X`
have the same image in `X / H` exactly when an element of `H` maps one to the other, so that `X / H`
is obtained from `X` by identifying the points of each `H`-orbit. The places of `k(X)` over a place
of `k(X)^H` form one orbit of `Gal(k(X) / k(X)^H) = H`. -/
lemma toQuotient_apply_eq_iff {y : X.toScheme} :
    (toQuotient H).hom x = (toQuotient H).hom y ↔ ∃ σ ∈ H, σ.asIso.hom.hom x = y := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_cases hx : x = genericPoint X.toScheme
    · have hy : y = genericPoint X.toScheme := by
        by_contra hy
        refine toQuotient_apply_ne_genericPoint H hy ?_
        rw [← h, hx, Hom.genericPoint_eq_of_isDominant]
      refine ⟨1, one_mem H, ?_⟩
      rw [hx, hy]
      rfl
    by_cases hy : y = genericPoint X.toScheme
    · refine absurd ?_ (toQuotient_apply_ne_genericPoint H hx)
      rw [h, hy, Hom.genericPoint_eq_of_isDominant]
    have hdx : IsDiscreteValuationRing (X.toScheme.presheaf.stalk x) :=
      isDiscreteValuationRing_stalk_of_ne_genericPoint hx
    have hdy : IsDiscreteValuationRing (X.toScheme.presheaf.stalk y) :=
      isDiscreteValuationRing_stalk_of_ne_genericPoint hy
    have hdz :
        IsDiscreteValuationRing ((quotient H).toScheme.presheaf.stalk ((toQuotient H).hom x)) :=
      isDiscreteValuationRing_stalk_of_ne_genericPoint (toQuotient_apply_ne_genericPoint H hx)
    rcases Place.exists_smul_eq_of_restrict_eq ((restrict_toPlace_eq_map (H := H) rfl).trans
      (restrict_toPlace_eq_map (H := H) h.symm).symm) with ⟨τ, hτ⟩
    have hτH : τ.restrictScalars k ∈ functionFieldSubgroup H :=
      (SetLike.ext_iff.mp (fixingSubgroup_fixedField_of_finite (functionFieldSubgroup H)) _).mp
        ((IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun a ha ↦ τ.commutes ⟨a, ha⟩)
    rcases hτH with ⟨σ, hσ, hστ⟩
    refine ⟨σ, hσ, ?_⟩
    have hσx : σ.asIso.hom.hom x ≠ genericPoint X.toScheme := fun hσx ↦ hx <| by
      rw [← inv_hom_apply_hom_hom_apply σ x, hσx, Hom.genericPoint_eq_of_isDominant]
    have hdσ : IsDiscreteValuationRing (X.toScheme.presheaf.stalk (σ.asIso.hom.hom x)) :=
      isDiscreteValuationRing_stalk_of_ne_genericPoint hσx
    have hsep : X.toScheme.IsSeparated := by
      constructor
      rw [← terminal.comp_from (X.toScheme ↘ Spec (.of k))]
      infer_instance
    refine (toPlace_eq_iff (k := k)).mp ?_
    rw [toPlace_hom_hom_apply σ x, hστ, ← Place.smul_eq_map, hτ]
  · rintro ⟨σ, hσ, rfl⟩
    rw [← Hom.comp_apply, ← comp_hom, hom_comp_toQuotient hσ]

@[nolint defsWithUnderscore]
instance : MulAction (Aut X) X.toScheme where
  smul σ x := σ.asIso.hom.hom x
  one_smul _ := rfl
  mul_smul σ τ x := τ.asIso.hom.hom.comp_apply σ.asIso.hom.hom x

variable (x) in
lemma smul_def : σ • x = σ.asIso.hom.hom x :=
  rfl

variable (H) in
/-- **The points of the quotient curve are the `H`-orbits of the points of `X`** (LMFDB
`ag.quotient_curve`): the projection `X ⟶ X / H` induces a bijection from the set of `H`-orbits of
points of `X` onto the set of points of `X / H`. -/
noncomputable def orbitEquivQuotient : orbitRel.Quotient H X.toScheme ≃ (quotient H).toScheme :=
  Equiv.ofBijective (Quotient.lift (toQuotient H).hom fun _ _ h ↦
    (toQuotient_apply_eq_iff.mpr <| by
      rcases orbitRel_apply.mp h with ⟨σ, hσ⟩
      exact ⟨σ, σ.2, hσ⟩).symm)
    ⟨fun p q ↦ Quotient.inductionOn₂ p q fun x y h ↦ by
      rcases toQuotient_apply_eq_iff.mp h with ⟨σ, hσ, hσx⟩
      exact Quotient.sound <| orbitRel_apply.mpr <| mem_orbit_symm.mp ⟨⟨σ, hσ⟩, hσx⟩,
    fun y ↦ by
      rcases (surjective_toQuotient H).surj y with ⟨x, rfl⟩
      exact ⟨⟦x⟧, rfl⟩⟩

variable (x) in
lemma orbitEquivQuotient_mk : orbitEquivQuotient H ⟦x⟧ = (toQuotient H).hom x :=
  rfl

lemma functionFieldAlgHom_toQuotient_germToFunctionField (s : Γ((quotient H).toScheme, V)) :
    (toQuotient H).hom.functionFieldAlgHom k ((quotient H).toScheme.germToFunctionField V s) =
      X.toScheme.germToFunctionField _ ((toQuotient H).hom.app V s) := by
  have h : ((quotient H).toScheme.germToFunctionField V ≫ (toQuotient H).hom.functionFieldMap) s =
      ((toQuotient H).hom.app V ≫ X.toScheme.germToFunctionField _) s :=
    congr($((toQuotient H).hom.germToFunctionField_functionFieldMap V) s)
  rwa [CommRingCat.comp_apply, CommRingCat.comp_apply] at h

variable (H) in
/-- **The sections of the quotient curve are the `H`-invariant sections**, `𝒪_{X/H} = (π_* 𝒪_X)^H`:
for a nonempty open `V` of `X / H`, the rational functions on `X` pulled back from the sections of
`𝒪_{X/H}` over `V` are the sections of `𝒪_X` over `π⁻¹ V` that lie in the fixed field `k(X)^H`.
A rational function on `X / H` is regular at a point `y` as soon as its pullback is regular at a
point over `y`, since the place of `y` is the restriction of the place of that point. -/
lemma range_germToFunctionField_quotient : Set.range (fun s : Γ((quotient H).toScheme, V) ↦
      (toQuotient H).hom.functionFieldAlgHom k ((quotient H).toScheme.germToFunctionField V s)) =
      Set.range (X.toScheme.germToFunctionField ((toQuotient H).hom ⁻¹ᵁ V)) ∩
        fixedField (functionFieldSubgroup H) := by
  ext f
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    refine ⟨⟨(toQuotient H).hom.app V s, ?_⟩, ?_⟩
    · exact (functionFieldAlgHom_toQuotient_germToFunctionField V s).symm
    · beta_reduce
      rw [SetLike.mem_coe, functionFieldAlgHom_toQuotient_apply]
      exact SetLike.coe_mem _
  · rintro ⟨⟨t, rfl⟩, hE⟩
    have hloc : ∀ y ∈ V, (quotientFunctionFieldEquiv H).symm ⟨_, hE⟩ ∈ (algebraMap
        ((quotient H).toScheme.presheaf.stalk y) (quotient H).toScheme.functionField).range :=
      fun y hy ↦ ?_
    · rcases Scheme.exists_germToFunctionField_eq_of_forall_mem_range hloc with ⟨s, hs⟩
      refine ⟨s, ?_⟩
      beta_reduce
      rw [hs, functionFieldAlgHom_toQuotient_apply, AlgEquiv.apply_symm_apply]
    rcases (surjective_toQuotient H).surj y with ⟨x, rfl⟩
    by_cases hx : x = genericPoint X.toScheme
    · have hcoh : Order.coheight ((toQuotient H).hom x) = 0 := by
        rw [hx, Hom.genericPoint_eq_of_isDominant]
        exact Order.coheight_eq_zero.mpr Scheme.isMax_genericPoint
      exact Scheme.exists_algebraMap_stalk_eq_of_coheight_eq_zero hcoh _
    have hdx : IsDiscreteValuationRing (X.toScheme.presheaf.stalk x) :=
      isDiscreteValuationRing_stalk_of_ne_genericPoint hx
    have hdy :
        IsDiscreteValuationRing ((quotient H).toScheme.presheaf.stalk ((toQuotient H).hom x)) :=
      isDiscreteValuationRing_stalk_of_ne_genericPoint (toQuotient_apply_ne_genericPoint H hx)
    have hfx : X.toScheme.germToFunctionField _ t ∈ (X.toScheme.toPlace (k := k) x).integers := by
      rw [← X.toScheme.algebraMap_germ_eq_germToFunctionField (hy : x ∈ (toQuotient H).hom ⁻¹ᵁ V)]
      exact X.toScheme.algebraMap_stalk_mem_toPlace_integers x _
    have hres : (⟨_, hE⟩ : fixedField (functionFieldSubgroup H)) ∈
        ((X.toScheme.toPlace (k := k) x).restrict k
          (fixedField (functionFieldSubgroup H))).integers :=
      (Place.mem_integers_restrict_iff k _ _ _).mpr hfx
    rw [restrict_toPlace_eq_map rfl, Place.mem_integers_map_iff] at hres
    exact ((quotient H).toScheme.mem_toPlace_integers_iff_exists_stalk _ _).mp hres

lemma app_toQuotient_injective : Function.Injective ((toQuotient H).hom.app V) := by
  intro s t hst
  have h : X.toScheme.germToFunctionField _ ((toQuotient H).hom.app V s) =
      X.toScheme.germToFunctionField _ ((toQuotient H).hom.app V t) := by
    rw [hst]
  rw [← functionFieldAlgHom_toQuotient_germToFunctionField,
    ← functionFieldAlgHom_toQuotient_germToFunctionField] at h
  exact (quotient H).toScheme.germToFunctionField_injective V
    (((toQuotient H).hom.functionFieldAlgHom k).injective h)

variable (H) in
/-- **The projection onto the quotient curve is an epimorphism of schemes**: two morphisms of
schemes out of `X / H` that agree after the projection are equal, since the projection is
surjective and injective on sections. This is the uniqueness half of the universal property of the
quotient among all schemes (`AlgebraicGeometry.Scheme.IsQuotientCurve`). -/
lemma epi_toQuotient : Epi (toQuotient H).hom := by
  have hsurj : Surjective (toQuotient H).hom := surjective_toQuotient H
  refine (toQuotient H).hom.epi_of_surjective_of_app_injective fun U ↦ ?_
  rcases isEmpty_or_nonempty U with hU | hU
  · have hbot : U = ⊥ := eq_bot_iff.mpr fun x hx ↦ (hU.false ⟨x, hx⟩).elim
    subst hbot
    exact Function.injective_of_subsingleton _
  · exact app_toQuotient_injective U

variable (H) in
/-- **The quotient of a geometrically irreducible curve is geometrically irreducible**: after a base
change to a field `L`, the base change of `X` is irreducible and maps onto the base change of
`X / H`, since the projection is surjective and surjectivity is stable under base change. -/
lemma geometricallyIrreducible_quotient [GeometricallyIrreducible (X.toScheme ↘ Spec (.of k))] :
    GeometricallyIrreducible ((quotient H).toScheme ↘ Spec (.of k)) := by
  refine ⟨fun L _ y Z fst snd h ↦ ?_⟩
  have hW : IsPullback (pullback.fst (X.toScheme ↘ Spec (.of k)) y) (pullback.snd _ y)
      ((toQuotient H).hom ≫ (quotient H).toScheme ↘ Spec (.of k)) y := by
    rw [comp_over]
    exact IsPullback.of_hasPullback _ _
  have hirr : IrreducibleSpace ↥(pullback (X.toScheme ↘ Spec (.of k)) y) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace y _ _ (IsPullback.of_hasPullback _ _)
  exact (MorphismProperty.of_isPullback (IsPullback.of_bot' hW h)
    (surjective_toQuotient H)).surj.irreducibleSpace (Hom.continuous _)

end TauCeti.AlgebraicGeometry.RegularProperCurveCat
