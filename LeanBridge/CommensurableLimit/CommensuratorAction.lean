/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanBridge.CommensurableLimit.DirectLimit
import Mathlib.RepresentationTheory.Invariants

/-!
# The commensurator action on the direct limit, and its level invariants

The commensurator `commensurator Γ₀` acts on `ModularFormCommensurable Γ₀ k` by the weight-`k` slash
action (a `g` sends the level-`Γ` piece to the level-`gΓg⁻¹` piece via `f ↦ f ∣[k] g⁻¹`). For an
element of *negative* determinant the slash action carries a `σ`-twist by complex conjugation, so it
is only `ℝ`-linear (`ℂ`-conjugate-linear) rather than `ℂ`-linear. We therefore view
`ModularFormCommensurable Γ₀ k` as an `ℝ`-vector space (by restriction of scalars from its
`ℂ`-structure) and build the action as a `Representation ℝ` of the *whole* commensurator. We prove
that the `Γ`-invariants of the limit are exactly `ModularForm Γ k` (the image of `ofLevel Γ`).

## Main definitions

* `ModularForm.CommIndex.conj` — the conjugation action of a commensurator element on the index.
* `ModularForm.translateℝ` — slash by an arbitrary `g ∈ GL(2,ℝ)` (either determinant sign) as an
  `ℝ`-linear map `ModularForm Γ k → ModularForm (g⁻¹Γg) k`.
* `ModularFormCommensurable.smulMap` — the `ℝ`-linear action of `g ∈ commensurator Γ₀` on the limit.
* `ModularFormCommensurable.toFunₗ` — the injective `ℂ`-linear map from the limit to functions
  `ℍ → ℂ`.
* `ModularFormCommensurable.commRep` — the weight-`k` `ℝ`-representation of `commensurator Γ₀` on the
  limit.
* `ModularFormCommensurable.ofLevelInvariantsEquiv` — the `ℝ`-linear isomorphism of
  `ModularForm Γ.carrier k` with the level invariants.

## Main results

* `Subgroup.commensurable_le_commensurator` — a subgroup commensurable with `Γ₀` lies in its
  commensurator.
* `ModularFormCommensurable.range_ofLevel_eq_invariants` — the level-`Γ` invariants of the
  commensurator action are exactly the image of `ModularForm Γ.carrier k` under `ofLevel`.

## Implementation notes

`ModularFormCommensurable Γ₀ k` is a `ℂ`-vector space built as a `Module.DirectLimit` over `ℂ`, and
the `ℂ`-linear universal property (`lift`) cannot produce the merely-`ℝ`-linear maps coming from
negative-determinant elements. To build the `ℝ`-linear `smulMap` we transport the `ℝ`-linear
universal property along the canonical `ℝ`-linear isomorphism `equivℝ` between the `ℂ`-built limit
and the same directed system rebuilt over `ℝ` (by `restrictScalars`); the two limits agree because
the components and the transition maps are unchanged — only the scalar ring is restricted.
-/

open scoped MatrixGroups Pointwise

namespace Subgroup

variable {G : Type*} [Group G]

/-- A subgroup commensurable with `Γ₀` is contained in the commensurator of `Γ₀`. -/
theorem commensurable_le_commensurator {Γ Γ₀ : Subgroup G} (h : Commensurable Γ Γ₀) :
    Γ ≤ Commensurable.commensurator Γ₀ := by
  intro g hg
  rw [Commensurable.commensurator_mem_iff]
  have hΓ : ConjAct.toConjAct g • Γ = Γ := by
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, map_inv,
      ConjAct.ofConjAct_toConjAct, inv_inv]
    refine ⟨fun hx ↦ ?_, fun hx ↦ Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hg) hx) hg⟩
    have hxx : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [hxx]
    exact Γ.mul_mem (Γ.mul_mem hg hx) (Γ.inv_mem hg)
  have h1 := h.symm.conj (ConjAct.toConjAct g)
  rw [hΓ] at h1
  exact h1.trans h

end Subgroup

namespace ModularForm

open Subgroup

/-- Determinant-one passes to conjugates: if `Γ` has determinant one, so does any conjugate
`g • Γ` (the determinant is conjugation-invariant). -/
instance HasDetOne.conj {g : GL (Fin 2) ℝ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] :
    (ConjAct.toConjAct g • Γ).HasDetOne := by
  refine ⟨fun {x} hx ↦ ?_⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
  simpa [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, map_mul, mul_comm, mul_left_comm]
    using HasDetOne.det_eq hx

namespace CommIndex

variable {Γ₀ : Subgroup (GL (Fin 2) ℝ)}

/-- The conjugation action of a commensurator element on the index of the direct limit:
`g` sends the level `Γ` to the conjugate level `gΓg⁻¹`, which stays in the commensurability class. -/
def conj (g : GL (Fin 2) ℝ) (hg : g ∈ Commensurable.commensurator Γ₀) (i : CommIndex Γ₀) :
    CommIndex Γ₀ where
  carrier := ConjAct.toConjAct g • i.carrier
  commensurable := (i.commensurable.conj (ConjAct.toConjAct g)).trans
    ((Commensurable.commensurator_mem_iff Γ₀ g).mp hg)
  hasDetOne := HasDetOne.conj

@[simp] lemma conj_carrier (g : GL (Fin 2) ℝ) (hg : g ∈ Commensurable.commensurator Γ₀)
    (i : CommIndex Γ₀) : (conj g hg i).carrier = ConjAct.toConjAct g • i.carrier := rfl

end CommIndex

variable {k : ℤ}

open ConjAct Pointwise UpperHalfPlane in
/-- `ℝ`-linear translate for ANY `g ∈ GL(2,ℝ)` (either determinant sign): the slash action is
`σ`-semilinear and `σ` fixes `ℝ`, so it is `ℝ`-linear regardless of `det g`. The underlying function
is `⇑f ∣[k] g`. -/
noncomputable def translateℝ (g : GL (Fin 2) ℝ) {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] :
    ModularForm Γ k →ₗ[ℝ] ModularForm (toConjAct g⁻¹ • Γ) k where
  toFun f := ModularForm.translate f g
  map_add' f₁ f₂ := by
    ext z
    simp only [ModularForm.coe_translate, ModularForm.coe_add, SlashAction.add_slash, Pi.add_apply]
  map_smul' c f := by
    ext z
    simp only [RingHom.id_apply, ModularForm.coe_translate, ModularForm.coe_smul]
    have h : ((c • ⇑f : UpperHalfPlane → ℂ)) ∣[k] g = c • ((⇑f : UpperHalfPlane → ℂ) ∣[k] g) := by
      rw [← smul_one_smul ℂ c (⇑f : UpperHalfPlane → ℂ), smul_slash,
          ← smul_one_smul ℂ c ((⇑f : UpperHalfPlane → ℂ) ∣[k] g)]
      congr 1
      rw [Complex.real_smul, mul_one, σ_ofReal]
    exact congrFun h z

@[simp] lemma coe_translateℝ (g : GL (Fin 2) ℝ) {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    (f : ModularForm Γ k) : ⇑(translateℝ g f) = ⇑f ∣[k] g := rfl

end ModularForm

namespace ModularFormCommensurable

open ModularForm Subgroup

/-- The `ℝ`-vector-space structure on the limit, by restriction of scalars from its `ℂ`-structure
(via `algebraMap ℝ ℂ`). The negative-determinant part of the commensurator acts only `ℝ`-linearly,
so the representation lives over `ℝ`. -/
noncomputable instance instModuleReal (Γ₀ : Subgroup (GL (Fin 2) ℝ)) [Γ₀.HasDetPlusMinusOne]
    (k : ℤ) : Module ℝ (ModularFormCommensurable Γ₀ k) :=
  Module.compHom _ (algebraMap ℝ ℂ)

instance (Γ₀ : Subgroup (GL (Fin 2) ℝ)) [Γ₀.HasDetPlusMinusOne] (k : ℤ) :
    IsScalarTower ℝ ℂ (ModularFormCommensurable Γ₀ k) where
  smul_assoc r c m := by
    show (algebraMap ℝ ℂ r * c) • m = algebraMap ℝ ℂ r • (c • m)
    rw [mul_smul]

variable (Γ₀ : Subgroup (GL (Fin 2) ℝ)) [Γ₀.HasDetPlusMinusOne] (k : ℤ)

/-- The transition maps of the directed system, made `ℝ`-linear by restriction of scalars; the
underlying functions are unchanged. -/
private noncomputable def commTransitionℝ :
    ∀ i j : CommIndex Γ₀, i ≤ j → (ModularForm i.carrier k →ₗ[ℝ] ModularForm j.carrier k) :=
  fun _ _ h ↦ (restrictSubgroupₗ h).restrictScalars ℝ

/-- The same directed system rebuilt over `ℝ`. Auxiliary: only used to transport the `ℝ`-linear
universal property to the `ℂ`-built limit `ModularFormCommensurable Γ₀ k`. -/
private noncomputable abbrev limℝ : Type :=
  Module.DirectLimit (fun i : CommIndex Γ₀ ↦ ModularForm i.carrier k) (commTransitionℝ Γ₀ k)

/-- The canonical `ℝ`-linear map from the `ℝ`-built limit to the `ℂ`-built limit: it sends each
level-`i` piece to itself, with scalars restricted. -/
private noncomputable def fromLimℝ : limℝ Γ₀ k →ₗ[ℝ] ModularFormCommensurable Γ₀ k :=
  Module.DirectLimit.lift ℝ (CommIndex Γ₀) _ (commTransitionℝ Γ₀ k)
    (fun i ↦ (ofLevel Γ₀ k i).restrictScalars ℝ) (fun _ _ h x ↦ ofLevel_restrict Γ₀ k h x)

/-- The canonical `ℝ`-linear isomorphism between the `ℂ`-built limit and the `ℝ`-built limit: both
glue the same components along the same (scalar-restricted) transition maps. -/
private noncomputable def equivℝ : ModularFormCommensurable Γ₀ k ≃ₗ[ℝ] limℝ Γ₀ k :=
  (LinearEquiv.ofBijective (fromLimℝ Γ₀ k)
    ⟨Module.DirectLimit.lift_injective _ _ (fun i ↦ ofLevel_injective Γ₀ k i), fun y ↦ by
      obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of y
      exact ⟨Module.DirectLimit.of ℝ _ _ _ i x, Module.DirectLimit.lift_of _ _ _⟩⟩).symm

private lemma equivℝ_ofLevel (i : CommIndex Γ₀) (f : ModularForm i.carrier k) :
    equivℝ Γ₀ k (ofLevel Γ₀ k i f) = Module.DirectLimit.of ℝ _ _ _ i f := by
  rw [equivℝ, LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, fromLimℝ,
    Module.DirectLimit.lift_of]
  rfl

/-- The action of `g ∈ commensurator Γ₀` on the `ℝ`-built limit: on the level-`i` piece it
translates by `g⁻¹` into the conjugate level `g i g⁻¹`. Assembled via the `ℝ`-linear universal
property of `limℝ`. -/
private noncomputable def actℝ (g : ↥(Commensurable.commensurator Γ₀)) :
    limℝ Γ₀ k →ₗ[ℝ] ModularFormCommensurable Γ₀ k :=
  Module.DirectLimit.lift ℝ (CommIndex Γ₀) _ (commTransitionℝ Γ₀ k)
    (fun i ↦ (ofLevel Γ₀ k (CommIndex.conj g.1 g.2 i)).restrictScalars ℝ ∘ₗ translateℝ g.1⁻¹)
    (fun i j h x ↦ by
      have hconj : CommIndex.conj g.1 g.2 i ≤ CommIndex.conj g.1 g.2 j := by
        rw [CommIndex.le_def, CommIndex.conj_carrier, CommIndex.conj_carrier]
        exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (CommIndex.le_def.mp h)
      have hcomm : translateℝ g.1⁻¹ (restrictSubgroupₗ h x)
          = restrictSubgroupₗ hconj (translateℝ g.1⁻¹ x) := by ext z; rfl
      show ofLevel Γ₀ k (CommIndex.conj g.1 g.2 j) (translateℝ g.1⁻¹ (restrictSubgroupₗ h x))
          = ofLevel Γ₀ k (CommIndex.conj g.1 g.2 i) (translateℝ g.1⁻¹ x)
      rw [hcomm, ofLevel_restrict Γ₀ k hconj])

/-- The `ℝ`-linear action of `g ∈ commensurator Γ₀` on the direct limit: on the level-`i` piece it
translates by `g⁻¹` (an `ℝ`-linear map for any determinant) into the conjugate level `g i g⁻¹`. It is
assembled via the `ℝ`-linear universal property of `limℝ`, transported along `equivℝ`. -/
noncomputable def smulMap (g : ↥(Commensurable.commensurator Γ₀)) :
    ModularFormCommensurable Γ₀ k →ₗ[ℝ] ModularFormCommensurable Γ₀ k :=
  actℝ Γ₀ k g ∘ₗ (equivℝ Γ₀ k : ModularFormCommensurable Γ₀ k →ₗ[ℝ] limℝ Γ₀ k)

lemma smulMap_ofLevel (g : ↥(Commensurable.commensurator Γ₀)) (i : CommIndex Γ₀)
    (f : ModularForm i.carrier k) :
    smulMap Γ₀ k g (ofLevel Γ₀ k i f)
      = ofLevel Γ₀ k (CommIndex.conj g.1 g.2 i) (translateℝ g.1⁻¹ f) := by
  rw [smulMap, LinearMap.comp_apply, LinearEquiv.coe_coe, equivℝ_ofLevel, actℝ,
    Module.DirectLimit.lift_of]
  rfl

/-- The `ℂ`-linear inclusion of a single level into functions `ℍ → ℂ`. -/
def coeₗ {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] :
    ModularForm Γ k →ₗ[ℂ] (UpperHalfPlane → ℂ) where
  toFun f := ⇑f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma coeₗ_apply {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] (f : ModularForm Γ k) :
    coeₗ k f = ⇑f := rfl

/-- Induction principle for the limit phrased with `ofLevel` rather than the raw
`Module.DirectLimit.of` (to which it is definitionally equal). -/
@[elab_as_elim]
lemma ofLevel_induction {C : ModularFormCommensurable Γ₀ k → Prop}
    (z : ModularFormCommensurable Γ₀ k)
    (ih : ∀ (i : CommIndex Γ₀) (f : ModularForm i.carrier k), C (ofLevel Γ₀ k i f)) : C z :=
  Module.DirectLimit.induction_on z ih

/-- Every element of the limit comes from some level. -/
lemma exists_ofLevel (z : ModularFormCommensurable Γ₀ k) :
    ∃ (i : CommIndex Γ₀) (f : ModularForm i.carrier k), ofLevel Γ₀ k i f = z :=
  Module.DirectLimit.exists_of z

/-- The underlying-function map out of the limit: a form over the class restricts to an honest
function `ℍ → ℂ`. It is `ℂ`-linear and injective, and intertwines `smulMap g` with `· ∣[k] g⁻¹`. -/
noncomputable def toFunₗ : ModularFormCommensurable Γ₀ k →ₗ[ℂ] (UpperHalfPlane → ℂ) :=
  lift Γ₀ k (fun _ ↦ coeₗ k)
    (fun i j h x ↦ by simp only [coeₗ_apply, coe_restrictSubgroupₗ])

@[simp] lemma toFunₗ_ofLevel (i : CommIndex Γ₀) (f : ModularForm i.carrier k) :
    toFunₗ Γ₀ k (ofLevel Γ₀ k i f) = ⇑f := by
  unfold toFunₗ
  simp only [lift_ofLevel, coeₗ_apply]

lemma toFunₗ_injective : Function.Injective (toFunₗ Γ₀ k) := by
  unfold toFunₗ lift
  apply Module.DirectLimit.lift_injective
  intro i a b hab
  exact DFunLike.coe_injective hab

lemma toFunₗ_smulMap (g : ↥(Commensurable.commensurator Γ₀))
    (x : ModularFormCommensurable Γ₀ k) :
    toFunₗ Γ₀ k (smulMap Γ₀ k g x) = toFunₗ Γ₀ k x ∣[k] g.1⁻¹ := by
  induction x using ofLevel_induction with
  | ih i f => rw [smulMap_ofLevel, toFunₗ_ofLevel, toFunₗ_ofLevel]; rfl

lemma smulMap_one : smulMap Γ₀ k (1 : ↥(Commensurable.commensurator Γ₀)) = LinearMap.id := by
  ext x
  apply toFunₗ_injective
  simp only [toFunₗ_smulMap, LinearMap.id_coe, id_eq, OneMemClass.coe_one, inv_one,
    SlashAction.slash_one]

lemma smulMap_mul (g h : ↥(Commensurable.commensurator Γ₀)) :
    smulMap Γ₀ k (g * h) = smulMap Γ₀ k g ∘ₗ smulMap Γ₀ k h := by
  ext x
  apply toFunₗ_injective
  simp only [toFunₗ_smulMap, LinearMap.comp_apply, Subgroup.coe_mul, mul_inv_rev,
    SlashAction.slash_mul]

/-- The weight-`k` action of `commensurator Γ₀` on `ModularFormCommensurable Γ₀ k` as an `ℝ`-linear
representation: `g` acts by the slash action of `g⁻¹` (well-defined and `ℝ`-linear for any
determinant — the `σ`-twist by complex conjugation fixes `ℝ`), permuting the levels by conjugation.-/
noncomputable def commRep :
    Representation ℝ (↥(Commensurable.commensurator Γ₀)) (ModularFormCommensurable Γ₀ k) where
  toFun := smulMap Γ₀ k
  map_one' := smulMap_one Γ₀ k
  map_mul' := smulMap_mul Γ₀ k

@[simp] lemma commRep_apply (g : ↥(Commensurable.commensurator Γ₀)) :
    commRep Γ₀ k g = smulMap Γ₀ k g := rfl

omit [Γ₀.HasDetPlusMinusOne] in
/-- A level (a determinant-one subgroup commensurable with `Γ₀`) lies in the commensurator of `Γ₀`.-/
lemma carrier_le_commensurator (Γ : CommIndex Γ₀) :
    Γ.carrier ≤ Commensurable.commensurator Γ₀ :=
  Subgroup.commensurable_le_commensurator Γ.commensurable

omit [Γ₀.HasDetPlusMinusOne] in
/-- The inclusion of a level into the commensurator `commensurator Γ₀`. -/
noncomputable def levelIncl (Γ : CommIndex Γ₀) :
    Γ.carrier →* ↥(Commensurable.commensurator Γ₀) :=
  Subgroup.inclusion (carrier_le_commensurator Γ₀ Γ)

omit [Γ₀.HasDetPlusMinusOne] in
@[simp] lemma coe_levelIncl (Γ : CommIndex Γ₀) (γ : Γ.carrier) :
    ((levelIncl Γ₀ Γ γ : ↥(Commensurable.commensurator Γ₀)) : GL (Fin 2) ℝ) =
      (γ : GL (Fin 2) ℝ) := rfl

/-- **The level invariants of the commensurator action are the modular forms of that level.**

For a level `Γ` in the commensurability class, the image of `ModularForm Γ.carrier k` under `ofLevel`
(as an `ℝ`-submodule) is exactly the submodule of `ModularFormCommensurable Γ₀ k` fixed by the action
of all of `Γ.carrier` (restricted from the `commRep` action of `commensurator Γ₀`). -/
theorem range_ofLevel_eq_invariants (Γ : CommIndex Γ₀) :
    LinearMap.range ((ofLevel Γ₀ k Γ).restrictScalars ℝ)
      = Representation.invariants ((commRep Γ₀ k).comp (levelIncl Γ₀ Γ)) := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    rw [Representation.mem_invariants]
    intro γ
    change smulMap Γ₀ k (levelIncl Γ₀ Γ γ) (ofLevel Γ₀ k Γ f) = ofLevel Γ₀ k Γ f
    apply toFunₗ_injective
    rw [toFunₗ_smulMap, toFunₗ_ofLevel, coe_levelIncl]
    exact SlashInvariantForm.slash_action_eqn f _ (Γ.carrier.inv_mem γ.2)
  · intro x hx
    rw [Representation.mem_invariants] at hx
    obtain ⟨Λ, f, rfl⟩ := exists_ofLevel Γ₀ k x
    set Λ' : CommIndex Γ₀ :=
      ⟨Λ.carrier ⊓ Γ.carrier, Subgroup.commensurable_inf Λ.commensurable Γ.commensurable,
        inferInstance⟩
    have hΛΛ' : Λ ≤ Λ' := CommIndex.le_def.mpr inf_le_left
    have hΓΛ' : Γ ≤ Λ' := CommIndex.le_def.mpr inf_le_right
    have hcomm : Subgroup.Commensurable Λ.carrier Γ.carrier :=
      Λ.commensurable.trans Γ.commensurable.symm
    have key : ∀ g : Γ.carrier, (⇑f : UpperHalfPlane → ℂ) ∣[k] (g : GL (Fin 2) ℝ)⁻¹ = ⇑f := by
      intro g
      have h2 := congrArg (toFunₗ Γ₀ k) (hx g)
      rwa [MonoidHom.comp_apply, commRep_apply, toFunₗ_smulMap, toFunₗ_ofLevel, coe_levelIncl] at h2
    let F : ModularForm Γ.carrier k :=
      { toFun := ⇑f
        slash_action_eq' := fun δ hδ ↦ by
          simpa only [inv_inv] using key ⟨δ⁻¹, Γ.carrier.inv_mem hδ⟩
        holo' := f.holo'
        bdd_at_cusps' := fun {c} hc ↦
          f.bdd_at_cusps' ((Subgroup.Commensurable.isCusp_iff hcomm).mpr hc) }
    refine ⟨F, ?_⟩
    rw [LinearMap.restrictScalars_apply]
    have e1 : restrictSubgroupₗ hΓΛ' F = restrictSubgroupₗ hΛΛ' f := by ext z; rfl
    rw [← ofLevel_restrict Γ₀ k hΓΛ' F, e1]
    exact ofLevel_restrict Γ₀ k hΛΛ' f

/-- **Corollary.** `ModularForm Γ.carrier k` is `ℝ`-linearly isomorphic to the `Γ.carrier`-invariants
of the limit, via `ofLevel`. -/
noncomputable def ofLevelInvariantsEquiv (Γ : CommIndex Γ₀) :
    ModularForm Γ.carrier k ≃ₗ[ℝ]
      Representation.invariants ((commRep Γ₀ k).comp (levelIncl Γ₀ Γ)) :=
  (LinearEquiv.ofInjective ((ofLevel Γ₀ k Γ).restrictScalars ℝ) (ofLevel_injective Γ₀ k Γ)).trans
    (LinearEquiv.ofEq _ _ (range_ofLevel_eq_invariants Γ₀ k Γ))

end ModularFormCommensurable
