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
action (a `g` sends the level-`Γ` piece to the level-`gΓg⁻¹` piece via `f ↦ f ∣[k] g⁻¹`). Because the
slash action is `ℂ`-linear only in positive determinant, the acting group is the positive-determinant
part `PComm Γ₀ := commensurator Γ₀ ⊓ GL(2,ℝ)⁺`. We prove that the `Γ`-invariants of the limit are
exactly `ModularForm Γ k` (the image of `ofLevel Γ`).

## Main definitions

* `ModularForm.PComm` — the positive-determinant part of the commensurator of `Γ₀` (the acting
  group).
* `ModularForm.CommIndex.conj` — the conjugation action of a commensurator element on the index.
* `ModularForm.translateₗ` — slash by a positive-determinant `g` as a `ℂ`-linear map
  `ModularForm Γ k → ModularForm (g⁻¹Γg) k`.
* `ModularFormCommensurable.smulMap` — the action of `g ∈ PComm Γ₀` on the direct limit.
* `ModularFormCommensurable.toFunₗ` — the injective `ℂ`-linear map from the limit to functions
  `ℍ → ℂ`.
* `ModularFormCommensurable.commRep` — the weight-`k` representation of `PComm Γ₀` on the limit.
* `ModularFormCommensurable.ofLevelInvariantsEquiv` — the `ℂ`-linear isomorphism of
  `ModularForm Γ.carrier k` with the level invariants.

## Main results

* `Subgroup.commensurable_le_commensurator` — a subgroup commensurable with `Γ₀` lies in its
  commensurator.
* `ModularFormCommensurable.range_ofLevel_eq_invariants` — the level-`Γ` invariants of the
  commensurator action are exactly the image of `ModularForm Γ.carrier k` under `ofLevel`.
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

/-- The acting group of the commensurator action: the positive-determinant part of the commensurator
of `Γ₀`. (Positive determinant is exactly where the slash action is `ℂ`-linear.) -/
noncomputable def PComm (Γ₀ : Subgroup (GL (Fin 2) ℝ)) : Subgroup (GL (Fin 2) ℝ) :=
  Commensurable.commensurator Γ₀ ⊓ Matrix.GLPos (Fin 2) ℝ

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

/-- `σ g = id` for positive-determinant `g`, by unfolding `UpperHalfPlane.σ`
(`if 0 < det then refl else conj`); this is where the slash action is `ℂ`-linear. -/
private lemma sigma_eq_refl_of_pos_det {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    UpperHalfPlane.σ g = ContinuousAlgEquiv.refl ℝ ℂ := if_pos hg

variable {k : ℤ}

/-- Translation by `g` (slash by `g`) as a `ℂ`-linear map
`ModularForm Γ k → ModularForm (g⁻¹Γg) k`, for positive-determinant `g` (where the slash action is
`ℂ`-linear, the `σ`-twist being trivial). The underlying function is `⇑f ∣[k] g`. -/
noncomputable def translateₗ (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val)
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] :
    ModularForm Γ k →ₗ[ℂ] ModularForm (ConjAct.toConjAct g⁻¹ • Γ) k where
  toFun f := ModularForm.translate f g
  map_add' f₁ f₂ := by
    ext z
    simp only [ModularForm.coe_translate, ModularForm.coe_add, SlashAction.add_slash, Pi.add_apply]
  map_smul' c f := by
    ext z
    change (⇑(c • f) ∣[k] g) z = c • ((⇑f ∣[k] g) z)
    simp only [show (⇑(c • f) : UpperHalfPlane → ℂ) = c • ⇑f from rfl,
      ModularForm.smul_slash, sigma_eq_refl_of_pos_det hg, ContinuousAlgEquiv.refl_apply,
      Pi.smul_apply, smul_eq_mul]

@[simp] lemma coe_translateₗ (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val)
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] (f : ModularForm Γ k) :
    ⇑(translateₗ g hg f) = ⇑f ∣[k] g := rfl

private lemma det_inv_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) : 0 < (g⁻¹).det.val := by
  rwa [map_inv, Units.val_inv_eq_inv_val, inv_pos]

variable {Γ₀ : Subgroup (GL (Fin 2) ℝ)}

/-- An element of `PComm Γ₀` lies in the commensurator of `Γ₀`. -/
lemma mem_commensurator_of_mem_PComm (g : ↥(PComm Γ₀)) :
    (g : GL (Fin 2) ℝ) ∈ Commensurable.commensurator Γ₀ :=
  (Subgroup.mem_inf.mp g.2).1

/-- An element of `PComm Γ₀` has positive determinant. -/
lemma det_pos_of_mem_PComm (g : ↥(PComm Γ₀)) : 0 < (g : GL (Fin 2) ℝ).det.val :=
  (Matrix.mem_glpos _).mp (Subgroup.mem_inf.mp g.2).2

end ModularForm

namespace ModularFormCommensurable

open ModularForm

variable (Γ₀ : Subgroup (GL (Fin 2) ℝ)) [Γ₀.HasDetOne] (k : ℤ)

/-- The action of `g ∈ PComm Γ₀` on the direct limit: on the level-`i` piece it translates by `g⁻¹`
(a `ℂ`-linear map, as `g` has positive determinant) into the conjugate level `g i g⁻¹`. -/
noncomputable def smulMap (g : ↥(PComm Γ₀)) :
    ModularFormCommensurable Γ₀ k →ₗ[ℂ] ModularFormCommensurable Γ₀ k :=
  lift Γ₀ k
    (fun i ↦ (ofLevel Γ₀ k (CommIndex.conj g.1 (mem_commensurator_of_mem_PComm g) i)).comp
      (translateₗ g.1⁻¹ (det_inv_pos (det_pos_of_mem_PComm g))))
    (fun i j h x ↦ by
      have hconj : CommIndex.conj g.1 (mem_commensurator_of_mem_PComm g) i
          ≤ CommIndex.conj g.1 (mem_commensurator_of_mem_PComm g) j := by
        rw [CommIndex.le_def, CommIndex.conj_carrier, CommIndex.conj_carrier]
        exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (CommIndex.le_def.mp h)
      have hcomm : translateₗ g.1⁻¹ (det_inv_pos (det_pos_of_mem_PComm g)) (restrictSubgroupₗ h x)
          = restrictSubgroupₗ hconj
              (translateₗ g.1⁻¹ (det_inv_pos (det_pos_of_mem_PComm g)) x) := by
        ext z; rfl
      simp only [LinearMap.comp_apply]
      exact (congrArg (ofLevel Γ₀ k (CommIndex.conj g.1 (mem_commensurator_of_mem_PComm g) j))
        hcomm).trans
        (ofLevel_restrict Γ₀ k hconj
          (translateₗ g.1⁻¹ (det_inv_pos (det_pos_of_mem_PComm g)) x)))

lemma smulMap_ofLevel (g : ↥(PComm Γ₀)) (i : CommIndex Γ₀) (f : ModularForm i.carrier k) :
    smulMap Γ₀ k g (ofLevel Γ₀ k i f)
      = ofLevel Γ₀ k (CommIndex.conj g.1 (mem_commensurator_of_mem_PComm g) i)
          (translateₗ g.1⁻¹ (det_inv_pos (det_pos_of_mem_PComm g)) f) :=
  lift_ofLevel Γ₀ k _ _ i f

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

lemma toFunₗ_smulMap (g : ↥(PComm Γ₀)) (x : ModularFormCommensurable Γ₀ k) :
    toFunₗ Γ₀ k (smulMap Γ₀ k g x) = toFunₗ Γ₀ k x ∣[k] g.1⁻¹ := by
  induction x using ofLevel_induction with
  | ih i f => rw [smulMap_ofLevel, toFunₗ_ofLevel, toFunₗ_ofLevel]; rfl

lemma smulMap_one : smulMap Γ₀ k (1 : ↥(PComm Γ₀)) = LinearMap.id := by
  ext x
  apply toFunₗ_injective
  simp only [toFunₗ_smulMap, LinearMap.id_coe, id_eq, OneMemClass.coe_one, inv_one,
    SlashAction.slash_one]

lemma smulMap_mul (g h : ↥(PComm Γ₀)) :
    smulMap Γ₀ k (g * h) = smulMap Γ₀ k g ∘ₗ smulMap Γ₀ k h := by
  ext x
  apply toFunₗ_injective
  simp only [toFunₗ_smulMap, LinearMap.comp_apply, Subgroup.coe_mul, mul_inv_rev,
    SlashAction.slash_mul]

/-- The weight-`k` action of `PComm Γ₀` on `ModularFormCommensurable Γ₀ k` as a `ℂ`-linear
representation: `g` acts by the slash action of `g⁻¹` (well-defined and `ℂ`-linear because `g` has
positive determinant), permuting the levels by conjugation. -/
noncomputable def commRep : Representation ℂ (↥(PComm Γ₀)) (ModularFormCommensurable Γ₀ k) where
  toFun := smulMap Γ₀ k
  map_one' := smulMap_one Γ₀ k
  map_mul' := smulMap_mul Γ₀ k

@[simp] lemma commRep_apply (g : ↥(PComm Γ₀)) : commRep Γ₀ k g = smulMap Γ₀ k g := rfl

omit [Γ₀.HasDetOne] in
/-- A level (a determinant-one subgroup commensurable with `Γ₀`) lies in the acting group
`PComm Γ₀` — it is in the commensurator and, being determinant-one, has positive determinant. -/
lemma carrier_le_PComm (Γ : CommIndex Γ₀) : Γ.carrier ≤ PComm Γ₀ := by
  refine le_inf (Subgroup.commensurable_le_commensurator Γ.commensurable) (fun γ hγ ↦ ?_)
  rw [Matrix.mem_glpos, show (γ.det : ℝˣ) = 1 from Subgroup.HasDetOne.det_eq hγ, Units.val_one]
  exact one_pos

omit [Γ₀.HasDetOne] in
/-- The inclusion of a level into the acting group `PComm Γ₀`. -/
noncomputable def levelIncl (Γ : CommIndex Γ₀) : Γ.carrier →* ↥(PComm Γ₀) :=
  Subgroup.inclusion (carrier_le_PComm Γ₀ Γ)

omit [Γ₀.HasDetOne] in
@[simp] lemma coe_levelIncl (Γ : CommIndex Γ₀) (γ : Γ.carrier) :
    ((levelIncl Γ₀ Γ γ : ↥(PComm Γ₀)) : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) := rfl

/-- **The level invariants of the commensurator action are the modular forms of that level.**

For a level `Γ` in the commensurability class, the image of `ModularForm Γ.carrier k` under `ofLevel`
is exactly the submodule of `ModularFormCommensurable Γ₀ k` fixed by the action of all of `Γ.carrier`
(restricted from the `commRep` action of `PComm Γ₀`). -/
theorem range_ofLevel_eq_invariants (Γ : CommIndex Γ₀) :
    LinearMap.range (ofLevel Γ₀ k Γ)
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
      rwa [MonoidHom.comp_apply, commRep_apply, toFunₗ_smulMap, toFunₗ_ofLevel,
        coe_levelIncl] at h2
    let F : ModularForm Γ.carrier k :=
      { toFun := ⇑f
        slash_action_eq' := fun δ hδ ↦ by
          simpa only [inv_inv] using key ⟨δ⁻¹, Γ.carrier.inv_mem hδ⟩
        holo' := f.holo'
        bdd_at_cusps' := fun {c} hc ↦
          f.bdd_at_cusps' ((Subgroup.Commensurable.isCusp_iff hcomm).mpr hc) }
    refine ⟨F, ?_⟩
    have e1 : restrictSubgroupₗ hΓΛ' F = restrictSubgroupₗ hΛΛ' f := by ext z; rfl
    rw [← ofLevel_restrict Γ₀ k hΓΛ' F, e1]
    exact ofLevel_restrict Γ₀ k hΛΛ' f

/-- **Corollary.** `ModularForm Γ.carrier k` is `ℂ`-linearly isomorphic to the `Γ.carrier`-invariants
of the limit, via `ofLevel`. -/
noncomputable def ofLevelInvariantsEquiv (Γ : CommIndex Γ₀) :
    ModularForm Γ.carrier k ≃ₗ[ℂ]
      Representation.invariants ((commRep Γ₀ k).comp (levelIncl Γ₀ Γ)) :=
  (LinearEquiv.ofInjective (ofLevel Γ₀ k Γ) (ofLevel_injective Γ₀ k Γ)).trans
    (LinearEquiv.ofEq _ _ (range_ofLevel_eq_invariants Γ₀ k Γ))

end ModularFormCommensurable
