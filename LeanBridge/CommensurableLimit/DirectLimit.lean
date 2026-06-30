/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanBridge.CommensurableLimit.CommensurabilityClass
import Mathlib.Algebra.Colimit.Module
import Mathlib.NumberTheory.ModularForms.Basic

/-!
# Modular forms of weight `k` over a commensurability class, as a direct limit

Fix `Γ₀ ≤ GL₂(ℝ)` with `det = ±1`. For each determinant-one subgroup `Γ` commensurable with `Γ₀` we have the space `ModularForm Γ k`, and for `Γ′ ≤ Γ` the restriction map
`ModularForm Γ k → ModularForm Γ′ k` (a form invariant under the bigger group is invariant under the
smaller one). Indexed by `ModularForm.CommIndex Γ₀` under reverse inclusion — a directed poset —
this is a directed system of `ℂ`-vector spaces, and we define

`ModularFormCommensurable Γ₀ k` := its `Module.DirectLimit`.

For `Γ₀ = 𝒮ℒ` (the image of `SL₂(ℤ)`) this is the space of modular forms of weight `k` for *some*
group commensurable with `SL₂(ℤ)` — the natural space on which the commensurator (Hecke) action
lives; see `ModularFormArithmetic`.

## Main definitions

* `ModularForm.restrictSubgroupₗ` — restriction along `Γ′ ≤ Γ` as a `ℂ`-linear map.
* `ModularFormCommensurable Γ₀ k` — the direct limit; an `AddCommGroup` and a `Module ℂ`.
* `ModularFormCommensurable.ofLevel` — the canonical map of each level into the limit.
* `ModularFormCommensurable.lift` — the universal property out of the limit.
* `ModularFormArithmetic k` — the headline instance at `Γ₀ = 𝒮ℒ`.

## Main results

* `ModularFormCommensurable.ofLevel_restrict` — compatibility of `ofLevel` with restriction.
* `ModularFormCommensurable.ofLevel_injective` — each level embeds into the limit.
* `ModularFormCommensurable.lift_ofLevel` — computation rule for `lift`.
-/

open scoped MatrixGroups

namespace ModularForm

variable {k : ℤ}

/-- Restriction of a modular form along a subgroup inclusion `Γ′ ≤ Γ`, as a `ℂ`-linear map.

The unbundled version is `ModularForm.restrictSubgroup`
(`LeanModularForms/HeckeRIngs/GL2/LevelRaise.lean`); this is its `ℂ`-linear packaging, reproduced
here so the direct-limit construction depends only on mathlib. The underlying function is unchanged,
so additivity and `ℂ`-homogeneity are definitional. -/
def restrictSubgroupₗ {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] [Γ'.HasDetOne]
    (h : Γ' ≤ Γ) : ModularForm Γ k →ₗ[ℂ] ModularForm Γ' k where
  toFun f :=
    { toFun := f.toFun
      slash_action_eq' := fun γ hγ ↦ f.slash_action_eq' γ (h hγ)
      holo' := f.holo'
      bdd_at_cusps' := fun hc ↦ f.bdd_at_cusps' (hc.mono h) }
  map_add' f g := by ext z; rfl
  map_smul' c f := by ext z; rfl

@[simp]
lemma coe_restrictSubgroupₗ {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] [Γ'.HasDetOne]
    (h : Γ' ≤ Γ) (f : ModularForm Γ k) : ⇑(restrictSubgroupₗ h f) = ⇑f := rfl

lemma restrictSubgroupₗ_injective {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] [Γ'.HasDetOne]
    (h : Γ' ≤ Γ) : Function.Injective (restrictSubgroupₗ (k := k) h) := by
  intro f g hfg
  ext z
  simpa using DFunLike.congr_fun hfg z

end ModularForm

open ModularForm

/-- The transition maps of the commensurability-class directed system: for `i ≤ j` (i.e.
`j.carrier ≤ i.carrier`), restriction `ModularForm i.carrier k → ModularForm j.carrier k`. -/
noncomputable def commTransition (Γ₀ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) :
    ∀ i j : CommIndex Γ₀, i ≤ j → (ModularForm i.carrier k →ₗ[ℂ] ModularForm j.carrier k) :=
  fun _ _ h ↦ ModularForm.restrictSubgroupₗ h

/-- The restriction maps form a directed system (each is the identity on underlying functions). -/
instance commDirectedSystem (Γ₀ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) :
    DirectedSystem (fun i : CommIndex Γ₀ ↦ ModularForm i.carrier k)
      (fun i j h ↦ (commTransition Γ₀ k i j h :
        ModularForm i.carrier k → ModularForm j.carrier k)) where
  map_self := by intros; ext z; rfl
  map_map := by intros; ext z; rfl

/-- **Modular forms of weight `k` over the commensurability class of `Γ₀`**, defined as the direct
limit of `ModularForm Γ k` over all determinant-one subgroups `Γ` commensurable with `Γ₀`, ordered
by reverse inclusion with restriction as the transition maps. -/
noncomputable def ModularFormCommensurable (Γ₀ : Subgroup (GL (Fin 2) ℝ)) [Γ₀.HasDetPlusMinusOne]
    (k : ℤ) : Type :=
  Module.DirectLimit (fun i : CommIndex Γ₀ ↦ ModularForm i.carrier k) (commTransition Γ₀ k)

namespace ModularFormCommensurable

noncomputable instance (Γ₀ : Subgroup (GL (Fin 2) ℝ)) [Γ₀.HasDetPlusMinusOne] (k : ℤ) :
    AddCommGroup (ModularFormCommensurable Γ₀ k) :=
  inferInstanceAs (AddCommGroup
    (Module.DirectLimit (fun i : CommIndex Γ₀ ↦ ModularForm i.carrier k) (commTransition Γ₀ k)))

noncomputable instance (Γ₀ : Subgroup (GL (Fin 2) ℝ)) [Γ₀.HasDetPlusMinusOne] (k : ℤ) :
    Module ℂ (ModularFormCommensurable Γ₀ k) :=
  inferInstanceAs (Module ℂ
    (Module.DirectLimit (fun i : CommIndex Γ₀ ↦ ModularForm i.carrier k) (commTransition Γ₀ k)))

variable (Γ₀ : Subgroup (GL (Fin 2) ℝ)) [Γ₀.HasDetPlusMinusOne] (k : ℤ)

/-- The canonical `ℂ`-linear map of the level-`i` modular forms into the direct limit. -/
noncomputable def ofLevel (i : CommIndex Γ₀) :
    ModularForm i.carrier k →ₗ[ℂ] ModularFormCommensurable Γ₀ k :=
  Module.DirectLimit.of ℂ (CommIndex Γ₀) (fun i ↦ ModularForm i.carrier k) (commTransition Γ₀ k) i

/-- `ofLevel` is compatible with restriction: restricting to a finer level then including agrees
with including directly. -/
@[simp]
lemma ofLevel_restrict {i j : CommIndex Γ₀} (h : i ≤ j) (f : ModularForm i.carrier k) :
    ofLevel Γ₀ k j (restrictSubgroupₗ h f) = ofLevel Γ₀ k i f :=
  Module.DirectLimit.of_f

/-- Each level embeds into the direct limit: `ofLevel` is injective. -/
lemma ofLevel_injective (i : CommIndex Γ₀) : Function.Injective (ofLevel Γ₀ k i) := by
  intro x y hxy
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.exists_eq_of_of_eq hxy
  exact restrictSubgroupₗ_injective hij hj

/-- **Universal property**: a family of `ℂ`-linear maps `gᵢ : ModularForm i.carrier k → P` that is
compatible with restriction factors (uniquely) through the direct limit. -/
noncomputable def lift {P : Type*} [AddCommGroup P] [Module ℂ P]
    (g : ∀ i : CommIndex Γ₀, ModularForm i.carrier k →ₗ[ℂ] P)
    (Hg : ∀ (i j : CommIndex Γ₀) (h : i ≤ j) (x : ModularForm i.carrier k),
      g j (restrictSubgroupₗ h x) = g i x) :
    ModularFormCommensurable Γ₀ k →ₗ[ℂ] P :=
  Module.DirectLimit.lift ℂ (CommIndex Γ₀) (fun i ↦ ModularForm i.carrier k) (commTransition Γ₀ k)
    g Hg

@[simp]
lemma lift_ofLevel {P : Type*} [AddCommGroup P] [Module ℂ P]
    (g : ∀ i : CommIndex Γ₀, ModularForm i.carrier k →ₗ[ℂ] P)
    (Hg : ∀ (i j : CommIndex Γ₀) (h : i ≤ j) (x : ModularForm i.carrier k),
      g j (restrictSubgroupₗ h x) = g i x)
    (i : CommIndex Γ₀) (x : ModularForm i.carrier k) :
    lift Γ₀ k g Hg (ofLevel Γ₀ k i x) = g i x :=
  Module.DirectLimit.lift_of _ _ _

end ModularFormCommensurable

/-- **Modular forms of weight `k` over the commensurability class of `SL₂(ℤ)`** (i.e. `Γ₀ = 𝒮ℒ`, the
image of `SL₂(ℤ)` in `GL₂(ℝ)`). The indexing class is exactly the determinant-one subgroups `Γ` with
`Subgroup.IsArithmetic Γ`. -/
noncomputable abbrev ModularFormArithmetic (k : ℤ) : Type :=
  ModularFormCommensurable 𝒮ℒ k
