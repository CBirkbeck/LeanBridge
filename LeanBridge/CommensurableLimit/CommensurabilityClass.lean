/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.GroupTheory.Commensurable
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups

/-!
# The commensurability class of a subgroup as a directed index

Fix a subgroup `Γ₀ ≤ GL₂(ℝ)`. This file packages the subgroups commensurable with `Γ₀` that lie in
the determinant-one part as a **directed index type** `ModularForm.CommIndex Γ₀`, ordered by
*reverse* inclusion (`i ≤ j ↔ j.carrier ≤ i.carrier`).

This is the index over which `CommensurableLimit/DirectLimit.lean` forms the direct limit of the
spaces `ModularForm Γ k`: the transition map `Mₖ(Γ) → Mₖ(Γ′)` exists exactly when `Γ′ ≤ Γ`, so the
diagram is covariant for the reverse-inclusion order, and the class being closed under intersection
makes the index directed.

## Main definitions

* `ModularForm.CommIndex Γ₀` — a subgroup of `GL₂(ℝ)` commensurable with `Γ₀` and determinant-one,
  bundled with those two facts.

## Main results

* `Subgroup.HasDetOne.of_le` — `HasDetOne` is antitone: it passes to subgroups.
* `Subgroup.commensurable_inf` — the meet of two subgroups commensurable with `Γ₀` is commensurable
  with `Γ₀` (general base; the body mirrors `Subgroup.IsArithmetic.inter`).
* `Preorder`, `Nonempty` and `IsDirected` (reverse inclusion) instances on `CommIndex Γ₀`, making it
  a directed index for a direct limit.
-/

open scoped MatrixGroups

namespace Subgroup

/-- `HasDetOne` is antitone: a subgroup of a determinant-one subgroup is itself determinant-one.
(Mathlib only provides the `⊓` special cases; this is the general monotonicity.) -/
theorem HasDetOne.of_le {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    {Γ' Γ : Subgroup (GL n R)} (h : Γ' ≤ Γ) [Γ.HasDetOne] : Γ'.HasDetOne :=
  ⟨fun hg ↦ HasDetOne.det_eq (h hg)⟩

/-- The meet of two subgroups commensurable with a fixed `Γ₀` is again commensurable with `Γ₀`. -/
theorem commensurable_inf {G : Type*} [Group G] {Γ₁ Γ₂ Γ₀ : Subgroup G}
    (h₁ : Commensurable Γ₁ Γ₀) (h₂ : Commensurable Γ₂ Γ₀) :
    Commensurable (Γ₁ ⊓ Γ₂) Γ₀ := by
  refine ⟨relIndex_inf_ne_zero h₁.1 h₂.1, relIndex_ne_zero_trans (K := Γ₁) h₁.2 ?_⟩
  rw [relIndex_eq_one.mpr inf_le_left]
  exact one_ne_zero

end Subgroup

namespace ModularForm

open Subgroup

/-- Index type for the commensurability-class direct limit: a subgroup of `GL₂(ℝ)` that is
commensurable with `Γ₀` and lies in the determinant-one part, bundled with those facts.

Ordered by **reverse inclusion** (`i ≤ j ↔ j.carrier ≤ i.carrier`), so that the restriction maps of
the modular-form direct limit run in the direction of increasing `≤`. -/
structure CommIndex (Γ₀ : Subgroup (GL (Fin 2) ℝ)) where
  /-- the underlying subgroup -/
  carrier : Subgroup (GL (Fin 2) ℝ)
  /-- it is commensurable with the fixed base `Γ₀` -/
  commensurable : Commensurable carrier Γ₀
  /-- it lies in the determinant-one part of `GL₂(ℝ)` -/
  hasDetOne : carrier.HasDetOne

namespace CommIndex

variable {Γ₀ : Subgroup (GL (Fin 2) ℝ)}

/-- Every index carries the determinant-one structure of its underlying subgroup, so the spaces
`ModularForm i.carrier k` are `ℂ`-vector spaces. -/
instance (i : CommIndex Γ₀) : i.carrier.HasDetOne := i.hasDetOne

/-- Reverse-inclusion preorder: `i ≤ j` means `j.carrier ≤ i.carrier`. -/
instance : Preorder (CommIndex Γ₀) where
  le i j := j.carrier ≤ i.carrier
  le_refl i := le_refl i.carrier
  le_trans _ _ _ hij hjk := le_trans hjk hij

@[simp] lemma le_def {i j : CommIndex Γ₀} : i ≤ j ↔ j.carrier ≤ i.carrier := Iff.rfl

/-- The determinant-one part `Γ₀ ⊓ ker det` is a determinant-one subgroup commensurable with `Γ₀`
(when `Γ₀` has determinant `±1` its determinant maps onto a subgroup of `{±1}`, so the det-one part
has index ≤ 2), hence a valid index — so the class is nonempty. This subsumes the determinant-one
case via `HasDetOne → HasDetPlusMinusOne`. -/
instance [Γ₀.HasDetPlusMinusOne] : Nonempty (CommIndex Γ₀) := by
  refine ⟨⟨Γ₀ ⊓ (Matrix.GeneralLinearGroup.det).ker, ⟨?_, ?_⟩,
    ⟨fun {g} hg => MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hg).2⟩⟩⟩
  · have hsub : (Γ₀ ⊓ (Matrix.GeneralLinearGroup.det).ker).subgroupOf Γ₀
        = ((Matrix.GeneralLinearGroup.det).comp Γ₀.subtype).ker := by
      rw [Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf, MonoidHom.comap_ker]
    show ((Γ₀ ⊓ (Matrix.GeneralLinearGroup.det).ker).subgroupOf Γ₀).index ≠ 0
    rw [hsub, Subgroup.index_ker]
    have hfin : (((Matrix.GeneralLinearGroup.det).comp Γ₀.subtype).range : Set ℝˣ) ⊆ {1, -1} := by
      rintro x ⟨g, rfl⟩
      simpa using HasDetPlusMinusOne.det_eq g.2
    have : Finite ((Matrix.GeneralLinearGroup.det).comp Γ₀.subtype).range :=
      (Set.Finite.subset ((Set.finite_singleton (-1 : ℝˣ)).insert 1) hfin).to_subtype
    exact Nat.card_ne_zero.mpr ⟨⟨1, one_mem _⟩, this⟩
  · rw [Subgroup.relIndex_eq_one.mpr inf_le_left]; exact one_ne_zero

/-- The commensurability class is directed under reverse inclusion: two indices have their meet as a
common upper bound (it is commensurable with `Γ₀` and determinant-one). -/
instance : IsDirected (CommIndex Γ₀) (· ≤ ·) where
  directed i j :=
    ⟨⟨i.carrier ⊓ j.carrier, commensurable_inf i.commensurable j.commensurable, inferInstance⟩,
      le_def.mpr inf_le_left, le_def.mpr inf_le_right⟩

/-- `Module.DirectLimit` needs decidable equality on the index; subgroup equality is not decidable,
so we use the classical instance. -/
noncomputable instance : DecidableEq (CommIndex Γ₀) := Classical.decEq _

end CommIndex

end ModularForm
