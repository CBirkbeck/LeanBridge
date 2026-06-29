/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.GroupTheory.Commensurable
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Data.Finsupp.Pointwise

/-!
# Hecke rings: definition

The abstract Hecke ring, following Shimura, *Introduction to the Arithmetic Theory of
Automorphic Functions*, Ch. 3.

This file contains only the core **definitions**:

* `HeckeRing.HeckePair` — an arithmetic pair `(H, Δ)` with `H ≤ Δ ≤ commensurator(H)`;
* `HeckeRing.HeckeCoset` — the double-coset quotient `Δ / (HgH = HhH)`, the basis of the ring;
* `HeckeRing.𝕋` — the Hecke ring itself, formal `Z`-linear combinations of double cosets.

The ring operations (convolution product) and their properties are intentionally **not**
included here; they will be added in follow-up work.

Ported from the AINTLIB project
(`projects/LeanModularForms/LeanModularForms/HeckeRIngs/AbstractHeckeRing/Basic.lean`).
-/

open Set DoubleCoset Subgroup Subgroup.Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G]

/-- An arithmetic group pair `(H, Δ)` consisting of a subgroup `H` and a submonoid `Δ`
of a group `G`, satisfying `H ≤ Δ ≤ commensurator(H)`. -/
@[ext]
structure HeckePair (G : Type*) [Group G] where
  H : Subgroup G
  Δ : Submonoid G
  h₀ : H.toSubmonoid ≤ Δ
  h₁ : Δ ≤ (commensurator H).toSubmonoid

/-- Two elements of `Δ` define the same double coset `HgH = HhH`. -/
def dcRel (P : HeckePair G) (g h : P.Δ) : Prop :=
  DoubleCoset.doubleCoset (g : G) P.H P.H = DoubleCoset.doubleCoset (h : G) P.H P.H

/-- The setoid on `Δ` identifying elements with the same double coset. -/
instance dcSetoid (P : HeckePair G) : Setoid P.Δ where
  r := dcRel P
  iseqv := ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩

/-- A Hecke double coset: an equivalence class of `Δ`-elements under `HgH = HhH`.
    This is the basis type for the Hecke ring. -/
def HeckeCoset (P : HeckePair G) := Quotient (dcSetoid P)

noncomputable instance instDecidableEqHeckeCoset (P : HeckePair G) :
    DecidableEq (HeckeCoset P) := Classical.decEq _

/-- The Hecke ring type: formal `Z`-linear combinations of double cosets `HeckeCoset P`. -/
def 𝕋 (P : HeckePair G) (Z : Type*) [CommRing Z] := Finsupp (HeckeCoset P) Z

/-- `FunLike` instance for `𝕋 P Z`: treat elements as functions `HeckeCoset P → Z`. -/
instance instFunLike𝕋 (P : HeckePair G) (Z : Type*) [CommRing Z] :
    FunLike (𝕋 P Z) (HeckeCoset P) Z :=
  inferInstanceAs (FunLike (HeckeCoset P →₀ Z) (HeckeCoset P) Z)

/-- The additive commutative group structure on the Hecke ring. -/
noncomputable instance instAddCommGroup𝕋 (P : HeckePair G) (Z : Type*) [CommRing Z] :
    AddCommGroup (𝕋 P Z) :=
  inferInstanceAs (AddCommGroup ((HeckeCoset P) →₀ Z))

end HeckeRing
