import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic.Group

/-!
# Isoclinism

For a group `G` with centre `Z(G)` and commutator subgroup `G'`, the map
`ω_G(x, y) = x⁻¹ y⁻¹ x y` from `G × G` to `G'` descends to `G / Z(G) × G / Z(G)`. An isoclinism
between `G₁` and `G₂` is a pair of isomorphisms `φ : G₁ / Z(G₁) ≃* G₂ / Z(G₂)` and
`σ : G₁' ≃* G₂'` with `σ ∘ ω_{G₁} = ω_{G₂} ∘ (φ × φ)`. Being isoclinic is an equivalence
relation.

The LMFDB's convention `x⁻¹ y⁻¹ x y` for the commutator differs from Mathlib's
`⁅x, y⁆ = x y x⁻¹ y⁻¹`; we follow the LMFDB (`Group.commutatorPairing x y = ⁅x⁻¹, y⁻¹⁆`). Since
`φ` is a homomorphism the two conventions give the same isoclinisms.

## Main definitions

* `Group.commutatorPairing`: the commutator `x⁻¹ y⁻¹ x y` as an element of `G'`.
* `Group.centralCommutatorMap` (LMFDB `group.isoclinism`): its descent `ω_G` to
  `G / Z(G) × G / Z(G)`.
* `Group.Isoclinism` (LMFDB `group.isoclinism`): the isoclinisms between two groups.
* `Group.IsIsoclinic` (LMFDB `group.isoclinism`): two groups are isoclinic.

## Main results

* `Group.IsIsoclinic.refl`, `Group.IsIsoclinic.symm`, `Group.IsIsoclinic.trans`: being isoclinic
  is an equivalence relation.
-/

open Subgroup

namespace Group

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- The commutator `x⁻¹ y⁻¹ x y` of two elements of a group `G`, as an element of its commutator
subgroup `G'` (LMFDB convention; it is Mathlib's `⁅x⁻¹, y⁻¹⁆`). -/
def commutatorPairing (x y : G) : commutator G :=
  ⟨x⁻¹ * y⁻¹ * x * y, by
    rw [commutator_def]
    simpa [commutatorElement_def] using commutator_mem_commutator (mem_top x⁻¹) (mem_top y⁻¹)⟩

lemma coe_commutatorPairing (x y : G) : (commutatorPairing x y : G) = x⁻¹ * y⁻¹ * x * y :=
  rfl

lemma inv_mul_mul_eq_of_mem_center {z : G} (hz : z ∈ center G) (g : G) : z⁻¹ * g * z = g := by
  rw [mul_assoc, mem_center_iff.mp hz g, inv_mul_cancel_left]

lemma commutatorPairing_mul_mul (a c : G) {z w : G} (hz : z ∈ center G) (hw : w ∈ center G) :
    commutatorPairing (a * z) (c * w) = commutatorPairing a c := by
  have h₁ : (a * z)⁻¹ * (c * w)⁻¹ * (a * z) * (c * w) =
      z⁻¹ * (a⁻¹ * (c * w)⁻¹ * a) * z * (c * w) := by
    group
  have h₂ : a⁻¹ * (w * c)⁻¹ * a * (w * c) = a⁻¹ * c⁻¹ * (w⁻¹ * a * w) * c := by
    group
  refine Subtype.ext ?_
  rw [coe_commutatorPairing, coe_commutatorPairing, h₁, inv_mul_mul_eq_of_mem_center hz,
    mem_center_iff.mp hw c, h₂, inv_mul_mul_eq_of_mem_center hw]

variable (G) in
/-- The commutator map `ω_G : G / Z(G) × G / Z(G) → G'`, `(x, y) ↦ x⁻¹ y⁻¹ x y`, well defined
since the commutator only depends on its arguments modulo the centre (LMFDB `group.isoclinism`). -/
def centralCommutatorMap : G ⧸ center G → G ⧸ center G → commutator G :=
  Quotient.lift₂ commutatorPairing fun a₁ a₂ b₁ b₂ h₁ h₂ =>
    (commutatorPairing_mul_mul a₁ a₂ (QuotientGroup.leftRel_apply.mp h₁)
      (QuotientGroup.leftRel_apply.mp h₂)).symm.trans <|
        congrArg₂ commutatorPairing (mul_inv_cancel_left a₁ b₁) (mul_inv_cancel_left a₂ b₂)

lemma centralCommutatorMap_mk (x y : G) :
    centralCommutatorMap G x y = commutatorPairing x y :=
  rfl

variable (G H) in
/-- An **isoclinism** between groups `G` and `H` (LMFDB `group.isoclinism`): isomorphisms
`φ : G / Z(G) ≃* H / Z(H)` and `σ : G' ≃* H'` such that `σ (ω_G (x, y)) = ω_H (φ x, φ y)`. -/
structure Isoclinism where
  /-- The isomorphism `φ` of the central quotients. -/
  centralQuotientEquiv : G ⧸ center G ≃* H ⧸ center H
  /-- The isomorphism `σ` of the commutator subgroups. -/
  commutatorEquiv : commutator G ≃* commutator H
  /-- The compatibility `σ ∘ ω_G = ω_H ∘ (φ × φ)`. -/
  map_centralCommutatorMap (x y : G ⧸ center G) : commutatorEquiv (centralCommutatorMap G x y) =
    centralCommutatorMap H (centralQuotientEquiv x) (centralQuotientEquiv y)

variable (G H) in
/-- Two groups are **isoclinic** if there is an isoclinism between them (LMFDB
`group.isoclinism`). -/
def IsIsoclinic : Prop :=
  Nonempty (Isoclinism G H)

namespace Isoclinism

variable (G) in
/-- The identity isoclinism. -/
def refl : Isoclinism G G :=
  ⟨.refl _, .refl _, fun _ _ => rfl⟩

/-- The inverse of an isoclinism. -/
def symm (e : Isoclinism G H) : Isoclinism H G :=
  ⟨e.centralQuotientEquiv.symm, e.commutatorEquiv.symm, fun x y =>
    e.commutatorEquiv.symm_apply_eq.mpr <| by
      rw [e.map_centralCommutatorMap, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]⟩

/-- The composition of two isoclinisms. -/
def trans (e : Isoclinism G H) (f : Isoclinism H K) : Isoclinism G K :=
  ⟨e.centralQuotientEquiv.trans f.centralQuotientEquiv, e.commutatorEquiv.trans f.commutatorEquiv,
    fun x y => by
      rw [MulEquiv.trans_apply, e.map_centralCommutatorMap, f.map_centralCommutatorMap]
      rfl⟩

end Isoclinism

variable (G) in
/-- **Being isoclinic is reflexive.** -/
lemma IsIsoclinic.refl : IsIsoclinic G G :=
  ⟨.refl G⟩

/-- **Being isoclinic is symmetric.** -/
lemma IsIsoclinic.symm (h : IsIsoclinic G H) : IsIsoclinic H G :=
  h.map Isoclinism.symm

/-- **Being isoclinic is transitive.** -/
lemma IsIsoclinic.trans (h : IsIsoclinic G H) (h' : IsIsoclinic H K) : IsIsoclinic G K :=
  h.elim fun e => h'.map e.trans

end Group
