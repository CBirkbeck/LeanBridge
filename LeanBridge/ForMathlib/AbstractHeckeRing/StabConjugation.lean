/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanBridge.ForMathlib.AbstractHeckeRing.Multiplication

/-!
# Stabilizer invariance and conjugation equivalences on `decompQuot`

For an abstract `HeckePair P`:

* Right multiplication by `h ∈ P.H` does not change the stabilizer subgroup
  (`stabilizerSubgroup_mul_right_H`).
* Left multiplication by `h ∈ P.H` conjugates the stabilizer
  (`stab_mul_left_eq_map_conj`).
* These combine to give `Equiv`s of decomposition quotients
  (`decompQuot_mul_left_equiv`, `decompQuot_double_H_equiv`) used in the
  `CongruenceHecke` degree-combinatorics computations.
-/

open scoped Pointwise

namespace HeckeRing

section StabilizerInvariance

variable {G : Type*} [Group G] (P : HeckePair G)

/-- Right multiplication by `h ∈ H` does not change the stabilizer subgroup:
`Stab(g·h) = Stab(g)` when `h ∈ H`,
because `(g·h)H(g·h)⁻¹ = g(hHh⁻¹)g⁻¹ = gHg⁻¹`. -/
lemma stabilizerSubgroup_mul_right_H (g : P.Δ) (h : P.H) :
    (ConjAct.toConjAct ((g : G) * (h : G)) • P.H).subgroupOf P.H =
    (ConjAct.toConjAct (g : G) • P.H).subgroupOf P.H := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · rw [show (g : G)⁻¹ * (x : G) * g =
      (h : G) * (((g : G) * (h : G))⁻¹ * (x : G) * ((g : G) * (h : G))) * (h : G)⁻¹ by group]
    exact P.H.mul_mem (P.H.mul_mem h.2 hx) (P.H.inv_mem h.2)
  · rw [show ((g : G) * (h : G))⁻¹ * (x : G) * ((g : G) * (h : G)) =
      (h : G)⁻¹ * ((g : G)⁻¹ * (x : G) * (g : G)) * (h : G) by group]
    exact P.H.mul_mem (P.H.mul_mem (P.H.inv_mem h.2) hx) h.2

/-- Left multiplication by `h ∈ H` conjugates the stabilizer:
`Stab(h·g) = conj(h)(Stab(g))` as subgroups of `H`.
Concretely, `x ∈ Stab(h·g)` iff `h⁻¹·x·h ∈ Stab(g)`. -/
lemma stab_mul_left_eq_map_conj (g : P.Δ) (h : P.H) :
    (ConjAct.toConjAct ((h : G) * (g : G)) • P.H).subgroupOf P.H =
    ((ConjAct.toConjAct (g : G) • P.H).subgroupOf P.H).map
      (MulAut.conj h).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv,
    Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨fun hx ↦ ?_, ?_⟩
  · refine ⟨⟨(h : G)⁻¹ * (x : G) * (h : G),
      P.H.mul_mem (P.H.mul_mem (P.H.inv_mem h.2) x.2) h.2⟩, ?_, ?_⟩
    · change (g : G)⁻¹ * ((h : G)⁻¹ * (x : G) * (h : G)) * (g : G) ∈ P.H
      rw [show (g : G)⁻¹ * ((h : G)⁻¹ * (x : G) * (h : G)) * (g : G) =
        ((h : G) * (g : G))⁻¹ * (x : G) * ((h : G) * (g : G)) by group]
      exact hx
    · ext
      change (h : G) * ((h : G)⁻¹ * (x : G) * (h : G)) * (h : G)⁻¹ = (x : G)
      group
  · rintro ⟨y, hy, rfl⟩
    change ((h : G) * (g : G))⁻¹ * ((h : G) * (y : G) * (h : G)⁻¹) *
      ((h : G) * (g : G)) ∈ P.H
    rw [show ((h : G) * (g : G))⁻¹ * ((h : G) * (y : G) * (h : G)⁻¹) * ((h : G) * (g : G)) =
      (g : G)⁻¹ * (y : G) * (g : G) by group]
    exact hy

end StabilizerInvariance

section ConjugationEquiv

variable {G : Type*} [Group G] (P : HeckePair G)

/-- Conjugation by `h⁻¹` is the inverse automorphism of conjugation by `h`; the two `MulAut.conj`
maps used to build `decompQuot_mul_left_equiv` are mutually inverse. -/
private lemma conj_inv_eq_symm {H : Type*} [Group H] (h : H) :
    MulAut.conj h⁻¹ = (MulAut.conj h).symm := by
  rw [map_inv, MulAut.inv_def]

/-- Conjugation by `h ∈ H` gives an Equiv on decomposition quotients:
`H/Stab(h·g) ≃ H/Stab(g)` via `σ ↦ h⁻¹·σ·h`.

The well-definedness uses `Stab(h·g) = h·Stab(g)·h⁻¹`, which means
`σ₁ ~_{Stab(h·g)} σ₂` iff `h⁻¹·σ₁·h ~_{Stab(g)} h⁻¹·σ₂·h`. -/
noncomputable def decompQuot_mul_left_equiv (g : P.Δ) (h : P.H)
    (hm : (h : G) * (g : G) ∈ P.Δ) :
    decompQuot P ⟨(h : G) * g, hm⟩ ≃ decompQuot P g := by
  set K := (ConjAct.toConjAct (g : G) • P.H).subgroupOf P.H
  set K' := K.map (MulAut.conj h).toMonoidHom
  refine (Subgroup.quotientEquivOfEq (stab_mul_left_eq_map_conj P g h)).trans ?_
  have h_wd : ∀ a b : P.H, QuotientGroup.leftRel K' a b →
      QuotientGroup.leftRel K ((MulAut.conj h⁻¹) a) ((MulAut.conj h⁻¹) b) := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simp only [← map_inv, ← map_mul]
    obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.mp hab
    rw [show a⁻¹ * b = (MulAut.conj h) k from hkeq.symm, conj_inv_eq_symm,
      MulEquiv.symm_apply_apply]
    exact hk
  exact Equiv.ofBijective
    (Quotient.map' (MulAut.conj h⁻¹) h_wd)
    ⟨fun x y ↦ by
      revert x y
      refine Quotient.ind₂ fun a b hxy ↦ ?_
      simp only [Quotient.map'_mk''] at hxy
      rw [Quotient.eq''] at hxy ⊢
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      simp only [← map_inv, ← map_mul] at hxy
      exact Subgroup.mem_map.mpr ⟨(MulAut.conj h⁻¹) (a⁻¹ * b), hxy, by
        rw [conj_inv_eq_symm, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]⟩,
    fun x ↦ by
      revert x
      refine Quotient.ind fun b ↦ ⟨Quotient.mk'' ((MulAut.conj h) b), ?_⟩
      simp only [Quotient.map'_mk'']
      rw [Quotient.eq'', QuotientGroup.leftRel_apply, conj_inv_eq_symm,
        MulEquiv.symm_apply_apply, inv_mul_cancel]
      exact K.one_mem⟩

/-- Combined left-right invariance: `decompQuot(h·g·k) ≃ decompQuot(g)` for `h, k ∈ H`.
Composes right-invariance (stabilizer equality) with left-conjugation. -/
noncomputable def decompQuot_double_H_equiv (g : P.Δ) (h k : P.H)
    (hm : (h : G) * (g : G) * (k : G) ∈ P.Δ) :
    decompQuot P ⟨(h : G) * (g : G) * (k : G), hm⟩ ≃ decompQuot P g := by
  have hgk : (g : G) * (k : G) ∈ P.Δ := P.Δ.mul_mem g.2 (P.h₀ k.2)
  have hhgk : (h : G) * ((g : G) * (k : G)) ∈ P.Δ := by rwa [mul_assoc] at hm
  refine (Subgroup.quotientEquivOfEq ?_).trans
    ((decompQuot_mul_left_equiv P ⟨(g : G) * k, hgk⟩ h hhgk).trans
    (Subgroup.quotientEquivOfEq (stabilizerSubgroup_mul_right_H P g k)))
  change (ConjAct.toConjAct ((h : G) * (g : G) * (k : G)) • P.H).subgroupOf P.H =
    (ConjAct.toConjAct ((h : G) * ((g : G) * (k : G))) • P.H).subgroupOf P.H
  congr 2; exact mul_assoc _ _ _

end ConjugationEquiv

end HeckeRing
