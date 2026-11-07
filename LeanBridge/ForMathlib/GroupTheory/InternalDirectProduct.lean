import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.NoncommCoprod

/-!
# Internal direct products

The direct product `G₁ × G₂` of two groups (LMFDB `group.direct_product`) is Mathlib's product
group, with the componentwise operation (`Prod.instGroup`, `Prod.mk_mul_mk`). Its subgroups
`H₁ = {(a, e₂)}` and `H₂ = {(e₁, a)}`, the ranges of `MonoidHom.inl` and `MonoidHom.inr`, are
normal, isomorphic to `G₁` and `G₂` (`MonoidHom.ofInjective` with `Prod.mk_left_injective` and
`Prod.mk_right_injective`), meet trivially and satisfy `H₁H₂ = G₁ × G₂`. Conversely, two normal
subgroups `H` and `K` of a group `G` with `H ∩ K = {e}` and `HK = G`, the direct factors of `G`,
give an isomorphism `H × K ≃* G`.

## Main definitions

* `Subgroup.IsDirectFactors` (LMFDB `group.direct_product`): normal subgroups `H` and `K` of `G`
  with `H ∩ K = {e}` and `HK = G`.
* `Subgroup.IsDirectFactors.mulEquiv` (LMFDB `group.direct_product`): the isomorphism
  `H × K ≃* G`, `(h, k) ↦ hk`, for direct factors `H` and `K`.

## Main results

* `MonoidHom.isDirectFactors_range_inl_range_inr` (LMFDB `group.direct_product`): the subgroups
  `H₁` and `H₂` of `G₁ × G₂` are normal, meet trivially and satisfy `H₁H₂ = G₁ × G₂`.
-/

open Pointwise

namespace Subgroup

variable {G : Type*} [Group G] (H K : Subgroup G)

/-- Normal subgroups `H` and `K` of `G` are **direct factors** of `G` (LMFDB
`group.direct_product`) if `H ∩ K = {e}` and `HK = G`; then `G ≅ H × K`
(`Subgroup.IsDirectFactors.mulEquiv`). -/
structure IsDirectFactors : Prop where
  /-- The first factor is normal. -/
  normal_left : H.Normal
  /-- The second factor is normal. -/
  normal_right : K.Normal
  /-- The factors meet trivially, `H ∩ K = {e}`. -/
  disjoint : Disjoint H K
  /-- The factors generate the group as a product of sets, `HK = G`. -/
  mul_eq_univ : (H : Set G) * (K : Set G) = Set.univ

namespace IsDirectFactors

variable {H K} (h : IsDirectFactors H K)

/-- The **isomorphism `H × K ≃* G`**, `(h, k) ↦ hk`, of two direct factors `H` and `K` of `G`
(LMFDB `group.direct_product`). -/
noncomputable def mulEquiv : H × K ≃* G :=
  MulEquiv.ofBijective (H.subtype.noncommCoprod K.subtype fun x y ↦
    commute_of_normal_of_disjoint H K h.normal_left h.normal_right h.disjoint _ _ x.2 y.2) <| by
    refine ⟨(MonoidHom.noncommCoprod_injective _ _ _).mpr ⟨H.subtype_injective,
      K.subtype_injective, ?_⟩, fun g ↦ ?_⟩
    · rw [range_subtype, range_subtype]
      exact h.disjoint
    · rcases Set.mem_mul.mp (h.mul_eq_univ ▸ Set.mem_univ g) with ⟨a, ha, b, hb, rfl⟩
      exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩

lemma mulEquiv_apply (x : H × K) : h.mulEquiv x = (x.1 : G) * x.2 :=
  rfl

end IsDirectFactors

end Subgroup

namespace MonoidHom

variable (G₁ G₂ : Type*) [Group G₁] [Group G₂]

/-- **The factors of a direct product are direct factors** (LMFDB `group.direct_product`): the
subgroups `H₁ = {(a, e₂)}` and `H₂ = {(e₁, a)}` of `G₁ × G₂` are normal, `H₁ ∩ H₂ = {(e₁, e₂)}`
and `H₁H₂ = G₁ × G₂`. -/
lemma isDirectFactors_range_inl_range_inr :
    (inl G₁ G₂).range.IsDirectFactors (inr G₁ G₂).range := by
  refine ⟨⟨fun n hn g ↦ ?_⟩, ⟨fun n hn g ↦ ?_⟩, ?_, ?_⟩
  · rcases hn with ⟨a, rfl⟩
    exact ⟨g.1 * a * g.1⁻¹, Prod.ext rfl (by simp)⟩
  · rcases hn with ⟨a, rfl⟩
    exact ⟨g.2 * a * g.2⁻¹, Prod.ext (by simp) rfl⟩
  · rw [Subgroup.disjoint_def]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    exact Prod.ext (Prod.ext_iff.mp hb).1.symm rfl
  · exact Set.eq_univ_of_forall fun x ↦
      Set.mem_mul.mpr ⟨(x.1, 1), ⟨x.1, rfl⟩, (1, x.2), ⟨x.2, rfl⟩, by simp⟩

end MonoidHom
