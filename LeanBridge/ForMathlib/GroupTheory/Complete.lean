import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Complete groups

A group `G` is complete if the conjugation map `G →* Aut(G)` is an isomorphism: `G` has trivial
centre and every automorphism of `G` is inner. A complete group is a direct factor of every group
in which it is a normal subgroup, its complement being its centralizer.

## Main definitions

* `Group.IsComplete` (LMFDB `group.complete`).

## Main results

* `Group.isComplete_iff`: a group is complete if and only if its centre is trivial and every
  automorphism is inner.
* `Subgroup.isComplement'_centralizer`: a complete normal subgroup is a direct factor, with its
  centralizer as a normal complement.
* `Group.surjective_conj_of_isComplement'`: conversely, if `G` is a direct factor of its holomorph
  `G ⋊ Aut(G)`, then every automorphism of `G` is inner.
-/

open Group SemidirectProduct Subgroup

namespace MulAut

variable {G : Type*} [Group G]

lemma ker_conj : (conj : G →* MulAut G).ker = center G := by
  ext g
  simp only [MonoidHom.mem_ker, MulEquiv.ext_iff, conj_apply, mem_center_iff, mul_inv_eq_iff_eq_mul]
  exact forall_congr' fun _ ↦ eq_comm

end MulAut

namespace Group

variable (G : Type*) [Group G] {H : Type*} [Group H]

/-- A group `G` is **complete** (LMFDB `group.complete`) if the conjugation map
`MulAut.conj : G →* MulAut G` is bijective, that is, if `G` has trivial centre and every
automorphism of `G` is inner (`Group.isComplete_iff`).

The knowl also lists the condition that "the natural map from `G` to its inner automorphism group
is an isomorphism", which only says that the centre is trivial: the intended map is the one to the
full automorphism group, as here. Its third condition, that `G` is a direct factor of every group
containing it as a normal subgroup, follows from completeness
(`Subgroup.isComplement'_centralizer`); the converse, a theorem of Baer, is only proved here for
the automorphisms, from `G` being a direct factor of its holomorph
(`Group.surjective_conj_of_isComplement'`), and not for the centre. -/
class IsComplete : Prop where
  bijective_conj : Function.Bijective (MulAut.conj : G →* MulAut G)

/-- **A group is complete if and only if its centre is trivial and all its automorphisms are
inner.** -/
lemma isComplete_iff :
    IsComplete G ↔ center G = ⊥ ∧ Function.Surjective (MulAut.conj : G →* MulAut G) := by
  rw [← MulAut.ker_conj, MonoidHom.ker_eq_bot_iff]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

variable {G}

lemma IsComplete.center_eq_bot [IsComplete G] : center G = ⊥ :=
  (isComplete_iff G).mp ‹_› |>.1

lemma IsComplete.surjective_conj [IsComplete G] :
    Function.Surjective (MulAut.conj : G →* MulAut G) :=
  IsComplete.bijective_conj.2

lemma IsComplete.of_mulEquiv [IsComplete G] (e : G ≃* H) : IsComplete H := by
  refine (isComplete_iff H).mpr ⟨?_, fun φ ↦ ?_⟩
  · rw [← map_center_eq e, IsComplete.center_eq_bot, Subgroup.map_bot]
  · rcases IsComplete.surjective_conj (e.trans (φ.trans e.symm)) with ⟨g, hg⟩
    refine ⟨e g, MulEquiv.ext fun h ↦ ?_⟩
    simpa using congrArg e (MulEquiv.congr_fun hg (e.symm h))

/-- **If a group is a direct factor of its holomorph `G ⋊ Aut(G)`, every automorphism is inner.**
Here `G` embeds in the holomorph through `SemidirectProduct.inl`, with normal image. -/
lemma surjective_conj_of_isComplement' {K : Subgroup (G ⋊[MonoidHom.id (MulAut G)] MulAut G)}
    [K.Normal] (h : (inl : G →* G ⋊[MonoidHom.id _] MulAut G).range.IsComplement' K) :
    Function.Surjective (MulAut.conj : G →* MulAut G) := by
  intro φ
  rcases h.2 (inr φ) with ⟨⟨⟨_, a, rfl⟩, k⟩, hk⟩
  refine ⟨a, MulEquiv.ext fun x ↦ inl_injective (φ := MonoidHom.id (MulAut G)) ?_⟩
  have hN : (inl : G →* G ⋊[MonoidHom.id _] MulAut G).range.Normal := by
    rw [range_inl_eq_ker_rightHom]
    infer_instance
  have hc : Commute (k : G ⋊[MonoidHom.id _] MulAut G) (inl x) :=
    (commute_of_normal_of_disjoint _ _ hN ‹_› h.disjoint _ _ ⟨x, rfl⟩ k.2).symm
  have hφ : (inl (φ x) : G ⋊[MonoidHom.id _] MulAut G) = inr φ * inl x * (inr φ)⁻¹ := by
    rw [← map_inv]
    exact inl_aut φ x
  rw [hφ, ← hk, MulAut.conj_apply, map_mul, map_mul, map_inv]
  nth_rw 1 [← hc.mul_inv_cancel]
  group

end Group

namespace Subgroup

variable {H : Type*} [Group H] (N : Subgroup H) [N.Normal] [Group.IsComplete N]

/-- **A complete normal subgroup is a direct factor**: its centralizer, a normal subgroup, is a
complement. -/
lemma isComplement'_centralizer : N.IsComplement' (centralizer (N : Set H)) := by
  refine isComplement'_of_disjoint_and_mul_eq_univ (disjoint_def.mpr fun hx hy ↦ ?_) ?_
  · have hc : (⟨_, hx⟩ : N) ∈ center N :=
      mem_center_iff.mpr fun m ↦ Subtype.ext (hy m m.2)
    rw [IsComplete.center_eq_bot, mem_bot] at hc
    exact congrArg Subtype.val hc
  · refine Set.eq_univ_of_forall fun h ↦ ?_
    rcases IsComplete.surjective_conj (MulAut.conjNormal h : MulAut N) with ⟨n, hn⟩
    refine ⟨n, n.2, (n : H)⁻¹ * h, mem_centralizer_iff.mpr fun m hm ↦ ?_,
      mul_inv_cancel_left _ _⟩
    have hm' : (n : H) * m * (n : H)⁻¹ = h * m * h⁻¹ :=
      congrArg Subtype.val (MulEquiv.congr_fun hn ⟨m, hm⟩)
    rw [← mul_right_inj (n : H), ← mul_left_inj h⁻¹]
    simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hm'

end Subgroup
