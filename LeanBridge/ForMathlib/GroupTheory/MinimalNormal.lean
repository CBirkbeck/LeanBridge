import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Order.Minimal

/-!
# Minimal normal subgroups and maximal quotients

## Main definitions

* `Subgroup.IsMinimalNormal` (LMFDB `group.minimal_normal`).
* `MonoidHom.IsMaximalQuotient` (LMFDB `group.maximal_quotient`).

## Main results

* `Subgroup.isMinimalNormal_iff`: the characterisation of the knowl, a nontrivial normal subgroup
  `K` such that every normal subgroup `H ≤ K` of `G` is trivial or `K`.
* `QuotientGroup.isMaximalQuotient_mk'`: the quotient map `G → G ⧸ K` is a maximal quotient if and
  only if `K` is a minimal normal subgroup.
-/

variable {G M : Type*} [Group G] [Group M]

namespace Subgroup

/-- A subgroup `K` of `G` is a **minimal normal subgroup** (LMFDB `group.minimal_normal`) if it is
a minimal element among the nontrivial normal subgroups of `G`. The LMFDB's wording does not
exclude `K = 1`, but minimal normal subgroups are nontrivial by the standard convention, which we
follow. -/
def IsMinimalNormal (K : Subgroup G) : Prop :=
  Minimal (fun N : Subgroup G ↦ N.Normal ∧ N ≠ ⊥) K

/-- The characterisation of minimal normal subgroups in LMFDB `group.minimal_normal`. -/
lemma isMinimalNormal_iff (K : Subgroup G) :
    K.IsMinimalNormal ↔ K.Normal ∧ K ≠ ⊥ ∧ ∀ H : Subgroup G, H.Normal → H ≤ K → H = ⊥ ∨ H = K := by
  refine ⟨fun h ↦ ⟨h.prop.1, h.prop.2, fun H hH hHK ↦ ?_⟩, fun ⟨hK, hK1, h⟩ ↦
    ⟨⟨hK, hK1⟩, fun H hH hHK ↦ (h H hH.1 hHK).resolve_left hH.2 |>.ge⟩⟩
  by_cases hH1 : H = ⊥
  · exact .inl hH1
  · exact .inr <| h.eq_of_le ⟨hH, hH1⟩ hHK

end Subgroup

/-- A surjective homomorphism `f : G →* M` is a **maximal quotient** (LMFDB
`group.maximal_quotient`) of `G` if its kernel is a minimal normal subgroup of `G`, i.e. `M ≅ G ⧸ K`
with `K` minimal normal. -/
def MonoidHom.IsMaximalQuotient (f : G →* M) : Prop :=
  Function.Surjective f ∧ f.ker.IsMinimalNormal

/-- The quotient `G ⧸ K` is a maximal quotient if and only if `K` is minimal normal. -/
lemma QuotientGroup.isMaximalQuotient_mk' (K : Subgroup G) [K.Normal] :
    (mk' K).IsMaximalQuotient ↔ K.IsMinimalNormal := by
  rw [MonoidHom.IsMaximalQuotient, ker_mk']
  exact and_iff_right <| mk'_surjective K
