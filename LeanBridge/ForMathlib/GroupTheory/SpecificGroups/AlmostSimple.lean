import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Subgroup.Center

/-!
# Almost simple groups

## Main definitions

* `IsAlmostSimple` (LMFDB `group.almost_simple`).

## Main results

* `IsSimpleGroup.isAlmostSimple`: every non-abelian simple group is almost simple.
-/

universe u

variable (G : Type u) [Group G]

/-- A group `G` is **almost simple** (LMFDB `group.almost_simple`) if `S ≤ G ≤ Aut(S)` for a
non-abelian simple group `S`: there is an embedding `G ↪ Aut(S)` whose image contains the inner
automorphisms of `S`. The group `S` is taken in the universe of `G`. -/
def IsAlmostSimple : Prop :=
  ∃ (S : Type u) (_ : Group S), IsSimpleGroup S ∧ ¬IsMulCommutative S ∧
    ∃ f : G →* MulAut S, Function.Injective f ∧ (MulAut.conj : S →* MulAut S).range ≤ f.range

variable {G}

/-- Every non-abelian simple group is almost simple, through its inner automorphisms. -/
lemma IsSimpleGroup.isAlmostSimple [IsSimpleGroup G] (hG : ¬IsMulCommutative G) :
    IsAlmostSimple G := by
  refine ⟨G, inferInstance, inferInstance, hG, MulAut.conj, ?_, le_rfl⟩
  have hn : (Subgroup.center G).Normal := inferInstance
  have hc : Subgroup.center G = ⊥ :=
    hn.eq_bot_or_eq_top.resolve_right fun h ↦ hG <| Subgroup.center_eq_top_iff.mp h
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hc]
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : x * y * x⁻¹ = y := DFunLike.congr_fun hx y
  exact (mul_inv_eq_iff_eq_mul.mp hy).symm
