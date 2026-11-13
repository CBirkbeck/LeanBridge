import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Subgroup.Center

/-!
# Almost simple groups

## Main definitions

* `IsAlmostSimple` (LMFDB `group.almost_simple`).

## Main results

* `IsSimpleGroup.isAlmostSimple`: every non-abelian simple group is almost simple.
* `IsAlmostSimple.of_centralizer_eq_bot`: a group with a simple normal subgroup of trivial
  centraliser is almost simple.
-/

universe u

open Subgroup

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

/-- **A group with a simple normal subgroup of trivial centraliser is almost simple**: the
subgroup `N` is non-abelian, since an abelian `N` would lie in its own centraliser, and `G` acts
faithfully on `N` by conjugation, through automorphisms that include the inner ones. -/
lemma IsAlmostSimple.of_centralizer_eq_bot {N : Subgroup G} [N.Normal] [IsSimpleGroup N]
    (h : centralizer (N : Set G) = ⊥) : IsAlmostSimple G := by
  refine ⟨N, inferInstance, inferInstance, fun hN ↦ ?_, MulAut.conjNormal,
    (injective_iff_map_eq_one _).mpr fun g hg ↦ ?_, ?_⟩
  · exact (nontrivial_iff_ne_bot N).mp inferInstance <| le_bot_iff.mp <|
      h ▸ le_centralizer_iff_isMulCommutative.mpr hN
  · have hg' : g ∈ centralizer (N : Set G) := mem_centralizer_iff.mpr fun x hx ↦ by
      have hx' : g * x * g⁻¹ = x := congrArg (fun φ : MulAut N ↦ (φ ⟨x, hx⟩ : G)) hg
      exact (mul_inv_eq_iff_eq_mul.mp hx').symm
    rwa [h, mem_bot] at hg'
  · rintro _ ⟨s, rfl⟩
    exact ⟨s, MulAut.conjNormal_val⟩
