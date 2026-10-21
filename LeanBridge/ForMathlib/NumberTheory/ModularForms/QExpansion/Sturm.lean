import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Analytic.SturmBound
import LeanBridge.ForMathlib.NumberTheory.ModularForms.QExpansion.Generic

/-!
# The Sturm bound in level one

Two modular forms of level one and weight `k` are equal as soon as their `q`-expansions agree on
every coefficient `q^i` with `12 i ≤ k`. This is the level-one case of the Sturm bound for
`M_k(N, χ)`, whose Sturm bound `⌊k / 12⌋` is the largest such `i` when `k ≥ 0`; in negative weight
the space is zero.

## Main results

* `ModularForm.eq_of_sturm_bound`: two level-1 weight-`k` forms agreeing on the first
  `⌊k/12⌋ + 1` q-coefficients are equal.
-/

namespace ModularForm

open CongruenceSubgroup UpperHalfPlane TauCeti
open scoped MatrixGroups

variable {k : ℤ}

/-- **Two-form Sturm bound.** Two level-1 weight-`k` modular forms whose q-expansions agree
on every coefficient `q^i` with `12 i ≤ k` are equal. -/
lemma eq_of_sturm_bound (f g : ModularForm 𝒮ℒ k) (h : ∀ i : ℕ, 12 * (i : ℤ) ≤ k →
    (PowerSeries.coeff (R := ℂ) i) (qExpansion 1 (f : ℍ → ℂ)) =
      (PowerSeries.coeff (R := ℂ) i) (qExpansion 1 (g : ℍ → ℂ))) : f = g := by
  rcases lt_or_ge k 0 with hk | hk
  · have h0 := rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero hk)
    exact (h0 f).trans (h0 g).symm
  have hmem (F : ModularForm 𝒮ℒ k) :
      mcast rfl F Gamma1_one_map_eq_SL ∈ modFormCharSpace k (1 : (ZMod 1)ˣ →* ℂˣ) :=
    (mem_modFormCharSpace_one_iff_diamondOp _).mpr fun d ↦ Subsingleton.elim d 1 ▸ by simp
  have hidx : (Gamma0 1).index = 1 :=
    Subgroup.index_eq_one.mpr <| eq_top_iff.mpr fun _ _ ↦ (Gamma0_mem).mpr <| Subsingleton.elim _ _
  refine ext fun z ↦ congr($(eq_of_sturmBound (hmem f) (hmem g) fun n hn ↦ h n ?_) z)
  rw [sturmBound, hidx, Nat.cast_one, mul_one] at hn
  omega

end ModularForm
