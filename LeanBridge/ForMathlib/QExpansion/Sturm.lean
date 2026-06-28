import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import LeanBridge.ForMathlib.QExpansion.Generic

/-!
# Sturm-bound helpers

The Sturm bound (mathlib: `ModularForm.sturm_bound_levelOne`) says: a level-1 modular form of
weight `k` whose first `⌊k/12⌋ + 1` q-coefficients all vanish is identically zero. We package
the standard corollaries:

* `ModularForm.eq_of_sturm_bound`: two level-1 weight-`k` forms agreeing on the first
  `⌊k/12⌋ + 1` q-coefficients are equal.
-/

namespace ModularForm

open UpperHalfPlane PowerSeries
open scoped MatrixGroups

variable {k : ℤ}

/-- **Two-form Sturm bound.** Two level-1 weight-`k` modular forms whose q-expansions agree
on every coefficient `q^i` with `12 i ≤ k` are equal. -/
theorem eq_of_sturm_bound (f g : ModularForm 𝒮ℒ k)
    (h : ∀ i : ℕ, 12 * (i : ℤ) ≤ k →
         (PowerSeries.coeff (R := ℂ) i) (qExpansion 1 (f : ℍ → ℂ))
           = (PowerSeries.coeff (R := ℂ) i) (qExpansion 1 (g : ℍ → ℂ))) :
    f = g := by
  have hsub : f - g = 0 := by
    -- mathlib's `sturm_bound_levelOne` takes an *order* hypothesis
    -- (`↑(k.toNat / 12) < (qExpansion 1 ·).order`); bridge it from the
    -- coefficient-vanishing hypothesis `h` via `PowerSeries.nat_le_order`.
    apply ModularForm.sturm_bound_levelOne
    rcases lt_or_ge k 0 with hk | hk
    · -- negative weight: the form is identically zero, so its q-expansion has order `⊤`
      rw [rank_zero_iff_forall_zero.mp (ModularForm.levelOne_neg_weight_rank_zero hk) (f - g),
        ModularForm.coe_zero, qExpansion_zero, order_zero]
      exact ENat.coe_lt_top _
    · refine lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _)
        (PowerSeries.nat_le_order _ (k.toNat / 12 + 1) fun i hi => ?_)
      rw [show ((f - g : ModularForm 𝒮ℒ k) : ℍ → ℂ) = ⇑f - ⇑g from
          ModularForm.coe_sub f g,
        ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
        map_sub, sub_eq_zero]
      exact h i (by omega)
  exact sub_eq_zero.mp hsub

end ModularForm
