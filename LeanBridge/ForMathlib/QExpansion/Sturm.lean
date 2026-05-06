import Mathlib.NumberTheory.ModularForms.LevelOne.SturmBound
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
    apply ModularForm.sturm_bound_levelOne
    intro i hi
    rw [show ((f - g : ModularForm 𝒮ℒ k) : ℍ → ℂ) = ⇑f - ⇑g from
        ModularForm.coe_sub f g,
      ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      map_sub, sub_eq_zero]
    exact h i hi
  exact sub_eq_zero.mp hsub

end ModularForm
