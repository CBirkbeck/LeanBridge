import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Rat

/-!
# Natural numbers are units in `ℚ`-algebras

A nonzero natural number is a unit of `ℚ`, so its image in every `ℚ`-algebra is a unit. Tau Ceti's
main branch, not its pin, has this fact (`TauCeti.isUnit_natCast_of_ne_zero`): this file is to give
way to it at the bump.

## Main results

* `isUnit_natCast_of_ne_zero`: a nonzero natural number is a unit in every `ℚ`-algebra.
-/

/-- **A nonzero natural number is a unit in every `ℚ`-algebra.** -/
lemma isUnit_natCast_of_ne_zero {K : Type*} [Semiring K] [Algebra ℚ K] {n : ℕ} (hn : n ≠ 0) :
    IsUnit (n : K) :=
  map_natCast (algebraMap ℚ K) n ▸ (isUnit_iff_ne_zero.mpr <| Nat.cast_ne_zero.mpr hn).map _
