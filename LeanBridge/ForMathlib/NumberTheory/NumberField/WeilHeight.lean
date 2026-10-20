import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization

/-!
# The absolute Weil height of points of projective space over a number field

Mathlib's `Projectivization.logHeight` is the logarithmic height of a point of projective space
over a number field `K` relative to `K`: the sum over the places `v` of `K` of
`[K_v : ℚ_v] log max_i ‖α_i‖_v`. The LMFDB normalizes it by the degree `[K : ℚ]`. For rational
numbers and algebraic numbers the LMFDB's Weil heights are Mathlib's `Height.logHeight₁`, computed
on `ℚ` by `Rat.logHeight₁_eq_log_max`, and `NumberField.absLogHeight₁`.

## Main definitions

* `Projectivization.absLogHeight` (LMFDB `nf.weil_height`).

The heights `h_L` attached to line bundles `L` on projective varieties, which the LMFDB knowl also
defines, need very ample line bundles and projective embeddings, which are not available.
-/

namespace Projectivization

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]
  (x : Projectivization K (ι → K))

/-- The **absolute logarithmic Weil height** (LMFDB `nf.weil_height`) of a point
`P = [α₀ : ⋯ : αₙ]` of projective space over a number field `K`:
`h(P) = (1 / [K : ℚ]) ∑_v [K_v : ℚ_v] log max_i ‖α_i‖_v`, the logarithmic height of `P` relative
to `K` divided by the degree of `K`. -/
noncomputable def absLogHeight : ℝ :=
  x.logHeight / Module.finrank ℚ K

lemma absLogHeight_mk {a : ι → K} (ha : a ≠ 0) :
    (mk K a ha).absLogHeight = Height.logHeight a / Module.finrank ℚ K :=
  rfl

lemma absLogHeight_nonneg : 0 ≤ x.absLogHeight :=
  div_nonneg x.logHeight_nonneg (Nat.cast_nonneg _)

end Projectivization
