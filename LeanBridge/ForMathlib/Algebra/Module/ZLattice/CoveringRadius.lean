import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# The covering radius of a lattice

The covering radius, or inhomogeneous minimum, of a convex `0`-symmetric set `K` with respect to a
lattice `L` in `ℝⁿ` is the least `t > 0` such that the translates `x + t K`, `x ∈ L`, cover `ℝⁿ`.
The covering radius of `L` is that of the closed unit ball: the least `t` such that every point
lies at distance at most `t` from `L`. Jarník's inequalities `λₙ / 2 ≤ μ ≤ (λ₁ + ⋯ + λₙ) / 2`, which
need the successive minima of `K` with respect to `L`, are not formalised.

## Main definitions

* `ZLattice.inhomogeneousMinimum` (LMFDB `lattice.covering_radius`).
* `ZLattice.coveringRadius` (LMFDB `lattice.covering_radius`).

## Main results

* `ZLattice.coveringRadius_eq`: the covering radius of `L` is the infimum of the `t > 0` such that
  every point lies at distance at most `t` from a point of `L`.
-/

open Metric Set
open scoped Pointwise

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : Submodule ℤ E)

/-- The **covering radius** or **inhomogeneous minimum** (LMFDB `lattice.covering_radius`)
`μ(K, L)` of a set `K` with respect to a lattice `L` in a real normed space `E`: the infimum of the
`t > 0` such that the translates `x + t K`, `x ∈ L`, cover `E`. The LMFDB takes `E = ℝⁿ`, a full
lattice `L` and a convex `0`-symmetric set `K`; for a compact convex body `K` with `0` in its
interior the infimum is attained, so it is the LMFDB's minimum. If no `t` works, as for a lattice
that is not full, the value is the junk value `0`. -/
noncomputable def inhomogeneousMinimum (K : Set E) : ℝ :=
  sInf {t | 0 < t ∧ ⋃ x ∈ L, x +ᵥ t • K = univ}

/-- The **covering radius** (LMFDB `lattice.covering_radius`) of a lattice `L` in a real normed
space: the covering radius `ZLattice.inhomogeneousMinimum` of the closed unit ball with respect to
`L`. -/
noncomputable def coveringRadius : ℝ :=
  inhomogeneousMinimum L (closedBall 0 1)

/-- **The covering radius of `L` is the least `t` such that every point lies at distance at most `t`
from `L`.** -/
lemma coveringRadius_eq :
    coveringRadius L = sInf {t | 0 < t ∧ ∀ y : E, ∃ x ∈ L, dist y x ≤ t} := by
  refine congrArg sInf <| ext fun t ↦ and_congr_right fun ht ↦ ?_
  simp only [smul_unitClosedBall_of_nonneg ht.le, vadd_closedBall_zero, eq_univ_iff_forall,
    mem_iUnion₂, mem_closedBall, exists_prop]

end ZLattice
