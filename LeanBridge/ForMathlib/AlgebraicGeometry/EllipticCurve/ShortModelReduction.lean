import Mathlib.FieldTheory.Finite.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.WorkedExamples.CanonicalEquations

/-!
# Short Weierstrass models over `ℤ` and bad reduction at `2` and `3`

Every elliptic curve over `ℚ` has a short Weierstrass equation `y² = x³ + Ax + B` with `A, B ∈ ℤ`
(Mathlib's `WeierstrassCurve.toShortNF`, and Tau Ceti's minimal-pair equation
`WeierstrassCurve.minimalPairModel`). A Weierstrass equation `W` with integer coefficients has
**bad reduction** at a prime `p` (`WeierstrassCurve.HasBadReductionAt`) if its reduction modulo `p`
is singular, which is to say that `p` divides its discriminant
(`WeierstrassCurve.hasBadReductionAt_iff`).

A short equation over `ℤ` always has bad reduction at `2`, its discriminant being
`-16 (4 A³ + 27 B²)` (`WeierstrassCurve.hasBadReductionAt_two_of_isShortNF`), even when the curve
has good reduction at `2`; and it may have bad reduction at `3` when the minimal equation of the
curve does not. Both happen for the curve 11.a2: its reduced minimal equation
`y² + y = x³ - x² - 10 x - 20` (Tau Ceti's `TauCeti.WorkedExamples.curve11a2`, minimal at every
prime by `TauCeti.WorkedExamples.isReducedMinimal_curve11a2`) has discriminant `-11⁵` and so good
reduction at `2` and `3`, while its minimal-pair short equation `y² = x³ - 13392 x - 1080432`
(`TauCeti.WorkedExamples.minimalPairModel_model_curve11a2`) has discriminant `-6¹² ⋅ 11⁵`, checked
independently.

## Main definitions

* `WeierstrassCurve.HasBadReductionAt` (LMFDB `ec.simple_equation`, `ec.bad_reduction`): bad
  reduction of an integral Weierstrass equation at a prime.

## Main results

* `WeierstrassCurve.hasBadReductionAt_iff`: bad reduction at `p` is `p ∣ Δ`.
* `WeierstrassCurve.hasBadReductionAt_two_of_isShortNF` (LMFDB `ec.simple_equation`): a short
  equation over `ℤ` has bad reduction at `2`.
* `WeierstrassCurve.not_hasBadReductionAt_two_curve11a2` and
  `WeierstrassCurve.not_hasBadReductionAt_three_curve11a2`: the minimal equation of 11.a2 has good
  reduction at `2` and `3`.
* `WeierstrassCurve.hasBadReductionAt_three_minimalPairModel_curve11a2` (LMFDB
  `ec.simple_equation`): the short equation over `ℤ` of 11.a2 has bad reduction at `3`.
-/

open TauCeti.WorkedExamples

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℤ) (p : ℕ)

/-- A Weierstrass equation `W` with integer coefficients has **bad reduction** at a prime `p`
(LMFDB `ec.simple_equation`, `ec.bad_reduction`): its reduction modulo `p` is singular, that is,
it has a singular point over `𝔽_p`. As `𝔽_p` is perfect, a singular point over an algebraic
closure of `𝔽_p` is already one over `𝔽_p`. The equation need not be minimal. -/
def HasBadReductionAt : Prop :=
  ∃ x y : ZMod p, (W.map (Int.castRingHom (ZMod p))).toAffine.IsSingular x y

variable {W p}

/-- **An integral Weierstrass equation has bad reduction at `p` exactly when `p ∣ Δ`.** -/
lemma hasBadReductionAt_iff [Fact p.Prime] : W.HasBadReductionAt p ↔ (p : ℤ) ∣ W.Δ := by
  rw [HasBadReductionAt, ← Affine.Δ_eq_zero_iff_exists_isSingular, map_Δ, eq_intCast,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **A short Weierstrass equation over `ℤ` has bad reduction at `2`** (LMFDB
`ec.simple_equation`): its discriminant `-16 (4 A³ + 27 B²)` is even. -/
lemma hasBadReductionAt_two_of_isShortNF [W.IsShortNF] : W.HasBadReductionAt 2 :=
  hasBadReductionAt_iff.mpr ⟨-8 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2), by rw [Δ_of_isShortNF]; ring1⟩

/-- **The minimal equation of 11.a2 has good reduction at `2`**: its discriminant `-11⁵` is odd. -/
lemma not_hasBadReductionAt_two_curve11a2 : ¬curve11a2.HasBadReductionAt 2 := by
  rw [hasBadReductionAt_iff, Δ_curve11a2]
  norm_num

/-- **The minimal equation of 11.a2 has good reduction at `3`**: `3 ∤ -11⁵`. -/
lemma not_hasBadReductionAt_three_curve11a2 : ¬curve11a2.HasBadReductionAt 3 := by
  rw [hasBadReductionAt_iff, Δ_curve11a2]
  norm_num

/-- **The short equation over `ℤ` of 11.a2 has bad reduction at `3`** (LMFDB `ec.simple_equation`):
the minimal-pair equation `y² = x³ - 13392 x - 1080432` of 11.a2 has discriminant `-6¹² ⋅ 11⁵`,
although the minimal equation of 11.a2 has good reduction at `3`. -/
lemma hasBadReductionAt_three_minimalPairModel_curve11a2 :
    (minimalPairModel (curve11a2.baseChange ℚ)).model.HasBadReductionAt 3 := by
  rw [minimalPairModel_model_curve11a2, hasBadReductionAt_iff, Δ_of_isShortNF]
  norm_num

end WeierstrassCurve
