import TauCeti.AlgebraicGeometry.EllipticCurve.HasseBound

/-!
# Point counts and the Hasse bound over small prime fields

This file certifies the test cases of LeanBridge issue #17, on the Hasse–Weil bound and point
counting for elliptic curves over finite fields. It uses Tau Ceti's point count
`WeierstrassCurve.pointCount` of a Weierstrass curve, which counts the solutions of its affine
equation and the point at infinity, and its Frobenius trace `WeierstrassCurve.frobeniusTrace`,
which is `a_q = q + 1 - #E(𝔽_q)` over a field with `q` elements. Each count is evaluated by
`decide`, which runs through the points of `𝔽_p × 𝔽_p`.

* The elliptic curve `E : y² = x³ + 1`, the LMFDB curve `36.a4`, has `6` points over `𝔽₅` and `12`
  points over `𝔽₇`. So `a_5 = 0` and `a_7 = -4`, as the LMFDB lists for `36.a4`, and the bound
  `a_q² ≤ 4q` holds: `0 ≤ 20` and `16 ≤ 28`.
* Every elliptic curve over `𝔽₂` or `𝔽₃` satisfies `a_q² ≤ 4q`, by Tau Ceti's Hasse bound
  `WeierstrassCurve.frobeniusTrace_sq_le_four_mul_card`. Independently of that theorem, `decide`
  runs through all `2⁵ = 32` Weierstrass curves over `𝔽₂` and all `3⁵ = 243` over `𝔽₃`, counts
  their points and checks the bound for each. This covers the singular curves as well, whose trace
  is `1`, `-1` or `0` since their singular point is counted.

## Main definitions

* `LeanBridge.PointCount.curveX3AddOne`: the Weierstrass curve `y² = x³ + 1`.

## Main results

* `LeanBridge.PointCount.pointCount_curveX3AddOne_zmod_five` and
  `LeanBridge.PointCount.pointCount_curveX3AddOne_zmod_seven`: `E` has `6` points over `𝔽₅` and
  `12` points over `𝔽₇`.
* `LeanBridge.PointCount.frobeniusTrace_curveX3AddOne_zmod_five` and
  `LeanBridge.PointCount.frobeniusTrace_curveX3AddOne_zmod_seven`: `a_5 = 0` and `a_7 = -4`.
* `LeanBridge.PointCount.frobeniusTrace_curveX3AddOne_zmod_five_sq_le_four_mul_five` and
  `LeanBridge.PointCount.frobeniusTrace_curveX3AddOne_zmod_seven_sq_le_four_mul_seven`: the bound
  `a_q² ≤ 4q` for `E` over `𝔽₅` and over `𝔽₇`, checked on these values.
* `LeanBridge.PointCount.frobeniusTrace_sq_le_four_mul_two_of_isElliptic` and
  `LeanBridge.PointCount.frobeniusTrace_sq_le_four_mul_three_of_isElliptic`: the Hasse bound for
  every elliptic curve over `𝔽₂` and over `𝔽₃`, from the general theorem.
* `LeanBridge.PointCount.frobeniusTrace_sq_le_four_mul_two` and
  `LeanBridge.PointCount.frobeniusTrace_sq_le_four_mul_three`: the same bound for every Weierstrass
  curve over `𝔽₂` and over `𝔽₃`, by enumeration.

The instances `(curveX3AddOne (ZMod 5)).IsElliptic` and `(curveX3AddOne (ZMod 7)).IsElliptic` say
that `E` is an elliptic curve over `𝔽₅` and over `𝔽₇`.
-/

open WeierstrassCurve

namespace LeanBridge.PointCount

local instance : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance : Fact (Nat.Prime 7) :=
  ⟨Nat.prime_seven⟩

variable (W₂ : WeierstrassCurve (ZMod 2)) (W₃ : WeierstrassCurve (ZMod 3))

/-- The Weierstrass curve `y² = x³ + 1`. -/
def curveX3AddOne (R : Type*) [CommRing R] : WeierstrassCurve R :=
  ⟨0, 0, 0, 0, 1⟩

instance : (curveX3AddOne (ZMod 5)).IsElliptic :=
  ⟨by decide⟩

instance : (curveX3AddOne (ZMod 7)).IsElliptic :=
  ⟨by decide⟩

/-- `y² = x³ + 1` has `6` points over `𝔽₅`: the point at infinity, `(0, ±1)`, `(2, ±2)` and
`(4, 0)`. -/
lemma pointCount_curveX3AddOne_zmod_five : (curveX3AddOne (ZMod 5)).pointCount = 6 := by
  simp only [pointCount_def, Affine.equation_iff, Nat.card_eq_fintype_card]
  decide

/-- `y² = x³ + 1` has `12` points over `𝔽₇`: the point at infinity, `(0, ±1)`, `(1, ±3)`, `(2, ±3)`,
`(4, ±3)`, `(3, 0)`, `(5, 0)` and `(6, 0)`. -/
lemma pointCount_curveX3AddOne_zmod_seven : (curveX3AddOne (ZMod 7)).pointCount = 12 := by
  simp only [pointCount_def, Affine.equation_iff, Nat.card_eq_fintype_card]
  decide

/-- The Frobenius trace of `y² = x³ + 1` over `𝔽₅` is `a_5 = 5 + 1 - 6 = 0`. -/
lemma frobeniusTrace_curveX3AddOne_zmod_five : (curveX3AddOne (ZMod 5)).frobeniusTrace = 0 := by
  rw [frobeniusTrace_def, pointCount_curveX3AddOne_zmod_five]
  norm_num

/-- The Frobenius trace of `y² = x³ + 1` over `𝔽₇` is `a_7 = 7 + 1 - 12 = -4`. -/
lemma frobeniusTrace_curveX3AddOne_zmod_seven : (curveX3AddOne (ZMod 7)).frobeniusTrace = -4 := by
  rw [frobeniusTrace_def, pointCount_curveX3AddOne_zmod_seven]
  norm_num

/-- **The Hasse bound for `y² = x³ + 1` over `𝔽₅`**, checked on its trace: `a_5² = 0 ≤ 4 · 5`. -/
lemma frobeniusTrace_curveX3AddOne_zmod_five_sq_le_four_mul_five :
    (curveX3AddOne (ZMod 5)).frobeniusTrace ^ 2 ≤ 4 * 5 :=
  frobeniusTrace_curveX3AddOne_zmod_five ▸ by decide

/-- **The Hasse bound for `y² = x³ + 1` over `𝔽₇`**, checked on its trace: `a_7² = 16 ≤ 4 · 7`. -/
lemma frobeniusTrace_curveX3AddOne_zmod_seven_sq_le_four_mul_seven :
    (curveX3AddOne (ZMod 7)).frobeniusTrace ^ 2 ≤ 4 * 7 :=
  frobeniusTrace_curveX3AddOne_zmod_seven ▸ by decide

/-- **The Hasse bound over `𝔽₂`**: the Frobenius trace `a_q` of an elliptic curve over `𝔽₂`
satisfies `a_q² ≤ 4 · 2`. This is the case `q = 2` of Tau Ceti's
`WeierstrassCurve.frobeniusTrace_sq_le_four_mul_card`. -/
lemma frobeniusTrace_sq_le_four_mul_two_of_isElliptic [W₂.IsElliptic] :
    W₂.frobeniusTrace ^ 2 ≤ 4 * 2 :=
  W₂.frobeniusTrace_sq_le_four_mul_card.trans_eq <| by simp

/-- **The Hasse bound over `𝔽₃`**: the Frobenius trace `a_q` of an elliptic curve over `𝔽₃`
satisfies `a_q² ≤ 4 · 3`. This is the case `q = 3` of Tau Ceti's
`WeierstrassCurve.frobeniusTrace_sq_le_four_mul_card`. -/
lemma frobeniusTrace_sq_le_four_mul_three_of_isElliptic [W₃.IsElliptic] :
    W₃.frobeniusTrace ^ 2 ≤ 4 * 3 :=
  W₃.frobeniusTrace_sq_le_four_mul_card.trans_eq <| by simp

/-- **The Hasse bound over `𝔽₂`, by enumeration**: the Frobenius trace `a_q` of every Weierstrass
curve over `𝔽₂`, singular or not, satisfies `a_q² ≤ 4 · 2`. `decide` runs through the `2⁵ = 32`
curves and counts the points of each, without using the Hasse bound. -/
lemma frobeniusTrace_sq_le_four_mul_two : W₂.frobeniusTrace ^ 2 ≤ 4 * 2 := by
  simp only [frobeniusTrace_def, pointCount_def, Affine.equation_iff, Nat.card_eq_fintype_card]
  rcases W₂ with ⟨a₁, a₂, a₃, a₄, a₆⟩
  revert a₁ a₂ a₃ a₄ a₆
  decide

/-- **The Hasse bound over `𝔽₃`, by enumeration**: the Frobenius trace `a_q` of every Weierstrass
curve over `𝔽₃`, singular or not, satisfies `a_q² ≤ 4 · 3`. `decide` runs through the `3⁵ = 243`
curves and counts the points of each, without using the Hasse bound. -/
lemma frobeniusTrace_sq_le_four_mul_three : W₃.frobeniusTrace ^ 2 ≤ 4 * 3 := by
  simp only [frobeniusTrace_def, pointCount_def, Affine.equation_iff, Nat.card_eq_fintype_card]
  rcases W₃ with ⟨a₁, a₂, a₃, a₄, a₆⟩
  revert a₁ a₂ a₃ a₄ a₆
  decide

end LeanBridge.PointCount
