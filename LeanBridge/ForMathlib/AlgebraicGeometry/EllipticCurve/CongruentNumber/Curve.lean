import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.CongruentNumber.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.NormNum.IsSquare

/-!
# The congruent number curve

For a positive integer `n`, the **congruent number curve** (LMFDB `ec.congruent_number_curve`) is
the elliptic curve `E_n : y² = x³ - n² x = x (x² - n²)` over `ℚ`, with Weierstrass coefficients
`[0, 0, 0, -n², 0]` and discriminant `64 n⁶`. A rational right triangle with legs `X`, `Y` and
hypotenuse `Z` of area `n` gives the rational point `(Z² / 4, Z (X² - Y²) / 8)` of `E_n`, whose
`y`-coordinate is not `0` because `2` is not the square of a rational. Conversely, a rational point
`(x, y)` of `E_n` with `y ≠ 0` gives the triangle with sides `|x² - n²| / |y|`, `|2 n x| / |y|` and
`(x² + n²) / |y|`, of area `n`. So a positive rational `n` is congruent if and only if `E_n(ℚ)` has
a point with `y ≠ 0` (LMFDB `ec.congruent_number_problem`). The points of `E_n(ℚ)` with `y = 0`
are `(0, 0)` and `(± n, 0)`, the points of order `2`; hence `n` is congruent as soon as `E_n(ℚ)` is
infinite.

The point of a triangle is twice the rational point `(X (X + Z) / 2, X² (X + Z) / 2)`, so only
points of `2 E_n(ℚ)` come from triangles, and for `n ≠ 0` a rational point `(x, y)` of `E_n` lies in
`2 E_n(ℚ)` if and only if `x`, `x - n` and `x + n` are all squares, in which case it is the point of
a triangle.

That the torsion subgroup of `E_n(ℚ)` is exactly `{O, (0, 0), (± n, 0)}`, so that a positive
integer `n` is congruent if and only if `E_n(ℚ)` is infinite, that is if and only if its rank is
positive, is proved in the file `CongruentNumber/Torsion.lean`. The knowl's other facts are not
formalised: the conductor of `E_n` is `32 n₀²` or `16 n₀²` for the squarefree part `n₀` of `n`, and
`E_n` lies in an isogeny class of four curves linked by `2`-isogenies. In that last statement the
knowl gives `[0, ± 12 n, 0, n², 0]` for two of the curves `2`-isogenous to
`E_n = [0, 0, 0, -n², 0]`. Vélu's formulae for the kernels `⟨(± n, 0)⟩` give `[0, ∓ 6 n, 0, n², 0]`
instead: the curve `[0, 12 n, 0, n², 0]` has discriminant `2240 n⁶ = 2⁶ · 5 · 7 · n⁶`, so for
`n = 1` it has bad reduction at `5` and `7` and cannot be isogenous to `E_1`, which has conductor
`32`.

## Main definitions

* `WeierstrassCurve.congruentNumberCurve` (LMFDB `ec.congruent_number_curve`): the curve `E_n`.
* `WeierstrassCurve.congruentNumberPoint`: the point of `E_n(ℚ)` attached to a rational right
  triangle of area `n`.
* `WeierstrassCurve.congruentNumberHalfPoint`: a rational point of which it is twice.

## Main results

* `WeierstrassCurve.Δ_congruentNumberCurve`: the discriminant of `E_n` is `64 n⁶`.
* `WeierstrassCurve.isElliptic_congruentNumberCurve`: `E_n` is an elliptic curve when `2` and `n`
  are units.
* `WeierstrassCurve.equation_congruentNumberCurve_triangle`: the point of a triangle lies on `E_n`.
* `WeierstrassCurve.congruentNumberCurve_triangle_y_ne_zero`: its `y`-coordinate is not `0`.
* `WeierstrassCurve.two_nsmul_congruentNumberHalfPoint`: the point of a triangle is twice a
  rational point.
* `WeierstrassCurve.exists_two_nsmul_eq_some_congruentNumberCurve_iff`: a rational point `(x, y)`
  of `E_n` is twice a rational point if and only if `x`, `x - n` and `x + n` are all squares.
* `WeierstrassCurve.two_nsmul_congruentNumberCurve_six`: the knowl's example, `2 (-3, 9)` on `E_6`
  is the point of the triangle `(3, 4, 5)`.
* `Rat.isCongruentNumber_of_equation`: a rational point of `E_n` with `y ≠ 0` gives a triangle.
* `Rat.isCongruentNumber_iff_exists_equation` (LMFDB `ec.congruent_number_problem`): a positive
  rational `n` is congruent if and only if `E_n(ℚ)` has a point `(x, y)` with `y ≠ 0`.
* `Rat.isCongruentNumber_of_infinite`: if `E_n(ℚ)` is infinite, then `n` is congruent.
-/

open WeierstrassCurve Affine

namespace WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] (n : R)

/-- The **congruent number curve** `E_n : y² = x³ - n² x` (LMFDB `ec.congruent_number_curve`), with
Weierstrass coefficients `[0, 0, 0, -n², 0]`. The LMFDB defines it over `ℚ` for a positive integer
`n`, as `congruentNumberCurve (n : ℚ)`; it is an elliptic curve whenever `2` and `n` are units
(`isElliptic_congruentNumberCurve`). -/
@[simps]
def congruentNumberCurve : WeierstrassCurve R where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -n ^ 2
  a₆ := 0

/-- **The discriminant of `E_n` is `64 n⁶`.** -/
lemma Δ_congruentNumberCurve : (congruentNumberCurve n).Δ = 64 * n ^ 6 := by
  simp only [Δ, b₂, b₄, b₆, congruentNumberCurve_a₁, congruentNumberCurve_a₂,
    congruentNumberCurve_a₃, congruentNumberCurve_a₄, congruentNumberCurve_a₆]
  ring1

/-- **`E_n` is an elliptic curve when `2` and `n` are units**, for instance over a field of
characteristic other than `2` when `n ≠ 0`. -/
lemma isElliptic_congruentNumberCurve (h₂ : IsUnit (2 : R)) (hn : IsUnit n) :
    (congruentNumberCurve n).IsElliptic := by
  rw [isElliptic_iff, Δ_congruentNumberCurve, show (64 : R) = 2 ^ 6 by norm_num]
  exact (h₂.pow 6).mul (hn.pow 6)

variable {n} in
lemma equation_congruentNumberCurve_iff (x y : R) :
    (congruentNumberCurve n).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - n ^ 2 * x := by
  rw [equation_iff, congruentNumberCurve_a₁, congruentNumberCurve_a₂, congruentNumberCurve_a₃,
    congruentNumberCurve_a₄, congruentNumberCurve_a₆]
  constructor <;> intro h <;> linear_combination h

end CommRing

variable {n X Y Z x y : ℚ}

lemma nonsingular_congruentNumberCurve_of_equation (hn : n ≠ 0)
    (h : (congruentNumberCurve n).toAffine.Equation x y) :
    (congruentNumberCurve n).toAffine.Nonsingular x y :=
  (equation_iff_nonsingular_of_Δ_ne_zero (by simp [Δ_congruentNumberCurve, hn])).mp h

/-- **The point of a triangle lies on `E_n`**: for rationals `X`, `Y`, `Z` with `X² + Y² = Z²` and
`X Y = 2 n`, the point `(Z² / 4, Z (X² - Y²) / 8)` satisfies `y² = x³ - n² x`. -/
lemma equation_congruentNumberCurve_triangle (h₁ : X ^ 2 + Y ^ 2 = Z ^ 2) (h₂ : X * Y = 2 * n) :
    (congruentNumberCurve n).toAffine.Equation (Z ^ 2 / 4) (Z * (X ^ 2 - Y ^ 2) / 8) := by
  rw [equation_congruentNumberCurve_iff]
  linear_combination Z ^ 2 / 64 * (X ^ 2 + Y ^ 2 + Z ^ 2) * h₁ - Z ^ 2 / 16 * (X * Y + 2 * n) * h₂

/-- **The point of a triangle is not of order `2`**: for rationals `X`, `Y`, `Z` with
`X² + Y² = Z²` and `X Y = 2 n ≠ 0`, the `y`-coordinate `Z (X² - Y²) / 8` is not `0`, since
`X² = Y²` would give `(Z / X)² = 2`. -/
lemma congruentNumberCurve_triangle_y_ne_zero (hn : n ≠ 0) (h₁ : X ^ 2 + Y ^ 2 = Z ^ 2)
    (h₂ : X * Y = 2 * n) : Z * (X ^ 2 - Y ^ 2) / 8 ≠ 0 := by
  have hX : X ≠ 0 :=
    left_ne_zero_of_mul (h₂ ▸ mul_ne_zero two_ne_zero hn)
  have hZ : Z ≠ 0 := by
    rintro rfl
    exact hX (pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith [sq_nonneg X, sq_nonneg Y]))
  intro h
  rcases mul_eq_zero.mp ((div_eq_zero_iff.mp h).resolve_right (by norm_num)) with h | h
  · exact hZ h
  have h2 : IsSquare (2 : ℚ) := by
    refine ⟨Z / X, ?_⟩
    field_simp
    linear_combination h + h₁
  exact absurd h2 (by norm_num)

/-- The rational point `(Z² / 4, Z (X² - Y²) / 8)` of the congruent number curve `E_n` attached to
a rational right triangle with legs `X`, `Y` and hypotenuse `Z` of area `n ≠ 0`, that is to
rationals with `X² + Y² = Z²` and `X Y = 2 n` (LMFDB `ec.congruent_number_curve`). It is not a
point of order `2`, as its `y`-coordinate is not `0`
(`congruentNumberCurve_triangle_y_ne_zero`). -/
def congruentNumberPoint (hn : n ≠ 0) (h₁ : X ^ 2 + Y ^ 2 = Z ^ 2) (h₂ : X * Y = 2 * n) :
    (congruentNumberCurve n).toAffine.Point :=
  .some (Z ^ 2 / 4) (Z * (X ^ 2 - Y ^ 2) / 8) <|
    nonsingular_congruentNumberCurve_of_equation hn <| equation_congruentNumberCurve_triangle h₁ h₂

lemma equation_congruentNumberCurve_halfPoint (h₁ : X ^ 2 + Y ^ 2 = Z ^ 2) (h₂ : X * Y = 2 * n) :
    (congruentNumberCurve n).toAffine.Equation (X * (X + Z) / 2) (X ^ 2 * (X + Z) / 2) := by
  rw [equation_congruentNumberCurve_iff]
  linear_combination X ^ 3 * (X + Z) / 8 * h₁ - X * (X + Z) * (X * Y + 2 * n) / 8 * h₂

/-- The rational point `(X (X + Z) / 2, X² (X + Z) / 2)` of the congruent number curve `E_n`
attached to a rational right triangle with legs `X`, `Y` and hypotenuse `Z` of area `n ≠ 0`, that is
to rationals with `X² + Y² = Z²` and `X Y = 2 n`: twice it is the point `congruentNumberPoint` of
the triangle (`two_nsmul_congruentNumberHalfPoint`). -/
def congruentNumberHalfPoint (hn : n ≠ 0) (h₁ : X ^ 2 + Y ^ 2 = Z ^ 2) (h₂ : X * Y = 2 * n) :
    (congruentNumberCurve n).toAffine.Point :=
  .some (X * (X + Z) / 2) (X ^ 2 * (X + Z) / 2) <|
    nonsingular_congruentNumberCurve_of_equation hn <| equation_congruentNumberCurve_halfPoint h₁ h₂

/-- **The point of a triangle is twice a rational point** (LMFDB `ec.congruent_number_curve`): for
rationals `X`, `Y`, `Z` with `X² + Y² = Z²` and `X Y = 2 n ≠ 0`, the point
`(Z² / 4, Z (X² - Y²) / 8)` of `E_n` is twice the point `(X (X + Z) / 2, X² (X + Z) / 2)`, at which
the tangent has slope `X + Z / 2`. So only points of `2 E_n(ℚ)` come from triangles. -/
lemma two_nsmul_congruentNumberHalfPoint (hn : n ≠ 0) (h₁ : X ^ 2 + Y ^ 2 = Z ^ 2)
    (h₂ : X * Y = 2 * n) :
    2 • congruentNumberHalfPoint hn h₁ h₂ = congruentNumberPoint hn h₁ h₂ := by
  have hX : X ≠ 0 :=
    left_ne_zero_of_mul (h₂ ▸ mul_ne_zero two_ne_zero hn)
  have hXZ : X + Z ≠ 0 := fun h ↦ by
    have hY : Y = 0 :=
      pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination h₁ + (Z - X) * h)
    exact hn (by linear_combination -h₂ / 2 + X / 2 * hY)
  have hy : X ^ 2 * (X + Z) / 2 ≠ (congruentNumberCurve n).toAffine.negY (X * (X + Z) / 2)
      (X ^ 2 * (X + Z) / 2) := by
    simp [self_eq_neg, hX, hXZ]
  have hℓ : (congruentNumberCurve n).toAffine.slope (X * (X + Z) / 2) (X * (X + Z) / 2)
      (X ^ 2 * (X + Z) / 2) (X ^ 2 * (X + Z) / 2) = (2 * X + Z) / 2 := by
    rw [slope_of_Y_ne rfl hy, div_eq_iff (sub_ne_zero.mpr hy)]
    simp only [negY, congruentNumberCurve_a₁, congruentNumberCurve_a₂, congruentNumberCurve_a₃,
      congruentNumberCurve_a₄]
    linear_combination -X ^ 2 / 4 * h₁ + (X * Y + 2 * n) / 4 * h₂
  rw [congruentNumberHalfPoint, two_nsmul, Point.add_self_of_Y_ne hy, congruentNumberPoint]
  congr 1 <;> rw [hℓ]
  · simp only [addX, congruentNumberCurve_a₁, congruentNumberCurve_a₂]
    ring1
  · simp only [addY, negY, negAddY, addX, congruentNumberCurve_a₁, congruentNumberCurve_a₂,
      congruentNumberCurve_a₃]
    linear_combination Z / 8 * h₁

/-- **The points of `2 E_n(ℚ)`** (LMFDB `ec.congruent_number_curve`): for a rational `n ≠ 0`, a
rational point `(x, y)` of `E_n` is twice a rational point if and only if `x`, `x - n` and `x + n`
are all squares. Twice a point `(x₁, y₁)` with `y₁ ≠ 0` has `x = ((x₁² + n²) / (2 y₁))²`,
`x - n = ((x₁² - 2 n x₁ - n²) / (2 y₁))²` and `x + n = ((x₁² + 2 n x₁ - n²) / (2 y₁))²`.
Conversely, if `x = a²`, `x - n = b²` and `x + n = c²`, then `(x, y)` is the point of the triangle
`(c - b, c + b, ± 2 a)`, which is twice a rational point. -/
lemma exists_two_nsmul_eq_some_congruentNumberCurve_iff (hn : n ≠ 0)
    (h : (congruentNumberCurve n).toAffine.Nonsingular x y) :
    (∃ Q, 2 • Q = Point.some x y h) ↔ IsSquare x ∧ IsSquare (x - n) ∧ IsSquare (x + n) := by
  constructor
  · rintro ⟨_ | ⟨x₁, y₁, h₁⟩, hQ⟩
    · simp [← Point.zero_def] at hQ
    by_cases hy : y₁ = (congruentNumberCurve n).toAffine.negY x₁ y₁
    · rw [two_nsmul, Point.add_self_of_Y_eq hy] at hQ
      simp at hQ
    rw [two_nsmul, Point.add_self_of_Y_ne hy] at hQ
    injection hQ with hQ
    rw [slope_of_Y_ne rfl hy] at hQ
    have hy₁ : y₁ ≠ 0 := fun hy₀ ↦ hy (by simp [hy₀])
    have he : y₁ ^ 2 = x₁ ^ 3 - n ^ 2 * x₁ :=
      (equation_congruentNumberCurve_iff _ _).mp h₁.1
    have hx : x * (2 * y₁) ^ 2 = (x₁ ^ 2 + n ^ 2) ^ 2 := by
      rw [← hQ]
      simp only [addX, negY, congruentNumberCurve_a₁, congruentNumberCurve_a₂,
        congruentNumberCurve_a₃, congruentNumberCurve_a₄, zero_mul, sub_zero]
      field_simp
      linear_combination -32 * x₁ * he
    have h2y : 2 * y₁ * (2 * y₁) ≠ 0 := by
      simp [hy₁]
    refine ⟨⟨(x₁ ^ 2 + n ^ 2) / (2 * y₁), ?_⟩, ⟨(x₁ ^ 2 - 2 * n * x₁ - n ^ 2) / (2 * y₁), ?_⟩,
      ⟨(x₁ ^ 2 + 2 * n * x₁ - n ^ 2) / (2 * y₁), ?_⟩⟩ <;>
      rw [div_mul_div_comm, eq_div_iff h2y]
    · linear_combination hx
    · linear_combination hx - 4 * n * he
    · linear_combination hx + 4 * n * he
  · rintro ⟨⟨a, rfl⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩
    have h₂ : (c - b) * (c + b) = 2 * n := by
      linear_combination hb - hc
    have hy : y ^ 2 = (a * b * c) ^ 2 := by
      linear_combination (equation_congruentNumberCurve_iff _ _).mp h.1 +
        a ^ 2 * (a ^ 2 + n) * hb + a ^ 2 * b ^ 2 * hc
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with rfl | rfl
    · refine ⟨congruentNumberHalfPoint hn (Z := -(2 * a)) (by linear_combination -2 * hb - 2 * hc)
        h₂, ?_⟩
      rw [two_nsmul_congruentNumberHalfPoint, congruentNumberPoint]
      congr 1 <;> ring1
    · refine ⟨congruentNumberHalfPoint hn (Z := 2 * a) (by linear_combination -2 * hb - 2 * hc)
        h₂, ?_⟩
      rw [two_nsmul_congruentNumberHalfPoint, congruentNumberPoint]
      congr 1 <;> ring1

/-- **The knowl's example on `E_6`**: `2 (-3, 9) = (25 / 4, -35 / 8)` on `E_6 : y² = x³ - 36 x`, the
point of the triangle `(3, 4, 5)`. -/
lemma two_nsmul_congruentNumberCurve_six : 2 • Point.some (-3) 9
    (nonsingular_congruentNumberCurve_of_equation (n := 6) (by norm_num)
    ((equation_congruentNumberCurve_iff _ _).mpr (by norm_num))) = congruentNumberPoint (n := 6)
    (X := 3) (Y := 4) (Z := 5) (by norm_num) (by norm_num) (by norm_num) := by
  rw [two_nsmul, Point.add_self_of_Y_ne (by norm_num), congruentNumberPoint]
  congr 1 <;> norm_num [addY]

lemma eq_zero_or_eq_or_eq_neg_of_equation_congruentNumberCurve
    (h : (congruentNumberCurve n).toAffine.Equation x 0) : x = 0 ∨ x = n ∨ x = -n := by
  rw [equation_congruentNumberCurve_iff] at h
  have h' : x * (x - n) * (x + n) = 0 := by
    linear_combination -h
  simpa [sub_eq_zero, add_eq_zero_iff_eq_neg, or_assoc] using h'

end WeierstrassCurve

namespace Rat

variable {n x y : ℚ}

/-- **A rational point off `y = 0` gives a triangle**: if `(x, y)` is a rational point of `E_n`
with `y ≠ 0`, for a positive rational `n`, then `n` is the area of the right triangle with legs
`|x² - n²| / |y|`, `|2 n x| / |y|` and hypotenuse `(x² + n²) / |y|`. -/
lemma isCongruentNumber_of_equation (hn : 0 < n)
    (h : (congruentNumberCurve n).toAffine.Equation x y) (hy : y ≠ 0) : n.IsCongruentNumber := by
  rw [equation_congruentNumberCurve_iff] at h
  have hx : x ≠ 0 := by
    rintro rfl
    exact hy (pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination h))
  have hx' : x ^ 2 - n ^ 2 ≠ 0 := fun hx' ↦
    hy (pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination h + x * hx'))
  have hy' : 0 < |y| :=
    abs_pos.mpr hy
  refine ⟨|x ^ 2 - n ^ 2| / |y|, |2 * n * x| / |y|, (x ^ 2 + n ^ 2) / |y|,
    div_pos (abs_pos.mpr hx') hy', div_pos (abs_pos.mpr (by positivity)) hy', by positivity, ?_,
    ?_⟩
  · simp only [div_pow, sq_abs]
    field_simp
    ring1
  · have e : (x ^ 2 - n ^ 2) * (2 * n * x) = 2 * n * y ^ 2 := by
      linear_combination (-2 * n) * h
    rw [div_mul_div_comm, ← abs_mul, e, abs_of_pos (by positivity), abs_mul_abs_self]
    field_simp

/-- **Congruent numbers and the congruent number curve** (LMFDB `ec.congruent_number_problem`,
`ec.congruent_number_curve`): a positive rational `n` is congruent if and only if the congruent
number curve `E_n : y² = x³ - n² x` has a rational point `(x, y)` with `y ≠ 0`. -/
lemma isCongruentNumber_iff_exists_equation (hn : 0 < n) :
    n.IsCongruentNumber ↔ ∃ x y : ℚ, (congruentNumberCurve n).toAffine.Equation x y ∧ y ≠ 0 := by
  refine ⟨?_, fun ⟨x, y, h, hy⟩ ↦ isCongruentNumber_of_equation hn h hy⟩
  rintro ⟨X, Y, Z, -, -, -, h₁, h₂⟩
  have h₂' : X * Y = 2 * n := by
    linear_combination 2 * h₂
  exact ⟨_, _, equation_congruentNumberCurve_triangle h₁ h₂',
    congruentNumberCurve_triangle_y_ne_zero hn.ne' h₁ h₂'⟩

/-- **If `E_n(ℚ)` is infinite, then `n` is congruent**: the points of `E_n(ℚ)` that give no
triangle are the point at infinity and the points `(0, 0)` and `(± n, 0)` of order `2`. -/
lemma isCongruentNumber_of_infinite (hn : 0 < n)
    (h : Infinite (congruentNumberCurve n).toAffine.Point) : n.IsCongruentNumber := by
  by_contra hc
  have hy (x y : ℚ) (hxy : (congruentNumberCurve n).toAffine.Nonsingular x y) : y = 0 :=
    by_contra fun hy ↦ hc (isCongruentNumber_of_equation hn hxy.1 hy)
  let f : (congruentNumberCurve n).toAffine.Point → Option ℚ := fun P ↦ match P with
    | .zero => none
    | .some x _ _ => some x
  have hf : Function.Injective f := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h <;> cases h
    · rfl
    have hy₁ : y₁ = 0 :=
      hy _ _ h₁
    have hy₂ : y₂ = 0 :=
      hy _ _ h₂
    subst hy₁ hy₂
    rfl
  refine Set.infinite_range_of_injective hf <|
    (Set.toFinite {none, some 0, some n, some (-n)}).subset ?_
  rintro _ ⟨_ | ⟨x, y, hxy⟩, rfl⟩
  · simp [f]
  have hy₀ : y = 0 :=
    hy _ _ hxy
  subst hy₀
  rcases eq_zero_or_eq_or_eq_neg_of_equation_congruentNumberCurve hxy.1 with rfl | rfl | rfl <;>
    simp [f]

end Rat
