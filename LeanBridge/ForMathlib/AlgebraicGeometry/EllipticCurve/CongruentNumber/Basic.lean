import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Congruent numbers

A **congruent number** (LMFDB `ec.congruent_number`) is a positive rational number `n` which is the
area `X Y / 2` of a right triangle with rational legs `X`, `Y` and rational hypotenuse `Z`. The
**congruent number problem** (LMFDB `ec.congruent_number_problem`) asks which rational numbers are
congruent. Since `n` is congruent if and only if `n t²` is, for every rational `t ≠ 0`, and every
positive rational is `n₀ t²` for a squarefree positive integer `n₀`, it suffices to decide it for
squarefree positive integers. A positive rational `n` is congruent if and only if there is a
rational number `a` such that `a`, `a - n` and `a + n` are all squares of rational numbers: given
a triangle, `a = (Z / 2)²` and `a ± n = ((X ± Y) / 2)²`; conversely, given `a = A²`, `a + n = B²`
and `a - n = C²`, the triangle is `(X, Y, Z) = (B + C, B - C, 2 A)`. The knowl states
`(X, Y, Z) = (2 A, B + C, B - C)`, which puts the hypotenuse first: for `n = 6` and `a = 25 / 4` it
gives `(5, 4, 3)`, and `5² + 4² ≠ 3²`.

The characterisation by rational points of the congruent number curve `E_n : y² = x³ - n² x` is in
`LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.CongruentNumber.Curve`.

## Main definitions

* `Rat.IsCongruentNumber` (LMFDB `ec.congruent_number`).

## Main results

* `Rat.isCongruentNumber_six`, `Rat.isCongruentNumber_five`: `6` and `5` are congruent numbers,
  with the triangles `(3, 4, 5)` and `(3 / 2, 20 / 3, 41 / 6)`.
* `Rat.isCongruentNumber_mul_sq_iff`: `n t²` is congruent if and only if `n` is, for `t ≠ 0`.
* `Rat.exists_squarefree_mul_sq`: every positive rational is `n₀ t²` for a squarefree positive
  integer `n₀` and a rational `t ≠ 0`.
* `Rat.isCongruentNumber_iff_exists_isSquare` (LMFDB `ec.congruent_number_problem`): `n > 0` is
  congruent if and only if `a`, `a - n` and `a + n` are squares for some rational `a`.
-/

namespace Rat

variable {n t : ℚ}

/-- A rational number `n` is a **congruent number** (LMFDB `ec.congruent_number`) if it is the area
`X Y / 2` of a right triangle with rational legs `X`, `Y` and rational hypotenuse `Z`: there are
positive rationals `X`, `Y`, `Z` with `X² + Y² = Z²` and `X Y / 2 = n`. A congruent number is
positive (`Rat.IsCongruentNumber.pos`). -/
def IsCongruentNumber (n : ℚ) : Prop :=
  ∃ X Y Z : ℚ, 0 < X ∧ 0 < Y ∧ 0 < Z ∧ X ^ 2 + Y ^ 2 = Z ^ 2 ∧ X * Y / 2 = n

lemma IsCongruentNumber.pos (h : n.IsCongruentNumber) : 0 < n := by
  rcases h with ⟨X, Y, -, hX, hY, -, -, rfl⟩
  positivity

/-- **`6` is a congruent number**, the area of the right triangle `(3, 4, 5)`. -/
lemma isCongruentNumber_six : (6 : ℚ).IsCongruentNumber :=
  ⟨3, 4, 5, by norm_num⟩

/-- **`5` is a congruent number**, the area of the right triangle `(3 / 2, 20 / 3, 41 / 6)`. -/
lemma isCongruentNumber_five : (5 : ℚ).IsCongruentNumber :=
  ⟨3 / 2, 20 / 3, 41 / 6, by norm_num⟩

lemma IsCongruentNumber.mul_sq (h : n.IsCongruentNumber) (ht : t ≠ 0) :
    (n * t ^ 2).IsCongruentNumber := by
  rcases h with ⟨X, Y, Z, hX, hY, hZ, h, rfl⟩
  refine ⟨X * |t|, Y * |t|, Z * |t|, by positivity, by positivity, by positivity, ?_, ?_⟩
  · linear_combination |t| ^ 2 * h
  · rw [← sq_abs t]
    ring1

/-- **Congruence is a property of square classes**: for `t ≠ 0`, `n t²` is a congruent number if
and only if `n` is. -/
lemma isCongruentNumber_mul_sq_iff (ht : t ≠ 0) :
    (n * t ^ 2).IsCongruentNumber ↔ n.IsCongruentNumber :=
  ⟨fun h ↦ by simpa [ht] using h.mul_sq (inv_ne_zero ht), (·.mul_sq ht)⟩

/-- **Every positive rational is a squarefree positive integer times a square**: `n = n₀ t²` with
`n₀` a squarefree positive integer and `t ≠ 0` rational. By
`Rat.isCongruentNumber_mul_sq_iff`, the congruent number problem therefore reduces to squarefree
positive integers. -/
lemma exists_squarefree_mul_sq (hn : 0 < n) :
    ∃ n₀ : ℕ, Squarefree n₀ ∧ ∃ t : ℚ, t ≠ 0 ∧ n = n₀ * t ^ 2 := by
  rcases exists_sq_mul_squarefree (n.num.natAbs * n.den) with ⟨b, a, hab, ha⟩
  have hab' : (b : ℚ) ^ 2 * a = n * n.den ^ 2 := by
    rw [sq (n.den : ℚ), ← mul_assoc, mul_den_eq_num, ← Int.natAbs_of_nonneg (num_nonneg.mpr hn.le)]
    exact_mod_cast hab
  have h : n = a * ((b : ℚ) / n.den) ^ 2 := by
    field_simp
    linear_combination -hab'
  exact ⟨a, ha, b / n.den, fun ht ↦ hn.ne' (by simpa [ht] using h), h⟩

/-- **Congruent numbers and three squares in arithmetic progression** (LMFDB
`ec.congruent_number_problem`): a positive rational `n` is congruent if and only if there is a
rational `a` with `a`, `a - n` and `a + n` all squares of rationals. A triangle `(X, Y, Z)` gives
`a = (Z / 2)²` with `a ± n = ((X ± Y) / 2)²`, and `a = A²`, `a + n = B²`, `a - n = C²` give the
triangle `(|B| + |C|, |B| - |C|, 2 |A|)`. -/
lemma isCongruentNumber_iff_exists_isSquare (hn : 0 < n) :
    n.IsCongruentNumber ↔ ∃ a : ℚ, IsSquare a ∧ IsSquare (a - n) ∧ IsSquare (a + n) := by
  constructor
  · rintro ⟨X, Y, Z, -, -, -, h, rfl⟩
    refine ⟨(Z / 2) ^ 2, ⟨Z / 2, sq _⟩, ⟨(X - Y) / 2, ?_⟩, ⟨(X + Y) / 2, ?_⟩⟩ <;>
      linear_combination -h / 4
  rintro ⟨a, ⟨A, hA⟩, ⟨C, hC⟩, ⟨B, hB⟩⟩
  have hBC : |C| < |B| :=
    sq_lt_sq.mp (by nlinarith)
  have hA₀ : 0 < |A| :=
    abs_pos.mpr fun h ↦ by nlinarith [mul_self_nonneg C]
  refine ⟨|B| + |C|, |B| - |C|, 2 * |A|, by linarith [abs_nonneg C], by linarith, by positivity,
    ?_, ?_⟩
  · linear_combination 2 * sq_abs B + 2 * sq_abs C - 4 * sq_abs A - 2 * hB - 2 * hC + 4 * hA
  · linear_combination (sq_abs B - sq_abs C - hB + hC) / 2

end Rat
