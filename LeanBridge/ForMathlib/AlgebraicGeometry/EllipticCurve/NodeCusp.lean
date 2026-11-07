import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.Algebra.Polynomial.QuadraticDiscriminant
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular
import TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial
import TauCeti.AlgebraicGeometry.EllipticCurve.NodePolynomial
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Nodes and cusps of Weierstrass cubics, and the reduction types

A singular point `P = (x₀, y₀)` of a Weierstrass cubic `f(x, y) = 0` over a field, where `f` is
Mathlib's Weierstrass polynomial `y² + a₁ x y + a₃ y - (x³ + a₂ x² + a₄ x + a₆)` and singularity is
Tau Ceti's Jacobian criterion `WeierstrassCurve.Affine.IsSingular`, is a double point: every line
through `P` meets the curve there with multiplicity at least `2`. The **tangent lines** at `P` are
the lines meeting it with multiplicity at least `3`. The vertical line never does, as it meets the
curve at `P` with multiplicity exactly `2`
(`WeierstrassCurve.Affine.evalEval_vertical_of_isSingular`), so every tangent line is
`y - y₀ = m (x - x₀)` for a **tangent slope** `m` (`WeierstrassCurve.Affine.IsTangentSlope`), and
the tangent slopes are the roots of `T² + a₁ T - (3 x₀ + a₂)`
(`WeierstrassCurve.Affine.isTangentSlope_iff`). Following Silverman (III.1, p. 45), the singular
point is a **node** if there are two distinct tangent slopes over an algebraic closure, and a
**cusp** if there is only one. The point at infinity of a Weierstrass cubic is never singular
(Mathlib's `WeierstrassCurve.Projective.nonsingular_zero`), and a Weierstrass cubic over a field has
at most one singular point (Tau Ceti's `WeierstrassCurve.Affine.eq_of_isSingular_of_isSingular`),
so the curve has a nodal or cuspidal singularity when its singular point over an algebraic closure
is a node or a cusp.

If `m` is a tangent slope, the other one is `-a₁ - m`, and `c₄ = (2 m + a₁)⁴`, the fourth power of
their difference (`WeierstrassCurve.Affine.c₄_eq_of_isTangentSlope`). Hence the singular point is a
node exactly when `c₄ ≠ 0` and a cusp exactly when `c₄ = 0` (Silverman, Proposition III.1.4), in
every characteristic. Applied to the reduction of a minimal Weierstrass equation over a discrete
valuation ring, whose `c₄` is that of the integral model reduced, this identifies Mathlib's
valuative predicates with the geometric definitions of the LMFDB (Silverman, Proposition VII.5.1):
the reduction is multiplicative exactly when the reduced curve has a node, and additive exactly
when it has a cusp. Over a field, the node polynomial of Mathlib's
`WeierstrassCurve.HasSplitMultiplicativeReduction` is `c₄` times the tangent polynomial at the
singular point (`WeierstrassCurve.Affine.nodePolynomial_eq_of_isSingular`), so the reduction is
split multiplicative exactly when both tangent slopes at the node lie in the residue field, and
non-split exactly when neither does. A node is always a rational point
(`WeierstrassCurve.Affine.isSingular_of_Δ_eq_zero_of_c₄_ne_zero`), while a cusp need not be over
an imperfect field, which is why nodes and cusps are looked for over an algebraic closure.

These are the conditions under which Tau Ceti's `WeierstrassCurve.Affine.Point.cuspAddEquiv` and
`WeierstrassCurve.Affine.Point.nodeAddEquiv` identify the nonsingular points with the additive and
the multiplicative group: a root `α` of the tangent polynomial with `2 α + a₁ = 0`, a single
tangent slope, or with `2 α + a₁ ≠ 0`, two tangent slopes `α ≠ -a₁ - α` defined over the field.

## Main definitions

* `WeierstrassCurve.Affine.IsTangentSlope` (LMFDB `ec.split_multiplicative_reduction`): a tangent
  slope at a point.
* `WeierstrassCurve.HasNode` (LMFDB `ec.multiplicative_reduction`, `ec.reduction_type`): a nodal
  singularity.
* `WeierstrassCurve.HasCusp` (LMFDB `ec.additive_reduction`, `ec.reduction_type`): a cuspidal
  singularity.
* `WeierstrassCurve.HasSplitNode` (LMFDB `ec.split_multiplicative_reduction`): a node with both
  tangent slopes defined over the base field.
* `WeierstrassCurve.HasNonsplitNode` (LMFDB `ec.nonsplit_multiplicative_reduction`): a node with
  tangent slopes not defined over the base field.

## Main results

* `WeierstrassCurve.Affine.evalEval_vertical_of_isSingular`: the vertical line through a singular
  point is not tangent.
* `WeierstrassCurve.Affine.isTangentSlope_iff`: the tangent slopes at a singular point are the
  roots of `T² + a₁ T - (3 x₀ + a₂)`.
* `WeierstrassCurve.Affine.c₄_eq_of_isTangentSlope`: `c₄ = (2 m + a₁)⁴` for a tangent slope `m`.
* `WeierstrassCurve.Affine.exists_ne_isTangentSlope_iff` and
  `WeierstrassCurve.Affine.existsUnique_isTangentSlope_iff`: a singular point with a tangent slope
  has two distinct tangent slopes exactly when `c₄ ≠ 0`, and a single one exactly when `c₄ = 0`.
* `WeierstrassCurve.Affine.nodePolynomial_eq_of_isSingular`: the node polynomial is `c₄` times the
  tangent polynomial at a singular point.
* `WeierstrassCurve.Affine.isSingular_of_Δ_eq_zero_of_c₄_ne_zero`: a node is a rational point.
* `WeierstrassCurve.hasNode_iff`, `WeierstrassCurve.hasCusp_iff`,
  `WeierstrassCurve.hasSplitNode_iff` and `WeierstrassCurve.hasNonsplitNode_iff`: the four
  singularity types in terms of `Δ`, `c₄` and the node polynomial (Silverman III.1.4).
* `WeierstrassCurve.hasNode_or_hasCusp_of_Δ_eq_zero` and `WeierstrassCurve.HasNode.not_hasCusp`:
  the singularity of a singular Weierstrass cubic is a node or a cusp, and not both.
* `WeierstrassCurve.HasSplitNode.hasNode` and `WeierstrassCurve.HasNonsplitNode.hasNode`: split and
  non-split nodes are nodes.
* `WeierstrassCurve.hasCusp_cusp`, `WeierstrassCurve.hasSplitNode_x_cube_add_x_sq` and
  `WeierstrassCurve.hasNonsplitNode_x_cube_sub_x_sq`: `y² = x³` has a cusp, and over `ℚ`,
  `y² = x³ + x²` has a split node and `y² = x³ - x²` a non-split one.
* `WeierstrassCurve.hasMultiplicativeReduction_iff_hasNode`,
  `WeierstrassCurve.hasAdditiveReduction_iff_hasCusp`,
  `WeierstrassCurve.hasSplitMultiplicativeReduction_iff_hasSplitNode` and
  `WeierstrassCurve.isNonsplitMultiplicativeReduction_iff_hasNonsplitNode`: Mathlib's reduction
  types of a minimal equation are the singularity types of its reduction (Silverman VII.5.1).
* `WeierstrassCurve.hasMultiplicativeReduction_iff_or`: multiplicative reduction is split or
  non-split.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 and VII.5.
* W. Fulton, *Algebraic Curves*, Chapter 3: the tangent lines at a point of multiplicity `r` are
  the lines meeting the curve there with multiplicity greater than `r`.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : Affine F) {x₀ y₀ m m₁ m₂ : F}

variable (x₀ y₀ m) in
/-- A **tangent slope** of a Weierstrass curve `W` at a singular point `(x₀, y₀)` (LMFDB
`ec.split_multiplicative_reduction`): the line `y - y₀ = m (x - x₀)` meets the curve at `(x₀, y₀)`
with multiplicity at least `3`, that is, `t³` divides the Weierstrass polynomial restricted to the
line `t ↦ (x₀ + t, y₀ + m t)`. A singular point is a double point: every line through it meets the
curve there with multiplicity at least `2`, and the tangent lines are those meeting it with higher
multiplicity. The predicate is only used at singular points: at a nonsingular point the tangent
line meets the curve with multiplicity at least `2`, and at least `3` only at a flex. -/
def IsTangentSlope : Prop :=
  X ^ 3 ∣ (W⁄F[X]).polynomial.evalEval (C x₀ + X) (C y₀ + C m * X)

variable {W}

variable (m) in
lemma evalEval_line_of_isSingular (h : W.IsSingular x₀ y₀) : (W⁄F[X]).polynomial.evalEval (C x₀ + X)
    (C y₀ + C m * X) = C (m ^ 2 + W.a₁ * m - (3 * x₀ + W.a₂)) * X ^ 2 - X ^ 3 := by
  rcases (isSingular_iff' W x₀ y₀).mp h with ⟨hE, hX, hY⟩
  rw [equation_iff'] at hE
  rw [evalEval_polynomial]
  simp only [baseChange_a₁, baseChange_a₂, baseChange_a₃, baseChange_a₄, baseChange_a₆,
    algebraMap_eq]
  linear_combination (norm := skip) congrArg C hE + X * congrArg C hX + C m * X * congrArg C hY
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_zero]
  ring1

/-- **The vertical line through a singular point meets the curve there with multiplicity exactly
`2`**: the Weierstrass polynomial restricted to `t ↦ (x₀, y₀ + t)` is `t²`. So it is not tangent,
and every tangent line at a singular point has a slope. -/
lemma evalEval_vertical_of_isSingular (h : W.IsSingular x₀ y₀) :
    (W⁄F[X]).polynomial.evalEval (C x₀) (C y₀ + X) = X ^ 2 := by
  rcases (isSingular_iff' W x₀ y₀).mp h with ⟨hE, -, hY⟩
  rw [equation_iff'] at hE
  rw [evalEval_polynomial]
  simp only [baseChange_a₁, baseChange_a₂, baseChange_a₃, baseChange_a₄, baseChange_a₆,
    algebraMap_eq]
  linear_combination (norm := skip) congrArg C hE + X * congrArg C hY
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_zero]
  ring1

/-- **The tangent slopes at a singular point `(x₀, y₀)` are the roots of the tangent polynomial
`T² + a₁ T - (3 x₀ + a₂)`**: the Weierstrass polynomial restricted to the line of slope `m` is
`(m² + a₁ m - (3 x₀ + a₂)) t² - t³`. -/
lemma isTangentSlope_iff (h : W.IsSingular x₀ y₀) :
    W.IsTangentSlope x₀ y₀ m ↔ m ^ 2 + W.a₁ * m - (3 * x₀ + W.a₂) = 0 := by
  rw [IsTangentSlope, evalEval_line_of_isSingular m h, dvd_sub_self_right, X_pow_dvd_iff]
  exact ⟨fun hd ↦ by simpa only [coeff_C_mul_X_pow, ↓reduceIte] using hd 2 (by norm_num),
    fun hc d hd ↦ by simp [hc]⟩

lemma c₄_eq_of_isSingular (h : W.IsSingular x₀ y₀) : W.c₄ = (W.b₂ + 12 * x₀) ^ 2 := by
  rcases (isSingular_iff' W x₀ y₀).mp h with ⟨-, hX, hY⟩
  rw [c₄, b₂, b₄]
  linear_combination (-24 * W.a₁) * hY + 48 * hX

lemma x_mul_c₄_of_isSingular (h : W.IsSingular x₀ y₀) : x₀ * W.c₄ = 18 * W.b₆ - W.b₂ * W.b₄ := by
  rcases (isSingular_iff' W x₀ y₀).mp h with ⟨hE, hX, hY⟩
  rw [equation_iff'] at hE
  linear_combination (norm := (simp only [c₄, b₂, b₄, b₆]; ring1))
    72 * hE - 2 * (W.b₂ + 12 * x₀) * hX +
      (W.a₁ * (W.b₂ + 12 * x₀) - 18 * (2 * y₀ + W.a₁ * x₀ + W.a₃)) * hY

lemma b₂_add_mul_y_of_isSingular (h : W.IsSingular x₀ y₀) :
    (W.b₂ + 12 * x₀) * y₀ = W.a₁ * W.a₄ - 2 * W.a₂ * W.a₃ - 3 * W.a₁ * x₀ ^ 2 - 6 * W.a₃ * x₀ := by
  rcases (isSingular_iff' W x₀ y₀).mp h with ⟨-, hX, hY⟩
  rw [b₂]
  linear_combination W.a₁ * hX + (2 * W.a₂ + 6 * x₀) * hY

lemma sq_two_mul_add_a₁_of_isTangentSlope (h : W.IsSingular x₀ y₀) (hm : W.IsTangentSlope x₀ y₀ m) :
    (2 * m + W.a₁) ^ 2 = W.b₂ + 12 * x₀ := by
  rw [b₂]
  linear_combination 4 * (isTangentSlope_iff h).mp hm

/-- **At a singular point with tangent slope `m`, `c₄ = (2 m + a₁)⁴`**: the fourth power of the
difference of the two tangent slopes `m` and `-a₁ - m`. -/
lemma c₄_eq_of_isTangentSlope (h : W.IsSingular x₀ y₀) (hm : W.IsTangentSlope x₀ y₀ m) :
    W.c₄ = (2 * m + W.a₁) ^ 4 := by
  rw [c₄_eq_of_isSingular h, ← sq_two_mul_add_a₁_of_isTangentSlope h hm]
  ring1

lemma isTangentSlope_neg_sub (h : W.IsSingular x₀ y₀) (hm : W.IsTangentSlope x₀ y₀ m) :
    W.IsTangentSlope x₀ y₀ (-W.a₁ - m) :=
  (isTangentSlope_iff h).mpr <| by linear_combination (isTangentSlope_iff h).mp hm

lemma eq_or_eq_of_isTangentSlope (h : W.IsSingular x₀ y₀) (hm₁ : W.IsTangentSlope x₀ y₀ m₁)
    (hm₂ : W.IsTangentSlope x₀ y₀ m₂) : m₂ = m₁ ∨ m₂ = -W.a₁ - m₁ := by
  have h0 : (m₂ - m₁) * (m₂ - (-W.a₁ - m₁)) = 0 := by
    linear_combination (isTangentSlope_iff h).mp hm₂ - (isTangentSlope_iff h).mp hm₁
  exact (mul_eq_zero.mp h0).imp sub_eq_zero.mp sub_eq_zero.mp

/-- **A singular point with a tangent slope has two distinct tangent slopes exactly when
`c₄ ≠ 0`.** Over an algebraically closed field it always has a tangent slope. -/
lemma exists_ne_isTangentSlope_iff (h : W.IsSingular x₀ y₀) (hm : W.IsTangentSlope x₀ y₀ m) :
    (∃ m₁ m₂, m₁ ≠ m₂ ∧ W.IsTangentSlope x₀ y₀ m₁ ∧ W.IsTangentSlope x₀ y₀ m₂) ↔ W.c₄ ≠ 0 := by
  refine ⟨fun ⟨m₁, m₂, hne, hm₁, hm₂⟩ ↦ ?_, fun hc₄ ↦
    ⟨m, -W.a₁ - m, fun he ↦ hc₄ ?_, hm, isTangentSlope_neg_sub h hm⟩⟩
  · rw [c₄_eq_of_isTangentSlope h hm₁]
    rcases eq_or_eq_of_isTangentSlope h hm₁ hm₂ with rfl | rfl
    · exact absurd rfl hne
    · exact pow_ne_zero 4 fun h0 ↦ hne <| by linear_combination h0
  · rw [c₄_eq_of_isTangentSlope h hm]
    exact (pow_eq_zero_iff four_ne_zero).mpr <| by linear_combination he

/-- **A singular point with a tangent slope has a single tangent slope exactly when `c₄ = 0`.**
Over an algebraically closed field it always has a tangent slope. -/
lemma existsUnique_isTangentSlope_iff (h : W.IsSingular x₀ y₀) (hm : W.IsTangentSlope x₀ y₀ m) :
    (∃! m', W.IsTangentSlope x₀ y₀ m') ↔ W.c₄ = 0 := by
  refine ⟨fun ⟨m', _, hu⟩ ↦ ?_, fun hc₄ ↦ ⟨m, hm, fun m' hm' ↦ ?_⟩⟩
  · rw [c₄_eq_of_isTangentSlope h hm]
    exact (pow_eq_zero_iff four_ne_zero).mpr <| by
      linear_combination hu m hm - hu _ (isTangentSlope_neg_sub h hm)
  · rw [c₄_eq_of_isTangentSlope h hm] at hc₄
    rcases eq_or_eq_of_isTangentSlope h hm hm' with rfl | rfl
    · rfl
    · linear_combination -(pow_eq_zero_iff four_ne_zero).mp hc₄

lemma exists_isTangentSlope [IsAlgClosed F] (h : W.IsSingular x₀ y₀) :
    ∃ m, W.IsTangentSlope x₀ y₀ m := by
  rcases (splits_quadratic_iff_exists_root one_ne_zero).mp
    (IsAlgClosed.splits (C 1 * X ^ 2 + C W.a₁ * X + C (-(3 * x₀ + W.a₂)))) with ⟨m, hm⟩
  exact ⟨m, (isTangentSlope_iff h).mpr <| by linear_combination hm⟩

/-- **The node polynomial is `c₄` times the tangent polynomial at a singular point**: if `(x₀, y₀)`
is singular, Tau Ceti's `WeierstrassCurve.nodePolynomial`, the polynomial of Mathlib's
`WeierstrassCurve.HasSplitMultiplicativeReduction`, is `c₄ (T² + a₁ T - (3 x₀ + a₂))`. -/
lemma nodePolynomial_eq_of_isSingular (h : W.IsSingular x₀ y₀) :
    W.nodePolynomial = C W.c₄ * (C 1 * X ^ 2 + C W.a₁ * X + C (-(3 * x₀ + W.a₂))) := by
  rw [C_1, one_mul]
  refine W.nodePolynomial_eq_C_mul ?_
  rw [nodePolynomial_coeff_zero]
  linear_combination -3 * x_mul_c₄_of_isSingular h

lemma splits_nodePolynomial_iff (h : W.IsSingular x₀ y₀) (hc₄ : W.c₄ ≠ 0) :
    W.nodePolynomial.Splits ↔ ∃ m, W.IsTangentSlope x₀ y₀ m := by
  rw [nodePolynomial_eq_of_isSingular h, splits_mul_iff_right (C_ne_zero.mpr hc₄) (Splits.C _),
    splits_quadratic_iff_exists_root one_ne_zero]
  exact exists_congr fun m ↦ by rw [isTangentSlope_iff h, one_mul, ← sub_eq_add_neg]

lemma isSingular_of_isSingular_map {L : Type*} [Field L] (φ : F →+* L) {x y : L}
    (h : (W.map φ).IsSingular x y) (hc₄ : W.c₄ ≠ 0) :
    letI x₀ : F := (18 * W.b₆ - W.b₂ * W.b₄) / W.c₄
    W.IsSingular x₀
      ((W.a₁ * W.a₄ - 2 * W.a₂ * W.a₃ - 3 * W.a₁ * x₀ ^ 2 - 6 * W.a₃ * x₀) / (W.b₂ + 12 * x₀)) := by
  set x₀ : F := (18 * W.b₆ - W.b₂ * W.b₄) / W.c₄
  set y₀ : F :=
    (W.a₁ * W.a₄ - 2 * W.a₂ * W.a₃ - 3 * W.a₁ * x₀ ^ 2 - 6 * W.a₃ * x₀) / (W.b₂ + 12 * x₀) with hy₀
  have hc₄' : φ W.c₄ ≠ 0 := (map_ne_zero φ).mpr hc₄
  have hx : φ x₀ = x := by
    rw [map_div₀, div_eq_iff hc₄', ← map_c₄, x_mul_c₄_of_isSingular h, map_b₆, map_b₂, map_b₄,
      map_sub, map_mul, map_mul, map_ofNat]
  subst hx
  have hb : φ (W.b₂ + 12 * x₀) ≠ 0 := by
    rw [map_add, map_mul, map_ofNat, ← map_b₂]
    exact fun h0 ↦ hc₄' <| by rw [← map_c₄, c₄_eq_of_isSingular h, h0, zero_pow two_ne_zero]
  have hy : (φ W.b₂ + 12 * φ x₀) * y = φ W.a₁ * φ W.a₄ - 2 * φ W.a₂ * φ W.a₃ -
      3 * φ W.a₁ * φ x₀ ^ 2 - 6 * φ W.a₃ * φ x₀ := by
    simpa only [map_b₂, map_a₁, map_a₄, map_a₂, map_a₃] using b₂_add_mul_y_of_isSingular h
  have hy' : φ y₀ = y := by
    rw [hy₀, map_div₀, div_eq_iff hb]
    simp only [map_sub, map_mul, map_ofNat, map_pow, map_add]
    linear_combination -hy
  rw [← hy'] at h
  exact (map_isSingular φ.injective W _ _).mp h

/-- **The singular point of a Weierstrass curve with `Δ = 0` and `c₄ ≠ 0` is rational**: it is
`(x₀, (a₁ a₄ - 2 a₂ a₃ - 3 a₁ x₀² - 6 a₃ x₀) / (b₂ + 12 x₀))` with `x₀ = (18 b₆ - b₂ b₄) / c₄`.
So a node is a point over the base field, with no perfectness assumption. -/
lemma isSingular_of_Δ_eq_zero_of_c₄_ne_zero (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0) :
    letI x₀ : F := (18 * W.b₆ - W.b₂ * W.b₄) / W.c₄
    W.IsSingular x₀
      ((W.a₁ * W.a₄ - 2 * W.a₂ * W.a₃ - 3 * W.a₁ * x₀ ^ 2 - 6 * W.a₃ * x₀) / (W.b₂ + 12 * x₀)) := by
  rcases exists_isSingular_of_Δ_eq_zero (W.map (algebraMap F (AlgebraicClosure F)))
    (by rw [map_Δ, hΔ, map_zero]) with ⟨x, y, h⟩
  exact isSingular_of_isSingular_map _ h hc₄

end WeierstrassCurve.Affine

namespace WeierstrassCurve

section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (L : Type*) [Field L] [Algebra F L]

/-- A Weierstrass curve `W` over a field `F` has a **nodal singularity** (LMFDB
`ec.multiplicative_reduction`, `ec.reduction_type`): over an algebraic closure of `F` it has a
singular point with two distinct tangent slopes, that is, two distinct tangent lines. -/
def HasNode : Prop :=
  ∃ x y m₁ m₂ : AlgebraicClosure F, (W⁄(AlgebraicClosure F)).toAffine.IsSingular x y ∧ m₁ ≠ m₂ ∧
    (W⁄(AlgebraicClosure F)).toAffine.IsTangentSlope x y m₁ ∧
      (W⁄(AlgebraicClosure F)).toAffine.IsTangentSlope x y m₂

/-- A Weierstrass curve `W` over a field `F` has a **cuspidal singularity** (LMFDB
`ec.additive_reduction`, `ec.reduction_type`): over an algebraic closure of `F` it has a singular
point with a single tangent slope, that is, a single tangent line. -/
def HasCusp : Prop :=
  ∃ x y : AlgebraicClosure F, (W⁄(AlgebraicClosure F)).toAffine.IsSingular x y ∧
    ∃! m, (W⁄(AlgebraicClosure F)).toAffine.IsTangentSlope x y m

/-- A Weierstrass curve `W` over a field `F` has a **nodal singularity with both tangent slopes
defined over `F`** (LMFDB `ec.split_multiplicative_reduction`): a singular point over `F` with two
distinct tangent slopes in `F`. A node has only two tangent slopes, so these are both of them. -/
def HasSplitNode : Prop :=
  ∃ x y m₁ m₂ : F, W.toAffine.IsSingular x y ∧ m₁ ≠ m₂ ∧ W.toAffine.IsTangentSlope x y m₁ ∧
    W.toAffine.IsTangentSlope x y m₂

/-- A Weierstrass curve `W` over a field `F` has a **nodal singularity with tangent slopes not
defined over `F`** (LMFDB `ec.nonsplit_multiplicative_reduction`): a singular point over `F` with
two distinct tangent slopes over an algebraic closure of `F`, none of which lies in `F`. -/
def HasNonsplitNode : Prop :=
  ∃ x y : F, W.toAffine.IsSingular x y ∧ (∃ m₁ m₂ : AlgebraicClosure F, m₁ ≠ m₂ ∧
    (W⁄(AlgebraicClosure F)).toAffine.IsTangentSlope (algebraMap F _ x) (algebraMap F _ y) m₁ ∧
      (W⁄(AlgebraicClosure F)).toAffine.IsTangentSlope (algebraMap F _ x) (algebraMap F _ y) m₂) ∧
    ∀ m, ¬W.toAffine.IsTangentSlope x y m

variable {W}

lemma Δ_baseChange_eq_zero_iff : (W⁄L).Δ = 0 ↔ W.Δ = 0 := by
  rw [baseChange, map_Δ]
  exact map_eq_zero_iff _ (algebraMap F L).injective

lemma c₄_baseChange_eq_zero_iff : (W⁄L).c₄ = 0 ↔ W.c₄ = 0 := by
  rw [baseChange, map_c₄]
  exact map_eq_zero_iff _ (algebraMap F L).injective

/-- **A Weierstrass curve has a node exactly when `Δ = 0` and `c₄ ≠ 0`** (Silverman III.1.4). -/
lemma hasNode_iff : W.HasNode ↔ W.Δ = 0 ∧ W.c₄ ≠ 0 := by
  rw [Ne, ← Δ_baseChange_eq_zero_iff (AlgebraicClosure F),
    ← c₄_baseChange_eq_zero_iff (AlgebraicClosure F)]
  refine ⟨fun ⟨x, y, m₁, m₂, h, hne, hm₁, hm₂⟩ ↦
    ⟨h.Δ_eq_zero, (Affine.exists_ne_isTangentSlope_iff h hm₁).mp ⟨m₁, m₂, hne, hm₁, hm₂⟩⟩,
    fun ⟨hΔ, hc₄⟩ ↦ ?_⟩
  rcases Affine.exists_isSingular_of_Δ_eq_zero _ hΔ with ⟨x, y, h⟩
  rcases Affine.exists_isTangentSlope h with ⟨m, hm⟩
  rcases (Affine.exists_ne_isTangentSlope_iff h hm).mpr hc₄ with ⟨m₁, m₂, hne, hm₁, hm₂⟩
  exact ⟨x, y, m₁, m₂, h, hne, hm₁, hm₂⟩

/-- **A Weierstrass curve has a cusp exactly when `Δ = c₄ = 0`** (Silverman III.1.4). -/
lemma hasCusp_iff : W.HasCusp ↔ W.Δ = 0 ∧ W.c₄ = 0 := by
  rw [← Δ_baseChange_eq_zero_iff (AlgebraicClosure F),
    ← c₄_baseChange_eq_zero_iff (AlgebraicClosure F)]
  refine ⟨fun ⟨x, y, h, hu⟩ ↦ ?_, fun ⟨hΔ, hc₄⟩ ↦ ?_⟩
  · rcases hu.exists with ⟨m, hm⟩
    exact ⟨h.Δ_eq_zero, (Affine.existsUnique_isTangentSlope_iff h hm).mp hu⟩
  · rcases Affine.exists_isSingular_of_Δ_eq_zero _ hΔ with ⟨x, y, h⟩
    rcases Affine.exists_isTangentSlope h with ⟨m, hm⟩
    exact ⟨x, y, h, (Affine.existsUnique_isTangentSlope_iff h hm).mpr hc₄⟩

/-- **A Weierstrass curve has a node with both tangent slopes defined over the base field exactly
when `Δ = 0`, `c₄ ≠ 0` and its node polynomial splits.** -/
lemma hasSplitNode_iff : W.HasSplitNode ↔ W.Δ = 0 ∧ W.c₄ ≠ 0 ∧ W.nodePolynomial.Splits := by
  refine ⟨fun ⟨x, y, m₁, m₂, h, hne, hm₁, hm₂⟩ ↦ ?_, fun ⟨hΔ, hc₄, hs⟩ ↦ ?_⟩
  · have hc₄ : W.c₄ ≠ 0 := (Affine.exists_ne_isTangentSlope_iff h hm₁).mp ⟨m₁, m₂, hne, hm₁, hm₂⟩
    exact ⟨h.Δ_eq_zero, hc₄, (Affine.splits_nodePolynomial_iff h hc₄).mpr ⟨m₁, hm₁⟩⟩
  · have h : W.toAffine.IsSingular _ _ := Affine.isSingular_of_Δ_eq_zero_of_c₄_ne_zero hΔ hc₄
    rcases (Affine.splits_nodePolynomial_iff h hc₄).mp hs with ⟨m, hm⟩
    rcases (Affine.exists_ne_isTangentSlope_iff h hm).mpr hc₄ with ⟨m₁, m₂, hne, hm₁, hm₂⟩
    exact ⟨_, _, m₁, m₂, h, hne, hm₁, hm₂⟩

/-- **A Weierstrass curve has a node with tangent slopes not defined over the base field exactly
when `Δ = 0`, `c₄ ≠ 0` and its node polynomial does not split.** -/
lemma hasNonsplitNode_iff : W.HasNonsplitNode ↔ W.Δ = 0 ∧ W.c₄ ≠ 0 ∧ ¬W.nodePolynomial.Splits := by
  refine ⟨fun ⟨x, y, h, ⟨m₁, m₂, hne, hm₁, hm₂⟩, hn⟩ ↦ ?_, fun ⟨hΔ, hc₄, hs⟩ ↦ ?_⟩
  · have hc₄ : W.c₄ ≠ 0 := by
      rw [Ne, ← c₄_baseChange_eq_zero_iff (AlgebraicClosure F)]
      exact (Affine.exists_ne_isTangentSlope_iff (h.map _) hm₁).mp ⟨m₁, m₂, hne, hm₁, hm₂⟩
    exact ⟨h.Δ_eq_zero, hc₄, fun hs ↦ ((Affine.splits_nodePolynomial_iff h hc₄).mp hs).elim hn⟩
  · have h : W.toAffine.IsSingular _ _ := Affine.isSingular_of_Δ_eq_zero_of_c₄_ne_zero hΔ hc₄
    have h' : (W⁄(AlgebraicClosure F)).toAffine.IsSingular _ _ := h.map (algebraMap F _)
    rcases Affine.exists_isTangentSlope h' with ⟨m, hm⟩
    refine ⟨_, _, h, (Affine.exists_ne_isTangentSlope_iff h' hm).mpr ?_, fun m hm ↦ hs <|
      (Affine.splits_nodePolynomial_iff h hc₄).mpr ⟨m, hm⟩⟩
    rwa [Ne, c₄_baseChange_eq_zero_iff]

/-- **The singularity of a singular Weierstrass cubic is a node or a cusp.** -/
lemma hasNode_or_hasCusp_of_Δ_eq_zero (hΔ : W.Δ = 0) : W.HasNode ∨ W.HasCusp :=
  (em (W.c₄ = 0)).symm.imp (hasNode_iff.mpr ⟨hΔ, ·⟩) (hasCusp_iff.mpr ⟨hΔ, ·⟩)

/-- **A node is not a cusp.** -/
lemma HasNode.not_hasCusp (h : W.HasNode) : ¬W.HasCusp :=
  fun h' ↦ (hasNode_iff.mp h).2 (hasCusp_iff.mp h').2

/-- **A node with both tangent slopes defined over the base field is a node.** -/
lemma HasSplitNode.hasNode (h : W.HasSplitNode) : W.HasNode :=
  hasNode_iff.mpr <| (hasSplitNode_iff.mp h).imp_right And.left

/-- **A node with tangent slopes not defined over the base field is a node.** -/
lemma HasNonsplitNode.hasNode (h : W.HasNonsplitNode) : W.HasNode :=
  hasNode_iff.mpr <| (hasNonsplitNode_iff.mp h).imp_right And.left

/-- **Tau Ceti's cusp curve `y² = x³` has a cusp.** -/
lemma hasCusp_cusp : (cusp F).HasCusp :=
  hasCusp_iff.mpr ⟨by simp [Δ, b₄, b₆, b₈], by simp [c₄, b₂, b₄]⟩

/-- **The cubic `y² = x³ + x²` over `ℚ` has a node with both tangent slopes `±1` in `ℚ`.** -/
lemma hasSplitNode_x_cube_add_x_sq : (⟨0, 1, 0, 0, 0⟩ : WeierstrassCurve ℚ).HasSplitNode := by
  have h : (⟨0, 1, 0, 0, 0⟩ : WeierstrassCurve ℚ).toAffine.IsSingular 0 0 := by simp
  exact ⟨0, 0, 1, -1, h, by norm_num, (Affine.isTangentSlope_iff h).mpr <| by norm_num,
    (Affine.isTangentSlope_iff h).mpr <| by norm_num⟩

/-- **The cubic `y² = x³ - x²` over `ℚ` has a node with tangent slopes `±i` not in `ℚ`.** -/
lemma hasNonsplitNode_x_cube_sub_x_sq :
    (⟨0, -1, 0, 0, 0⟩ : WeierstrassCurve ℚ).HasNonsplitNode := by
  have h : (⟨0, -1, 0, 0, 0⟩ : WeierstrassCurve ℚ).toAffine.IsSingular 0 0 := by simp
  have hc₄ : (⟨0, -1, 0, 0, 0⟩ : WeierstrassCurve ℚ).c₄ ≠ 0 := by norm_num [c₄, b₂, b₄]
  refine hasNonsplitNode_iff.mpr ⟨h.Δ_eq_zero, hc₄, fun hs ↦ ?_⟩
  rcases (Affine.splits_nodePolynomial_iff h hc₄).mp hs with ⟨m, hm⟩
  rw [Affine.isTangentSlope_iff h] at hm
  nlinarith [sq_nonneg m]

end Field

section Reduction

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K] {W : WeierstrassCurve K} [IsMinimal R W]

/-- **Multiplicative reduction is nodal reduction** (Silverman VII.5.1): a minimal equation has
multiplicative reduction, Mathlib's `v(Δ) < 1` and `v(c₄) = 1`, exactly when its reduction has a
node. -/
lemma hasMultiplicativeReduction_iff_hasNode :
    W.HasMultiplicativeReduction R ↔ (W.reduction R).HasNode := by
  rw [hasNode_iff, reduction_Δ_eq_zero_iff]
  refine ⟨fun h ↦ ⟨h.not_hasGoodReduction, h.reduction_c₄_ne_zero R⟩, fun ⟨hg, hc₄⟩ ↦ ?_⟩
  rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction R (W := W) with
    hg' | hm | ha
  · exact absurd hg' hg
  · exact hm
  · exact absurd (ha.reduction_c₄_eq_zero R) hc₄

/-- **Additive reduction is cuspidal reduction** (Silverman VII.5.1): a minimal equation has
additive reduction, Mathlib's `v(Δ) < 1` and `v(c₄) < 1`, exactly when its reduction has a cusp. -/
lemma hasAdditiveReduction_iff_hasCusp : W.HasAdditiveReduction R ↔ (W.reduction R).HasCusp := by
  rw [hasCusp_iff, reduction_Δ_eq_zero_iff]
  refine ⟨fun h ↦ ⟨h.not_hasGoodReduction, h.reduction_c₄_eq_zero R⟩, fun ⟨hg, hc₄⟩ ↦ ?_⟩
  rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction R (W := W) with
    hg' | hm | ha
  · exact absurd hg' hg
  · exact absurd hc₄ (hm.reduction_c₄_ne_zero R)
  · exact ha

/-- **Split multiplicative reduction is reduction with a node whose tangent slopes are defined over
the residue field**: Mathlib's condition that the node polynomial of the integral model splits
over the residue field is that both tangent slopes at the node of the reduction lie in it. -/
lemma hasSplitMultiplicativeReduction_iff_hasSplitNode :
    W.HasSplitMultiplicativeReduction R ↔ (W.reduction R).HasSplitNode := by
  rw [hasSplitNode_iff, ← and_assoc, ← hasNode_iff, ← hasMultiplicativeReduction_iff_hasNode R]
  exact ⟨fun h ↦ ⟨h.toHasMultiplicativeReduction,
    (h.toHasMultiplicativeReduction.splits_nodePolynomial_reduction_iff R).mpr h⟩,
    fun ⟨hm, hs⟩ ↦ (hm.splits_nodePolynomial_reduction_iff R).mp hs⟩

/-- **Non-split multiplicative reduction is reduction with a node whose tangent slopes are not
defined over the residue field.** -/
lemma isNonsplitMultiplicativeReduction_iff_hasNonsplitNode :
    W.IsNonsplitMultiplicativeReduction R ↔ (W.reduction R).HasNonsplitNode := by
  rw [hasNonsplitNode_iff, ← and_assoc, ← hasNode_iff, ← hasMultiplicativeReduction_iff_hasNode R,
    IsNonsplitMultiplicativeReduction]
  exact and_congr_right fun hm ↦ not_congr (hm.splits_nodePolynomial_reduction_iff R).symm

/-- **Multiplicative reduction is split or non-split** (LMFDB `ec.multiplicative_reduction`). -/
lemma hasMultiplicativeReduction_iff_or : W.HasMultiplicativeReduction R ↔
    W.HasSplitMultiplicativeReduction R ∨ W.IsNonsplitMultiplicativeReduction R :=
  ⟨fun h ↦ (em _).imp id (⟨h, ·⟩), (·.elim (·.toHasMultiplicativeReduction) (·.1))⟩

end Reduction

end WeierstrassCurve
