import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.Equation
import Mathlib.Algebra.Polynomial.SpecificDegree
import TauCeti.FieldTheory.FunctionField.Hyperelliptic.Genus.Basic

/-!
# The function field of a hyperelliptic Weierstrass equation

A Weierstrass equation `y² + h(x)y = f(x)` over a field `K` defines the function field
`K(x, y) = K(x)[Y] / (Y² + h(x)Y - f(x))` of a curve. When `2` is invertible and the discriminant
is nonzero, `f + h²/4` and `4f + h²` are separable, and `w = 2y + h(x)` satisfies the simplified
equation `w² = 4f + h²`, with `4f + h²` squarefree of degree `2g + 1` or `2g + 2`. Hence
`Y² + h(x)Y - f(x)` is irreducible, and Tau Ceti's computation of the genus of `w² = F(x)` shows
that the function field has genus `g`, and is hyperelliptic for `g ≥ 2`.

## Main definitions

* `HyperellipticEquation.equationPolynomial`: the polynomial `Y² + h(x)Y - f(x)` over `K(x)`.
* `HyperellipticEquation.FunctionField` (LMFDB `g2c.g2curve`): the function field `K(x, y)`.
* `HyperellipticEquation.y` and `HyperellipticEquation.w`: the coordinates `y` and `w = 2y + h(x)`.

## Main results

* `HyperellipticEquation.separable_rhs` and `HyperellipticEquation.separable_simplifiedPolynomial`:
  an equation with nonzero discriminant has `f + h²/4` and `4f + h²` separable.
* `HyperellipticEquation.irreducible_equationPolynomial`: an equation with nonzero discriminant
  defines a field.
* `HyperellipticEquation.genus_functionField`: its function field has genus `g`.
* `HyperellipticEquation.isHyperellipticFunctionField`: for `g ≥ 2`, its function field is
  hyperelliptic.
-/

open Polynomial
open scoped IntermediateField

namespace HyperellipticEquation

variable {g : ℕ} {K : Type*} [Field K] (E : HyperellipticEquation g K)

/-- The polynomial `Y² + h(x)Y - f(x)` over the rational function field `K(x)`, whose root is the
coordinate `y` of a Weierstrass equation `y² + h(x)y = f(x)`. -/
noncomputable def equationPolynomial : (RatFunc K)[X] :=
  X ^ 2 + C (algebraMap K[X] (RatFunc K) E.h) * X - C (algebraMap K[X] (RatFunc K) E.f)

/-- The **function field** `K(x, y)` of a Weierstrass equation `y² + h(x)y = f(x)` (LMFDB
`g2c.g2curve`): the quotient of `K(x)[Y]` by `Y² + h(x)Y - f(x)`. It is a field when the
discriminant is nonzero (`HyperellipticEquation.irreducible_equationPolynomial`). -/
abbrev FunctionField : Type _ :=
  AdjoinRoot E.equationPolynomial

/-- The coordinate `y` in the function field of a Weierstrass equation. -/
noncomputable def y : E.FunctionField :=
  AdjoinRoot.root E.equationPolynomial

lemma aeval_equationPolynomial {A : Type*} [CommRing A] [Algebra (RatFunc K) A] (z : A) : aeval z
    E.equationPolynomial = z ^ 2 + algebraMap (RatFunc K) A (algebraMap K[X] _ E.h) * z - algebraMap
    (RatFunc K) A (algebraMap K[X] _ E.f) := by
  rw [equationPolynomial, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, aeval_C]

lemma y_sq_add : E.y ^ 2 + algebraMap (RatFunc K) E.FunctionField (algebraMap K[X] _ E.h) * E.y =
    algebraMap (RatFunc K) E.FunctionField (algebraMap K[X] _ E.f) := by
  rw [← sub_eq_zero, ← aeval_equationPolynomial, y, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

/-- The coordinate `w = 2y + h(x)` of the simplified equation `w² = 4f + h²`. -/
noncomputable def w : E.FunctionField :=
  2 * E.y + algebraMap (RatFunc K) E.FunctionField (algebraMap K[X] _ E.h)

lemma w_sq : E.w ^ 2 = algebraMap (RatFunc K) E.FunctionField (algebraMap K[X] _
    E.simplifiedPolynomial) := by
  rw [w, simplifiedPolynomial, map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_ofNat,
    map_ofNat]
  linear_combination 4 * E.y_sq_add

lemma natDegree_equationPolynomial : E.equationPolynomial.natDegree = 2 := by
  rw [equationPolynomial]
  compute_degree!

variable [Invertible (2 : K)] {E} (hE : E.discriminant ≠ 0)

include hE

/-- **An equation with nonzero discriminant has `f + h²/4` separable.** -/
lemma separable_rhs : E.rhs.Separable :=
  (discr_ne_zero_iff <| ne_zero_of_natDegree_gt <| (2 * g).succ_pos.trans_le <|
    le_natDegree_rhs hE).mp fun h ↦ hE <| by simp [discriminant, binaryDiscr, h]

/-- **An equation with nonzero discriminant has `4f + h²` separable.** -/
lemma separable_simplifiedPolynomial : E.simplifiedPolynomial.Separable := by
  rw [← four_mul_rhs, ← C_ofNat]
  exact (separable_rhs hE).unit_mul <| isUnit_C.mpr isUnit_four

lemma squarefree_simplifiedPolynomial : Squarefree E.simplifiedPolynomial :=
  (separable_simplifiedPolynomial hE).squarefree

/-- **The equation polynomial of an equation with nonzero discriminant is irreducible**, so that
its function field is a field: `4f + h²` is squarefree of positive degree, hence not a square in
`K(x)`. -/
lemma irreducible_equationPolynomial : Irreducible E.equationPolynomial := by
  refine irreducible_of_degree_le_three_of_not_isRoot ?_ fun r hr ↦ ?_
  · simp [natDegree_equationPolynomial]
  rw [IsRoot, ← coe_aeval_eq_eval, aeval_equationPolynomial] at hr
  have hsq : (2 * r + algebraMap K[X] _ E.h) ^ 2 = algebraMap K[X] _ E.simplifiedPolynomial := by
    rw [simplifiedPolynomial, map_add, map_mul, map_pow, map_ofNat]
    linear_combination 4 * hr
  rcases IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow two_pos
    (hsq ▸ isIntegral_algebraMap) with ⟨c, hc⟩
  have hF : E.simplifiedPolynomial = c ^ 2 :=
    IsFractionRing.injective K[X] (RatFunc K) (by rw [map_pow, hc, hsq])
  have hc' : IsUnit c := squarefree_simplifiedPolynomial hE c (dvd_of_eq (by rw [hF, sq]))
  have h₀ : E.simplifiedPolynomial.natDegree = 0 := natDegree_eq_zero_of_isUnit (hF ▸ hc'.pow 2)
  rcases natDegree_simplifiedPolynomial_eq hE with h | h <;> omega

omit hE

variable [Fact (Irreducible E.equationPolynomial)]

lemma y_mem_adjoin_w : E.y ∈ (RatFunc K)⟮E.w⟯ := by
  have h2 : (2 : RatFunc K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (RatFunc K)) 2, ← map_zero (algebraMap K (RatFunc K))]
    exact (algebraMap K (RatFunc K)).injective.ne two_ne_zero
  have hy : E.y = algebraMap (RatFunc K) E.FunctionField 2⁻¹ * (E.w - algebraMap (RatFunc K)
      E.FunctionField (algebraMap K[X] _ E.h)) := by
    rw [w, add_sub_cancel_right, ← mul_assoc,
      ← map_ofNat (algebraMap (RatFunc K) E.FunctionField) 2, ← map_mul, inv_mul_cancel₀ h2,
      map_one, one_mul]
  rw [hy]
  exact mul_mem (IntermediateField.algebraMap_mem _ _)
    (sub_mem (IntermediateField.mem_adjoin_simple_self _ _) (IntermediateField.algebraMap_mem _ _))

lemma adjoin_w_eq_top : (RatFunc K)⟮E.w⟯ = ⊤ :=
  top_le_iff.mp <| (IntermediateField.adjoin_root_eq_top E.equationPolynomial).symm.le.trans <|
    IntermediateField.adjoin_simple_le_iff.mpr y_mem_adjoin_w

include hE

/-- **The function field of a Weierstrass equation of genus `g` with nonzero discriminant has genus
`g`**: it is `K(x, w)` with `w² = 4f + h²`, a squarefree polynomial of degree `2g + 1` or
`2g + 2`. -/
lemma genus_functionField : TauCeti.genus K E.FunctionField = g := by
  rcases natDegree_simplifiedPolynomial_eq hE with h | h <;>
  rw [TauCeti.genus_eq_of_sq_eq two_ne_zero (squarefree_simplifiedPolynomial hE) (by omega)
    adjoin_w_eq_top E.w_sq, h] <;> omega

/-- **The function field of a Weierstrass equation of genus `g ≥ 2` with nonzero discriminant is
hyperelliptic**: `K(x)` is a rational subfield of index two. -/
lemma isHyperellipticFunctionField (hg : 2 ≤ g) :
    TauCeti.IsHyperellipticFunctionField K E.FunctionField := by
  refine TauCeti.isHyperellipticFunctionField_of_sq_eq two_ne_zero
    (squarefree_simplifiedPolynomial hE) ?_ adjoin_w_eq_top E.w_sq
  rcases natDegree_simplifiedPolynomial_eq hE with h | h <;> omega

end HyperellipticEquation
