import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Weierstrass equations of hyperelliptic curves and their discriminants

A Weierstrass equation `y² + h(x)y = f(x)` of genus `g` has `deg h ≤ g + 1` and `deg f ≤ 2g + 2`.
Completing the square turns it into `(y + h/2)² = f + h²/4`, and its discriminant is `2^(4g)`
times the discriminant of `f + h²/4` as a binary form of degree `2g + 2`. For genus two this is
the LMFDB's `2⁸ lc(f + h²/4)² disc(f + h²/4)` or `2⁸ disc(f + h²/4)`, according as `f + h²/4` has
degree five or six, and it vanishes when `f + h²/4` has smaller degree, as then the binary form
has a multiple root at infinity.

The discriminant is only defined when `2` is invertible: in general it is the polynomial with
integer coefficients `2^(-4(g + 1)) disc(4f + h²)`, whose integrality is not proved here.

The equation also defines the weighted homogeneous equation `y² + h(x, z)y = f(x, z)` of degree
`2g + 2`, with `y` of weight `g + 1` and `x`, `z` of weight `1`, whose zero locus in the weighted
projective plane is the smooth projective model of the curve, and the simplified equation
`w² = 4f + h²`, with `w = 2y + h(x)`.

## Main definitions

* `Polynomial.binaryDiscr`: the discriminant of a polynomial as a binary form of a given degree.
* `Polynomial.homogenizeXZ`: the homogenisation of a polynomial in two of three variables.
* `HyperellipticEquation` (LMFDB `g2c.g2curve`, `g2c.minimal_equation`): Weierstrass equations
  `y² + h(x)y = f(x)` of genus `g`.
* `HyperellipticEquation.map`: base change of a Weierstrass equation.
* `HyperellipticEquation.weightedEquation` (LMFDB `g2c.minimal_equation`): the weighted
  homogeneous equation.
* `HyperellipticEquation.simplifiedPolynomial`: the polynomial `4f + h²` of the simplified
  equation.
* `HyperellipticEquation.rhs`: the polynomial `f + h²/4`.
* `HyperellipticEquation.discriminant` (LMFDB `g2c.discriminant`): the discriminant.

## Main results

* `HyperellipticEquation.isWeightedHomogeneous_weightedEquation`: the weighted homogeneous equation
  is weighted homogeneous of degree `2g + 2`.
* `HyperellipticEquation.aeval_weightedEquation`: the weighted homogeneous equation at `z = 1` is
  the Weierstrass equation.
* `HyperellipticEquation.discriminant_of_natDegree_eq` and
  `HyperellipticEquation.discriminant_of_natDegree_eq_add_one`: the LMFDB's formula for the
  discriminant.
* `HyperellipticEquation.le_natDegree_rhs` and
  `HyperellipticEquation.natDegree_simplifiedPolynomial_eq`: an equation with nonzero discriminant
  has `f + h²/4` and `4f + h²` of degree `2g + 1` or `2g + 2`.
* `HyperellipticEquation.natDegree_h_eq_or_le_natDegree_f`: an equation with nonzero
  discriminant has `deg h = g + 1` or `deg f ≥ 2g + 1`.
-/

open Polynomial
open MvPolynomial (IsWeightedHomogeneous isWeightedHomogeneous_X)

variable {g : ℕ} {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra R A] (x y : A)

namespace Polynomial

variable {p : R[X]} {n d : ℕ}

variable (p n) in
/-- The **discriminant of a polynomial `p` as a binary form of degree `n`**, for `n ≥ 2`: the
discriminant of the homogenisation of `p` to degree `n`. It is `disc p` when `p` has degree `n`,
it is `lc(p)² disc p` when `p` has degree `n - 1`, and it is `0` when `p` has smaller degree, as
the binary form then has a multiple root at infinity. -/
noncomputable def binaryDiscr : R :=
  if p.natDegree = n then p.discr else
    if p.natDegree + 1 = n then p.leadingCoeff ^ 2 * p.discr else 0

lemma binaryDiscr_of_natDegree_eq (h : p.natDegree = n) : p.binaryDiscr n = p.discr :=
  ite_eq_left h

lemma binaryDiscr_of_natDegree_add_one_eq (h : p.natDegree + 1 = n) :
    p.binaryDiscr n = p.leadingCoeff ^ 2 * p.discr := by
  rw [binaryDiscr, ite_eq_right (by omega), ite_eq_left h]

lemma binaryDiscr_of_natDegree_add_one_lt (h : p.natDegree + 1 < n) : p.binaryDiscr n = 0 := by
  rw [binaryDiscr, ite_eq_right (by omega), ite_eq_right (by omega)]

variable (p d) in
/-- The homogenisation `∑ pᵢ xⁱ z^(d - i)` of a polynomial `p` to degree `d`, in the variables
`x = X 0` and `z = X 2` of `MvPolynomial (Fin 3) R`. -/
noncomputable def homogenizeXZ : MvPolynomial (Fin 3) R :=
  ∑ i ∈ Finset.range (d + 1), .C (p.coeff i) * .X 0 ^ i * .X 2 ^ (d - i)

variable (p d) in
lemma isWeightedHomogeneous_homogenizeXZ (m : ℕ) :
    IsWeightedHomogeneous ![1, m, 1] (p.homogenizeXZ d) d := by
  refine IsWeightedHomogeneous.sum _ _ _ fun i hi ↦ ?_
  convert (((isWeightedHomogeneous_X R ![1, m, 1] 0).pow i).mul
    ((isWeightedHomogeneous_X R ![1, m, 1] 2).pow (d - i))).C_mul (p.coeff i) using 1
  · rw [mul_assoc]
  · simp at hi ⊢
    omega

lemma aeval_homogenizeXZ (hp : p.natDegree ≤ d) :
    MvPolynomial.aeval ![x, y, 1] (p.homogenizeXZ d) = aeval x p := by
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hp), homogenizeXZ, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [Algebra.smul_def]

end Polynomial

variable (g R) in
/-- A **Weierstrass equation** `y² + h(x)y = f(x)` of genus `g` over a commutative ring `R` (LMFDB
`g2c.g2curve` for `g = 2`, and `g2c.minimal_equation`): polynomials `h` and `f` of degrees at most
`g + 1` and `2g + 2`. Over a field of characteristic not two with nonzero discriminant, it defines
a curve of genus `g` (`HyperellipticEquation.genus_functionField`), whose smooth projective model
is the weighted homogeneous equation `y² + h(x, z)y = f(x, z)` of degree `2g + 2`
(`HyperellipticEquation.weightedEquation`). -/
@[ext]
structure HyperellipticEquation where
  /-- The polynomial `h` of `y² + h(x)y = f(x)`. -/
  h : R[X]
  /-- The polynomial `f` of `y² + h(x)y = f(x)`. -/
  f : R[X]
  /-- The polynomial `h` has degree at most `g + 1`. -/
  natDegree_h_le : h.natDegree ≤ g + 1
  /-- The polynomial `f` has degree at most `2g + 2`. -/
  natDegree_f_le : f.natDegree ≤ 2 * g + 2

namespace HyperellipticEquation

variable (E : HyperellipticEquation g R)

/-- The base change of a Weierstrass equation along a ring homomorphism. -/
@[simps]
noncomputable def map (φ : R →+* S) : HyperellipticEquation g S where
  h := E.h.map φ
  f := E.f.map φ
  natDegree_h_le := natDegree_map_le.trans E.natDegree_h_le
  natDegree_f_le := natDegree_map_le.trans E.natDegree_f_le

/-- The **weighted homogeneous equation** `y² + h(x, z)y - f(x, z)` of a Weierstrass equation
`y² + h(x)y = f(x)` of genus `g` (LMFDB `g2c.minimal_equation`), in the variables `x = X 0`,
`y = X 1` and `z = X 2` of weights `1`, `g + 1` and `1`, where `h(x, z)` and `f(x, z)` are the
homogenisations of `h` and `f` to degrees `g + 1` and `2g + 2`. It is weighted homogeneous of degree
`2g + 2` (`HyperellipticEquation.isWeightedHomogeneous_weightedEquation`), and its zero locus in the
weighted projective plane is the LMFDB's smooth projective model of the curve. -/
noncomputable def weightedEquation : MvPolynomial (Fin 3) R :=
  .X 1 ^ 2 + E.h.homogenizeXZ (g + 1) * .X 1 - E.f.homogenizeXZ (2 * g + 2)

/-- **The weighted homogeneous equation is weighted homogeneous of degree `2g + 2`**, for the
weights `1`, `g + 1` and `1` of `x`, `y` and `z`. -/
lemma isWeightedHomogeneous_weightedEquation :
    IsWeightedHomogeneous ![1, g + 1, 1] E.weightedEquation (2 * g + 2) := by
  have hy : IsWeightedHomogeneous ![1, g + 1, 1] (.X 1 : MvPolynomial (Fin 3) R) (g + 1) :=
    isWeightedHomogeneous_X R _ 1
  have hd : g + 1 + (g + 1) = 2 * g + 2 := by ring1
  rw [weightedEquation, sq, ← hd]
  exact ((hy.mul hy).add ((E.h.isWeightedHomogeneous_homogenizeXZ _ _).mul hy)).sub
    (E.f.isWeightedHomogeneous_homogenizeXZ _ _)

/-- **The weighted homogeneous equation at `z = 1` is the Weierstrass equation**
`y² + h(x)y - f(x)`. -/
lemma aeval_weightedEquation :
    MvPolynomial.aeval ![x, y, 1] E.weightedEquation = y ^ 2 + aeval x E.h * y - aeval x E.f := by
  simp [weightedEquation, aeval_homogenizeXZ _ _ E.natDegree_h_le,
    aeval_homogenizeXZ _ _ E.natDegree_f_le]

/-- The polynomial `4f + h²` of a Weierstrass equation `y² + h(x)y = f(x)`: for `w = 2y + h`, the
equation becomes the simplified equation `w² = 4f + h²`. -/
noncomputable def simplifiedPolynomial : R[X] :=
  4 * E.f + E.h ^ 2

variable [Invertible (2 : R)]

/-- The polynomial `f + h²/4` of a Weierstrass equation `y² + h(x)y = f(x)`, which becomes
`(y + h/2)² = f + h²/4` after completing the square. -/
noncomputable def rhs : R[X] :=
  E.f + C (⅟2 ^ 2) * E.h ^ 2

/-- The **discriminant** of a Weierstrass equation `y² + h(x)y = f(x)` of genus `g` (LMFDB
`g2c.discriminant` for `g = 2`): `2^(4g)` times the discriminant of `f + h²/4` as a binary form of
degree `2g + 2`. For `g = 2` this is `2⁸ disc(f + h²/4)` if `f + h²/4` has degree six and
`2⁸ lc(f + h²/4)² disc(f + h²/4)` if it has degree five; the LMFDB writes `lc(f)` for the latter
leading coefficient, which is the same when `deg h ≤ 2`, as for its reduced integral models. It is
`0` when `f + h²/4` has smaller degree, where the LMFDB's formula is not meant to apply. -/
noncomputable def discriminant : R :=
  2 ^ (4 * g) * E.rhs.binaryDiscr (2 * g + 2)

lemma natDegree_rhs_le : E.rhs.natDegree ≤ 2 * g + 2 :=
  natDegree_add_le_of_degree_le E.natDegree_f_le <| (natDegree_C_mul_le _ _).trans <|
    natDegree_pow_le.trans <| by linarith [E.natDegree_h_le]

lemma four_mul_invOf_two_sq : (4 : R) * ⅟2 ^ 2 = 1 := by
  rw [show (4 : R) = 2 * 2 by norm_num, sq, mul_mul_mul_comm, mul_invOf_self, one_mul]

lemma isUnit_four : IsUnit (4 : R) :=
  .of_mul_eq_one _ four_mul_invOf_two_sq

lemma four_mul_rhs : 4 * E.rhs = E.simplifiedPolynomial := by
  rw [rhs, simplifiedPolynomial, mul_add, ← mul_assoc, ← C_ofNat, ← C_mul, four_mul_invOf_two_sq,
    C_1, one_mul]

lemma natDegree_simplifiedPolynomial : E.simplifiedPolynomial.natDegree = E.rhs.natDegree := by
  rw [← four_mul_rhs, ← C_ofNat, natDegree_C_mul_of_isUnit isUnit_four]

/-- **The discriminant of an equation with `deg(f + h²/4) = 2g + 2`**: `2^(4g) disc(f + h²/4)`. -/
lemma discriminant_of_natDegree_eq (h : E.rhs.natDegree = 2 * g + 2) :
    E.discriminant = 2 ^ (4 * g) * E.rhs.discr := by
  rw [discriminant, binaryDiscr_of_natDegree_eq h]

/-- **The discriminant of an equation with `deg(f + h²/4) = 2g + 1`**:
`2^(4g) lc(f + h²/4)² disc(f + h²/4)`. -/
lemma discriminant_of_natDegree_eq_add_one (h : E.rhs.natDegree = 2 * g + 1) :
    E.discriminant = 2 ^ (4 * g) * E.rhs.leadingCoeff ^ 2 * E.rhs.discr := by
  rw [discriminant, binaryDiscr_of_natDegree_add_one_eq (by omega), mul_assoc]

lemma discriminant_of_natDegree_lt (h : E.rhs.natDegree < 2 * g + 1) : E.discriminant = 0 := by
  rw [discriminant, binaryDiscr_of_natDegree_add_one_lt (by omega), mul_zero]

variable {E} (hE : E.discriminant ≠ 0)

include hE

/-- **An equation with nonzero discriminant has `deg(f + h²/4) ≥ 2g + 1`.** -/
lemma le_natDegree_rhs : 2 * g + 1 ≤ E.rhs.natDegree :=
  not_lt.mp fun h ↦ hE <| E.discriminant_of_natDegree_lt h

/-- **An equation with nonzero discriminant has `4f + h²` of degree `2g + 1` or `2g + 2`.** -/
lemma natDegree_simplifiedPolynomial_eq : E.simplifiedPolynomial.natDegree = 2 * g + 1 ∨
    E.simplifiedPolynomial.natDegree = 2 * g + 2 := by
  grind [natDegree_simplifiedPolynomial, le_natDegree_rhs hE, natDegree_rhs_le]

/-- **An equation with nonzero discriminant has `deg h = g + 1` or `deg f ≥ 2g + 1`**: for `g = 2`,
`deg h = 3` or `deg f ∈ {5, 6}`. -/
lemma natDegree_h_eq_or_le_natDegree_f : E.h.natDegree = g + 1 ∨ 2 * g + 1 ≤ E.f.natDegree := by
  refine or_iff_not_imp_left.mpr fun hh ↦ ?_
  have hlt : (C (⅟2 ^ 2) * E.h ^ 2).natDegree < E.rhs.natDegree :=
    (natDegree_C_mul_le _ _).trans_lt <| natDegree_pow_le.trans_lt <| by
      grind [E.natDegree_h_le, le_natDegree_rhs hE]
  rw [show E.f = E.rhs - C (⅟2 ^ 2) * E.h ^ 2 by rw [rhs, add_sub_cancel_right],
    natDegree_sub_eq_left_of_natDegree_lt hlt]
  exact le_natDegree_rhs hE

end HyperellipticEquation
