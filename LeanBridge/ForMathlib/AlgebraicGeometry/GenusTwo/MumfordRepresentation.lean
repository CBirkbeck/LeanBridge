import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.RationalPoint

/-!
# Mumford representations of effective divisors on hyperelliptic curves

The LMFDB writes a point of the Jacobian of a genus 2 curve `X : y² + h(x, z)y = f(x, z)` as the
class of a divisor `D₀ - nD_∞`, where `D₀` is an effective divisor of degree at most `2` given by a
pair of binary forms `a(x, z)` of degree at most `2` and `b(x, z)` of degree `3`: `D₀` is the
intersection of `X` with the locus `a(x, z) = 0`, `y = b(x, z)` (LMFDB `g2c.mw_generator`). This
intersection is the divisor `D₀` exactly when `y = b(x, z)` lies on `X` along `a(x, z) = 0`, that is
when `a(x, z)` divides `b² + hb - f`; its points are then the points `(x₀ : b(x₀, z₀) : z₀)` of `X`
at the roots `(x₀ : z₀)` of `a(x, z)`. At `z = 1` this is the Mumford representation `(u, v)` of
`D₀`, `u = a(x, 1)` and `v = b(x, 1)`, with `u` dividing `v² + hv - f`.

The divisor `D₀ - nD_∞` and its class in the Jacobian are not formalised: the Jacobian is only
characterised by its functor of points (`TauCeti.AlgebraicGeometry.AbelianVariety.IsJacobian`), and
divisors on the weighted projective model are not available.

## Main definitions

* `HyperellipticEquation.substY`: the binary form `b² + hb - f`, the equation at `y = b(x, z)`.
* `HyperellipticEquation.IsMumfordPair` (LMFDB `g2c.mw_generator`): the pairs `(a, b)` describing an
  effective divisor `D₀` of degree at most the genus.

## Main results

* `HyperellipticEquation.IsMumfordPair.isWeightedSolution`: the points `(x₀ : b(x₀, z₀) : z₀)` at
  the roots `(x₀ : z₀)` of `a(x, z)` lie on the curve.
* `HyperellipticEquation.IsMumfordPair.dvd`: the Mumford representation `(a(x, 1), b(x, 1))`
  satisfies `a(x, 1) ∣ b(x, 1)² + h b(x, 1) - f`.
-/

open Polynomial

namespace HyperellipticEquation

variable {g : ℕ} {K : Type*} [Field K] (E : HyperellipticEquation g K) {d : ℕ} {a b : K[X]}

variable (b) in
/-- The polynomial `b(x, z)² + h(x, z) b(x, z) - f(x, z)`, the weighted homogeneous equation of `E`
at `y = b(x, z)`, for the homogenisation `b(x, z)` of `b` to degree `g + 1`, in the variables
`x = X 0` and `z = X 2`. -/
noncomputable def substY : MvPolynomial (Fin 3) K :=
  MvPolynomial.aeval ![.X 0, b.homogenizeXZ (g + 1), .X 2] E.weightedEquation

variable (d a b) in
/-- A **Mumford pair** `(a, b)` of degree `d` (LMFDB `g2c.mw_generator`) for a Weierstrass equation
`y² + h(x)y = f(x)` of genus `g`: a nonzero polynomial `a` of degree at most `d ≤ g`, homogenised to
the binary form `a(x, z)` of degree `d`, and a polynomial `b` of degree at most `g + 1`, homogenised
to the binary form `b(x, z)` of degree `g + 1`, such that `a(x, z)` divides
`b(x, z)² + h(x, z) b(x, z) - f(x, z)`. It describes the effective divisor `D₀` of degree `d` cut
out on the curve by `a(x, z) = 0` and `y = b(x, z)`, whose points are the points
`(x₀ : b(x₀, z₀) : z₀)` at the roots `(x₀ : z₀)` of `a(x, z)`
(`HyperellipticEquation.IsMumfordPair.isWeightedSolution`). For `h = 0` and `deg f = 2g + 1`, the
pair `(a(x, 1), b(x, 1))` is the Mumford representation of `D₀`
(`HyperellipticEquation.IsMumfordPair.dvd`). -/
structure IsMumfordPair : Prop where
  /-- The polynomial `a` is nonzero. -/
  a_ne_zero : a ≠ 0
  /-- The polynomial `a` has degree at most `d`. -/
  natDegree_a_le : a.natDegree ≤ d
  /-- The degree `d` is at most the genus. -/
  le_genus : d ≤ g
  /-- The polynomial `b` has degree at most `g + 1`. -/
  natDegree_b_le : b.natDegree ≤ g + 1
  /-- The binary form `a(x, z)` divides `b(x, z)² + h(x, z) b(x, z) - f(x, z)`. -/
  dvd_substY : a.homogenizeXZ d ∣ E.substY b

variable {E}

/-- **The points of the divisor of a Mumford pair lie on the curve**: if `(a, b)` is a Mumford pair
and `(x₀ : z₀)` is a root of `a(x, z)`, then `(x₀ : b(x₀, z₀) : z₀)` is a point of the curve. -/
lemma IsMumfordPair.isWeightedSolution (hab : E.IsMumfordPair d a b) {x₀ z₀ : K}
    (hx : x₀ ≠ 0 ∨ z₀ ≠ 0) (ha : MvPolynomial.eval ![x₀, 0, z₀] (a.homogenizeXZ d) = 0) :
    E.IsWeightedSolution ![x₀, MvPolynomial.eval ![x₀, 0, z₀] (b.homogenizeXZ (g + 1)), z₀] := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases hx with hx | hx
    · exact hx (congrFun h 0)
    · exact hx (congrFun h 2)
  rcases hab.dvd_substY with ⟨c, hc⟩
  have ha' : MvPolynomial.aeval ![x₀, 0, z₀] (a.homogenizeXZ d) = 0 := ha
  have hv : (fun i ↦ MvPolynomial.aeval ![x₀, 0, z₀]
      (![.X 0, b.homogenizeXZ (g + 1), .X 2] i : MvPolynomial (Fin 3) K)) =
      ![x₀, MvPolynomial.eval ![x₀, 0, z₀] (b.homogenizeXZ (g + 1)), z₀] := by
    ext i
    fin_cases i <;> simp
  have h : MvPolynomial.aeval ![x₀, 0, z₀] (E.substY b) =
      MvPolynomial.aeval ![x₀, 0, z₀] (a.homogenizeXZ d * c) :=
    congrArg _ hc
  rw [substY, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, hv, map_mul, ha', zero_mul] at h
  exact h

/-- **The Mumford representation of a Mumford pair**: if `(a, b)` is a Mumford pair, then at
`z = 1`, `a` divides `b² + hb - f`, which is the Mumford representation
`(u, v) = (a(x, 1), b(x, 1))` of the divisor it describes when `h = 0` and `deg f = 2g + 1`. -/
lemma IsMumfordPair.dvd (hab : E.IsMumfordPair d a b) : a ∣ b ^ 2 + E.h * b - E.f := by
  rcases hab.dvd_substY with ⟨c, hc⟩
  have hv : (fun i ↦ MvPolynomial.aeval ![(X : K[X]), 0, 1]
      (![.X 0, b.homogenizeXZ (g + 1), .X 2] i : MvPolynomial (Fin 3) K)) = ![X, b, 1] := by
    ext1 i
    fin_cases i <;> simp [aeval_homogenizeXZ _ _ hab.natDegree_b_le]
  have h : MvPolynomial.aeval ![(X : K[X]), 0, 1] (E.substY b) =
      MvPolynomial.aeval ![(X : K[X]), 0, 1] (a.homogenizeXZ d * c) :=
    congrArg _ hc
  rw [substY, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, hv, aeval_weightedEquation, map_mul,
    aeval_homogenizeXZ _ _ hab.natDegree_a_le] at h
  simp only [aeval_X_left_apply] at h
  exact ⟨_, h⟩

end HyperellipticEquation
