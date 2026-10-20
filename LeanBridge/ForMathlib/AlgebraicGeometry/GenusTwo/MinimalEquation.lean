import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.FunctionField

/-!
# Minimal equations of hyperelliptic curves over `ℚ`

An integral Weierstrass equation `y² + h(x)y = f(x)` of a hyperelliptic curve `X` over `ℚ` is
minimal when the absolute value of its discriminant is the smallest among all integral Weierstrass
equations of `X`. Two equations with nonzero discriminant define the same curve exactly when their
function fields are isomorphic over `ℚ`, since a smooth projective curve is determined by its
function field.

The discriminant of an integral equation is computed over `ℚ`; it is an integer, which is not
proved here, and neither is the existence of minimal equations, nor the fact that the primes
dividing the minimal discriminant are the primes of bad reduction.

## Main definitions

* `HyperellipticEquation.toRat`: the Weierstrass equation over `ℚ` of an integral equation.
* `HyperellipticEquation.IsMinimal` (LMFDB `g2c.minimal_equation`): minimal equations.

## Main results

* `HyperellipticEquation.IsMinimal.abs_discriminant_eq`: two minimal equations of the same curve
  have discriminants of the same absolute value (LMFDB `g2c.discriminant`).
-/

namespace HyperellipticEquation

variable {g : ℕ} {E : HyperellipticEquation g ℤ}

variable (E) in
/-- The Weierstrass equation over `ℚ` of an integral Weierstrass equation. -/
noncomputable abbrev toRat : HyperellipticEquation g ℚ :=
  E.map (Int.castRingHom ℚ)

variable (E) in
/-- An integral Weierstrass equation `y² + h(x)y = f(x)` of genus `g` is a **minimal equation**
(LMFDB `g2c.minimal_equation`) if its discriminant `Δ` is nonzero and `|Δ|` is the smallest among
the discriminants of the integral Weierstrass equations of genus `g` of the same curve over `ℚ`:
those with nonzero discriminant whose function fields over `ℚ` are isomorphic to its own. -/
structure IsMinimal : Prop where
  /-- A minimal equation has nonzero discriminant. -/
  discriminant_ne_zero : E.toRat.discriminant ≠ 0
  /-- The discriminant of a minimal equation has the least absolute value among those of the
  integral equations with nonzero discriminant of the same curve. -/
  abs_discriminant_le (E' : HyperellipticEquation g ℤ) : E'.toRat.discriminant ≠ 0 → Nonempty
    (E'.toRat.FunctionField ≃ₐ[ℚ] E.toRat.FunctionField) → |E.toRat.discriminant| ≤
    |E'.toRat.discriminant|

/-- **Two minimal equations of the same curve have discriminants of the same absolute value**, so
that the absolute discriminant of a curve is well defined. -/
lemma IsMinimal.abs_discriminant_eq {E' : HyperellipticEquation g ℤ} (hE : E.IsMinimal)
    (hE' : E'.IsMinimal) (e : E'.toRat.FunctionField ≃ₐ[ℚ] E.toRat.FunctionField) :
    |E.toRat.discriminant| = |E'.toRat.discriminant| :=
  le_antisymm (hE.abs_discriminant_le E' hE'.discriminant_ne_zero ⟨e⟩)
    (hE'.abs_discriminant_le E hE.discriminant_ne_zero ⟨e.symm⟩)

end HyperellipticEquation
