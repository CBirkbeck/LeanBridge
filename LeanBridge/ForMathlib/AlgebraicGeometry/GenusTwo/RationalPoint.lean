import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.Equation

/-!
# Rational points of a hyperelliptic curve

The LMFDB writes the rational points of a hyperelliptic curve `y² + h(x)y = f(x)` of genus `g` in
projective coordinates `(x : y : z)` on its smooth projective model, the weighted homogeneous
equation `y² + h(x, z)y = f(x, z)` of degree `2g + 2` in the weighted projective plane, where `y`
has weight `g + 1` and `x` and `z` have weight `1` (`HyperellipticEquation.weightedEquation`). A
point over a field `F` is thus a nonzero solution `(x, y, z) ∈ F³` of this equation, up to the
scaling `(x, y, z) ~ (λx, λ^(g+1) y, λz)` by `λ ∈ F^×`. Faltings' theorem that there are finitely
many rational points when `g ≥ 2` and `F` is a number field is not proved here.

## Main definitions

* `HyperellipticEquation.weightedScale`: the scaling `(x, y, z) ↦ (λx, λ^(g+1) y, λz)`.
* `HyperellipticEquation.IsWeightedSolution`: nonzero solutions of the weighted equation.
* `HyperellipticEquation.RationalPoint` (LMFDB `g2c.all_rational_points`): the `F`-rational
  points, the solutions modulo scaling.

## Main results

* `HyperellipticEquation.IsWeightedSolution.weightedScale`: scaling preserves the solutions.
-/

variable {g : ℕ} {F : Type*} [Field F] (E : HyperellipticEquation g F)

namespace HyperellipticEquation

variable (g) in
/-- The **scaling** `(x, y, z) ↦ (λx, λ^(g+1) y, λz)` of the weighted projective plane with weights
`1`, `g + 1` and `1`. -/
def weightedScale (c : Fˣ) (P : Fin 3 → F) : Fin 3 → F :=
  ![c * P 0, c ^ (g + 1) * P 1, c * P 2]

lemma weightedScale_one (P : Fin 3 → F) : weightedScale g 1 P = P := by
  ext i
  fin_cases i <;> simp [weightedScale]

lemma weightedScale_mul (c d : Fˣ) (P : Fin 3 → F) :
    weightedScale g (c * d) P = weightedScale g c (weightedScale g d P) := by
  ext i
  fin_cases i <;> simp [weightedScale, mul_pow, mul_assoc]

lemma weightedScale_eq_zero {c : Fˣ} {P : Fin 3 → F} (h : weightedScale g c P = 0) : P = 0 := by
  rw [← weightedScale_one P, ← inv_mul_cancel c, weightedScale_mul, h]
  ext i
  fin_cases i <;> simp [weightedScale]

lemma eval_weightedScale {φ : MvPolynomial (Fin 3) F} {d : ℕ}
    (hφ : MvPolynomial.IsWeightedHomogeneous ![1, g + 1, 1] φ d) (c : Fˣ) (P : Fin 3 → F) :
    MvPolynomial.eval (weightedScale g c P) φ = c ^ d * MvPolynomial.eval P φ := by
  have hP : weightedScale g c P = fun i ↦ (c : F) ^ (![1, g + 1, 1] : Fin 3 → ℕ) i * P i := by
    ext i
    fin_cases i <;> simp [weightedScale]
  rw [hP, MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hw : Finsupp.weight ![1, g + 1, 1] m = d := hφ (MvPolynomial.mem_support_iff.mp hm)
  rw [← hw, Finsupp.weight_apply, Finsupp.sum]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum, smul_eq_mul]
  rw [Finset.sum_congr rfl fun i _ ↦ Nat.mul_comm (m i) ((![1, g + 1, 1] : Fin 3 → ℕ) i)]
  ring1

/-- A **nonzero solution** `(x, y, z) ∈ F³` of the weighted homogeneous equation
`y² + h(x, z)y = f(x, z)`. -/
def IsWeightedSolution (P : Fin 3 → F) : Prop :=
  P ≠ 0 ∧ MvPolynomial.eval P E.weightedEquation = 0

/-- **The scaling preserves the nonzero solutions of the weighted equation**, which is weighted
homogeneous. -/
lemma IsWeightedSolution.weightedScale {P : Fin 3 → F} (hP : E.IsWeightedSolution P) (c : Fˣ) :
    E.IsWeightedSolution (weightedScale g c P) :=
  ⟨fun h ↦ hP.1 (weightedScale_eq_zero h), by
    rw [eval_weightedScale E.isWeightedHomogeneous_weightedEquation, hP.2, mul_zero]⟩

/-- The equivalence relation `P ~ weightedScale g c P` on the nonzero solutions of the weighted
equation. -/
def weightedSolutionSetoid : Setoid {P : Fin 3 → F // E.IsWeightedSolution P} where
  r P Q := ∃ c : Fˣ, (Q : Fin 3 → F) = weightedScale g c P
  iseqv := by
    refine ⟨fun P ↦ ⟨1, (weightedScale_one _).symm⟩, ?_, ?_⟩
    · rintro P Q ⟨c, hc⟩
      exact ⟨c⁻¹, by rw [hc, ← weightedScale_mul, inv_mul_cancel, weightedScale_one]⟩
    · rintro P Q R ⟨c, hc⟩ ⟨d, hd⟩
      exact ⟨d * c, by rw [hd, hc, weightedScale_mul]⟩

/-- The **`F`-rational points** (LMFDB `g2c.all_rational_points`, for `F = ℚ`) of the hyperelliptic
curve with Weierstrass equation `E`: the nonzero solutions `(x, y, z) ∈ F³` of the weighted
homogeneous equation `y² + h(x, z)y = f(x, z)`, its smooth projective model, up to the scaling
`(x, y, z) ~ (λx, λ^(g+1) y, λz)` by `λ ∈ F^×`. -/
def RationalPoint : Type _ :=
  Quotient E.weightedSolutionSetoid

end HyperellipticEquation
