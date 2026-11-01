import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.IsomorphicEquations
import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.Label

/-!
# The discriminant of a genus 2 curve over `ℚ`

The discriminant of a genus 2 curve `C` over `ℚ` (LMFDB `g2c.discriminant`) is the discriminant of a
minimal equation of `C`: an integral Weierstrass equation `y² + h(x)y = f(x)` of `C` whose
discriminant has the least absolute value among the integral equations of `C`. It is well defined:
every genus 2 curve over `ℚ` has a minimal equation, and two minimal equations of the same curve
have the same discriminant (`HyperellipticEquation.IsMinimal.discriminant_eq`).

Every Weierstrass equation over `ℚ` becomes integral after the change of variables `y = Y / μ`,
which multiplies `h` by `μ` and `f` by `μ²`, for a common denominator `μ` of their coefficients.
The discriminant of an integral equation of genus `g` is `2^(-(4g + 4))` times the discriminant of
the integral polynomial `4f + h²` as a binary form of degree `2g + 2`, so the absolute values of the
discriminants of the integral equations of a curve lie in `2^(-(4g + 4)) ℕ`, and one of them is the
least. That the discriminant of an integral equation is itself an integer is not proved here.

## Main definitions

* `GenusTwoCurve.minimalDiscriminant` (LMFDB `g2c.discriminant`): the discriminant of a genus 2
  curve over `ℚ`.

## Main results

* `HyperellipticEquation.exists_toRat_eq_changeOfVariables`: every equation over `ℚ` is related
  by a change of variables to an integral equation.
* `HyperellipticEquation.two_pow_mul_discriminant_toRat`: the discriminant of an integral equation
  is `2^(-(4g + 4))` times the discriminant of `4f + h²` as a binary form of degree `2g + 2`.
* `HyperellipticEquation.exists_isMinimal_algEquiv`: an integral equation with nonzero
  discriminant has a minimal equation defining the same curve.
* `GenusTwoCurve.exists_isMinimalEquation` (LMFDB `g2c.minimal_equation`): every genus 2 curve
  over `ℚ` has a minimal equation.
* `GenusTwoCurve.minimalDiscriminant_eq` (LMFDB `g2c.discriminant`): the discriminant of a genus 2
  curve is the discriminant of any of its minimal equations.
* `GenusTwoCurve.minimalDiscriminant_eq_of_algEquiv` (LMFDB `g2c.discriminant`): genus 2 curves
  with isomorphic function fields have the same discriminant.
* `GenusTwoCurve.minimalDiscriminant_ne_zero`: the discriminant of a genus 2 curve is nonzero.
* `GenusTwoCurve.abs_minimalDiscriminant` and `GenusTwoCurve.absDiscriminant_pos` (LMFDB
  `g2c.abs_discriminant`): its absolute value is the absolute discriminant, which is positive.
-/

open Polynomial

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} {p : R[X]}

lemma binaryDiscr_map_of_injective {φ : R →+* S} (hφ : Function.Injective φ) :
    (p.map φ).binaryDiscr n = φ (p.binaryDiscr n) := by
  rw [binaryDiscr, binaryDiscr, natDegree_map_eq_of_injective hφ, leadingCoeff_map_of_injective hφ,
    discr_map_of_natDegree_eq φ (natDegree_map_eq_of_injective hφ p)]
  split_ifs <;> simp

lemma binaryComp_one_zero_zero_one (hp : p.natDegree ≤ n) : p.binaryComp n 1 0 0 1 = p := by
  rw [binaryComp, map_one, map_zero, one_mul, add_zero, zero_mul, zero_add]
  exact aeval_homogenize_X_one p hp

end Polynomial

namespace HyperellipticEquation

variable {g : ℕ}

/-- **Every Weierstrass equation over `ℚ` has an integral model**: an equation `y² + h(x)y = f(x)`
over `ℚ` becomes the integral equation `Y² + μh(X)Y = μ²f(X)` under the change of variables
`x = X`, `y = Y / μ`, for a suitable `μ ≠ 0`. -/
lemma exists_toRat_eq_changeOfVariables (E : HyperellipticEquation g ℚ) :
    ∃ (E₀ : HyperellipticEquation g ℤ) (μ : ℚ), μ ≠ 0 ∧ E₀.toRat =
      E.changeOfVariables 1 0 0 1 μ⁻¹ 0 (natDegree_zero.trans_le (Nat.zero_le _)) := by
  rcases IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) E.h with ⟨b₁, hb₁, h₁⟩
  rcases IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) E.f with ⟨b₂, hb₂, h₂⟩
  generalize IsLocalization.integerNormalization (nonZeroDivisors ℤ) E.h = P at h₁
  generalize IsLocalization.integerNormalization (nonZeroDivisors ℤ) E.f = Q at h₂
  rw [algebraMap_int_eq] at h₁ h₂
  have hP : P.natDegree ≤ g + 1 := by
    rw [← natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)), h₁]
    exact (natDegree_smul_le _ _).trans E.natDegree_h_le
  have hQ : Q.natDegree ≤ 2 * g + 2 := by
    rw [← natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)), h₂]
    exact (natDegree_smul_le _ _).trans E.natDegree_f_le
  refine ⟨⟨C b₂ * P, C (b₁ ^ 2 * b₂) * Q, (natDegree_C_mul_le _ _).trans hP,
    (natDegree_C_mul_le _ _).trans hQ⟩, b₁ * b₂, mul_ne_zero
      (Int.cast_ne_zero.mpr (nonZeroDivisors.ne_zero hb₁))
      (Int.cast_ne_zero.mpr (nonZeroDivisors.ne_zero hb₂)), HyperellipticEquation.ext ?_ ?_⟩
  · simp only [eq_intCast, map_h, Polynomial.map_mul, Polynomial.map_intCast, h₁, changeOfVariables,
      inv_inv, map_mul, map_intCast, binaryComp_one_zero_zero_one E.natDegree_h_le]
    ring1
  · simp only [eq_intCast, map_f, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_intCast,
      h₂, changeOfVariables, inv_inv, map_mul, map_intCast, map_pow,
      binaryComp_one_zero_zero_one E.natDegree_f_le]
    ring1

variable (E : HyperellipticEquation g ℤ)

/-- **The discriminant of an integral equation** `y² + h(x)y = f(x)` of genus `g` is
`2^(-(4g + 4))` times the discriminant of the integral polynomial `4f + h²` as a binary form of
degree `2g + 2`, so that `2^(4g + 4) Δ` is an integer. -/
lemma two_pow_mul_discriminant_toRat : 2 ^ (4 * g + 4) * E.toRat.discriminant =
    (E.simplifiedPolynomial.binaryDiscr (2 * g + 2) : ℚ) := by
  have hs : E.toRat.simplifiedPolynomial = E.simplifiedPolynomial.map (Int.castRingHom ℚ) := by
    simp only [simplifiedPolynomial, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_ofNat, map_h, map_f]
  have h4 : (C (⅟2 ^ 2) : ℚ[X]) * 4 = 1 := by
    rw [← map_ofNat C 4, ← C_mul, mul_comm, four_mul_invOf_two_sq, C_1]
  have hr : E.toRat.rhs = C (⅟2 ^ 2) * E.toRat.simplifiedPolynomial := by
    rw [← four_mul_rhs, ← mul_assoc, h4, one_mul]
  have h : (2 : ℚ) ^ (4 * g + 4) * 2 ^ (4 * g) * (⅟2 ^ 2) ^ (2 * (2 * g + 2) - 2) = 1 := by
    rw [← pow_add, ← pow_mul, (by omega : 2 * (2 * g + 2) - 2 = 4 * g + 2),
      (by ring1 : 4 * g + 4 + 4 * g = 2 * (4 * g + 2)), ← mul_pow, mul_invOf_self, one_pow]
  rw [discriminant, hr, binaryDiscr_C_mul (by omega) (by norm_num), hs,
    binaryDiscr_map_of_injective (RingHom.injective_int _), eq_intCast]
  linear_combination (E.simplifiedPolynomial.binaryDiscr (2 * g + 2) : ℚ) * h

lemma abs_discriminant_toRat_mul : |E.toRat.discriminant| * 2 ^ (4 * g + 4) =
    ((E.simplifiedPolynomial.binaryDiscr (2 * g + 2)).natAbs : ℚ) := by
  rw [Nat.cast_natAbs, Int.cast_abs, ← two_pow_mul_discriminant_toRat, abs_mul, abs_pow, abs_two,
    mul_comm]

/-- **Minimal equations exist**: an integral Weierstrass equation with nonzero discriminant has a
minimal equation (`HyperellipticEquation.IsMinimal`) with an isomorphic function field over `ℚ`.
The absolute values of the discriminants of the integral equations of a curve lie in
`2^(-(4g + 4)) ℕ` (`HyperellipticEquation.two_pow_mul_discriminant_toRat`), so one of them is the
least. -/
lemma exists_isMinimal_algEquiv (hE : E.toRat.discriminant ≠ 0) : ∃ E' : HyperellipticEquation g ℤ,
    E'.IsMinimal ∧ Nonempty (E'.toRat.FunctionField ≃ₐ[ℚ] E.toRat.FunctionField) := by
  classical
  have hS : ∃ n : ℕ, ∃ E' : HyperellipticEquation g ℤ, E'.toRat.discriminant ≠ 0 ∧
      Nonempty (E'.toRat.FunctionField ≃ₐ[ℚ] E.toRat.FunctionField) ∧
        (E'.simplifiedPolynomial.binaryDiscr (2 * g + 2)).natAbs = n :=
    ⟨_, E, hE, ⟨AlgEquiv.refl⟩, rfl⟩
  rcases Nat.find_spec hS with ⟨E₁, hE₁, ⟨e₁⟩, hn₁⟩
  refine ⟨E₁, ⟨hE₁, fun E' hE' ⟨e'⟩ ↦ le_of_mul_le_mul_right ?_ (pow_pos two_pos (4 * g + 4))⟩,
    ⟨e₁⟩⟩
  rw [abs_discriminant_toRat_mul, abs_discriminant_toRat_mul, hn₁, Nat.cast_le]
  exact Nat.find_min' hS ⟨E', hE', ⟨e'.trans e₁⟩, rfl⟩

end HyperellipticEquation

namespace GenusTwoCurve

variable (C : GenusTwoCurve ℚ) {E : HyperellipticEquation 2 ℤ}

/-- **Every genus 2 curve over `ℚ` has a minimal equation** (LMFDB `g2c.minimal_equation`): an
integral Weierstrass equation of the curve whose discriminant has the least absolute value. -/
lemma exists_isMinimalEquation : ∃ E, C.IsMinimalEquation E := by
  rcases C.exists_toRat_eq_changeOfVariables with ⟨E₀, μ, hμ, hc⟩
  have hd : E₀.toRat.discriminant ≠ 0 := by
    rw [hc, C.discriminant_changeOfVariables _ _ _ _ _ _ (inv_ne_zero hμ)]
    simpa [hμ] using C.discriminant_ne_zero
  rcases C.nonempty_algEquiv_changeOfVariables (natDegree_zero.trans_le (Nat.zero_le _))
    C.discriminant_ne_zero (by norm_num : (1 : ℚ) * 1 - 0 * 0 ≠ 0) (inv_ne_zero hμ) with ⟨φ⟩
  have hψ : Nonempty (C.FunctionField ≃ₐ[ℚ] E₀.toRat.FunctionField) := by
    generalize E₀.toRat = E' at hc ⊢
    subst hc
    exact ⟨by convert φ <;> exact Subsingleton.elim _ _⟩
  rcases E₀.exists_isMinimal_algEquiv hd with ⟨E, hE, ⟨e⟩⟩
  exact ⟨E, hE, ⟨e.trans hψ.some.symm⟩⟩

/-- The **discriminant** of a genus 2 curve `C` over `ℚ` (LMFDB `g2c.discriminant`): the
discriminant `Δ` of a minimal equation of `C`, which exists
(`GenusTwoCurve.exists_isMinimalEquation`) and does not depend on the minimal equation
(`GenusTwoCurve.minimalDiscriminant_eq`). It is computed with LeanBridge's discriminant of
Weierstrass equations, `2⁸ lc(f + h²/4)² disc(f + h²/4)` when `f + h²/4` has degree five, where the
LMFDB writes `lc(f)` (the two agree for the LMFDB's reduced minimal equations, but not for every
equation). -/
noncomputable def minimalDiscriminant : ℚ :=
  C.exists_isMinimalEquation.choose.toRat.discriminant

/-- **The discriminant of a genus 2 curve is that of any of its minimal equations** (LMFDB
`g2c.discriminant`), so it is an invariant of the curve that does not depend on the choice of
minimal equation. -/
lemma minimalDiscriminant_eq (hE : C.IsMinimalEquation E) :
    C.minimalDiscriminant = E.toRat.discriminant :=
  C.exists_isMinimalEquation.choose_spec.1.discriminant_eq le_rfl hE.1
    (hE.2.some.trans C.exists_isMinimalEquation.choose_spec.2.some.symm)

/-- **The discriminant of a genus 2 curve is an invariant of the curve** (LMFDB `g2c.discriminant`):
genus 2 curves over `ℚ` with isomorphic function fields have the same discriminant. -/
lemma minimalDiscriminant_eq_of_algEquiv {C' : GenusTwoCurve ℚ}
    (e : C.FunctionField ≃ₐ[ℚ] C'.FunctionField) : C.minimalDiscriminant = C'.minimalDiscriminant :=
  (C'.minimalDiscriminant_eq ⟨C.exists_isMinimalEquation.choose_spec.1,
    ⟨C.exists_isMinimalEquation.choose_spec.2.some.trans e⟩⟩).symm

/-- **The discriminant of a genus 2 curve is nonzero.** -/
lemma minimalDiscriminant_ne_zero : C.minimalDiscriminant ≠ 0 :=
  C.exists_isMinimalEquation.choose_spec.1.discriminant_ne_zero

/-- **The absolute value of the discriminant of a genus 2 curve is its absolute discriminant**
(LMFDB `g2c.abs_discriminant`). -/
lemma abs_minimalDiscriminant : |C.minimalDiscriminant| = C.absDiscriminant :=
  (C.absDiscriminant_eq C.exists_isMinimalEquation.choose_spec).symm

/-- **The absolute discriminant of a genus 2 curve is positive** (LMFDB `g2c.abs_discriminant`):
it is not the junk value `0` of a curve without minimal equation. -/
lemma absDiscriminant_pos : 0 < C.absDiscriminant :=
  C.abs_minimalDiscriminant ▸ abs_pos.mpr C.minimalDiscriminant_ne_zero

end GenusTwoCurve
