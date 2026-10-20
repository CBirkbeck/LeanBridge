import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The divisor functions

For a complex number `τ`, the divisor function `σ_τ(n) = ∑_{d ∣ n} d ^ τ` is a multiplicative
arithmetic function. For a natural exponent `k` it is Mathlib's `ArithmeticFunction.sigma`, which
takes natural values.

## Main definitions

* `ArithmeticFunction.divisorFunction` (LMFDB `af.divisor_function`).

## Main results

* `ArithmeticFunction.isMultiplicative_divisorFunction`: the divisor function is multiplicative.
* `ArithmeticFunction.divisorFunction_natCast`: for a natural exponent `k`, the divisor function
  is Mathlib's `σ k`.
-/

open Finset

namespace ArithmeticFunction

variable (τ : ℂ) (n : ℕ)

/-- The **divisor function** `σ_τ(n) = ∑_{d ∣ n} d ^ τ` (LMFDB `af.divisor_function`) for a complex
exponent `τ`, as an arithmetic function with complex values. For a natural exponent `k` it is
Mathlib's `ArithmeticFunction.sigma k` (`divisorFunction_natCast`). -/
noncomputable def divisorFunction : ArithmeticFunction ℂ :=
  ⟨fun n ↦ ∑ d ∈ n.divisors, (d : ℂ) ^ τ, by simp⟩

lemma divisorFunction_apply : divisorFunction τ n = ∑ d ∈ n.divisors, (d : ℂ) ^ τ :=
  rfl

/-- The divisor function is multiplicative. -/
lemma isMultiplicative_divisorFunction : (divisorFunction τ).IsMultiplicative := by
  let f : ArithmeticFunction ℂ := ⟨fun n ↦ if n = 0 then 0 else (n : ℂ) ^ τ, by simp⟩
  have h : divisorFunction τ = (zeta : ArithmeticFunction ℂ) * f := by
    ext n
    rw [coe_zeta_mul_apply, divisorFunction_apply]
    exact sum_congr rfl fun d hd ↦ by simp [f, (Nat.pos_of_mem_divisors hd).ne']
  exact h ▸ isMultiplicative_zeta.natCast.mul <| IsMultiplicative.iff_ne_zero.mpr
    ⟨by simp [f], fun {m n} _ hn _ ↦ by simp [f, hn, Complex.natCast_mul_natCast_cpow]⟩

/-- For a natural exponent `k`, the divisor function is Mathlib's `σ k`. -/
lemma divisorFunction_natCast (k : ℕ) : divisorFunction k n = sigma k n := by
  simp [divisorFunction_apply, sigma_apply]

end ArithmeticFunction
