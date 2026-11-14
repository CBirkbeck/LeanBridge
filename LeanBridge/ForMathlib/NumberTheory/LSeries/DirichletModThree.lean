import LeanBridge.ForMathlib.NumberTheory.LFunction.Dirichlet
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The Dirichlet character modulo 3 and its L-function

Dirichlet introduced the series `L(s, χ) = ∑ χ(n) n ^ (-s)` of a Dirichlet character `χ`, the
extension by zero to the integers of a character of `(ℤ/qℤ)ˣ`, to prove that an arithmetic
progression `a, a + q, a + 2q, …` with `a` prime to `q` contains infinitely many primes (Mathlib's
`Nat.infinite_setOfPred_prime_and_modEq`). His proof rests on `L(1, χ) ≠ 0` for `χ ≠ 1` (Mathlib's
`DirichletCharacter.LFunction_apply_one_ne_zero`), which he obtained from special values. This file
formalises the example of LMFDB `lfunction.history.dirichlet`: the character `χ₃` modulo `3` with
`χ₃(n) = 1, -1, 0` for `n ≡ 1, 2, 0 (mod 3)`, and the functional equation and the special value
`L(1, χ₃) = π / (3 √3)` of its L-function. Its Euler product is the case of `χ₃` of
`DirichletCharacter.LFunction_eulerProduct_hasProd`, for every Dirichlet character.

The character `χ₃` is odd, quadratic and primitive, and its Gauss sum is `√3 i`, so its root number
is `1` and Mathlib's functional equation reads `Λ(1 - s, χ₃) = 3 ^ (s - 1 / 2) Λ(s, χ₃)` for
`Λ(s, χ₃) = Γ_ℝ(s + 1) L(s, χ₃)`. The knowl's function `(3 / π) ^ (s / 2) Γ((s + 1) / 2) L(s, χ₃)`
is `√π 3 ^ (s / 2) Λ(s, χ₃)`, an entire function invariant under `s ↦ 1 - s`. In Lean the expression
`(3 / π) ^ (s / 2) * Gamma ((s + 1) / 2) * LFunction χ₃ s` differs from this entire function at
`s = -1, -3, -5, …`: there `Γ((s + 1) / 2)` has a pole, where Mathlib's `Complex.Gamma` takes the
value `0`, and `L(s, χ₃)` has a zero, whereas the entire function does not vanish. So the invariance
is stated for the entire function, and for the expression away from these points and from their
images `s = 2, 4, 6, …`.

For the special value, `L(σ, χ₃) = ∑ ((3k + 1) ^ (-σ) - (3k + 2) ^ (-σ))` for real `σ > 1`, where
the `k`-th term is at most `2 / (3k + 1) ^ 2` for `1 ≤ σ ≤ 2` by Bernoulli's inequality. By
dominated convergence and the continuity of `L(s, χ₃)` at `s = 1`, the same holds at `σ = 1`. The
partial sums of `∑ (1 / (3k + 1) - 1 / (3k + 2))` differ from one third of those of the partial
fraction expansion `π cot(π x) - 1 / x = ∑ (1 / (x - n) + 1 / (x + n))` at `x = 1 / 3` by
`1 - 1 / (3n + 1)`, so that `L(1, χ₃) = (π / 3) cot(π / 3) = π / (3 √3)`.

Tau Ceti's main, later than the pin, has general statements behind three of these results, and
nothing here uses them. The character `χ₃` is the Kronecker character `(-3 / ·)`, there
`TauCeti.kroneckerChar ℂ (-3)`. The special value is the case `N = 3` of the cotangent formula
`DirichletCharacter.two_mul_LFunction_one_eq_sum_mul_cot` for `L(1, χ)`, `χ` odd, and also follows
from the class number formula
`TauCeti.NumberField.classNumber_eq_LFunction_one_of_discr_eq_neg_three`. The functional equation
and the zero-free regions hold there for the entire completion of every primitive `χ ≠ 1`
(`TauCeti.LFunctions.dirichletData_entireCompletion_one_sub`, with the root number as a factor).
After a bump of the pin, the proofs of the special value and of the zero-free regions reduce to
these.

## Main definitions

* `DirichletCharacter.χ₃` (LMFDB `lfunction.history.dirichlet`): the Dirichlet character modulo `3`.
* `DirichletCharacter.completedLFunctionModThree`: the entire function
  `(3 / π) ^ (s / 2) Γ((s + 1) / 2) L(s, χ₃)`.

## Main results

* `DirichletCharacter.χ₃_intCast`: the values of `χ₃` at the integers.
* `DirichletCharacter.isPrimitive_χ₃`: `χ₃` is primitive.
* `DirichletCharacter.gaussSum_χ₃`, `DirichletCharacter.rootNumber_χ₃`: the Gauss sum of `χ₃` is
  `√3 i` and its root number is `1`.
* `DirichletCharacter.differentiable_completedLFunctionModThree`,
  `DirichletCharacter.completedLFunctionModThree_eq`: the function
  `(3 / π) ^ (s / 2) Γ((s + 1) / 2) L(s, χ₃)` is entire, with this formula away from the poles of
  `Γ((s + 1) / 2)`.
* `DirichletCharacter.completedLFunctionModThree_eq_sqrt_pi_mul_completed`: it is `√π` times the
  completion of the analytic L-function of `χ₃` (`AnalyticLFunction.dirichlet`).
* `DirichletCharacter.completedLFunctionModThree_one_sub`,
  `DirichletCharacter.Gamma_mul_LFunction_χ₃_one_sub` (LMFDB `lfunction.history.dirichlet`): the
  functional equation, `(3 / π) ^ (s / 2) Γ((s + 1) / 2) L(s, χ₃)` is invariant under `s ↦ 1 - s`.
* `DirichletCharacter.completedLFunctionModThree_ne_zero_of_one_le_re`,
  `DirichletCharacter.completedLFunctionModThree_ne_zero_of_re_nonpos`: this entire function has no
  zero outside the strip `0 < re s < 1`.
* `DirichletCharacter.hasSum_LFunction_χ₃`: `L(s, χ₃) = ∑ ((3k + 1) ^ (-s) - (3k + 2) ^ (-s))` for
  `re s > 1`.
* `DirichletCharacter.hasSum_LFunction_χ₃_one`: `L(1, χ₃) = 1 - 1/2 + 1/4 - 1/5 + 1/7 - 1/8 + ⋯`.
* `DirichletCharacter.LFunction_χ₃_apply_one` (LMFDB `lfunction.history.dirichlet`): the special
  value `L(1, χ₃) = π / (3 √3)`.
* `DirichletCharacter.LFunction_χ₃_apply_one_ne_zero`: `L(1, χ₃) ≠ 0`, from the special value.

## References

* P. G. L. Dirichlet, *Beweis des Satzes, dass jede unbegrenzte arithmetische Progression, deren
  erstes Glied und Differenz ganze Zahlen ohne gemeinschaftlichen Factor sind, unendlich viele
  Primzahlen enthält* (1837), Werke I, 313–342.
-/

open Complex Filter ZMod

open scoped Real Topology

private lemma Complex.cos_pi_div_three : cos (π / 3 : ℂ) = 1 / 2 := by
  rw [← ofReal_ofNat 3, ← ofReal_div, ← ofReal_cos, Real.cos_pi_div_three, ofReal_div, ofReal_one,
    ofReal_ofNat]

private lemma Complex.sin_pi_div_three : sin (π / 3 : ℂ) = √3 / 2 := by
  rw [← ofReal_ofNat 3, ← ofReal_div, ← ofReal_sin, Real.sin_pi_div_three, ofReal_div, ofReal_ofNat]

private lemma Complex.ofReal_cpow_one_half {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) ^ (1 / 2 : ℂ) = √x := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow hx, ofReal_div, ofReal_one, ofReal_ofNat]

private lemma Complex.ofReal_pi_ne_zero : (π : ℂ) ≠ 0 :=
  ofReal_ne_zero.mpr Real.pi_ne_zero

private lemma Complex.ofReal_sqrt_three_ne_zero : ((√3 : ℝ) : ℂ) ≠ 0 :=
  ofReal_ne_zero.mpr <| Real.sqrt_ne_zero'.mpr zero_lt_three

namespace DirichletCharacter

variable {s : ℂ} {σ : ℝ} (n : ℕ)

/-- The **Dirichlet character `χ₃` modulo `3`** (LMFDB `lfunction.history.dirichlet`), with values
`1`, `-1`, `0` at the integers congruent to `1`, `2`, `0` modulo `3`
(`DirichletCharacter.χ₃_intCast`): the quadratic character of the field `ℤ/3ℤ`, with complex
values. -/
noncomputable def χ₃ : DirichletCharacter ℂ 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

@[simp]
lemma χ₃_apply_zero : χ₃ 0 = 0 :=
  χ₃.map_zero

@[simp]
lemma χ₃_apply_two : χ₃ 2 = -1 := by
  simp [χ₃, (by decide : quadraticChar (ZMod 3) 2 = -1)]

/-- **The values of `χ₃`** (LMFDB `lfunction.history.dirichlet`): `χ₃(m)` is `1`, `-1` or `0` as the
integer `m` is congruent to `1`, `2` or `0` modulo `3`. -/
lemma χ₃_intCast (m : ℤ) : χ₃ m = if m % 3 = 1 then 1 else if m % 3 = 2 then -1 else 0 := by
  have h₀ : 0 ≤ m % 3 := m.emod_nonneg three_ne_zero
  have h₃ : m % 3 < 3 := m.emod_lt_of_pos three_pos
  rw [← ZMod.intCast_mod m 3]
  interval_cases m % 3 <;> simp

lemma χ₃_natCast : χ₃ n = if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0 :=
  mod_cast χ₃_intCast n

lemma isQuadratic_χ₃ : χ₃.IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod 3)).comp _

lemma inv_χ₃ : χ₃⁻¹ = χ₃ :=
  isQuadratic_χ₃.inv

lemma odd_χ₃ : χ₃.Odd :=
  χ₃_apply_two

lemma χ₃_ne_one : χ₃ ≠ 1 :=
  fun h ↦ odd_χ₃.not_even χ₃ <| h ▸ MulChar.one_apply isUnit_one.neg

/-- **The character `χ₃` is primitive**: its conductor divides the prime `3` and is not `1`. -/
lemma isPrimitive_χ₃ : χ₃.IsPrimitive :=
  (Nat.prime_three.eq_one_or_self_of_dvd _ χ₃.conductor_dvd_level).resolve_left <|
    mt eq_one_iff_conductor_eq_one.mpr χ₃_ne_one

/-- **The Gauss sum of `χ₃`** for the standard additive character `n ↦ e ^ (2πi n / 3)` is
`τ(χ₃) = e ^ (2πi / 3) - e ^ (4πi / 3) = √3 i`. -/
lemma gaussSum_χ₃ : gaussSum χ₃ stdAddChar = √3 * I := by
  have h (f : ZMod 3 → ℂ) : ∑ a, f a = f 0 + f 1 + f 2 := Fin.sum_univ_three f
  have h₁ : stdAddChar (1 : ZMod 3) = cexp (2 * π * I * 1 / 3) := mod_cast stdAddChar_coe 1
  have h₂ : stdAddChar (2 : ZMod 3) = cexp (2 * π * I * 2 / 3) := mod_cast stdAddChar_coe 2
  rw [gaussSum, h, χ₃_apply_zero, map_one, χ₃_apply_two, h₁, h₂,
    (by ring1 : (2 * π * I * 1 / 3 : ℂ) = (π - π / 3) * I),
    (by ring1 : (2 * π * I * 2 / 3 : ℂ) = (π / 3 + π) * I), exp_mul_I, exp_mul_I, cos_pi_sub,
    sin_pi_sub, cos_add_pi, sin_add_pi, sin_pi_div_three]
  ring1

/-- **The root number of `χ₃`** is `1`: `χ₃` is odd, and `τ(χ₃) / (i √3) = 1`. -/
lemma rootNumber_χ₃ : rootNumber χ₃ = 1 := by
  have h : ((3 : ℕ) : ℂ) ^ (1 / 2 : ℂ) = √3 := mod_cast ofReal_cpow_one_half zero_le_three
  rw [rootNumber, gaussSum_χ₃, ite_eq_right (odd_χ₃.not_even χ₃), h, pow_one,
    mul_div_cancel_right₀ _ I_ne_zero, div_self ofReal_sqrt_three_ne_zero]

variable (s) in
lemma completedLFunction_χ₃_one_sub :
    completedLFunction χ₃ (1 - s) = 3 ^ (s - 1 / 2) * completedLFunction χ₃ s := by
  rw [isPrimitive_χ₃.completedLFunction_one_sub, rootNumber_χ₃, inv_χ₃, mul_one, Nat.cast_ofNat]

variable (s) in
lemma LFunction_χ₃_eq_completed_div_Gammaℝ :
    LFunction χ₃ s = completedLFunction χ₃ s / Gammaℝ (s + 1) :=
  odd_χ₃.gammaFactor_def s ▸ χ₃.LFunction_eq_completed_div_gammaFactor s (.inr (by norm_num))

variable (s) in
/-- The **completed L-function of `χ₃`** as normalised in LMFDB `lfunction.history.dirichlet`: the
entire function `√π 3 ^ (s / 2) Λ(s, χ₃)`, where `Λ(s, χ₃) = Γ_ℝ(s + 1) L(s, χ₃)` is Mathlib's
`DirichletCharacter.completedLFunction`. It is `(3 / π) ^ (s / 2) Γ((s + 1) / 2) L(s, χ₃)` wherever
`Γ((s + 1) / 2)` has no pole (`DirichletCharacter.completedLFunctionModThree_eq`). -/
noncomputable def completedLFunctionModThree : ℂ :=
  √π * 3 ^ (s / 2) * completedLFunction χ₃ s

variable (s) in
/-- **The knowl's completed L-function of `χ₃` is `√π` times that of the analytic L-function of
`χ₃`**: `AnalyticLFunction.dirichlet isPrimitive_χ₃`, of degree `1` and conductor `3`, is completed
by `3 ^ (s / 2) Λ(s, χ₃)`, and its sign is the root number `1` (`AnalyticLFunction.sign_dirichlet`,
`DirichletCharacter.rootNumber_χ₃`). -/
lemma completedLFunctionModThree_eq_sqrt_pi_mul_completed : completedLFunctionModThree s =
    √π * (AnalyticLFunction.dirichlet isPrimitive_χ₃).completed s := by
  rw [AnalyticLFunction.dirichlet_completed, completedLFunctionModThree, Nat.cast_ofNat, mul_assoc]

/-- **The function `(3 / π) ^ (s / 2) Γ((s + 1) / 2) L(s, χ₃)` is entire.** -/
lemma differentiable_completedLFunctionModThree : Differentiable ℂ completedLFunctionModThree :=
  ((differentiable_const _).mul <| (differentiable_id.div_const 2).const_cpow <|
    .inl three_ne_zero).mul <| differentiable_completedLFunction χ₃_ne_one

/-- **The completed L-function of `χ₃` is `(3 / π) ^ (s / 2) Γ((s + 1) / 2) L(s, χ₃)`** (LMFDB
`lfunction.history.dirichlet`), for `s` not among the poles `-1, -3, -5, …` of `Γ((s + 1) / 2)`. At
these poles the right-hand side is `0` in Lean (`Complex.Gamma_neg_nat_eq_zero`), unlike the
left-hand side (`DirichletCharacter.completedLFunctionModThree_ne_zero_of_re_nonpos`). -/
lemma completedLFunctionModThree_eq (hs : ∀ n : ℕ, s ≠ -(2 * n + 1)) :
    completedLFunctionModThree s = (3 / π) ^ (s / 2) * Gamma ((s + 1) / 2) * LFunction χ₃ s := by
  have hΓ : Gamma ((s + 1) / 2) ≠ 0 := Gamma_ne_zero fun n hn ↦ hs n (by linear_combination 2 * hn)
  have h : (3 / π : ℂ) ^ (s / 2) = 3 ^ (s / 2) / π ^ (s / 2) :=
    mod_cast div_cpow_ofReal_nonneg zero_le_three Real.pi_nonneg (s / 2)
  rw [completedLFunctionModThree, LFunction_χ₃_eq_completed_div_Gammaℝ, Gammaℝ_def, h,
    ← ofReal_cpow_one_half Real.pi_nonneg, (by ring1 : -(s + 1) / 2 = -(s / 2 + 1 / 2)), cpow_neg,
    cpow_add _ _ ofReal_pi_ne_zero]
  field_simp

variable (s) in
/-- **The functional equation of `L(s, χ₃)`** (LMFDB `lfunction.history.dirichlet`): the entire
function `(3 / π) ^ (s / 2) Γ((s + 1) / 2) L(s, χ₃)` is invariant under `s ↦ 1 - s`. -/
lemma completedLFunctionModThree_one_sub :
    completedLFunctionModThree (1 - s) = completedLFunctionModThree s := by
  rw [completedLFunctionModThree, completedLFunction_χ₃_one_sub, completedLFunctionModThree,
    mul_assoc, ← mul_assoc (3 ^ _), ← cpow_add _ _ three_ne_zero,
    (by ring1 : (1 - s) / 2 + (s - 1 / 2) = s / 2), mul_assoc]

/-- **The functional equation of `L(s, χ₃)`** (LMFDB `lfunction.history.dirichlet`), for the
expression `(3 / π) ^ (s / 2) Γ((s + 1) / 2) L(s, χ₃)` itself: it is invariant under `s ↦ 1 - s`
for `s` outside `-1, -3, -5, …` and `2, 4, 6, …`, where one of the two sides is not the value of
the entire function `DirichletCharacter.completedLFunctionModThree`, as Mathlib's `Complex.Gamma`
is `0` at its poles. -/
lemma Gamma_mul_LFunction_χ₃_one_sub (hs : ∀ n : ℕ, s ≠ -(2 * n + 1))
    (hs' : ∀ n : ℕ, s ≠ 2 * n + 2) : (3 / π) ^ ((1 - s) / 2) * Gamma ((1 - s + 1) / 2) *
    LFunction χ₃ (1 - s) = (3 / π) ^ (s / 2) * Gamma ((s + 1) / 2) * LFunction χ₃ s := by
  rw [← completedLFunctionModThree_eq hs,
    ← completedLFunctionModThree_eq fun n hn ↦ hs' n (by linear_combination -hn),
    completedLFunctionModThree_one_sub]

/-- **The completed L-function of `χ₃` does not vanish for `re s ≥ 1`**, as `L(s, χ₃)` does not
(Mathlib's `DirichletCharacter.LFunction_ne_zero_of_one_le_re`). -/
lemma completedLFunctionModThree_ne_zero_of_one_le_re (hs : 1 ≤ s.re) :
    completedLFunctionModThree s ≠ 0 :=
  mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr <| Real.sqrt_ne_zero'.mpr Real.pi_pos) <|
    cpow_ne_zero_iff.mpr <| .inl three_ne_zero) (div_ne_zero_iff.mp <|
      LFunction_χ₃_eq_completed_div_Gammaℝ s ▸
        χ₃.LFunction_ne_zero_of_one_le_re (.inl χ₃_ne_one) hs).1

/-- **The completed L-function of `χ₃` does not vanish for `re s ≤ 0`**, by the functional
equation. In particular it is not `0` at the poles `s = -1, -3, -5, …` of `Γ((s + 1) / 2)`, where
the expression `(3 / π) ^ (s / 2) * Gamma ((s + 1) / 2) * LFunction χ₃ s` is `0` in Lean. -/
lemma completedLFunctionModThree_ne_zero_of_re_nonpos (hs : s.re ≤ 0) :
    completedLFunctionModThree s ≠ 0 :=
  completedLFunctionModThree_one_sub s ▸
    completedLFunctionModThree_ne_zero_of_one_le_re (by simpa using hs)

/-- **The series for `L(s, χ₃)`**, for `re s > 1`, summed over the pairs of consecutive integers
`3k + 1` and `3k + 2`: `L(s, χ₃)` is the sum over `k ≥ 0` of
`(3k + 1) ^ (-s) - (3k + 2) ^ (-s)`. -/
lemma hasSum_LFunction_χ₃ (hs : 1 < s.re) :
    HasSum (fun k : ℕ ↦ 1 / (3 * k + 1 : ℂ) ^ s - 1 / (3 * k + 2 : ℂ) ^ s) (LFunction χ₃ s) := by
  have hL : HasSum (LSeries.term (χ₃ ·) s) (LFunction χ₃ s) :=
    χ₃.LFunction_eq_LSeries hs ▸ (ZMod.LSeriesSummable_of_one_lt_re χ₃ hs).LSeriesHasSum
  refine ((Nat.divModEquiv 3).symm.hasSum_iff.mpr hL).prod_fiberwise fun k ↦ ?_
  have h₃ : (3 : ZMod 3) = 0 := rfl
  have h : 1 / (3 * k + 1 : ℂ) ^ s - 1 / (3 * k + 2 : ℂ) ^ s =
      ∑ c : Fin 3, (LSeries.term (χ₃ ·) s ∘ (Nat.divModEquiv 3).symm) (k, c) := by
    rw [Fin.sum_univ_three]
    simp [LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), h₃, mul_comm, sub_eq_add_neg, neg_div]
  exact h ▸ hasSum_fintype _

private lemma abs_one_div_rpow_sub_one_div_rpow_le {x : ℝ} (hx : 1 ≤ x) (hσ₁ : 1 ≤ σ)
    (hσ₂ : σ ≤ 2) : |1 / x ^ σ - 1 / (x + 1) ^ σ| ≤ 2 / x ^ 2 := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hx₁ : x ≤ x + 1 := (lt_add_one x).le
  have hx₂ : 0 < x + 1 := hx₀.trans_le hx₁
  have ha : x ≤ x ^ σ := x.rpow_one.ge.trans <| Real.rpow_le_rpow_of_exponent_le hx hσ₁
  have hab : x ^ σ / (x + 1) ^ σ ≤ 1 :=
    (div_le_one <| Real.rpow_pos_of_pos hx₂ σ).mpr <|
      Real.rpow_le_rpow hx₀.le hx₁ (zero_le_one.trans hσ₁)
  have hB : 1 + σ * (x / (x + 1) - 1) ≤ (1 + (x / (x + 1) - 1)) ^ σ :=
    one_add_mul_self_le_rpow_one_add (by linarith [div_nonneg hx₀.le hx₂.le]) hσ₁
  have h₁ : x / (x + 1) = 1 - 1 / (x + 1) :=
    eq_sub_of_add_eq <| (add_div x 1 (x + 1)).symm.trans (div_self hx₂.ne')
  have h₂ : σ * (1 / (x + 1)) ≤ 2 / x :=
    (mul_one_div σ (x + 1)).trans_le <| div_le_div₀ zero_le_two hσ₂ hx₀ hx₁
  rw [add_sub_cancel, Real.div_rpow hx₀.le hx₂.le, h₁] at hB
  rw [(by field_simp : 1 / x ^ σ - 1 / (x + 1) ^ σ = (1 - x ^ σ / (x + 1) ^ σ) / x ^ σ),
    abs_of_nonneg (div_nonneg (sub_nonneg.mpr hab) (hx₀.le.trans ha)), sq, ← div_div]
  exact div_le_div₀ (by positivity) (by linarith) hx₀ ha

private lemma norm_one_div_cpow_sub_one_div_cpow_le (hσ₁ : 1 ≤ σ) (hσ₂ : σ ≤ 2) :
    ‖1 / (3 * n + 1 : ℂ) ^ (σ : ℂ) - 1 / (3 * n + 2 : ℂ) ^ (σ : ℂ)‖ ≤ 2 / (3 * n + 1) ^ 2 := by
  have h : |1 / (3 * n + 1 : ℝ) ^ σ - 1 / (3 * n + 1 + 1 : ℝ) ^ σ| ≤ 2 / (3 * n + 1) ^ 2 :=
    abs_one_div_rpow_sub_one_div_rpow_le (le_add_of_nonneg_left (by positivity)) hσ₁ hσ₂
  rw [← Real.norm_eq_abs, ← norm_real, ofReal_sub, ofReal_div, ofReal_div,
    ofReal_cpow (by positivity), ofReal_cpow (by positivity)] at h
  push_cast at h
  rwa [add_assoc, one_add_one_eq_two] at h

/-- **The series for `L(1, χ₃)`**: `L(1, χ₃) = 1 - 1/2 + 1/4 - 1/5 + 1/7 - 1/8 + ⋯`, the sum over
`k ≥ 0` of `1 / (3k + 1) - 1 / (3k + 2)`. For real `σ > 1` the L-function is the sum of the terms
`(3k + 1) ^ (-σ) - (3k + 2) ^ (-σ)`, which are at most `2 / (3k + 1) ^ 2` for `σ ≤ 2`, so the
identity passes to the limit `σ → 1` by dominated convergence, `L(s, χ₃)` being continuous at
`s = 1`. -/
lemma hasSum_LFunction_χ₃_one :
    HasSum (fun k : ℕ ↦ (1 / (3 * k + 1) - 1 / (3 * k + 2) : ℂ)) (LFunction χ₃ 1) := by
  have hb : Summable fun k : ℕ ↦ (2 / (3 * k + 1) ^ 2 : ℝ) :=
    (((Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective
      fun a b (h : 3 * a + 1 = 3 * b + 1) ↦ by omega).mul_left 2).congr fun k ↦ by
        simp [div_eq_mul_inv]
  have hc {c : ℂ} (h : c ≠ 0) : Tendsto (fun σ : ℝ ↦ 1 / c ^ (σ : ℂ)) (𝓝[>] 1) (𝓝 (1 / c)) :=
    tendsto_const_nhds.div (tendsto_nhdsWithin_of_tendsto_nhds <|
      (continuous_ofReal.const_cpow (.inl h)).tendsto' 1 c (by rw [ofReal_one, cpow_one])) h
  have h₁ (k : ℕ) : (3 * k + 1 : ℂ) ≠ 0 := mod_cast (3 * k).succ_ne_zero
  have h₂ (k : ℕ) : (3 * k + 2 : ℂ) ≠ 0 := mod_cast (3 * k + 1).succ_ne_zero
  have hL : Tendsto (fun σ : ℝ ↦ LFunction χ₃ σ) (𝓝[>] 1) (𝓝 (LFunction χ₃ 1)) :=
    tendsto_nhdsWithin_of_tendsto_nhds <| ((differentiable_LFunction χ₃_ne_one).continuous.comp'
      continuous_ofReal).tendsto' 1 _ (congrArg _ ofReal_one)
  have h : ∀ᶠ σ : ℝ in 𝓝[>] 1, LFunction χ₃ σ =
      ∑' k : ℕ, (1 / (3 * k + 1 : ℂ) ^ (σ : ℂ) - 1 / (3 * k + 2 : ℂ) ^ (σ : ℂ)) :=
    eventually_mem_nhdsWithin.mono fun σ hσ ↦
      (hasSum_LFunction_χ₃ (by rwa [ofReal_re])).tsum_eq.symm
  rw [tendsto_nhds_unique (hL.congr' h) <| tendsto_tsum_of_dominated_convergence hb
    (fun k ↦ (hc (h₁ k)).sub (hc (h₂ k))) <| eventually_of_mem (Ioc_mem_nhdsGT one_lt_two)
      fun σ hσ k ↦ norm_one_div_cpow_sub_one_div_cpow_le k hσ.1.le hσ.2]
  exact (hb.of_norm_bounded fun k ↦ by
    simpa using norm_one_div_cpow_sub_one_div_cpow_le k le_rfl one_le_two).hasSum

private lemma one_div_three_mem_integerComplement : (1 / 3 : ℂ) ∈ integerComplement := by
  rintro ⟨m, hm⟩
  have h : 3 * m = 1 := mod_cast (congrArg (3 * ·) hm).trans (mul_one_div_cancel three_ne_zero)
  omega

private lemma sum_range_one_div_sub_one_div :
    ∑ k ∈ Finset.range n, (1 / (3 * k + 1) - 1 / (3 * k + 2) : ℂ) =
      1 / 3 * ∑ k ∈ Finset.range n, cotTerm (1 / 3) k + (1 - 1 / (3 * n + 1 : ℕ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, cotTerm,
      (by ring1 : (1 / 3 : ℂ) - (n + 1) = -(3 * n + 2) / 3)]
    push_cast
    field_simp
    ring1

/-- **The special value `L(1, χ₃) = π / (3 √3)`** (LMFDB `lfunction.history.dirichlet`): by the
partial fraction expansion of the cotangent at `1 / 3`, the series
`1 - 1/2 + 1/4 - 1/5 + 1/7 - 1/8 + ⋯` for `L(1, χ₃)` has sum `(π / 3) cot(π / 3)`. -/
lemma LFunction_χ₃_apply_one : LFunction χ₃ 1 = π / (3 * √3) := by
  rw [tendsto_nhds_unique hasSum_LFunction_χ₃_one.tendsto_sum_nat <|
    (((tendsto_logDeriv_euler_cot_sub one_div_three_mem_integerComplement).const_mul (1 / 3)).add <|
      tendsto_const_nhds.sub <| tendsto_one_div_atTop_nhds_zero_nat.comp <|
        tendsto_atTop_mono (fun n ↦ (by omega : n ≤ 3 * n + 1)) tendsto_id).congr fun n ↦
          (sum_range_one_div_sub_one_div n).symm,
    (by ring1 : (π : ℂ) * (1 / 3) = π / 3), cot_eq_cos_div_sin, cos_pi_div_three, sin_pi_div_three]
  ring1

/-- **`L(1, χ₃) ≠ 0`**, from the special value `L(1, χ₃) = π / (3 √3)`, as in Dirichlet's proof of
his theorem. Mathlib's `DirichletCharacter.LFunction_apply_one_ne_zero` proves that `L(1, χ) ≠ 0`
for every Dirichlet character `χ ≠ 1`. -/
lemma LFunction_χ₃_apply_one_ne_zero : LFunction χ₃ 1 ≠ 0 :=
  LFunction_χ₃_apply_one ▸
    div_ne_zero ofReal_pi_ne_zero (mul_ne_zero three_ne_zero ofReal_sqrt_three_ne_zero)

end DirichletCharacter
