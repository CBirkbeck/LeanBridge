import LeanBridge.ForMathlib.Analysis.SpecialFunctions.JacobiTripleProduct
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# The product expansion of the Jacobi theta function and its eta quotients

Let `θ(τ) = ∑_{n ∈ ℤ} e^{πin²τ}` be Jacobi's theta function (Mathlib's `jacobiTheta`), and write
`s = e^{πiτ}` and `q = e^{2πiτ} = s²`. By the Jacobi triple product identity, for `Im τ > 0`,

`θ(τ) = ∏_{n ≥ 1} (1 - s^(2n)) (1 + s^(2n-1))² = ∏_{n ≥ 1} (1 + q^(n-1/2))² (1 - qⁿ)`,

and more generally the two-variable theta function `θ(z, τ) = ∑_{n ∈ ℤ} e^{2πinz + πin²τ}`
(Mathlib's `jacobiTheta₂`) is `∏_{n ≥ 1} (1 - s^(2n)) (1 + w s^(2n-1)) (1 + w⁻¹ s^(2n-1))` with
`w = e^{2πiz}`. Sorting the factors `1 - xⁿ` of the Euler products by the parity of `n` turns the
product for `θ` into quotients of values of the Dedekind eta function
`η(τ) = e^{2πiτ/24} ∏_{n ≥ 1} (1 - qⁿ)`:

`θ(τ) = η(τ)⁵ / (η(τ/2)² η(2τ)²) = η((τ + 1)/2)² / η(τ + 1)`.

These are the product expansion and the two eta quotients of the LMFDB knowl
`mf.half_integral_weight.theta`, for the theta function `∑ e^{πizn²}` that the knowl writes. That
function is a modular form of weight `1/2` for the theta group, not of level `4`; the theta
function of level `4` is `θ(2z) = ∑_{n ∈ ℤ} e^{2πin²z}`, for which the same identities are restated
in `LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ThetaProduct`.

Tau Ceti's main, not at LeanBridge's pin, has the Euler-product bookkeeping that private lemmas do
here: the splitting of `∏_{n ≥ 1} (1 - qⁿ)` by the parity of `n`
(`TauCeti.tprod_one_sub_pow_eq_tprod_one_sub_pow_odd_mul`,
`TauCeti.tprod_one_sub_pow_odd_mul_tprod_one_add_pow_odd`), `η` as an exponential times the Euler
product (`TauCeti.ModularForm.eta_eq_exp_mul_tprod`), and `η(2τ)`, `η(τ/2)` and `η((τ + 1)/2)` as
`η(τ)` times products (`TauCeti.ModularForm.eta_two_mul`, `TauCeti.ModularForm.eta_div_two`,
`TauCeti.ModularForm.eta_add_one_div_two`). They can replace those lemmas after the bump.

## Main results

* `jacobiTheta₂_eq_tprod`: the Jacobi triple product for the two-variable theta function.
* `hasProd_jacobiTheta`: the product `∏_{n ≥ 1} (1 - s^(2n)) (1 + s^(2n-1))²` converges to `θ(τ)`.
* `jacobiTheta_eq_tprod`: `θ(τ) = ∏_{n ≥ 1} (1 - s^(2n)) (1 + s^(2n-1))²`.
* `jacobiTheta_eq_tprod_half` (LMFDB `mf.half_integral_weight.theta`):
  `θ(τ) = ∏_{n ≥ 1} (1 + q^(n-1/2))² (1 - qⁿ)`.
* `jacobiTheta_eq_eta_pow_five_div` (LMFDB `mf.half_integral_weight.theta`):
  `θ(τ) = η(τ)⁵ / (η(τ/2)² η(2τ)²)`.
* `jacobiTheta_eq_eta_sq_div` (LMFDB `mf.half_integral_weight.theta`):
  `θ(τ) = η((τ + 1)/2)² / η(τ + 1)`.
-/

open Complex Function JacobiTripleProduct

open scoped Real ModularForm

/-- The Euler product `∏_{n ≥ 1} (1 - xⁿ)`. -/
private noncomputable def eulerProd (x : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - x ^ (n + 1))

/-- The product `∏_{n ≥ 1} (1 + x^(2n-1))`. -/
private noncomputable def oddProd (x : ℂ) : ℂ :=
  ∏' n : ℕ, (1 + x ^ (2 * n + 1))

variable {x τ : ℂ} (z : ℂ)

private lemma multipliable_one_sub_pow_odd (hx : ‖x‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 - x ^ (2 * n + 1) := by
  simpa only [neg_one_mul, ← sub_eq_add_neg] using multipliable_one_add_mul_pow (-1) hx

private lemma eulerProd_eq_mul (hx : ‖x‖ < 1) :
    eulerProd x = (∏' n : ℕ, (1 - x ^ (2 * n + 1))) * eulerProd (x ^ 2) := by
  have h : Multipliable fun n : ℕ ↦ 1 - x ^ (2 * n + 1 + 1) :=
    (multipliable_one_sub_pow (norm_sq_lt_one hx)).congr fun n ↦ by ring1
  exact (tprod_even_mul_odd (f := fun n ↦ 1 - x ^ (n + 1)) (multipliable_one_sub_pow_odd hx)
    h).symm.trans <| congrArg _ <| tprod_congr fun n ↦ by ring1

private lemma oddProd_mul (hx : ‖x‖ < 1) :
    oddProd x * ∏' n : ℕ, (1 - x ^ (2 * n + 1)) = ∏' n : ℕ, (1 - (x ^ 2) ^ (2 * n + 1)) := by
  have h : Multipliable fun n : ℕ ↦ 1 + x ^ (2 * n + 1) := by
    simpa only [one_mul] using multipliable_one_add_mul_pow 1 hx
  rw [oddProd, ← h.tprod_mul (multipliable_one_sub_pow_odd hx)]
  exact tprod_congr fun n ↦ by ring1

private lemma oddProd_mul_eulerProd_mul (hx : ‖x‖ < 1) :
    oddProd x * eulerProd x * eulerProd (x ^ 4) = eulerProd (x ^ 2) ^ 2 := by
  have h : eulerProd (x ^ 2) = (∏' n : ℕ, (1 - (x ^ 2) ^ (2 * n + 1))) * eulerProd (x ^ 4) := by
    rw [eulerProd_eq_mul (norm_sq_lt_one hx), ← pow_mul]
  linear_combination oddProd x * eulerProd (x ^ 4) * eulerProd_eq_mul hx +
    eulerProd (x ^ 2) * eulerProd (x ^ 4) * oddProd_mul hx - eulerProd (x ^ 2) * h

private lemma eulerProd_neg (hx : ‖x‖ < 1) : eulerProd (-x) = oddProd x * eulerProd (x ^ 2) := by
  rw [eulerProd_eq_mul (by rwa [norm_neg]), neg_sq]
  exact congrArg (· * _) <| tprod_congr fun n ↦ by
    rw [(odd_two_mul_add_one n).neg_pow, sub_neg_eq_add]

private lemma norm_cexp_pi_mul_I_mul_lt_one (hτ : 0 < τ.im) : ‖cexp (π * I * τ)‖ < 1 := by
  rw [norm_exp, Real.exp_lt_one_iff]
  simpa using mul_pos Real.pi_pos hτ

variable (τ) in
private lemma jacobiTheta₂_term_eq (n : ℤ) :
    jacobiTheta₂_term n z τ = cexp (2 * π * I * z) ^ n * cexp (π * I * τ) ^ n ^ 2 := by
  rw [jacobiTheta₂_term, exp_add, ← exp_int_mul, ← exp_int_mul]
  congr 2 <;> push_cast <;> ring1

/-- **The Jacobi triple product for the two-variable theta function**: for `Im τ > 0`,
`θ(z, τ) = ∏_{n ≥ 1} (1 - s^(2n)) (1 + w s^(2n-1)) (1 + w⁻¹ s^(2n-1))`, where `w = e^{2πiz}` and
`s = e^{πiτ}`. -/
lemma jacobiTheta₂_eq_tprod (hτ : 0 < τ.im) : jacobiTheta₂ z τ =
    ∏' n : ℕ, (1 - cexp (π * I * τ) ^ (2 * (n + 1))) *
        (1 + cexp (2 * π * I * z) * cexp (π * I * τ) ^ (2 * n + 1)) *
        (1 + cexp (-(2 * π * I * z)) * cexp (π * I * τ) ^ (2 * n + 1)) := by
  rw [jacobiTheta₂, tsum_congr fun n ↦ jacobiTheta₂_term_eq τ z n, exp_neg]
  exact tsum_zpow_mul_zpow_sq (norm_cexp_pi_mul_I_mul_lt_one hτ) (exp_ne_zero _)

variable (τ) in
private lemma jacobiTheta_eq_tsum :
    jacobiTheta τ = ∑' n : ℤ, (1 : ℂ) ^ n * cexp (π * I * τ) ^ n ^ 2 := by
  refine tsum_congr fun n ↦ ?_
  rw [one_zpow, one_mul, ← exp_int_mul]
  congr 1
  push_cast
  ring1

/-- **The product expansion of the Jacobi theta function**: for `Im τ > 0`, the product
`∏_{n ≥ 1} (1 - s^(2n)) (1 + s^(2n-1))²` converges to `θ(τ)`, where `s = e^{πiτ}`. -/
lemma hasProd_jacobiTheta (hτ : 0 < τ.im) : HasProd
    (fun n : ℕ ↦ (1 - cexp (π * I * τ) ^ (2 * (n + 1))) * (1 + cexp (π * I * τ) ^ (2 * n + 1)) ^ 2)
    (jacobiTheta τ) := by
  rw [jacobiTheta_eq_tsum]
  exact (hasProd_tsum_zpow_mul_zpow_sq (norm_cexp_pi_mul_I_mul_lt_one hτ) one_ne_zero).congr_fun
    fun n ↦ by
      rw [inv_one, one_mul]
      ring1

/-- **The product expansion of the Jacobi theta function**: for `Im τ > 0`,
`θ(τ) = ∏_{n ≥ 1} (1 - s^(2n)) (1 + s^(2n-1))²`, where `s = e^{πiτ}`. -/
lemma jacobiTheta_eq_tprod (hτ : 0 < τ.im) : jacobiTheta τ =
    ∏' n : ℕ, (1 - cexp (π * I * τ) ^ (2 * (n + 1))) * (1 + cexp (π * I * τ) ^ (2 * n + 1)) ^ 2 :=
  (hasProd_jacobiTheta hτ).tprod_eq.symm

variable (τ) in
private lemma cexp_two_pi_mul_I_mul : cexp (2 * π * I * τ) = cexp (π * I * τ) ^ 2 := by
  rw [← exp_nat_mul]
  congr 1
  push_cast
  ring1

/-- **The product expansion of the theta function** (LMFDB `mf.half_integral_weight.theta`): for
`Im τ > 0`, `θ(τ) = ∏_{n ≥ 1} (1 + q^(n-1/2))² (1 - qⁿ)`, where `q = e^{2πiτ}` and
`q^(n-1/2) = e^{2πiτ(n-1/2)}`. -/
lemma jacobiTheta_eq_tprod_half (hτ : 0 < τ.im) : jacobiTheta τ =
    ∏' n : ℕ, (1 + cexp (2 * π * I * τ * (n + 1 / 2))) ^ 2 *
        (1 - cexp (2 * π * I * τ) ^ (n + 1)) := by
  rw [jacobiTheta_eq_tprod hτ]
  refine tprod_congr fun n ↦ ?_
  have h : cexp (2 * π * I * τ * (n + 1 / 2)) = cexp (π * I * τ) ^ (2 * n + 1) := by
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring1
  rw [h, cexp_two_pi_mul_I_mul, ← pow_mul, mul_comm]

private lemma jacobiTheta_eq_mul (hτ : 0 < τ.im) :
    jacobiTheta τ = eulerProd (cexp (π * I * τ) ^ 2) * oddProd (cexp (π * I * τ)) ^ 2 := by
  rw [jacobiTheta_eq_tsum, tsum_zpow_mul_zpow_sq_eq_mul (norm_cexp_pi_mul_I_mul_lt_one hτ)
    one_ne_zero]
  simp only [eulerProd, oddProd, inv_one, one_mul, pow_mul]
  ring1

variable (τ) in
private lemma eta_eq : η τ = cexp (2 * π * I * τ / 24) * eulerProd (cexp (2 * π * I * τ)) := by
  simp only [ModularForm.eta, ModularForm.eta_q_eq_pow, Periodic.qParam, ofReal_ofNat, eulerProd]

/-- **The theta function as an eta quotient** (LMFDB `mf.half_integral_weight.theta`): for
`Im τ > 0`, `θ(τ) = η(τ)⁵ / (η(τ/2)² η(2τ)²)`. -/
lemma jacobiTheta_eq_eta_pow_five_div (hτ : 0 < τ.im) :
    jacobiTheta τ = η τ ^ 5 / (η (τ / 2) ^ 2 * η (2 * τ) ^ 2) := by
  have hs : ‖cexp (π * I * τ)‖ < 1 := norm_cexp_pi_mul_I_mul_lt_one hτ
  have h₁ : cexp (2 * π * I * (τ / 2)) = cexp (π * I * τ) := by
    congr 1
    ring1
  have h₂ : cexp (2 * π * I * (2 * τ)) = cexp (π * I * τ) ^ 4 := by
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring1
  have he : cexp (2 * π * I * (τ / 2) / 24) ^ 2 * cexp (2 * π * I * (2 * τ) / 24) ^ 2 =
      cexp (2 * π * I * τ / 24) ^ 5 := by
    simp only [← exp_nat_mul, ← exp_add]
    congr 1
    push_cast
    ring1
  rw [eq_div_iff (mul_ne_zero (pow_ne_zero 2 <| ModularForm.eta_ne_zero <| by simpa using hτ) <|
    pow_ne_zero 2 <| ModularForm.eta_ne_zero <| by simpa using hτ), eta_eq, eta_eq, eta_eq, h₁, h₂,
    cexp_two_pi_mul_I_mul, jacobiTheta_eq_mul hτ]
  generalize cexp (π * I * τ) = s at hs ⊢
  linear_combination eulerProd (s ^ 2) * cexp (2 * π * I * (τ / 2) / 24) ^ 2 *
    cexp (2 * π * I * (2 * τ) / 24) ^ 2 * (oddProd s * eulerProd s * eulerProd (s ^ 4) +
      eulerProd (s ^ 2) ^ 2) * oddProd_mul_eulerProd_mul hs + eulerProd (s ^ 2) ^ 5 * he

/-- **The theta function as an eta quotient** (LMFDB `mf.half_integral_weight.theta`): for
`Im τ > 0`, `θ(τ) = η((τ + 1)/2)² / η(τ + 1)`. -/
lemma jacobiTheta_eq_eta_sq_div (hτ : 0 < τ.im) :
    jacobiTheta τ = η ((τ + 1) / 2) ^ 2 / η (τ + 1) := by
  have hs : ‖cexp (π * I * τ)‖ < 1 := norm_cexp_pi_mul_I_mul_lt_one hτ
  have h₁ : cexp (2 * π * I * ((τ + 1) / 2)) = -cexp (π * I * τ) := by
    rw [← neg_one_mul, ← exp_pi_mul_I, ← exp_add]
    congr 1
    ring1
  have h₂ : cexp (2 * π * I * (τ + 1)) = cexp (π * I * τ) ^ 2 := by
    rw [mul_add, exp_add, mul_one, exp_two_pi_mul_I, mul_one, cexp_two_pi_mul_I_mul]
  have he : cexp (2 * π * I * ((τ + 1) / 2) / 24) ^ 2 = cexp (2 * π * I * (τ + 1) / 24) := by
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring1
  rw [eq_div_iff (ModularForm.eta_ne_zero <| by simpa using hτ), eta_eq, eta_eq, h₁, h₂,
    jacobiTheta_eq_mul hτ, eulerProd_neg hs]
  linear_combination
    (-(oddProd (cexp (π * I * τ)) ^ 2 * eulerProd (cexp (π * I * τ) ^ 2) ^ 2)) * he
