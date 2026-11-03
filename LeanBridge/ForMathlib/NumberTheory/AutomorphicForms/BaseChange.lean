import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import Mathlib.RingTheory.RamificationInertia.Inertia

/-!
# Base change of GL(2) modular forms

Let `K ⊇ F` be a finite extension of number fields and `f` a modular form on `GL(2)` over `F` of
level `𝔑`, with good Euler factors `L_𝔭(f, T)`, `𝔭 ∤ 𝔑`. For `r ≥ 1` and `h ∈ ℂ[T]`, `h^{(r)}` is
the polynomial whose roots are the `r`-th powers of those of `h`, of the same degree. A modular
form `g` on `GL(2)` over `K` is a **base change** of `f` (LMFDB `mf.base_change`) if
`L_𝔮(g, T) = L_𝔭^{(r)}(f, T)` for all but finitely many primes `𝔮` of `K`, where `𝔮` lies over
`𝔭 ∤ 𝔑` and `r` is the residue degree of `𝔮` over `𝔭`.

Modular forms on `GL(2)` over an arbitrary number field are not formalised: what is missing is
the general notion (automorphic forms on `GL₂(𝔸_F)`, or tuples of functions on
`ℍ^{r₁} × ℋ₃^{r₂}` indexed by the class group) with Hecke operators `T_𝔭` at every `𝔭 ∤ 𝔑` and a
central character, which give `L_𝔭(f, T) = 1 - a_𝔭 T + χ(𝔭) N(𝔭)^{k-1} T²`; only classical
newforms (`F = ℚ`), Hilbert modular forms (`F` totally real) and Bianchi modular forms (`F`
imaginary quadratic of class number `1`) exist. The base change relation is therefore formalised
on the families of good Euler factors, through which the LMFDB defines it, and `h^{(r)}` is
formalised for every polynomial: normalised to keep the constant term, which is `1` for an Euler
factor, it maps `∏ᵢ (1 - αᵢ T)` to `∏ᵢ (1 - αᵢ^r T)`.

## Main definitions

* `Polynomial.rootPowers` (LMFDB `mf.base_change`): the polynomial `h^{(r)}`.
* `NumberField.IsBaseChangeOfEulerFactors` (LMFDB `mf.base_change`): the base change relation on
  families of good Euler factors.

## Main results

* `Polynomial.rootPowers_mul`: `h^{(r)}` of `(1 - αT)(1 - βT)` is `(1 - α^r T)(1 - β^r T)`.
* `Polynomial.rootPowers_two_of_quadratic`: for a quadratic Euler factor
  `h = 1 - aT + bT² = (1 - αT)(1 - βT)`, `h^{(2)} = 1 - (a² - 2b) T + b² T²`, the formula
  `α² + β² = a² - 2αβ` of the inert primes in LMFDB `mf.bianchi.base_change`.
-/

open Polynomial

namespace Polynomial

/-- The polynomial **`h^{(r)}`** (LMFDB `mf.base_change`) whose roots are the `r`-th powers of the
roots of `h ∈ ℂ[X]`, with multiplicity, of the same degree as `h` when `h(0) ≠ 0`:
`h^{(r)}(T) = h(0) ∏_ρ (1 - T / ρ^r)` over the roots `ρ` of `h`. The knowl does not fix the
scalar; it is normalised here by `h^{(r)}(0) = h(0)`, so that `h^{(r)} = ∏ᵢ (1 - αᵢ^r T)` for an
Euler factor `h = ∏ᵢ (1 - αᵢ T)`, as the base change of Euler factors requires. -/
noncomputable def rootPowers (r : ℕ) (h : ℂ[X]) : ℂ[X] :=
  C (h.coeff 0) * (h.roots.map fun ρ ↦ 1 - C (ρ ^ r)⁻¹ * X).prod

/-- **`h^{(r)}` of a product of linear factors**: for `α, β ≠ 0`, the polynomial `h^{(r)}` of
`h = (1 - αT)(1 - βT)` is `(1 - α^r T)(1 - β^r T)`. -/
lemma rootPowers_mul (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0) (r : ℕ) :
    ((1 - C α * X) * (1 - C β * X) : ℂ[X]).rootPowers r =
      (1 - C (α ^ r) * X) * (1 - C (β ^ r) * X) := by
  have hf (a : ℂ) (ha : a ≠ 0) : (1 - C a * X : ℂ[X]) = C (-a) * (X - C a⁻¹) := by
    rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ ha]
    simp [sub_eq_add_neg, add_comm]
  have hn (a : ℂ) (ha : a ≠ 0) : (1 - C a * X : ℂ[X]) ≠ 0 := by
    rw [hf a ha]
    exact mul_ne_zero (C_ne_zero.mpr (neg_ne_zero.mpr ha)) (X_sub_C_ne_zero _)
  have hr : ((1 - C α * X) * (1 - C β * X) : ℂ[X]).roots = {α⁻¹, β⁻¹} := by
    rw [roots_mul (mul_ne_zero (hn α hα) (hn β hβ)), hf α hα, hf β hβ,
      roots_C_mul _ (neg_ne_zero.mpr hα), roots_C_mul _ (neg_ne_zero.mpr hβ), roots_X_sub_C,
      roots_X_sub_C]
    rfl
  have hc : ((1 - C α * X) * (1 - C β * X) : ℂ[X]).coeff 0 = 1 := by
    simp
  rw [rootPowers, hr, hc]
  simp

lemma exists_eq_mul_of_quadratic (a b : ℂ) (hb : b ≠ 0) : ∃ α β : ℂ, α ≠ 0 ∧ β ≠ 0 ∧
    (1 - C a * X + C b * X ^ 2 : ℂ[X]) = (1 - C α * X) * (1 - C β * X) := by
  have he : (X ^ 2 - C a * X + C b : ℂ[X]) = X ^ 2 + (C (-a) * X + C b) := by
    simp only [map_neg]
    ring1
  have hdeg : (X ^ 2 - C a * X + C b : ℂ[X]).degree ≠ 0 := by
    rw [he, degree_add_eq_left_of_degree_lt]
    · simp
    · rw [degree_X_pow]
      exact (degree_linear_le).trans_lt (by decide)
  rcases IsAlgClosed.exists_root _ hdeg with ⟨α, hα⟩
  have hα' : α ^ 2 - a * α + b = 0 := by
    simpa using hα
  have hb' : α * (a - α) = b := by
    linear_combination -hα'
  refine ⟨α, a - α, left_ne_zero_of_mul (hb' ▸ hb), right_ne_zero_of_mul (hb' ▸ hb), ?_⟩
  rw [← hb', C_mul, C_sub]
  ring1

/-- **`h^{(2)}` of a quadratic Euler factor**: for `h = 1 - aT + bT² = (1 - αT)(1 - βT)` with
`b ≠ 0`, `h^{(2)} = (1 - α²T)(1 - β²T) = 1 - (a² - 2b) T + b² T²`. -/
lemma rootPowers_two_of_quadratic (a b : ℂ) (hb : b ≠ 0) :
    rootPowers 2 (1 - C a * X + C b * X ^ 2) = 1 - C (a ^ 2 - 2 * b) * X + C (b ^ 2) * X ^ 2 := by
  rcases exists_eq_mul_of_quadratic a b hb with ⟨α, β, hα, hβ, he⟩
  have hm : ((1 - C α * X) * (1 - C β * X) : ℂ[X]) = 1 - C (α + β) * X + C (α * β) * X ^ 2 := by
    simp only [map_add, map_mul]
    ring1
  have ha : a = α + β := by
    simpa only [coeff_add, coeff_sub, coeff_one, coeff_C_mul_X, coeff_C_mul_X_pow, one_ne_zero,
      OfNat.one_ne_ofNat, ↓reduceIte, zero_sub, add_zero, neg_inj]
      using congrArg (coeff · 1) (he.trans hm)
  have hb' : b = α * β := by
    simpa only [coeff_add, coeff_sub, coeff_one, coeff_C_mul_X, coeff_C_mul_X_pow,
      OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte, sub_zero, zero_add]
      using congrArg (coeff · 2) (he.trans hm)
  rw [he, rootPowers_mul α β hα hβ, ha, hb']
  simp only [map_sub, map_mul, map_pow, map_add, map_ofNat]
  ring1

end Polynomial

namespace NumberField

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- A modular form `g` on `GL(2)` over `K`, with good Euler factors `Lg 𝔮`, is a **base change**
(LMFDB `mf.base_change`) of a modular form `f` on `GL(2)` over `F ⊆ K` of level `𝔑`, with good
Euler factors `Lf 𝔭` at the primes `𝔭 ∤ 𝔑`: `L_𝔮(g, T) = L_𝔭^{(r)}(f, T)` for all but finitely
many primes `𝔮` of `K`, where `𝔮` lies over `𝔭 ∤ 𝔑` and `r` is the residue degree of `𝔮` over `𝔭`.
Modular forms on `GL(2)` over arbitrary number fields are not formalised, so the relation is
stated on the families of good Euler factors through which the LMFDB defines it. -/
def IsBaseChangeOfEulerFactors (𝔑 : Ideal (𝓞 F)) (Lf : Ideal (𝓞 F) → ℂ[X])
    (Lg : Ideal (𝓞 K) → ℂ[X]) : Prop :=
  ∀ᶠ 𝔮 in Filter.cofinite, 𝔮.IsPrime → 𝔮 ≠ ⊥ → ¬𝔑 ≤ 𝔮.comap (algebraMap (𝓞 F) (𝓞 K)) →
    Lg 𝔮 = (Lf (𝔮.comap (algebraMap (𝓞 F) (𝓞 K)))).rootPowers (𝔮.inertiaDeg (𝓞 F))

end NumberField
