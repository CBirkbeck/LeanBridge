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

/-- **`h^{(2)}` of a quadratic Euler factor**: for `h = 1 - aT + bT² = (1 - αT)(1 - βT)` with
`b ≠ 0`, `h^{(2)} = (1 - α²T)(1 - β²T) = 1 - (a² - 2b) T + b² T²`. -/
lemma rootPowers_two_of_quadratic (a b : ℂ) (hb : b ≠ 0) :
    rootPowers 2 (1 - C a * X + C b * X ^ 2) = 1 - C (a ^ 2 - 2 * b) * X + C (b ^ 2) * X ^ 2 := by
  have hh : (1 - C a * X + C b * X ^ 2 : ℂ[X]) = C b * X ^ 2 + C (-a) * X + C 1 := by
    simp only [map_neg, map_one]
    ring1
  have hdeg : (C b * X ^ 2 + C (-a) * X + C 1 : ℂ[X]).natDegree = 2 := natDegree_quadratic hb
  rcases Multiset.card_eq_two.mp (IsAlgClosed.card_roots_eq_natDegree.trans hdeg) with
    ⟨ρ₁, ρ₂, hρ⟩
  have h₀ : 1 = b * ρ₁ * ρ₂ := eq_mul_mul_of_roots_quadratic_eq_pair hρ
  have h₁ : -a = -b * (ρ₁ + ρ₂) := eq_neg_mul_add_of_roots_quadratic_eq_pair hρ
  have hρ₁ : ρ₁ ≠ 0 := fun h ↦ by simp [h] at h₀
  have hρ₂ : ρ₂ ≠ 0 := fun h ↦ by simp [h] at h₀
  have hb' : b = (ρ₁ * ρ₂)⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination -h₀)
  have ha : a = b * (ρ₁ + ρ₂) := by linear_combination -h₁
  have hs : (ρ₁ ^ 2)⁻¹ + (ρ₂ ^ 2)⁻¹ = a ^ 2 - 2 * b := by
    rw [ha, hb']
    field_simp
    ring1
  have hp : (ρ₁ ^ 2)⁻¹ * (ρ₂ ^ 2)⁻¹ = b ^ 2 := by
    rw [hb']
    field_simp
  have hc : (C b * X ^ 2 + C (-a) * X + C 1 : ℂ[X]).coeff 0 = 1 := by
    simp
  rw [hh, rootPowers, hc, hρ, ← hs, ← hp]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons,
    Multiset.map_singleton, Multiset.prod_singleton, map_one, map_add, map_mul]
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
