import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.HalfIntegralWeight
import Mathlib.NumberTheory.LSeries.Convolution
import TauCeti.NumberTheory.LSeries.Twist
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# The Shimura correspondence

Let `k` be odd, `λ = (k - 1) / 2`, `N` a positive integer divisible by `4`, `χ` a Dirichlet
character modulo `N` and `t` a squarefree positive integer. The Shimura correspondence (LMFDB
`cmf.shimura_correspondence`) is the linear map `Sh_t` from the cusp forms `S_{k/2}(N, χ)` of
half-integral weight `k/2` to the modular forms of weight `k - 1`, level `N/2` and character `χ²`
defined by the identity of Dirichlet series

`L(s, Sh_t(g)) = L(χ_t, s + 1 - λ) ∑_{n ≥ 1} a_{tn²} n ^ (-s)`

for `g = ∑ aₙ qⁿ`, where `χ_t(m) = χ(m) (-1/m) ^ λ (t/m)`. That the right-hand side is the L-series
of a modular form of weight `k - 1`, level `N/2` and character `χ²`, a cusp form when `k ≥ 5`, is
Shimura's theorem (1973), which is not proved here, and neither is the Hecke linearity of `Sh_t`.
This file defines the relation `F = Sh_t(g)` by the coefficients of `F`: its `n`-th Fourier
coefficient is `∑_{d ∣ n} χ_t(d) d ^ (λ - 1) a_{t(n/d)²}`, the Dirichlet convolution that the
identity expresses. The relation is linear in `g`, and it determines a cusp form `F`.

The knowl writes `χ_t(m) = χ(m) (-1/m) (t/m)`, without the exponent `λ`; that is Shimura's
character only for odd `λ`, and the character `χ(m) ((-1) ^ λ t / m)` of Shimura's theorem is used
here. As in Shimura's theorem `t` is positive: for `t < 0` the coefficients `a_{tn²}` of a
holomorphic form vanish. The definitions accept every natural number `t`, squarefree or not; only
Shimura's theorem needs `t` squarefree. The Fourier coefficients of `g`, which is `1`-periodic
since the multiplier of `(1, 1; 0, 1) ∈ Γ₀(N)` is trivial, are the coefficients of Mathlib's
`q`-expansion `UpperHalfPlane.qExpansion 1 g`. The symbols `(-1/m)` and `(t/m)` are Jacobi symbols,
which are only evaluated at odd `m` since `χ(m) = 0` for even `m`.

## Main definitions

* `ModularForm.shimuraCharacter` (LMFDB `cmf.shimura_correspondence`): the character
  `χ_t(m) = χ(m) (-1/m) ^ λ (t/m)`.
* `ModularForm.shimuraCoeff` (LMFDB `cmf.shimura_correspondence`): the Fourier coefficients of
  `Sh_t(g)` in terms of those of `g`.
* `ModularForm.IsShimuraLift` (LMFDB `cmf.shimura_correspondence`): `F` is the Shimura lift
  `Sh_t(g)` of `g ∈ S_{k/2}(N, χ)`.

## Main results

* `ModularForm.shimuraCoeff_apply`: the `n`-th coefficient of `Sh_t(g)` is
  `∑_{d ∣ n} χ_t(d) d ^ (λ - 1) a_{t(n/d)²}`.
* `ModularForm.LSeries_shimuraCoeff`: the identity
  `L(s, Sh_t(g)) = L(χ_t, s + 1 - λ) ∑ a_{tn²} n ^ (-s)` defining the Shimura correspondence.
* `ModularForm.shimuraCoeff_add`, `ModularForm.shimuraCoeff_smul`: the correspondence is linear.
* `ModularForm.IsShimuraLift.eq`: a cusp form is determined as a Shimura lift.
-/

open UpperHalfPlane TauCeti LSeries

namespace ModularForm

variable {N : ℕ} (χ : DirichletCharacter ℂ N) (k : ℤ) (t : ℕ)

/-- The **character** `χ_t(m) = χ(m) (-1/m) ^ λ (t/m)` (LMFDB `cmf.shimura_correspondence`) of the
Shimura correspondence `Sh_t` on forms of weight `k/2` and character `χ`, where `λ = (k - 1) / 2`
and `(-1/m)`, `(t/m)` are Jacobi symbols. The knowl omits the exponent `λ`, which Shimura's
theorem requires. -/
noncomputable def shimuraCharacter (m : ℕ) : ℂ :=
  χ m * (jacobiSym (-1) m : ℂ) ^ ((k - 1) / 2) * jacobiSym t m

/-- The **Fourier coefficients of the Shimura lift** `Sh_t(g)` (LMFDB `cmf.shimura_correspondence`)
of a form `g = ∑ aₙ qⁿ` of weight `k/2` and character `χ`: the Dirichlet convolution of
`d ↦ χ_t(d) d ^ (λ - 1)` with `m ↦ a_{tm²}`, where `λ = (k - 1) / 2`, so that its L-series is
`L(χ_t, s + 1 - λ) ∑ a_{tm²} m ^ (-s)` (`LSeries_shimuraCoeff`) and its `n`-th term is
`∑_{d ∣ n} χ_t(d) d ^ (λ - 1) a_{t(n/d)²}` (`shimuraCoeff_apply`). -/
noncomputable def shimuraCoeff (a : ℕ → ℂ) : ℕ → ℂ :=
  convolution (fun d ↦ shimuraCharacter χ k t d * (d : ℂ) ^ ((((k - 1) / 2 : ℤ) : ℂ) - 1))
    fun m ↦ a (t * m ^ 2)

/-- A function `F` on `ℍ` is the **Shimura lift** `Sh_t(g)` (LMFDB `cmf.shimura_correspondence`)
of a cusp form `g ∈ S_{k/2}(N, χ)` of half-integral weight if its Fourier coefficients `bₙ`,
`n ≥ 1`, are those of the Dirichlet series `L(χ_t, s + 1 - λ) ∑ a_{tm²} m ^ (-s)`, where `aₙ` are
the Fourier coefficients of `g` and `λ = (k - 1) / 2`, that is,
`L(s, F) = L(χ_t, s + 1 - λ) ∑ a_{tm²} m ^ (-s)`. By Shimura's theorem, which is not proved here,
`g` has a Shimura lift of weight `k - 1`, level `N/2` and character `χ²`, a cusp form if `k ≥ 5`;
a cusp form is determined as a Shimura lift (`IsShimuraLift.eq`). -/
def IsShimuraLift (g : halfIntegralWeightCuspSpace χ k) (F : ℍ → ℂ) : Prop :=
  ∀ n ≠ 0, (qExpansion 1 F).coeff n =
    shimuraCoeff χ k t (fun m ↦ (qExpansion 1 (g : ℍ → ℂ)).coeff m) n

variable {χ k t} {a b : ℕ → ℂ} {n : ℕ}

/-- **The `n`-th Fourier coefficient of the Shimura lift** is
`∑_{d ∣ n} χ_t(d) d ^ (λ - 1) a_{t(n/d)²}`. -/
lemma shimuraCoeff_apply : shimuraCoeff χ k t a n = ∑ d ∈ n.divisors,
    shimuraCharacter χ k t d * (d : ℂ) ^ ((((k - 1) / 2 : ℤ) : ℂ) - 1) * a (t * (n / d) ^ 2) := by
  rw [shimuraCoeff, convolution_def]
  exact Nat.sum_divisorsAntidiagonal fun x y ↦
    shimuraCharacter χ k t x * (x : ℂ) ^ ((((k - 1) / 2 : ℤ) : ℂ) - 1) * a (t * y ^ 2)

/-- **The identity defining the Shimura correspondence**: where both series on the right converge
absolutely, the L-series of the coefficients of `Sh_t(g)` is
`L(χ_t, s + 1 - λ) ∑ a_{tm²} m ^ (-s)`, with `λ = (k - 1) / 2`. -/
lemma LSeries_shimuraCoeff {s : ℂ}
    (h₁ : LSeriesSummable (shimuraCharacter χ k t) (s + 1 - ((k - 1) / 2 : ℤ)))
    (h₂ : LSeriesSummable (fun m ↦ a (t * m ^ 2)) s) : LSeries (shimuraCoeff χ k t a) s =
      LSeries (shimuraCharacter χ k t) (s + 1 - ((k - 1) / 2 : ℤ)) *
          LSeries (fun m ↦ a (t * m ^ 2)) s := by
  have h : (fun d : ℕ ↦ shimuraCharacter χ k t d * (d : ℂ) ^ ((((k - 1) / 2 : ℤ) : ℂ) - 1)) =
      fun d ↦ shimuraCharacter χ k t d * (d : ℂ) ^ (-(1 - (((k - 1) / 2 : ℤ) : ℂ))) := by
    simp_rw [neg_sub]
  have hs : s + 1 - (((k - 1) / 2 : ℤ) : ℂ) = s + (1 - (((k - 1) / 2 : ℤ) : ℂ)) := by
    ring1
  rw [shimuraCoeff, LSeries_convolution' _ h₂, h, LSeries_mul_natCast_cpow_neg, hs]
  rwa [h, LSeriesSummable, funext (term_mul_natCast_cpow_neg _ _ s), ← hs]

/-- **The Shimura correspondence is additive.** -/
lemma shimuraCoeff_add :
    shimuraCoeff χ k t (a + b) = shimuraCoeff χ k t a + shimuraCoeff χ k t b := by
  ext n
  rw [Pi.add_apply, shimuraCoeff_apply, shimuraCoeff_apply, shimuraCoeff_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ ↦ by rw [Pi.add_apply, mul_add]

/-- **The Shimura correspondence commutes with scalars.** -/
lemma shimuraCoeff_smul (c : ℂ) : shimuraCoeff χ k t (c • a) = c • shimuraCoeff χ k t a := by
  ext n
  rw [Pi.smul_apply, shimuraCoeff_apply, shimuraCoeff_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ ↦ by
    rw [Pi.smul_apply, smul_eq_mul]
    ring1

/-- **A cusp form is determined as a Shimura lift**: two cusp forms of the same weight and level
that are Shimura lifts of the same `g` are equal, as their Fourier coefficients agree, the
constant ones being `0`. -/
lemma IsShimuraLift.eq {g : halfIntegralWeightCuspSpace χ k} {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.HasDetOne] (hΓ : 1 ∈ Γ.strictPeriods) {w : ℤ} {F F' : CuspForm Γ w}
    (hF : IsShimuraLift χ k t g F) (hF' : IsShimuraLift χ k t g F') : F = F' :=
  CuspForm.qExpansion_injective one_pos hΓ <| PowerSeries.ext fun n ↦ by
    rcases eq_or_ne n 0 with rfl | hn
    · rw [CuspFormClass.qExpansion_coeff_zero F one_pos hΓ,
        CuspFormClass.qExpansion_coeff_zero F' one_pos hΓ]
    · exact (hF n hn).trans (hF' n hn).symm

end ModularForm
