import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Convergence
import TauCeti.NumberTheory.LSeries.EulerProduct

/-!
# The Selberg class axioms

Selberg's axioms for a Dirichlet series `F(s) = ∑ aₙ n ^ (-s)` are:

1. analyticity: `(s - 1) ^ m F(s)` is an entire function of finite order for some `m ∈ ℕ`;
2. the Ramanujan hypothesis: `aₙ = O(n ^ ε)` for every `ε > 0`;
3. a functional equation: `Λ(s) = γ(s) F(s)` satisfies `Λ(s) = conj (Λ (1 - conj s))` for a
  gamma factor `γ(s) = ε Q ^ s ∏ᵢ Γ(λᵢ s + μᵢ)` with `|ε| = 1`, `Q > 0`, `λᵢ > 0` and
  `re μᵢ ≥ 0`;
4. an Euler product: `a₁ = 1` and `log F(s) = ∑ bₙ n ^ (-s)`, where `bₙ = 0` unless `n` is a
  positive power of a prime and `bₙ = O(n ^ θ)` for some `θ < 1 / 2`.

The Dirichlet series that satisfy them form the Selberg class. Dirichlet series are encoded by
their coefficients `a : ℕ → ℂ`, as for Mathlib's `LSeries` (the value `a 0` plays no role). As a
check of the formalisation, the constant series `1` satisfies all four axioms, so the Selberg class
is not empty, and the Riemann zeta function satisfies the Ramanujan hypothesis, the functional
equation with `γ(s) = π ^ (-s / 2) Γ(s / 2)` and the Euler product axiom with `bₙ = Λ(n) / log n`;
that `(s - 1) ζ(s)` has finite order is not proved here.

## Main definitions

* `LSeries.SelbergAnalyticity`, `LSeries.RamanujanHypothesis`,
  `LSeries.SelbergFunctionalEquation` and `LSeries.SelbergEulerProduct`: the four axioms, with
  the gamma factors `LSeries.SelbergGammaFactor` of the functional equation.
* `LSeries.SelbergAxioms` (LMFDB `lfunction.selberg_class.axioms`): the Selberg axioms.
* `LSeries.selbergClass` (LMFDB `lfunction.selberg_class`): the Selberg class.
* `LSeries.SelbergGammaFactor.zeta`: the gamma factor `π ^ (-s / 2) Γ(s / 2)` of the Riemann zeta
  function.

## Main results

* `LSeries.RamanujanHypothesis.LSeriesSummable`: under the Ramanujan hypothesis, the Dirichlet
  series converges absolutely for `re s > 1`.
* `LSeries.ramanujanHypothesis_one`, `LSeries.selbergFunctionalEquation_one` and
  `LSeries.selbergEulerProduct_one`: the Riemann zeta function satisfies the Ramanujan hypothesis,
  Selberg's functional equation and Selberg's Euler product axiom.
* `LSeries.delta_mem_selbergClass`: the constant series `1` is in the Selberg class.
-/

open ArithmeticFunction Asymptotics Complex Filter TauCeti.LSeries
open scoped ComplexConjugate Real

namespace LSeries

/-- The data `(ε, Q, (λᵢ, μᵢ)ᵢ)` of a **gamma factor** `γ(s) = ε Q ^ s ∏ᵢ Γ(λᵢ s + μᵢ)` in the
functional equation of the Selberg class (LMFDB `lfunction.selberg_class.axioms`), with `|ε| = 1`,
`Q > 0`, `λᵢ > 0` and `re μᵢ ≥ 0`. The finite family of pairs `(λᵢ, μᵢ)` is a multiset, as the
order of the factors does not matter. -/
structure SelbergGammaFactor where
  /-- The constant `ε`, of absolute value `1`. -/
  ε : ℂ
  /-- The positive real `Q`. -/
  Q : ℝ
  /-- The pairs `(λᵢ, μᵢ)` of the factors `Γ(λᵢ s + μᵢ)`. -/
  factors : Multiset (ℝ × ℂ)
  norm_ε : ‖ε‖ = 1
  Q_pos : 0 < Q
  fst_pos_of_mem_factors : ∀ x ∈ factors, 0 < x.1
  re_snd_nonneg_of_mem_factors : ∀ x ∈ factors, 0 ≤ x.2.re

variable (γ : SelbergGammaFactor) (a : ℕ → ℂ) {s : ℂ}

variable (s) in
/-- The gamma factor `γ(s) = ε Q ^ s ∏ᵢ Γ(λᵢ s + μᵢ)` of the functional equation of the Selberg
class (LMFDB `lfunction.selberg_class.axioms`). -/
noncomputable def SelbergGammaFactor.toFun : ℂ :=
  γ.ε * (γ.Q : ℂ) ^ s * (γ.factors.map fun x ↦ Gamma (x.1 * s + x.2)).prod

/-- Selberg's **analyticity** axiom (LMFDB `lfunction.selberg_class.axioms`) for the Dirichlet
series `F(s) = ∑ aₙ n ^ (-s)`: for some `m ∈ ℕ`, `(s - 1) ^ m F(s)` is an entire function `G` of
finite order, that is `|G(z)| ≤ C exp (|z| ^ ρ)` for some `C` and `ρ` and all large `|z|`. Here
`F(s)` is the sum of the series for `re s > 1`, where it converges absolutely under the Ramanujan
hypothesis (`RamanujanHypothesis.LSeriesSummable`); `G` is its continuation multiplied by
`(s - 1) ^ m`. Mathlib has no order of growth of entire functions, so the bound is written out. -/
def SelbergAnalyticity : Prop :=
  ∃ m : ℕ, ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
    (∃ ρ : ℝ, G =O[cocompact ℂ] fun z ↦ Real.exp (‖z‖ ^ ρ)) ∧ ∀ s : ℂ, 1 < s.re → G s =
    (s - 1) ^ m * LSeries a s

/-- The **Ramanujan hypothesis** (LMFDB `lfunction.selberg_class.axioms`) of the Selberg class for
the Dirichlet series `∑ aₙ n ^ (-s)`: `aₙ = O(n ^ ε)` for every `ε > 0`. -/
def RamanujanHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε → a =O[atTop] fun n ↦ (n : ℝ) ^ ε

/-- Selberg's **functional equation** axiom (LMFDB `lfunction.selberg_class.axioms`,
`lfunction.functional_equation`) for the Dirichlet series `F(s) = ∑ aₙ n ^ (-s)`: there is a gamma
factor `γ(s) = ε Q ^ s ∏ᵢ Γ(λᵢ s + μᵢ)` such that `Λ(s) = γ(s) F(s)` satisfies
`Λ(s) = conj (Λ (1 - conj s))`, where `F` is the continuation of the series from `re s > 1` to
`ℂ ∖ {1}`. The identity is required on the strip `0 < re s < 1`, where `Λ(s)` and
`conj (Λ (1 - conj s))` are holomorphic; by analytic continuation it then holds wherever both sides
are holomorphic, which is the identity of meromorphic functions on `ℂ` when `F` is meromorphic at
`1` (as the analyticity axiom ensures), and it avoids the junk values at the poles of the gamma
factor. -/
def SelbergFunctionalEquation : Prop :=
  ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {1}ᶜ ∧ (∀ s : ℂ, 1 < s.re → F s = LSeries a s) ∧
    ∃ γ : SelbergGammaFactor, ∀ s : ℂ, 0 < s.re → s.re < 1 → γ.toFun s * F s =
    conj (γ.toFun (1 - conj s) * F (1 - conj s))

/-- Selberg's **Euler product** axiom (LMFDB `lfunction.selberg_class.axioms`,
`lfunction.euler_product`) for the Dirichlet series `F(s) = ∑ aₙ n ^ (-s)`: `a₁ = 1` and
`log F(s) = ∑ bₙ n ^ (-s)`, where `bₙ = 0` unless `n` is a positive power of a prime and
`bₙ = O(n ^ θ)` for some `θ < 1 / 2`. The logarithm is understood as `F(s) = exp (∑ bₙ n ^ (-s))`
with the series converging absolutely, for `re s > 1`; given the other axioms this is the same as
asking it on some right half-plane, since then `b_p = a_p`. -/
def SelbergEulerProduct : Prop :=
  a 1 = 1 ∧ ∃ b : ℕ → ℂ, (∀ n, ¬IsPrimePow n → b n = 0) ∧
    (∃ θ : ℝ, θ < 1 / 2 ∧ b =O[atTop] fun n ↦ (n : ℝ) ^ θ) ∧
    ∀ s : ℂ, 1 < s.re → LSeriesSummable b s ∧ exp (LSeries b s) = LSeries a s

/-- The **Selberg axioms** (LMFDB `lfunction.selberg_class.axioms`) for the Dirichlet series
`F(s) = ∑ aₙ n ^ (-s)`: analyticity, the Ramanujan hypothesis, a functional equation and an Euler
product. -/
structure SelbergAxioms : Prop where
  selbergAnalyticity : SelbergAnalyticity a
  ramanujanHypothesis : RamanujanHypothesis a
  selbergFunctionalEquation : SelbergFunctionalEquation a
  selbergEulerProduct : SelbergEulerProduct a

/-- The **Selberg class** (LMFDB `lfunction.selberg_class`): the Dirichlet series, encoded by their
coefficients, that satisfy the Selberg axioms. -/
def selbergClass : Set (ℕ → ℂ) :=
  {a | SelbergAxioms a}

variable {a}

/-- Under the Ramanujan hypothesis, the Dirichlet series converges absolutely for `re s > 1`. -/
lemma RamanujanHypothesis.LSeriesSummable (h : RamanujanHypothesis a) (hs : 1 < s.re) :
    LSeriesSummable a s :=
  LSeriesSummable_of_isBigO_rpow (x := (1 + s.re) / 2) (by linarith) (h _ (by linarith))

lemma RamanujanHypothesis.abscissaOfAbsConv_le_one (h : RamanujanHypothesis a) :
    abscissaOfAbsConv a ≤ 1 :=
  abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun _ hy ↦ h.LSeriesSummable <| by simpa

/-- The Riemann zeta function `∑ n ^ (-s)` satisfies the Ramanujan hypothesis. -/
lemma ramanujanHypothesis_one : RamanujanHypothesis 1 := by
  refine fun ε hε ↦ IsBigO.of_bound 1 <| eventually_atTop.mpr ⟨1, fun n hn ↦ ?_⟩
  rw [Pi.one_apply, norm_one, one_mul, Real.norm_of_nonneg (by positivity)]
  exact Real.one_le_rpow (by exact_mod_cast hn) hε.le

/-- The gamma factor `π ^ (-s / 2) Γ(s / 2)` of the Riemann zeta function. -/
noncomputable def SelbergGammaFactor.zeta : SelbergGammaFactor where
  ε := 1
  Q := π ^ (-1 / 2 : ℝ)
  factors := {(1 / 2, 0)}
  norm_ε := norm_one
  Q_pos := by positivity
  fst_pos_of_mem_factors x hx := by
    rw [Multiset.mem_singleton.mp hx]
    norm_num
  re_snd_nonneg_of_mem_factors x hx := by
    rw [Multiset.mem_singleton.mp hx]
    norm_num

lemma SelbergGammaFactor.zeta_toFun : SelbergGammaFactor.zeta.toFun s = Gammaℝ s := by
  simp only [toFun, zeta, Multiset.map_singleton, Multiset.prod_singleton, one_mul,
    ← cpow_mul_ofReal_nonneg Real.pi_pos.le]
  congr 2 <;> push_cast <;> ring1

/-- The Riemann zeta function satisfies Selberg's functional equation, with the gamma factor
`π ^ (-s / 2) Γ(s / 2)`. -/
lemma selbergFunctionalEquation_one : SelbergFunctionalEquation 1 := by
  refine ⟨riemannZeta, fun s hs ↦ (differentiableAt_riemannZeta hs).differentiableWithinAt,
    fun s hs ↦ (LSeries_one_eq_riemannZeta hs).symm, .zeta, fun s hs₀ hs₁ ↦ ?_⟩
  have h (z : ℂ) (hz : 0 < z.re) :
      SelbergGammaFactor.zeta.toFun z * riemannZeta z = completedRiemannZeta z := by
    rw [SelbergGammaFactor.zeta_toFun, riemannZeta_def_of_ne_zero (by rintro rfl; simp at hz),
      mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hz)]
  rw [h s hs₀, h (1 - conj s) (by simpa using hs₁), completedRiemannZeta_one_sub,
    completedRiemannZeta_conj, conj_conj]

/-- The Riemann zeta function satisfies Selberg's Euler product axiom:
`log ζ(s) = ∑ Λ(n) / log n n ^ (-s)`, where `Λ(n) / log n` is `1 / k` at `n = p ^ k`. -/
lemma selbergEulerProduct_one : SelbergEulerProduct 1 := by
  have hb (n : ℕ) : ‖((Λ n / Real.log n : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_real, Real.norm_of_nonneg (div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n))]
    exact div_le_one_of_le₀ vonMangoldt_le_log (Real.log_natCast_nonneg n)
  refine ⟨rfl, fun n ↦ ((Λ n / Real.log n : ℝ) : ℂ),
    fun n hn ↦ by simp [vonMangoldt_eq_zero_iff.mpr hn],
    ⟨0, by norm_num, IsBigO.of_bound 1 <| eventually_atTop.mpr ⟨1, fun n _ ↦ by simpa using hb n⟩⟩,
    fun s hs ↦ ?_⟩
  have hsum : LSeriesSummable (fun n ↦ ((Λ n / Real.log n : ℝ) : ℂ)) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ ↦ hb n) hs
  refine ⟨hsum, ?_⟩
  rw [LSeries_one_eq_riemannZeta hs, ← riemannZeta_eulerProduct_exp_log hs, LSeries,
    tsum_eq_tsum_primes_of_support_subset_prime_powers hsum fun n hn ↦ ?_]
  · congr 1
    refine tsum_congr fun p ↦ ?_
    have hz : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_natCast_cpow_of_pos p.prop.pos, neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
    have h :
        HasSum (fun k : ℕ ↦ ((p : ℂ) ^ (-s)) ^ (k + 1) / (k + 1 : ℕ)) (-log (1 - p ^ (-s))) := by
      simpa using (hasSum_nat_add_iff' 1).mpr (hasSum_taylorSeries_neg_log hz)
    rw [← h.tsum_eq]
    refine tsum_congr fun k ↦ ?_
    rw [term_pow _ p.prop.ne_zero, vonMangoldt_apply_pow k.succ_ne_zero,
      vonMangoldt_apply_prime p.prop, Nat.cast_pow, Real.log_pow,
      div_mul_cancel_right₀ (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne']
    push_cast
    ring1
  · by_contra h
    refine hn ?_
    rcases eq_or_ne n 0 with rfl | h₀
    · exact term_zero ..
    · simp [term_of_ne_zero h₀, vonMangoldt_eq_zero_iff.mpr h]

/-- The constant Dirichlet series `1 = ∑ δₙ n ^ (-s)`, where `δ₁ = 1` and `δₙ = 0` for `n ≠ 1`,
satisfies the Selberg axioms, with `m = 0`, the gamma factor `γ(s) = 1` and `bₙ = 0`: the Selberg
class is not empty. -/
lemma delta_mem_selbergClass : delta ∈ selbergClass where
  selbergAnalyticity := ⟨0, 1, differentiable_const 1,
    ⟨0, IsBigO.of_bound 1 <| Eventually.of_forall fun z ↦ by simp⟩,
    fun s _ ↦ by simp [LSeries_delta]⟩
  ramanujanHypothesis _ _ := IsBigO.of_bound 0 <| eventually_atTop.mpr ⟨2, fun n hn ↦ by
    simp [delta, (one_lt_two.trans_le hn).ne']⟩
  selbergFunctionalEquation := ⟨1, differentiableOn_const 1,
    fun s _ ↦ congrFun LSeries_delta.symm s, ⟨1, 1, 0, norm_one, one_pos, by simp, by simp⟩,
    fun s _ _ ↦ by simp [SelbergGammaFactor.toFun]⟩
  selbergEulerProduct := ⟨rfl, 0, fun _ _ ↦ rfl, ⟨0, by norm_num, isBigO_zero _ _⟩,
    fun s _ ↦ ⟨LSeriesSummable_zero, by simp [LSeries_delta]⟩⟩

end LSeries
