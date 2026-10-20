import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.PowerSeries.Basic
import TauCeti.NumberTheory.LSeries.Twist

/-!
# Analytic L-functions

An analytic L-function in the sense of the LMFDB is a Dirichlet series `L(s) = ∑ aₙ n ^ (-s)`
with an Euler product and a functional equation of the form

`Λ(s) = N ^ (s / 2) ∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ) L(s) = ε conj (Λ (1 - conj s))`.

It is stored in its analytic normalisation, whose central point is `s = 1 / 2`. The degree
`J + 2 K`, the conductor `N`, the spectral parameters `μⱼ` and `νₖ` and the sign `ε` form the
Selberg data of the L-function.

## Main definitions

* `AnalyticLFunction.SelbergData` (LMFDB `lfunction.selbergdata`): the data of a functional
  equation, with its degree `AnalyticLFunction.SelbergData.degree` (LMFDB `lfunction.degree`) and
  its gamma factor `AnalyticLFunction.SelbergData.gammaFactor` (LMFDB `lfunction.infinity_factor`).
* `AnalyticLFunction` (LMFDB `lfunction`, `lfunction.functional_equation`): an analytic
  L-function, with its Dirichlet coefficients, its continuation, its completion
  `AnalyticLFunction.completed` (LMFDB `lfunction.completed`) and its Selberg data.
* `AnalyticLFunction.degree`, `AnalyticLFunction.conductor` and `AnalyticLFunction.sign` (LMFDB
  `lfunction.degree`, `lfunction.conductor`, `lfunction.sign`): the degree, the conductor and the
  sign `ε` of an analytic L-function.
* `AnalyticLFunction.arithmeticNormalization` (LMFDB `lfunction.normalization`): the L-function
  `L(s - w / 2)` in its arithmetic normalisation of weight `w`, the Dirichlet series with the
  coefficients `AnalyticLFunction.arithmeticCoeff`.
* `AnalyticLFunction.motivicWeight` (LMFDB `lfunction.motivic_weight`).

## Main results

* `AnalyticLFunction.norm_sign`: the sign has absolute value `1`.
* `AnalyticLFunction.eqOn_toFun_of_coeff_eq`: the continuation is determined by the Dirichlet
  coefficients.
* `AnalyticLFunction.arithmeticNormalization_eq_LSeries`: the arithmetic normalisation of weight
  `w` is the Dirichlet series with the coefficients `aₙ n ^ (w / 2)`.
* `AnalyticLFunction.completed_sub_eq_sign_mul_conj`: the functional equation in the arithmetic
  normalisation of weight `w`, which relates `s` and `1 + w - s`.
-/

open Complex Filter Set TauCeti.LSeries
open scoped ComplexConjugate Polynomial Topology

/-- The **Selberg data** (LMFDB `lfunction.selbergdata`) of a functional equation
`Λ(s) = N ^ (s / 2) ∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ) L(s) = ε conj (Λ (1 - conj s))`: the
**conductor** `N` (LMFDB `lfunction.conductor`), the **spectral parameters** `μⱼ` of the factors
`Γ_ℝ` and `νₖ` of the factors `Γ_ℂ` (LMFDB `lfunction.spectral_parameters`), and the **sign** `ε`
(LMFDB `lfunction.sign`). The degree, the first entry of the LMFDB's quadruple, is
`AnalyticLFunction.SelbergData.degree`. As in the LMFDB, the spectral parameters are normalised
so that each `re μⱼ` is `0` or `1` (assuming Selberg's eigenvalue conjecture), each `re νₖ` is a
positive integer or half-integer, and `∑ μⱼ + 2 ∑ νₖ` is real; the LMFDB states that this makes
the data of a functional equation unique, which is not proved here. -/
structure AnalyticLFunction.SelbergData where
  /-- The conductor `N`. -/
  conductor : ℕ
  /-- The spectral parameters `μⱼ` of the factors `Γ_ℝ(s + μⱼ)`. -/
  μ : Multiset ℂ
  /-- The spectral parameters `νₖ` of the factors `Γ_ℂ(s + νₖ)`. -/
  ν : Multiset ℂ
  /-- The sign `ε`. -/
  sign : ℂ
  conductor_pos : 0 < conductor
  re_eq_zero_or_one_of_mem_μ : ∀ x ∈ μ, x.re = 0 ∨ x.re = 1
  exists_two_mul_re_eq_of_mem_ν : ∀ x ∈ ν, ∃ k : ℕ, 0 < k ∧ 2 * x.re = k
  im_sum_add_two_mul_sum : (μ.sum + 2 * ν.sum).im = 0

namespace AnalyticLFunction.SelbergData

variable (D : SelbergData) {s : ℂ}

/-- The **degree** `J + 2 K` (LMFDB `lfunction.degree`) of a functional equation with `J` factors
`Γ_ℝ` and `K` factors `Γ_ℂ`. -/
def degree : ℕ :=
  D.μ.card + 2 * D.ν.card

variable (s) in
/-- The **gamma factor** `∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ)` (LMFDB `lfunction.infinity_factor`) of a
functional equation, the product of its shifted Deligne gamma factors `Γ_ℝ` and `Γ_ℂ` (LMFDB
`lfunction.gamma_factor`). -/
noncomputable def gammaFactor : ℂ :=
  (D.μ.map fun x ↦ Gammaℝ (s + x)).prod * (D.ν.map fun x ↦ Gammaℂ (s + x)).prod

lemma gammaFactor_ne_zero (hs : 0 < s.re) : D.gammaFactor s ≠ 0 := by
  refine mul_ne_zero (Multiset.prod_ne_zero fun h ↦ ?_) (Multiset.prod_ne_zero fun h ↦ ?_)
  · rcases Multiset.mem_map.mp h with ⟨x, hx, h⟩
    refine Gammaℝ_ne_zero_of_re_pos ?_ h
    rcases D.re_eq_zero_or_one_of_mem_μ x hx with h | h <;> simp [h, hs, add_pos]
  · rcases Multiset.mem_map.mp h with ⟨x, hx, h⟩
    rcases D.exists_two_mul_re_eq_of_mem_ν x hx with ⟨k, hk, hx⟩
    have hre : 0 < (s + x).re := by
      rw [add_re]
      linarith [(Nat.cast_pos.mpr hk : (0 : ℝ) < k)]
    have hre₁ : 0 < (s + x + 1).re := by
      rw [add_re, one_re]
      linarith
    rw [← Gammaℝ_mul_Gammaℝ_add_one] at h
    exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos hre) (Gammaℝ_ne_zero_of_re_pos hre₁) h

end AnalyticLFunction.SelbergData

/-- An **analytic L-function** (LMFDB `lfunction`), in its analytic normalisation: a Dirichlet
series `L(s) = ∑ aₙ n ^ (-s)` that converges absolutely for `re s > 1`, has an Euler product and
satisfies a **functional equation** (LMFDB `lfunction.functional_equation`) of the form

`Λ(s) = N ^ (s / 2) ∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ) L(s) = ε conj (Λ (1 - conj s))`

with Selberg data `(N, μ, ν, ε)` and degree `d = J + 2 K`. The structure records the coefficients
`aₙ`, the continuation `L(s)` of the series, which is holomorphic on `ℂ` except for at most a pole
at `s = 1`, and the completed L-function `Λ(s)`, which is holomorphic except at `s = 0` and
`s = 1`, the only possible poles of a completed L-function (they come from factors `ζ(s)`). The
completion equals `N ^ (s / 2) ∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ) L(s)` for `re s > 1`, hence as a
meromorphic function by analytic continuation, and the functional equation is stated pointwise
for `s ≠ 0, 1`, where no junk values intervene.

The Euler product is encoded by the multiplicativity of the coefficients, with `a₁ = 1`, and by
local factors `∑ₖ a_{pᵏ} Tᵏ = 1 / Fₚ(T)` for polynomials `Fₚ` of degree at most `d`, with equality
exactly for the primes `p ∤ N` (LMFDB `lfunction.euler_product`, without the Ramanujan bounds
`|αᵢ(p)| = 1` and `|βᵢ(p)| ≤ 1`, which are not known in general). -/
structure AnalyticLFunction where
  /-- The Dirichlet coefficients `aₙ`, in the analytic normalisation. -/
  coeff : ℕ → ℂ
  /-- The analytic continuation `L(s)` of the Dirichlet series. -/
  toFun : ℂ → ℂ
  /-- The completed L-function `Λ(s)` (LMFDB `lfunction.completed`). -/
  completed : ℂ → ℂ
  /-- The Selberg data of the functional equation. -/
  selbergData : AnalyticLFunction.SelbergData
  coeff_one : coeff 1 = 1
  coeff_mul_of_coprime {m n : ℕ} : m.Coprime n → coeff (m * n) = coeff m * coeff n
  exists_eulerFactor (p : ℕ) : p.Prime → ∃ F : ℂ[X], F.natDegree ≤ selbergData.degree ∧
    (F.natDegree = selbergData.degree ↔ ¬p ∣ selbergData.conductor) ∧ (F : PowerSeries ℂ) *
    PowerSeries.mk (fun k ↦ coeff (p ^ k)) = 1
  LSeriesSummable_coeff {s : ℂ} : 1 < s.re → LSeriesSummable coeff s
  toFun_eq_LSeries {s : ℂ} : 1 < s.re → toFun s = LSeries coeff s
  differentiableOn_toFun : DifferentiableOn ℂ toFun {1}ᶜ
  meromorphicAt_toFun : MeromorphicAt toFun 1
  completed_eq {s : ℂ} : 1 < s.re → completed s = (selbergData.conductor : ℂ) ^ (s / 2) *
    selbergData.gammaFactor s * toFun s
  differentiableOn_completed : DifferentiableOn ℂ completed {0, 1}ᶜ
  completed_eq_sign_mul_conj {s : ℂ} :
    s ≠ 0 → s ≠ 1 → completed s = selbergData.sign * conj (completed (1 - conj s))

namespace AnalyticLFunction

variable (L : AnalyticLFunction) {L' : AnalyticLFunction} (w : ℕ) {s : ℂ} {n : ℕ}

/-- The **degree** (LMFDB `lfunction.degree`) of an analytic L-function. -/
def degree : ℕ :=
  L.selbergData.degree

/-- The **conductor** (LMFDB `lfunction.conductor`) of an analytic L-function. -/
def conductor : ℕ :=
  L.selbergData.conductor

/-- The **sign** `ε` (LMFDB `lfunction.sign`, `lfunction.root_number`) of the functional equation
`Λ(s) = ε conj (Λ (1 - conj s))` of an analytic L-function, also called its root number. -/
def sign : ℂ :=
  L.selbergData.sign

lemma analyticOnNhd_toFun : AnalyticOnNhd ℂ L.toFun {1}ᶜ :=
  L.differentiableOn_toFun.analyticOnNhd isOpen_compl_singleton

lemma tendsto_toFun_atTop : Tendsto (fun x : ℝ ↦ L.toFun x) atTop (𝓝 1) := by
  have h : LSeries.abscissaOfAbsConv L.coeff < ⊤ :=
    (L.LSeriesSummable_coeff (s := 2) (by simp)).abscissaOfAbsConv_le.trans_lt (by simp)
  refine (L.coeff_one ▸ LSeries.tendsto_atTop h).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  exact (L.toFun_eq_LSeries (by simpa using hx)).symm

lemma exists_toFun_ne_zero : ∃ x : ℝ, 1 < x ∧ L.toFun x ≠ 0 :=
  ((eventually_gt_atTop 1).and (L.tendsto_toFun_atTop.eventually_ne one_ne_zero)).exists

lemma exists_completed_ne_zero : ∃ x : ℝ, 1 < x ∧ L.completed x ≠ 0 := by
  rcases L.exists_toFun_ne_zero with ⟨x, hx₁, hx⟩
  refine ⟨x, hx₁, ?_⟩
  rw [L.completed_eq (by simpa using hx₁)]
  exact mul_ne_zero (mul_ne_zero (by simp [L.selbergData.conductor_pos.ne'])
    (L.selbergData.gammaFactor_ne_zero (by simpa using zero_lt_one.trans hx₁))) hx

/-- The sign of the functional equation of an analytic L-function has absolute value `1`. -/
lemma norm_sign : ‖L.sign‖ = 1 := by
  rcases L.exists_completed_ne_zero with ⟨x, hx, hΛ⟩
  have hx₀ : (x : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'
  have hx₁ : (x : ℂ) ≠ 1 :=
    ofReal_ne_one.mpr hx.ne'
  have h₁ : L.completed x = L.sign * conj (L.completed (1 - x)) := by
    rw [L.completed_eq_sign_mul_conj hx₀ hx₁, conj_ofReal, sign]
  have h₂ : L.completed (1 - x) = L.sign * conj (L.completed x) := by
    rw [L.completed_eq_sign_mul_conj (sub_ne_zero.mpr hx₁.symm) (by simpa using hx₀), map_sub,
      map_one, conj_ofReal, sub_sub_cancel, sign]
  rw [h₂, map_mul, conj_conj, ← mul_assoc, mul_conj', ← ofReal_pow] at h₁
  have h : ((‖L.sign‖ ^ 2 : ℝ) : ℂ) = 1 :=
    (mul_eq_right₀ hΛ).mp h₁.symm
  rw [← ofReal_one, ofReal_inj] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

/-- The continuation of an analytic L-function is determined by its Dirichlet coefficients. -/
lemma eqOn_toFun_of_coeff_eq (h : ∀ n ≠ 0, L.coeff n = L'.coeff n) :
    EqOn L.toFun L'.toFun {1}ᶜ := by
  refine L.analyticOnNhd_toFun.eqOn_of_preconnected_of_eventuallyEq L'.analyticOnNhd_toFun
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ)) ?_
  filter_upwards [(continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
    (by norm_num : (2 : ℂ) ∈ re ⁻¹' Ioi 1)] with z hz
  rw [L.toFun_eq_LSeries hz, L'.toFun_eq_LSeries hz, LSeries_congr (fun hn ↦ h _ hn)]

variable (s) in
/-- The L-function `s ↦ L(s - w / 2)` in its **arithmetic normalisation** of weight `w` (LMFDB
`lfunction.normalization`), whose central point is `(w + 1) / 2` and whose functional equation
relates `s` and `1 + w - s`. Conversely, `L` is the **analytic normalisation**
`L(s) = L_arith(s + w / 2)` of it. -/
noncomputable def arithmeticNormalization : ℂ :=
  L.toFun (s - w / 2)

variable (n) in
/-- The Dirichlet coefficients `aₙ n ^ (w / 2)` of the arithmetic normalisation of weight `w` of an
analytic L-function with Dirichlet coefficients `aₙ`. -/
noncomputable def arithmeticCoeff : ℂ :=
  L.coeff n * (n : ℂ) ^ ((w : ℂ) / 2)

lemma arithmeticNormalization_def : L.arithmeticNormalization w = fun s ↦ L.toFun (s - w / 2) :=
  rfl

variable (s) in
lemma arithmeticNormalization_add : L.arithmeticNormalization w (s + w / 2) = L.toFun s := by
  simp [arithmeticNormalization]

/-- The arithmetic normalisation of weight `w` is the Dirichlet series with the coefficients
`aₙ n ^ (w / 2)` for `re s > 1 + w / 2`. -/
lemma arithmeticNormalization_eq_LSeries (hs : 1 + (w : ℝ) / 2 < s.re) :
    L.arithmeticNormalization w s = LSeries (L.arithmeticCoeff w) s := by
  have hs' : 1 < (s - w / 2).re := by
    simp
    linarith
  rw [arithmeticNormalization, L.toFun_eq_LSeries hs', sub_eq_add_neg,
    ← LSeries_mul_natCast_cpow_neg, neg_neg]
  rfl

/-- The functional equation in the arithmetic normalisation of weight `w` relates `s` and
`1 + w - s`: the completion `Λ(s - w / 2)` equals `ε conj (Λ ((1 + w - conj s) - w / 2))`. -/
lemma completed_sub_eq_sign_mul_conj (hs₀ : s ≠ w / 2) (hs₁ : s ≠ 1 + w / 2) :
    L.completed (s - w / 2) = L.sign * conj (L.completed (1 + w - conj s - w / 2)) := by
  rw [L.completed_eq_sign_mul_conj (sub_ne_zero.mpr hs₀) (by grind)]
  congr 3
  simp only [map_sub, map_div₀, map_natCast, map_ofNat]
  ring1

/-- The **motivic weight** (LMFDB `lfunction.motivic_weight`) of an arithmetic L-function: the
least `w` such that every coefficient `aₙ n ^ (w / 2)` with `n ≥ 1` is an algebraic integer. When
there is no such `w` it takes the junk value `0`. -/
noncomputable def motivicWeight : ℕ :=
  sInf {w | ∀ n ≠ 0, IsIntegral ℤ (L.arithmeticCoeff w n)}

lemma isIntegral_arithmeticCoeff_motivicWeight
    (h : ∃ w, ∀ n ≠ 0, IsIntegral ℤ (L.arithmeticCoeff w n)) (hn : n ≠ 0) :
    IsIntegral ℤ (L.arithmeticCoeff L.motivicWeight n) :=
  Nat.sInf_mem (s := {w | ∀ n ≠ 0, IsIntegral ℤ (L.arithmeticCoeff w n)}) h n hn

end AnalyticLFunction
