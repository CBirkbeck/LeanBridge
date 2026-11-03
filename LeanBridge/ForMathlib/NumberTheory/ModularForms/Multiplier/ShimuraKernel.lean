import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.JacobiThetaMultiplier
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Niwa's theta kernel for the Shimura correspondence

For `z = x + i y`, `w = u + i v` in the upper half plane, integers `C`, `μ` and `s ∈ ℂ`, let
`τ = C z + μ` and

`S_s(z, w; C, μ) = (v / 2) exp(-(π v² / 4 y) τ τ̄ - (i s v² / 4 y) τ̄ + s² v² / (16 π y))
  ∑_b e((b + C u / 2)² z + μ u (b + C u / 4)) exp(i s v (b + C u / 2))`,

which is a Gaussian times Jacobi's theta function `ϑ(z, τ u + s v / (2π))`. This is the mixed model
of the theta kernel of the ternary form `b² - 4 a c` of signature `(2, 1)` (Niwa, 1975): the pair
`(C, μ)` is permuted by `Γ₀(4)`, acting on `z`, and only the unary part `b` carries the theta
multiplier. Precisely, for `γ = (a, b; c, d) ∈ Γ₀(4)`,

`S_s(γ z, w; C, μ) = j(γ, z) S_{s (c z + d)}(z, w; (C, μ) γ)`.

The kernel of weight `k / 2`, `k = 2 l + 1`, is the coefficient of `s ^ l`, so the law above gives
it the factor `j(γ, z) (c z + d) ^ l`. Each term of the kernel is a Gaussian in `s`, and its
coefficients are `ModularForm.gaussCoeff`: `exp(α s + β s²) = ∑_l gaussCoeff l α β s ^ l`.

## Main definitions

* `ModularForm.gaussCoeff`: the coefficients of `exp(α s + β s²)`.
* `ModularForm.shimuraKernelGen`: the generating kernel `S_s(z, w; C, μ)`.

## Main results

* `ModularForm.hasSum_gaussCoeff_mul_pow`: the generating function of `gaussCoeff`.
* `ModularForm.norm_gaussCoeff_mul_pow_le`: the bound of `gaussCoeff` by its generating function.
* `ModularForm.tsum_exp_neg_mul_add_sq_le`: the bound of a shifted Gaussian sum, uniform in the
  shift.
* `ModularForm.shimuraKernelGen_smul`: the law of the kernel under `Γ₀(4)` in `z`.
* `ModularForm.norm_shimuraKernelTerm_mul_pow_le`: the bound of the terms of the kernel by a
  majorant, uniform in `l`.
* `ModularForm.shimuraKernelCoeff_smul`: the law under `Γ₀(4)` in `z` of the kernel of weight
  `l + 1/2`.

## References

* S. Niwa, *Modular forms of half integral weight and the integral of certain theta-functions*,
  Nagoya Math. J. 56 (1975), 147–161.
* B. A. Cipra, *On the Niwa–Shintani theta-kernel lifting of modular forms*, Nagoya Math. J. 91
  (1983), 49–117.
-/

open Complex CongruenceSubgroup Filter ModularGroup Topology

open scoped Real MatrixGroups Manifold ComplexConjugate Nat

open UpperHalfPlane hiding I I_re I_im

namespace ModularForm

section GaussCoeff

variable (l : ℕ) (α β s : ℂ)

/-- The coefficient of `s ^ l` in `exp(α s + β s²)`:
`∑_{2 j ≤ l} α ^ (l - 2 j) / (l - 2 j)! · β ^ j / j!`, which is a Hermite polynomial up to
normalisation. -/
noncomputable def gaussCoeff : ℂ :=
  ∑ j ∈ Finset.range (l / 2 + 1), α ^ (l - 2 * j) / ((l - 2 * j)! : ℂ) * (β ^ j / (j ! : ℂ))

private lemma hasSum_exp_series (x : ℂ) : HasSum (fun n : ℕ ↦ x ^ n / (n ! : ℂ)) (cexp x) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp x

private lemma summable_norm_exp_series (x : ℂ) : Summable fun n : ℕ ↦ ‖x ^ n / (n ! : ℂ)‖ := by
  simpa using Real.summable_pow_div_factorial ‖x‖

/-- The fibre of `(n, j) ↦ n + 2 j` over `l`, as the `j` with `2 j ≤ l`. -/
private def gaussFiberEquiv : {p : ℕ × ℕ // p.1 + 2 * p.2 = l} ≃ Finset.range (l / 2 + 1) where
  toFun p := ⟨p.1.2, Finset.mem_range.mpr (by have h : p.1.1 + 2 * p.1.2 = l := p.2; omega)⟩
  invFun j := ⟨(l - 2 * j, j), by
    have h : (j : ℕ) < l / 2 + 1 := Finset.mem_range.mp j.2
    omega⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    have h : p.1.1 + 2 * p.1.2 = l := p.2
    show l - 2 * p.1.2 = p.1.1
    omega
  right_inv j := rfl

/-- **The generating function of `gaussCoeff`**: `exp(α s + β s²) = ∑_l gaussCoeff l α β s ^ l`. -/
lemma hasSum_gaussCoeff_mul_pow :
    HasSum (fun l ↦ gaussCoeff l α β * s ^ l) (cexp (α * s + β * s ^ 2)) := by
  have hs :
      Summable fun p : ℕ × ℕ ↦ (α * s) ^ p.1 / (p.1 ! : ℂ) * ((β * s ^ 2) ^ p.2 / (p.2 ! : ℂ)) :=
    summable_mul_of_summable_norm (f := fun n : ℕ ↦ (α * s) ^ n / (n ! : ℂ))
      (g := fun n : ℕ ↦ (β * s ^ 2) ^ n / (n ! : ℂ)) (summable_norm_exp_series _)
      (summable_norm_exp_series _)
  have h3 : HasSum (fun p : ℕ × ℕ ↦ (α * s) ^ p.1 / (p.1 ! : ℂ) * ((β * s ^ 2) ^ p.2 / (p.2 ! : ℂ)))
      (cexp (α * s + β * s ^ 2)) := by
    rw [Complex.exp_add]
    exact HasSum.mul (f := fun n : ℕ ↦ (α * s) ^ n / (n ! : ℂ))
      (g := fun n : ℕ ↦ (β * s ^ 2) ^ n / (n ! : ℂ)) (hasSum_exp_series _) (hasSum_exp_series _) hs
  refine ((Equiv.sigmaFiberEquiv fun p : ℕ × ℕ ↦ p.1 + 2 * p.2).hasSum_iff.mpr h3).sigma fun l ↦ ?_
  have h5 : HasSum (fun j : Finset.range (l / 2 + 1) ↦
      α ^ (l - 2 * (j : ℕ)) / ((l - 2 * (j : ℕ))! : ℂ) * (β ^ (j : ℕ) / ((j : ℕ)! : ℂ)) * s ^ l)
        (gaussCoeff l α β * s ^ l) := by
    rw [gaussCoeff, Finset.sum_mul]
    exact Finset.hasSum _ fun j ↦
      α ^ (l - 2 * j) / ((l - 2 * j)! : ℂ) * (β ^ j / (j ! : ℂ)) * s ^ l
  convert (gaussFiberEquiv l).hasSum_iff.mpr h5 using 1
  funext c
  rcases c with ⟨⟨n, j⟩, hc⟩
  have hn : l - 2 * j = n := by
    have : n + 2 * j = l := hc
    omega
  have hl : l = n + 2 * j := hc.symm
  simp only [Equiv.sigmaFiberEquiv, gaussFiberEquiv, Function.comp_apply, Equiv.coe_fn_mk, hn]
  rw [hl]
  ring1

private lemma norm_gaussCoeff_le_re :
    ‖gaussCoeff l α β‖ ≤ (gaussCoeff l (‖α‖ : ℂ) (‖β‖ : ℂ)).re := by
  have h (j : ℕ) : ((‖α‖ : ℂ) ^ (l - 2 * j) / ((l - 2 * j)! : ℂ) * ((‖β‖ : ℂ) ^ j / (j ! : ℂ))).re =
      ‖α ^ (l - 2 * j) / ((l - 2 * j)! : ℂ) * (β ^ j / (j ! : ℂ))‖ := by
    have e : ((‖α‖ : ℂ) ^ (l - 2 * j) / ((l - 2 * j)! : ℂ) * ((‖β‖ : ℂ) ^ j / (j ! : ℂ))) =
        ((‖α‖ ^ (l - 2 * j) / ((l - 2 * j)! : ℝ) * (‖β‖ ^ j / (j ! : ℝ)) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [e, ofReal_re, norm_mul, norm_div, norm_div, norm_pow, norm_pow, norm_natCast, norm_natCast]
  rw [gaussCoeff, gaussCoeff, re_sum]
  simp_rw [h]
  exact norm_sum_le _ _

/-- **The bound of `gaussCoeff` by its generating function**: for `r ≥ 0`,
`|gaussCoeff l α β| r ^ l ≤ exp(|α| r + |β| r²)`. -/
lemma norm_gaussCoeff_mul_pow_le {r : ℝ} (hr : 0 ≤ r) :
    ‖gaussCoeff l α β‖ * r ^ l ≤ Real.exp (‖α‖ * r + ‖β‖ * r ^ 2) := by
  have h1 : HasSum (fun l ↦ gaussCoeff l (‖α‖ : ℂ) (‖β‖ : ℂ) * (r : ℂ) ^ l)
      (cexp ((‖α‖ : ℂ) * r + (‖β‖ : ℂ) * (r : ℂ) ^ 2)) :=
    hasSum_gaussCoeff_mul_pow (‖α‖ : ℂ) (‖β‖ : ℂ) (r : ℂ)
  have h2 : HasSum (fun l ↦ (gaussCoeff l (‖α‖ : ℂ) (‖β‖ : ℂ)).re * r ^ l)
      (Real.exp (‖α‖ * r + ‖β‖ * r ^ 2)) := by
    have e : cexp ((‖α‖ : ℂ) * r + (‖β‖ : ℂ) * (r : ℂ) ^ 2) =
        ((Real.exp (‖α‖ * r + ‖β‖ * r ^ 2) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [e] at h1
    simpa only [ofReal_re, ← ofReal_pow, re_mul_ofReal] using Complex.hasSum_re h1
  refine (mul_le_mul_of_nonneg_right (norm_gaussCoeff_le_re l α β) (pow_nonneg hr l)).trans ?_
  exact le_hasSum h2 l fun j _ ↦ mul_nonneg ((norm_nonneg _).trans (norm_gaussCoeff_le_re j α β))
    (pow_nonneg hr j)

lemma conj_gaussCoeff : conj (gaussCoeff l α β) = gaussCoeff l (conj α) (conj β) := by
  simp only [gaussCoeff, map_sum, map_mul, map_div₀, map_pow, map_natCast]

lemma gaussCoeff_mul_mul_sq : gaussCoeff l (α * s) (β * s ^ 2) = gaussCoeff l α β * s ^ l := by
  rw [gaussCoeff, gaussCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : 2 * j ≤ l := by
    have h : j < l / 2 + 1 := Finset.mem_range.mp hj
    omega
  have e : s ^ l = s ^ (l - 2 * j) * (s ^ 2) ^ j := by
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hj']
  rw [e, mul_pow, mul_pow]
  ring1

end GaussCoeff

section GaussianSum

variable {t : ℝ} (ξ : ℝ)

private lemma exp_nat_le_of_le {x : ℝ} {n : ℕ} (ht : 0 < t) (hx : (n : ℝ) ≤ |x|) :
    Real.exp (-t * x ^ 2) ≤ Real.exp (-t) ^ n := by
  rw [← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases n with _ | n
    · simp
    · exact_mod_cast Nat.le_self_pow two_ne_zero (n + 1)
  have h2 : (n : ℝ) ^ 2 ≤ x ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) hx 2
  nlinarith

private lemma summable_exp_neg_pow (ht : 0 < t) : Summable fun n : ℕ ↦ Real.exp (-t) ^ n :=
  summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht))

private lemma two_mul_inv_one_sub_exp_le (ht : 0 < t) : 2 * (1 - Real.exp (-t))⁻¹ ≤ 2 + 2 / t := by
  have h1 : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  have h2 : Real.exp (-t) ≤ (t + 1)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) h1
  have h3 : t / (t + 1) ≤ 1 - Real.exp (-t) := by
    have e : t / (t + 1) = 1 - (t + 1)⁻¹ := by
      field_simp
      ring1
    linarith
  have h4 : (1 - Real.exp (-t))⁻¹ ≤ (t / (t + 1))⁻¹ := inv_anti₀ (by positivity) h3
  rw [inv_div] at h4
  have e : 2 + 2 / t = 2 * ((t + 1) / t) := by
    field_simp
  rw [e]
  linarith

private lemma abs_natCast_add_fract (n : ℕ) : (n : ℝ) ≤ |(n : ℝ) + Int.fract ξ| :=
  (le_add_of_nonneg_right (Int.fract_nonneg ξ)).trans (le_abs_self _)

private lemma abs_neg_natCast_add_fract (n : ℕ) :
    (n : ℝ) ≤ |((-((n : ℤ) + 1) : ℤ) : ℝ) + Int.fract ξ| := by
  have h1 : Int.fract ξ < 1 := Int.fract_lt_one ξ
  refine le_trans ?_ (neg_le_abs _)
  push_cast
  linarith

private lemma summable_exp_neg_mul_add_fract (ht : 0 < t) :
    Summable fun n : ℤ ↦ Real.exp (-t * ((n : ℝ) + Int.fract ξ) ^ 2) := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine Summable.of_nonneg_of_le (fun n ↦ (Real.exp_pos _).le) (fun n ↦ ?_)
      (summable_exp_neg_pow ht)
    exact exp_nat_le_of_le ht (abs_natCast_add_fract ξ n)
  · refine Summable.of_nonneg_of_le (fun n ↦ (Real.exp_pos _).le) (fun n ↦ ?_)
      (summable_exp_neg_pow ht)
    exact exp_nat_le_of_le ht (abs_neg_natCast_add_fract ξ n)

private lemma comp_add_floor (n : ℤ) : ((n : ℝ) + ξ) = (((n + ⌊ξ⌋ : ℤ) : ℝ) + Int.fract ξ) := by
  have h : ξ = ⌊ξ⌋ + Int.fract ξ := (Int.floor_add_fract ξ).symm
  push_cast
  linarith

lemma summable_exp_neg_mul_add_sq (ht : 0 < t) :
    Summable fun n : ℤ ↦ Real.exp (-t * ((n : ℝ) + ξ) ^ 2) := by
  refine ((Equiv.addRight ⌊ξ⌋).summable_iff.mpr (summable_exp_neg_mul_add_fract ξ ht)).congr
    fun n ↦ ?_
  rw [comp_add_floor ξ n]
  rfl

/-- **The bound of a shifted Gaussian sum, uniform in the shift**:
`∑_n e^{-t (n + ξ)²} ≤ 2 + 2 / t` for `t > 0` and real `ξ`. -/
lemma tsum_exp_neg_mul_add_sq_le (ht : 0 < t) :
    ∑' n : ℤ, Real.exp (-t * ((n : ℝ) + ξ) ^ 2) ≤ 2 + 2 / t := by
  have e : ∑' n : ℤ, Real.exp (-t * ((n : ℝ) + ξ) ^ 2) =
      ∑' n : ℤ, Real.exp (-t * ((n : ℝ) + Int.fract ξ) ^ 2) := by
    rw [← (Equiv.addRight ⌊ξ⌋).tsum_eq fun n : ℤ ↦ Real.exp (-t * ((n : ℝ) + Int.fract ξ) ^ 2)]
    refine tsum_congr fun n ↦ ?_
    rw [comp_add_floor ξ n]
    rfl
  have hG : HasSum (fun n : ℕ ↦ Real.exp (-t) ^ n) (1 - Real.exp (-t))⁻¹ :=
    hasSum_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht))
  have h₁ : Summable fun n : ℕ ↦ Real.exp (-t * (((n : ℤ) : ℝ) + Int.fract ξ) ^ 2) :=
    Summable.of_nonneg_of_le (fun n ↦ (Real.exp_pos _).le)
      (fun n ↦ exp_nat_le_of_le ht (abs_natCast_add_fract ξ n)) hG.summable
  have h₂ : Summable fun n : ℕ ↦ Real.exp (-t * (((-((n : ℤ) + 1) : ℤ) : ℝ) + Int.fract ξ) ^ 2) :=
    Summable.of_nonneg_of_le (fun n ↦ (Real.exp_pos _).le)
      (fun n ↦ exp_nat_le_of_le ht (abs_neg_natCast_add_fract ξ n)) hG.summable
  rw [e, (HasSum.of_nat_of_neg_add_one h₁.hasSum h₂.hasSum).tsum_eq]
  have h3 : ∑' n : ℕ, Real.exp (-t * (((n : ℤ) : ℝ) + Int.fract ξ) ^ 2) ≤ (1 - Real.exp (-t))⁻¹ :=
    hG.tsum_eq ▸ Summable.tsum_le_tsum (fun n ↦ exp_nat_le_of_le ht (abs_natCast_add_fract ξ n)) h₁
      hG.summable
  have h4 : ∑' n : ℕ, Real.exp (-t * (((-((n : ℤ) + 1) : ℤ) : ℝ) + Int.fract ξ) ^ 2) ≤
      (1 - Real.exp (-t))⁻¹ :=
    hG.tsum_eq ▸ Summable.tsum_le_tsum
      (fun n ↦ exp_nat_le_of_le ht (abs_neg_natCast_add_fract ξ n)) h₂ hG.summable
  linarith [two_mul_inv_one_sub_exp_le ht]

variable {t₁ t₂ t₃ : ℝ}

private lemma summable_prod_gauss (ht₂ : 0 < t₂) (ht₃ : 0 < t₃) (ξ₂ : ℝ) (ξ₃ : ℤ → ℝ) : Summable
    fun q : ℤ × ℤ ↦ Real.exp (-t₂ * ((q.1 : ℝ) + ξ₂) ^ 2) *
      Real.exp (-t₃ * ((q.2 : ℝ) + ξ₃ q.1) ^ 2) := by
  refine (summable_prod_of_nonneg fun q ↦ by positivity).mpr ⟨fun m ↦ ?_, ?_⟩
  · exact (summable_exp_neg_mul_add_sq (ξ₃ m) ht₃).mul_left (Real.exp (-t₂ * ((m : ℝ) + ξ₂) ^ 2))
  · refine Summable.of_nonneg_of_le (fun m ↦ tsum_nonneg fun n ↦ by positivity) (fun m ↦ ?_)
      ((summable_exp_neg_mul_add_sq ξ₂ ht₂).mul_right (2 + 2 / t₃))
    dsimp only
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (tsum_exp_neg_mul_add_sq_le (ξ₃ m) ht₃) (Real.exp_pos _).le

private lemma tsum_prod_gauss_le (ht₂ : 0 < t₂) (ht₃ : 0 < t₃) (ξ₂ : ℝ) (ξ₃ : ℤ → ℝ) : ∑' q : ℤ × ℤ,
    Real.exp (-t₂ * ((q.1 : ℝ) + ξ₂) ^ 2) * Real.exp (-t₃ * ((q.2 : ℝ) + ξ₃ q.1) ^ 2) ≤
      (2 + 2 / t₂) * (2 + 2 / t₃) := by
  rw [(summable_prod_gauss ht₂ ht₃ ξ₂ ξ₃).tsum_prod]
  have h1 (m : ℤ) : ∑' n : ℤ, Real.exp (-t₂ * ((m : ℝ) + ξ₂) ^ 2) *
      Real.exp (-t₃ * ((n : ℝ) + ξ₃ m) ^ 2) ≤ Real.exp (-t₂ * ((m : ℝ) + ξ₂) ^ 2) *
        (2 + 2 / t₃) := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (tsum_exp_neg_mul_add_sq_le (ξ₃ m) ht₃) (Real.exp_pos _).le
  have hs : Summable fun m : ℤ ↦ Real.exp (-t₂ * ((m : ℝ) + ξ₂) ^ 2) * (2 + 2 / t₃) :=
    (summable_exp_neg_mul_add_sq ξ₂ ht₂).mul_right _
  refine (Summable.tsum_le_tsum h1 (summable_prod_gauss ht₂ ht₃ ξ₂ ξ₃).prod hs).trans ?_
  rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right (tsum_exp_neg_mul_add_sq_le ξ₂ ht₂) (by positivity)

lemma summable_triple_gauss (ξ₂ : ℤ → ℝ) (ξ₃ : ℤ → ℤ → ℝ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (ht₃ : 0 < t₃) : Summable fun p : ℤ × ℤ × ℤ ↦ Real.exp (-t₁ * (p.1 : ℝ) ^ 2) *
      (Real.exp (-t₂ * ((p.2.1 : ℝ) + ξ₂ p.1) ^ 2) *
        Real.exp (-t₃ * ((p.2.2 : ℝ) + ξ₃ p.1 p.2.1) ^ 2)) := by
  refine (summable_prod_of_nonneg fun q ↦ by positivity).mpr ⟨fun c ↦ ?_, ?_⟩
  · exact (summable_prod_gauss ht₂ ht₃ (ξ₂ c) (ξ₃ c)).mul_left (Real.exp (-t₁ * (c : ℝ) ^ 2))
  · have hs : Summable fun c : ℤ ↦ Real.exp (-t₁ * (c : ℝ) ^ 2) * ((2 + 2 / t₂) * (2 + 2 / t₃)) :=
      ((summable_exp_neg_mul_add_sq 0 ht₁).congr fun c ↦ by rw [add_zero]).mul_right _
    refine Summable.of_nonneg_of_le (fun c ↦ tsum_nonneg fun q ↦ by positivity) (fun c ↦ ?_) hs
    dsimp only
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (tsum_prod_gauss_le ht₂ ht₃ (ξ₂ c) (ξ₃ c)) (Real.exp_pos _).le

end GaussianSum

section Kernel

variable (s : ℂ) (z w : ℍ) (C μ b : ℤ)

/-- The exponent outside the theta function in the generating kernel:
`-(π v² / 4 y) τ τ̄ + 2 π i (C u² / 4) τ + s (-(i v² / 4 y) τ̄ + i v C u / 2) + s² v² / (16 π y)`,
with `τ = C z + μ`. -/
noncomputable def shimuraKernelOuter : ℂ :=
  -((π : ℂ) * (w.im : ℂ) ^ 2 / (4 * (z.im : ℂ))) * ((C : ℂ) * z + μ) *
      ((C : ℂ) * conj (z : ℂ) + μ) +
    2 * π * I * ((C : ℂ) * (w.re : ℂ) ^ 2 / 4) * ((C : ℂ) * z + μ) +
    s * (-(I * (w.im : ℂ) ^ 2 / (4 * (z.im : ℂ))) * ((C : ℂ) * conj (z : ℂ) + μ) +
      I * (w.im : ℂ) * C * (w.re : ℂ) / 2) +
    s ^ 2 * ((w.im : ℂ) ^ 2 / (16 * π * (z.im : ℂ)))

/-- The **generating kernel** `S_s(z, w; C, μ)` of Niwa's theta kernel in the mixed model, with
`τ = C z + μ`: `(v / 2)` times the exponential of `ModularForm.shimuraKernelOuter` times Jacobi's
theta function `ϑ(z, τ u + s v / (2π))`, that is, `jacobiTheta₂ (τ u + s v / (2π)) (2 z)`. -/
noncomputable def shimuraKernelGen : ℂ :=
  ((w.im : ℂ) / 2) * cexp (shimuraKernelOuter s z w C μ) *
    jacobiTheta₂ (((C : ℂ) * z + μ) * (w.re : ℂ) + s * (w.im : ℂ) / (2 * π)) (2 * z)

variable {s} in
private lemma outer_algebra {p i u v c C' τ τb J Jb y : ℂ} (hp : p ≠ 0) (hJ : J ≠ 0) (hJb : Jb ≠ 0)
    (hy : y ≠ 0) (hb : Jb = J - 2 * i * c * y) : -(p * v ^ 2 / (4 * (y / (J * Jb)))) * (τ / J) *
      (τb / Jb) + 2 * p * i * ((C' * J - c * τ) * u ^ 2 / 4) * (τ / J) +
      s * (-(i * v ^ 2 / (4 * (y / (J * Jb)))) * (τb / Jb) + i * v * (C' * J - c * τ) * u / 2) +
      s ^ 2 * (v ^ 2 / (16 * p * (y / (J * Jb)))) +
      2 * p * i * c * (τ * u + (s * J) * v / (2 * p)) ^ 2 / (4 * J) =
    -(p * v ^ 2 / (4 * y)) * τ * τb + 2 * p * i * (C' * u ^ 2 / 4) * τ +
      (s * J) * (-(i * v ^ 2 / (4 * y)) * τb + i * v * C' * u / 2) +
      (s * J) ^ 2 * (v ^ 2 / (16 * p * y)) := by
  field_simp
  rw [hb]
  ring1

variable {z} {γ : SL(2, ℤ)}

variable (z) in
private lemma conj_eq_sub : conj (z : ℂ) = (z : ℂ) - 2 * I * (z.im : ℂ) := by
  have h : (z : ℂ) - conj (z : ℂ) = ((2 * (z : ℂ).im : ℝ) : ℂ) * I := Complex.sub_conj (z : ℂ)
  have e : ((2 * (z : ℂ).im : ℝ) : ℂ) = 2 * (z.im : ℂ) := by
    push_cast
    rfl
  rw [e] at h
  linear_combination -h

private lemma shimuraKernelOuter_smul : shimuraKernelOuter s (γ • z) w C μ +
    2 * π * I * (γ 1 0 : ℂ) *
      ((((C * γ 0 0 + μ * γ 1 0 : ℤ) : ℂ) * z + ((C * γ 0 1 + μ * γ 1 1 : ℤ) : ℂ)) * (w.re : ℂ) +
        (s * ((γ 1 0 : ℂ) * z + γ 1 1)) * (w.im : ℂ) / (2 * π)) ^ 2 /
          (4 * ((γ 1 0 : ℂ) * z + γ 1 1)) =
      shimuraKernelOuter (s * ((γ 1 0 : ℂ) * z + γ 1 1)) z w (C * γ 0 0 + μ * γ 1 0)
        (C * γ 0 1 + μ * γ 1 1) := by
  have hJ : (γ 1 0 : ℂ) * (z : ℂ) + γ 1 1 ≠ 0 := denomZ_ne_zero γ z
  have hJb : (γ 1 0 : ℂ) * conj (z : ℂ) + γ 1 1 ≠ 0 := denomZ_conj_ne_zero γ z
  have hdetc : (γ 0 0 : ℂ) * γ 1 1 - (γ 0 1 : ℂ) * γ 1 0 = 1 := γ.intCast_fin_two_mul_sub_mul_eq_one
  have hb : (γ 1 0 : ℂ) * conj (z : ℂ) + γ 1 1 =
      ((γ 1 0 : ℂ) * z + γ 1 1) - 2 * I * (γ 1 0 : ℂ) * (z.im : ℂ) := by
    rw [conj_eq_sub]
    ring1
  have hτ : (C : ℂ) * ((γ • z : ℍ) : ℂ) + μ = (((C * γ 0 0 + μ * γ 1 0 : ℤ) : ℂ) * z +
      ((C * γ 0 1 + μ * γ 1 1 : ℤ) : ℂ)) / ((γ 1 0 : ℂ) * z + γ 1 1) := by
    rw [coe_smul_eq_div, eq_div_iff hJ, add_mul, mul_assoc, div_mul_cancel₀ _ hJ]
    push_cast
    ring1
  have hτb : (C : ℂ) * conj ((γ • z : ℍ) : ℂ) + μ =
      (((C * γ 0 0 + μ * γ 1 0 : ℤ) : ℂ) * conj (z : ℂ) + ((C * γ 0 1 + μ * γ 1 1 : ℤ) : ℂ)) /
        ((γ 1 0 : ℂ) * conj (z : ℂ) + γ 1 1) := by
    rw [conj_coe_smul, eq_div_iff hJb, add_mul, mul_assoc, div_mul_cancel₀ _ hJb]
    push_cast
    ring1
  have hC : (C : ℂ) = ((C * γ 0 0 + μ * γ 1 0 : ℤ) : ℂ) * ((γ 1 0 : ℂ) * z + γ 1 1) -
      (γ 1 0 : ℂ) * (((C * γ 0 0 + μ * γ 1 0 : ℤ) : ℂ) * z +
        ((C * γ 0 1 + μ * γ 1 1 : ℤ) : ℂ)) := by
    push_cast
    linear_combination (-(C : ℂ)) * hdetc
  have hy : (z.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr z.im_ne_zero
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [shimuraKernelOuter, shimuraKernelOuter, hτ, hτb, coe_im_smul, hC]
  exact outer_algebra (p := (π : ℂ)) (i := I) (u := (w.re : ℂ)) (v := (w.im : ℂ)) (s := s)
    (c := (γ 1 0 : ℂ)) (C' := ((C * γ 0 0 + μ * γ 1 0 : ℤ) : ℂ))
    (τ := ((C * γ 0 0 + μ * γ 1 0 : ℤ) : ℂ) * z + ((C * γ 0 1 + μ * γ 1 1 : ℤ) : ℂ))
    (τb := ((C * γ 0 0 + μ * γ 1 0 : ℤ) : ℂ) * conj (z : ℂ) + ((C * γ 0 1 + μ * γ 1 1 : ℤ) : ℂ))
    (J := (γ 1 0 : ℂ) * z + γ 1 1) (y := (z.im : ℂ)) hp hJ hJb hy hb

/-- **The law of the kernel in `z`**: for `γ = (a, b; c, d) ∈ Γ₀(4)`,
`S_s(γ z, w; C, μ) = j(γ, z) S_{s (c z + d)}(z, w; C a + μ c, C b + μ d)`, where `j` is Shimura's
theta multiplier. -/
lemma shimuraKernelGen_smul (hγ : γ ∈ Gamma0 4) : shimuraKernelGen s (γ • z) w C μ =
    thetaFactor γ z * shimuraKernelGen (s * denom γ z) z w (C * γ 0 0 + μ * γ 1 0)
      (C * γ 0 1 + μ * γ 1 1) := by
  have hd : denom γ z = (γ 1 0 : ℂ) * z + γ 1 1 := ModularGroup.denom_apply γ z
  have hJ : (γ 1 0 : ℂ) * (z : ℂ) + γ 1 1 ≠ 0 := denomZ_ne_zero γ z
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hξ : ((C : ℂ) * ((γ • z : ℍ) : ℂ) + μ) * (w.re : ℂ) + s * (w.im : ℂ) / (2 * π) =
      ((((C * γ 0 0 + μ * γ 1 0 : ℤ) : ℂ) * z + ((C * γ 0 1 + μ * γ 1 1 : ℤ) : ℂ)) * (w.re : ℂ) +
        (s * ((γ 1 0 : ℂ) * z + γ 1 1)) * (w.im : ℂ) / (2 * π)) / ((γ 1 0 : ℂ) * z + γ 1 1) := by
    have hτ : (C : ℂ) * ((γ • z : ℍ) : ℂ) + μ = (((C * γ 0 0 + μ * γ 1 0 : ℤ) : ℂ) * z +
        ((C * γ 0 1 + μ * γ 1 1 : ℤ) : ℂ)) / ((γ 1 0 : ℂ) * z + γ 1 1) := by
      rw [coe_smul_eq_div, eq_div_iff hJ, add_mul, mul_assoc, div_mul_cancel₀ _ hJ]
      push_cast
      ring1
    rw [hτ]
    generalize (γ 1 0 : ℂ) * (z : ℂ) + γ 1 1 = J at hJ ⊢
    field_simp
  rw [shimuraKernelGen, shimuraKernelGen, hξ, ← hd, jacobiTheta₂_two_mul_smul z _ hγ, hd,
    ← shimuraKernelOuter_smul s w C μ, Complex.exp_add]
  ring1

variable (z)

/-- The exponent of the `b`-th term of the kernel, without `s`: `-(π v² / 4 y) τ τ̄ +
2 π i ((b + C u / 2)² z + μ u (b + C u / 4))`, with `τ = C z + μ`. -/
noncomputable def shimuraKernelTermExp : ℂ :=
  -((π : ℂ) * (w.im : ℂ) ^ 2 / (4 * (z.im : ℂ))) * ((C : ℂ) * z + μ) *
      ((C : ℂ) * conj (z : ℂ) + μ) +
    2 * π * I * (((b : ℂ) + C * (w.re : ℂ) / 2) ^ 2 * z + μ * (w.re : ℂ) * (b + C * (w.re : ℂ) / 4))

/-- The coefficient of `s` in the exponent of the `b`-th term of the kernel:
`i v (b + C u / 2 - (v / 4 y) τ̄)`, with `τ = C z + μ`. -/
noncomputable def shimuraKernelAlpha : ℂ :=
  I * (w.im : ℂ) * ((b : ℂ) + C * (w.re : ℂ) / 2 -
    (w.im : ℂ) / (4 * (z.im : ℂ)) * ((C : ℂ) * conj (z : ℂ) + μ))

/-- The coefficient of `s²` in the exponent of the terms of the kernel: `v² / (16 π y)`. -/
noncomputable def shimuraKernelBeta : ℝ :=
  w.im ^ 2 / (16 * π * z.im)

/-- The `b`-th term of the coefficient of `s ^ l` in the kernel `S_s(z, w; C, μ)`. -/
noncomputable def shimuraKernelTerm (l : ℕ) : ℂ :=
  ((w.im : ℂ) / 2) * cexp (shimuraKernelTermExp z w C μ b) *
    gaussCoeff l (shimuraKernelAlpha z w C μ b) (shimuraKernelBeta z w)

/-- The **coefficient of `s ^ l` in the kernel** `S_s(z, w; C, μ)`: the kernel of weight `l + 1/2`
in `z`, for one pair `(C, μ)`. -/
noncomputable def shimuraKernelCoeff (l : ℕ) : ℂ :=
  ∑' b : ℤ, shimuraKernelTerm z w C μ b l

lemma shimuraKernelOuter_add_term : shimuraKernelOuter s z w C μ +
    (2 * π * I * b * (((C : ℂ) * z + μ) * (w.re : ℂ) + s * (w.im : ℂ) / (2 * π)) +
      π * I * (b : ℂ) ^ 2 * (2 * z)) = shimuraKernelTermExp z w C μ b +
        (shimuraKernelAlpha z w C μ b * s + (shimuraKernelBeta z w : ℂ) * s ^ 2) := by
  have hy : (z.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr z.im_ne_zero
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [shimuraKernelOuter, shimuraKernelTermExp, shimuraKernelAlpha, shimuraKernelBeta]
  push_cast
  field_simp
  ring1

lemma hasSum_shimuraKernelGen : HasSum (fun b : ℤ ↦ ((w.im : ℂ) / 2) *
    cexp (shimuraKernelTermExp z w C μ b + (shimuraKernelAlpha z w C μ b * s +
      (shimuraKernelBeta z w : ℂ) * s ^ 2))) (shimuraKernelGen s z w C μ) := by
  have him : 0 < (2 * (z : ℂ)).im := by
    have e : (2 * (z : ℂ)).im = 2 * z.im := by simp
    rw [e]
    exact mul_pos two_pos z.im_pos
  have e : (fun b : ℤ ↦ ((w.im : ℂ) / 2) * cexp (shimuraKernelTermExp z w C μ b +
      (shimuraKernelAlpha z w C μ b * s + (shimuraKernelBeta z w : ℂ) * s ^ 2))) = fun b : ℤ ↦
        ((w.im : ℂ) / 2) * cexp (shimuraKernelOuter s z w C μ) * jacobiTheta₂_term b
          (((C : ℂ) * z + μ) * (w.re : ℂ) + s * (w.im : ℂ) / (2 * π)) (2 * z) := by
    funext b
    rw [jacobiTheta₂_term, mul_assoc, ← Complex.exp_add, shimuraKernelOuter_add_term]
  rw [e]
  exact (hasSum_jacobiTheta₂_term (((C : ℂ) * z + μ) * (w.re : ℂ) + s * (w.im : ℂ) / (2 * π))
    him).mul_left (((w.im : ℂ) / 2) * cexp (shimuraKernelOuter s z w C μ))

private lemma mul_conj_eq_normSq :
    ((C : ℂ) * z + μ) * ((C : ℂ) * conj (z : ℂ) + μ) = ((normSq ((C : ℂ) * z + μ) : ℝ) : ℂ) := by
  rw [← Complex.mul_conj]
  simp only [map_add, map_mul, map_intCast]

lemma norm_cexp_shimuraKernelTermExp : ‖cexp (shimuraKernelTermExp z w C μ b)‖ =
    Real.exp (-(π * w.im ^ 2 / (4 * z.im)) * normSq ((C : ℂ) * z + μ) -
      2 * π * z.im * ((b : ℝ) + C * w.re / 2) ^ 2) := by
  rw [Complex.norm_exp, shimuraKernelTermExp, mul_assoc (-_ : ℂ), mul_conj_eq_normSq]
  congr 1
  have e : (2 * (π : ℂ) * I * (((b : ℂ) + C * (w.re : ℂ) / 2) ^ 2 * z +
      μ * (w.re : ℂ) * (b + C * (w.re : ℂ) / 4))) = (((2 * π * μ * w.re * (b + C * w.re / 4) +
        2 * π * ((b : ℝ) + C * w.re / 2) ^ 2 * z.re : ℝ) : ℂ) * I +
          ((-(2 * π * z.im * ((b : ℝ) + C * w.re / 2) ^ 2) : ℝ) : ℂ)) := by
    have hz : (z : ℂ) = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im (z : ℂ)).symm
    rw [hz]
    push_cast
    linear_combination (2 * (π : ℂ) * ((b : ℂ) + C * (w.re : ℂ) / 2) ^ 2 * (z.im : ℂ)) * I_sq
  have e2 : -((π : ℂ) * (w.im : ℂ) ^ 2 / (4 * (z.im : ℂ))) * ((normSq ((C : ℂ) * z + μ) : ℝ) : ℂ) =
      ((-(π * w.im ^ 2 / (4 * z.im)) * normSq ((C : ℂ) * z + μ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [e, e2, add_re, add_re, ofReal_re, ofReal_re, re_ofReal_mul, I_re, mul_zero]
  ring1

private lemma two_mul_le_add {r T : ℝ} : 2 * r * T ≤ π * T ^ 2 + r ^ 2 / π := by
  have hp : 0 < π := Real.pi_pos
  have h : 0 ≤ (π * T - r) ^ 2 := sq_nonneg (π * T - r)
  have e : π * T ^ 2 + r ^ 2 / π - 2 * r * T = (π * T - r) ^ 2 / π := by
    field_simp
    ring1
  have h2 : 0 ≤ (π * T - r) ^ 2 / π := by positivity
  linarith

private lemma exponent_le {r y v T D : ℝ} (hy : 0 < y) (hv : 0 < v) : -(π * v ^ 2 / (4 * y)) *
    T ^ 2 - 2 * π * y * D ^ 2 + ((v * D + v ^ 2 / (4 * y) * T) * r + v ^ 2 / (16 * π * y) * r ^ 2) ≤
      7 * r ^ 2 * v ^ 2 / (16 * π * y) - π * v ^ 2 / (8 * y) * T ^ 2 - π * y * D ^ 2 := by
  have hp : 0 < π := Real.pi_pos
  have h0 : 0 ≤ v ^ 2 / (8 * y) := by positivity
  have h1 : v ^ 2 / (8 * y) * (2 * r * T) ≤ v ^ 2 / (8 * y) * (π * T ^ 2 + r ^ 2 / π) :=
    mul_le_mul_of_nonneg_left two_mul_le_add h0
  have h2 : v * D * r ≤ π * y * D ^ 2 + r ^ 2 * v ^ 2 / (4 * π * y) := by
    have h3 : 0 ≤ (2 * π * y * D - r * v) ^ 2 := sq_nonneg (2 * π * y * D - r * v)
    have e : π * y * D ^ 2 + r ^ 2 * v ^ 2 / (4 * π * y) - v * D * r =
        (2 * π * y * D - r * v) ^ 2 / (4 * π * y) := by
      field_simp
      ring1
    have h4 : 0 ≤ (2 * π * y * D - r * v) ^ 2 / (4 * π * y) := by positivity
    linarith
  have e1 : 7 * r ^ 2 * v ^ 2 / (16 * π * y) = v ^ 2 / (8 * y) * (r ^ 2 / π) +
      r ^ 2 * v ^ 2 / (4 * π * y) + v ^ 2 / (16 * π * y) * r ^ 2 := by
    field_simp
    ring1
  have e2 : π * v ^ 2 / (4 * y) = 2 * (π * v ^ 2 / (8 * y)) := by
    field_simp
    norm_num
  have e3 : π * v ^ 2 / (8 * y) * T ^ 2 = v ^ 2 / (8 * y) * (π * T ^ 2) := by
    field_simp
  have e4 : v ^ 2 / (4 * y) * T * r = v ^ 2 / (8 * y) * (2 * r * T) := by
    field_simp
    ring1
  rw [e1, e2]
  nlinarith

/-- The majorant of the `b`-th term of the kernel at radius `r`:
`(v / 2) exp(7 r² v² / (16 π y)) exp(-(π v² / 8 y) |C z + μ|²) exp(-π y (b + C u / 2)²)`. -/
noncomputable def shimuraKernelMajorant (r : ℝ) : ℝ :=
  w.im / 2 * Real.exp (7 * r ^ 2 * w.im ^ 2 / (16 * π * z.im)) *
    (Real.exp (-(π * w.im ^ 2 / (8 * z.im)) * normSq ((C : ℂ) * z + μ)) *
      Real.exp (-(π * z.im) * ((b : ℝ) + C * w.re / 2) ^ 2))

variable {r : ℝ}

lemma mul_exp_alpha_le (hr : 0 ≤ r) : w.im / 2 * ‖cexp (shimuraKernelTermExp z w C μ b)‖ *
    Real.exp (‖shimuraKernelAlpha z w C μ b‖ * r + shimuraKernelBeta z w * r ^ 2) ≤
      shimuraKernelMajorant z w C μ b r := by
  have hy : 0 < z.im := z.im_pos
  have hv : 0 < w.im := w.im_pos
  have hp : 0 < π := Real.pi_pos
  have hT : ‖(C : ℂ) * conj (z : ℂ) + μ‖ = ‖(C : ℂ) * z + μ‖ := by
    have e : (C : ℂ) * conj (z : ℂ) + μ = conj ((C : ℂ) * z + μ) := by
      simp only [map_add, map_mul, map_intCast]
    rw [e, Complex.norm_conj]
  have hα : ‖shimuraKernelAlpha z w C μ b‖ ≤ w.im * |(b : ℝ) + C * w.re / 2| +
      w.im ^ 2 / (4 * z.im) * ‖(C : ℂ) * z + μ‖ := by
    have e : ‖shimuraKernelAlpha z w C μ b‖ = w.im * ‖(((b : ℝ) + C * w.re / 2 : ℝ) : ℂ) -
        (w.im : ℂ) / (4 * (z.im : ℂ)) * ((C : ℂ) * conj (z : ℂ) + μ)‖ := by
      rw [shimuraKernelAlpha, norm_mul, norm_mul, norm_I, one_mul, norm_real,
        Real.norm_of_nonneg hv.le]
      push_cast
      rfl
    have e2 : ‖(w.im : ℂ) / (4 * (z.im : ℂ)) * ((C : ℂ) * conj (z : ℂ) + μ)‖ =
        w.im / (4 * z.im) * ‖(C : ℂ) * z + μ‖ := by
      have e3 : (w.im : ℂ) / (4 * (z.im : ℂ)) = ((w.im / (4 * z.im) : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [norm_mul, e3, norm_real, Real.norm_of_nonneg (by positivity), hT]
    rw [e]
    have h1 : ‖(((b : ℝ) + C * w.re / 2 : ℝ) : ℂ) - (w.im : ℂ) / (4 * (z.im : ℂ)) *
        ((C : ℂ) * conj (z : ℂ) + μ)‖ ≤ ‖(((b : ℝ) + C * w.re / 2 : ℝ) : ℂ)‖ +
          ‖(w.im : ℂ) / (4 * (z.im : ℂ)) * ((C : ℂ) * conj (z : ℂ) + μ)‖ :=
      norm_sub_le _ _
    rw [e2, norm_real, Real.norm_eq_abs] at h1
    have e4 : w.im ^ 2 / (4 * z.im) = w.im * (w.im / (4 * z.im)) := by
      field_simp
    rw [e4, mul_assoc, ← mul_add]
    exact mul_le_mul_of_nonneg_left h1 hv.le
  have hn : normSq ((C : ℂ) * z + μ) = ‖(C : ℂ) * z + μ‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have hD : ((b : ℝ) + C * w.re / 2) ^ 2 = |(b : ℝ) + C * w.re / 2| ^ 2 := (sq_abs _).symm
  rw [shimuraKernelMajorant, norm_cexp_shimuraKernelTermExp, shimuraKernelBeta,
    mul_assoc (w.im / 2), ← Real.exp_add, mul_assoc (w.im / 2), ← Real.exp_add, ← Real.exp_add, hn,
    hD]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have h2 : ‖shimuraKernelAlpha z w C μ b‖ * r ≤ (w.im * |(b : ℝ) + C * w.re / 2| +
      w.im ^ 2 / (4 * z.im) * ‖(C : ℂ) * z + μ‖) * r := mul_le_mul_of_nonneg_right hα hr
  linarith [exponent_le (r := r) (T := ‖(C : ℂ) * z + μ‖) (D := |(b : ℝ) + C * w.re / 2|) hy hv]

/-- **The bound of the `b`-th term of the kernel by the majorant**, at every radius `r ≥ 0`. -/
lemma norm_shimuraKernelTerm_mul_pow_le (l : ℕ) (hr : 0 ≤ r) :
    ‖shimuraKernelTerm z w C μ b l‖ * r ^ l ≤ shimuraKernelMajorant z w C μ b r := by
  have hv : 0 < w.im := w.im_pos
  have hβ : ‖((shimuraKernelBeta z w : ℝ) : ℂ)‖ = shimuraKernelBeta z w := by
    rw [norm_real, Real.norm_of_nonneg]
    have hp : 0 < π := Real.pi_pos
    have hy : 0 < z.im := z.im_pos
    rw [shimuraKernelBeta]
    positivity
  have e : ‖(w.im : ℂ) / 2‖ = w.im / 2 := by
    rw [norm_div, norm_real, Real.norm_of_nonneg hv.le]
    norm_num
  rw [shimuraKernelTerm, norm_mul, norm_mul, e, mul_assoc]
  refine le_trans ?_ (mul_exp_alpha_le z w C μ b hr)
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) (norm_nonneg _))
  simpa only [hβ] using norm_gaussCoeff_mul_pow_le l (shimuraKernelAlpha z w C μ b)
    (shimuraKernelBeta z w : ℂ) hr

lemma summable_shimuraKernelMajorant {N : ℕ} (hN : N ≠ 0) (ρ : ℝ) :
    Summable fun p : (ℤ × ℤ) × ℤ ↦ shimuraKernelMajorant z w ((N : ℤ) * p.1.1) p.1.2 p.2 ρ := by
  have hy : 0 < z.im := z.im_pos
  have hv : 0 < w.im := w.im_pos
  have hp : 0 < π := Real.pi_pos
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  refine ((Equiv.prodAssoc ℤ ℤ ℤ).summable_iff.mpr (summable_triple_gauss
    (fun c : ℤ ↦ (N : ℝ) * c * z.re) (fun c _ ↦ (N : ℝ) * c * w.re / 2)
    (t₁ := π * w.im ^ 2 / (8 * z.im) * ((N : ℝ) * z.im) ^ 2) (t₂ := π * w.im ^ 2 / (8 * z.im))
    (t₃ := π * z.im) (by positivity) (by positivity) (by positivity))).mul_left
    (w.im / 2 * Real.exp (7 * ρ ^ 2 * w.im ^ 2 / (16 * π * z.im))) |>.congr fun p ↦ ?_
  have hn : normSq ((((N : ℤ) * p.1.1 : ℤ) : ℂ) * z + (p.1.2 : ℂ)) =
      ((N : ℝ) * p.1.1 * z.im) ^ 2 + ((p.1.2 : ℝ) + (N : ℝ) * p.1.1 * z.re) ^ 2 := by
    rw [normSq_apply]
    simp only [add_re, mul_re, intCast_re, intCast_im, coe_re, coe_im, add_im, mul_im]
    push_cast
    ring1
  have e1 : -(π * w.im ^ 2 / (8 * z.im) * ((N : ℝ) * z.im) ^ 2) * (p.1.1 : ℝ) ^ 2 =
      -(π * w.im ^ 2 / (8 * z.im)) * ((N : ℝ) * p.1.1 * z.im) ^ 2 := by
    ring1
  have e2 : (((N : ℤ) * p.1.1 : ℤ) : ℝ) = (N : ℝ) * p.1.1 := by
    push_cast
    rfl
  simp only [shimuraKernelMajorant, Equiv.prodAssoc_apply, Function.comp_apply]
  rw [hn, mul_add, Real.exp_add, e1, e2]
  ring1

private lemma eq_zero_of_hasSum_real {c : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ τ : ℝ, |τ| < ε → HasSum (fun n ↦ c n * τ ^ n) 0) : c = 0 := by
  have hr : 0 < ε / 2 := half_pos hε
  let r : NNReal := ⟨ε / 2, hr.le⟩
  have hsum : Summable fun n ↦ ‖FormalMultilinearSeries.ofScalars ℝ c n‖ * (r : ℝ) ^ n := by
    have h1 : Summable fun n ↦ c n * (ε / 2) ^ n :=
      (h (ε / 2) (by rw [abs_of_pos hr]; linarith)).summable
    refine h1.norm.congr fun n ↦ ?_
    rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Real.norm_of_nonneg hr.le]
    rfl
  have hp : HasFPowerSeriesOnBall (0 : ℝ → ℝ) (FormalMultilinearSeries.ofScalars ℝ c) 0
      (r : ENNReal) := by
    refine ⟨FormalMultilinearSeries.le_radius_of_summable_norm _ hsum, ?_, fun {y} hy ↦ ?_⟩
    · exact ENNReal.coe_pos.mpr hr
    · have hy' : |y| < ε := by
        have h2 : ‖y‖₊ < r := by
          simpa [Metric.eball] using hy
        have h3 : |y| < ε / 2 := by
          exact_mod_cast h2
        linarith
      simpa [mul_comm] using h y hy'
  exact (FormalMultilinearSeries.ofScalars_series_eq_zero ℝ).mp hp.hasFPowerSeriesAt.eq_zero

lemma eq_zero_of_hasSum_ofReal {c : ℕ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ τ : ℝ, |τ| < ε → HasSum (fun n ↦ c n * (τ : ℂ) ^ n) 0) : c = 0 := by
  have hre : (fun n ↦ (c n).re) = 0 := eq_zero_of_hasSum_real hε fun τ hτ ↦ by
    simpa only [← ofReal_pow, re_mul_ofReal, zero_re] using Complex.hasSum_re (h τ hτ)
  have him : (fun n ↦ (c n).im) = 0 := eq_zero_of_hasSum_real hε fun τ hτ ↦ by
    simpa only [← ofReal_pow, im_mul_ofReal, zero_im] using Complex.hasSum_im (h τ hτ)
  funext n
  exact Complex.ext (congrFun hre n) (congrFun him n)

lemma eq_of_forall_hasSum_mul_pow {c d : ℕ → ℂ} {f : ℂ → ℂ}
    (hc : ∀ s, HasSum (fun n ↦ c n * s ^ n) (f s)) (hd : ∀ s, HasSum (fun n ↦ d n * s ^ n) (f s))
    (n : ℕ) : c n = d n := by
  have h : (fun n ↦ c n - d n) = 0 := eq_zero_of_hasSum_ofReal one_pos fun τ _ ↦ by
    simpa only [sub_mul, sub_self] using (hc τ).sub (hd τ)
  exact sub_eq_zero.mp (congrFun h n)

lemma hasSum_tsum_mul_pow {ι : Type*} {T : ι → ℕ → ℂ} {G : ι → ℂ} {M : ι → ℝ} {t : ℂ}
    (hM : Summable M) (hT : ∀ i l, ‖T i l‖ * (2 * ‖t‖) ^ l ≤ M i)
    (hG : ∀ i, HasSum (fun l ↦ T i l * t ^ l) (G i)) :
    HasSum (fun l ↦ (∑' i, T i l) * t ^ l) (∑' i, G i) := by
  have hM0 (i : ι) : 0 ≤ M i := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hT i 0)
  have hs : Summable fun x : ι × ℕ ↦ T x.1 x.2 * t ^ x.2 := by
    refine Summable.of_norm_bounded (g := fun x : ι × ℕ ↦ M x.1 * (1 / 2 : ℝ) ^ x.2)
      (hM.mul_of_nonneg (summable_geometric_two) hM0 fun n ↦ by positivity) fun x ↦ ?_
    have e : 2 * ‖t‖ * (1 / 2) = ‖t‖ := by ring1
    have h1 : ‖T x.1 x.2 * t ^ x.2‖ = ‖T x.1 x.2‖ * (2 * ‖t‖) ^ x.2 * (1 / 2 : ℝ) ^ x.2 := by
      rw [norm_mul, norm_pow, mul_assoc, ← mul_pow, e]
    rw [h1]
    exact mul_le_mul_of_nonneg_right (hT _ _) (by positivity)
  have h1 : HasSum (fun x : ℕ × ι ↦ T x.2 x.1 * t ^ x.1) (∑' x : ι × ℕ, T x.1 x.2 * t ^ x.2) :=
    (Equiv.prodComm ℕ ι).hasSum_iff.mpr hs.hasSum
  have h2 : HasSum (fun l ↦ ∑' i, T i l * t ^ l) (∑' x : ι × ℕ, T x.1 x.2 * t ^ x.2) :=
    h1.prod_fiberwise fun l ↦ (h1.summable.prod_factor l).hasSum
  rw [hs.tsum_prod, tsum_congr fun i ↦ (hG i).tsum_eq] at h2
  simpa only [tsum_mul_right] using h2

lemma hasSum_shimuraKernelTerm_mul_pow : HasSum (fun l ↦ shimuraKernelTerm z w C μ b l * s ^ l)
    (((w.im : ℂ) / 2) * cexp (shimuraKernelTermExp z w C μ b + (shimuraKernelAlpha z w C μ b * s +
      (shimuraKernelBeta z w : ℂ) * s ^ 2))) := by
  simpa only [mul_assoc, ← Complex.exp_add, shimuraKernelTerm] using
    (hasSum_gaussCoeff_mul_pow (shimuraKernelAlpha z w C μ b) (shimuraKernelBeta z w : ℂ)
      s).mul_left (((w.im : ℂ) / 2) * cexp (shimuraKernelTermExp z w C μ b))

variable (r) in
lemma summable_shimuraKernelMajorant_right :
    Summable fun b : ℤ ↦ shimuraKernelMajorant z w C μ b r := by
  have hy : 0 < z.im := z.im_pos
  have hp : 0 < π := Real.pi_pos
  exact (summable_exp_neg_mul_add_sq (C * w.re / 2) (mul_pos hp hy)).mul_left _ |>.mul_left _

lemma hasSum_shimuraKernelCoeff_mul_pow :
    HasSum (fun l ↦ shimuraKernelCoeff z w C μ l * s ^ l) (shimuraKernelGen s z w C μ) := by
  rw [← (hasSum_shimuraKernelGen s z w C μ).tsum_eq]
  exact hasSum_tsum_mul_pow (T := fun b l ↦ shimuraKernelTerm z w C μ b l)
    (G := fun b ↦ ((w.im : ℂ) / 2) * cexp (shimuraKernelTermExp z w C μ b +
      (shimuraKernelAlpha z w C μ b * s + (shimuraKernelBeta z w : ℂ) * s ^ 2)))
    (summable_shimuraKernelMajorant_right z w C μ (2 * ‖s‖))
    (fun b l ↦ norm_shimuraKernelTerm_mul_pow_le z w C μ b l (by positivity))
    (fun b ↦ hasSum_shimuraKernelTerm_mul_pow s z w C μ b)

/-- **The law of the kernel of weight `l + 1/2` in `z`**, for one pair: for
`γ = (a, b; c, d) ∈ Γ₀(4)`, the coefficient of `s ^ l` in `S_s(z, w; C, μ)` satisfies
`S^(l)(γ z, w; C, μ) = j(γ, z) (c z + d) ^ l S^(l)(z, w; C a + μ c, C b + μ d)`. -/
lemma shimuraKernelCoeff_smul (hγ : γ ∈ Gamma0 4) (l : ℕ) : shimuraKernelCoeff (γ • z) w C μ l =
    thetaFactor γ z * denom γ z ^ l * shimuraKernelCoeff z w (C * γ 0 0 + μ * γ 1 0)
      (C * γ 0 1 + μ * γ 1 1) l := by
  refine eq_of_forall_hasSum_mul_pow (d := fun l ↦ thetaFactor γ z * denom γ z ^ l *
    shimuraKernelCoeff z w (C * γ 0 0 + μ * γ 1 0) (C * γ 0 1 + μ * γ 1 1) l)
    (fun s ↦ hasSum_shimuraKernelCoeff_mul_pow s (γ • z) w C μ) (fun s ↦ ?_) l
  have e : (fun l ↦ thetaFactor γ z * (shimuraKernelCoeff z w (C * γ 0 0 + μ * γ 1 0)
      (C * γ 0 1 + μ * γ 1 1) l * (s * denom γ z) ^ l)) = fun l ↦ thetaFactor γ z * denom γ z ^ l *
        shimuraKernelCoeff z w (C * γ 0 0 + μ * γ 1 0) (C * γ 0 1 + μ * γ 1 1) l * s ^ l := by
    funext l
    rw [mul_pow]
    ring1
  rw [shimuraKernelGen_smul s w C μ hγ, ← e]
  exact (hasSum_shimuraKernelCoeff_mul_pow (s * denom γ z) z w (C * γ 0 0 + μ * γ 1 0)
    (C * γ 0 1 + μ * γ 1 1)).mul_left (thetaFactor γ z)

end Kernel

section Theta

variable {N : ℕ} (ψ : DirichletCharacter ℂ N) (s : ℂ) (z w : ℍ) (l : ℕ)

/-- The **generating theta kernel** `Θ_s(z, w) = ∑_{(C, μ)} ψ⁻¹(μ) S_s(z, w; N C, μ)`, the sum over
all pairs of integers. -/
noncomputable def shimuraThetaGen : ℂ :=
  ∑' p : ℤ × ℤ, ψ⁻¹ (p.2 : ZMod N) * shimuraKernelGen s z w ((N : ℤ) * p.1) p.2

/-- **Niwa's theta kernel** of weight `l + 1/2` in `z`: the coefficient
`Θ^(l)(z, w) = ∑_{(C, μ)} ψ⁻¹(μ) S^(l)(z, w; N C, μ)` of `s ^ l` in `Θ_s(z, w)`. -/
noncomputable def shimuraTheta : ℂ :=
  ∑' p : ℤ × ℤ, ψ⁻¹ (p.2 : ZMod N) * shimuraKernelCoeff z w ((N : ℤ) * p.1) p.2 l

private lemma norm_inv_apply_le (a : ZMod N) : ‖ψ⁻¹ a‖ ≤ 1 :=
  DirichletCharacter.norm_le_one ψ⁻¹ a

variable [NeZero N]

lemma summable_inv_mul_gen_term : Summable fun p : (ℤ × ℤ) × ℤ ↦ ψ⁻¹ (p.1.2 : ZMod N) *
    (((w.im : ℂ) / 2) * cexp (shimuraKernelTermExp z w ((N : ℤ) * p.1.1) p.1.2 p.2 +
      (shimuraKernelAlpha z w ((N : ℤ) * p.1.1) p.1.2 p.2 * s +
        (shimuraKernelBeta z w : ℂ) * s ^ 2))) := by
  refine Summable.of_norm_bounded
    (summable_shimuraKernelMajorant z w (NeZero.ne N) ‖s‖) fun p ↦ ?_
  rw [norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (norm_inv_apply_le ψ _)).trans ?_
  refine le_trans ?_ (mul_exp_alpha_le z w _ _ _ (norm_nonneg s))
  have hv : 0 < w.im := w.im_pos
  have e : ‖(w.im : ℂ) / 2‖ = w.im / 2 := by
    rw [norm_div, norm_real, Real.norm_of_nonneg hv.le]
    norm_num
  have hβ : 0 ≤ shimuraKernelBeta z w := by
    have hp : 0 < π := Real.pi_pos
    have hy : 0 < z.im := z.im_pos
    rw [shimuraKernelBeta]
    positivity
  rw [norm_mul, e, Complex.exp_add, norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (by positivity)
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ((norm_add_le _ _).trans ?_))
  rw [norm_mul, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hβ]

lemma tsum_inv_mul_gen_term : ∑' p : (ℤ × ℤ) × ℤ, ψ⁻¹ (p.1.2 : ZMod N) * (((w.im : ℂ) / 2) *
    cexp (shimuraKernelTermExp z w ((N : ℤ) * p.1.1) p.1.2 p.2 +
      (shimuraKernelAlpha z w ((N : ℤ) * p.1.1) p.1.2 p.2 * s +
        (shimuraKernelBeta z w : ℂ) * s ^ 2))) = shimuraThetaGen ψ s z w := by
  rw [(summable_inv_mul_gen_term ψ s z w).tsum_prod, shimuraThetaGen]
  refine tsum_congr fun q ↦ ?_
  dsimp only
  rw [tsum_mul_left, (hasSum_shimuraKernelGen s z w ((N : ℤ) * q.1) q.2).tsum_eq]

lemma summable_inv_mul_shimuraKernelTerm : Summable fun p : (ℤ × ℤ) × ℤ ↦
    ψ⁻¹ (p.1.2 : ZMod N) * shimuraKernelTerm z w ((N : ℤ) * p.1.1) p.1.2 p.2 l := by
  refine Summable.of_norm_bounded (summable_shimuraKernelMajorant z w (NeZero.ne N) 1) fun p ↦ ?_
  rw [norm_mul]
  refine le_trans ?_ (norm_shimuraKernelTerm_mul_pow_le z w _ _ _ l zero_le_one)
  rw [one_pow, mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_inv_apply_le ψ _)

lemma hasSum_shimuraTheta_mul_pow :
    HasSum (fun l ↦ shimuraTheta ψ z w l * s ^ l) (shimuraThetaGen ψ s z w) := by
  have hT (p : (ℤ × ℤ) × ℤ) (l : ℕ) : ‖ψ⁻¹ (p.1.2 : ZMod N) *
      shimuraKernelTerm z w ((N : ℤ) * p.1.1) p.1.2 p.2 l‖ * (2 * ‖s‖) ^ l ≤
        shimuraKernelMajorant z w ((N : ℤ) * p.1.1) p.1.2 p.2 (2 * ‖s‖) := by
    rw [norm_mul]
    refine le_trans ?_ (norm_shimuraKernelTerm_mul_pow_le z w _ _ _ l (by positivity))
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_inv_apply_le ψ _)
  have e1 (l : ℕ) : ∑' p : (ℤ × ℤ) × ℤ, ψ⁻¹ (p.1.2 : ZMod N) *
      shimuraKernelTerm z w ((N : ℤ) * p.1.1) p.1.2 p.2 l = shimuraTheta ψ z w l := by
    rw [(summable_inv_mul_shimuraKernelTerm ψ z w l).tsum_prod, shimuraTheta]
    refine tsum_congr fun q ↦ ?_
    dsimp only
    rw [tsum_mul_left, shimuraKernelCoeff]
  rw [← tsum_inv_mul_gen_term]
  simpa only [e1] using
    hasSum_tsum_mul_pow (summable_shimuraKernelMajorant z w (NeZero.ne N) (2 * ‖s‖)) hT
      (G := fun p ↦ ψ⁻¹ (p.1.2 : ZMod N) * (((w.im : ℂ) / 2) *
        cexp (shimuraKernelTermExp z w ((N : ℤ) * p.1.1) p.1.2 p.2 +
          (shimuraKernelAlpha z w ((N : ℤ) * p.1.1) p.1.2 p.2 * s +
            (shimuraKernelBeta z w : ℂ) * s ^ 2)))) fun p ↦ by
      simpa only [mul_assoc] using
        (hasSum_shimuraKernelTerm_mul_pow s z w ((N : ℤ) * p.1.1) p.1.2 p.2).mul_left
          (ψ⁻¹ (p.1.2 : ZMod N))

end Theta

end ModularForm
