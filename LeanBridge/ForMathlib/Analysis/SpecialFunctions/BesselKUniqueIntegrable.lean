import LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselKUniqueComplex

/-!
# The solutions of the modified Bessel equation of complex order integrable against a power

For every order `ν ∈ ℂ`, a solution `v` of the modified Bessel equation
`x² v'' + x v' - (x² + ν²) v = 0` on `(0, ∞)` such that `|v(x)| / x^k` is integrable on `(a, ∞)`
for some `a` and `k` is a multiple of the `K`-Bessel function `K_ν` (`Complex.besselK`, LMFDB
`specialfunction.k_bessel`). This weakens the polynomial growth of `v` and `v'` asked by
`Complex.eq_div_mul_besselK_of_ode_of_ne_zero` to a growth condition on average on `v` alone,
which is what square-integrability gives for the Fourier coefficients of a Maass form. The
Wronskian `W = x (v K_ν' - v' K_ν)` is constant (Abel); integrating `W φ` against the bump
`φ(x) = (x - A)(A + 1 - x)` over `[A, A + 1]` and moving the derivative of `v` onto `x K_ν φ` gives
`W / 6 = ∫_A^{A+1} v (2x K_ν' φ + K_ν φ + x K_ν φ')`, which is at most a constant times
`(A + 1)^{k+1} e^{-A} ∫_a^∞ |v(x)| / x^k dx` by the exponential decay of `K_ν` and `K_ν'`
(`Complex.norm_besselK_le`), so `W = 0`, and `v` is a multiple of `K_ν` by the uniqueness of the
solutions with given initial values (`Complex.eq_zero_of_besselODE`). The other solutions grow
like `eˣ / √x`, the `I`-Bessel part.

In the normalisation of Maass forms: a solution of `y² v'' + (1/4 + R² - κ² y²) v = 0` with
`|v(y)| / y^k` integrable on `(a, ∞)` is a multiple of `√y K_{iR}(κy)`.

## Main results

* `Complex.eq_div_mul_besselK_of_ode_of_integrableOn`: a solution with `|v(x)| / x^k` integrable
  at `∞` is `v(x₀) / K_ν(x₀) · K_ν` for every `x₀ > 0` with `K_ν(x₀) ≠ 0`.
* `Complex.eq_div_mul_sqrt_mul_besselK_of_ode_of_integrableOn`: a solution of the Maass equation
  with `|v(y)| / y^k` integrable at `∞` is `v(y₀) / (√y₀ K_{iR}(κy₀)) · √y K_{iR}(κy)` for every
  `y₀ > 0` with `K_{iR}(κy₀) ≠ 0`.
-/

open Filter MeasureTheory Real Set Topology

namespace Complex

variable {ν R : ℂ} {κ a : ℝ} {v v' v'' : ℝ → ℂ} {x₀ x : ℝ} {k : ℕ}

/-- **The solutions of the modified Bessel equation integrable against a power are the multiples
of `K_ν`**, for every order `ν ∈ ℂ`: a solution `v` of `x² v'' + x v' - (x² + ν²) v = 0` on
`(0, ∞)` such that `|v(x)| / x^k` is integrable on `(a, ∞)` is `v(x₀) / K_ν(x₀) · K_ν` for every
`x₀ > 0` with `K_ν(x₀) ≠ 0` (such an `x₀` exists, `exists_besselK_ne_zero`). The Wronskian
`W = x (v K_ν' - v' K_ν)` is constant, and `W / 6 = ∫_A^{A+1} W φ` for `φ(x) = (x - A)(A + 1 - x)`
is, after an integration by parts, at most a constant times `(A + 1)^{k+1} e^{-A}`, so `W = 0`. -/
lemma eq_div_mul_besselK_of_ode_of_integrableOn (hv : ∀ x, 0 < x → HasDerivAt v (v' x) x)
    (hv' : ∀ x, 0 < x → HasDerivAt v' (v'' x) x)
    (hode : ∀ x : ℝ, 0 < x → (x : ℂ) ^ 2 * v'' x + x * v' x - ((x : ℂ) ^ 2 + ν ^ 2) * v x = 0)
    (hint : IntegrableOn (fun x ↦ ‖v x‖ / x ^ k) (Ioi a)) (hx₀ : 0 < x₀) (hK₀ : besselK ν x₀ ≠ 0)
    (hx : 0 < x) : v x = v x₀ / besselK ν x₀ * besselK ν x := by
  have hK (y : ℝ) (hy : 0 < y) :
      HasDerivAt (fun y : ℝ ↦ besselK ν y) (-besselK (ν + 1) y + ν / y * besselK ν y) y :=
    hasDerivAt_besselK_eq_add ν hy
  let W : ℝ → ℂ := fun y ↦ (y : ℂ) * (v y * (-besselK (ν + 1) y + ν / y * besselK ν y) -
    v' y * besselK ν y)
  have hW (y : ℝ) (hy : 0 < y) : HasDerivAt W 0 y := by
    have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
    refine ((hasDerivAt_id y).ofReal_comp.mul (((hv y hy).mul
      (hasDerivAt_neg_besselK_add ν hy)).sub ((hv' y hy).mul (hK y hy)))).congr_deriv ?_
    refine mul_left_cancel₀ hy' ?_
    simp only [Pi.mul_apply, Pi.sub_apply, id, ofReal_one]
    field_simp
    linear_combination (-besselK ν y) * hode y hy
  have hconst (y : ℝ) (hy : 0 < y) : W y = W 1 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun z hz ↦ (hW z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hW z hz).deriv) hy (mem_Ioi.mpr one_pos)
  have hW₁ : W 1 = 0 := by
    let c₀ : ℝ := 2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand ν 1 t‖
    let c₁ : ℝ := 2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand (ν + 1) 1 t‖
    let D : ℝ := 2 * (c₁ + ‖ν‖ * c₀ + c₀)
    let I : ℝ := ∫ x in Ioi (max a 0), ‖v x‖ / x ^ k
    have hint' : IntegrableOn (fun x ↦ ‖v x‖ / x ^ k) (Ioi (max a 0)) :=
      hint.mono_set (Ioi_subset_Ioi (le_max_left a 0))
    have hbound : ∀ᶠ A in atTop,
        ‖W 1‖ ≤ 6 * (D * rexp 2 * I) * ((A + 1) ^ (k + 1) * rexp (-(A + 1))) := by
      filter_upwards [eventually_gt_atTop (max a 0), eventually_ge_atTop 1] with A haA hA1
      let φ : ℝ → ℝ := fun y ↦ (y - A) * (A + 1 - y)
      let Kd : ℝ → ℂ := fun y ↦ -besselK (ν + 1) y + ν / y * besselK ν y
      let g : ℝ → ℂ := fun y ↦ v y * (((2 * y * φ y : ℝ) : ℂ) * Kd y +
        ((φ y + y * (2 * A + 1 - 2 * y) : ℝ) : ℂ) * besselK ν y)
      let H : ℝ → ℂ := fun y ↦ W 1 * (((y - A) ^ 2 / 2 - (y - A) ^ 3 / 3 : ℝ) : ℂ) +
        (y : ℂ) * v y * besselK ν y * (φ y : ℂ)
      have hA0 : 0 < A := lt_of_le_of_lt (le_max_right a 0) haA
      have hH (y : ℝ) (hy : y ∈ uIcc A (A + 1)) : HasDerivAt H (g y) y := by
        rw [uIcc_of_le (by linarith)] at hy
        have hy0 : 0 < y := by linarith [hy.1]
        have hΦ : HasDerivAt (fun y : ℝ ↦ (y - A) ^ 2 / 2 - (y - A) ^ 3 / 3) (φ y) y := by
          refine ((((hasDerivAt_id y).sub_const A).pow 2).div_const 2 |>.sub
            ((((hasDerivAt_id y).sub_const A).pow 3).div_const 3)).congr_deriv ?_
          simp only [id]
          push_cast
          ring1
        have hφ : HasDerivAt φ (2 * A + 1 - 2 * y) y := by
          refine (((hasDerivAt_id y).sub_const A).mul
            ((hasDerivAt_id y).const_sub (A + 1))).congr_deriv ?_
          simp only [id]
          ring1
        refine ((hΦ.ofReal_comp.const_mul (W 1)).add ((((hasDerivAt_id y).ofReal_comp.mul
          (hv y hy0)).mul (hK y hy0)).mul hφ.ofReal_comp)).congr_deriv ?_
        have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy0.ne'
        rw [← hconst y hy0]
        simp only [W, g, Kd, Pi.mul_apply, id]
        push_cast
        field_simp
        ring1
      have hg : IntervalIntegrable g volume A (A + 1) := by
        refine ContinuousOn.intervalIntegrable fun y hy ↦ ContinuousAt.continuousWithinAt ?_
        rw [uIcc_of_le (by linarith)] at hy
        have hy0 : 0 < y := by linarith [hy.1]
        have hv0 : ContinuousAt v y := (hv y hy0).continuousAt
        have hK0 : ContinuousAt (fun y : ℝ ↦ besselK ν y) y := (hK y hy0).continuousAt
        have hKd : ContinuousAt Kd y := (hasDerivAt_neg_besselK_add ν hy0).continuousAt
        fun_prop
      have hFTC : ∫ y in A..A + 1, g y = W 1 / 6 := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hH hg]
        simp only [H, φ]
        push_cast
        ring1
      have hc₀ : 0 ≤ c₀ := mul_nonneg (by norm_num) (integral_nonneg fun t ↦ norm_nonneg _)
      have hc₁ : 0 ≤ c₁ := mul_nonneg (by norm_num) (integral_nonneg fun t ↦ norm_nonneg _)
      have hD : 0 ≤ D := by
        positivity
      let M : ℝ := D * rexp 2 * ((A + 1) ^ (k + 1) * rexp (-(A + 1)))
      have hM : 0 ≤ M := by
        positivity
      have hpt : ∀ᵐ y ∂volume, y ∈ Ioc A (A + 1) → ‖g y‖ ≤ M * (‖v y‖ / y ^ k) := by
        refine ae_of_all _ fun y hy ↦ ?_
        have hy1 : 1 ≤ y := by linarith [hy.1]
        have hy0 : 0 < y := by linarith
        have hφ0 : 0 ≤ φ y := mul_nonneg (by linarith [hy.1]) (by linarith [hy.2])
        have hφ1 : φ y ≤ 1 := by nlinarith [hy.1, hy.2]
        have hK0 : ‖besselK ν y‖ ≤ rexp (-(y - 1)) * c₀ := norm_besselK_le ν hy1
        have hK1 : ‖besselK (ν + 1) y‖ ≤ rexp (-(y - 1)) * c₁ := norm_besselK_le (ν + 1) hy1
        have hr : ‖ν / (y : ℂ)‖ ≤ ‖ν‖ := by
          rw [norm_div, norm_real, Real.norm_of_nonneg hy0.le]
          exact div_le_self (norm_nonneg ν) hy1
        have hKd : ‖Kd y‖ ≤ rexp (-(y - 1)) * (c₁ + ‖ν‖ * c₀) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_neg, norm_mul]
          nlinarith [mul_le_mul hr hK0 (norm_nonneg _) (norm_nonneg ν)]
        have h1 : ‖((2 * y * φ y : ℝ) : ℂ)‖ ≤ 2 * y := by
          rw [norm_real, Real.norm_of_nonneg (by positivity)]
          nlinarith
        have h2 : ‖((φ y + y * (2 * A + 1 - 2 * y) : ℝ) : ℂ)‖ ≤ 2 * y := by
          rw [norm_real, Real.norm_eq_abs, abs_le]
          constructor <;> nlinarith [hy.1, hy.2]
        have hgy : ‖g y‖ ≤ ‖v y‖ * (y * rexp (-(y - 1)) * D) := by
          simp only [g]
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (norm_nonneg _)
          rw [norm_mul, norm_mul]
          nlinarith [mul_le_mul h1 hKd (norm_nonneg _) (by positivity),
            mul_le_mul h2 hK0 (norm_nonneg _) (by positivity)]
        refine hgy.trans ?_
        have e1 : ‖v y‖ * (y * rexp (-(y - 1)) * D) =
            ‖v y‖ / y ^ k * (D * (y ^ (k + 1) * rexp (-(y - 1)))) := by
          field_simp
          ring1
        have e2 : M * (‖v y‖ / y ^ k) =
            ‖v y‖ / y ^ k * (D * ((A + 1) ^ (k + 1) * rexp (-(A - 1)))) := by
          have he : rexp (-(A - 1)) = rexp 2 * rexp (-(A + 1)) := by
            rw [← Real.exp_add]
            congr 1
            ring1
          simp only [M]
          rw [he]
          ring1
        rw [e1, e2]
        gcongr
        · exact hy.2
        · linarith [hy.1]
      have hMI : IntervalIntegrable (fun y ↦ M * (‖v y‖ / y ^ k)) volume A (A + 1) := by
        refine (hint'.mono_set ?_).intervalIntegrable.const_mul M
        rw [uIcc_of_le (by linarith)]
        exact (Icc_subset_Ioi_iff (by linarith)).mpr haA
      have hle : ∫ y in A..A + 1, M * (‖v y‖ / y ^ k) ≤ M * I := by
        rw [intervalIntegral.integral_const_mul]
        refine mul_le_mul_of_nonneg_left ?_ hM
        rw [intervalIntegral.integral_of_le (by linarith)]
        refine setIntegral_mono_set hint' ?_
          (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi haA.le)).eventuallyLE
        exact (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun y hy ↦
          div_nonneg (norm_nonneg _) (pow_nonneg ((le_max_right a 0).trans (mem_Ioi.mp hy).le) k))
      have h : ‖∫ y in A..A + 1, g y‖ ≤ M * I :=
        (intervalIntegral.norm_integral_le_of_norm_le (by linarith) hpt hMI).trans hle
      rw [hFTC, norm_div, RCLike.norm_ofNat] at h
      simp only [M] at h
      linarith
    have hlim : Tendsto (fun A : ℝ ↦ 6 * (D * rexp 2 * I) * ((A + 1) ^ (k + 1) * rexp (-(A + 1))))
        atTop (𝓝 0) := by
      simpa using ((tendsto_pow_mul_exp_neg_atTop_nhds_zero (k + 1)).comp
        (tendsto_atTop_add_const_right atTop 1 tendsto_id)).const_mul (6 * (D * rexp 2 * I))
    exact norm_le_zero_iff.mp (ge_of_tendsto hlim hbound)
  have hW₀ : v x₀ * (-besselK (ν + 1) x₀ + ν / x₀ * besselK ν x₀) - v' x₀ * besselK ν x₀ = 0 :=
    (mul_eq_zero.mp <| (hconst x₀ hx₀).trans hW₁).resolve_left (ofReal_ne_zero.mpr hx₀.ne')
  refine sub_eq_zero.mp <| eq_zero_of_besselODE (ν := ν)
    (v := fun y ↦ v y - v x₀ / besselK ν x₀ * besselK ν y)
    (v' := fun y ↦ v' y - v x₀ / besselK ν x₀ * (-besselK (ν + 1) y + ν / y * besselK ν y))
    (v'' := fun y ↦ v'' y - v x₀ / besselK ν x₀ *
      (besselK ν y + besselK (ν + 1) y / y + (ν ^ 2 - ν) / (y : ℂ) ^ 2 * besselK ν y))
    (fun y hy ↦ (hv y hy).sub ((hK y hy).const_mul _))
    (fun y hy ↦ (hv' y hy).sub ((hasDerivAt_neg_besselK_add ν hy).const_mul _)) (fun y hy ↦ ?_)
    hx₀ ?_ ?_ hx
  · have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
    field_simp
    linear_combination besselK ν x₀ * hode y hy
  · field_simp
    ring1
  · have hx₀' : (x₀ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx₀.ne'
    field_simp at hW₀ ⊢
    linear_combination -hW₀

/-- **The solutions of the Maass equation integrable against a power are the multiples of
`√y K_{iR}(κy)`**: for `κ > 0` and `R ∈ ℂ`, a solution `v` of
`y² v'' + (1/4 + R² - κ² y²) v = 0` on `(0, ∞)` (the equation of the `n`-th Fourier coefficient of
a Maass form with Laplace eigenvalue `1/4 + R²`, for `κ = 2π|n|`) such that `|v(y)| / y^k` is
integrable on `(a, ∞)` is `v(y₀) / (√y₀ K_{iR}(κy₀)) · √y K_{iR}(κy)` for every `y₀ > 0` with
`K_{iR}(κy₀) ≠ 0`. The function `t ↦ v(t/κ) / √(t/κ)` solves the modified Bessel equation of order
`iR` and inherits the integrability (`eq_div_mul_besselK_of_ode_of_integrableOn`). -/
lemma eq_div_mul_sqrt_mul_besselK_of_ode_of_integrableOn (hκ : 0 < κ)
    (hv : ∀ x, 0 < x → HasDerivAt v (v' x) x) (hv' : ∀ x, 0 < x → HasDerivAt v' (v'' x) x)
    (hode : ∀ x : ℝ, 0 < x → (x : ℂ) ^ 2 * v'' x +
      (1 / 4 + R ^ 2 - ((κ * x : ℝ) : ℂ) ^ 2) * v x = 0)
    (hint : IntegrableOn (fun x ↦ ‖v x‖ / x ^ k) (Ioi a)) (hx₀ : 0 < x₀)
    (hK : besselK (I * R) (κ * x₀) ≠ 0) (hx : 0 < x) :
    v x = v x₀ / (√x₀ * besselK (I * R) (κ * x₀)) * (√x * besselK (I * R) (κ * x)) := by
  let ρ : ℝ → ℝ := fun t ↦ (√(t / κ))⁻¹
  have hρ (t : ℝ) (ht : 0 < t) : HasDerivAt ρ (-ρ t / (2 * t)) t :=
    hasDerivAt_inv_sqrt_div hκ ht
  have hs (t : ℝ) : HasDerivAt (fun t : ℝ ↦ t / κ) κ⁻¹ t := by
    simpa using (hasDerivAt_id t).div_const κ
  let u : ℝ → ℂ := fun t ↦ (ρ t : ℂ) * v (t / κ)
  let u' : ℝ → ℂ := fun t ↦ ((-ρ t / (2 * t) : ℝ) : ℂ) * v (t / κ) +
    ((ρ t / κ : ℝ) : ℂ) * v' (t / κ)
  let u'' : ℝ → ℂ := fun t ↦ ((3 * ρ t / (4 * t ^ 2) : ℝ) : ℂ) * v (t / κ) -
    ((ρ t / (t * κ) : ℝ) : ℂ) * v' (t / κ) + ((ρ t / κ ^ 2 : ℝ) : ℂ) * v'' (t / κ)
  have hu (t : ℝ) (ht : 0 < t) : HasDerivAt u (u' t) t := by
    refine ((hρ t ht).ofReal_comp.mul ((hv (t / κ) (div_pos ht hκ)).scomp t (hs t))).congr_deriv ?_
    simp only [u', Function.comp_apply, real_smul]
    push_cast
    ring1
  have hu' (t : ℝ) (ht : 0 < t) : HasDerivAt u' (u'' t) t := by
    have h1 : HasDerivAt (fun t ↦ -ρ t / (2 * t)) (3 * ρ t / (4 * t ^ 2)) t := by
      refine ((hρ t ht).neg.div ((hasDerivAt_id t).const_mul 2)
        (mul_ne_zero two_ne_zero ht.ne')).congr_deriv ?_
      simp only [id, Pi.neg_apply]
      field_simp
      ring1
    have h2 : HasDerivAt (fun t ↦ ρ t / κ) (-ρ t / (2 * t) / κ) t := (hρ t ht).div_const κ
    refine ((h1.ofReal_comp.mul ((hv (t / κ) (div_pos ht hκ)).scomp t (hs t))).add
      (h2.ofReal_comp.mul ((hv' (t / κ) (div_pos ht hκ)).scomp t (hs t)))).congr_deriv ?_
    have hκ' : (κ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hκ.ne'
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    simp only [u'', Function.comp_apply, real_smul]
    push_cast
    field_simp
    ring1
  have hode' (t : ℝ) (ht : 0 < t) :
      (t : ℂ) ^ 2 * u'' t + t * u' t - ((t : ℂ) ^ 2 + (I * R) ^ 2) * u t = 0 := by
    have hκ' : (κ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hκ.ne'
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have e : (t : ℂ) ^ 2 * u'' t + t * u' t - ((t : ℂ) ^ 2 + (I * R) ^ 2) * u t =
        (ρ t : ℂ) * (((t / κ : ℝ) : ℂ) ^ 2 * v'' (t / κ) +
          (1 / 4 + R ^ 2 - ((κ * (t / κ) : ℝ) : ℂ) ^ 2) * v (t / κ)) := by
      simp only [u', u'', mul_pow, I_sq]
      push_cast
      field_simp
      ring1
    rw [e, hode (t / κ) (div_pos ht hκ), mul_zero]
  have hb : 0 < κ * max a 1 := mul_pos hκ (lt_max_of_lt_right one_pos)
  have hint' : IntegrableOn (fun t ↦ (κ ^ k)⁻¹ * (‖v (κ⁻¹ * t)‖ / (κ⁻¹ * t) ^ k))
      (Ioi (κ * max a 1)) := by
    refine ((integrableOn_Ioi_comp_mul_left_iff (fun x ↦ ‖v x‖ / x ^ k) _
      (inv_pos.mpr hκ)).mpr ?_).const_mul _
    rw [← mul_assoc, inv_mul_cancel₀ hκ.ne', one_mul]
    exact hint.mono_set (Ioi_subset_Ioi (le_max_left a 1))
  have hU : IntegrableOn (fun t ↦ ‖u t‖ / t ^ k) (Ioi (κ * max a 1)) := by
    refine hint'.mono' (ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t ht ↦ ?_))
    · have ht0 : 0 < t := hb.trans ht
      exact ((hu t ht0).continuousAt.norm.div (continuous_pow k).continuousAt
        (pow_ne_zero k ht0.ne')).continuousWithinAt
    · have ht0 : 0 < t := hb.trans ht
      have hκt : κ ≤ t := (le_mul_of_one_le_right hκ.le (le_max_right a 1)).trans (mem_Ioi.mp ht).le
      have hρ1 : ρ t ≤ 1 :=
        inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr ((one_le_div hκ).mpr hκt))
      have hρ0 : 0 ≤ ρ t := inv_nonneg.mpr (Real.sqrt_nonneg _)
      have e : (κ ^ k)⁻¹ * (‖v (κ⁻¹ * t)‖ / (κ⁻¹ * t) ^ k) = ‖v (t / κ)‖ / t ^ k := by
        rw [← div_eq_inv_mul t κ, div_pow]
        field_simp
      rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (pow_nonneg ht0.le k)), e]
      refine div_le_div_of_nonneg_right ?_ (pow_nonneg ht0.le k)
      simp only [u]
      rw [norm_mul, norm_real, Real.norm_of_nonneg hρ0]
      exact mul_le_of_le_one_left (norm_nonneg _) hρ1
  have key : u (κ * x) = u (κ * x₀) / besselK (I * R) (κ * x₀) * besselK (I * R) (κ * x) :=
    eq_div_mul_besselK_of_ode_of_integrableOn hu hu' hode' hU (mul_pos hκ hx₀) hK (mul_pos hκ hx)
  have hsx : ((√x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
  simp only [u, ρ] at key
  push_cast at key ⊢
  field_simp at key ⊢
  linear_combination key

end Complex
