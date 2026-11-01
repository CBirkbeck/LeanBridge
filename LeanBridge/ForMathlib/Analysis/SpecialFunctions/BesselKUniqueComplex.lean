import LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselKNonvanishing
import Mathlib.Analysis.ODE.ExistUnique

/-!
# The decaying solutions of the modified Bessel equation of complex order

For every order `ν ∈ ℂ`, the solutions of the modified Bessel equation
`x² u'' + x u' - (x² + ν²) u = 0` on `(0, ∞)` which grow at most polynomially at `∞`, with their
derivatives, are the multiples of the `K`-Bessel function `K_ν` (`Complex.besselK`, LMFDB
`specialfunction.k_bessel`). This extends `Complex.eq_div_mul_besselK_of_ode` from real orders,
where `K_ν` has no zero, to complex orders such as the order `iR` of the Fourier coefficients of a
Maass form of spectral parameter `R`, where `K_{iR}` has zeros. The Wronskian `x (u K_ν' - u' K_ν)`
is constant (Abel) and tends to `0` at `∞`, so it vanishes; at a point `x₀ > 0` with
`K_ν(x₀) ≠ 0` (`Complex.exists_besselK_ne_zero`), `u - (u(x₀)/K_ν(x₀)) K_ν` and its derivative
vanish, so it vanishes on `(0, ∞)` by the uniqueness of solutions of linear differential equations
(Grönwall). The growth is only needed near `∞`.

In the normalisation of Maass forms: the `n`-th Fourier coefficient `v(y)` of a Maass form of
Laplace eigenvalue `1/4 + R²` solves `y² v'' + (1/4 + R² - κ² y²) v = 0` with `κ = 2π|n|`, and its
solutions of polynomial growth are the multiples of `√y K_{iR}(κy)`.

## Main results

* `Complex.eq_zero_of_besselODE`: a solution of the modified Bessel equation vanishing with its
  derivative at a point of `(0, ∞)` vanishes on `(0, ∞)`.
* `Complex.eq_div_mul_besselK_of_ode_of_ne_zero`: a solution of polynomial growth is
  `u(x₀) / K_ν(x₀) · K_ν` for every `x₀ > 0` with `K_ν(x₀) ≠ 0`.
* `Complex.eq_div_mul_sqrt_mul_besselK_of_ode`: a solution of polynomial growth of the Maass
  equation is `v(y₀) / (√y₀ K_{iR}(κy₀)) · √y K_{iR}(κy)` for every `y₀ > 0` with
  `K_{iR}(κy₀) ≠ 0`.
-/

open Filter MeasureTheory Real Set Topology

namespace Complex

variable {ν R : ℂ} {κ : ℝ} {v v' v'' : ℝ → ℂ} {x₀ x C : ℝ} {N : ℕ}

/-- **Uniqueness of the solutions of the modified Bessel equation**: a solution `v` of
`x² v'' + x v' - (x² + ν²) v = 0` on `(0, ∞)` with `v(x₀) = v'(x₀) = 0` at some `x₀ > 0` vanishes on
`(0, ∞)`. On every compact subinterval of `(0, ∞)` the equation is a linear system with bounded
coefficients, whose solutions are determined by their initial values (Grönwall). -/
lemma eq_zero_of_besselODE (hv : ∀ x, 0 < x → HasDerivAt v (v' x) x)
    (hv' : ∀ x, 0 < x → HasDerivAt v' (v'' x) x)
    (hode : ∀ x : ℝ, 0 < x → (x : ℂ) ^ 2 * v'' x + x * v' x - ((x : ℂ) ^ 2 + ν ^ 2) * v x = 0)
    (hx₀ : 0 < x₀) (h₀ : v x₀ = 0) (h₀' : v' x₀ = 0) (hx : 0 < x) : v x = 0 := by
  set a : ℝ := min x x₀ / 2 with ha_def
  have ha : 0 < a := by
    positivity
  let V : ℝ → ℂ × ℂ → ℂ × ℂ := fun t w ↦ (w.2, -(t : ℂ)⁻¹ * w.2 + (1 + ν ^ 2 / (t : ℂ) ^ 2) * w.1)
  have hV (t : ℝ) (ht : t ∈ Ioo a (max x x₀ + 1)) :
      LipschitzOnWith (2 + a⁻¹ + ‖ν‖ ^ 2 / a ^ 2).toNNReal (V t) univ := by
    refine LipschitzOnWith.of_dist_le_mul fun w _ w' _ ↦ ?_
    have ht0 : 0 < t := ha.trans ht.1
    have h1 : ‖(t : ℂ)⁻¹‖ ≤ a⁻¹ := by
      rw [norm_inv, norm_real, Real.norm_of_nonneg ht0.le]
      exact inv_anti₀ ha ht.1.le
    have h2 : ‖1 + ν ^ 2 / (t : ℂ) ^ 2‖ ≤ 1 + ‖ν‖ ^ 2 / a ^ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_one, norm_div, norm_pow, norm_pow, norm_real, Real.norm_of_nonneg ht0.le]
      gcongr
      exact ht.1.le
    have hp : ‖w.1 - w'.1‖ ≤ dist w w' := (dist_eq_norm w.1 w'.1).symm.trans_le (le_max_left _ _)
    have hq : ‖w.2 - w'.2‖ ≤ dist w w' := (dist_eq_norm w.2 w'.2).symm.trans_le (le_max_right _ _)
    have hK : 1 ≤ 2 + a⁻¹ + ‖ν‖ ^ 2 / a ^ 2 := by
      have h3 : 0 ≤ ‖ν‖ ^ 2 / a ^ 2 := by
        positivity
      linarith [inv_pos.mpr ha]
    have e : -(t : ℂ)⁻¹ * w.2 + (1 + ν ^ 2 / (t : ℂ) ^ 2) * w.1 -
        (-(t : ℂ)⁻¹ * w'.2 + (1 + ν ^ 2 / (t : ℂ) ^ 2) * w'.1) =
          -(t : ℂ)⁻¹ * (w.2 - w'.2) + (1 + ν ^ 2 / (t : ℂ) ^ 2) * (w.1 - w'.1) := by
      ring1
    rw [Prod.dist_eq, Real.coe_toNNReal _ (zero_le_one.trans hK), dist_eq_norm, dist_eq_norm]
    refine max_le (hq.trans (le_mul_of_one_le_left dist_nonneg hK)) ?_
    simp only [V]
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_neg]
    nlinarith [norm_nonneg (w.2 - w'.2), norm_nonneg (w.1 - w'.1), norm_nonneg ((t : ℂ)⁻¹),
      norm_nonneg (1 + ν ^ 2 / (t : ℂ) ^ 2), (dist_nonneg : 0 ≤ dist w w')]
  have hsol (t : ℝ) (ht : t ∈ Ioo a (max x x₀ + 1)) :
      HasDerivAt (fun t ↦ (v t, v' t)) (V t (v t, v' t)) t ∧ (v t, v' t) ∈ univ := by
    have ht0 : 0 < t := ha.trans ht.1
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    refine ⟨((hv t ht0).prodMk (hv' t ht0)).congr_deriv <| Prod.ext rfl ?_, mem_univ _⟩
    simp only [V]
    field_simp
    linear_combination hode t ht0
  have hzero (t : ℝ) (_ : t ∈ Ioo a (max x x₀ + 1)) :
      HasDerivAt (fun _ ↦ (0 : ℂ × ℂ)) (V t 0) t ∧ (0 : ℂ × ℂ) ∈ univ := by
    refine ⟨(hasDerivAt_const t (0 : ℂ × ℂ)).congr_deriv ?_, mem_univ _⟩
    exact Prod.ext (by simp [V]) (by simp [V])
  have hmem (y : ℝ) (hyx : y ≤ max x x₀) (hya : min x x₀ ≤ y) : y ∈ Ioo a (max x x₀ + 1) :=
    ⟨by linarith, by linarith⟩
  have h : (v x, v' x) = (0 : ℂ × ℂ) := ODE_solution_unique_of_mem_Ioo hV
    (hmem x₀ (le_max_right _ _) (min_le_right _ _)) hsol hzero (by simp [h₀, h₀'])
    (hmem x (le_max_left _ _) (min_le_left _ _))
  exact congrArg Prod.fst h

/-- **The decaying solutions of the modified Bessel equation are the multiples of `K_ν`**, for every
order `ν ∈ ℂ`: a solution `v` of `x² v'' + x v' - (x² + ν²) v = 0` on `(0, ∞)` which grows at most
polynomially at `∞`, with its derivative, is `v(x₀) / K_ν(x₀) · K_ν` for every `x₀ > 0` with
`K_ν(x₀) ≠ 0` (such an `x₀` exists, `exists_besselK_ne_zero`). The Wronskian
`x (v K_ν' - v' K_ν)` is constant (Abel) and tends to `0` at `∞` (`K_ν` and `K_ν'` decay
exponentially, `norm_besselK_le`), so it vanishes, and `v - v(x₀) / K_ν(x₀) · K_ν` vanishes with
its derivative at `x₀`, hence everywhere (`eq_zero_of_besselODE`). -/
lemma eq_div_mul_besselK_of_ode_of_ne_zero (hv : ∀ x, 0 < x → HasDerivAt v (v' x) x)
    (hv' : ∀ x, 0 < x → HasDerivAt v' (v'' x) x)
    (hode : ∀ x : ℝ, 0 < x → (x : ℂ) ^ 2 * v'' x + x * v' x - ((x : ℂ) ^ 2 + ν ^ 2) * v x = 0)
    (hv₁ : ∀ᶠ x in atTop, ‖v x‖ ≤ C * x ^ N) (hv₂ : ∀ᶠ x in atTop, ‖v' x‖ ≤ C * x ^ N)
    (hx₀ : 0 < x₀) (hK₀ : besselK ν x₀ ≠ 0) (hx : 0 < x) :
    v x = v x₀ / besselK ν x₀ * besselK ν x := by
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
  have hbound : ∀ᶠ y in atTop, ‖W y‖ ≤ C * ((2⁻¹ * ∫ t in Ioi 0,
      ‖besselKIntegrand (ν + 1) 1 t‖) + ‖ν‖ * (2⁻¹ * ∫ t in Ioi 0,
        ‖besselKIntegrand ν 1 t‖) + 2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand ν 1 t‖) *
          rexp 1 * (y ^ (N + 1) * rexp (-y)) := by
    filter_upwards [eventually_ge_atTop 1, hv₁, hv₂] with y hy hy₁ hy₂
    have hy₀ : 0 < y := by
      linarith
    have hC : 0 ≤ C := by
      by_contra! hC
      nlinarith [norm_nonneg (v y), pow_pos hy₀ N]
    have h₀ : ‖besselK ν y‖ ≤ rexp (-(y - 1)) * (2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand ν 1 t‖) :=
      norm_besselK_le ν hy
    have h₁ : ‖besselK (ν + 1) y‖ ≤
        rexp (-(y - 1)) * (2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand (ν + 1) 1 t‖) :=
      norm_besselK_le (ν + 1) hy
    have hr : ‖ν / (y : ℂ)‖ ≤ ‖ν‖ := by
      rw [norm_div, norm_real, Real.norm_of_nonneg hy₀.le]
      exact div_le_self (norm_nonneg ν) hy
    have hd : ‖-besselK (ν + 1) y + ν / y * besselK ν y‖ ≤
        rexp (-(y - 1)) * ((2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand (ν + 1) 1 t‖) +
          ‖ν‖ * (2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand ν 1 t‖)) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, norm_mul]
      nlinarith [mul_le_mul hr h₀ (norm_nonneg _) (norm_nonneg ν)]
    have hW' : ‖W y‖ ≤ y * (C * y ^ N * (rexp (-(y - 1)) *
        ((2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand (ν + 1) 1 t‖) +
          ‖ν‖ * (2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand ν 1 t‖))) + C * y ^ N *
            (rexp (-(y - 1)) * (2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand ν 1 t‖))) := by
      simp only [W]
      rw [norm_mul, norm_real, Real.norm_of_nonneg hy₀.le]
      refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) hy₀.le
      rw [norm_mul, norm_mul]
      gcongr
    have he : rexp (-(y - 1)) = rexp 1 * rexp (-y) := by
      rw [← Real.exp_add]
      congr 1
      ring1
    rw [he] at hW'
    refine hW'.trans (le_of_eq ?_)
    ring1
  have hlim : Tendsto W atTop (𝓝 0) := by
    refine squeeze_zero_norm' hbound ?_
    simpa using (tendsto_pow_mul_exp_neg_atTop_nhds_zero (N + 1)).const_mul
      (C * ((2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand (ν + 1) 1 t‖) +
        ‖ν‖ * (2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand ν 1 t‖) +
          2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand ν 1 t‖) * rexp 1)
  have hW₁ : W 1 = 0 := tendsto_nhds_unique (tendsto_const_nhds.congr'
    ((eventually_gt_atTop 0).mono fun y hy ↦ (hconst y hy).symm)) hlim
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

lemma hasDerivAt_inv_sqrt_div (hκ : 0 < κ) (hx : 0 < x) :
    HasDerivAt (fun t ↦ (√(t / κ))⁻¹) (-(√(x / κ))⁻¹ / (2 * x)) x := by
  have h1 : 0 < x / κ := div_pos hx hκ
  have hsq : √(x / κ) ^ 2 = x / κ := Real.sq_sqrt h1.le
  refine (((Real.hasDerivAt_sqrt h1.ne').comp x ((hasDerivAt_id x).div_const κ)).inv
    (Real.sqrt_pos.mpr h1).ne').congr_deriv ?_
  simp only [Function.comp_apply, id, hsq]
  field_simp

/-- **The decaying solutions of the Maass equation are the multiples of `√y K_{iR}(κy)`**: for
`κ > 0` and `R ∈ ℂ`, a solution `v` of `y² v'' + (1/4 + R² - κ² y²) v = 0` on `(0, ∞)` (the equation
of the `n`-th Fourier coefficient `v(y)` of a Maass form `∑ v_n(y) e^{2πinx}` with Laplace
eigenvalue `1/4 + R²`, for `κ = 2π|n|`) which grows at most polynomially at `∞`, with its
derivative, is `v(y₀) / (√y₀ K_{iR}(κy₀)) · √y K_{iR}(κy)` for every `y₀ > 0` with
`K_{iR}(κy₀) ≠ 0`. The function `t ↦ v(t/κ) / √(t/κ)` solves the modified Bessel equation of order
`iR` (`eq_div_mul_besselK_of_ode_of_ne_zero`). -/
lemma eq_div_mul_sqrt_mul_besselK_of_ode (hκ : 0 < κ) (hv : ∀ x, 0 < x → HasDerivAt v (v' x) x)
    (hv' : ∀ x, 0 < x → HasDerivAt v' (v'' x) x)
    (hode : ∀ x : ℝ, 0 < x → (x : ℂ) ^ 2 * v'' x +
      (1 / 4 + R ^ 2 - ((κ * x : ℝ) : ℂ) ^ 2) * v x = 0) (hv₁ : ∀ᶠ x in atTop, ‖v x‖ ≤ C * x ^ N)
    (hv₂ : ∀ᶠ x in atTop, ‖v' x‖ ≤ C * x ^ N) (hx₀ : 0 < x₀) (hK : besselK (I * R) (κ * x₀) ≠ 0)
    (hx : 0 < x) :
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
  have hρ0 (t : ℝ) : 0 ≤ ρ t := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hρ1 (t : ℝ) (ht : κ ≤ t) : ρ t ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr ((one_le_div hκ).mpr ht))
  have hev :
      ∀ᶠ t in atTop, ‖v (t / κ)‖ ≤ |C| * (t / κ) ^ N ∧ ‖v' (t / κ)‖ ≤ |C| * (t / κ) ^ N := by
    filter_upwards [(tendsto_id.atTop_div_const hκ).eventually (hv₁.and hv₂),
      eventually_ge_atTop 0] with t ht ht0
    have hpow : 0 ≤ (t / κ) ^ N := pow_nonneg (div_nonneg ht0 hκ.le) N
    exact ⟨ht.1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hpow),
      ht.2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hpow)⟩
  have e (t : ℝ) : (1 + κ⁻¹) * |C| / κ ^ N * t ^ N = (1 + κ⁻¹) * (|C| * (t / κ) ^ N) := by
    rw [div_pow]
    field_simp
  have hb₁ : ∀ᶠ t in atTop, ‖u t‖ ≤ (1 + κ⁻¹) * |C| / κ ^ N * t ^ N := by
    filter_upwards [hev, eventually_ge_atTop κ] with t ht hκt
    rw [e, norm_mul, norm_real, Real.norm_of_nonneg (hρ0 t)]
    nlinarith [hρ1 t hκt, norm_nonneg (v (t / κ)), inv_nonneg.mpr hκ.le, hρ0 t]
  have hb₂ : ∀ᶠ t in atTop, ‖u' t‖ ≤ (1 + κ⁻¹) * |C| / κ ^ N * t ^ N := by
    filter_upwards [hev, eventually_ge_atTop κ, eventually_ge_atTop 1] with t ht hκt ht1
    have hc1 : ‖((-ρ t / (2 * t) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg (hρ0 t),
        abs_of_pos (by linarith), div_le_one (by linarith)]
      linarith [hρ1 t hκt]
    have hc2 : ‖((ρ t / κ : ℝ) : ℂ)‖ ≤ κ⁻¹ := by
      rw [norm_real, Real.norm_of_nonneg (div_nonneg (hρ0 t) hκ.le), div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.mpr hκ.le) (hρ1 t hκt)
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    nlinarith [norm_nonneg (v (t / κ)), norm_nonneg (v' (t / κ)), inv_nonneg.mpr hκ.le,
      norm_nonneg ((-ρ t / (2 * t) : ℝ) : ℂ), norm_nonneg ((ρ t / κ : ℝ) : ℂ)]
  have key : u (κ * x) = u (κ * x₀) / besselK (I * R) (κ * x₀) * besselK (I * R) (κ * x) :=
    eq_div_mul_besselK_of_ode_of_ne_zero hu hu' hode' hb₁ hb₂ (mul_pos hκ hx₀) hK (mul_pos hκ hx)
  have hsx : ((√x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
  simp only [u, ρ] at key
  push_cast at key ⊢
  field_simp at key ⊢
  linear_combination key

end Complex
