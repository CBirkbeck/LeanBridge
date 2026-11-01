import LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselKUniqueComplex
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.FourierSeries
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.UpperHalfPlane
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# The differential equation of the Fourier coefficients of a Maass form

Let `f` be a smooth function on the upper half-plane with `f(z + 1) = f(z)` and
`(Δ + λ) f = 0` for the hyperbolic Laplacian `Δ = y² (∂²/∂x² + ∂²/∂y²)`
(`UpperHalfPlane.hyperbolicLaplacian`), such as a Maass form on `Γ₀(N)` with eigenvalue `λ`. Its
`n`-th Fourier coefficient `a_n(y) = ∫_0^1 f(t + iy) e^{-2πint} dt` (the coefficient of the
expansion `UpperHalfPlane.hasSum_fourierCoeffOn_mul_exp`) is twice differentiable, by
differentiation under the integral sign, and solves `y² a_n'' + (λ - 4π²n²y²) a_n = 0`, by two
integrations by parts in `x`. For `λ = 1/4 + R²` and `n ≠ 0`, if `a_n` and `a_n'` grow at most
polynomially, then `a_n(y)` is a multiple of `√y K_{iR}(2π|n|y)`
(`Complex.eq_div_mul_sqrt_mul_besselK_of_ode`): this is the `n`-th term of the Fourier expansion of
a Maass form (LMFDB `mf.maass.mwf.fourierexpansion`, `mf.maass.mwf.coefficients`). The growth
bound is a hypothesis: it is not part of the definition of Maass forms, which only asks for
square-integrability on `Γ₀(N) \ ℍ`, and it is not derived from it here.

## Main results

* `UpperHalfPlane.fourierCoeff_ode`: the differential equation of `a_n`.
* `UpperHalfPlane.fourierCoeff_eq_div_mul_sqrt_mul_besselK`: under a polynomial growth bound,
  `a_n(y) = c_n √y K_{iR}(2π|n|y)`.
-/

open Filter Function MeasureTheory Real Set Topology

open scoped ContDiff

namespace UpperHalfPlane

variable {f G : ℂ → ℂ} {y : ℝ} (n : ℤ)

lemma continuous_comp_add_mul_I (hG : ContDiffOn ℝ ∞ G {z | 0 < z.im}) (hy : 0 < y) :
    Continuous fun t : ℝ ↦ G (t + y * Complex.I) :=
  hG.continuousOn.comp_continuous (by fun_prop) fun t ↦ by simpa using hy

lemma hasDerivAt_comp_add_mul_I_im (hG : ContDiffOn ℝ ∞ G {z | 0 < z.im}) (t : ℝ) (hy : 0 < y) :
    HasDerivAt (fun s : ℝ ↦ G (t + s * Complex.I)) (fderiv ℝ G (t + y * Complex.I) Complex.I)
      y := by
  have hz : 0 < ((t : ℂ) + y * Complex.I).im := by
    simpa using hy
  have h1 : HasDerivAt (fun s : ℝ ↦ (t : ℂ) + s * Complex.I) Complex.I y := by
    simpa using ((hasDerivAt_id y).ofReal_comp.mul_const Complex.I).const_add (t : ℂ)
  exact ((hG.differentiableOn (by simp)).differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds hz)).hasFDerivAt.comp_hasDerivAt y h1

lemma hasDerivAt_integral_comp_add_mul_I (hG : ContDiffOn ℝ ∞ G {z | 0 < z.im}) {e : ℝ → ℂ}
    (he : Continuous e) (hy : 0 < y) :
    HasDerivAt (fun s : ℝ ↦ ∫ t in (0 : ℝ)..1, e t * G (t + s * Complex.I))
      (∫ t in (0 : ℝ)..1, e t * fderiv ℝ G (t + y * Complex.I) Complex.I) y := by
  let K : Set ℂ := (fun q : ℝ × ℝ ↦ (q.1 : ℂ) + q.2 * Complex.I) '' (Icc 0 1 ×ˢ Icc (y / 2) (2 * y))
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hKH : K ⊆ {z | 0 < z.im} := by
    rintro _ ⟨q, hq, rfl⟩
    have h2 : y / 2 ≤ q.2 := hq.2.1
    simp only [mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re]
    linarith
  have hGI : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ G w Complex.I) {z | 0 < z.im} :=
    contDiffOn_fderiv_apply Complex.I hG
  rcases hK.exists_bound_of_continuousOn (hGI.continuousOn.mono hKH) with ⟨M, hM⟩
  rcases (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn he.continuousOn with
    ⟨E, hE⟩
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (s t : ℝ) ↦ e t * G (t + s * Complex.I))
    (F' := fun (s t : ℝ) ↦ e t * fderiv ℝ G (t + s * Complex.I) Complex.I) (bound := fun _ ↦ E * M)
    (Icc_mem_nhds (half_lt_self hy) (by linarith : y < 2 * y)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [eventually_gt_nhds hy] with s hs
    exact (he.mul (continuous_comp_add_mul_I hG hs)).aestronglyMeasurable
  · exact (he.mul (continuous_comp_add_mul_I hG hy)).intervalIntegrable _ _
  · exact (he.mul (continuous_comp_add_mul_I hGI hy)).aestronglyMeasurable
  · refine .of_forall fun t ht s hs ↦ ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at ht
      exact Ioc_subset_Icc_self ht
    rw [norm_mul]
    exact mul_le_mul (hE t ht') (hM _ ⟨(t, s), ⟨ht', hs⟩, rfl⟩) (norm_nonneg _)
      ((norm_nonneg _).trans (hE t ht'))
  · exact intervalIntegrable_const
  · refine .of_forall fun t ht s hs ↦ ?_
    exact (hasDerivAt_comp_add_mul_I_im hG t (by linarith [hs.1])).const_mul (e t)

lemma integral_exp_mul_deriv_deriv {g g' g'' : ℝ → ℂ} (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : ∀ t, HasDerivAt g' (g'' t) t) (hc : Continuous g'') (hp : g 1 = g 0)
    (hp' : g' 1 = g' 0) : ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) * g'' t =
      -(2 * π * n) ^ 2 * ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) * g t := by
  have he (t : ℝ) : HasDerivAt (fun t : ℝ ↦ Complex.exp (-(2 * π * Complex.I * n) * t))
      (-(2 * π * Complex.I * n) * Complex.exp (-(2 * π * Complex.I * n) * t)) t := by
    simpa [mul_comm] using ((hasDerivAt_id t).ofReal_comp.const_mul
      (-(2 * π * Complex.I * n))).cexp
  have he1 : Complex.exp (-(2 * π * Complex.I * n) * (1 : ℝ)) = 1 := by
    have h : -(2 * π * Complex.I * n) * ((1 : ℝ) : ℂ) = ((-n : ℤ) : ℂ) * (2 * π * Complex.I) := by
      push_cast
      ring1
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hec : Continuous fun t : ℝ ↦
      -(2 * π * Complex.I * n) * Complex.exp (-(2 * π * Complex.I * n) * t) := by
    fun_prop
  have hg'c : Continuous g' := continuous_iff_continuousAt.mpr fun t ↦ (hg' t).continuousAt
  have h3 (φ : ℝ → ℂ) : ∫ t in (0 : ℝ)..1,
      -(2 * π * Complex.I * n) * Complex.exp (-(2 * π * Complex.I * n) * t) * φ t =
        -(2 * π * Complex.I * n) * ∫ t in (0 : ℝ)..1,
          Complex.exp (-(2 * π * Complex.I * n) * t) * φ t := by
    rw [← intervalIntegral.integral_const_mul]
    simp only [mul_assoc]
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t _ ↦ he t) (fun t _ ↦ hg' t)
    (hec.intervalIntegrable _ _) (hc.intervalIntegrable _ _), h3,
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t _ ↦ he t) (fun t _ ↦ hg t)
    (hec.intervalIntegrable _ _) (hg'c.intervalIntegrable _ _), h3, he1, hp, hp',
    Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  linear_combination (4 * π ^ 2 * n ^ 2 * ∫ t in (0 : ℝ)..1,
    Complex.exp (-(2 * π * Complex.I * n) * t) * g t) * Complex.I_sq

/-- **The differential equation of the Fourier coefficients** of a smooth function `f` on the
upper half-plane with `f(z + 1) = f(z)` and `(Δ + λ) f = 0`: the `n`-th Fourier coefficient
`a_n(y) = ∫_0^1 f(t + iy) e^{-2πint} dt` satisfies `y² a_n''(y) + (λ - 4π²n²y²) a_n(y) = 0`, where
`a_n''(y) = ∫_0^1 ∂²f/∂y²(t + iy) e^{-2πint} dt` is its second derivative
(`hasDerivAt_integral_comp_add_mul_I`). -/
lemma fourierCoeff_ode (hf : ContDiffOn ℝ ∞ f {z | 0 < z.im})
    (hper : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z) {eigenvalue : ℂ}
    (hΔ : ∀ z : ℂ, 0 < z.im → hyperbolicLaplacian f z + eigenvalue * f z = 0) (hy : 0 < y) :
    (y : ℂ) ^ 2 * (∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) *
      fderiv ℝ (fun w ↦ fderiv ℝ f w Complex.I) (t + y * Complex.I) Complex.I) +
        (eigenvalue - ((2 * π * n * y : ℝ) : ℂ) ^ 2) *
          ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) * f (t + y * Complex.I) =
      0 := by
  have hpos (t : ℝ) : 0 < ((t : ℂ) + y * Complex.I).im := by
    simpa using hy
  have him (t : ℝ) : ((t : ℂ) + y * Complex.I).im = y := by
    simp
  have e1 : ((1 : ℝ) : ℂ) + y * Complex.I = ((0 : ℝ) : ℂ) + y * Complex.I + 1 := by
    push_cast
    ring1
  have hf1 : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ f w 1) {z | 0 < z.im} := contDiffOn_fderiv_apply 1 hf
  have hx : ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) *
      fderiv ℝ (fun w ↦ fderiv ℝ f w 1) (t + y * Complex.I) 1 = -(2 * π * n) ^ 2 *
        ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) * f (t + y * Complex.I) :=
    integral_exp_mul_deriv_deriv n (hasDerivAt_comp_add_mul_I · hf hy)
      (hasDerivAt_comp_add_mul_I · hf1 hy)
      (continuous_comp_add_mul_I (contDiffOn_fderiv_apply 1 hf1) hy)
      ((congrArg f e1).trans (hper _ (hpos 0)))
      ((congrArg (fderiv ℝ f · 1) e1).trans (periodic_fderiv_apply 1 hper (hpos 0)))
  have hL (t : ℝ) : (y : ℂ) ^ 2 * (Complex.exp (-(2 * π * Complex.I * n) * t) *
      fderiv ℝ (fun w ↦ fderiv ℝ f w 1) (t + y * Complex.I) 1) +
        (y : ℂ) ^ 2 * (Complex.exp (-(2 * π * Complex.I * n) * t) *
          fderiv ℝ (fun w ↦ fderiv ℝ f w Complex.I) (t + y * Complex.I) Complex.I) +
            eigenvalue * (Complex.exp (-(2 * π * Complex.I * n) * t) * f (t + y * Complex.I)) =
      0 := by
    have h : hyperbolicLaplacian f (t + y * Complex.I) + eigenvalue * f (t + y * Complex.I) = 0 :=
      hΔ _ (hpos t)
    rw [hyperbolicLaplacian, him t] at h
    push_cast at h
    linear_combination Complex.exp (-(2 * π * Complex.I * n) * t) * h
  have he : Continuous fun t : ℝ ↦ Complex.exp (-(2 * π * Complex.I * n) * t) := by
    fun_prop
  have hint {φ : ℝ → ℂ} (hφ : Continuous φ) (c : ℂ) :
      IntervalIntegrable (fun t ↦ c * (Complex.exp (-(2 * π * Complex.I * n) * t) * φ t))
        volume 0 1 :=
    (continuous_const.mul (he.mul hφ)).intervalIntegrable 0 1
  have key : ∫ t in (0 : ℝ)..1, ((y : ℂ) ^ 2 * (Complex.exp (-(2 * π * Complex.I * n) * t) *
      fderiv ℝ (fun w ↦ fderiv ℝ f w Complex.I) (t + y * Complex.I) Complex.I) +
        eigenvalue * (Complex.exp (-(2 * π * Complex.I * n) * t) * f (t + y * Complex.I))) =
      ∫ t in (0 : ℝ)..1, -((y : ℂ) ^ 2 * (Complex.exp (-(2 * π * Complex.I * n) * t) *
        fderiv ℝ (fun w ↦ fderiv ℝ f w 1) (t + y * Complex.I) 1)) :=
    intervalIntegral.integral_congr fun t _ ↦ by linear_combination hL t
  have hc : Continuous fun t : ℝ ↦ fderiv ℝ (fun w ↦ fderiv ℝ f w Complex.I) (t + y * Complex.I)
      Complex.I :=
    continuous_comp_add_mul_I (contDiffOn_fderiv_apply _ <| contDiffOn_fderiv_apply _ hf) hy
  rw [intervalIntegral.integral_add (hint hc _) (hint (continuous_comp_add_mul_I hf hy) _),
    intervalIntegral.integral_neg] at key
  simp only [intervalIntegral.integral_const_mul] at key
  push_cast
  linear_combination key - (y : ℂ) ^ 2 * hx

variable {n} in
/-- **The Fourier coefficients of a Maass form are multiples of `√y K_{iR}(2π|n|y)`**: for `f`
smooth on the upper half-plane with `f(z + 1) = f(z)` and `(Δ + 1/4 + R²) f = 0`, and `n ≠ 0`, if
the `n`-th Fourier coefficient `a_n(y) = ∫_0^1 f(t + iy) e^{-2πint} dt` and its derivative grow at
most polynomially as `y → ∞`, then
`a_n(y) = a_n(y₀) / (√y₀ K_{iR}(2π|n|y₀)) · √y K_{iR}(2π|n|y)` for every `y₀ > 0` with
`K_{iR}(2π|n|y₀) ≠ 0` (such a `y₀` exists, `Complex.exists_besselK_ne_zero`): the exponentially
growing solutions of `fourierCoeff_ode` are excluded. -/
lemma fourierCoeff_eq_div_mul_sqrt_mul_besselK (hf : ContDiffOn ℝ ∞ f {z | 0 < z.im})
    (hper : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z) {R : ℂ}
    (hΔ : ∀ z : ℂ, 0 < z.im → hyperbolicLaplacian f z + maassEigenvalue R * f z = 0) (hn : n ≠ 0)
    {C : ℝ} {N : ℕ} (ha₁ : ∀ᶠ s : ℝ in atTop,
      ‖∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) * f (t + s * Complex.I)‖ ≤
        C * s ^ N)
    (ha₂ : ∀ᶠ s : ℝ in atTop, ‖∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) *
      fderiv ℝ f (t + s * Complex.I) Complex.I‖ ≤ C * s ^ N) {y₀ : ℝ} (hy₀ : 0 < y₀)
    (hK : (Complex.I * R).besselK (2 * π * |(n : ℝ)| * y₀) ≠ 0) (hy : 0 < y) :
    ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) * f (t + y * Complex.I) =
      (∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) * f (t + y₀ * Complex.I)) /
        (√y₀ * (Complex.I * R).besselK (2 * π * |(n : ℝ)| * y₀)) *
          (√y * (Complex.I * R).besselK (2 * π * |(n : ℝ)| * y)) := by
  have he : Continuous fun t : ℝ ↦ Complex.exp (-(2 * π * Complex.I * n) * t) := by
    fun_prop
  have hκ : 0 < 2 * π * |(n : ℝ)| := by
    have h : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hn)
    positivity
  refine Complex.eq_div_mul_sqrt_mul_besselK_of_ode hκ
    (v := fun s : ℝ ↦ ∫ t in (0 : ℝ)..1,
      Complex.exp (-(2 * π * Complex.I * n) * t) * f (t + s * Complex.I))
    (v' := fun s : ℝ ↦ ∫ t in (0 : ℝ)..1,
      Complex.exp (-(2 * π * Complex.I * n) * t) * fderiv ℝ f (t + s * Complex.I) Complex.I)
    (v'' := fun s : ℝ ↦ ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) *
      fderiv ℝ (fun w ↦ fderiv ℝ f w Complex.I) (t + s * Complex.I) Complex.I)
    (fun x hx ↦ hasDerivAt_integral_comp_add_mul_I hf he hx)
    (fun x hx ↦ hasDerivAt_integral_comp_add_mul_I (contDiffOn_fderiv_apply Complex.I hf) he hx)
    (fun x hx ↦ ?_) ha₁ ha₂ hy₀ hK hy
  have hsq : ((2 * π * |(n : ℝ)| * x : ℝ) : ℂ) ^ 2 = ((2 * π * n * x : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow]
    congr 1
    linear_combination (2 * π * x) ^ 2 * sq_abs (n : ℝ)
  rw [hsq]
  exact fourierCoeff_ode n hf hper hΔ hx

end UpperHalfPlane
