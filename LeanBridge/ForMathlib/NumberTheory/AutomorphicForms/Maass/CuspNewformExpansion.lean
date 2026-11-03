import LeanBridge.ForMathlib.Analysis.Complex.UpperHalfPlane.StripIntegral
import LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselKUniqueIntegrable
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CuspNewform
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.FourierExpansionExists

/-!
# The expansions of Maass cusp newforms

Every Maass cusp newform `F` of weight `0` on `Γ₀(N)` with trivial character and spectral
parameter `R` (`UpperHalfPlane.IsMaassCuspNewform`) has, if it is even, the cosine expansion
`F(x + iy) = ∑_{n ≥ 1} a(n) √y K_{iR}(2πny) cos(2πnx)` and, if it is odd, the sine expansion, with
the coefficients `a = maassCoefficients R F` (LMFDB `mf.maass.mwf.coefficients`), with no
hypothesis on the growth of `F`: square-integrability replaces the polynomial bounds on `F` and
`∂F/∂y` of `UpperHalfPlane.hasMaassCosineExpansion_maassCoefficients`.

The `n`-th Fourier coefficient `a_n(y) = ∫_0^1 F(t + iy) e^{-2πint} dt` satisfies
`|a_n(y)|² ≤ ∫_{-1/2}^{1/2} |F(t + iy)|² dt` (Cauchy–Schwarz and periodicity), and the rectangle
`(-1/2, 1/2) × (1, ∞)` lies in the standard fundamental domain `𝒟ᵒ`, on which `|F|²` is integrable
for the invariant measure `dx dy / y²`; by Fubini, `|a_n(y)|² / y²` is integrable on `(1, ∞)`, and
so is `|a_n(y)| / y²`. By the differential equation of `a_n` and the uniqueness of the solutions
of the modified Bessel equation that are integrable against a power
(`Complex.eq_div_mul_sqrt_mul_besselK_of_ode_of_integrableOn`), `a_n(y)` is a multiple of
`√y K_{iR}(2π|n|y)` for `n ≠ 0`. With the vanishing constant term at `∞` this gives the Fourier
expansion of every element of `M(N, χ, λ)` whose constant term at `∞` vanishes, and so the
expansions of the cusp newforms. At every level `N ≠ 0`, for an even or odd cusp newform,
`a(1) ≠ 0` and the coefficient `a(n) / a(1)` of the cusp newform normalised by `a(1) = 1` is real
for every `n`, `gcd(n, N) > 1` included
(`UpperHalfPlane.IsMaassCuspNewform.maassCoefficients_one_ne_zero_of_even`,
`UpperHalfPlane.IsMaassCuspNewform.conj_maassCoefficients_div_of_even` and the odd versions, in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.NewformAtkinLehner`), by the Main Lemma
of Atkin and Lehner for Maass forms.

## Main results

* `UpperHalfPlane.integrableOn_sq_norm_fourierCoeff_div_sq`,
  `UpperHalfPlane.integrableOn_norm_fourierCoeff_div_sq`: the Fourier coefficients of an element
  of `M(N, χ, λ)` satisfy `∫_1^∞ |a_n(y)|² dy / y² < ∞` and `∫_1^∞ |a_n(y)| dy / y² < ∞`.
* `UpperHalfPlane.fourierCoeff_eq_div_mul_sqrt_mul_besselK_of_integrableOn`: a Fourier coefficient
  `a_n` with `|a_n(y)| / y^k` integrable at `∞` is a multiple of `√y K_{iR}(2π|n|y)`.
* `UpperHalfPlane.exists_hasMaassFourierExpansion_of_integrableOn`,
  `UpperHalfPlane.exists_hasMaassFourierExpansion_of_mem_maassSpace`: the Fourier expansion of a
  Maass form with vanishing constant term at `∞` whose coefficients are integrable against a
  power, for instance of any element of `M(N, χ, λ)` with vanishing constant term at `∞`.
* `UpperHalfPlane.IsMaassNewform.hasMaassCosineExpansion_of_integral_eq_zero`,
  `UpperHalfPlane.IsMaassNewform.hasMaassSineExpansion_of_integral_eq_zero`: the cosine (sine)
  expansion of an even (odd) Maass newform with vanishing constant term at `∞`.
* `UpperHalfPlane.IsMaassCuspNewform.hasMaassCosineExpansion`,
  `UpperHalfPlane.IsMaassCuspNewform.hasMaassSineExpansion`: the cosine (sine) expansion of an
  even (odd) Maass cusp newform, with the coefficients `maassCoefficients R F`.
-/

open Function MeasureTheory Real Set

open scoped ContDiff

namespace UpperHalfPlane

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {eigenvalue R : ℂ} {F : ℍ → ℂ} {f : ℂ → ℂ} (n : ℤ)

lemma integrableOn_inv_sq_mul_norm_sq (hF : F ∈ maassSpace N χ eigenvalue) :
    IntegrableOn (fun p : ℝ × ℝ ↦ (p.2 ^ 2)⁻¹ * ‖F (ofComplex (p.1 + p.2 * Complex.I))‖ ^ 2)
      (Ioo (-(1 / 2)) (1 / 2) ×ˢ Ioi 1) := by
  refine (integrableOn_re_im_mem_prod_iff measurableSet_Ioo measurableSet_Ioi
    (Ioi_subset_Ioi zero_le_one)).mp ((integrableOn_norm_sq_smul_fdo 1 hF).mono_set ?_)
  rintro z ⟨hx, hy⟩
  refine Set.mem_smul_set.mpr ⟨z, ⟨?_, abs_lt.mpr hx⟩, one_smul _ z⟩
  rw [Complex.normSq_apply, coe_re, coe_im]
  have hy' : 1 < z.im := hy
  nlinarith [mul_self_nonneg z.re]

lemma sq_intervalIntegral_le {h : ℝ → ℝ} (hc : Continuous h) :
    (∫ t in (0 : ℝ)..1, h t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, h t ^ 2 := by
  set c : ℝ := ∫ t in (0 : ℝ)..1, h t with hc_def
  have hi1 : IntervalIntegrable (fun t ↦ h t ^ 2) volume 0 1 := (hc.pow 2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t ↦ 2 * c * h t) volume 0 1 :=
    (continuous_const.mul hc).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun t ↦ h t ^ 2 - 2 * c * h t) volume 0 1 := hi1.sub hi2
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, (h t ^ 2 - 2 * c * h t + c ^ 2) :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ ↦ by nlinarith [sq_nonneg (h t - c)]
  rw [intervalIntegral.integral_add hi3 intervalIntegrable_const,
    intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, ← hc_def, sub_zero, one_smul] at h0
  nlinarith

/-- **The Fourier coefficients of a square-integrable Maass form are square-integrable against
`y⁻²`**: for `F` in `M(N, χ, λ)` (`maassSpace`), which is `1`-periodic, the `n`-th Fourier
coefficient `a_n(y) = ∫_0^1 F(t + iy) e^{-2πint} dt` satisfies `∫_1^∞ |a_n(y)|² dy / y² < ∞`, as
`|a_n(y)|² ≤ ∫_{-1/2}^{1/2} |F(t + iy)|² dt` (Cauchy–Schwarz and periodicity) and `|F|²` is
integrable on the rectangle `(-1/2, 1/2) × (1, ∞)` of the standard fundamental domain for
`dx dy / y²` (Fubini). -/
lemma integrableOn_sq_norm_fourierCoeff_div_sq (hF : F ∈ maassSpace N χ eigenvalue) :
    IntegrableOn (fun y : ℝ ↦ ‖∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) *
      (F ∘ ofComplex) (t + y * Complex.I)‖ ^ 2 / y ^ 2) (Ioi 1) := by
  have hf : Integrable (fun p : ℝ × ℝ ↦ (p.2 ^ 2)⁻¹ * ‖F (ofComplex (p.1 + p.2 * Complex.I))‖ ^ 2)
      ((volume.restrict (Ioo (-(1 / 2)) (1 / 2))).prod (volume.restrict (Ioi 1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact integrableOn_inv_sq_mul_norm_sq hF
  have he : Continuous fun t : ℝ ↦ Complex.exp (-(2 * π * Complex.I * n) * t) := by
    fun_prop
  refine hf.integral_norm_prod_right.mono'
    (ContinuousOn.aestronglyMeasurable (fun y hy ↦ ?_) measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun y hy ↦ ?_))
  · have hy0 : 0 < y := one_pos.trans hy
    exact (((hasDerivAt_integral_comp_add_mul_I hF.1 he hy0).continuousAt.norm.pow 2).div
      (continuous_pow 2).continuousAt (pow_ne_zero 2 hy0.ne')).continuousWithinAt
  · have hy0 : 0 < y := one_pos.trans hy
    have hcy : Continuous fun t : ℝ ↦ ‖(F ∘ ofComplex) (t + y * Complex.I)‖ :=
      (continuous_comp_add_mul_I hF.1 hy0).norm
    have hp : Periodic (fun t : ℝ ↦ ‖(F ∘ ofComplex) (t + y * Complex.I)‖ ^ 2) 1 := fun t ↦ by
      have h : (F ∘ ofComplex) (t + y * Complex.I + 1) = (F ∘ ofComplex) (t + y * Complex.I) :=
        comp_add_one_of_mem_maassSpace hF (by simpa using hy0)
      simp only [Complex.ofReal_add, Complex.ofReal_one]
      rw [add_right_comm, h]
    have h2 : ∫ t in (0 : ℝ)..0 + 1, ‖(F ∘ ofComplex) (t + y * Complex.I)‖ ^ 2 =
        ∫ t in (-(1 / 2) : ℝ)..-(1 / 2) + 1, ‖(F ∘ ofComplex) (t + y * Complex.I)‖ ^ 2 :=
      hp.intervalIntegral_add_eq 0 (-(1 / 2))
    have e : -(1 / 2 : ℝ) + 1 = 1 / 2 := by
      norm_num
    rw [zero_add, e] at h2
    have hn : ‖∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) *
        (F ∘ ofComplex) (t + y * Complex.I)‖ ≤
          ∫ t in (0 : ℝ)..1, ‖(F ∘ ofComplex) (t + y * Complex.I)‖ := by
      refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans_eq ?_
      refine intervalIntegral.integral_congr fun t _ ↦ ?_
      simp only [norm_mul, norm_exp_neg_two_pi_I_mul, one_mul]
    have h1 : ‖∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) *
        (F ∘ ofComplex) (t + y * Complex.I)‖ ^ 2 ≤
          ∫ t : ℝ in Ioo (-(1 / 2)) (1 / 2), ‖(F ∘ ofComplex) (t + y * Complex.I)‖ ^ 2 := by
      refine (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans ((sq_intervalIntegral_le hcy).trans ?_)
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num), ← h2]
    dsimp only
    have h3 : ∫ x : ℝ in Ioo (-(1 / 2)) (1 / 2),
        ‖(y ^ 2)⁻¹ * ‖F (ofComplex (x + y * Complex.I))‖ ^ 2‖ =
          (y ^ 2)⁻¹ * ∫ t : ℝ in Ioo (-(1 / 2)) (1 / 2),
            ‖(F ∘ ofComplex) (t + y * Complex.I)‖ ^ 2 := by
      rw [← integral_const_mul]
      exact integral_congr_ae (.of_forall fun x ↦
        Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (sq_nonneg _)))
    rw [h3, Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (sq_nonneg _))

/-- **The Fourier coefficients of a square-integrable Maass form are integrable against `y⁻²`**:
for `F` in `M(N, χ, λ)` (`maassSpace`), the `n`-th Fourier coefficient
`a_n(y) = ∫_0^1 F(t + iy) e^{-2πint} dt` satisfies `∫_1^∞ |a_n(y)| dy / y² < ∞`, as
`|a_n(y)| ≤ |a_n(y)|² + 1` (`integrableOn_sq_norm_fourierCoeff_div_sq`). -/
lemma integrableOn_norm_fourierCoeff_div_sq (hF : F ∈ maassSpace N χ eigenvalue) :
    IntegrableOn (fun y : ℝ ↦ ‖∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) *
      (F ∘ ofComplex) (t + y * Complex.I)‖ / y ^ 2) (Ioi 1) := by
  have he : Continuous fun t : ℝ ↦ Complex.exp (-(2 * π * Complex.I * n) * t) := by
    fun_prop
  have h : IntegrableOn (fun y : ℝ ↦ (y ^ 2)⁻¹) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).congr_fun (fun y hy ↦ by
      dsimp only
      rw [Real.rpow_neg (zero_le_one.trans (mem_Ioi.mp hy).le), Real.rpow_two]) measurableSet_Ioi
  have hsq (x : ℝ) : x ≤ x ^ 2 + 1 := by
    nlinarith [sq_nonneg (2 * x - 1)]
  refine ((integrableOn_sq_norm_fourierCoeff_div_sq n hF).add h).mono'
    (ContinuousOn.aestronglyMeasurable (fun y hy ↦ ?_) measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun y hy ↦ ?_))
  · have hy0 : 0 < y := one_pos.trans hy
    exact ((hasDerivAt_integral_comp_add_mul_I hF.1 he hy0).continuousAt.norm.div
      (continuous_pow 2).continuousAt (pow_ne_zero 2 hy0.ne')).continuousWithinAt
  · rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (sq_nonneg y))]
    exact (div_le_div_of_nonneg_right (hsq _) (sq_nonneg y)).trans_eq (by simp [add_div])

variable {n} {a : ℝ} {k : ℕ}

/-- **The Fourier coefficients of a Maass form integrable against a power are multiples of
`√y K_{iR}(2π|n|y)`**: for `f` smooth on the upper half-plane with `f(z + 1) = f(z)` and
`(Δ + 1/4 + R²) f = 0`, and `n ≠ 0`, if `|a_n(y)| / y^k` is integrable on `(a, ∞)` for the `n`-th
Fourier coefficient `a_n(y) = ∫_0^1 f(t + iy) e^{-2πint} dt`, then
`a_n(y) = a_n(y₀) / (√y₀ K_{iR}(2π|n|y₀)) · √y K_{iR}(2π|n|y)` for every `y₀ > 0` with
`K_{iR}(2π|n|y₀) ≠ 0`. -/
lemma fourierCoeff_eq_div_mul_sqrt_mul_besselK_of_integrableOn
    (hf : ContDiffOn ℝ ∞ f {z | 0 < z.im}) (hper : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (hΔ : ∀ z : ℂ, 0 < z.im → hyperbolicLaplacian f z + maassEigenvalue R * f z = 0) (hn : n ≠ 0)
    (hint : IntegrableOn (fun s : ℝ ↦ ‖∫ t in (0 : ℝ)..1,
      Complex.exp (-(2 * π * Complex.I * n) * t) * f (t + s * Complex.I)‖ / s ^ k) (Ioi a))
    {y₀ y : ℝ} (hy₀ : 0 < y₀) (hK : (Complex.I * R).besselK (2 * π * |(n : ℝ)| * y₀) ≠ 0)
    (hy : 0 < y) :
    ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) * f (t + y * Complex.I) =
      (∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) * f (t + y₀ * Complex.I)) /
        (√y₀ * (Complex.I * R).besselK (2 * π * |(n : ℝ)| * y₀)) *
          (√y * (Complex.I * R).besselK (2 * π * |(n : ℝ)| * y)) := by
  have he : Continuous fun t : ℝ ↦ Complex.exp (-(2 * π * Complex.I * n) * t) := by
    fun_prop
  have hκ : 0 < 2 * π * |(n : ℝ)| := by
    have h : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hn)
    positivity
  refine Complex.eq_div_mul_sqrt_mul_besselK_of_ode_of_integrableOn hκ
    (fun _ ↦ hasDerivAt_integral_comp_add_mul_I hf he)
    (fun _ ↦ hasDerivAt_integral_comp_add_mul_I (contDiffOn_fderiv_apply Complex.I hf) he)
    (fun x hx ↦ ?_) hint hy₀ hK hy
  have hsq : ((2 * π * |(n : ℝ)| * x : ℝ) : ℂ) ^ 2 = ((2 * π * n * x : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow]
    congr 1
    linear_combination (2 * π * x) ^ 2 * sq_abs (n : ℝ)
  rw [hsq]
  exact fourierCoeff_ode n hf hper hΔ hx

/-- **The Fourier expansion of a Maass form with coefficients integrable against a power**: a smooth
function `f` on the upper half-plane with `f(z + 1) = f(z)`, `(Δ + 1/4 + R²) f = 0`,
`∫_0^1 f(t + iy) dt = 0` for every `y > 0`, and `|a_n(y)| / y^k` integrable on `(a, ∞)` for the
Fourier coefficients `a_n`, `n ≠ 0`, has the Fourier expansion
`f(x + iy) = ∑_{n ∈ ℤ} c(n) √y K_{iR}(2π|n|y) e^{2πinx}` with `c(0) = 0`. -/
lemma exists_hasMaassFourierExpansion_of_integrableOn (hf : ContDiffOn ℝ ∞ f {z | 0 < z.im})
    (hper : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (hΔ : ∀ z : ℂ, 0 < z.im → hyperbolicLaplacian f z + maassEigenvalue R * f z = 0)
    (h0 : ∀ y : ℝ, 0 < y → ∫ t in (0 : ℝ)..1, f (t + y * Complex.I) = 0)
    (hint : ∀ n : ℤ, n ≠ 0 → IntegrableOn (fun s : ℝ ↦ ‖∫ t in (0 : ℝ)..1,
      Complex.exp (-(2 * π * Complex.I * n) * t) * f (t + s * Complex.I)‖ / s ^ k) (Ioi a)) :
    ∃ c : ℤ → ℂ, c 0 = 0 ∧ HasMaassFourierExpansion f R c := by
  rcases (Complex.I * R).exists_besselK_ne_zero with ⟨x₀, hx₀, hK⟩
  refine ⟨fun n ↦ if n = 0 then 0 else (∫ t in (0 : ℝ)..1, Complex.exp
    (-(2 * π * Complex.I * n) * t) * f (t + (x₀ / (2 * π * |(n : ℝ)|) : ℝ) * Complex.I)) /
      (√(x₀ / (2 * π * |(n : ℝ)|)) * (Complex.I * R).besselK x₀), ite_eq_left rfl, fun z ↦ ?_⟩
  have hz : (z : ℂ) = (z.re : ℂ) + z.im * Complex.I := (Complex.re_add_im z).symm
  rw [hz]
  refine (hasSum_fourierCoeffOn_mul_exp z.re hf hper z.im_pos).congr_fun fun n ↦ ?_
  rw [fourierCoeffOn_eq_integral_exp]
  dsimp only
  split_ifs with hn
  · subst hn
    simp [h0 _ z.im_pos]
  · have hn' : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hn)
    have hyn : 0 < x₀ / (2 * π * |(n : ℝ)|) := by
      positivity
    have hxn : 2 * π * |(n : ℝ)| * (x₀ / (2 * π * |(n : ℝ)|)) = x₀ := two_pi_mul_abs_mul_div hn x₀
    have hKn : (Complex.I * R).besselK (2 * π * |(n : ℝ)| * (x₀ / (2 * π * |(n : ℝ)|))) ≠ 0 := by
      rwa [hxn]
    rw [fourierCoeff_eq_div_mul_sqrt_mul_besselK_of_integrableOn hf hper hΔ hn (hint n hn) hyn hKn
      z.im_pos, hxn, Int.cast_abs]
    ring1

/-- **The Fourier expansion of a square-integrable Maass form with vanishing constant term**: an
element `F` of `M(N, χ, 1/4 + R²)` (`maassSpace`, square-integrable on `Γ₀(N) \ ℍ`) with
`∫_0^1 F(t + iy) dt = 0` for every `y > 0` has the Fourier expansion
`F(x + iy) = ∑_{n ∈ ℤ} c(n) √y K_{iR}(2π|n|y) e^{2πinx}` with `c(0) = 0`, with no growth
hypothesis (`integrableOn_norm_fourierCoeff_div_sq`). -/
lemma exists_hasMaassFourierExpansion_of_mem_maassSpace
    (hF : F ∈ maassSpace N χ (maassEigenvalue R))
    (h0 : ∀ y : ℝ, 0 < y → ∫ t in (0 : ℝ)..1, (F ∘ ofComplex) (t + y * Complex.I) = 0) :
    ∃ c : ℤ → ℂ, c 0 = 0 ∧ HasMaassFourierExpansion (F ∘ ofComplex) R c :=
  exists_hasMaassFourierExpansion_of_integrableOn hF.1 (fun _ ↦ comp_add_one_of_mem_maassSpace hF)
    hF.2.2.2 h0 fun n _ ↦ integrableOn_norm_fourierCoeff_div_sq n hF

/-- **The cosine expansion of an even Maass newform with vanishing constant term**: an even Maass
newform `F` of weight `0` on `Γ₀(N)` with trivial character and eigenvalue `1/4 + R²` with
`∫_0^1 F(t + iy) dt = 0` for every `y > 0` has the cosine expansion with the coefficients
`maassCoefficients R F`, with no growth hypothesis. -/
lemma IsMaassNewform.hasMaassCosineExpansion_of_integral_eq_zero
    (hF : IsMaassNewform N 1 (maassEigenvalue R) F)
    (h0 : ∀ y : ℝ, 0 < y → ∫ t in (0 : ℝ)..1, (F ∘ ofComplex) (t + y * Complex.I) = 0)
    (hs : IsEvenMaassForm (F ∘ ofComplex)) :
    HasMaassCosineExpansion (F ∘ ofComplex) R (maassCoefficients R (F ∘ ofComplex)) := by
  rcases exists_hasMaassFourierExpansion_of_mem_maassSpace hF.1.1 h0 with ⟨a, ha0, ha⟩
  have hc : HasMaassCosineExpansion (F ∘ ofComplex) R fun n ↦ 2 * a n :=
    ha.hasMaassCosineExpansion hs ha0
  rwa [hc.maassCoefficients_eq]

/-- **The sine expansion of an odd Maass newform with vanishing constant term**: an odd Maass
newform `F` of weight `0` on `Γ₀(N)` with trivial character and eigenvalue `1/4 + R²` with
`∫_0^1 F(t + iy) dt = 0` for every `y > 0` has the sine expansion with the coefficients
`maassCoefficients R F`, with no growth hypothesis. -/
lemma IsMaassNewform.hasMaassSineExpansion_of_integral_eq_zero
    (hF : IsMaassNewform N 1 (maassEigenvalue R) F)
    (h0 : ∀ y : ℝ, 0 < y → ∫ t in (0 : ℝ)..1, (F ∘ ofComplex) (t + y * Complex.I) = 0)
    (hs : IsOddMaassForm (F ∘ ofComplex)) :
    HasMaassSineExpansion (F ∘ ofComplex) R (maassCoefficients R (F ∘ ofComplex)) := by
  rcases exists_hasMaassFourierExpansion_of_mem_maassSpace hF.1.1 h0 with ⟨a, ha0, ha⟩
  have hc : HasMaassSineExpansion (F ∘ ofComplex) R fun n ↦ 2 * Complex.I * a n :=
    ha.hasMaassSineExpansion hs ha0
  rwa [hc.maassCoefficients_eq]

variable [NeZero N]

/-- **The cosine expansion of an even Maass cusp newform** (LMFDB `mf.maass.mwf.coefficients`): an
even Maass cusp newform `F` of weight `0` on `Γ₀(N)` with spectral parameter `R` has the cosine
expansion `F(x + iy) = ∑_{n ≥ 1} a(n) √y K_{iR}(2πny) cos(2πnx)` with the coefficients
`a = maassCoefficients R F`, with no growth hypothesis. -/
lemma IsMaassCuspNewform.hasMaassCosineExpansion (hF : IsMaassCuspNewform N R F)
    (hs : IsEvenMaassForm (F ∘ ofComplex)) :
    HasMaassCosineExpansion (F ∘ ofComplex) R (maassCoefficients R (F ∘ ofComplex)) :=
  hF.1.hasMaassCosineExpansion_of_integral_eq_zero (fun _ ↦ hF.integral_eq_zero) hs

/-- **The sine expansion of an odd Maass cusp newform** (LMFDB `mf.maass.mwf.coefficients`): an odd
Maass cusp newform `F` of weight `0` on `Γ₀(N)` with spectral parameter `R` has the sine expansion
`F(x + iy) = ∑_{n ≥ 1} a(n) √y K_{iR}(2πny) sin(2πnx)` with the coefficients
`a = maassCoefficients R F`, with no growth hypothesis. -/
lemma IsMaassCuspNewform.hasMaassSineExpansion (hF : IsMaassCuspNewform N R F)
    (hs : IsOddMaassForm (F ∘ ofComplex)) :
    HasMaassSineExpansion (F ∘ ofComplex) R (maassCoefficients R (F ∘ ofComplex)) :=
  hF.1.hasMaassSineExpansion_of_integral_eq_zero (fun _ ↦ hF.integral_eq_zero) hs

end UpperHalfPlane
