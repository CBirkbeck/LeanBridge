import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CoefficientsUnique
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.FourierCoefficientODE

/-!
# Existence of the Fourier expansion of a Maass cusp form

Let `f` be a smooth function on the upper half-plane with `f(z + 1) = f(z)` and
`(Δ + 1/4 + R²) f = 0`, such as a Maass form on `Γ₀(N)` of spectral parameter `R`. If its constant
term `∫_0^1 f(t + iy) dt` vanishes (cuspidality at `∞`) and `f` and `∂f/∂y` grow at most
polynomially in `y`, uniformly in `x` (moderate growth), then `f` has a Fourier expansion
`f(x + iy) = ∑_{n ∈ ℤ} a(n) √y K_{iR}(2π|n|y) e^{2πinx}` (`UpperHalfPlane.HasMaassFourierExpansion`,
LMFDB `mf.maass.mwf.fourierexpansion`, `mf.maass.mwf.coefficients`): its Fourier series in `x`
converges (`UpperHalfPlane.hasSum_fourierCoeffOn_mul_exp`) and its coefficients are multiples of
`√y K_{iR}(2π|n|y)` (`UpperHalfPlane.fourierCoeff_eq_div_mul_sqrt_mul_besselK`), whose
constant is fixed at a point where `K_{iR}` does not vanish (`Complex.exists_besselK_ne_zero`).

The two hypotheses are not part of `UpperHalfPlane.IsMaassForm` or `UpperHalfPlane.maassSpace`,
which ask for square-integrability on `Γ₀(N) \ ℍ` only. Moderate growth is replaced by
square-integrability in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CuspNewformExpansion`, and the constant
term vanishes for real `R`
(`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.ConstantTerm`); the constant newform
`1` of level `1` (`UpperHalfPlane.isMaassNewform_const_one`, `R = ±i/2`) has no such expansion.

For an even (odd) form the coefficients satisfy `a(-n) = a(n)` (`a(-n) = -a(n)`), by the uniqueness
of the Fourier coefficients, so that the expansion is a cosine (sine) expansion with coefficients
`2a(n)` (`2i a(n)`); these are then the coefficients `UpperHalfPlane.maassCoefficients R f` of the
LMFDB (`UpperHalfPlane.HasMaassCosineExpansion.maassCoefficients_eq`,
`UpperHalfPlane.HasMaassSineExpansion.maassCoefficients_eq`).

## Main results

* `UpperHalfPlane.exists_hasMaassFourierExpansion`: the Fourier expansion of a Maass form with
  vanishing constant term and moderate growth.
* `UpperHalfPlane.HasMaassFourierExpansion.hasMaassCosineExpansion`,
  `UpperHalfPlane.HasMaassFourierExpansion.hasMaassSineExpansion`: the Fourier expansion of an even
  (odd) function is a cosine (sine) expansion.
* `UpperHalfPlane.hasMaassCosineExpansion_maassCoefficients`,
  `UpperHalfPlane.hasMaassSineExpansion_maassCoefficients`: the cosine (sine) expansion, with the
  coefficients `maassCoefficients R f`, of an even (odd) Maass form with vanishing constant term
  and moderate growth.
-/

open Filter Function MeasureTheory Real Set Topology

open scoped ContDiff

namespace UpperHalfPlane

variable {f : ℂ → ℂ} {R : ℂ} {a : ℤ → ℂ} {C : ℝ} {N : ℕ} {g : ℝ → ℂ} (n : ℤ)

variable (g) in
lemma fourierCoeffOn_eq_integral_exp : fourierCoeffOn (lt_add_of_pos_right 0 one_pos) g n =
    ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) * g t := by
  rw [fourierCoeffOn_eq_integral]
  simp only [zero_add, sub_zero, div_one, one_smul]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [fourier_coe_apply]
  congr 2
  push_cast
  ring1

lemma norm_exp_neg_two_pi_I_mul (t : ℝ) : ‖Complex.exp (-(2 * π * Complex.I * n) * t)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

lemma norm_integral_exp_mul_le {B : ℝ} (hg : ∀ t, ‖g t‖ ≤ B) :
    ‖∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) * g t‖ ≤ B := by
  have h : ‖∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) * g t‖ ≤ B * |1 - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t _ ↦ by
      rw [norm_mul, norm_exp_neg_two_pi_I_mul, one_mul]
      exact hg t
  simpa using h

variable {n} in
lemma two_pi_mul_abs_mul_div (hn : n ≠ 0) (x : ℝ) :
    2 * π * |(n : ℝ)| * (x / (2 * π * |(n : ℝ)|)) = x := by
  field_simp

/-- **The Fourier expansion of a Maass form of moderate growth with vanishing constant term**: a
smooth function `f` on the upper half-plane with `f(z + 1) = f(z)`, `(Δ + 1/4 + R²) f = 0`,
`∫_0^1 f(t + iy) dt = 0` for every `y > 0`, and `|f(x + iy)|, |∂f/∂y(x + iy)| ≤ C y^N` for large
`y`, has the Fourier expansion `f(x + iy) = ∑_{n ∈ ℤ} a(n) √y K_{iR}(2π|n|y) e^{2πinx}`. -/
lemma exists_hasMaassFourierExpansion (hf : ContDiffOn ℝ ∞ f {z | 0 < z.im})
    (hper : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (hΔ : ∀ z : ℂ, 0 < z.im → hyperbolicLaplacian f z + maassEigenvalue R * f z = 0)
    (h0 : ∀ y : ℝ, 0 < y → ∫ t in (0 : ℝ)..1, f (t + y * Complex.I) = 0)
    (hb : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ, ‖f (t + y * Complex.I)‖ ≤ C * y ^ N)
    (hb' : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ, ‖fderiv ℝ f (t + y * Complex.I) Complex.I‖ ≤ C * y ^ N) :
    ∃ a : ℤ → ℂ, a 0 = 0 ∧ HasMaassFourierExpansion f R a := by
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
    rw [fourierCoeff_eq_div_mul_sqrt_mul_besselK hf hper hΔ hn
      (hb.mono fun s hs ↦ norm_integral_exp_mul_le n hs)
      (hb'.mono fun s hs ↦ norm_integral_exp_mul_le n hs) hyn hKn z.im_pos, hxn, Int.cast_abs]
    ring1

lemma HasMaassFourierExpansion.comp_neg_of_even (h : HasMaassFourierExpansion f R a)
    (hf : IsEvenMaassForm f) : HasMaassFourierExpansion f R fun n ↦ a (-n) := by
  intro z
  have h1 : HasSum (fun n : ℤ ↦ a n * √z.im * (Complex.I * R).besselK (2 * π * |n| * z.im) *
      Complex.exp (2 * π * Complex.I * n * ((-z.re : ℝ) : ℂ))) (f z) := by
    simpa only [hf z, re_maassReflection_smul, im_maassReflection_smul] using
      h (maassReflection • z)
  refine ((Equiv.neg ℤ).hasSum_iff.mpr h1).congr_fun fun n ↦ ?_
  simp only [Function.comp_apply, Equiv.neg_apply, abs_neg]
  congr 2
  push_cast
  ring1

lemma HasMaassFourierExpansion.comp_neg_of_odd (h : HasMaassFourierExpansion f R a)
    (hf : IsOddMaassForm f) : HasMaassFourierExpansion f R fun n ↦ -a (-n) := by
  intro z
  have h1 : HasSum (fun n : ℤ ↦ -(a n * √z.im * (Complex.I * R).besselK (2 * π * |n| * z.im) *
      Complex.exp (2 * π * Complex.I * n * ((-z.re : ℝ) : ℂ)))) (f z) := by
    simpa only [hf z, neg_neg, re_maassReflection_smul, im_maassReflection_smul] using
      (h (maassReflection • z)).neg
  refine ((Equiv.neg ℤ).hasSum_iff.mpr h1).congr_fun fun n ↦ ?_
  simp only [Function.comp_apply, Equiv.neg_apply, abs_neg]
  push_cast
  simp only [mul_neg, neg_mul, neg_neg]

lemma HasMaassFourierExpansion.coeff_neg_eq (h : HasMaassFourierExpansion f R a)
    (hf : IsEvenMaassForm f) (hn : n ≠ 0) : a (-n) = a n := by
  rcases (Complex.I * R).exists_besselK_ne_zero with ⟨x, hx, hK⟩
  have hxn : 2 * π * ((|n| : ℤ) : ℝ) * (x / (2 * π * |(n : ℝ)|)) = x := by
    rw [Int.cast_abs]
    exact two_pi_mul_abs_mul_div hn x
  have key : a (-n) * (Complex.I * R).besselK (2 * π * ((|n| : ℤ) : ℝ) *
      (x / (2 * π * |(n : ℝ)|))) = a n * (Complex.I * R).besselK (2 * π * ((|n| : ℤ) : ℝ) *
        (x / (2 * π * |(n : ℝ)|))) :=
    (h.comp_neg_of_even hf).mul_besselK_eq h n (div_pos hx (by positivity))
  rw [hxn] at key
  exact mul_right_cancel₀ hK key

lemma HasMaassFourierExpansion.coeff_neg_eq_neg (h : HasMaassFourierExpansion f R a)
    (hf : IsOddMaassForm f) (hn : n ≠ 0) : a (-n) = -a n := by
  rcases (Complex.I * R).exists_besselK_ne_zero with ⟨x, hx, hK⟩
  have hxn : 2 * π * ((|n| : ℤ) : ℝ) * (x / (2 * π * |(n : ℝ)|)) = x := by
    rw [Int.cast_abs]
    exact two_pi_mul_abs_mul_div hn x
  have key : -a (-n) * (Complex.I * R).besselK (2 * π * ((|n| : ℤ) : ℝ) *
      (x / (2 * π * |(n : ℝ)|))) = a n * (Complex.I * R).besselK (2 * π * ((|n| : ℤ) : ℝ) *
        (x / (2 * π * |(n : ℝ)|))) :=
    (h.comp_neg_of_odd hf).mul_besselK_eq h n (div_pos hx (by positivity))
  rw [hxn] at key
  linear_combination -mul_right_cancel₀ hK key

lemma hasSum_pnat_of_hasSum_nat {u : ℕ → ℂ} {s : ℂ} (hu : HasSum u s) (h0 : u 0 = 0) :
    HasSum (fun k : ℕ+ ↦ u k) s := by
  refine (PNat.coe_injective.hasSum_iff fun k hk ↦ ?_).mpr hu
  have hk0 : k = 0 := by
    by_contra hk0
    exact hk ⟨⟨k, Nat.pos_of_ne_zero hk0⟩, rfl⟩
  rw [hk0, h0]

/-- **An even Fourier expansion is a cosine expansion**: if `f` has the Fourier expansion
`∑_{n ∈ ℤ} a(n) √y K_{iR}(2π|n|y) e^{2πinx}` with `a(0) = 0` and `f` is even
(`IsEvenMaassForm`), then `a(-n) = a(n)` and `f` has the cosine expansion with coefficients
`2 a(n)`, `n ≥ 1`. -/
lemma HasMaassFourierExpansion.hasMaassCosineExpansion (h : HasMaassFourierExpansion f R a)
    (hf : IsEvenMaassForm f) (ha0 : a 0 = 0) : HasMaassCosineExpansion f R fun n ↦ 2 * a n := by
  intro z
  refine (hasSum_pnat_of_hasSum_nat (by simpa [ha0] using (h z).nat_add_neg)
    (by simp [ha0])).congr_fun fun k ↦ ?_
  have hneg : a (-((k : ℕ) : ℤ)) = a ((k : ℕ) : ℤ) := h.coeff_neg_eq _ hf (by positivity)
  simp only [hneg]
  have e1 : 2 * π * Complex.I * ((k : ℕ) : ℂ) * z.re =
      ((2 * π * (k : ℕ) * z.re : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring1
  rw [e1, Complex.ofReal_cos, Complex.cos, neg_mul]
  ring1

/-- **An odd Fourier expansion is a sine expansion**: if `f` has the Fourier expansion
`∑_{n ∈ ℤ} a(n) √y K_{iR}(2π|n|y) e^{2πinx}` with `a(0) = 0` and `f` is odd (`IsOddMaassForm`),
then `a(-n) = -a(n)` and `f` has the sine expansion with coefficients `2i a(n)`, `n ≥ 1`. -/
lemma HasMaassFourierExpansion.hasMaassSineExpansion (h : HasMaassFourierExpansion f R a)
    (hf : IsOddMaassForm f) (ha0 : a 0 = 0) :
    HasMaassSineExpansion f R fun n ↦ 2 * Complex.I * a n := by
  intro z
  refine (hasSum_pnat_of_hasSum_nat (by simpa [ha0] using (h z).nat_add_neg)
    (by simp [ha0])).congr_fun fun k ↦ ?_
  have hneg : a (-((k : ℕ) : ℤ)) = -a ((k : ℕ) : ℤ) := h.coeff_neg_eq_neg _ hf (by positivity)
  simp only [hneg]
  have e1 : 2 * π * Complex.I * ((k : ℕ) : ℂ) * z.re =
      ((2 * π * (k : ℕ) * z.re : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring1
  rw [e1, Complex.ofReal_sin, Complex.sin, neg_mul]
  linear_combination (a ((k : ℕ) : ℤ) * √z.im * (Complex.I * R).besselK (2 * π * (k : ℕ) * z.im) *
    (Complex.exp (-(((2 * π * (k : ℕ) * z.re : ℝ) : ℂ) * Complex.I)) -
      Complex.exp (((2 * π * (k : ℕ) * z.re : ℝ) : ℂ) * Complex.I))) * Complex.I_sq

/-- **The cosine expansion of an even Maass form** (LMFDB `mf.maass.mwf.coefficients`): a smooth
even function `f` on the upper half-plane with `f(z + 1) = f(z)`, `(Δ + 1/4 + R²) f = 0`, vanishing
constant term and moderate growth (as in `exists_hasMaassFourierExpansion`) has the cosine
expansion `f(x + iy) = ∑_{n ≥ 1} c(n) √y K_{iR}(2πny) cos(2πnx)` with the coefficients
`c = maassCoefficients R f`. -/
lemma hasMaassCosineExpansion_maassCoefficients (hf : ContDiffOn ℝ ∞ f {z | 0 < z.im})
    (hper : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (hΔ : ∀ z : ℂ, 0 < z.im → hyperbolicLaplacian f z + maassEigenvalue R * f z = 0)
    (h0 : ∀ y : ℝ, 0 < y → ∫ t in (0 : ℝ)..1, f (t + y * Complex.I) = 0)
    (hb : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ, ‖f (t + y * Complex.I)‖ ≤ C * y ^ N)
    (hb' : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ, ‖fderiv ℝ f (t + y * Complex.I) Complex.I‖ ≤ C * y ^ N)
    (hs : IsEvenMaassForm f) : HasMaassCosineExpansion f R (maassCoefficients R f) := by
  rcases exists_hasMaassFourierExpansion hf hper hΔ h0 hb hb' with ⟨a, ha0, ha⟩
  have hc : HasMaassCosineExpansion f R fun n ↦ 2 * a n := ha.hasMaassCosineExpansion hs ha0
  rwa [hc.maassCoefficients_eq]

/-- **The sine expansion of an odd Maass form** (LMFDB `mf.maass.mwf.coefficients`): a smooth odd
function `f` on the upper half-plane with `f(z + 1) = f(z)`, `(Δ + 1/4 + R²) f = 0`, vanishing
constant term and moderate growth (as in `exists_hasMaassFourierExpansion`) has the sine expansion
`f(x + iy) = ∑_{n ≥ 1} c(n) √y K_{iR}(2πny) sin(2πnx)` with the coefficients
`c = maassCoefficients R f`. -/
lemma hasMaassSineExpansion_maassCoefficients (hf : ContDiffOn ℝ ∞ f {z | 0 < z.im})
    (hper : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (hΔ : ∀ z : ℂ, 0 < z.im → hyperbolicLaplacian f z + maassEigenvalue R * f z = 0)
    (h0 : ∀ y : ℝ, 0 < y → ∫ t in (0 : ℝ)..1, f (t + y * Complex.I) = 0)
    (hb : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ, ‖f (t + y * Complex.I)‖ ≤ C * y ^ N)
    (hb' : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ, ‖fderiv ℝ f (t + y * Complex.I) Complex.I‖ ≤ C * y ^ N)
    (hs : IsOddMaassForm f) : HasMaassSineExpansion f R (maassCoefficients R f) := by
  rcases exists_hasMaassFourierExpansion hf hper hΔ h0 hb hb' with ⟨a, ha0, ha⟩
  have hc : HasMaassSineExpansion f R fun n ↦ 2 * Complex.I * a n :=
    ha.hasMaassSineExpansion hs ha0
  rwa [hc.maassCoefficients_eq]

end UpperHalfPlane
