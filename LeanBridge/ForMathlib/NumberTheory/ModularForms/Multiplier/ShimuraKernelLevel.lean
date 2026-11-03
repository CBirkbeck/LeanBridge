import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraKernel
import Mathlib.Analysis.Fourier.ZMod

/-!
# Niwa's theta kernel in the ternary model: the law in the second variable

Poisson summation in `μ`, with the periodic weight `ψ⁻¹(μ)`, turns the mixed model of the kernel
`Θ_s(z, w) = ∑_{(C, μ)} ψ⁻¹(μ) S_s(z, w; N C, μ)` into the theta series of the ternary form
`b² - 4 a c`, of signature `(2, 1)`:

`Θ_s(z, w) = (√y / N) ∑_{(C, b, n)} ψ̂(n) exp(s R + 2 π i z (b² - 4 a c) - 4 π y p²)`,

where `a = N C / 4`, `c = n / N`, `R = a w² + b w + c`, `p = (a |w|² + b u + c) / v`, and `ψ̂` is
the finite Fourier transform of `ψ⁻¹`. The group `Γ₀(N / 2)` acts on `w` and on the lattice of the
`(N C / 4, b, n / N)`: `R` is multiplied by `(γ w + δ) ^ (-2)`, while `p` and `b² - 4 a c` are
invariant, and `n` is multiplied by `δ²` modulo `N`, so that `ψ̂` is multiplied by `ψ(δ) ^ 2`. Hence
`Θ_s(z, γ' w) = ψ(δ) ^ (-2) Θ_{s (γ w + δ) ^ (-2)}(z, w)`, and the kernel `Θ^(l)` of weight
`l + 1/2` in `z`, the coefficient of `s ^ l`, has the factor `ψ(δ) ^ (-2) (γ w + δ) ^ (-2 l)`.

## Main definitions

* `ModularForm.shimuraTernaryP`: the linear form `p`.
* `ModularForm.shimuraTernaryExp`: the exponent of the ternary theta series.
* `ModularForm.shimuraThetaTernary`: the ternary theta series.

## Main results

* `ModularForm.tsum_zmod_mul_cexp_gauss`: Poisson summation for a periodic weight and a Gaussian.
* `ModularForm.shimuraThetaGen_eq_ternary`: the mixed model is the ternary model.
* `ModularForm.shimuraThetaTernary_smul`: the law of the ternary theta series on `Γ₀(N / 2)`.
* `ModularForm.shimuraTheta_smul_right`: the law of Niwa's kernel in `w`.
-/

open Complex CongruenceSubgroup Filter ModularGroup Topology

open scoped Real MatrixGroups Manifold ComplexConjugate ZMod

open UpperHalfPlane hiding I I_re I_im

namespace ModularForm

section Poisson

variable {N : ℕ} [NeZero N] (φ : ZMod N → ℂ) {κ : ℝ} (ν : ℂ)

private lemma norm_cexp_gauss (μ : ℤ) : ‖cexp (-(π : ℂ) * κ * ((μ : ℂ) + ν) ^ 2)‖ =
    Real.exp (π * κ * ν.im ^ 2) * Real.exp (-(π * κ) * ((μ : ℝ) + ν.re) ^ 2) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  have e : -(π : ℂ) * κ * ((μ : ℂ) + ν) ^ 2 = ((-(π * κ) : ℝ) : ℂ) * ((μ : ℂ) + ν) ^ 2 := by
    push_cast
    ring1
  rw [e, re_ofReal_mul, sq, mul_re]
  simp only [add_re, intCast_re, add_im, intCast_im]
  ring1

private lemma summable_mul_cexp_gauss (hκ : 0 < κ) :
    Summable fun μ : ℤ ↦ φ μ * cexp (-(π : ℂ) * κ * ((μ : ℂ) + ν) ^ 2) := by
  have hp : 0 < π := Real.pi_pos
  rcases Finite.exists_le (fun a : ZMod N ↦ ‖φ a‖) with ⟨K, hK⟩
  refine Summable.of_norm_bounded (((summable_exp_neg_mul_add_sq ν.re
    (mul_pos hp hκ)).mul_left (Real.exp (π * κ * ν.im ^ 2))).mul_left K) fun μ ↦ ?_
  rw [norm_mul, norm_cexp_gauss]
  exact mul_le_mul_of_nonneg_right (hK _) (by positivity)

/-- **Poisson summation for a periodic weight and a Gaussian**: for `φ` on `ℤ / N`, `κ > 0` and
`ν ∈ ℂ`,
`∑_μ φ(μ) exp(-π κ (μ + ν)²) = (√κ N)⁻¹ ∑_n φ̂(n) exp(-2 π i n ν / N - π n² / (κ N²))`,
with `φ̂` the finite Fourier transform of `φ`. -/
lemma tsum_zmod_mul_cexp_gauss (hκ : 0 < κ) : ∑' μ : ℤ,
    φ μ * cexp (-(π : ℂ) * κ * ((μ : ℂ) + ν) ^ 2) = ((Real.sqrt κ * N : ℝ) : ℂ)⁻¹ * ∑' n : ℤ,
      ZMod.dft φ (n : ZMod N) *
          cexp (-(2 * π * I * n * ν / N) - π * (n : ℂ) ^ 2 / (κ * (N : ℂ) ^ 2)) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hκ' : (κ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hκ.ne'
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hτ : 0 < (I * (κ : ℂ) * (N : ℂ) ^ 2).im := by
    have e : I * (κ : ℂ) * (N : ℂ) ^ 2 = ((κ * (N : ℝ) ^ 2 : ℝ) : ℂ) * I := by
      push_cast
      ring1
    rw [e]
    simp only [mul_im, ofReal_re, I_im, I_re, mul_zero]
    positivity
  have hP : (-I * (I * (κ : ℂ) * (N : ℂ) ^ 2)) ^ (1 / 2 : ℂ) = ((Real.sqrt κ * N : ℝ) : ℂ) := by
    have e : -I * (I * (κ : ℂ) * (N : ℂ) ^ 2) = ((κ * (N : ℝ) ^ 2 : ℝ) : ℂ) := by
      push_cast
      linear_combination (-(κ : ℂ) * (N : ℂ) ^ 2) * I_sq
    rw [e, ← ofReal_ofNat, ← ofReal_one, ← ofReal_div,
      ← ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_mul hκ.le,
      Real.sqrt_sq hN'.le]
  have hq (r : Fin N) : ∑' q : ℤ, φ ((q * N + (r : ℕ) : ℤ) : ZMod N) *
      cexp (-(π : ℂ) * κ * (((q * N + (r : ℕ) : ℤ) : ℂ) + ν) ^ 2) =
        φ ((r : ℕ) : ZMod N) * (((Real.sqrt κ * N : ℝ) : ℂ)⁻¹ * ∑' k : ℤ,
          cexp (2 * π * I * k * ((((r : ℕ) : ℂ) + ν) / N) -
            π * I * (k : ℂ) ^ 2 / (I * κ * (N : ℂ) ^ 2))) := by
    rw [← inv_inj.mpr hP, ← one_div, ← tsum_cexp_add_sq hτ, ← tsum_mul_left]
    refine tsum_congr fun q ↦ ?_
    congr 1
    · congr 1
      push_cast
      simp
    · congr 1
      push_cast
      field_simp
      linear_combination (-((q : ℂ) * N + ((r : ℕ) : ℂ) + ν) ^ 2) * I_sq
  have hτ₂ : 0 < (-1 / (I * (κ : ℂ) * (N : ℂ) ^ 2)).im := by
    have ht0 : I * (κ : ℂ) * (N : ℂ) ^ 2 ≠ 0 := fun h ↦ by simp [h] at hτ
    rw [neg_div, one_div, neg_im, inv_im, neg_div, neg_neg]
    exact div_pos hτ (normSq_pos.mpr ht0)
  have hsk (α : ℂ) : Summable fun k : ℤ ↦ cexp (2 * π * I * k * α -
      π * I * (k : ℂ) ^ 2 / (I * κ * (N : ℂ) ^ 2)) := by
    refine ((summable_jacobiTheta₂_term_iff α _).mpr hτ₂).congr fun k ↦ ?_
    rw [jacobiTheta₂_term]
    congr 1
    ring1
  have hk (k : ℤ) : ∑ r : Fin N, φ ((r : ℕ) : ZMod N) * cexp (2 * π * I * k *
      ((((r : ℕ) : ℂ) + ν) / N) - π * I * (k : ℂ) ^ 2 / (I * κ * (N : ℂ) ^ 2)) =
        ZMod.dft φ ((-k : ℤ) : ZMod N) * cexp (-(2 * π * I * (-k : ℤ) * ν / N) -
          π * ((-k : ℤ) : ℂ) ^ 2 / (κ * (N : ℂ) ^ 2)) := by
    rw [ZMod.dft_apply, Finset.sum_mul, ← ZMod.sum_range_natCast_eq, ← Fin.sum_univ_eq_sum_range
      (fun r : ℕ ↦ ZMod.stdAddChar (-((r : ZMod N) * ((-k : ℤ) : ZMod N))) • φ (r : ZMod N) *
        cexp (-(2 * π * I * (-k : ℤ) * ν / N) - π * ((-k : ℤ) : ℂ) ^ 2 / (κ * (N : ℂ) ^ 2))) N]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have e : -(((r : ℕ) : ZMod N) * ((-k : ℤ) : ZMod N)) = (((r : ℕ) * k : ℤ) : ZMod N) := by
      push_cast
      ring1
    have h2 : cexp (2 * π * I * k * ((((r : ℕ) : ℂ) + ν) / N) -
        π * I * (k : ℂ) ^ 2 / (I * κ * (N : ℂ) ^ 2)) =
          cexp (2 * π * I * (((r : ℕ) * k : ℤ) : ℂ) / N) * cexp (-(2 * π * I * (-k : ℤ) * ν / N) -
            π * ((-k : ℤ) : ℂ) ^ 2 / (κ * (N : ℂ) ^ 2)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring1
    rw [e, ZMod.stdAddChar_coe, smul_eq_mul, h2]
    ring1
  rw [TauCeti.tsum_int_eq_sum_fin_tsum (summable_mul_cexp_gauss φ ν hκ) N]
  simp_rw [hq]
  have h1 : ∑ r : Fin N, φ ((r : ℕ) : ZMod N) * (((Real.sqrt κ * N : ℝ) : ℂ)⁻¹ * ∑' k : ℤ,
      cexp (2 * π * I * k * ((((r : ℕ) : ℂ) + ν) / N) -
        π * I * (k : ℂ) ^ 2 / (I * κ * (N : ℂ) ^ 2))) =
          ((Real.sqrt κ * N : ℝ) : ℂ)⁻¹ * ∑' k : ℤ, ∑ r : Fin N, φ ((r : ℕ) : ZMod N) *
            cexp (2 * π * I * k * ((((r : ℕ) : ℂ) + ν) / N) -
              π * I * (k : ℂ) ^ 2 / (I * κ * (N : ℂ) ^ 2)) := by
    rw [Summable.tsum_finsetSum fun r _ ↦ (hsk _).mul_left _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [tsum_mul_left]
    ring1
  rw [h1]
  simp_rw [hk]
  congr 1
  exact (Equiv.neg ℤ).tsum_eq fun n : ℤ ↦ ZMod.dft φ (n : ZMod N) *
    cexp (-(2 * π * I * n * ν / N) - π * (n : ℂ) ^ 2 / (κ * (N : ℂ) ^ 2))

end Poisson

section Ternary

variable (s : ℂ) (z w : ℍ) {N : ℕ} [NeZero N]

/-- The linear form `p = (a |w|² + b u + c) / v` on the ternary space, for `w = u + i v`: the
component of `(a, b, c)` along the negative line determined by `w`. -/
noncomputable def shimuraTernaryP (a b c : ℝ) : ℝ :=
  (a * (w.re ^ 2 + w.im ^ 2) + b * w.re + c) / w.im

/-- The exponent `s R + 2 π i z (b² - 4 a c) - 4 π y p²` of the ternary theta series, with
`R = a w² + b w + c` and `p = shimuraTernaryP w a b c`. -/
noncomputable def shimuraTernaryExp (a b c : ℝ) : ℂ :=
  s * ((a : ℂ) * (w : ℂ) ^ 2 + (b : ℂ) * w + c) + 2 * π * I * z * ((b : ℂ) ^ 2 - 4 * a * c) -
    4 * π * z.im * (shimuraTernaryP w a b c : ℂ) ^ 2

variable {s} in
private lemma exp_algebra₁ {p i x y u v C μ b : ℂ} (hp : p ≠ 0) (hy : y ≠ 0) (hv : v ≠ 0) :
    -(p * v ^ 2 / (4 * y)) * (C * (x + i * y) + μ) * (C * (x - i * y) + μ) +
      2 * p * i * ((b + C * u / 2) ^ 2 * (x + i * y) + μ * u * (b + C * u / 4)) +
      (i * v * (b + C * u / 2 - v / (4 * y) * (C * (x - i * y) + μ)) * s +
        v ^ 2 / (16 * p * y) * s ^ 2) =
    -(p * (v ^ 2 / (4 * y)) * C ^ 2 * ((x + i * y) * (x - i * y))) +
      2 * p * i * (b + C * u / 2) ^ 2 * (x + i * y) +
      s * (-(i * (v ^ 2 / (4 * y)) * C * (x - i * y)) + i * v * (b + C * u / 2)) +
      v ^ 2 / (16 * p * y) * s ^ 2 +
      p * (v ^ 2 / (4 * y)) *
          (C * x + i * s / (2 * p) - 4 * i * y / v ^ 2 * u * (b + C * u / 4)) ^ 2 +
      -(p * (v ^ 2 / (4 * y))) *
          (μ + (C * x + i * s / (2 * p) - 4 * i * y / v ^ 2 * u * (b + C * u / 4))) ^ 2 := by
  field_simp
  ring1

variable {s} in
private lemma exp_algebra₂ {p i x y u v C n b : ℂ} (hp : p ≠ 0) (hy : y ≠ 0) (hv : v ≠ 0) :
    (-(p * (v ^ 2 / (4 * y)) * C ^ 2 * ((x + i * y) * (x - i * y))) +
      2 * p * i * (b + C * u / 2) ^ 2 * (x + i * y) +
      s * (-(i * (v ^ 2 / (4 * y)) * C * (x - i * y)) + i * v * (b + C * u / 2)) +
      v ^ 2 / (16 * p * y) * s ^ 2 +
      p * (v ^ 2 / (4 * y)) *
          (C * x + i * s / (2 * p) - 4 * i * y / v ^ 2 * u * (b + C * u / 4)) ^ 2) +
      (-(2 * p * i * n * (C * x + i * s / (2 * p) - 4 * i * y / v ^ 2 * u * (b + C * u / 4))) -
        p * n ^ 2 / (v ^ 2 / (4 * y))) -
      (s * (C / 4 * (u + i * v) ^ 2 + b * (u + i * v) + n) +
        2 * p * i * (x + i * y) * (b ^ 2 - 4 * (C / 4) * n) -
        4 * p * y * ((C / 4 * (u ^ 2 + v ^ 2) + b * u + n) / v) ^ 2) =
    (p * (v ^ 2 / (4 * y)) * C ^ 2 * y ^ 2 + 2 * p * (b + C * u / 2) ^ 2 * y +
      s * (v ^ 2 / (4 * y)) * C * y +
      p * (v ^ 2 / (4 * y)) * (s / (2 * p) - 4 * y / v ^ 2 * u * (b + C * u / 4)) ^ 2 -
      2 * p * n * (s / (2 * p) - 4 * y / v ^ 2 * u * (b + C * u / 4)) - s * (C / 4) * v ^ 2 -
      2 * p * y * (b ^ 2 - 4 * (C / 4) * n)) * (i ^ 2 + 1) := by
  field_simp
  ring1

variable (ψ : DirichletCharacter ℂ N)

/-- The weight `ψ̂(n) = ∑_ℓ ψ⁻¹(ℓ) e(-n ℓ / N)` of the ternary theta series, the finite Fourier
transform of `ψ⁻¹`. -/
noncomputable def shimuraGaussWeight (n : ℤ) : ℂ :=
  ZMod.dft (⇑(ψ⁻¹ : DirichletCharacter ℂ N)) (n : ZMod N)

private lemma sqrt_div_eq : ((w.im : ℂ) / 2) * ((Real.sqrt (w.im ^ 2 / (4 * z.im)) * N : ℝ) : ℂ)⁻¹ =
    ((Real.sqrt z.im / N : ℝ) : ℂ) := by
  have hy : 0 < z.im := z.im_pos
  have hv : 0 < w.im := w.im_pos
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have h1 : Real.sqrt (w.im ^ 2 / (4 * z.im)) = w.im / (2 * Real.sqrt z.im) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq hv.le, Real.sqrt_mul (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs : 0 < Real.sqrt z.im := Real.sqrt_pos.mpr hy
  rw [h1, ← ofReal_ofNat, ← ofReal_div, ← ofReal_inv, ← ofReal_mul]
  congr 1
  field_simp

lemma tsum_inv_mul_gen_term_eq (C b : ℤ) : ∑' μ : ℤ, ψ⁻¹ (μ : ZMod N) * (((w.im : ℂ) / 2) *
    cexp (shimuraKernelTermExp z w C μ b + (shimuraKernelAlpha z w C μ b * s +
      (shimuraKernelBeta z w : ℂ) * s ^ 2))) = ((Real.sqrt z.im / N : ℝ) : ℂ) * ∑' n : ℤ,
        shimuraGaussWeight ψ n * cexp (shimuraTernaryExp s z w ((C : ℝ) / 4) b ((n : ℝ) / N)) := by
  have hy : (z.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr z.im_ne_zero
  have hv : (w.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr w.im_ne_zero
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hκ : 0 < w.im ^ 2 / (4 * z.im) := by
    have h1 : 0 < z.im := z.im_pos
    have h2 : 0 < w.im := w.im_pos
    positivity
  have hκc : ((w.im ^ 2 / (4 * z.im) : ℝ) : ℂ) = (w.im : ℂ) ^ 2 / (4 * (z.im : ℂ)) := by
    push_cast
    rfl
  have hz : (z : ℂ) = (z.re : ℂ) + I * (z.im : ℂ) := by
    rw [mul_comm]
    exact (Complex.re_add_im (z : ℂ)).symm
  have hzb : conj (z : ℂ) = (z.re : ℂ) - I * (z.im : ℂ) := by
    rw [hz]
    simp [sub_eq_add_neg]
  have hw : (w : ℂ) = (w.re : ℂ) + I * (w.im : ℂ) := by
    rw [mul_comm]
    exact (Complex.re_add_im (w : ℂ)).symm
  let ν : ℂ := (C : ℂ) * z.re + I * s / (2 * π) -
    4 * I * z.im / (w.im : ℂ) ^ 2 * w.re * (b + C * w.re / 4)
  let E₁ : ℂ := -(π * ((w.im : ℂ) ^ 2 / (4 * z.im)) * (C : ℂ) ^ 2 *
      (((z.re : ℂ) + I * z.im) * ((z.re : ℂ) - I * z.im))) +
    2 * π * I * ((b : ℂ) + C * w.re / 2) ^ 2 * ((z.re : ℂ) + I * z.im) +
      s * (-(I * ((w.im : ℂ) ^ 2 / (4 * z.im)) * C * ((z.re : ℂ) - I * z.im)) +
        I * w.im * ((b : ℂ) + C * w.re / 2)) +
          (w.im : ℂ) ^ 2 / (16 * π * z.im) * s ^ 2 + π * ((w.im : ℂ) ^ 2 / (4 * z.im)) * ν ^ 2
  have h₁ (μ : ℤ) : shimuraKernelTermExp z w C μ b + (shimuraKernelAlpha z w C μ b * s +
      (shimuraKernelBeta z w : ℂ) * s ^ 2) = E₁ +
        -(π : ℂ) * ((w.im ^ 2 / (4 * z.im) : ℝ) : ℂ) * ((μ : ℂ) + ν) ^ 2 := by
    rw [hκc, shimuraKernelTermExp, shimuraKernelAlpha, shimuraKernelBeta, hzb, hz]
    push_cast
    exact (exp_algebra₁ hp hy hv).trans (by ring1)
  have h₂ (n : ℤ) : E₁ + (-(2 * π * I * n * ν / N) -
      π * (n : ℂ) ^ 2 / (((w.im ^ 2 / (4 * z.im) : ℝ) : ℂ) * (N : ℂ) ^ 2)) =
        shimuraTernaryExp s z w ((C : ℝ) / 4) b ((n : ℝ) / N) := by
    have e : -(2 * (π : ℂ) * I * n * ν / N) -
        π * (n : ℂ) ^ 2 / (((w.im ^ 2 / (4 * z.im) : ℝ) : ℂ) * (N : ℂ) ^ 2) =
          -(2 * π * I * ((n : ℂ) / N) * ν) -
            π * ((n : ℂ) / N) ^ 2 / ((w.im : ℂ) ^ 2 / (4 * z.im)) := by
      rw [hκc]
      field_simp
    rw [e]
    refine (sub_eq_zero.mp ((exp_algebra₂ (p := (π : ℂ)) (i := I) (x := (z.re : ℂ))
      (y := (z.im : ℂ)) (u := (w.re : ℂ)) (v := (w.im : ℂ)) (s := s) (C := (C : ℂ))
      (n := (n : ℂ) / N) (b := (b : ℂ)) hp hy hv).trans
        (by rw [I_sq, neg_add_cancel, mul_zero]))).trans ?_
    rw [shimuraTernaryExp, shimuraTernaryP, hw, hz]
    push_cast
    rfl
  simp_rw [h₁, Complex.exp_add]
  have h₃ : ∑' μ : ℤ, ψ⁻¹ (μ : ZMod N) * (((w.im : ℂ) / 2) * (cexp E₁ *
      cexp (-(π : ℂ) * ((w.im ^ 2 / (4 * z.im) : ℝ) : ℂ) * ((μ : ℂ) + ν) ^ 2))) =
        ((w.im : ℂ) / 2) * cexp E₁ * ∑' μ : ℤ, ψ⁻¹ (μ : ZMod N) *
          cexp (-(π : ℂ) * ((w.im ^ 2 / (4 * z.im) : ℝ) : ℂ) * ((μ : ℂ) + ν) ^ 2) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun μ ↦ by ring1
  have h₄ : ∑' n : ℤ, shimuraGaussWeight ψ n *
      cexp (shimuraTernaryExp s z w ((C : ℝ) / 4) b ((n : ℝ) / N)) = cexp E₁ * ∑' n : ℤ,
        shimuraGaussWeight ψ n * cexp (-(2 * π * I * n * ν / N) -
          π * (n : ℂ) ^ 2 / (((w.im ^ 2 / (4 * z.im) : ℝ) : ℂ) * (N : ℂ) ^ 2)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    rw [← h₂ n, Complex.exp_add]
    ring1
  rw [h₃, tsum_zmod_mul_cexp_gauss (⇑ψ⁻¹) ν hκ, ← sqrt_div_eq z w, h₄]
  simp only [shimuraGaussWeight]
  ring1

/-- The **ternary theta series**
`(√y / N) ∑_{(C, b, n)} ψ̂(n) exp(s R + 2 π i z (b² - 4 a c) - 4 π y p²)`, with `a = N C / 4`,
`c = n / N`, where `ψ̂` is the finite Fourier transform of `ψ⁻¹`. -/
noncomputable def shimuraThetaTernary : ℂ :=
  ((Real.sqrt z.im / N : ℝ) : ℂ) * ∑' p : ℤ × ℤ × ℤ, shimuraGaussWeight ψ p.2.2 *
    cexp (shimuraTernaryExp s z w ((N : ℝ) * p.1 / 4) p.2.1 ((p.2.2 : ℝ) / N))

private lemma exponent_ternary_le {r y v a R p Q D A : ℝ} (hy : 0 < y) (hv : 0 < v)
    (hR : R ^ 2 = A ^ 2 * v ^ 2 + v ^ 2 * D ^ 2) (hp : p = A + 2 * a * v)
    (hQ : Q = R ^ 2 / v ^ 2 - p ^ 2) : r * R - 2 * π * y * Q - 4 * π * y * p ^ 2 ≤
      r ^ 2 * v ^ 2 / (4 * π * y) - 2 * π * y * v ^ 2 * a ^ 2 - π * y * D ^ 2 - π * y * p ^ 2 := by
  have hπ : 0 < π := Real.pi_pos
  have h1 : r * R ≤ π * y * (R ^ 2 / v ^ 2) + r ^ 2 * v ^ 2 / (4 * π * y) := by
    have h3 : 0 ≤ (2 * π * y * R - r * v ^ 2) ^ 2 := sq_nonneg _
    have e : π * y * (R ^ 2 / v ^ 2) + r ^ 2 * v ^ 2 / (4 * π * y) - r * R =
        (2 * π * y * R - r * v ^ 2) ^ 2 / (4 * π * y * v ^ 2) := by
      field_simp
      ring1
    have h4 : 0 ≤ (2 * π * y * R - r * v ^ 2) ^ 2 / (4 * π * y * v ^ 2) := by positivity
    linarith
  have h2 : R ^ 2 / v ^ 2 = A ^ 2 + D ^ 2 := by
    rw [hR]
    field_simp
  have h5 : 2 * (v ^ 2 * a ^ 2) ≤ A ^ 2 + p ^ 2 := by
    rw [hp]
    nlinarith [sq_nonneg (A + a * v)]
  have h6 : 0 ≤ π * y := by positivity
  have h7 : π * y * (2 * (v ^ 2 * a ^ 2)) ≤ π * y * (A ^ 2 + p ^ 2) :=
    mul_le_mul_of_nonneg_left h5 h6
  rw [hQ, h2]
  rw [h2] at h1
  nlinarith

lemma norm_cexp_shimuraTernaryExp_le (a b c : ℝ) : ‖cexp (shimuraTernaryExp s z w a b c)‖ ≤
    Real.exp (‖s‖ ^ 2 * w.im ^ 2 / (4 * π * z.im)) *
      (Real.exp (-(2 * π * z.im * w.im ^ 2) * a ^ 2) *
        (Real.exp (-(π * z.im) * (b + 2 * a * w.re) ^ 2) *
          Real.exp (-(π * z.im) * shimuraTernaryP w a b c ^ 2))) := by
  have hy : 0 < z.im := z.im_pos
  have hv : 0 < w.im := w.im_pos
  have hw : (w : ℂ) = (w.re : ℂ) + (w.im : ℂ) * I := (Complex.re_add_im (w : ℂ)).symm
  let A : ℝ := (a * (w.re ^ 2 - w.im ^ 2) + b * w.re + c) / w.im
  let D : ℝ := b + 2 * a * w.re
  have hRc : (a : ℂ) * (w : ℂ) ^ 2 + (b : ℂ) * w + c =
      ((A * w.im : ℝ) : ℂ) + ((w.im * D : ℝ) : ℂ) * I := by
    have e : A * w.im = a * (w.re ^ 2 - w.im ^ 2) + b * w.re + c := by
      simp only [A]
      field_simp
    rw [e, hw]
    simp only [D]
    push_cast
    linear_combination (a : ℂ) * (w.im : ℂ) ^ 2 * I_sq
  have hRn :
      ‖(a : ℂ) * (w : ℂ) ^ 2 + (b : ℂ) * w + c‖ ^ 2 = A ^ 2 * w.im ^ 2 + w.im ^ 2 * D ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hRc, Complex.normSq_add_mul_I]
    ring1
  have hp : shimuraTernaryP w a b c = A + 2 * a * w.im := by
    simp only [shimuraTernaryP, A]
    field_simp
    ring1
  have hQ : b ^ 2 - 4 * a * c = ‖(a : ℂ) * (w : ℂ) ^ 2 + (b : ℂ) * w + c‖ ^ 2 / w.im ^ 2 -
      shimuraTernaryP w a b c ^ 2 := by
    rw [hRn, hp]
    simp only [A]
    field_simp
    ring1
  have hre : (shimuraTernaryExp s z w a b c).re ≤
      ‖s‖ * ‖(a : ℂ) * (w : ℂ) ^ 2 + (b : ℂ) * w + c‖ - 2 * π * z.im * (b ^ 2 - 4 * a * c) -
        4 * π * z.im * shimuraTernaryP w a b c ^ 2 := by
    have e1 : (2 * (π : ℂ) * I * z * ((b : ℂ) ^ 2 - 4 * a * c)) =
        ((2 * π * (b ^ 2 - 4 * a * c) : ℝ) : ℂ) * (I * z) := by
      push_cast
      ring1
    have e2 : (4 * (π : ℂ) * z.im * (shimuraTernaryP w a b c : ℂ) ^ 2) =
        ((4 * π * z.im * shimuraTernaryP w a b c ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [shimuraTernaryExp, e1, e2, sub_re, add_re, ofReal_re, re_ofReal_mul, I_mul_re]
    have e3 : (z : ℂ).im = z.im := rfl
    rw [e3]
    have h1 : (s * ((a : ℂ) * (w : ℂ) ^ 2 + (b : ℂ) * w + c)).re ≤
        ‖s‖ * ‖(a : ℂ) * (w : ℂ) ^ 2 + (b : ℂ) * w + c‖ :=
      (Complex.re_le_norm _).trans_eq (norm_mul _ _)
    nlinarith
  rw [Complex.norm_exp, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr <| hre.trans <|
    (exponent_ternary_le (r := ‖s‖) (a := a) hy hv hRn hp hQ).trans (le_of_eq ?_)
  simp only [D]
  ring1

lemma summable_shimuraThetaTernary : Summable fun p : ℤ × ℤ × ℤ ↦ shimuraGaussWeight ψ p.2.2 *
    cexp (shimuraTernaryExp s z w ((N : ℝ) * p.1 / 4) p.2.1 ((p.2.2 : ℝ) / N)) := by
  have hy : 0 < z.im := z.im_pos
  have hv : 0 < w.im := w.im_pos
  have hp : 0 < π := Real.pi_pos
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  rcases Finite.exists_le (fun y : ZMod N ↦ ‖ZMod.dft (⇑(ψ⁻¹ : DirichletCharacter ℂ N)) y‖) with
    ⟨K, hK⟩
  refine Summable.of_norm_bounded (((summable_triple_gauss (fun c : ℤ ↦ (N : ℝ) * c / 4 * 2 * w.re)
      (fun c b ↦ (N : ℝ) * ((N : ℝ) * c / 4 * (w.re ^ 2 + w.im ^ 2) + b * w.re))
      (t₁ := 2 * π * z.im * w.im ^ 2 * ((N : ℝ) / 4) ^ 2) (t₂ := π * z.im)
      (t₃ := π * z.im / ((N : ℝ) * w.im) ^ 2) (by positivity) (by positivity)
      (by positivity)).mul_left (Real.exp (‖s‖ ^ 2 * w.im ^ 2 / (4 * π * z.im)))).mul_left K)
    fun p ↦ ?_
  rw [norm_mul]
  refine mul_le_mul (hK _) ((norm_cexp_shimuraTernaryExp_le s z w _ _ _).trans_eq ?_)
    (norm_nonneg _) ((norm_nonneg _).trans (hK 0))
  have e1 : -(2 * π * z.im * w.im ^ 2) * ((N : ℝ) * p.1 / 4) ^ 2 =
      -(2 * π * z.im * w.im ^ 2 * ((N : ℝ) / 4) ^ 2) * (p.1 : ℝ) ^ 2 := by
    ring1
  have e2 : (p.2.1 : ℝ) + 2 * ((N : ℝ) * p.1 / 4) * w.re =
      (p.2.1 : ℝ) + (N : ℝ) * p.1 / 4 * 2 * w.re := by
    ring1
  have e3 : -(π * z.im) * shimuraTernaryP w ((N : ℝ) * p.1 / 4) p.2.1 ((p.2.2 : ℝ) / N) ^ 2 =
      -(π * z.im / ((N : ℝ) * w.im) ^ 2) * ((p.2.2 : ℝ) +
        (N : ℝ) * ((N : ℝ) * p.1 / 4 * (w.re ^ 2 + w.im ^ 2) + p.2.1 * w.re)) ^ 2 := by
    rw [shimuraTernaryP]
    field_simp
    ring1
  rw [e1, e2, e3]

/-- **The mixed model is the ternary model**: by Poisson summation in `μ`, the generating kernel
`Θ_s(z, w) = ∑_{(C, μ)} ψ⁻¹(μ) S_s(z, w; N C, μ)` is the ternary theta series. -/
lemma shimuraThetaGen_eq_ternary : shimuraThetaGen ψ s z w = shimuraThetaTernary s z w ψ := by
  let e : ℤ × ℤ × ℤ ≃ (ℤ × ℤ) × ℤ :=
    { toFun := fun t ↦ ((t.1, t.2.2), t.2.1)
      invFun := fun p ↦ (p.1.1, p.2, p.1.2)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let F : (ℤ × ℤ) × ℤ → ℂ := fun p ↦ ψ⁻¹ (p.1.2 : ZMod N) * (((w.im : ℂ) / 2) *
    cexp (shimuraKernelTermExp z w ((N : ℤ) * p.1.1) p.1.2 p.2 +
      (shimuraKernelAlpha z w ((N : ℤ) * p.1.1) p.1.2 p.2 * s +
        (shimuraKernelBeta z w : ℂ) * s ^ 2)))
  have hs : Summable fun t : ℤ × ℤ × ℤ ↦ F (e t) :=
    e.summable_iff.mpr (summable_inv_mul_gen_term ψ s z w)
  have h0 : shimuraThetaGen ψ s z w = ∑' t : ℤ × ℤ × ℤ, F (e t) :=
    (tsum_inv_mul_gen_term ψ s z w).symm.trans (e.tsum_eq F).symm
  rw [h0, hs.tsum_prod, shimuraThetaTernary, (summable_shimuraThetaTernary s z w ψ).tsum_prod,
    ← tsum_mul_left]
  refine tsum_congr fun c ↦ ?_
  rw [(hs.prod_factor c).tsum_prod,
    ((summable_shimuraThetaTernary s z w ψ).prod_factor c).tsum_prod, ← tsum_mul_left]
  refine tsum_congr fun b ↦ ?_
  have ec : (((N : ℤ) * c : ℤ) : ℝ) / 4 = (N : ℝ) * c / 4 := by
    push_cast
    rfl
  exact (tsum_inv_mul_gen_term_eq s z w ψ ((N : ℤ) * c) b).trans (by simp only [ec])

end Ternary

section TernaryLaw

variable (s : ℂ) (z w : ℍ) (γ : SL(2, ℤ)) (a b c : ℝ)

/-- The action of `γ = (α, β; γ', δ)` on the coefficient `a` of the ternary space. -/
private def actA : ℝ :=
  a * (γ 0 0 : ℝ) ^ 2 + b * γ 0 0 * γ 1 0 + c * (γ 1 0 : ℝ) ^ 2

private def actB : ℝ :=
  2 * a * γ 0 0 * γ 0 1 + b * (γ 0 0 * γ 1 1 + γ 0 1 * γ 1 0) + 2 * c * γ 1 0 * γ 1 1

private def actC : ℝ :=
  a * (γ 0 1 : ℝ) ^ 2 + b * γ 0 1 * γ 1 1 + c * (γ 1 1 : ℝ) ^ 2

private lemma ofReal_re_im : ((w.re : ℝ) : ℂ) = ((w : ℂ) + conj (w : ℂ)) / 2 := by
  have e : ((2 * (w : ℂ).re : ℝ) : ℂ) = 2 * (w.re : ℂ) := by
    push_cast
    rfl
  rw [Complex.add_conj, e]
  ring1

private lemma ofReal_sq_add_sq : ((w.re ^ 2 + w.im ^ 2 : ℝ) : ℂ) = (w : ℂ) * conj (w : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_apply]
  push_cast
  have e1 : ((w : ℂ).re : ℂ) = (w.re : ℂ) := rfl
  have e2 : ((w : ℂ).im : ℂ) = (w.im : ℂ) := rfl
  rw [e1, e2]
  ring1

private lemma p_algebra {A B C D W Wb p q r v J Jb : ℂ} (hJ : J ≠ 0) (hJb : Jb ≠ 0) (hv : v ≠ 0)
    (hJe : J = C * W + D) (hJbe : Jb = C * Wb + D) :
    (p * ((A * W + B) / J * ((A * Wb + B) / Jb)) + q * (((A * W + B) / J + (A * Wb + B) / Jb) / 2) +
      r) / (v / (J * Jb)) = ((p * A ^ 2 + q * A * C + r * C ^ 2) * (W * Wb) +
        (2 * p * A * B + q * (A * D + B * C) + 2 * r * C * D) * ((W + Wb) / 2) +
          (p * B ^ 2 + q * B * D + r * D ^ 2)) / v := by
  field_simp
  rw [hJe, hJbe]
  ring1

private lemma quadratic_algebra {A B C D W p q r J : ℂ} (hJ : J ≠ 0) (hJe : J = C * W + D) :
    p * ((A * W + B) / J) ^ 2 + q * ((A * W + B) / J) + r =
      ((p * A ^ 2 + q * A * C + r * C ^ 2) * W ^ 2 +
        (2 * p * A * B + q * (A * D + B * C) + 2 * r * C * D) * W +
          (p * B ^ 2 + q * B * D + r * D ^ 2)) / J ^ 2 := by
  field_simp
  rw [hJe]
  ring1

lemma shimuraTernaryP_smul : shimuraTernaryP (γ • w) a b c =
    shimuraTernaryP w (actA γ a b c) (actB γ a b c) (actC γ a b c) := by
  have hv : (w.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr w.im_ne_zero
  refine Complex.ofReal_injective ?_
  have h1 (w' : ℍ) (a b c : ℝ) : ((shimuraTernaryP w' a b c : ℝ) : ℂ) =
      ((a : ℂ) * ((w' : ℂ) * conj (w' : ℂ)) + b * (((w' : ℂ) + conj (w' : ℂ)) / 2) + c) /
        (w'.im : ℂ) := by
    rw [shimuraTernaryP, ← ofReal_sq_add_sq, ← ofReal_re_im]
    push_cast
    rfl
  rw [h1, h1, conj_coe_smul, coe_smul_eq_div, coe_im_smul]
  simp only [actA, actB, actC]
  push_cast
  exact p_algebra (denomZ_ne_zero γ w) (denomZ_conj_ne_zero γ w) hv rfl rfl

private lemma actB_sq_sub :
    (actB γ a b c : ℂ) ^ 2 - 4 * actA γ a b c * actC γ a b c = (b : ℂ) ^ 2 - 4 * a * c := by
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - (γ 0 1 : ℂ) * γ 1 0 = 1 := by
    exact_mod_cast γ.fin_two_mul_sub_mul_eq_one
  simp only [actA, actB, actC]
  push_cast
  linear_combination
    ((γ 0 0 : ℂ) * γ 1 1 - (γ 0 1 : ℂ) * γ 1 0 + 1) * ((b : ℂ) ^ 2 - 4 * a * c) * hdet

private lemma quadratic_smul : (a : ℂ) * ((γ • w : ℍ) : ℂ) ^ 2 + (b : ℂ) * ((γ • w : ℍ) : ℂ) + c =
    ((actA γ a b c : ℂ) * (w : ℂ) ^ 2 + (actB γ a b c : ℂ) * w + (actC γ a b c : ℂ)) /
      ((γ 1 0 : ℂ) * w + γ 1 1) ^ 2 := by
  rw [coe_smul_eq_div]
  simp only [actA, actB, actC]
  push_cast
  exact quadratic_algebra (denomZ_ne_zero γ w) rfl

lemma shimuraTernaryExp_smul : shimuraTernaryExp s z (γ • w) a b c =
    shimuraTernaryExp (s / ((γ 1 0 : ℂ) * w + γ 1 1) ^ 2) z w (actA γ a b c) (actB γ a b c)
      (actC γ a b c) := by
  rw [shimuraTernaryExp, shimuraTernaryExp, shimuraTernaryP_smul, quadratic_smul, actB_sq_sub,
    div_eq_mul_inv s, div_eq_mul_inv _ (_ ^ 2)]
  ring1

/-- The action of `γ` on the lattice of the ternary theta series, for `N = 4 M` and
`γ = (α, β; 2 M g, δ)`: it sends `(N C / 4, b, n / N)` to `(N C' / 4, b', n' / N)`. -/
private def ternaryMap (M α β g δ : ℤ) (p : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (p.1 * α ^ 2 + 2 * p.2.1 * α * g + p.2.2 * g ^ 2,
    2 * M * p.1 * α * β + p.2.1 * (α * δ + β * (2 * M * g)) + p.2.2 * g * δ,
    4 * M ^ 2 * p.1 * β ^ 2 + 4 * M * p.2.1 * β * δ + p.2.2 * δ ^ 2)

private lemma ternaryMap_inv {M α β g δ : ℤ} (hdet : α * δ - β * (2 * M * g) = 1) (p : ℤ × ℤ × ℤ) :
    ternaryMap M δ (-β) (-g) α (ternaryMap M α β g δ p) = p := by
  rcases p with ⟨c, b, n⟩
  simp only [ternaryMap, Prod.mk_inj]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination ((α * δ - β * (2 * M * g) + 1) * c) * hdet
  · linear_combination ((α * δ - β * (2 * M * g) + 1) * b) * hdet
  · linear_combination ((α * δ - β * (2 * M * g) + 1) * n) * hdet

private lemma ternaryMap_inv' {M α β g δ : ℤ} (hdet : α * δ - β * (2 * M * g) = 1) (p : ℤ × ℤ × ℤ) :
    ternaryMap M α β g δ (ternaryMap M δ (-β) (-g) α p) = p := by
  rcases p with ⟨c, b, n⟩
  simp only [ternaryMap, Prod.mk_inj]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination ((α * δ - β * (2 * M * g) + 1) * c) * hdet
  · linear_combination ((α * δ - β * (2 * M * g) + 1) * b) * hdet
  · linear_combination ((α * δ - β * (2 * M * g) + 1) * n) * hdet

/-- The action of `γ` on the lattice, as a bijection. -/
private def ternaryEquiv {M α β g δ : ℤ} (hdet : α * δ - β * (2 * M * g) = 1) :
    ℤ × ℤ × ℤ ≃ ℤ × ℤ × ℤ where
  toFun := ternaryMap M α β g δ
  invFun := ternaryMap M δ (-β) (-g) α
  left_inv := ternaryMap_inv hdet
  right_inv := ternaryMap_inv' hdet

variable {N : ℕ} {M g : ℤ}

private lemma cast_N (hM : (N : ℤ) = 4 * M) : (N : ℝ) = 4 * M := by
  exact_mod_cast hM

private lemma det_eq' (hg : γ 1 0 = 2 * M * g) : γ 0 0 * γ 1 1 - γ 0 1 * (2 * M * g) = 1 := by
  rw [← hg]
  exact γ.fin_two_mul_sub_mul_eq_one

private lemma isUnit_of_det (hM : (N : ℤ) = 4 * M) (hg : γ 1 0 = 2 * M * g) :
    IsUnit ((γ 1 1 : ℤ) : ZMod N) := by
  have h1 : IsCoprime (γ 1 1) (2 * M) := ⟨γ 0 0, -(γ 0 1 * g), by
    linear_combination det_eq' γ hg⟩
  have h2 : IsCoprime (γ 1 1) 2 := h1.of_mul_right_left
  have h3 : IsCoprime (γ 1 1) (N : ℤ) := by
    have e : (N : ℤ) = 2 * (2 * M) := by
      rw [hM]
      ring1
    rw [e]
    exact h2.mul_right h1
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  exact h3.symm

variable [NeZero N] (ψ : DirichletCharacter ℂ N)

lemma shimuraGaussWeight_eq {n n' δ : ℤ} (hδ : IsUnit (δ : ZMod N))
    (hn : (n' : ZMod N) = n * δ ^ 2) :
    shimuraGaussWeight ψ n = ψ⁻¹ (δ : ZMod N) ^ 2 * shimuraGaussWeight ψ n' := by
  rcases hδ with ⟨u, hu⟩
  rw [shimuraGaussWeight, shimuraGaussWeight, ZMod.dft_apply, ZMod.dft_apply, hn, ← hu,
    ← Equiv.sum_comp (Units.mulRight (u ^ 2)) (fun j : ZMod N ↦
      ZMod.stdAddChar (-(j * (n : ZMod N))) • (ψ⁻¹ : DirichletCharacter ℂ N) j), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have e1 : ((Units.mulRight (u ^ 2)) j : ZMod N) = j * (u : ZMod N) ^ 2 := by
    simp
  have e2 : -(j * (u : ZMod N) ^ 2 * (n : ZMod N)) = -(j * ((n : ZMod N) * (u : ZMod N) ^ 2)) := by
    ring1
  rw [e1, e2, smul_eq_mul, smul_eq_mul, map_mul, map_pow]
  ring1

private lemma cast_M_ne_zero (hM : (N : ℤ) = 4 * M) : (M : ℝ) ≠ 0 := by
  intro h
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [cast_N hM, h, mul_zero] at hN
  exact hN rfl

private lemma actA_cast (hM : (N : ℤ) = 4 * M) (hg : γ 1 0 = 2 * M * g) (p : ℤ × ℤ × ℤ) :
    actA γ ((N : ℝ) * p.1 / 4) p.2.1 ((p.2.2 : ℝ) / N) =
      (N : ℝ) * ((ternaryMap M (γ 0 0) (γ 0 1) g (γ 1 1) p).1 : ℤ) / 4 := by
  have hM0 : (M : ℝ) ≠ 0 := cast_M_ne_zero hM
  simp only [actA, ternaryMap, hg]
  rw [cast_N hM]
  push_cast
  field_simp
  ring1

private lemma actB_cast (hM : (N : ℤ) = 4 * M) (hg : γ 1 0 = 2 * M * g) (p : ℤ × ℤ × ℤ) :
    actB γ ((N : ℝ) * p.1 / 4) p.2.1 ((p.2.2 : ℝ) / N) =
      ((ternaryMap M (γ 0 0) (γ 0 1) g (γ 1 1) p).2.1 : ℤ) := by
  have hM0 : (M : ℝ) ≠ 0 := cast_M_ne_zero hM
  simp only [actB, ternaryMap, hg]
  rw [cast_N hM]
  push_cast
  field_simp
  ring1

private lemma actC_cast (hM : (N : ℤ) = 4 * M) (p : ℤ × ℤ × ℤ) :
    actC γ ((N : ℝ) * p.1 / 4) p.2.1 ((p.2.2 : ℝ) / N) =
      ((ternaryMap M (γ 0 0) (γ 0 1) g (γ 1 1) p).2.2 : ℤ) / (N : ℝ) := by
  have hM0 : (M : ℝ) ≠ 0 := cast_M_ne_zero hM
  simp only [actC, ternaryMap]
  rw [cast_N hM]
  push_cast
  field_simp

/-- **The law of the ternary theta series**: for `N = 4 M` and `γ = (α, β; 2 M g, δ) ∈ Γ₀(N / 2)`,
`Θ_s(z, γ w) = ψ⁻¹(δ) ^ 2 Θ_{s (2 M g w + δ) ^ (-2)}(z, w)`. -/
lemma shimuraThetaTernary_smul (hM : (N : ℤ) = 4 * M) (hg : γ 1 0 = 2 * M * g) :
    shimuraThetaTernary s z (γ • w) ψ = ψ⁻¹ ((γ 1 1 : ℤ) : ZMod N) ^ 2 *
      shimuraThetaTernary (s / ((γ 1 0 : ℂ) * w + γ 1 1) ^ 2) z w ψ := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * (2 * M * g) = 1 := det_eq' γ hg
  have h : ∑' p : ℤ × ℤ × ℤ, shimuraGaussWeight ψ p.2.2 *
      cexp (shimuraTernaryExp s z (γ • w) ((N : ℝ) * p.1 / 4) p.2.1 ((p.2.2 : ℝ) / N)) =
        ψ⁻¹ ((γ 1 1 : ℤ) : ZMod N) ^ 2 * ∑' p : ℤ × ℤ × ℤ, shimuraGaussWeight ψ p.2.2 *
          cexp (shimuraTernaryExp (s / ((γ 1 0 : ℂ) * w + γ 1 1) ^ 2) z w ((N : ℝ) * p.1 / 4) p.2.1
            ((p.2.2 : ℝ) / N)) := by
    rw [← (ternaryEquiv hdet).tsum_eq fun p : ℤ × ℤ × ℤ ↦ shimuraGaussWeight ψ p.2.2 *
      cexp (shimuraTernaryExp (s / ((γ 1 0 : ℂ) * w + γ 1 1) ^ 2) z w ((N : ℝ) * p.1 / 4) p.2.1
        ((p.2.2 : ℝ) / N)), ← tsum_mul_left]
    refine tsum_congr fun p ↦ ?_
    have hn : (((ternaryEquiv hdet p).2.2 : ℤ) : ZMod N) =
        (p.2.2 : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) ^ 2 := by
      have h4 : (4 : ZMod N) * (M : ZMod N) = 0 := by
        have h5 : ((N : ℤ) : ZMod N) = 0 := by simp
        rw [hM] at h5
        push_cast at h5
        exact h5
      simp only [ternaryEquiv, ternaryMap, Equiv.coe_fn_mk]
      push_cast
      linear_combination ((M : ZMod N) * (p.1 : ZMod N) * ((γ 0 1 : ℤ) : ZMod N) ^ 2 +
        (p.2.1 : ZMod N) * ((γ 0 1 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N)) * h4
    rw [shimuraGaussWeight_eq ψ (isUnit_of_det γ hM hg) hn, shimuraTernaryExp_smul,
      actA_cast γ hM hg, actB_cast γ hM hg, actC_cast γ hM]
    simp only [ternaryEquiv, Equiv.coe_fn_mk]
    ring1
  rw [shimuraThetaTernary, shimuraThetaTernary, h]
  ring1

lemma shimuraThetaGen_smul_right (hM : (N : ℤ) = 4 * M) (hg : γ 1 0 = 2 * M * g) :
    shimuraThetaGen ψ s z (γ • w) = ψ⁻¹ ((γ 1 1 : ℤ) : ZMod N) ^ 2 *
      shimuraThetaGen ψ (s / ((γ 1 0 : ℂ) * w + γ 1 1) ^ 2) z w := by
  rw [shimuraThetaGen_eq_ternary, shimuraThetaGen_eq_ternary,
    shimuraThetaTernary_smul s z w γ ψ hM hg]

/-- **The law of Niwa's kernel in `w`**: for `N = 4 M` and `γ = (α, β; 2 M g, δ) ∈ Γ₀(N / 2)`, the
kernel of weight `l + 1/2` satisfies
`Θ^(l)(z, γ w) = ψ⁻¹(δ) ^ 2 (2 M g w + δ) ^ (-2 l) Θ^(l)(z, w)`. -/
lemma shimuraTheta_smul_right (hM : (N : ℤ) = 4 * M) (hg : γ 1 0 = 2 * M * g) (l : ℕ) :
    shimuraTheta ψ z (γ • w) l = ψ⁻¹ ((γ 1 1 : ℤ) : ZMod N) ^ 2 *
      (((γ 1 0 : ℂ) * w + γ 1 1) ^ (2 * l))⁻¹ * shimuraTheta ψ z w l := by
  refine eq_of_forall_hasSum_mul_pow (d := fun l ↦ ψ⁻¹ ((γ 1 1 : ℤ) : ZMod N) ^ 2 *
    (((γ 1 0 : ℂ) * w + γ 1 1) ^ (2 * l))⁻¹ * shimuraTheta ψ z w l)
    (fun s ↦ hasSum_shimuraTheta_mul_pow ψ s z (γ • w)) (fun s ↦ ?_) l
  have e : (fun l ↦ ψ⁻¹ ((γ 1 1 : ℤ) : ZMod N) ^ 2 * (shimuraTheta ψ z w l *
      (s / ((γ 1 0 : ℂ) * w + γ 1 1) ^ 2) ^ l)) = fun l ↦ ψ⁻¹ ((γ 1 1 : ℤ) : ZMod N) ^ 2 *
        (((γ 1 0 : ℂ) * w + γ 1 1) ^ (2 * l))⁻¹ * shimuraTheta ψ z w l * s ^ l := by
    funext l
    rw [div_pow, ← pow_mul, div_eq_mul_inv]
    ring1
  rw [← e, shimuraThetaGen_smul_right s z w γ ψ hM hg]
  exact (hasSum_shimuraTheta_mul_pow ψ (s / ((γ 1 0 : ℂ) * w + γ 1 1) ^ 2) z w).mul_left
    (ψ⁻¹ ((γ 1 1 : ℤ) : ZMod N) ^ 2)

end TernaryLaw

end ModularForm
