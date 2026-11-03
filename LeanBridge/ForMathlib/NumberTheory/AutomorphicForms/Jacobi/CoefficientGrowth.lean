import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Jacobi.FourierCoefficients
import Mathlib.NumberTheory.Modular

/-!
# Growth of the Fourier coefficients of Jacobi forms

The Fourier coefficients `c(n, r)` of a Jacobi form `φ ∈ J_{k,N}`, `N ≥ 1`, grow polynomially:
`|c(n, r)| ≤ C (1 + |n|)^k`, and `J_{k,N} = 0` for `k ≤ 0`. The proof is Hecke's argument, carried
out with the transformation laws of `φ`:

* the function `|φ(τ, z)| e^{-2πN y²/v}`, `τ = u + iv`, `z = x + iy` (`ModularForm.jacobiNorm`), is
  invariant under the Heisenberg group, and is multiplied by `|cτ + d|^k` under
  `(a, b; c, d) ∈ SL(2, ℤ)`;
* on the region `v ≥ 1/2`, `|y| ≤ v/2`, which meets every orbit of the Jacobi group, it is at most
  `C₀ = ∑ |c(n, r)| (e^{-π(n + r/2)} + e^{-π(n - r/2)})` (`ModularForm.jacobiSupBound`): its term is
  `|c(n, r)| e^{-2πv(n + rα + Nα²)}` with `α = y/v`, and `n + rα + Nα² ≥ 0` on the support
  `4nN ≥ r²`;
* for `τ ∈ ℍ` there is `γ = (a, b; c, d) ∈ SL(2, ℤ)` with `Im γτ ≥ 1/2` and `|cτ + d| ≤ 1`, which
  gives `|φ(τ, u)| |cτ + d|^k ≤ C₀` for real `u`. As `|cτ + d| ≥ Im τ` when `Im τ ≤ 1`, this gives
  `|φ(τ, u)| ≤ C₀ (Im τ)^{-k}` for `k ≥ 0`, and `|φ(τ, u)| ≤ C₀` for `k ≤ 0`;
* the coefficient `c(n, r) e^{-2πny}` is the Fourier coefficient of `(x, u) ↦ φ(x + iy, u)` on
  the torus `(ℝ / ℤ)²`, so it is bounded by the supremum `C₀ y^{-k}`; take `y = 1/(1 + |n|)`.
  For `k ≤ 0`, Bessel's inequality on the torus, applied to the `K` coefficients
  `c(n + λr + Nλ², r + 2Nλ) = c(n, r)`, `0 ≤ λ < K`, gives `K |c(n, r)|² ≤ C₀² e^{4π}` for every
  `K`, so `c(n, r) = 0`.

In index `1`, `n - |r|/2 ≥ 0` on the support `4n ≥ r²`, so that `|φ(τ, z)|` itself is at most `C₀`
on the region `v ≥ 1/2`, `|y| ≤ v/2`. For a Jacobi cusp form,
`n + rα + Nα² ≥ (4nN - r²)/(4N) ≥ 1/(4N)` on the support, which makes
`|φ(τ, z)| v^{k/2} e^{-2πN y²/v}` bounded on all of `ℍ × ℂ` (Eichler and Zagier, §1).

The polynomial bound is the hypothesis of
`SiegelUpperHalfSpace.maassLift_mem_scalarModularForms_of_norm_jacobiCoeff_le`.

## Main definitions

* `ModularForm.jacobiSupBound`: the constant `∑ |c(n, r)| (e^{-π(n + r/2)} + e^{-π(n - r/2)})`.
* `ModularForm.jacobiNorm`: the function `|φ(τ, z)| e^{-2πN y²/v}`.

## Main results

* `UnitAddTorus.norm_le_of_norm_tsum_mFourier_le`: the coefficients of an absolutely convergent
  Fourier series on the torus are bounded by the supremum of its sum.
* `UnitAddTorus.sum_norm_sq_le_of_norm_tsum_mFourier_le`: Bessel's inequality for such series.
* `ModularForm.jacobiNorm_add_mul`: invariance under `z ↦ z + aτ`.
* `ModularForm.jacobiNorm_smul`: the transformation under `SL(2, ℤ)`.
* `ModularForm.jacobiNorm_le_jacobiSupBound`: the bound on the region `v ≥ 1/2`, `|y| ≤ v/2`.
* `ModularForm.jacobiNorm_mul_norm_denom_zpow_le`: the bound under `SL(2, ℤ)`.
* `ModularForm.norm_jacobiCoeff_le_of_mem_jacobiFormSpace`: Hecke's bound
  `|c(n, r)| ≤ C (1 + |n|)^k` for `φ ∈ J_{k,N}`, `N ≥ 1`.
* `ModularForm.eq_zero_of_mem_jacobiFormSpace_of_nonpos`: `J_{k,N} = 0` for `k ≤ 0`, `N ≥ 1`.
* `ModularForm.exists_jacobiNorm_mul_sqrt_zpow_le`: `|φ(τ, z)| v^{k/2} e^{-2πN y²/v}` is bounded for
  a Jacobi cusp form.
-/

open Complex MeasureTheory Real UnitAddTorus

open UpperHalfPlane hiding I

open scoped MatrixGroups

attribute [local instance] unitAddCircleHaarMeasureSpace

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι] {c : (ι → ℤ) → ℂ} {B : ℝ} (m : ι → ℤ)

private lemma summable_smul_mFourier (hc : Summable c) : Summable fun k ↦ c k • mFourier k :=
  .of_norm <| by simpa [norm_smul, mFourier_norm] using hc.norm

private lemma eq_inner_toLp (hc : Summable c) :
    c m = inner ℂ (mFourierLp 2 m) (ContinuousMap.toLp 2 volume ℂ (∑' k, c k • mFourier k)) := by
  have hm : HasSum (fun k ↦ if k = m then c k else 0) (inner ℂ (mFourierLp 2 m)
      (ContinuousMap.toLp 2 volume ℂ (∑' k, c k • mFourier k))) := by
    simpa only [ContinuousLinearMap.comp_apply, map_smul, innerSL_apply_apply,
      orthonormal_iff_ite.mp orthonormal_mFourier m, smul_eq_mul, mul_ite, mul_one, mul_zero,
      eq_comm (a := m)] using ((innerSL ℂ (mFourierLp 2 m)).comp
        (ContinuousMap.toLp 2 volume ℂ)).hasSum (summable_smul_mFourier hc).hasSum
  exact (hasSum_ite_eq m (c m)).unique (hm.congr_fun fun b ↦ by
    split_ifs with hb
    · rw [hb]
    · rfl)

private lemma norm_toLp_le (hc : Summable c) (h : ∀ x, ‖∑' k, c k * mFourier k x‖ ≤ B) :
    ‖ContinuousMap.toLp 2 volume ℂ (∑' k, c k • mFourier k)‖ ≤ B := by
  have hG : ‖∑' k, c k • mFourier k‖ ≤ B :=
    (ContinuousMap.norm_le _ ((norm_nonneg _).trans (h 0))).mpr fun x ↦ by
      rw [← ContinuousMap.tsum_apply (summable_smul_mFourier hc)]
      simpa using h x
  refine (((ContinuousMap.toLp 2 volume ℂ).le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) ?_)).trans hG
  refine (ContinuousMap.toLp_norm_le volume).trans ?_
  simp [measureUnivNNReal]

/-- **The coefficients of a Fourier series on the torus are bounded by its supremum**: if
`∑ c(k) e^{2πi k·x}` converges absolutely and its sum is bounded by `B` on `(ℝ / ℤ)^ι`, then
`|c(k)| ≤ B` for every `k`. -/
lemma norm_le_of_norm_tsum_mFourier_le (hc : Summable c) (h : ∀ x, ‖∑' k, c k * mFourier k x‖ ≤ B) :
    ‖c m‖ ≤ B := by
  rw [eq_inner_toLp m hc]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [orthonormal_mFourier.1 m, one_mul]
  exact norm_toLp_le hc h

/-- **Bessel's inequality for Fourier series on the torus**: if `∑ c(k) e^{2πi k·x}` converges
absolutely and its sum is bounded by `B` on `(ℝ / ℤ)^ι`, then `∑_{k ∈ s} |c(k)|² ≤ B²` for every
finite set `s` of frequencies. -/
lemma sum_norm_sq_le_of_norm_tsum_mFourier_le (hc : Summable c)
    (h : ∀ x, ‖∑' k, c k * mFourier k x‖ ≤ B) (s : Finset (ι → ℤ)) :
    ∑ m ∈ s, ‖c m‖ ^ 2 ≤ B ^ 2 := by
  have h1 : ∑ m ∈ s, ‖c m‖ ^ 2 = ∑ m ∈ s, ‖inner ℂ (mFourierLp 2 m)
      (ContinuousMap.toLp 2 volume ℂ (∑' k, c k • mFourier k))‖ ^ 2 :=
    Finset.sum_congr rfl fun m _ ↦ by
      rw [← eq_inner_toLp m hc]
  rw [h1]
  exact (orthonormal_mFourier.sum_inner_products_le _).trans
    (pow_le_pow_left₀ (norm_nonneg _) (norm_toLp_le hc h) 2)

end UnitAddTorus

namespace ModularForm

variable {k : ℤ} {N : ℕ} {φ : ℍ × ℂ → ℂ}

/-- The constant `∑_{n, r} |c(n, r)| (e^{-π(n + r/2)} + e^{-π(n - r/2)})` attached to
`f : ℍ × ℂ → ℂ` with Fourier coefficients `c(n, r)`. For a Jacobi form of index `N` the series
converges, and its sum bounds `|f(τ, z)| e^{-2πN (Im z)²/Im τ}` on the region `Im τ ≥ 1/2`,
`|Im z| ≤ Im τ / 2`, which meets every orbit of the Jacobi group `SL(2, ℤ) ⋉ ℤ²`. -/
noncomputable def jacobiSupBound (f : ℍ × ℂ → ℂ) : ℝ :=
  ∑' p : ℤ × ℤ, ‖jacobiCoeff f p‖ *
    (rexp (-(π * ((p.1 : ℝ) + p.2 / 2))) + rexp (-(π * ((p.1 : ℝ) - p.2 / 2))))

lemma jacobiSupBound_nonneg : 0 ≤ jacobiSupBound φ :=
  tsum_nonneg fun p ↦ by positivity

lemma norm_jacobiFourierExp (p : ℤ × ℤ) (x : ℍ × ℂ) :
    ‖jacobiFourierExp p x‖ = rexp (-(2 * π * (p.1 * x.1.im + p.2 * x.2.im))) := by
  rw [jacobiFourierExp, Complex.norm_exp]
  congr 1
  simp

/-- The point `(i/2, si/4)` of `ℍ × ℂ`. -/
private noncomputable def basePoint (s : ℝ) : ℍ × ℂ :=
  (mk (I / 2) (by simp), s * I / 4)

private lemma summable_mul_rexp (hφ : φ ∈ jacobiFormSpace k N) (s : ℝ) :
    Summable fun p : ℤ × ℤ ↦ ‖jacobiCoeff φ p‖ * rexp (-(π * ((p.1 : ℝ) + s * p.2 / 2))) :=
  (summable_norm_iff.mpr ((hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ)
    (basePoint s)).summable).congr fun p ↦ by
      rw [norm_mul, norm_jacobiFourierExp]
      congr 2
      simp [basePoint]
      ring1

lemma summable_jacobiSupBound (hφ : φ ∈ jacobiFormSpace k N) : Summable fun p : ℤ × ℤ ↦
    ‖jacobiCoeff φ p‖ *
        (rexp (-(π * ((p.1 : ℝ) + p.2 / 2))) + rexp (-(π * ((p.1 : ℝ) - p.2 / 2)))) :=
  ((summable_mul_rexp hφ 1).add (summable_mul_rexp hφ (-1))).congr fun p ↦ by
    rw [one_mul, neg_one_mul, neg_div, ← sub_eq_add_neg, ← mul_add]

lemma eq_zero_of_jacobiCoeff_eq_zero (hφ : φ ∈ jacobiFormSpace k N) (hc : jacobiCoeff φ = 0) :
    φ = 0 :=
  funext fun x ↦ (hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ x).unique <| by
    simp [hc]

variable (N φ) in
/-- The function `|φ(τ, z)| e^{-2πN y²/v}` on `ℍ × ℂ`, for `τ = u + iv`, `z = x + iy`. For a Jacobi
form `φ` of weight `k` and index `N` it is invariant under `z ↦ z + aτ + b`, and it is multiplied by
`|cτ + d|^k` under `(a, b; c, d) ∈ SL(2, ℤ)`, so that `|φ(τ, z)| v^{k/2} e^{-2πN y²/v}` is invariant
under the Jacobi group. -/
noncomputable def jacobiNorm (x : ℍ × ℂ) : ℝ :=
  ‖φ x‖ * rexp (-(2 * π * N * x.2.im ^ 2 / x.1.im))

variable (τ : ℍ) (z : ℂ) (a : ℤ) (γ : SL(2, ℤ))

/-- **The function `|φ(τ, z)| e^{-2πN y²/v}` is invariant under `z ↦ z + aτ`**, by the elliptic
transformation law. -/
lemma jacobiNorm_add_mul (hφ : φ ∈ jacobiFormSpace k N) :
    jacobiNorm N φ (τ, z + a * τ) = jacobiNorm N φ (τ, z) := by
  have hv : τ.im ≠ 0 := τ.im_pos.ne'
  have hre : (-2 * π * I * N * (a ^ 2 * τ + 2 * a * z)).re =
      2 * π * N * (a ^ 2 * τ.im + 2 * a * z.im) := by
    have h : -2 * π * I * N * (a ^ 2 * τ + 2 * a * z) =
        ((2 * π * N : ℝ) : ℂ) * -(I * (((a ^ 2 : ℝ) : ℂ) * τ + ((2 * a : ℝ) : ℂ) * z)) := by
      push_cast
      ring1
    rw [h, re_ofReal_mul, neg_re, I_mul_re, add_im, im_ofReal_mul, im_ofReal_mul, neg_neg]
    rfl
  rw [jacobiNorm, jacobiNorm]
  dsimp only
  rw [apply_add_mul_of_mem_jacobiFormSpace τ z a hφ, norm_mul, Complex.norm_exp, hre,
    mul_comm _ ‖φ _‖, mul_assoc, ← Real.exp_add]
  congr 2
  simp
  field_simp
  ring1

private lemma exp_identity {x y p c v : ℝ} (hv : v ≠ 0) (hn₀ : p ^ 2 + (c * v) ^ 2 ≠ 0) :
    -(c * ((2 * x * y * p - (x ^ 2 - y ^ 2) * (c * v)) / (p ^ 2 + (c * v) ^ 2))) -
      ((y * p - x * (c * v)) / (p ^ 2 + (c * v) ^ 2)) ^ 2 / (v / (p ^ 2 + (c * v) ^ 2)) =
        -(y ^ 2 / v) := by
  generalize hn : p ^ 2 + (c * v) ^ 2 = n at hn₀ ⊢
  field_simp
  rw [← hn]
  ring1

/-- **The transformation of `|φ(τ, z)| e^{-2πN y²/v}` under `SL(2, ℤ)`**: it is multiplied by
`|cτ + d|^k`, by the transformation law of `φ` and the identity
`c v Im(z²/(cτ + d)) + Im(z/(cτ + d))² |cτ + d|² = y²`. -/
lemma jacobiNorm_smul (hφ : φ ∈ jacobiFormSpace k N) :
    jacobiNorm N φ (γ • τ, z / denom γ τ) = ‖denom γ τ‖ ^ k * jacobiNorm N φ (τ, z) := by
  have hJ : denom γ τ ≠ 0 := denom_ne_zero γ τ
  have hv : τ.im ≠ 0 := τ.im_pos.ne'
  have him : (γ • τ).im = τ.im / normSq (denom γ τ) := ModularGroup.im_smul_eq_div_normSq γ τ
  have hn₀ : normSq (denom γ τ) ≠ 0 := (normSq_pos.mpr hJ).ne'
  have hJim : (denom γ τ).im = (γ 1 0 : ℝ) * τ.im := by
    rw [ModularGroup.denom_apply]
    simp
  have hre : (2 * π * I * N * (γ 1 0 : ℤ) * z ^ 2 / denom γ τ).re =
      -(2 * π * N * ((γ 1 0 : ℝ) * ((z ^ 2 / denom γ τ).im))) := by
    have h : 2 * π * I * N * (γ 1 0 : ℤ) * z ^ 2 / denom γ τ =
        ((2 * π * N * (γ 1 0 : ℝ) : ℝ) : ℂ) * I * (z ^ 2 / denom γ τ) := by
      push_cast
      ring1
    rw [h]
    simp
    ring1
  have hexp : (2 * π * I * N * (γ 1 0 : ℤ) * z ^ 2 / denom γ τ).re +
      -(2 * π * N * (z / denom γ τ).im ^ 2 / (γ • τ).im) = -(2 * π * N * z.im ^ 2 / τ.im) := by
    have h₁ : (z ^ 2 / denom γ τ).im = (2 * z.re * z.im * (denom γ τ).re -
        (z.re ^ 2 - z.im ^ 2) * (denom γ τ).im) / normSq (denom γ τ) := by
      rw [Complex.div_im, pow_two]
      simp
      ring1
    have h₂ : (z / denom γ τ).im =
        (z.im * (denom γ τ).re - z.re * (denom γ τ).im) / normSq (denom γ τ) := by
      rw [Complex.div_im]
      ring1
    have hn : normSq (denom γ τ) = (denom γ τ).re ^ 2 + ((γ 1 0 : ℝ) * τ.im) ^ 2 := by
      rw [normSq_apply, hJim]
      ring1
    have h₃ : -((γ 1 0 : ℝ) * ((2 * z.re * z.im * (denom γ τ).re -
        (z.re ^ 2 - z.im ^ 2) * (denom γ τ).im) / normSq (denom γ τ))) -
          ((z.im * (denom γ τ).re - z.re * (denom γ τ).im) / normSq (denom γ τ)) ^ 2 /
            (τ.im / normSq (denom γ τ)) = -(z.im ^ 2 / τ.im) := by
      rw [hn, hJim]
      exact exp_identity hv (hn ▸ hn₀)
    rw [hre, him, h₁, h₂]
    linear_combination (2 * π * N) * h₃
  rw [jacobiNorm, jacobiNorm]
  dsimp only
  rw [hφ.2.1 γ (τ, z), jacobiFactor, norm_mul, norm_mul, norm_zpow, Complex.norm_exp]
  dsimp only
  rw [mul_assoc, mul_assoc, mul_left_comm (rexp _), ← Real.exp_add, hexp]

private lemma rexp_mul_rexp_le {n r v y M δ : ℝ} (hM : 0 < M) (h : 4 * M * δ + r ^ 2 ≤ 4 * n * M)
    (hv : 1 / 2 ≤ v) (hy : |y| ≤ v / 2) : rexp (-(2 * π * (n * v + r * y))) *
    rexp (-(2 * π * M * y ^ 2 / v)) ≤ (rexp (-(π * (n + r / 2))) + rexp (-(π * (n - r / 2)))) *
      rexp (-(2 * π * ((v - 1 / 2) * δ))) := by
  have hv₀ : 0 < v := by linarith
  have hα : |y / v| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hv₀, div_le_iff₀ hv₀]
    linarith
  have hyv : y = y / v * v := (div_mul_cancel₀ y hv₀.ne').symm
  generalize y / v = α at hα hyv
  subst hyv
  have hQ : δ ≤ n + r * α + M * α ^ 2 := by
    have h₁ : 4 * M * (n + r * α + M * α ^ 2 - δ) = 4 * n * M - (r ^ 2 + 4 * M * δ) +
        (r + 2 * M * α) ^ 2 := by
      ring1
    have h₂ : 0 ≤ 4 * M * (n + r * α + M * α ^ 2 - δ) := by
      rw [h₁]
      nlinarith [sq_nonneg (r + 2 * M * α)]
    nlinarith [nonneg_of_mul_nonneg_right h₂ (by positivity : 0 < 4 * M)]
  have hmain : π * (n + r * α) + 2 * π * ((v - 1 / 2) * δ) ≤
      2 * π * (n * v + r * (α * v)) + 2 * π * M * (α * v) ^ 2 / v := by
    have he : 2 * π * M * (α * v) ^ 2 / v = 2 * π * (M * α ^ 2 * v) := by
      field_simp
    rw [he]
    have h₁ : (v - 1 / 2) * δ ≤ (v - 1 / 2) * (n + r * α + M * α ^ 2) :=
      mul_le_mul_of_nonneg_left hQ (by linarith)
    have h₂ : 0 ≤ M * α ^ 2 := by positivity
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left h₁ (by positivity : (0 : ℝ) ≤ 2 * π),
      mul_nonneg Real.pi_pos.le h₂]
  have hα' : -(1 / 2) ≤ α ∧ α ≤ 1 / 2 := abs_le.mp hα
  rw [← Real.exp_add, add_mul, ← Real.exp_add, ← Real.exp_add]
  rcases le_total 0 r with hr | hr
  · refine (Real.exp_le_exp.mpr ?_).trans (le_add_of_nonneg_left (Real.exp_nonneg _))
    nlinarith [Real.pi_pos, mul_nonneg hr (by linarith [hα'.1] : 0 ≤ α + 1 / 2)]
  · refine (Real.exp_le_exp.mpr ?_).trans (le_add_of_nonneg_right (Real.exp_nonneg _))
    nlinarith [Real.pi_pos, mul_nonneg (neg_nonneg.mpr hr) (by linarith [hα'.2] : 0 ≤ 1 / 2 - α)]

variable {τ z}

private lemma jacobiNorm_le_mul_rexp (hN : 0 < N) (hφ : φ ∈ jacobiFormSpace k N) {δ : ℝ}
    (hs : ∀ p : ℤ × ℤ, jacobiCoeff φ p ≠ 0 → 4 * (N : ℝ) * δ + (p.2 : ℝ) ^ 2 ≤ 4 * p.1 * N)
    (hτ : 1 / 2 ≤ τ.im) (hz : |z.im| ≤ τ.im / 2) :
    jacobiNorm N φ (τ, z) ≤ jacobiSupBound φ * rexp (-(2 * π * ((τ.im - 1 / 2) * δ))) := by
  have hc : HasJacobiFourierExpansion φ (jacobiCoeff φ) :=
    hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ
  have hb : Summable fun p ↦ ‖jacobiCoeff φ p * jacobiFourierExp p (τ, z)‖ :=
    summable_norm_iff.mpr (hc (τ, z)).summable
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [jacobiNorm, ← (hc (τ, z)).tsum_eq]
  dsimp only
  refine (mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hb) (Real.exp_nonneg _)).trans ?_
  rw [← tsum_mul_right, jacobiSupBound, ← tsum_mul_right]
  refine (hb.mul_right _).tsum_le_tsum (fun p ↦ ?_) ((summable_jacobiSupBound hφ).mul_right _)
  rw [norm_mul, norm_jacobiFourierExp, mul_assoc ‖jacobiCoeff φ p‖, mul_assoc ‖jacobiCoeff φ p‖]
  by_cases hp : jacobiCoeff φ p = 0
  · simp [hp]
  · exact mul_le_mul_of_nonneg_left (rexp_mul_rexp_le hN' (hs p hp) hτ hz) (norm_nonneg _)

/-- **The bound on the region `v ≥ 1/2`, `|y| ≤ v/2`**, which meets every orbit of the Jacobi group:
for `φ ∈ J_{k,N}`, `N ≥ 1`,
`|φ(τ, z)| e^{-2πN y²/v} ≤ ∑ |c(n, r)| (e^{-π(n + r/2)} + e^{-π(n - r/2)})` there, since the term of
`(n, r)` is `|c(n, r)| e^{-2πv(n + rα + Nα²)}`, `α = y/v`, with `n + rα + Nα² ≥ 0` on the support
and `n + rα ≥ n - |r|/2`. -/
lemma jacobiNorm_le_jacobiSupBound (hN : 0 < N) (hφ : φ ∈ jacobiFormSpace k N) (hτ : 1 / 2 ≤ τ.im)
    (hz : |z.im| ≤ τ.im / 2) : jacobiNorm N φ (τ, z) ≤ jacobiSupBound φ := by
  have h : jacobiNorm N φ (τ, z) ≤ jacobiSupBound φ * rexp (-(2 * π * ((τ.im - 1 / 2) * 0))) :=
    jacobiNorm_le_mul_rexp hN hφ (fun p hp ↦ ?_) hτ hz
  · simpa using h
  · have hS : 0 ≤ p.1 ∧ p.2 ^ 2 ≤ 4 * p.1 * (N : ℤ) := by
      by_contra h
      exact hp <| jacobiCoeff_eq_zero_of_mem_jacobiFourierSupported hφ.2.2 h
    have h' : (p.2 : ℝ) ^ 2 ≤ 4 * p.1 * N := by
      exact_mod_cast hS.2
    simpa using h'

private lemma rexp_le_add_rexp {n r y v : ℝ} (hn : |r| ≤ 2 * n) (hy : 1 / 2 ≤ y)
    (hv : |v| ≤ y / 2) :
    rexp (-(2 * π * (n * y + r * v))) ≤ rexp (-(π * (n + r / 2))) + rexp (-(π * (n - r / 2))) := by
  rcases le_total 0 r with hr | hr
  · refine (Real.exp_le_exp.mpr ?_).trans (le_add_of_nonneg_left (Real.exp_pos _).le)
    rw [abs_of_nonneg hr] at hn
    nlinarith [Real.pi_pos, abs_le.mp hv, mul_nonneg (by linarith : 0 ≤ y - 1 / 2)
      (by linarith : 0 ≤ n - r / 2), mul_nonneg hr (by linarith [(abs_le.mp hv).1] : 0 ≤ v + y / 2)]
  · refine (Real.exp_le_exp.mpr ?_).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
    rw [abs_of_nonpos hr] at hn
    nlinarith [Real.pi_pos, abs_le.mp hv, mul_nonneg (by linarith : 0 ≤ y - 1 / 2)
      (by linarith : 0 ≤ n + r / 2), mul_nonneg (neg_nonneg.mpr hr)
      (by linarith [(abs_le.mp hv).2] : 0 ≤ y / 2 - v)]

private lemma abs_le_two_mul {n r : ℤ} (hn : 0 ≤ n) (hr : r ^ 2 ≤ 4 * n) : |r| ≤ 2 * n := by
  by_contra h
  have h' : 2 * n + 1 ≤ |r| := by omega
  nlinarith [sq_abs r, abs_nonneg r]

lemma norm_le_jacobiSupBound (hφ : φ ∈ jacobiFormSpace k 1) (hτ : 1 / 2 ≤ τ.im)
    (hz : |z.im| ≤ τ.im / 2) : ‖φ (τ, z)‖ ≤ jacobiSupBound φ := by
  have hc : HasJacobiFourierExpansion φ (jacobiCoeff φ) :=
    hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ
  have hs : Summable fun p ↦ ‖jacobiCoeff φ p * jacobiFourierExp p (τ, z)‖ :=
    summable_norm_iff.mpr (hc (τ, z)).summable
  rw [← (hc (τ, z)).tsum_eq]
  refine (norm_tsum_le_tsum_norm hs).trans <| hs.tsum_le_tsum (fun p ↦ ?_) <|
    summable_jacobiSupBound hφ
  rw [norm_mul, norm_jacobiFourierExp]
  by_cases hp : jacobiCoeff φ p = 0
  · rw [hp, norm_zero, zero_mul, zero_mul]
  have hS : 0 ≤ p.1 ∧ p.2 ^ 2 ≤ 4 * p.1 * ((1 : ℕ) : ℤ) := by
    by_contra h
    exact hp <| jacobiCoeff_eq_zero_of_mem_jacobiFourierSupported hφ.2.2 h
  have hr : |(p.2 : ℝ)| ≤ 2 * p.1 := by
    exact_mod_cast abs_le_two_mul hS.1 (by simpa using hS.2)
  exact mul_le_mul_of_nonneg_left (rexp_le_add_rexp hr hτ hz) (norm_nonneg _)

variable (τ) in
private lemma exists_abs_im_add_mul_le (w : ℂ) : ∃ a : ℤ, |(w + a * τ).im| ≤ τ.im / 2 := by
  refine ⟨-round (w.im / τ.im), ?_⟩
  have h₁ : |w.im / τ.im - round (w.im / τ.im)| ≤ 1 / 2 := abs_sub_round _
  have h₂ : (w + ((-round (w.im / τ.im) : ℤ) : ℂ) * τ).im =
      (w.im / τ.im - round (w.im / τ.im)) * τ.im := by
    have hv : τ.im ≠ 0 := τ.im_pos.ne'
    simp
    field_simp
    ring1
  rw [h₂, abs_mul, abs_of_pos τ.im_pos]
  nlinarith [τ.im_pos]

variable (τ z) {γ}

private lemma jacobiNorm_mul_norm_denom_zpow_le_mul (hN : 0 < N) (hφ : φ ∈ jacobiFormSpace k N)
    {δ : ℝ} (hs : ∀ p : ℤ × ℤ, jacobiCoeff φ p ≠ 0 → 4 * (N : ℝ) * δ + (p.2 : ℝ) ^ 2 ≤ 4 * p.1 * N)
    (hγ : 1 / 2 ≤ (γ • τ).im) : jacobiNorm N φ (τ, z) * ‖denom γ τ‖ ^ k ≤ jacobiSupBound φ *
    rexp (-(2 * π * (((γ • τ).im - 1 / 2) * δ))) := by
  rcases exists_abs_im_add_mul_le (γ • τ) (z / denom γ τ) with ⟨a, ha⟩
  rw [mul_comm, ← jacobiNorm_smul τ z γ hφ, ← jacobiNorm_add_mul (γ • τ) _ a hφ]
  exact jacobiNorm_le_mul_rexp hN hφ hs hγ ha

/-- **The bound under `SL(2, ℤ)`**: for `φ ∈ J_{k,N}`, `N ≥ 1`, and `γ = (a, b; c, d)` with
`Im γτ ≥ 1/2`,
`|φ(τ, z)| e^{-2πN y²/v} |cτ + d|^k ≤ ∑ |c(n, r)| (e^{-π(n + r/2)} + e^{-π(n - r/2)})`. -/
lemma jacobiNorm_mul_norm_denom_zpow_le (hN : 0 < N) (hφ : φ ∈ jacobiFormSpace k N)
    (hγ : 1 / 2 ≤ (γ • τ).im) : jacobiNorm N φ (τ, z) * ‖denom γ τ‖ ^ k ≤ jacobiSupBound φ := by
  rcases exists_abs_im_add_mul_le (γ • τ) (z / denom γ τ) with ⟨a, ha⟩
  rw [mul_comm, ← jacobiNorm_smul τ z γ hφ, ← jacobiNorm_add_mul (γ • τ) _ a hφ]
  exact jacobiNorm_le_jacobiSupBound hN hφ hγ ha

variable (u : ℝ)

private lemma jacobiNorm_ofReal : jacobiNorm N φ (τ, (u : ℂ)) = ‖φ (τ, u)‖ := by
  simp [jacobiNorm]

private lemma norm_le_jacobiSupBound_of_nonpos (hN : 0 < N) (hφ : φ ∈ jacobiFormSpace k N)
    (hk : k ≤ 0) : ‖φ (τ, u)‖ ≤ jacobiSupBound φ := by
  rcases ModularGroup.exists_one_half_le_im_smul_and_norm_denom_le τ with ⟨γ, hγ, hd⟩
  rw [← jacobiNorm_ofReal]
  exact (le_mul_of_one_le_right (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))
    (one_le_zpow_of_nonpos₀ (norm_pos_iff.mpr (denom_ne_zero γ τ)) hd hk)).trans
      (jacobiNorm_mul_norm_denom_zpow_le τ u hN hφ hγ)

variable {τ} (γ) in
private lemma im_le_norm_denom (hτ : τ.im ≤ 1) : τ.im ≤ ‖denom γ τ‖ := by
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · have hdet : γ 1 1 * γ 0 0 = 1 := by
      have h : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.det_coe
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero, mul_comm] at h
      exact h
    rw [ModularGroup.denom_apply, hc]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with hd | hd <;> simpa [hd] using hτ
  · have h1 : (1 : ℝ) ≤ |(γ 1 0 : ℝ)| := by exact_mod_cast Int.one_le_abs hc
    refine le_trans ?_ (abs_im_le_norm _)
    rw [ModularGroup.denom_apply]
    simp [abs_of_pos τ.im_pos]
    nlinarith [τ.im_pos]

private lemma norm_mul_im_pow_le (hN : 0 < N) (hφ : φ ∈ jacobiFormSpace k N) (hτ : τ.im ≤ 1) :
    ‖φ (τ, u)‖ * τ.im ^ k.toNat ≤ jacobiSupBound φ := by
  rcases le_or_gt 0 k with hk | hk
  · rcases ModularGroup.exists_one_half_le_im_smul_and_norm_denom_le τ with ⟨γ, hγ, -⟩
    have h : jacobiNorm N φ (τ, (u : ℂ)) * ‖denom γ τ‖ ^ k ≤ jacobiSupBound φ :=
      jacobiNorm_mul_norm_denom_zpow_le τ u hN hφ hγ
    rw [jacobiNorm_ofReal] at h
    refine (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)).trans h
    rw [← Int.toNat_of_nonneg hk, zpow_natCast, Int.toNat_natCast]
    exact pow_le_pow_left₀ τ.im_pos.le (im_le_norm_denom γ hτ) _
  · rw [Int.toNat_of_nonpos hk.le, pow_zero, mul_one]
    exact norm_le_jacobiSupBound_of_nonpos τ u hN hφ hk.le

variable {y B : ℝ} {c : ℤ × ℤ → ℂ} (v : Fin 2 → ℝ)

/-- The point `(v₀ + yi, v₁)` of `ℍ × ℂ`, for real `v₀, v₁` and `y > 0`. -/
private noncomputable def heightPoint (hy : 0 < y) : ℍ × ℂ :=
  (mk (v 0 + y * I) (by simpa using hy), (v 1 : ℂ))

private lemma jacobiFourierExp_heightPoint (hy : 0 < y) (p : Fin 2 → ℤ) :
    jacobiFourierExp (p 0, p 1) (heightPoint v hy) =
      cexp (-2 * π * p 0 * y) * mFourier p fun i ↦ (v i : UnitAddCircle) := by
  simp only [jacobiFourierExp, heightPoint, mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, Fin.prod_univ_two, ← Complex.exp_add]
  congr 1
  linear_combination (2 * π * p 0 * y : ℂ) * I_sq

private lemma hasSum_heightPoint (hc : HasJacobiFourierExpansion φ c) (hy : 0 < y) : HasSum
    (fun p : Fin 2 → ℤ ↦ c (p 0, p 1) * cexp (-2 * π * p 0 * y) * mFourier p fun i ↦
      (v i : UnitAddCircle)) (φ (heightPoint v hy)) :=
  ((finTwoArrowEquiv ℤ).hasSum_iff.mpr (hc (heightPoint v hy))).congr_fun fun p ↦ by
    rw [mul_assoc, ← jacobiFourierExp_heightPoint]
    rfl

private lemma summable_heightCoeff (hc : HasJacobiFourierExpansion φ c) (hy : 0 < y) :
    Summable fun p : Fin 2 → ℤ ↦ c (p 0, p 1) * cexp (-2 * π * p 0 * y) :=
  (hasSum_heightPoint 0 hc hy).summable.congr fun p ↦ by
    simp [mFourier]

private lemma norm_tsum_heightCoeff_le (hc : HasJacobiFourierExpansion φ c) (hy : 0 < y)
    (hB : ∀ (τ : ℍ) (u : ℝ), τ.im = y → ‖φ (τ, u)‖ ≤ B) (x : UnitAddTorus (Fin 2)) :
    ‖∑' p, c (p 0, p 1) * cexp (-2 * π * p 0 * y) * mFourier p x‖ ≤ B := by
  choose v hv using fun i ↦ QuotientAddGroup.mk_surjective (x i)
  rw [← (funext hv : (fun i ↦ (v i : UnitAddCircle)) = x), (hasSum_heightPoint v hc hy).tsum_eq]
  exact hB _ _ (by simp)

variable (n r : ℤ)

private lemma norm_mul_rexp_le_of_hasJacobiFourierExpansion (hc : HasJacobiFourierExpansion φ c)
    (hy : 0 < y) (hB : ∀ (τ : ℍ) (u : ℝ), τ.im = y → ‖φ (τ, u)‖ ≤ B) :
    ‖c (n, r)‖ * rexp (-(2 * π * n * y)) ≤ B := by
  have h : ‖c (![n, r] 0, ![n, r] 1) * cexp (-2 * π * (![n, r] 0 : ℤ) * y)‖ ≤ B :=
    norm_le_of_norm_tsum_mFourier_le ![n, r] (summable_heightCoeff hc hy)
      (norm_tsum_heightCoeff_le hc hy hB)
  simpa [Complex.norm_exp] using h

/-- **The Fourier coefficients of a Jacobi form grow polynomially** (Hecke's bound): for
`φ ∈ J_{k,N}`, `N ≥ 1`, `|c(n, r)| ≤ C e^{2π} (1 + |n|)^k` if `k ≥ 0`, and `|c(n, r)| ≤ C e^{2π}` if
`k < 0`, where `C = jacobiSupBound φ`. The coefficient `c(n, r) e^{-2πny}` is bounded by the
supremum of `|φ(x + iy, u)|` over real `x, u`, which is at most `C y^{-k}` for `y ≤ 1`; take
`y = 1/(1 + |n|)`. -/
lemma norm_jacobiCoeff_le_of_mem_jacobiFormSpace (hN : 0 < N) (hφ : φ ∈ jacobiFormSpace k N) :
    ‖jacobiCoeff φ (n, r)‖ ≤ jacobiSupBound φ * rexp (2 * π) * (1 + |(n : ℝ)|) ^ k.toNat := by
  have hc : HasJacobiFourierExpansion φ (jacobiCoeff φ) :=
    hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ
  have hn₀ : 0 < 1 + |(n : ℝ)| := by positivity
  have hy1 : (1 + |(n : ℝ)|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [abs_nonneg (n : ℝ)])
  have hB (τ : ℍ) (u : ℝ) (hτ : τ.im = (1 + |(n : ℝ)|)⁻¹) :
      ‖φ (τ, u)‖ ≤ jacobiSupBound φ * (1 + |(n : ℝ)|) ^ k.toNat := by
    have h : ‖φ (τ, u)‖ * τ.im ^ k.toNat ≤ jacobiSupBound φ :=
      norm_mul_im_pow_le τ u hN hφ (hτ ▸ hy1)
    rwa [hτ, inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)] at h
  have h : ‖jacobiCoeff φ (n, r)‖ * rexp (-(2 * π * n * (1 + |(n : ℝ)|)⁻¹)) ≤
      jacobiSupBound φ * (1 + |(n : ℝ)|) ^ k.toNat :=
    norm_mul_rexp_le_of_hasJacobiFourierExpansion n r hc (inv_pos.mpr hn₀) hB
  have hS : 0 ≤ jacobiSupBound φ := jacobiSupBound_nonneg
  have he : rexp (2 * π * n * (1 + |(n : ℝ)|)⁻¹) ≤ rexp (2 * π) := by
    have h1 : (n : ℝ) * (1 + |(n : ℝ)|)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hn₀]
      linarith [le_abs_self (n : ℝ)]
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos]
  have h' : ‖jacobiCoeff φ (n, r)‖ * rexp (-(2 * π * n * (1 + |(n : ℝ)|)⁻¹)) *
      rexp (2 * π * n * (1 + |(n : ℝ)|)⁻¹) ≤ jacobiSupBound φ * (1 + |(n : ℝ)|) ^ k.toNat *
        rexp (2 * π * n * (1 + |(n : ℝ)|)⁻¹) :=
    mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
  rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h'
  nlinarith [mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ jacobiSupBound φ *
    (1 + |(n : ℝ)|) ^ k.toNat)]

private lemma natCast_mul_le_jacobiSupBound_sq (hN : 0 < N) (hφ : φ ∈ jacobiFormSpace k N)
    (hk : k ≤ 0) {K : ℕ} (hK : 1 ≤ K) :
    K * (‖jacobiCoeff φ (n, r)‖ ^ 2 * rexp (-(2 * π)) ^ 2) ≤ jacobiSupBound φ ^ 2 := by
  have hc₀ : HasJacobiFourierExpansion φ (jacobiCoeff φ) :=
    hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ
  have hM : 0 < ((|n| + |r| + N + 1 : ℤ) : ℝ) * K ^ 2 := by
    positivity
  have hy : 0 < (((|n| + |r| + N + 1 : ℤ) : ℝ) * K ^ 2)⁻¹ := inv_pos.mpr hM
  have hN₀ : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hinj : Function.Injective fun l : ℕ ↦ ![n + l * r + N * l ^ 2, r + 2 * N * l] :=
      fun l l' h ↦ by
    have h₁ : r + 2 * (N : ℤ) * l = r + 2 * N * l' := by simpa using congrFun h 1
    have h₂ : (N : ℤ) * l = N * l' := by linarith
    exact_mod_cast mul_left_cancel₀ hN₀ h₂
  have h : ∑ p ∈ (Finset.range K).image (fun l : ℕ ↦ ![n + l * r + N * l ^ 2, r + 2 * N * l]),
      ‖jacobiCoeff φ (p 0, p 1) *
        cexp (-2 * π * p 0 * (((|n| + |r| + N + 1 : ℤ) : ℝ) * K ^ 2)⁻¹)‖ ^ 2 ≤
          jacobiSupBound φ ^ 2 :=
    sum_norm_sq_le_of_norm_tsum_mFourier_le (summable_heightCoeff hc₀ hy)
      (norm_tsum_heightCoeff_le hc₀ hy fun τ u _ ↦ norm_le_jacobiSupBound_of_nonpos τ u hN hφ hk) _
  have hK' : (K : ℝ) * (‖jacobiCoeff φ (n, r)‖ ^ 2 * rexp (-(2 * π)) ^ 2) =
      ((Finset.range K).image fun l : ℕ ↦ ![n + l * r + N * l ^ 2, r + 2 * N * l]).card •
        (‖jacobiCoeff φ (n, r)‖ ^ 2 * rexp (-(2 * π)) ^ 2) := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range, nsmul_eq_mul]
  rw [hK']
  refine (Finset.card_nsmul_le_sum _ _ _ fun p hp ↦ ?_).trans h
  rcases Finset.mem_image.mp hp with ⟨l, hl, rfl⟩
  have hl : (l : ℝ) ≤ K := by
    exact_mod_cast (Finset.mem_range.mp hl).le
  have hc : jacobiCoeff φ (n + l * r + N * l ^ 2, r + 2 * N * l) = jacobiCoeff φ (n, r) := by
    simpa using jacobiCoeff_add_of_mem_jacobiFormSpace l n r hφ
  have hnl : ((n + l * r + N * l ^ 2 : ℤ) : ℝ) * (((|n| + |r| + N + 1 : ℤ) : ℝ) * K ^ 2)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hM]
    push_cast
    have h1 : (1 : ℝ) ≤ K := by
      exact_mod_cast hK
    have hK2 : (K : ℝ) ≤ K ^ 2 := by
      nlinarith
    have hlr : (l : ℝ) * r ≤ |(r : ℝ)| * K ^ 2 :=
      (mul_le_mul_of_nonneg_left (le_abs_self (r : ℝ)) (Nat.cast_nonneg l)).trans <| by
        nlinarith [abs_nonneg (r : ℝ)]
    have hll : (l : ℝ) ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg l) hl 2
    have hK3 : (1 : ℝ) ≤ K ^ 2 := by
      nlinarith
    nlinarith [le_abs_self (n : ℝ), abs_nonneg (n : ℝ), abs_nonneg (r : ℝ),
      mul_le_mul_of_nonneg_left hll (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hc, norm_mul, Complex.norm_exp, mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_nonneg _) ?_ 2) (by positivity)
  generalize (((|n| + |r| + N + 1 : ℤ) : ℝ) * K ^ 2)⁻¹ = y at hnl ⊢
  generalize n + l * r + N * l ^ 2 = a at hnl ⊢
  rw [Real.exp_le_exp]
  simp
  nlinarith [mul_le_mul_of_nonneg_left hnl Real.pi_pos.le]

/-- **There are no nonzero Jacobi forms of weight `k ≤ 0` and index `N ≥ 1`**: for `k ≤ 0` the
transformation laws give `|φ(τ, u)| ≤ C` for all `τ` and real `u`, so by Bessel's inequality on
the torus at height `y`, `∑ |c(n_λ, r_λ)|² e^{-4πn_λ y} ≤ C²` over the `K` pairs
`(n_λ, r_λ) = (n + λr + Nλ², r + 2Nλ)`, `0 ≤ λ < K`, which carry the coefficient `c(n, r)`; with
`y = 1/((|n| + |r| + N + 1) K²)` this gives `K |c(n, r)|² e^{-4π} ≤ C²` for every `K ≥ 1`. -/
lemma eq_zero_of_mem_jacobiFormSpace_of_nonpos (hN : 0 < N) (hφ : φ ∈ jacobiFormSpace k N)
    (hk : k ≤ 0) : φ = 0 := by
  refine eq_zero_of_jacobiCoeff_eq_zero hφ <| funext fun p ↦ ?_
  rcases p with ⟨n, r⟩
  rw [Pi.zero_apply, ← norm_eq_zero]
  by_contra hne
  have ha : 0 < ‖jacobiCoeff φ (n, r)‖ ^ 2 * rexp (-(2 * π)) ^ 2 := by
    have h0 : 0 < ‖jacobiCoeff φ (n, r)‖ := (norm_nonneg _).lt_of_ne' hne
    positivity
  rcases exists_nat_gt (jacobiSupBound φ ^ 2 /
    (‖jacobiCoeff φ (n, r)‖ ^ 2 * rexp (-(2 * π)) ^ 2)) with ⟨K, hK⟩
  have hK1 : 1 ≤ K := by
    have h0 : (0 : ℝ) < K := lt_of_le_of_lt (by positivity) hK
    exact_mod_cast h0
  rw [div_lt_iff₀ ha] at hK
  linarith [natCast_mul_le_jacobiSupBound_sq n r hN hφ hk hK1]

lemma one_add_pow_le_mul_rexp (K : ℕ) {ε x : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) :
    (1 + x) ^ K ≤ K.factorial / ε ^ K * rexp (ε * (1 + x)) := by
  have h : (ε * (1 + x)) ^ K / K.factorial ≤ rexp (ε * (1 + x)) :=
    Real.pow_div_factorial_le_exp _ (by positivity) K
  rw [div_le_iff₀ (by positivity), mul_pow] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

/-- **A Jacobi cusp form is bounded in the invariant norm**: for `φ ∈ J_{k,N}^cusp`, `N ≥ 1`, the
function `|φ(τ, z)| v^{k/2} e^{-2πN y²/v}` is bounded on `ℍ × ℂ` (Eichler and Zagier, §1). It is
invariant under the Jacobi group, and on the region `v ≥ 1/2`, `|y| ≤ v/2`, it is at most
`C v^{k/2} e^{-π(v - 1/2)/(2N)}`, since `n + rα + Nα² ≥ (4nN - r²)/(4N) ≥ 1/(4N)` on the support of
the Fourier expansion. -/
lemma exists_jacobiNorm_mul_sqrt_zpow_le (hN : 0 < N) (hφ : φ ∈ jacobiCuspFormSpace k N) :
    ∃ C, ∀ (τ : ℍ) (z : ℂ), jacobiNorm N φ (τ, z) * √τ.im ^ k ≤ C := by
  rcases le_or_gt k 0 with hk | hk
  · refine ⟨0, fun τ z ↦ ?_⟩
    rw [jacobiNorm, eq_zero_of_mem_jacobiFormSpace_of_nonpos hN hφ.1 hk]
    simp
  lift k to ℕ using hk.le
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hε : 0 < π / (2 * N) := by positivity
  have hs (p : ℤ × ℤ) (hp : jacobiCoeff φ p ≠ 0) :
      4 * (N : ℝ) * (1 / (4 * N)) + (p.2 : ℝ) ^ 2 ≤ 4 * p.1 * N := by
    have hS : p.2 ^ 2 < 4 * p.1 * (N : ℤ) := by
      by_contra h
      exact hp <| jacobiCoeff_eq_zero_of_mem_jacobiFourierSupported hφ.2 h
    have h' : (p.2 : ℝ) ^ 2 + 1 ≤ 4 * p.1 * N := by
      exact_mod_cast (Int.add_one_le_iff.mpr hS)
    have h₁ : 4 * (N : ℝ) * (1 / (4 * N)) = 1 := by
      field_simp
    linarith
  refine ⟨jacobiSupBound φ * (k.factorial / (π / (2 * N)) ^ k * rexp (3 * (π / (2 * N)) / 2)),
    fun τ z ↦ ?_⟩
  rcases ModularGroup.exists_one_half_le_im_smul_and_norm_denom_le τ with ⟨γ, hγ, -⟩
  have h : jacobiNorm N φ (τ, z) * ‖denom γ τ‖ ^ k ≤
      jacobiSupBound φ * rexp (-(2 * π * (((γ • τ).im - 1 / 2) * (1 / (4 * N))))) :=
    jacobiNorm_mul_norm_denom_zpow_le_mul τ z hN hφ.1 hs hγ
  have hJ : 0 < ‖denom γ τ‖ := norm_pos_iff.mpr (denom_ne_zero γ τ)
  have hv' : 0 < (γ • τ).im := (γ • τ).im_pos
  have hsqrt : √τ.im = √(γ • τ).im * ‖denom γ τ‖ := by
    have him : τ.im = (γ • τ).im * ‖denom γ τ‖ ^ 2 := by
      rw [ModularGroup.im_smul_eq_div_normSq, normSq_eq_norm_sq]
      field_simp
    rw [him, Real.sqrt_mul hv'.le, Real.sqrt_sq hJ.le]
  have hbound : rexp (-(2 * π * (((γ • τ).im - 1 / 2) * (1 / (4 * N))))) * √(γ • τ).im ^ k ≤
      k.factorial / (π / (2 * N)) ^ k * rexp (3 * (π / (2 * N)) / 2) := by
    have h₁ : √(γ • τ).im ^ k ≤ (1 + (γ • τ).im) ^ k :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (by
        nlinarith [Real.sq_sqrt hv'.le, Real.sqrt_nonneg (γ • τ).im, sq_nonneg (√(γ • τ).im - 1)]) k
    have h₂ : (1 + (γ • τ).im) ^ k ≤
        k.factorial / (π / (2 * N)) ^ k * rexp (π / (2 * N) * (1 + (γ • τ).im)) :=
      one_add_pow_le_mul_rexp k hε hv'.le
    have h₃ : rexp (-(2 * π * (((γ • τ).im - 1 / 2) * (1 / (4 * N))))) *
        rexp (π / (2 * N) * (1 + (γ • τ).im)) = rexp (3 * (π / (2 * N)) / 2) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring1
    refine (mul_le_mul_of_nonneg_left (h₁.trans h₂) (Real.exp_nonneg _)).trans (le_of_eq ?_)
    rw [mul_left_comm, h₃]
  have he : jacobiNorm N φ (τ, z) * √τ.im ^ (k : ℤ) =
      jacobiNorm N φ (τ, z) * ‖denom γ τ‖ ^ (k : ℤ) * √(γ • τ).im ^ k := by
    rw [zpow_natCast, zpow_natCast, hsqrt, mul_pow]
    ring1
  rw [he]
  refine (mul_le_mul_of_nonneg_right h (pow_nonneg (Real.sqrt_nonneg _) k)).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hbound jacobiSupBound_nonneg

end ModularForm
