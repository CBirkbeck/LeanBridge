import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.RadialGreenKernel

/-!
# The pairing of two Maass forms through a point-pair invariant

For `F` in `M(N, χ, a)` and `G` in `M(N, χ, b)` (`UpperHalfPlane.maassSpace`), and a radial kernel
`φ`, write `B(φ; F, G) = ∫_{Γ₀(N) \ ℍ} ∫_ℍ φ(cosh d(z, w)) F(w) conj(G(z)) dμ(w) dμ(z)`
(`UpperHalfPlane.kernelPair`, in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.EigenvalueReal`). This file develops `B`
further, with no decay hypothesis on `F` and `G`. The kernels `P_n = coshDistNormalBump n`, of mass
`1` and shrinking to the point `c = 1`, give averages of `F` over small balls, and the kernel
`radialGreen n` compares `P_{2n + 1}` and `P_n` by Green's identity on `ℍ`, in the place of
Selberg's theorem on the eigenvalue of an integral operator:
`(n + 1) bumpMass n (B(P_{2n + 1}) - B(P_n)) = -a B(radialGreen n)`, where `radialGreen n` has small
mass. Summing along the chain `n ↦ 2n + 1`, and using Fatou's lemma when `n` goes to infinity, this
gives for `F ≠ 0` with real eigenvalue `l` and `E = ‖F‖²`
`E ≤ Re B(P_{2m + 1}; F, F) + 2 |l| E / (m + 1)`, so that the average of `F` over a small enough
ball has a norm at least half of that of `F`, the size of the ball depending only on `|l|`. Hence:

* every eigenvalue of `M(N, χ, λ)` is nonnegative, the averages `Re B(P_n; F, F)` being at most `E`,
  and being larger for larger balls if `λ < 0`;
* eigenforms of different eigenvalues are orthogonal: for `a ≠ conj b`, the pairing `B(φ; F, G)`
  vanishes for every `φ`, and Fatou's lemma gives `‖F + ω G‖² ≤ ‖F‖² + ‖G‖²` for `|ω| = 1`.

## Main definitions

* `UpperHalfPlane.doubleChain`: the chain `m, 2m + 1, 4m + 3, …`.

## Main results

* `UpperHalfPlane.le_re_kernelPair_add`: `E ≤ Re B(P_{2m + 1}; F, F) + 2 |l| E / (m + 1)`.
* `UpperHalfPlane.zero_le_of_mem_maassSpace`: the eigenvalue of a nonzero element of `M(N, χ, l)` is
  nonnegative.
* `UpperHalfPlane.maassPetersson_eq_zero_of_ne`: Maass forms with different eigenvalues are
  orthogonal.
-/

open Filter MeasureTheory

open scoped ComplexConjugate

namespace UpperHalfPlane

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {a b : ℂ} {φ k : ℝ → ℝ} {F G : ℍ → ℂ} {C l : ℝ}
  (n : ℕ)

lemma kernelPair_radialLaplacian_radialGreen (hF : F ∈ maassSpace N χ a)
    (hG : G ∈ maassSpace N χ b) : kernelPair N (radialLaplacian (radialGreen n)) F G =
      (((n + 1) * bumpMass n : ℝ) : ℂ) * (kernelPair N (coshDistNormalBump (2 * n + 1)) F G -
        kernelPair N (coshDistNormalBump n) F G) := by
  have hP (m : ℕ) : Integrable (fun p : ℍ × ℍ ↦
      (coshDistNormalBump m (dist p.1 p.2).cosh : ℂ) * (F p.2 * conj (G p.1)))
        (gammaZeroPairMeasure N) :=
    integrable_kernel_mul hF hG contDiff_coshDistNormalBump.continuous
      fun _ hc ↦ coshDistNormalBump_eq_zero hc
  rw [kernelPair, kernelPair, kernelPair, ← integral_sub (hP _) (hP _), ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun p ↦ ?_)
  dsimp only
  rw [radialLaplacian_radialGreen_eq_mul n (by linarith [(dist p.1 p.2).one_le_cosh])]
  push_cast
  ring1

lemma re_kernelPair_sub (hF : F ∈ maassSpace N χ (l : ℂ)) :
    (kernelPair N (coshDistNormalBump (2 * n + 1)) F F).re -
      (kernelPair N (coshDistNormalBump n) F F).re =
        -(l / ((n + 1) * bumpMass n)) * (kernelPair N (radialGreen n) F F).re := by
  have h1 : kernelPair N (radialLaplacian (radialGreen n)) F F =
      -(l : ℂ) * kernelPair N (radialGreen n) F F :=
    kernelPair_radialLaplacian hF hF (contDiff_radialGreen n)
      fun _ hc ↦ radialGreen_eq_zero_of_three_le n hc
  rw [kernelPair_radialLaplacian_radialGreen n hF hF, ← Complex.ofReal_neg] at h1
  have h2 : ((n + 1) * bumpMass n) * ((kernelPair N (coshDistNormalBump (2 * n + 1)) F F).re -
      (kernelPair N (coshDistNormalBump n) F F).re) =
        -l * (kernelPair N (radialGreen n) F F).re := by
    simpa only [Complex.re_ofReal_mul, Complex.sub_re] using congrArg Complex.re h1
  have h3 : ((n : ℝ) + 1) * bumpMass n ≠ 0 :=
    mul_ne_zero (by positivity) (bumpMass_pos n).ne'
  have hm : bumpMass n ≠ 0 := (bumpMass_pos n).ne'
  refine mul_left_cancel₀ h3 ?_
  rw [h2]
  field_simp

lemma norm_kernelPair_le (hF : F ∈ maassSpace N χ a) (hk : Continuous k)
    (hk0 : ∀ c, C ≤ c → k c = 0) (hφk : ∀ c, 1 ≤ c → |φ c| ≤ k c) :
    ‖kernelPair N φ F F‖ ≤ (∫ w, k (dist I w).cosh) * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := by
  have h1 :
      Integrable (fun p : ℍ × ℍ ↦ k (dist p.1 p.2).cosh * ‖F p.1‖ ^ 2) (gammaZeroPairMeasure N) :=
    integrable_kernel_mul_norm_sq_fst hF hk hk0
  have h2 :
      Integrable (fun p : ℍ × ℍ ↦ k (dist p.1 p.2).cosh * ‖F p.2‖ ^ 2) (gammaZeroPairMeasure N) :=
    integrable_kernel_mul_norm_sq_snd hF hk hk0
  have h3 : ∫ p : ℍ × ℍ, (k (dist p.1 p.2).cosh * ‖F p.1‖ ^ 2 +
      k (dist p.1 p.2).cosh * ‖F p.2‖ ^ 2) / 2 ∂gammaZeroPairMeasure N =
        (∫ w, k (dist I w).cosh) * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := by
    rw [integral_div, integral_add h1 h2, integral_kernel_mul_norm_sq_fst hF hk hk0,
      integral_kernel_mul_norm_sq_snd hF hk hk0]
    ring1
  rw [← h3]
  refine norm_integral_le_of_norm_le ((h1.add h2).div_const 2) (.of_forall fun p ↦ ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
  have h4 : |φ (dist p.1 p.2).cosh| ≤ k (dist p.1 p.2).cosh :=
    hφk _ (dist p.1 p.2).one_le_cosh
  have h5 : 2 * ‖F p.1‖ * ‖F p.2‖ ≤ ‖F p.1‖ ^ 2 + ‖F p.2‖ ^ 2 := two_mul_le_add_sq _ _
  have h6 : 0 ≤ ‖F p.2‖ * ‖F p.1‖ := by
    positivity
  have h7 :
      |φ (dist p.1 p.2).cosh| * (‖F p.2‖ * ‖F p.1‖) ≤ k (dist p.1 p.2).cosh * (‖F p.2‖ * ‖F p.1‖) :=
    mul_le_mul_of_nonneg_right h4 h6
  have h8 : k (dist p.1 p.2).cosh * (2 * ‖F p.1‖ * ‖F p.2‖) ≤
      k (dist p.1 p.2).cosh * (‖F p.1‖ ^ 2 + ‖F p.2‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h5 ((abs_nonneg _).trans h4)
  linarith

lemma abs_re_kernelPair_sub_le (hF : F ∈ maassSpace N χ (l : ℂ)) (m : ℕ) :
    |(kernelPair N (coshDistNormalBump (2 * (2 * m + 1) + 1)) F F).re -
      (kernelPair N (coshDistNormalBump (2 * m + 1)) F F).re| ≤
        |l| * (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) / (m + 1) := by
  have h0 : (0 : ℝ) < m + 1 := by
    positivity
  have hm : 0 < bumpMass m := bumpMass_pos m
  have hK : (((2 * m + 1 : ℕ) : ℝ) + 1) * bumpMass (2 * m + 1) = (m + 1) * bumpMass m := by
    rw [bumpMass_two_mul_add_one]
    push_cast
    ring1
  have hE : 0 ≤ ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := integral_nonneg fun z ↦ by positivity
  have hle : ‖kernelPair N (radialGreen (2 * m + 1)) F F‖ ≤
      bumpMass m * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 :=
    norm_kernelPair_le hF contDiff_coshDistBump.continuous (fun _ hc ↦ coshDistBump_eq_zero hc)
      fun c hc ↦ by
        rw [abs_of_nonpos (radialGreen_nonpos _ hc)]
        exact neg_radialGreen_le_coshDistBump m hc
  rw [re_kernelPair_sub _ hF, hK, abs_mul, abs_neg, abs_div, abs_of_pos (mul_pos h0 hm)]
  have h1 : |(kernelPair N (radialGreen (2 * m + 1)) F F).re| ≤
      bumpMass m * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := (Complex.abs_re_le_norm _).trans hle
  have h2 : |l| / ((m + 1) * bumpMass m) * |(kernelPair N (radialGreen (2 * m + 1)) F F).re| ≤
      |l| / ((m + 1) * bumpMass m) * (bumpMass m * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  refine h2.trans (le_of_eq ?_)
  field_simp

variable (m : ℕ) in
/-- The chain `m, 2m + 1, 4m + 3, …`, whose `J`-th term plus `1` is `2^J (m + 1)`
(`doubleChain_add_one`). The kernels `coshDistNormalBump (doubleChain m J)` shrink geometrically. -/
def doubleChain (J : ℕ) : ℕ :=
  (fun n ↦ 2 * n + 1)^[J] m

variable (m J : ℕ)

lemma doubleChain_succ : doubleChain m (J + 1) = 2 * doubleChain m J + 1 :=
  Function.iterate_succ_apply' _ _ _

lemma doubleChain_add_one : (doubleChain m J : ℝ) + 1 = 2 ^ J * (m + 1) := by
  induction J with
  | zero => simp [doubleChain]
  | succ J ih =>
    rw [doubleChain_succ]
    push_cast
    rw [pow_succ]
    linear_combination 2 * ih

lemma le_doubleChain : J ≤ doubleChain m J := by
  induction J with
  | zero => exact Nat.zero_le _
  | succ J ih =>
    rw [doubleChain_succ]
    omega

lemma self_le_doubleChain : m ≤ doubleChain m J := by
  induction J with
  | zero => exact le_rfl
  | succ J ih =>
    rw [doubleChain_succ]
    omega

lemma tendsto_doubleChain : Tendsto (doubleChain m) atTop atTop :=
  tendsto_atTop_mono (le_doubleChain m) tendsto_id

variable {m J}

lemma re_kernelPair_doubleChain_le (hF : F ∈ maassSpace N χ (l : ℂ)) :
    (kernelPair N (coshDistNormalBump (doubleChain m (J + 1))) F F).re ≤
      (kernelPair N (coshDistNormalBump (2 * m + 1)) F F).re +
        (2 - 2 / 2 ^ J) * (|l| * (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) / (m + 1)) := by
  induction J with
  | zero =>
    have h : doubleChain m (0 + 1) = 2 * m + 1 := rfl
    rw [h]
    norm_num
  | succ J ih =>
    have h1 : |(kernelPair N (coshDistNormalBump (2 * (2 * doubleChain m J + 1) + 1)) F F).re -
        (kernelPair N (coshDistNormalBump (2 * doubleChain m J + 1)) F F).re| ≤
          |l| * (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) / (doubleChain m J + 1) :=
      abs_re_kernelPair_sub_le hF (doubleChain m J)
    rw [← doubleChain_succ, ← doubleChain_succ, doubleChain_add_one] at h1
    have h2 : (kernelPair N (coshDistNormalBump (doubleChain m (J + 1 + 1))) F F).re -
        (kernelPair N (coshDistNormalBump (doubleChain m (J + 1))) F F).re ≤
          |l| * (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) / (2 ^ J * ((m : ℝ) + 1)) :=
      (abs_le.mp h1).2
    have h3 : |l| * (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) / (2 ^ J * ((m : ℝ) + 1)) =
        1 / 2 ^ J * (|l| * (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) / (m + 1)) := by
      field_simp
    rw [h3] at h2
    have h4 : (2 : ℝ) - 2 / 2 ^ (J + 1) = 2 - 2 / 2 ^ J + 1 / 2 ^ J := by
      field_simp
      ring1
    rw [h4, add_mul]
    linarith

variable (m) in
/-- **The average of a Maass form over a small ball is close to the form**: for `F` in
`M(N, χ, l)`, `l` real, and `E = ‖F‖² > 0`, `E ≤ Re B(P_{2m + 1}; F, F) + 2 |l| E / (m + 1)`, for
the kernel `P_n = coshDistNormalBump n`. The differences of the pairings with the consecutive
kernels of the chain `doubleChain m` are given by Green's identity, in terms of the kernels
`radialGreen` of small mass, and Fatou's lemma passes to the limit along the chain. -/
lemma le_re_kernelPair_add (hF : F ∈ maassSpace N χ (l : ℂ))
    (hE : 0 < ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) : ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 ≤
      (kernelPair N (coshDistNormalBump (2 * m + 1)) F F).re +
        2 * (|l| * (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) / (m + 1)) := by
  have hL : 0 ≤ |l| * (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) / (m + 1) := by
    positivity
  refine le_of_forall_re_kernelPair_le hF hE ((tendsto_doubleChain m).comp
    (tendsto_add_atTop_nat 1)) fun J ↦ re_kernelPair_doubleChain_le hF |>.trans ?_
  have h4 : (0 : ℝ) < 2 / 2 ^ J := by
    positivity
  nlinarith

lemma integral_kernel_mul_norm_sub_sq_eq (hF : F ∈ maassSpace N χ a) (hφ : Continuous φ)
    (hφ0 : ∀ c, C ≤ c → φ c = 0) : ∫ p : ℍ × ℍ, φ (dist p.1 p.2).cosh * ‖F p.1 - F p.2‖ ^ 2
      ∂gammaZeroPairMeasure N =
        (∫ w, φ (dist I w).cosh) * (2 * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) -
          2 * (kernelPair N φ F F).re := by
  have h1 : ∫ p : ℍ × ℍ, φ (dist p.1 p.2).cosh * ‖F p.1 + (-F) p.2‖ ^ 2
      ∂gammaZeroPairMeasure N = (∫ w, φ (dist I w).cosh) *
        ((∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) + ∫ z in gammaZeroDomain N, ‖(-F) z‖ ^ 2) +
          2 * (kernelPair N φ (-F) F).re :=
    integral_kernel_mul_norm_add_sq (neg_mem hF) hF hφ hφ0
  have h3 : kernelPair N φ (-F) F = -kernelPair N φ F F := by
    rw [kernelPair, kernelPair, ← integral_neg]
    refine integral_congr_ae (.of_forall fun p ↦ ?_)
    simp
  simp only [Pi.neg_apply, norm_neg, ← sub_eq_add_neg] at h1
  rw [h3, Complex.neg_re] at h1
  rw [h1]
  ring1

lemma integrable_kernel_mul_norm_sub_sq (hF : F ∈ maassSpace N χ a) (hφ : Continuous φ)
    (hφ0 : ∀ c, C ≤ c → φ c = 0) : Integrable
      (fun p : ℍ × ℍ ↦ φ (dist p.1 p.2).cosh * ‖F p.1 - F p.2‖ ^ 2) (gammaZeroPairMeasure N) := by
  have h : Integrable (fun p : ℍ × ℍ ↦ φ (dist p.1 p.2).cosh * ‖F p.1 + (-F) p.2‖ ^ 2)
      (gammaZeroPairMeasure N) := integrable_kernel_mul_norm_add_sq (neg_mem hF) hF hφ hφ0
  simpa only [Pi.neg_apply, ← sub_eq_add_neg] using h

lemma re_kernelPair_le (hF : F ∈ maassSpace N χ a) :
    (kernelPair N (coshDistNormalBump n) F F).re ≤ ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := by
  have h1 : ∫ p : ℍ × ℍ, coshDistNormalBump n (dist p.1 p.2).cosh * ‖F p.1 - F p.2‖ ^ 2
      ∂gammaZeroPairMeasure N = (∫ w, coshDistNormalBump n (dist I w).cosh) *
        (2 * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) -
          2 * (kernelPair N (coshDistNormalBump n) F F).re :=
    integral_kernel_mul_norm_sub_sq_eq hF contDiff_coshDistNormalBump.continuous
      fun _ hc ↦ coshDistNormalBump_eq_zero hc
  rw [integral_coshDistNormalBump I, one_mul] at h1
  have h2 : 0 ≤ ∫ p : ℍ × ℍ, coshDistNormalBump n (dist p.1 p.2).cosh *
      ‖F p.1 - F p.2‖ ^ 2 ∂gammaZeroPairMeasure N :=
    integral_nonneg fun p ↦ mul_nonneg (coshDistNormalBump_nonneg _) (by positivity)
  linarith

lemma maassPetersson_smul_smul (x y : ℂ) :
    maassPetersson N (x • F) (y • G) = x * conj y * maassPetersson N F G := by
  simp only [maassPetersson, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  ring1

lemma re_kernelPair_radialGreen_neg (hF : F ∈ maassSpace N χ (l : ℂ))
    (hE : 0 < ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) (hm : 384 * |l| < m + 1) :
    (kernelPair N (radialGreen (2 * (2 * m + 1) + 1)) F F).re < 0 := by
  let n : ℕ := 2 * (2 * m + 1) + 1
  let E : ℝ := ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2
  have hψ : Continuous fun c ↦ -radialGreen n c := (contDiff_radialGreen n).continuous.neg
  have hψ0 : ∀ c, 3 ≤ c → -radialGreen n c = 0 := fun c hc ↦ by
    rw [radialGreen_eq_zero_of_three_le n hc, neg_zero]
  have hk : Continuous (coshDistBump (2 * m + 1)) := contDiff_coshDistBump.continuous
  have hk0 : ∀ c, 3 ≤ c → coshDistBump (2 * m + 1) c = 0 := fun _ hc ↦ coshDistBump_eq_zero hc
  have hI1 : ∫ p : ℍ × ℍ, (-radialGreen n (dist p.1 p.2).cosh) * ‖F p.1 - F p.2‖ ^ 2
      ∂gammaZeroPairMeasure N = (∫ w, -radialGreen n (dist I w).cosh) * (2 * E) -
        2 * (kernelPair N (fun c ↦ -radialGreen n c) F F).re :=
    integral_kernel_mul_norm_sub_sq_eq hF hψ hψ0
  have hneg : kernelPair N (fun c ↦ -radialGreen n c) F F = -kernelPair N (radialGreen n) F F := by
    rw [kernelPair, kernelPair, ← integral_neg]
    refine integral_congr_ae (.of_forall fun p ↦ ?_)
    simp
  rw [hneg, Complex.neg_re] at hI1
  have hI2 : ∫ p : ℍ × ℍ, (-radialGreen n (dist p.1 p.2).cosh) * ‖F p.1 - F p.2‖ ^ 2
      ∂gammaZeroPairMeasure N ≤ ∫ p : ℍ × ℍ, coshDistBump (2 * m + 1) (dist p.1 p.2).cosh *
        ‖F p.1 - F p.2‖ ^ 2 ∂gammaZeroPairMeasure N :=
    integral_mono (integrable_kernel_mul_norm_sub_sq hF hψ hψ0)
      (integrable_kernel_mul_norm_sub_sq hF hk hk0) fun p ↦ mul_le_mul_of_nonneg_right
        (neg_radialGreen_le_coshDistBump (2 * m + 1) (Real.one_le_cosh _)) (by positivity)
  have hI3 : ∫ p : ℍ × ℍ, coshDistBump (2 * m + 1) (dist p.1 p.2).cosh *
      ‖F p.1 - F p.2‖ ^ 2 ∂gammaZeroPairMeasure N = bumpMass (2 * m + 1) *
        (2 * E - 2 * (kernelPair N (coshDistNormalBump (2 * m + 1)) F F).re) := by
    have h1 : ∫ p : ℍ × ℍ, coshDistNormalBump (2 * m + 1) (dist p.1 p.2).cosh *
        ‖F p.1 - F p.2‖ ^ 2 ∂gammaZeroPairMeasure N =
          (∫ w, coshDistNormalBump (2 * m + 1) (dist I w).cosh) * (2 * E) -
            2 * (kernelPair N (coshDistNormalBump (2 * m + 1)) F F).re :=
      integral_kernel_mul_norm_sub_sq_eq hF contDiff_coshDistNormalBump.continuous
        fun _ hc ↦ coshDistNormalBump_eq_zero hc
    rw [integral_coshDistNormalBump I, one_mul] at h1
    rw [← h1, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun p ↦ ?_)
    dsimp only
    rw [coshDistBump_eq_mul (2 * m + 1), mul_assoc]
  have hclose :
      E ≤ (kernelPair N (coshDistNormalBump (2 * m + 1)) F F).re + 2 * (|l| * E / (m + 1)) :=
    le_re_kernelPair_add m hF hE
  have hM : bumpMass (2 * m + 1) / 192 ≤ ∫ w, -radialGreen n (dist I w).cosh := by
    have h1 : ∫ w : ℍ, 1 / 12 * coshDistBump (8 * n + 7) (dist I w).cosh ≤
        ∫ w, -radialGreen n (dist I w).cosh :=
      integral_mono ((integrable_kernel I contDiff_coshDistBump.continuous
        fun _ hc ↦ coshDistBump_eq_zero hc).const_mul _) (integrable_kernel I hψ hψ0)
        fun w ↦ coshDistBump_le_neg_radialGreen n (Real.one_le_cosh _)
    rw [integral_const_mul, ← bumpMass, bumpMass_eight_mul_add_seven, bumpMass_two_mul_add_one]
      at h1
    linarith
  have hb : 0 < bumpMass (2 * m + 1) := bumpMass_pos _
  have hm0 : (0 : ℝ) < m + 1 := by
    positivity
  have hE0 : 0 < E := hE
  have hlt : 2 * (|l| * E / (m + 1)) < E / 192 := by
    have h0 : 2 * |l| / ((m : ℝ) + 1) < 1 / 192 := by
      rw [div_lt_iff₀ hm0]
      linarith
    have h1 : 2 * (|l| * E / (m + 1)) = 2 * |l| / ((m : ℝ) + 1) * E := by
      ring1
    have h2 : 2 * |l| / ((m : ℝ) + 1) * E < 1 / 192 * E := mul_lt_mul_of_pos_right h0 hE0
    rw [h1]
    linarith
  have h6 : E - (kernelPair N (coshDistNormalBump (2 * m + 1)) F F).re < E / 192 := by
    linarith
  have h8 : bumpMass (2 * m + 1) * (E - (kernelPair N (coshDistNormalBump (2 * m + 1)) F F).re) <
      bumpMass (2 * m + 1) * (E / 192) := mul_lt_mul_of_pos_left h6 hb
  have h9 : bumpMass (2 * m + 1) / 192 * E ≤ (∫ w, -radialGreen n (dist I w).cosh) * E :=
    mul_le_mul_of_nonneg_right hM hE0.le
  have h10 : bumpMass (2 * m + 1) / 192 * E = bumpMass (2 * m + 1) * (E / 192) := by
    ring1
  nlinarith

/-- **The eigenvalue of a Maass form is nonnegative** (LMFDB `mf.maass.exceptional_eigenvalue`,
`mf.maass.spectral_index`): a nonzero element of `M(N, χ, l)`, `l` real, has `l ≥ 0`, with no
cuspidality or decay hypothesis. If `l < 0`, then along the chain `doubleChain m`, for `m` large,
the pairing `Re B(P_n; F, F)` with the kernels `P_n` decreases strictly when the kernels shrink,
since `B(P_{2n + 1}) - B(P_n)` is a positive multiple of `B(radialGreen n)` with a negative real
part; Fatou's lemma then gives a pairing larger than `‖F‖²`, which is impossible. -/
lemma zero_le_of_mem_maassSpace (hF : F ∈ maassSpace N χ (l : ℂ)) (hF0 : F ≠ 0) : 0 ≤ l := by
  by_contra hl
  have hl0 : l < 0 := not_le.mp hl
  have hE : 0 < ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := integral_norm_sq_pos hF hF0
  rcases exists_nat_gt (384 * |l|) with ⟨m, hm⟩
  have hm' : 384 * |l| < m + 1 := hm.trans (by linarith)
  have hstep (J : ℕ) : (kernelPair N (coshDistNormalBump (doubleChain m (J + 3))) F F).re <
      (kernelPair N (coshDistNormalBump (doubleChain m (J + 2))) F F).re := by
    have hJ : 384 * |l| < doubleChain m J + 1 := by
      have h : (m : ℝ) ≤ doubleChain m J := by
        exact_mod_cast self_le_doubleChain m J
      linarith
    have h1 : (kernelPair N (radialGreen (doubleChain m (J + 2))) F F).re < 0 := by
      rw [doubleChain_succ, doubleChain_succ]
      exact re_kernelPair_radialGreen_neg hF hE hJ
    have h2 : (kernelPair N (coshDistNormalBump (2 * doubleChain m (J + 2) + 1)) F F).re -
        (kernelPair N (coshDistNormalBump (doubleChain m (J + 2))) F F).re =
          -(l / ((doubleChain m (J + 2) + 1) * bumpMass (doubleChain m (J + 2)))) *
            (kernelPair N (radialGreen (doubleChain m (J + 2))) F F).re :=
      re_kernelPair_sub _ hF
    have h3 : 0 < -(l / ((doubleChain m (J + 2) + 1) * bumpMass (doubleChain m (J + 2)))) :=
      neg_pos.mpr (div_neg_of_neg_of_pos hl0 (mul_pos (by positivity) (bumpMass_pos _)))
    rw [doubleChain_succ]
    linarith [mul_neg_of_pos_of_neg h3 h1]
  have hanti (J : ℕ) : (kernelPair N (coshDistNormalBump (doubleChain m (J + 3))) F F).re ≤
      (kernelPair N (coshDistNormalBump (doubleChain m 3)) F F).re := by
    induction J with
    | zero => exact le_rfl
    | succ J ih => exact (hstep (J + 1)).le.trans ih
  have h : ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 ≤
      (kernelPair N (coshDistNormalBump (doubleChain m 3)) F F).re :=
    le_of_forall_re_kernelPair_le hF hE ((tendsto_doubleChain m).comp
      (tendsto_add_atTop_nat 3)) hanti
  have h7 : (kernelPair N (coshDistNormalBump (doubleChain m 3)) F F).re <
      (kernelPair N (coshDistNormalBump (doubleChain m 2)) F F).re := hstep 0
  have h8 : (kernelPair N (coshDistNormalBump (doubleChain m 2)) F F).re ≤
      ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := re_kernelPair_le _ hF
  linarith

lemma re_maassPetersson_nonpos (hF : F ∈ maassSpace N χ a) (hG : G ∈ maassSpace N χ b)
    (hab : a ≠ conj b) : (maassPetersson N F G).re ≤ 0 := by
  have h : ENNReal.ofReal (∫ z in gammaZeroDomain N, ‖G z + F z‖ ^ 2) ≤ liminf (fun j : ℕ ↦
      ENNReal.ofReal ((∫ z in gammaZeroDomain N, ‖G z‖ ^ 2) +
        (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) +
          2 * (kernelPair N (coshDistNormalBump j) F G).re)) atTop :=
    ofReal_integral_le_liminf hF hG tendsto_id
  simp only [kernelPair_eq_zero hF hG contDiff_coshDistNormalBump
    (fun _ hc ↦ coshDistNormalBump_eq_zero hc) hab, Complex.zero_re, mul_zero, add_zero,
    liminf_const] at h
  have hE : 0 ≤ (∫ z in gammaZeroDomain N, ‖G z‖ ^ 2) + ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 :=
    add_nonneg (integral_nonneg fun z ↦ by positivity) (integral_nonneg fun z ↦ by positivity)
  have h1 : ∫ z in gammaZeroDomain N, ‖G z + F z‖ ^ 2 ≤
      (∫ z in gammaZeroDomain N, ‖G z‖ ^ 2) + ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff hE).mp h
  have hexp (z : ℍ) :
      ‖G z + F z‖ ^ 2 = ‖G z‖ ^ 2 + ‖F z‖ ^ 2 + 2 * Complex.reCLM (F z * conj (G z)) := by
    simpa using mul_norm_add_sq_eq 1 (G z) (F z)
  have hG2 : IntegrableOn (fun z ↦ ‖G z‖ ^ 2) (gammaZeroDomain N) :=
    integrableOn_norm_sq_of_mem_maassSpace hG
  have hF2 : IntegrableOn (fun z ↦ ‖F z‖ ^ 2) (gammaZeroDomain N) :=
    integrableOn_norm_sq_of_mem_maassSpace hF
  have hFG : IntegrableOn (fun z ↦ F z * conj (G z)) (gammaZeroDomain N) :=
    (memLp_of_mem_maassSpace hF).integrable_mul (memLp_of_mem_maassSpace hG).star
  have h12 : IntegrableOn (fun z ↦ ‖G z‖ ^ 2 + ‖F z‖ ^ 2) (gammaZeroDomain N) := hG2.add hF2
  simp only [hexp] at h1
  rw [integral_add h12 ((Complex.reCLM.integrable_comp hFG).const_mul 2), integral_add hG2 hF2,
    integral_const_mul, Complex.reCLM.integral_comp_comm hFG] at h1
  have h2 :
      Complex.reCLM (∫ z in gammaZeroDomain N, F z * conj (G z)) = (maassPetersson N F G).re :=
    rfl
  linarith

/-- **Maass forms with different eigenvalues are orthogonal**: for `F` in `M(N, χ, a)` and `G` in
`M(N, χ, b)` with `a ≠ conj b`, `⟨F, G⟩ = 0`, with no cuspidality or decay hypothesis. The pairing
`B(φ; F, ωG)` vanishes for every kernel `φ`, so that Fatou's lemma gives
`‖ωG + F‖² ≤ ‖G‖² + ‖F‖²` for `ω` in `{1, -1, i, -i}`. -/
lemma maassPetersson_eq_zero_of_ne (hF : F ∈ maassSpace N χ a) (hG : G ∈ maassSpace N χ b)
    (hab : a ≠ conj b) : maassPetersson N F G = 0 := by
  have h (c : ℂ) : (conj c * maassPetersson N F G).re ≤ 0 := by
    have e : maassPetersson N F (c • G) = conj c * maassPetersson N F G := by
      simpa using maassPetersson_smul_smul (F := F) (G := G) 1 c
    exact e ▸ re_maassPetersson_nonpos hF (Submodule.smul_mem _ _ hG) hab
  have h1 : (conj (1 : ℂ) * maassPetersson N F G).re ≤ 0 := h 1
  have h2 : (conj (-1 : ℂ) * maassPetersson N F G).re ≤ 0 := h (-1)
  have h3 : (conj Complex.I * maassPetersson N F G).re ≤ 0 := h Complex.I
  have h4 : (conj (-Complex.I) * maassPetersson N F G).re ≤ 0 := h (-Complex.I)
  simp only [map_one, map_neg, Complex.conj_I, Complex.mul_re, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at h1 h2 h3 h4
  exact Complex.ext (by simp; linarith) (by simp; linarith)

end UpperHalfPlane
