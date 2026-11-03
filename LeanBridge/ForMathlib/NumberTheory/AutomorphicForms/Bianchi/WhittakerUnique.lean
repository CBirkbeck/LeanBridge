import LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselKUnique
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.WhittakerRadial

/-!
# Uniqueness of the harmonic Whittaker function of moderate growth

Let `k ≥ 1` (the weights of LMFDB `mf.bianchi.weight`) and `μ ∈ ℂ`, `μ ≠ 0`. A harmonic Fourier mode
`F(x, y) = ψ(μx) φ(y)` of weight `k` (`bianchiFourierMode`, `IsBianchiHarmonic k`), with `φ` of
class `C²` on `(0, ∞)` and of moderate growth (`‖φ(y)‖ ≤ C yⁿ` for `y ≥ 1`, the bound of
`HasPolynomialGrowthAtCusps`), is `φ₀(1) / W_k(u, 4π|μ|)₀` times the Fourier–Bessel (Whittaker)
function `y W_k(u, 4π|μ|y) ψ(μx)` (`bianchiWhittakerFunction`), which is harmonic
(`isBianchiHarmonic_bianchiWhittakerFunction`) and of moderate growth (`K_ν` decays). So the vector
`W_k` of the expansion `HasBianchiWhittakerExpansion` by which the newforms of weight `k` are
normalised (`BianchiNewformOfWeight`, `c(1) = 1`) is, up to a scalar, the only one possible.

The Casimir equations of `F` are radial equations of `R_j(y) = y^k φ_j(y)`
(`bianchiRadialOperator_eq_zero_of_casimirOne`, `bianchiRadialOperator_eq_zero_of_casimirTwo`).
The reflected radial equation of index `k` of the second Casimir operator only involves `R₀`:
`y² R₀'' - (2k + 1) y R₀' + ((k + 1)² - k²/4 - 16π²|μ|²y²) R₀ = 0`, so
`R₀(y) / y^{k+1} = φ₀(y) / y`, as a function of `4π|μ|y`, solves the modified Bessel equation of
order `k/2`. Its difference with the radial equation of index `0` of the first Casimir operator is
the first order relation `y R₀' = (k + 2)/2 R₀ - 4πiμ y R₁`, by which `φ₀'` grows moderately with
`φ`. A moderately growing solution of the Bessel equation is a multiple of `K_{k/2}`
(`Complex.eq_div_mul_besselK_of_ode`), so `R₀` is proportional to the radial function of index `0`
of the Whittaker function. The radial equation of index `j` of the first Casimir operator gives
`R_{j+1}` from `R_j` and its first two derivatives, as `4πiμ(k - j) y ≠ 0` for `j < k`, so all `R_j`
are proportional.

The Fourier coefficients of a Bianchi cusp form are such Fourier modes, and the form is the sum of
its Fourier coefficients: `IsBianchiModularForm.hasSum_bianchiFourierMode`.

## Main results

* `HyperbolicThreeSpace.norm_smul_bianchiWhittakerVector_le`: the Fourier–Bessel vector is of
  moderate growth.
* `HyperbolicThreeSpace.bianchiFourierMode_eq_smul_bianchiWhittakerFunction`: uniqueness of the
  harmonic Whittaker function of moderate growth.
* `HyperbolicThreeSpace.isBianchiHarmonic_bianchiFourierMode_iff`: the harmonic Fourier modes of
  moderate growth are the multiples of the Whittaker function.
* `HyperbolicThreeSpace.bianchiFourierMode_eq_bianchiWhittakerTerm`: a harmonic Fourier mode of
  moderate growth is a term of the Fourier–Bessel expansion.
-/

open Complex Filter MeasureTheory NumberField Set Topology

open scoped ComplexConjugate Real

namespace HyperbolicThreeSpace

open WhittakerCasimir

variable {μ : ℂ} {k : ℕ} {φ : ℝ → Fin (k + 1) → ℂ} {C α : ℝ} {n : ℕ}

variable (μ k) in
/-- The radial part `y W_k(u, 4π|μ|y)` of the Fourier–Bessel function `bianchiWhittakerFunction`. -/
private noncomputable def whittakerRadial (y : ℝ) : Fin (k + 1) → ℂ :=
  (y : ℂ) • bianchiWhittakerVector k (μ / ‖μ‖) (4 * π * ‖μ‖ * y)

variable (μ k) in
private lemma bianchiFourierMode_whittakerRadial :
    bianchiFourierMode μ (whittakerRadial μ k) = bianchiWhittakerFunction μ k := by
  funext z
  simp only [bianchiFourierMode, whittakerRadial, bianchiWhittakerFunction]
  rw [smul_smul, mul_comm]

private lemma contDiffOn_whittakerRadial (hμ : μ ≠ 0) :
    ContDiffOn ℝ 2 (whittakerRadial μ k) (Ioi 0) := by
  have hα : 0 < 4 * π * ‖μ‖ := by
    have hμ' : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
    positivity
  refine contDiffOn_pi.mpr fun j ↦ ?_
  have hK :
      ContDiffOn ℝ 2 (fun s : ℝ ↦ besselK ((j : ℕ) - (k : ℂ) / 2) (4 * π * ‖μ‖ * s)) (Ioi 0) :=
    ((contDiffOn_besselK _).of_le (by norm_cast)).comp (by fun_prop) fun s hs ↦ mul_pos hα hs
  exact contDiff_ofReal.contDiffOn.mul (contDiffOn_const.mul hK)

/-- **The Fourier–Bessel vector is of moderate growth**: for `μ ≠ 0` and `y ≥ 1`,
`‖y W_k(u, 4π|μ|y)‖ ≤ C y`, where `C = ∑_j ½ ∫₀^∞ |t^{j - k/2 - 1} e^{-2π|μ|(t + 1/t)}| dt`. So the
radial part of the Fourier–Bessel function `bianchiWhittakerFunction` satisfies the growth
hypothesis of `bianchiFourierMode_eq_smul_bianchiWhittakerFunction`. -/
lemma norm_smul_bianchiWhittakerVector_le (hμ : μ ≠ 0) {y : ℝ} (hy : 1 ≤ y) :
    ‖(y : ℂ) • bianchiWhittakerVector k (μ / ‖μ‖) (4 * π * ‖μ‖ * y)‖ ≤ (∑ j : Fin (k + 1),
      2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand ((j : ℕ) - (k : ℂ) / 2) (4 * π * ‖μ‖) t‖) * y := by
  have hμ' : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
  have hα : 0 < 4 * π * ‖μ‖ := by positivity
  have hc (j : Fin (k + 1)) :
      0 ≤ 2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand ((j : ℕ) - (k : ℂ) / 2) (4 * π * ‖μ‖) t‖ :=
    mul_nonneg (by norm_num) (integral_nonneg fun _ ↦ norm_nonneg _)
  rw [norm_smul, norm_real, Real.norm_of_nonneg (zero_le_one.trans hy), mul_comm]
  refine mul_le_mul_of_nonneg_right ((pi_norm_le_iff_of_nonneg
    (Finset.sum_nonneg fun j _ ↦ hc j)).mpr fun j ↦ ?_) (zero_le_one.trans hy)
  simp only [bianchiWhittakerVector]
  rw [norm_mul, norm_zpow, norm_mul, Complex.norm_I, one_mul, norm_div_norm_eq_one hμ, one_zpow,
    one_mul]
  have hle : 4 * π * ‖μ‖ ≤ 4 * π * ‖μ‖ * y := le_mul_of_one_le_right hα.le hy
  exact ((norm_besselK_le_of_le _ hα hle).trans (mul_le_of_le_one_left (hc j)
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sub_nonneg.mpr hle))))).trans
      (Finset.single_le_sum (fun i _ ↦ hc i) (Finset.mem_univ j))

private lemma exists_bound_of_growth (hφ : ContinuousOn φ (Ioi 0))
    (hC : ∀ y, 1 ≤ y → ‖φ y‖ ≤ C * y ^ n) (hα : 0 < α) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, 1 ≤ x → ‖φ (x / α)‖ ≤ B * x ^ n := by
  have hα' : 0 < α⁻¹ := inv_pos.mpr hα
  rcases (isCompact_Icc (a := α⁻¹) (b := 1)).exists_bound_of_continuousOn
    (hφ.mono fun y hy ↦ hα'.trans_le hy.1) with ⟨M, hM⟩
  refine ⟨max M 0 + |C| * α⁻¹ ^ n, by positivity, fun x hx ↦ ?_⟩
  have hx₀ : 1 ≤ x ^ n := one_le_pow₀ hx
  have hxα : α⁻¹ ≤ x / α := by
    rw [div_eq_mul_inv]
    nlinarith
  have hp : 0 ≤ |C| * α⁻¹ ^ n := by positivity
  rcases le_total (x / α) 1 with h | h
  · have hb : ‖φ (x / α)‖ ≤ M := hM _ ⟨hxα, h⟩
    nlinarith [le_max_left M 0, le_max_right M 0]
  · have hb : ‖φ (x / α)‖ ≤ C * (x / α) ^ n := hC _ h
    have e : (x / α) ^ n = α⁻¹ ^ n * x ^ n := by
      rw [div_pow, div_eq_mul_inv, inv_pow, mul_comm]
    rw [e] at hb
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C)
      (mul_nonneg (pow_nonneg hα'.le n) (zero_le_one.trans hx₀)),
      mul_nonneg (le_max_right M 0) (zero_le_one.trans hx₀)]

variable {R₀ : ℝ → ℂ} {t : ℝ}

variable (k R₀) in
/-- The quotient `R₀(t) / t^{k+1}`, which solves the modified Bessel equation of order `k / 2` in
`4π|μ|t` when `R₀` is the radial function of index `0` of a harmonic Fourier mode. -/
private noncomputable def radialQuot (t : ℝ) : ℂ :=
  R₀ t / (t : ℂ) ^ (k + 1)

variable (k R₀) in
/-- The derivative of `radialQuot`. -/
private noncomputable def radialQuot' (t : ℝ) : ℂ :=
  deriv R₀ t / (t : ℂ) ^ (k + 1) - ((k : ℂ) + 1) * R₀ t / (t : ℂ) ^ (k + 2)

variable (k R₀) in
/-- The second derivative of `radialQuot`. -/
private noncomputable def radialQuot'' (t : ℝ) : ℂ :=
  deriv (deriv R₀) t / (t : ℂ) ^ (k + 1) - 2 * ((k : ℂ) + 1) * deriv R₀ t / (t : ℂ) ^ (k + 2) +
    ((k : ℂ) + 1) * ((k : ℂ) + 2) * R₀ t / (t : ℂ) ^ (k + 3)

private lemma hasDerivAt_radialQuot (hR : ContDiffOn ℝ 2 R₀ (Ioi 0)) (ht : 0 < t) :
    HasDerivAt (radialQuot k R₀) (radialQuot' k R₀ t) t := by
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  refine ((hasDerivAt_of_contDiffOn_Ioi hR ht).div (hasDerivAt_ofReal_pow k)
    (pow_ne_zero _ ht')).congr_deriv ?_
  simp only [radialQuot']
  push_cast
  field_simp
  ring1

private lemma hasDerivAt_radialQuot' (hR : ContDiffOn ℝ 2 R₀ (Ioi 0)) (ht : 0 < t) :
    HasDerivAt (radialQuot' k R₀) (radialQuot'' k R₀ t) t := by
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  refine (((hasDerivAt_deriv_of_contDiffOn_Ioi hR ht).div (hasDerivAt_ofReal_pow k)
    (pow_ne_zero _ ht')).sub (((hasDerivAt_of_contDiffOn_Ioi hR ht).const_mul ((k : ℂ) + 1)).div
      (hasDerivAt_ofReal_pow (k + 1)) (pow_ne_zero _ ht'))).congr_deriv ?_
  simp only [radialQuot'']
  push_cast
  field_simp
  ring1

private lemma eq_mul_besselK_of_radial (hα : 0 < α) (hR : ContDiffOn ℝ 2 R₀ (Ioi 0))
    (hode : ∀ t : ℝ, 0 < t → (t : ℂ) ^ 2 * deriv (deriv R₀) t - (2 * k + 1) * t * deriv R₀ t +
      (((k : ℂ) + 1) ^ 2 - (k : ℂ) ^ 2 / 4 - (α : ℂ) ^ 2 * (t : ℂ) ^ 2) * R₀ t = 0)
    (hb₀ : ∀ x, 1 ≤ x → ‖radialQuot k R₀ (x / α)‖ ≤ C * x ^ n)
    (hb₁ : ∀ x, 1 ≤ x → ‖radialQuot' k R₀ (x / α) / α‖ ≤ C * x ^ n) (ht : 0 < t) :
    R₀ t = R₀ 1 / besselK (-(k / 2 : ℝ) : ℝ) α * (t : ℂ) ^ (k + 1) *
      besselK (-(k / 2 : ℝ) : ℝ) (α * t) := by
  have hα' : (α : ℂ) ≠ 0 := ofReal_ne_zero.mpr hα.ne'
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ ↦ x / α) (1 / α) x :=
    (hasDerivAt_id' x).div_const α
  have hu (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun x ↦ radialQuot k R₀ (x / α)) (radialQuot' k R₀ (x / α) / α) x := by
    refine ((hasDerivAt_radialQuot hR (div_pos hx hα)).scomp x (hd x)).congr_deriv ?_
    rw [real_smul]
    push_cast
    ring1
  have hu' (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun x ↦ radialQuot' k R₀ (x / α) / α) (radialQuot'' k R₀ (x / α) / α ^ 2) x := by
    refine (((hasDerivAt_radialQuot' hR (div_pos hx hα)).scomp x (hd x)).div_const
      (α : ℂ)).congr_deriv ?_
    rw [real_smul]
    push_cast
    ring1
  have hode' (x : ℝ) (hx : 0 < x) : (x : ℂ) ^ 2 * (radialQuot'' k R₀ (x / α) / α ^ 2) +
      x * (radialQuot' k R₀ (x / α) / α) -
        ((x : ℂ) ^ 2 + ((-(k / 2 : ℝ) : ℝ) : ℂ) ^ 2) * radialQuot k R₀ (x / α) = 0 := by
    have ht₀ : 0 < x / α := div_pos hx hα
    have hx' : (x : ℂ) = α * ((x / α : ℝ) : ℂ) := by
      rw [ofReal_div]
      field_simp
    have ht' : ((x / α : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht₀.ne'
    rw [hx']
    generalize x / α = s at ht₀ ht' ⊢
    have e : ((s : ℂ) ^ 2 * radialQuot'' k R₀ s + s * radialQuot' k R₀ s -
        ((α : ℂ) ^ 2 * (s : ℂ) ^ 2 + (k : ℂ) ^ 2 / 4) * radialQuot k R₀ s) * (s : ℂ) ^ (k + 1) =
          (s : ℂ) ^ 2 * deriv (deriv R₀) s - (2 * k + 1) * s * deriv R₀ s +
            (((k : ℂ) + 1) ^ 2 - (k : ℂ) ^ 2 / 4 - (α : ℂ) ^ 2 * (s : ℂ) ^ 2) * R₀ s := by
      simp only [radialQuot, radialQuot', radialQuot'']
      field_simp
      ring1
    rw [hode s ht₀, mul_eq_zero] at e
    push_cast
    field_simp
    linear_combination 4 * e.resolve_right (pow_ne_zero _ ht')
  have key (x : ℝ) (hx : 0 < x) : radialQuot k R₀ (x / α) =
      radialQuot k R₀ (1 / α) / besselK (-(k / 2 : ℝ) : ℝ) 1 * besselK (-(k / 2 : ℝ) : ℝ) x :=
    eq_div_mul_besselK_of_ode _ hu hu' hode' hb₀ hb₁ hx
  have h₁ : radialQuot k R₀ 1 =
      radialQuot k R₀ (1 / α) / besselK (-(k / 2 : ℝ) : ℝ) 1 * besselK (-(k / 2 : ℝ) : ℝ) α := by
    simpa only [div_self hα.ne'] using key α hα
  have h₂ : radialQuot k R₀ t = radialQuot k R₀ (1 / α) / besselK (-(k / 2 : ℝ) : ℝ) 1 *
      besselK (-(k / 2 : ℝ) : ℝ) (α * t) := by
    simpa only [mul_div_cancel_left₀ _ hα.ne'] using key (α * t) (mul_pos hα ht)
  have hK : besselK (-(k / 2 : ℝ) : ℝ) α ≠ 0 := besselK_ofReal_ne_zero _ hα
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  simp only [radialQuot, ofReal_one, one_pow, div_one] at h₁ h₂
  rw [h₁, mul_div_assoc, div_self hK, mul_one,
    ← div_mul_cancel₀ (R₀ t) (pow_ne_zero (k + 1) ht'), h₂]
  ring1

private lemma eq_mul_of_bianchiRadialOperator {R S : ℕ → ℝ → ℂ} (hμ : μ ≠ 0)
    (hR : ∀ j < k, ∀ y, 0 < y → bianchiRadialOperator μ k R j y = 0)
    (hS : ∀ j < k, ∀ y, 0 < y → bianchiRadialOperator μ k S j y = 0) {a : ℂ}
    (h₀ : ∀ y, 0 < y → R 0 y = a * S 0 y) {j : ℕ} (hj : j ≤ k) {y : ℝ} (hy : 0 < y) :
    R j y = a * S j y := by
  induction j generalizing y with
  | zero => exact h₀ y hy
  | succ j ih =>
    have hjk : j < k := hj
    have hR' (s : ℝ) (hs : 0 < s) : R j s = a * S j s := ih hjk.le hs
    have hd (s : ℝ) (hs : 0 < s) : deriv (R j) s = a * deriv (S j) s := by
      have hev : R j =ᶠ[𝓝 s] fun s ↦ a * S j s :=
        eventually_of_mem (Ioi_mem_nhds hs) fun s' (hs' : 0 < s') ↦ hR' s' hs'
      rw [hev.deriv_eq, deriv_const_mul_field']
    have hdd : deriv (deriv (R j)) y = a * deriv (deriv (S j)) y := by
      have hev : deriv (R j) =ᶠ[𝓝 y] fun s ↦ a * deriv (S j) s :=
        eventually_of_mem (Ioi_mem_nhds hy) fun s (hs : 0 < s) ↦ hd s hs
      rw [hev.deriv_eq, deriv_const_mul_field']
    have h₁ : bianchiRadialOperator μ k R j y = 0 := hR j hjk y hy
    have h₂ : bianchiRadialOperator μ k S j y = 0 := hS j hjk y hy
    simp only [bianchiRadialOperator] at h₁ h₂
    rw [hR' y hy, hd y hy, hdd] at h₁
    have hc : 4 * π * I * μ * ((k : ℂ) - j) * y ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero) hμ)
          (sub_ne_zero.mpr (Nat.cast_injective.ne hjk.ne'))) (ofReal_ne_zero.mpr hy.ne')
    refine mul_left_cancel₀ hc ?_
    linear_combination h₁ - a * h₂

private lemma fourierModeRadial_zero_eq (hk : k ≠ 0) (hμ : μ ≠ 0) (hφ : ContDiffOn ℝ 2 φ (Ioi 0))
    (hgrowth : ∃ (C : ℝ) (n : ℕ), ∀ y, 1 ≤ y → ‖φ y‖ ≤ C * y ^ n)
    (h : IsBianchiHarmonic k (bianchiFourierMode μ φ)) (ht : 0 < t) :
    fourierModeRadial φ 0 t = fourierModeRadial φ 0 1 /
      besselK (-(k / 2 : ℝ) : ℝ) (4 * π * ‖μ‖) * (t : ℂ) ^ (k + 1) *
        besselK (-(k / 2 : ℝ) : ℝ) (4 * π * ‖μ‖ * t) := by
  have hμ' : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
  have hα : 0 < 4 * π * ‖μ‖ := by positivity
  have hE2 (y : ℝ) (hy : 0 < y) : (k * (k + 2) / 2 : ℂ) * fourierModeRadial φ 0 y -
      (2⁻¹ + k) * y * deriv (fourierModeRadial φ 0) y +
        2⁻¹ * (y : ℂ) ^ 2 * deriv (deriv (fourierModeRadial φ 0)) y -
          8 * π ^ 2 * normSq μ * (y : ℂ) ^ 2 * fourierModeRadial φ 0 y -
            harmonicEigenvalue k * fourierModeRadial φ 0 y = 0 := by
    have h₂ : bianchiRadialOperator (conj μ) k
        (fun j y ↦ (-1) ^ j * fourierModeRadial φ (k - j) y) k y = 0 :=
      bianchiRadialOperator_eq_zero_of_casimirTwo hφ h.2 le_rfl hy
    simp only [bianchiRadialOperator, Nat.sub_self, deriv_const_mul_field', normSq_conj] at h₂
    refine (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero k (neg_ne_zero.mpr one_ne_zero))
    linear_combination h₂
  have hrel (y : ℝ) (hy : 0 < y) : (y : ℂ) * deriv (fourierModeRadial φ 0) y =
      (k + 2) / 2 * fourierModeRadial φ 0 y - 4 * π * I * μ * y * fourierModeRadial φ 1 y := by
    have h₁ : bianchiRadialOperator μ k (fourierModeRadial φ) 0 y = 0 :=
      bianchiRadialOperator_eq_zero_of_casimirOne hφ h.1 (Nat.zero_le k) hy
    simp only [bianchiRadialOperator] at h₁
    refine mul_left_cancel₀ (Nat.cast_ne_zero.mpr hk : (k : ℂ) ≠ 0) ?_
    linear_combination h₁ - hE2 y hy
  have hn : (normSq μ : ℂ) = (‖μ‖ : ℂ) ^ 2 := by
    rw [normSq_eq_norm_sq, ofReal_pow]
  have hev : harmonicEigenvalue k = ((k : ℂ) ^ 2 - 4) / 8 :=
    rfl
  have hode (y : ℝ) (hy : 0 < y) : (y : ℂ) ^ 2 * deriv (deriv (fourierModeRadial φ 0)) y -
      (2 * k + 1) * y * deriv (fourierModeRadial φ 0) y + (((k : ℂ) + 1) ^ 2 - (k : ℂ) ^ 2 / 4 -
        ((4 * π * ‖μ‖ : ℝ) : ℂ) ^ 2 * (y : ℂ) ^ 2) * fourierModeRadial φ 0 y = 0 := by
    push_cast
    linear_combination 2 * hE2 y hy + 16 * π ^ 2 * (y : ℂ) ^ 2 * fourierModeRadial φ 0 y * hn +
      2 * fourierModeRadial φ 0 y * hev
  have hq₀ (y : ℝ) (hy : 0 < y) :
      radialQuot k (fourierModeRadial φ 0) y = φ y (Fin.ofNat (k + 1) 0) * (y : ℂ)⁻¹ := by
    have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
    simp only [radialQuot, fourierModeRadial]
    field_simp
    ring1
  have hq₁ (y : ℝ) (hy : 0 < y) : radialQuot' k (fourierModeRadial φ 0) y =
      -((k : ℂ) / 2) * φ y (Fin.ofNat (k + 1) 0) * (y : ℂ)⁻¹ ^ 2 -
        4 * π * I * μ * φ y (Fin.ofNat (k + 1) 1) * (y : ℂ)⁻¹ := by
    have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
    have hD : deriv (fourierModeRadial φ 0) y = ((k + 2) / 2 * fourierModeRadial φ 0 y -
        4 * π * I * μ * y * fourierModeRadial φ 1 y) / y := by
      rw [eq_div_iff hy']
      linear_combination hrel y hy
    simp only [radialQuot', hD, fourierModeRadial]
    field_simp
    ring1
  rcases hgrowth with ⟨C₀, n, hC₀⟩
  rcases exists_bound_of_growth hφ.continuousOn hC₀ hα with ⟨B, hB, hBx⟩
  have hb₀ (x : ℝ) (hx : 1 ≤ x) : ‖radialQuot k (fourierModeRadial φ 0) (x / (4 * π * ‖μ‖))‖ ≤
      ((k / 2 + 1) * (4 * π * ‖μ‖) * B) * x ^ n := by
    have hy : 0 < x / (4 * π * ‖μ‖) := div_pos (zero_lt_one.trans_le hx) hα
    have hinv : ‖((x / (4 * π * ‖μ‖) : ℝ) : ℂ)⁻¹‖ ≤ 4 * π * ‖μ‖ := by
      rw [norm_inv, norm_real, Real.norm_of_nonneg hy.le, inv_div]
      exact div_le_self hα.le hx
    have hφ₀ : ‖φ (x / (4 * π * ‖μ‖)) (Fin.ofNat (k + 1) 0)‖ ≤ B * x ^ n :=
      (norm_le_pi_norm _ _).trans (hBx x hx)
    have hxn : 0 ≤ B * x ^ n := mul_nonneg hB (pow_nonneg (zero_le_one.trans hx) n)
    rw [hq₀ _ hy, norm_mul]
    nlinarith [mul_le_mul hφ₀ hinv (norm_nonneg _) hxn,
      mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ k / 2) hα.le) hxn]
  have hb₁ (x : ℝ) (hx : 1 ≤ x) : ‖radialQuot' k (fourierModeRadial φ 0) (x / (4 * π * ‖μ‖)) /
      ((4 * π * ‖μ‖ : ℝ) : ℂ)‖ ≤ ((k / 2 + 1) * (4 * π * ‖μ‖) * B) * x ^ n := by
    have hy : 0 < x / (4 * π * ‖μ‖) := div_pos (zero_lt_one.trans_le hx) hα
    have hinv : ‖((x / (4 * π * ‖μ‖) : ℝ) : ℂ)⁻¹‖ ≤ 4 * π * ‖μ‖ := by
      rw [norm_inv, norm_real, Real.norm_of_nonneg hy.le, inv_div]
      exact div_le_self hα.le hx
    have hφ₀ : ‖φ (x / (4 * π * ‖μ‖)) (Fin.ofNat (k + 1) 0)‖ ≤ B * x ^ n :=
      (norm_le_pi_norm _ _).trans (hBx x hx)
    have hφ₁ : ‖φ (x / (4 * π * ‖μ‖)) (Fin.ofNat (k + 1) 1)‖ ≤ B * x ^ n :=
      (norm_le_pi_norm _ _).trans (hBx x hx)
    have h₁ : ‖-((k : ℂ) / 2) * φ (x / (4 * π * ‖μ‖)) (Fin.ofNat (k + 1) 0) *
        ((x / (4 * π * ‖μ‖) : ℝ) : ℂ)⁻¹ ^ 2‖ ≤ k / 2 * (B * x ^ n) * (4 * π * ‖μ‖) ^ 2 := by
      rw [norm_mul, norm_mul, norm_neg, norm_pow, norm_div, Complex.norm_natCast,
        Complex.norm_ofNat]
      gcongr
    have h₂ : ‖4 * π * I * μ * φ (x / (4 * π * ‖μ‖)) (Fin.ofNat (k + 1) 1) *
        ((x / (4 * π * ‖μ‖) : ℝ) : ℂ)⁻¹‖ ≤ 4 * π * ‖μ‖ * (B * x ^ n) * (4 * π * ‖μ‖) := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, norm_real,
        Complex.norm_I, Real.norm_of_nonneg Real.pi_pos.le, mul_one]
      gcongr
    rw [hq₁ _ hy, norm_div, norm_real, Real.norm_of_nonneg hα.le, div_le_iff₀ hα]
    nlinarith [norm_sub_le (-((k : ℂ) / 2) * φ (x / (4 * π * ‖μ‖)) (Fin.ofNat (k + 1) 0) *
      ((x / (4 * π * ‖μ‖) : ℝ) : ℂ)⁻¹ ^ 2) (4 * π * I * μ * φ (x / (4 * π * ‖μ‖))
        (Fin.ofNat (k + 1) 1) * ((x / (4 * π * ‖μ‖) : ℝ) : ℂ)⁻¹)]
  exact eq_mul_besselK_of_radial hα (contDiffOn_fourierModeRadial hφ 0) hode hb₀ hb₁ ht

/-- **Uniqueness of the harmonic Whittaker function of moderate growth** (LMFDB
`mf.bianchi.spaces`, `mf.bianchi.newform`): for `k ≥ 1` and `μ ≠ 0`, a Fourier mode
`F(x, y) = ψ(μx) φ(y)` of weight `k` (`bianchiFourierMode`), with `φ` of class `C²` on `(0, ∞)`
and of moderate growth (`‖φ(y)‖ ≤ C yⁿ` for `y ≥ 1`), which is harmonic (`IsBianchiHarmonic k`) is
the multiple `φ₀(1) / W_k(u, 4π|μ|)₀` of the Fourier–Bessel function `y W_k(u, 4π|μ|y) ψ(μx)`
(`bianchiWhittakerFunction`). The second Casimir equation gives a modified Bessel equation for
`φ₀(y) / y` in `4π|μ|y`, whose moderately growing solutions are the multiples of `K_{k/2}`
(`Complex.eq_div_mul_besselK_of_ode`), and the first one gives `φ_{j+1}` from `φ_j`. -/
lemma bianchiFourierMode_eq_smul_bianchiWhittakerFunction (hk : k ≠ 0) (hμ : μ ≠ 0)
    (hφ : ContDiffOn ℝ 2 φ (Ioi 0)) (hgrowth : ∃ (C : ℝ) (n : ℕ), ∀ y, 1 ≤ y → ‖φ y‖ ≤ C * y ^ n)
    (h : IsBianchiHarmonic k (bianchiFourierMode μ φ)) : bianchiFourierMode μ φ =
      (φ 1 0 / bianchiWhittakerVector k (μ / ‖μ‖) (4 * π * ‖μ‖) 0) •
        bianchiWhittakerFunction μ k := by
  have hμ' : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
  have hα : 0 < 4 * π * ‖μ‖ := by positivity
  have hW : IsBianchiHarmonic k (bianchiFourierMode μ (whittakerRadial μ k)) := by
    rw [bianchiFourierMode_whittakerRadial]
    exact isBianchiHarmonic_bianchiWhittakerFunction μ k hμ
  have hK : besselK (-(k / 2 : ℝ) : ℝ) (4 * π * ‖μ‖) ≠ 0 := besselK_ofReal_ne_zero _ hα
  have hμc : (‖μ‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hμ'.ne'
  have hS₀ (t : ℝ) : fourierModeRadial (whittakerRadial μ k) 0 t = (I * (μ / ‖μ‖)) ^ (k / 2) *
      (t : ℂ) ^ (k + 1) * besselK (-(k / 2 : ℝ) : ℝ) (4 * π * ‖μ‖ * t) := by
    have h0 : Fin.ofNat (k + 1) 0 = 0 := Fin.ext (Nat.zero_mod _)
    simp only [fourierModeRadial, whittakerRadial, bianchiWhittakerVector, h0, Pi.smul_apply,
      Fin.val_zero, Nat.cast_zero, sub_zero, zero_sub, zpow_natCast]
    push_cast
    ring1
  have hS₁ : fourierModeRadial (whittakerRadial μ k) 0 1 ≠ 0 := by
    rw [hS₀, ofReal_one, one_pow, mul_one, mul_one]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero I_ne_zero (div_ne_zero hμ hμc))) hK
  have h₀ (t : ℝ) (ht : 0 < t) : fourierModeRadial φ 0 t = fourierModeRadial φ 0 1 /
      fourierModeRadial (whittakerRadial μ k) 0 1 *
        fourierModeRadial (whittakerRadial μ k) 0 t := by
    rw [div_mul_eq_mul_div, eq_div_iff hS₁, fourierModeRadial_zero_eq hk hμ hφ hgrowth h ht, hS₀,
      hS₀]
    simp only [ofReal_one, one_pow]
    field_simp
  have ha : fourierModeRadial φ 0 1 / fourierModeRadial (whittakerRadial μ k) 0 1 =
      φ 1 0 / bianchiWhittakerVector k (μ / ‖μ‖) (4 * π * ‖μ‖) 0 := by
    simp [fourierModeRadial, whittakerRadial]
  rw [← bianchiFourierMode_whittakerRadial, ← ha]
  generalize fourierModeRadial φ 0 1 / fourierModeRadial (whittakerRadial μ k) 0 1 = a at h₀ ⊢
  funext z
  ext i
  have hy : 0 < z.coords.2 := z.height_pos
  have hi :
      fourierModeRadial φ i z.coords.2 = a * fourierModeRadial (whittakerRadial μ k) i z.coords.2 :=
    eq_mul_of_bianchiRadialOperator hμ
      (fun j hj y hy ↦ bianchiRadialOperator_eq_zero_of_casimirOne hφ h.1 hj.le hy)
      (fun j hj y hy ↦ bianchiRadialOperator_eq_zero_of_casimirOne
        (contDiffOn_whittakerRadial hμ) hW.1 hj.le hy) h₀ (Nat.lt_succ_iff.mp i.2) hy
  simp only [fourierModeRadial, Fin.ofNat_val_eq_self] at hi
  have hy' : (z.coords.2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (ofReal_ne_zero.mpr hy.ne')
  simp only [bianchiFourierMode, Pi.smul_apply]
  rw [mul_left_cancel₀ hy' (hi.trans (mul_left_comm _ _ _))]
  ring1

/-- **The harmonic Fourier modes of moderate growth are the multiples of the Whittaker function**
(LMFDB `mf.bianchi.spaces`, `mf.bianchi.newform`): for `k ≥ 1` and `μ ≠ 0`, a Fourier mode
`ψ(μx) φ(y)` of weight `k`, with `φ` of class `C²` on `(0, ∞)` and of moderate growth, is harmonic
exactly when it is `φ₀(1) / W_k(u, 4π|μ|)₀` times `y W_k(u, 4π|μ|y) ψ(μx)`. -/
lemma isBianchiHarmonic_bianchiFourierMode_iff (hk : k ≠ 0) (hμ : μ ≠ 0)
    (hφ : ContDiffOn ℝ 2 φ (Ioi 0)) (hgrowth : ∃ (C : ℝ) (n : ℕ), ∀ y, 1 ≤ y → ‖φ y‖ ≤ C * y ^ n) :
    IsBianchiHarmonic k (bianchiFourierMode μ φ) ↔ bianchiFourierMode μ φ =
      (φ 1 0 / bianchiWhittakerVector k (μ / ‖μ‖) (4 * π * ‖μ‖) 0) • bianchiWhittakerFunction μ k :=
  ⟨bianchiFourierMode_eq_smul_bianchiWhittakerFunction hk hμ hφ hgrowth, fun h ↦ by
    rw [h]
    exact isBianchiHarmonic_smul_bianchiWhittakerFunction μ k hμ _⟩

variable {K : Type*} [Field K] [NumberField K] {σ : K →+* ℂ} {δ : ℂ} {a : 𝓞 K}

/-- **A harmonic Fourier mode of moderate growth is a term of the Fourier–Bessel expansion** (LMFDB
`mf.bianchi.spaces`, `mf.bianchi.newform`): for `k ≥ 1`, `δ` with `|δ| = √|Δ|` and
`0 ≠ α ∈ 𝒪_K`, a harmonic Fourier mode `ψ(μx) φ(y)` of frequency `μ = σ(α) / δ`, with `φ` of class
`C²` on `(0, ∞)` and of moderate growth, is the term `c(α) y W_k(u, 4π|α|y / √|Δ|) ψ(αx / δ)` of
the Fourier–Bessel expansion of weight `k` (`bianchiWhittakerTerm`, `HasBianchiWhittakerExpansion`)
with `c(α) = φ₀(1) / W_k(u, 4π|μ|)₀`. So, once the Fourier coefficients of a Bianchi cusp form of
weight `k` are known to be such Fourier modes, they are the terms of an expansion of this shape,
whose coefficients they determine. -/
lemma bianchiFourierMode_eq_bianchiWhittakerTerm (hk : k ≠ 0) (hδ : ‖δ‖ = √|(discr K : ℝ)|)
    (ha : a ≠ 0) (hφ : ContDiffOn ℝ 2 φ (Ioi 0))
    (hgrowth : ∃ (C : ℝ) (n : ℕ), ∀ y, 1 ≤ y → ‖φ y‖ ≤ C * y ^ n)
    (h : IsBianchiHarmonic k (bianchiFourierMode (σ a / δ) φ)) (z : HyperbolicThreeSpace) :
    bianchiFourierMode (σ a / δ) φ z = bianchiWhittakerTerm σ δ k (fun _ ↦ φ 1 0 /
      bianchiWhittakerVector k (σ a / δ / ‖σ a / δ‖) (4 * π * ‖σ a / δ‖) 0) z.coords a := by
  have hδ₀ : δ ≠ 0 := norm_ne_zero_iff.mp <| hδ ▸ (Real.sqrt_pos.mpr <| abs_pos.mpr <|
    Int.cast_ne_zero.mpr <| discr_ne_zero K).ne'
  have hμ : (σ a : ℂ) / δ ≠ 0 :=
    div_ne_zero ((map_ne_zero σ).mpr (RingOfIntegers.coe_ne_zero_iff.mpr ha)) hδ₀
  rw [bianchiWhittakerTerm_coords k σ δ _ a hδ z,
    bianchiFourierMode_eq_smul_bianchiWhittakerFunction hk hμ hφ hgrowth h, Pi.smul_apply]

end HyperbolicThreeSpace
