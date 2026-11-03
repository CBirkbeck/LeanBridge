import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.MainLemma
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.ReductionTheory
import Mathlib.Algebra.Module.ZLattice.Summable

/-!
# Bounds for cuspidal functions

Let `K` be an imaginary quadratic field, embedded in `ℂ` by `σ`, and `H` a cuspidal function
(`HyperbolicThreeSpace.IsBianchiCuspFunction`) of even weight `k ≥ 1`, periodic for `σ(𝒪_K)`. Then
`H` has a Fourier–Bessel expansion
(`HyperbolicThreeSpace.IsBianchiCuspFunction.hasBianchiWhittakerExpansion`)
`H(x, y) = ∑_{α ≠ 0} c(α) y W_k(u, 4π|μ|y) ψ(μx)`, `μ = σ(α) / √Δ`, and for `y` bounded below the
exponential decay of the `K`-Bessel functions bounds `y^k ⟨H, H⟩_k` in terms of a bound for the
`c(α)`. This gives:

* the invariant norm `y^k ⟨H, H⟩_k` is bounded above any height
  (`HyperbolicThreeSpace.IsBianchiCuspFunction.exists_bianchiNormSq_le`), the coefficients being
  bounded by the size of `H` at one height, as `K_{k/2}(t) ≥ e^{-5t/4} / 2`;
* a **Sturm bound** (`HyperbolicThreeSpace.exists_bianchiNormSq_le_half`): if `y^k ⟨H, H⟩_k ≤ M` on
  `ℋ₃`, then `|c(α)| ≤ |μ|^{k/2+1} √M / K_{k/2}(4π)`, by the Fourier coefficient at height
  `1 / |μ|`, and so if `c(α) = 0` for `|σ(α)| ≤ B`, with `B` only depending on `K`, `k` and `y₁`,
  then `y^k ⟨H, H⟩_k ≤ M / 2` at height at least `y₁`.

## Main results

* `Complex.norm_besselK_le_of_le`: the exponential decay of `K_ν`.
* `Complex.exp_le_norm_besselK`: the lower bound of `K_r`, `r ≥ 1`.
* `HyperbolicThreeSpace.summable_exp_neg_mul_norm`: the series `∑_{α ≠ 0} e^{-b|σ(α)|}` converges.
* `HyperbolicThreeSpace.IsBianchiCuspFunction.hasBianchiWhittakerExpansion`: the Fourier–Bessel
  expansion of a periodic cuspidal function.
* `HyperbolicThreeSpace.IsBianchiCuspFunction.exists_bianchiNormSq_le`: its invariant norm is
  bounded above any height.
* `HyperbolicThreeSpace.height_pow_mul_norm_smul_le`,
  `HyperbolicThreeSpace.height_pow_mul_norm_le_of_hasSum`: the estimates of the terms of a
  Fourier–Bessel series and of its sum.
* `HyperbolicThreeSpace.exists_bianchiNormSq_le_half`: the Sturm bound.
-/

open MeasureTheory Set Real

namespace Complex

variable (ν : ℂ) {x x₀ : ℝ}

/-- **The exponential decay of `K_ν`**: for `0 < x₀ ≤ x`,
`|K_ν(x)| ≤ e^{-(x - x₀)} · ½ ∫₀^∞ |t^(ν - 1) e^(-x₀(t + 1/t)/2)| dt`, as `t + 1/t ≥ 2`. -/
lemma norm_besselK_le_of_le (hx₀ : 0 < x₀) (hx : x₀ ≤ x) :
    ‖besselK ν x‖ ≤ rexp (-(x - x₀)) * (2⁻¹ * ∫ t in Ioi 0, ‖besselKIntegrand ν x₀ t‖) := by
  have hint : Integrable (fun t ↦ ‖besselKIntegrand ν x₀ t‖) (volume.restrict (Ioi 0)) :=
    (integrableOn_besselKIntegrand ν hx₀).norm
  have h : ‖∫ t in Ioi 0, besselKIntegrand ν x t‖ ≤
      ∫ t in Ioi 0, rexp (-(x - x₀)) * ‖besselKIntegrand ν x₀ t‖ := by
    refine norm_integral_le_of_norm_le (hint.const_mul _) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t (ht : 0 < t) ↦ ?_)
    rw [norm_besselKIntegrand ν ht, norm_besselKIntegrand ν ht, ← mul_assoc,
      mul_comm (rexp _), mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (rpow_nonneg ht.le _)
    have h2 : 2 ≤ t + t⁻¹ := by
      have e : t + t⁻¹ - 2 = (t - 1) ^ 2 / t := by
        field_simp
        ring1
      have hq : 0 ≤ (t - 1) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
      linarith
    nlinarith
  rw [besselK, norm_mul, integral_const_mul] at *
  simp only [norm_inv, RCLike.norm_ofNat] at *
  nlinarith [norm_nonneg (∫ t in Ioi 0, besselKIntegrand ν x t), exp_pos (-(x - x₀))]

/-- **The lower bound of `K_r`**: for `r ≥ 1` and `x > 0`, `|K_r(x)| ≥ e^{-5x/4} / 2`, by the
integrand of `K_r(x)` on `[1, 2]`, where `t^{r-1} ≥ 1` and `t + 1/t ≤ 5/2`. -/
lemma exp_le_norm_besselK {r : ℝ} (hr : 1 ≤ r) (hx : 0 < x) :
    2⁻¹ * rexp (-(5 / 4 * x)) ≤ ‖besselK (r : ℂ) x‖ := by
  have h : ∀ t ∈ Ioi (0 : ℝ), besselKIntegrand (r : ℂ) x t =
      ((t ^ (r - 1) * rexp (-(x / 2) * (t + t⁻¹)) : ℝ) : ℂ) := by
    intro t ht
    rw [besselKIntegrand, ofReal_mul, ofReal_cpow (mem_Ioi.mp ht).le, ofReal_sub, ofReal_one]
  have hint : IntegrableOn (fun t : ℝ ↦ t ^ (r - 1) * rexp (-(x / 2) * (t + t⁻¹))) (Ioi 0) :=
    IntegrableOn.congr_fun (f := fun t ↦ ‖besselKIntegrand (r : ℂ) x t‖)
      (integrableOn_besselKIntegrand (r : ℂ) hx).norm
      (fun t ht ↦ by
        simp only
        rw [norm_besselKIntegrand _ (mem_Ioi.mp ht), ofReal_re]) measurableSet_Ioi
  have hnn (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : 0 ≤ t ^ (r - 1) * rexp (-(x / 2) * (t + t⁻¹)) :=
    mul_nonneg (rpow_nonneg (mem_Ioi.mp ht).le _) (exp_pos _).le
  have hsub : Ioc (1 : ℝ) 2 ⊆ Ioi 0 := fun t ht ↦ zero_lt_one.trans ht.1
  have hlow : rexp (-(5 / 4 * x)) ≤ ∫ t in Ioi 0, t ^ (r - 1) * rexp (-(x / 2) * (t + t⁻¹)) := by
    have h₁ : ∫ t in Ioc (1 : ℝ) 2, t ^ (r - 1) * rexp (-(x / 2) * (t + t⁻¹)) ≤
        ∫ t in Ioi 0, t ^ (r - 1) * rexp (-(x / 2) * (t + t⁻¹)) :=
      setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall hnn))
        (.of_forall hsub)
    refine le_trans ?_ h₁
    have h₂ : ∫ t in Ioc (1 : ℝ) 2, rexp (-(5 / 4 * x)) = rexp (-(5 / 4 * x)) := by
      norm_num
    rw [← h₂]
    refine setIntegral_mono_on (by simp) (hint.mono_set hsub) measurableSet_Ioc fun t ht ↦ ?_
    have ht₀ : 0 < t := zero_lt_one.trans ht.1
    have h₃ : 1 ≤ t ^ (r - 1) := one_le_rpow ht.1.le (by linarith)
    have h₄ : t + t⁻¹ ≤ 5 / 2 := by
      have h₅ : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht.1.le
      have h₆ : t * t⁻¹ = 1 := mul_inv_cancel₀ ht₀.ne'
      nlinarith [ht.1, ht.2]
    have h₇ : rexp (-(5 / 4 * x)) ≤ rexp (-(x / 2) * (t + t⁻¹)) := exp_le_exp.mpr (by nlinarith)
    exact h₇.trans (le_mul_of_one_le_left (exp_pos _).le h₃)
  rw [besselK, setIntegral_congr_fun measurableSet_Ioi h, integral_complex_ofReal, norm_mul,
    norm_real, norm_inv, RCLike.norm_ofNat]
  exact mul_le_mul_of_nonneg_left (hlow.trans (Real.le_norm_self _)) (by norm_num)

end Complex

open Complex Matrix Module NumberField HilbertModularGroup

open scoped ComplexConjugate MatrixGroups nonZeroDivisors

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] {σ : K →+* ℂ} {δ : ℂ} {x : K} {k : ℕ} {u : ℂ} {μ : ℂ} {t t₀ : ℝ}
  {H : HyperbolicThreeSpace → Fin (k + 1) → ℂ} {c : 𝓞 K → ℂ}

lemma one_le_div_two (hk' : Even k) (hk : k ≠ 0) : (1 : ℝ) ≤ (k : ℝ) / 2 := by
  have h : 2 ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hk'.two_dvd
  have h' : (2 : ℝ) ≤ k := by
    exact_mod_cast h
  linarith

variable (k t) in
lemma norm_bianchiWhittakerVector_apply (hu : ‖u‖ = 1) (j : Fin (k + 1)) :
    ‖bianchiWhittakerVector k u t j‖ = ‖besselK ((j : ℕ) - (k : ℂ) / 2) t‖ := by
  rw [bianchiWhittakerVector, norm_mul, norm_zpow, norm_mul, norm_I, one_mul, hu]
  simp

variable (k) in
lemma norm_bianchiWhittakerVector_le (hu : ‖u‖ = 1) (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    ‖bianchiWhittakerVector k u t‖ ≤ rexp (-(t - t₀)) *
      ∑ j : Fin (k + 1), (2⁻¹ * ∫ s in Ioi 0, ‖besselKIntegrand ((j : ℕ) - (k : ℂ) / 2) t₀ s‖) := by
  have hnn (j : Fin (k + 1)) :
      0 ≤ 2⁻¹ * ∫ s in Ioi 0, ‖besselKIntegrand ((j : ℕ) - (k : ℂ) / 2) t₀ s‖ :=
    mul_nonneg (by norm_num) (integral_nonneg fun _ ↦ norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (exp_pos _).le
    (Finset.sum_nonneg fun j _ ↦ hnn j))).mpr fun j ↦ ?_
  rw [norm_bianchiWhittakerVector_apply k _ hu]
  refine (norm_besselK_le_of_le _ ht₀ ht).trans (mul_le_mul_of_nonneg_left ?_ (exp_pos _).le)
  exact Finset.single_le_sum (f := fun j : Fin (k + 1) ↦
    2⁻¹ * ∫ s in Ioi 0, ‖besselKIntegrand ((j : ℕ) - (k : ℂ) / 2) t₀ s‖) (fun j _ ↦ hnn j)
      (Finset.mem_univ j)

variable (μ k) in
lemma norm_bianchiWhittakerFunction (z : HyperbolicThreeSpace) : ‖bianchiWhittakerFunction μ k z‖ =
    z.height * ‖bianchiWhittakerVector k (μ / ‖μ‖) (4 * π * ‖μ‖ * z.height)‖ := by
  have hre : (2 * π * I * (μ * z.coords.1 + conj (μ * z.coords.1))).re = 0 := by
    rw [add_conj]
    simp
  rw [bianchiWhittakerFunction, norm_smul, norm_mul, norm_exp, hre, Real.exp_zero, mul_one,
    norm_real, Real.norm_of_nonneg (coords_snd_pos z).le]
  rfl

variable (K) in
/-- The subgroup of the unipotent upper triangular matrices `(1, a; 0, 1)` of `GL₂(𝒪_K)`. -/
def glUnipotents : Subgroup (GL (Fin 2) (𝓞 K)) where
  carrier := range glUpper
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a + b, Units.ext ?_⟩
    rw [Units.val_mul, coe_glUpper, coe_glUpper, coe_glUpper]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]
  one_mem' := ⟨0, Units.ext <| by
    rw [coe_glUpper]
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨-a, inv_eq_of_mul_eq_one_right (Units.ext ?_) |>.symm⟩
    rw [Units.val_mul, coe_glUpper, coe_glUpper, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

lemma exists_mem_glUnipotents (a : 𝓞 K) :
    ∃ γ ∈ glUnipotents K, (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![1, a; 0, 1] :=
  ⟨glUpper a, ⟨a, rfl⟩, rfl⟩

lemma extend_glSlash_glUpper (a : 𝓞 K) {p : ℂ × ℝ} (hp : 0 < p.2) :
    extend (glSlash σ k (glUpper a) H) p = extend H (p.1 + σ a, p.2) := by
  have h : GeneralLinearGroup.map (algebraMap (𝓞 K) K) (glUpper a) =
      heckeUpper 1 (algebraMap (𝓞 K) K a) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heckeUpper, coe_glUpper]
  rw [glSlash, h, extend_bianchiGLSlash_heckeUpper_one _ hp]

lemma IsBianchiCuspFunction.isBianchiModularForm (hk : Even k) (hH : IsBianchiCuspFunction σ k H)
    (hper : ∀ a : 𝓞 K, glSlash σ k (glUpper a) H = H) :
    IsBianchiModularForm σ (glUnipotents K) k H where
  analyticAt := hH.analyticAt
  invariant := isBianchiSlashInvariant_of_glSlash_eq hk <| by
    rintro _ ⟨a, rfl⟩
    exact hper a
  harmonic := hH.harmonic
  growth := hH.growth

lemma extend_add_eq_of_glSlash_glUpper_eq (hper : ∀ a : 𝓞 K, glSlash σ k (glUpper a) H = H) {y : ℝ}
    (hy : 0 < y) {l : ℂ} (hl : l ∈ bianchiScaledLattice σ 1) (w : ℂ) :
    extend H (l + w, y) = extend H (w, y) := by
  rcases mem_bianchiScaledLattice.mp hl with ⟨a, rfl⟩
  have h : extend (glSlash σ k (glUpper a) H) (w, y) = extend H ((w, y).1 + σ a, (w, y).2) :=
    extend_glSlash_glUpper a hy
  rw [hper] at h
  rw [one_mul, add_comm (σ a) w]
  exact h.symm

lemma norm_bianchiFourierCoeff_le_of_forall {P : Set ℂ} (hPb : Bornology.IsBounded P) {y A : ℝ}
    (hA : ∀ w : ℂ, ‖extend H (w, y)‖ ≤ A) : ‖bianchiFourierCoeff P μ H y‖ ≤ A := by
  have hA₀ : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hI : ‖∫ w in P, cexp (-(2 * π * I * (μ * w + conj (μ * w)))) • extend H (w, y)‖ ≤
      A * volume.real P :=
    norm_setIntegral_le_of_norm_le_const hPb.measure_lt_top fun w _ ↦ by
      have hre : (-(2 * π * I * (μ * w + conj (μ * w)))).re = 0 := by
        rw [add_conj]
        simp
      rw [norm_smul, Complex.norm_exp, hre, Real.exp_zero, one_mul]
      exact hA w
  rw [bianchiFourierCoeff, norm_smul, norm_inv, norm_real, Real.norm_of_nonneg measureReal_nonneg]
  rcases measureReal_nonneg.eq_or_lt with h₀ | h₀
  · rw [← h₀]
    simpa using hA₀
  · rw [inv_mul_le_iff₀ h₀]
    linarith

lemma bianchiNormSq_le_of_even (hk : Even k) (z : HyperbolicThreeSpace) :
    bianchiNormSq H z ≤ 2 ^ k * (z.height ^ (k / 2) * ‖H z‖) ^ 2 := by
  have hsum : ∑ i : Fin (k + 1), (k.choose i : ℝ) = 2 ^ k := by
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ (k.choose i : ℝ)) (k + 1)]
    exact_mod_cast Nat.sum_range_choose k
  have hy : z.height ^ k = (z.height ^ (k / 2)) ^ 2 := by
    rw [← pow_mul, Nat.div_two_mul_two_of_even hk]
  have h₁ : ∑ i : Fin (k + 1), (k.choose i : ℝ) * ‖H z i‖ ^ 2 ≤ 2 ^ k * ‖H z‖ ^ 2 := by
    rw [← hsum, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm _ i) 2) (Nat.cast_nonneg _)
  rw [bianchiNormSq, mul_pow, ← hy]
  nlinarith [mul_le_mul_of_nonneg_left h₁ (pow_nonneg z.height_pos.le k)]

lemma norm_extend_le_of_bianchiNormSq_le {M : ℝ} (hM : ∀ z, bianchiNormSq H z ≤ M) (hk : Even k)
    {y : ℝ} (hy : 0 < y) (w : ℂ) : ‖extend H (w, y)‖ ≤ (y ^ (k / 2))⁻¹ * √M := by
  have hy' : 0 < y ^ (k / 2) := pow_pos hy _
  rw [extend, dite_eq_left hy]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j ↦ ?_
  rw [le_inv_mul_iff₀ hy']
  have h₁ : (.mk (WithLp.toLp 2 (w, y)) hy : HyperbolicThreeSpace).height ^ k *
      ‖H (.mk (WithLp.toLp 2 (w, y)) hy) j‖ ^ 2 ≤ M :=
    (sq_norm_apply_le_bianchiNormSq H (.mk (WithLp.toLp 2 (w, y)) hy) j).trans (hM _)
  have hy₂ : y ^ k = (y ^ (k / 2)) ^ 2 := by
    rw [← pow_mul, Nat.div_two_mul_two_of_even hk]
  have h₂ : (y ^ (k / 2) * ‖H (.mk (WithLp.toLp 2 (w, y)) hy) j‖) ^ 2 ≤ M := by
    rw [mul_pow, ← hy₂]
    exact h₁
  exact (le_abs_self _).trans (Real.abs_le_sqrt h₂)

variable (k) in
/-- The constant of the estimate of a term of a Fourier–Bessel series
(`height_pow_mul_norm_smul_le`), for frequencies `μ` and heights `y` with `4π|μ|y ≥ t₁`. -/
noncomputable def bianchiTailConstant (t₁ : ℝ) : ℝ :=
  rexp t₁ *
    (∑ j : Fin (k + 1), (2⁻¹ * ∫ s in Ioi 0, ‖besselKIntegrand ((j : ℕ) - (k : ℂ) / 2) t₁ s‖)) *
    ((k / 2 + 1).factorial / (3 / 4 * π) ^ (k / 2 + 1))

lemma bianchiTailConstant_nonneg (t₁ : ℝ) : 0 ≤ bianchiTailConstant k t₁ := by
  have hnn (j : Fin (k + 1)) :
      0 ≤ 2⁻¹ * ∫ s in Ioi 0, ‖besselKIntegrand ((j : ℕ) - (k : ℂ) / 2) t₁ s‖ :=
    mul_nonneg (by norm_num) (integral_nonneg fun _ ↦ norm_nonneg _)
  have h₁ : 0 ≤ ∑ j : Fin (k + 1),
      (2⁻¹ * ∫ s in Ioi 0, ‖besselKIntegrand ((j : ℕ) - (k : ℂ) / 2) t₁ s‖) :=
    Finset.sum_nonneg fun j _ ↦ hnn j
  rw [bianchiTailConstant]
  positivity

/-- **The estimate of a term of a Fourier–Bessel series**: for `μ ≠ 0`, `0 < t₁ ≤ 4π|μ|y₁`, and a
coefficient `|a| ≤ E |μ|^{k/2+1} e^{(5/2)π|μ|y₁}`, one has
`y^{k/2} |a y W_k(u, 4π|μ|y)| ≤ E C e^{-(3/4)π|μ|y₁}` at height `y ≥ y₁`, with `C` only depending on
`k` and `t₁`. -/
lemma height_pow_mul_norm_smul_le {y₁ t₁ E : ℝ} (hμ : μ ≠ 0) (ht₁ : 0 < t₁)
    (ht₁' : t₁ ≤ 4 * π * ‖μ‖ * y₁) (hE : 0 ≤ E) {a : ℂ}
    (ha : ‖a‖ ≤ E * ‖μ‖ ^ (k / 2 + 1) * rexp (5 / 2 * π * ‖μ‖ * y₁)) {z : HyperbolicThreeSpace}
    (hz : y₁ ≤ z.height) : z.height ^ (k / 2) * ‖a • bianchiWhittakerFunction μ k z‖ ≤
      E * bianchiTailConstant k t₁ * rexp (-(3 / 4 * π * ‖μ‖ * y₁)) := by
  have hs : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
  have hy : 0 < z.height := z.height_pos
  have hu : ‖μ / ‖μ‖‖ = 1 := norm_div_norm_eq_one hμ
  have ht : t₁ ≤ 4 * π * ‖μ‖ * z.height := ht₁'.trans <|
    mul_le_mul_of_nonneg_left hz (by positivity)
  have hW : ‖bianchiWhittakerVector k (μ / ‖μ‖) (4 * π * ‖μ‖ * z.height)‖ ≤
      rexp (-(4 * π * ‖μ‖ * z.height - t₁)) * ∑ j : Fin (k + 1),
        2⁻¹ * ∫ s in Set.Ioi 0, ‖besselKIntegrand ((j : ℕ) - (k : ℂ) / 2) t₁ s‖ :=
    norm_bianchiWhittakerVector_le k hu ht₁ ht
  have hA₀ : 0 ≤ ∑ j : Fin (k + 1),
      (2⁻¹ * ∫ s in Ioi 0, ‖besselKIntegrand ((j : ℕ) - (k : ℂ) / 2) t₁ s‖) :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (by norm_num) (integral_nonneg fun _ ↦ norm_nonneg _)
  rw [bianchiTailConstant]
  generalize (∑ j : Fin (k + 1),
    (2⁻¹ * ∫ s in Ioi 0, ‖besselKIntegrand ((j : ℕ) - (k : ℂ) / 2) t₁ s‖)) = A₀ at hW hA₀ ⊢
  have h₁ : ‖a • bianchiWhittakerFunction μ k z‖ ≤ (E * ‖μ‖ ^ (k / 2 + 1) *
      rexp (5 / 2 * π * ‖μ‖ * y₁)) * (z.height * (rexp (-(4 * π * ‖μ‖ * z.height - t₁)) * A₀)) := by
    rw [norm_smul, norm_bianchiWhittakerFunction]
    gcongr
  have hD : (‖μ‖ * z.height) ^ (k / 2 + 1) * rexp (-(3 / 4 * π * ‖μ‖ * z.height)) ≤
      (k / 2 + 1).factorial / (3 / 4 * π) ^ (k / 2 + 1) := by
    have h₂ : (3 / 4 * π * ‖μ‖ * z.height) ^ (k / 2 + 1) / (k / 2 + 1).factorial ≤
        rexp (3 / 4 * π * ‖μ‖ * z.height) :=
      Real.pow_div_factorial_le_exp _ (by positivity) _
    have e : 3 / 4 * π * ‖μ‖ * z.height = 3 / 4 * π * (‖μ‖ * z.height) := by
      ring1
    rw [e, mul_pow, div_le_iff₀ (by positivity)] at h₂
    rw [e, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _), div_mul_eq_mul_div,
      le_div_iff₀ (by positivity)]
    linarith
  have hexp : rexp (5 / 2 * π * ‖μ‖ * y₁) * rexp (-(4 * π * ‖μ‖ * z.height - t₁)) ≤
      rexp t₁ * (rexp (-(3 / 4 * π * ‖μ‖ * z.height)) * rexp (-(3 / 4 * π * ‖μ‖ * y₁))) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    refine exp_le_exp.mpr ?_
    have h₃ : ‖μ‖ * y₁ ≤ ‖μ‖ * z.height := mul_le_mul_of_nonneg_left hz hs.le
    have hπ : 0 < π := Real.pi_pos
    nlinarith
  have e₁ : z.height ^ (k / 2) * ((E * ‖μ‖ ^ (k / 2 + 1) * rexp (5 / 2 * π * ‖μ‖ * y₁)) *
      (z.height * (rexp (-(4 * π * ‖μ‖ * z.height - t₁)) * A₀))) =
        E * A₀ * (‖μ‖ * z.height) ^ (k / 2 + 1) *
          (rexp (5 / 2 * π * ‖μ‖ * y₁) * rexp (-(4 * π * ‖μ‖ * z.height - t₁))) := by
    rw [mul_pow, pow_succ z.height]
    ring1
  have e₂ : E * (rexp t₁ * A₀ * ((k / 2 + 1).factorial / (3 / 4 * π) ^ (k / 2 + 1))) *
      rexp (-(3 / 4 * π * ‖μ‖ * y₁)) = E * A₀ * rexp t₁ *
        ((k / 2 + 1).factorial / (3 / 4 * π) ^ (k / 2 + 1)) * rexp (-(3 / 4 * π * ‖μ‖ * y₁)) := by
    ring1
  refine (mul_le_mul_of_nonneg_left h₁ (pow_nonneg hy.le _)).trans ?_
  rw [e₁, e₂]
  have h₄ : (‖μ‖ * z.height) ^ (k / 2 + 1) * (rexp (5 / 2 * π * ‖μ‖ * y₁) *
      rexp (-(4 * π * ‖μ‖ * z.height - t₁))) ≤
        rexp t₁ * ((k / 2 + 1).factorial / (3 / 4 * π) ^ (k / 2 + 1)) *
          rexp (-(3 / 4 * π * ‖μ‖ * y₁)) := by
    refine (mul_le_mul_of_nonneg_left hexp (by positivity)).trans ?_
    have e₃ : (‖μ‖ * z.height) ^ (k / 2 + 1) * (rexp t₁ * (rexp (-(3 / 4 * π * ‖μ‖ * z.height)) *
        rexp (-(3 / 4 * π * ‖μ‖ * y₁)))) = rexp t₁ * ((‖μ‖ * z.height) ^ (k / 2 + 1) *
          rexp (-(3 / 4 * π * ‖μ‖ * z.height))) * rexp (-(3 / 4 * π * ‖μ‖ * y₁)) := by
      ring1
    rw [e₃]
    gcongr
  have h₅ : E * A₀ * ((‖μ‖ * z.height) ^ (k / 2 + 1) * (rexp (5 / 2 * π * ‖μ‖ * y₁) *
      rexp (-(4 * π * ‖μ‖ * z.height - t₁)))) ≤ E * A₀ * (rexp t₁ *
        ((k / 2 + 1).factorial / (3 / 4 * π) ^ (k / 2 + 1)) * rexp (-(3 / 4 * π * ‖μ‖ * y₁))) :=
    mul_le_mul_of_nonneg_left h₄ (mul_nonneg hE hA₀)
  linarith

variable [NumberField K]

lemma summable_norm_rpow_apply (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) {r : ℝ} (hr : r < -2) :
    Summable fun α : {α : 𝓞 K // α ≠ 0} ↦ ‖σ α.1‖ ^ r := by
  let L : Submodule ℤ ℂ := Submodule.span ℤ (range (integralLatticeBasis σ hK hx))
  have hrank : finrank ℤ L = 2 := by
    rw [ZLattice.rank ℝ L, Complex.finrank_real_complex]
  have hr' : r < -(finrank ℤ L : ℝ) := by
    rw [hrank]
    exact_mod_cast hr
  have hs : Summable fun z : L ↦ ‖z‖ ^ r := ZLattice.summable_norm_rpow L r hr'
  let f : {α : 𝓞 K // α ≠ 0} → L :=
    fun α ↦ ⟨σ α.1, map_mem_span_integralLatticeBasis hK hx α.1⟩
  have hf : Function.Injective f := fun α β h ↦ Subtype.ext <| RingOfIntegers.coe_injective <|
    σ.injective (congrArg Subtype.val h)
  have e (α : {α : 𝓞 K // α ≠ 0}) : ‖f α‖ = ‖σ α.1‖ := rfl
  simpa only [Function.comp_def, e] using hs.comp_injective hf

/-- **The series `∑_{α ≠ 0} e^{-b|σ(α)|}` converges**, for `b > 0` and a quadratic field `K`
embedded in `ℂ` by `σ` with `σ(K) ⊄ ℝ`, since `σ(𝒪_K)` is a lattice in `ℂ`. -/
lemma summable_exp_neg_mul_norm (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) {b : ℝ} (hb : 0 < b) :
    Summable fun α : {α : 𝓞 K // α ≠ 0} ↦ rexp (-(b * ‖σ α.1‖)) := by
  refine Summable.of_nonneg_of_le (fun _ ↦ (exp_pos _).le) (fun α ↦ ?_)
    ((summable_norm_rpow_apply hK hx (by norm_num : (-3 : ℝ) < -2)).mul_left (6 / b ^ 3))
  have hα : 0 < ‖σ α.1‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr
    (RingOfIntegers.coe_ne_zero_iff.mpr α.2))
  have h₁ : (b * ‖σ α.1‖) ^ 3 / (3 : ℕ).factorial ≤ rexp (b * ‖σ α.1‖) :=
    Real.pow_div_factorial_le_exp _ (by positivity) 3
  have h₂ : rexp (-(b * ‖σ α.1‖)) ≤ 6 / (b * ‖σ α.1‖) ^ 3 := by
    rw [Real.exp_neg, inv_le_comm₀ (exp_pos _) (by positivity)]
    refine le_trans (le_of_eq ?_) h₁
    simp [Nat.factorial]
  refine h₂.trans_eq ?_
  rw [Real.rpow_neg hα.le, Real.rpow_ofNat, mul_pow]
  field_simp

/-- **The sum of the estimates of the terms of a Fourier–Bessel series.** -/
lemma height_pow_mul_norm_le_of_hasSum (hδ : ‖δ‖ = √|(discr K : ℝ)|)
    (hc : HasBianchiWhittakerExpansion σ δ k (extend H) c) {y₁ t₁ E b : ℝ} (ht₁ : 0 < t₁)
    (hν : ∀ α : 𝓞 K, α ≠ 0 → σ (α : K) / δ ≠ 0)
    (ht₁' : ∀ α : 𝓞 K, α ≠ 0 → t₁ ≤ 4 * π * ‖σ α / δ‖ * y₁) (hE : 0 ≤ E) (hcE : ∀ α : 𝓞 K, α ≠ 0 →
      ‖c α‖ ≤ E * ‖σ α / δ‖ ^ (k / 2 + 1) * rexp (5 / 2 * π * ‖σ α / δ‖ * y₁))
    {g : {α : 𝓞 K // α ≠ 0} → ℝ} (hg : HasSum g b) (hg₀ : ∀ α, 0 ≤ g α)
    (hgc : ∀ α : {α : 𝓞 K // α ≠ 0}, c α = 0 ∨ rexp (-(3 / 4 * π * ‖σ α.1 / δ‖ * y₁)) ≤ g α)
    {z : HyperbolicThreeSpace} (hz : y₁ ≤ z.height) :
    z.height ^ (k / 2) * ‖H z‖ ≤ E * bianchiTailConstant k t₁ * b := by
  have hT : 0 ≤ E * bianchiTailConstant k t₁ := mul_nonneg hE (bianchiTailConstant_nonneg _)
  have h₁ : HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦ bianchiWhittakerTerm σ δ k c z.coords α)
      (extend H z.coords) := hc z.coords (coords_snd_pos z)
  rw [extend_coords] at h₁
  simp only [bianchiWhittakerTerm_coords k σ δ c _ hδ z] at h₁
  have h₂ : ‖(z.height ^ (k / 2) : ℝ) • H z‖ ≤ E * bianchiTailConstant k t₁ * b :=
    (h₁.const_smul (z.height ^ (k / 2) : ℝ)).norm_le_of_bounded (hg.mul_left _) fun α ↦ by
      rw [norm_smul, Real.norm_of_nonneg (pow_nonneg z.height_pos.le _)]
      rcases hgc α with h₀ | hle
      · rw [h₀, zero_smul, norm_zero, mul_zero]
        exact mul_nonneg hT (hg₀ α)
      · exact (height_pow_mul_norm_smul_le (hν α α.2) ht₁ (ht₁' α α.2) hE (hcE α α.2) hz).trans
          (mul_le_mul_of_nonneg_left hle hT)
  rwa [norm_smul, Real.norm_of_nonneg (pow_nonneg z.height_pos.le _)] at h₂

lemma summable_exp_neg_norm_div (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) (hδ₀ : δ ≠ 0) {y₁ : ℝ}
    (hy₁ : 0 < y₁) :
    Summable fun α : {α : 𝓞 K // α ≠ 0} ↦ rexp (-(3 / 4 * π * ‖σ α.1 / δ‖ * y₁)) := by
  have hδ' : 0 < ‖δ‖ := norm_pos_iff.mpr hδ₀
  refine (summable_exp_neg_mul_norm hK hx (b := 3 / 4 * π * y₁ / ‖δ‖) (by positivity)).congr
    fun α ↦ ?_
  rw [norm_div]
  congr 2
  field_simp

lemma IsBianchiCuspFunction.exists_norm_extend_le (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hH : IsBianchiCuspFunction σ k H) (hper : ∀ a : 𝓞 K, glSlash σ k (glUpper a) H = H) {y : ℝ}
    (hy : 0 < y) : ∃ C : ℝ, ∀ w : ℂ, ‖extend H (w, y)‖ ≤ C := by
  have hc : Continuous fun w ↦ extend H (w, y) := continuous_extend_mk hH.analyticAt hy
  rcases ((ZSpan.fundamentalDomain_isBounded (integralLatticeBasis σ hK hx)).isCompact_closure
    ).exists_bound_of_continuousOn hc.continuousOn with ⟨C, hC⟩
  refine ⟨C, fun w ↦ ?_⟩
  rcases ZSpan.exist_unique_vadd_mem_fundamentalDomain (integralLatticeBasis σ hK hx) w with
    ⟨v, hv, -⟩
  rw [← extend_add_eq_of_glSlash_glUpper_eq hper hy (coe_mem_bianchiScaledLattice_one hK hx v) w]
  exact hC _ (subset_closure hv)

variable [IsTotallyComplex K]

lemma IsBianchiCuspFunction.setIntegral_extend_eq_zero (hK : finrank ℚ K = 2)
    (hH : IsBianchiCuspFunction σ k H) (hper : ∀ a : 𝓞 K, glSlash σ k (glUpper a) H = H) {y : ℝ}
    (hy : 0 < y) {P : Set ℂ} (hP : IsAddFundamentalDomain (bianchiScaledLattice σ 1) P volume) :
    ∫ w in P, extend H (w, y) = 0 := by
  rcases hH.constantTerm 1 with ⟨t, ht, hp, hz⟩
  have hsec (w : ℂ) : bianchiCuspSection σ k H 1 w y = extend H (w, y) := by
    simp [bianchiCuspSection, bianchiSlash_one]
  have hc : Continuous fun w ↦ extend H (w, y) := continuous_extend_mk hH.analyticAt hy
  have hper₂ : ∀ l ∈ bianchiScaledLattice σ t, ∀ w, extend H (l + w, y) = extend H (w, y) := by
    simpa only [hsec] using hp y hy
  have h₀ : ∀ P, IsAddFundamentalDomain (bianchiScaledLattice σ t) P volume →
      ∫ w in P, extend H (w, y) = 0 := by
    simpa only [hsec] using fun P hP ↦ hz y P hy hP
  rcases exists_mul_eq_mul ht one_ne_zero with ⟨w₁, w₂, hw₁, hw₂, he⟩
  rcases exists_isBounded_isAddFundamentalDomain_bianchiScaledLattice (σ := σ) hK (t := t * w₁)
    (mul_ne_zero ht (RingOfIntegers.coe_ne_zero_iff.mpr hw₁)) with ⟨P', -, hP'⟩
  have h₁ : ∫ w in P', extend H (w, y) = 0 := setIntegral_eq_zero_of_mul hK ht hw₁ hc hper₂ hP' h₀
  rw [he] at hP'
  exact setIntegral_eq_zero_of_mul_eq_zero hK one_ne_zero hw₂ hc
    (fun l hl w ↦ extend_add_eq_of_glSlash_glUpper_eq hper hy hl w) hP hP' h₁

/-- **The Fourier–Bessel expansion of a periodic cuspidal function**: for a quadratic field `K`
embedded in `ℂ` by `σ` with `σ(K) ⊄ ℝ` and `δ² = Δ`, a cuspidal function `H` of even weight
`k ≥ 1`, periodic for `σ(𝒪_K)`, is the sum of its Fourier–Bessel series, whose coefficients are its
normalised Fourier coefficients. -/
lemma IsBianchiCuspFunction.hasBianchiWhittakerExpansion (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hk' : Even k) (hk : k ≠ 0) (hδ : δ ^ 2 = discr K) (hH : IsBianchiCuspFunction σ k H)
    (hper : ∀ a : 𝓞 K, glSlash σ k (glUpper a) H = H) :
    HasBianchiWhittakerExpansion σ δ k (extend H) fun α ↦
      bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) (σ α / δ) H 1 0 /
        bianchiWhittakerVector k (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ α / δ‖) 0 := by
  have hF : IsBianchiModularForm σ (glUnipotents K) k H := hH.isBianchiModularForm hk' hper
  have hP : IsAddFundamentalDomain (bianchiScaledLattice σ 1)
      (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) volume :=
    isAddFundamentalDomain_bianchiScaledLattice_one hK hx
  refine hF.hasBianchiWhittakerExpansion_of_finrank_eq_two hK hx exists_mem_glUnipotents hk hδ
    fun z ↦ ?_
  let m : ℂ → Fin (k + 1) → ℂ := fun ν ↦ bianchiFourierMode ν
    (bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) ν H) z
  have h₀ : m 0 = 0 := by
    have h₁ : bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) 0 H
        z.coords.2 = 0 := by
      simp [bianchiFourierCoeff, hH.setIntegral_extend_eq_zero hK hper (coords_snd_pos z) hP]
    simp only [m, bianchiFourierMode, h₁, smul_zero]
  let S : Set ℂ := {ν | ∀ l ∈ Submodule.span ℤ (range (integralLatticeBasis σ hK hx)),
    cexp (2 * π * I * (ν * l + conj (ν * l))) = 1}
  let T : Set ℂ := {ν | ν ≠ 0 ∧ ν ∈ S}
  have hind : T.indicator m = S.indicator m := by
    funext ν
    by_cases hS : ν ∈ S
    · by_cases hν : ν = 0
      · rw [Set.indicator_of_notMem (fun h : ν ∈ T ↦ h.1 hν), Set.indicator_of_mem hS, hν, h₀]
      · rw [Set.indicator_of_mem (⟨hν, hS⟩ : ν ∈ T), Set.indicator_of_mem hS]
    · rw [Set.indicator_of_notMem (fun h : ν ∈ T ↦ hS h.2), Set.indicator_of_notMem hS]
  have hS : HasSum (m ∘ ((↑) : S → ℂ)) (H z) :=
    hF.hasSum_bianchiFourierMode hK hx z exists_mem_glUnipotents
  exact hasSum_subtype_iff_indicator.mpr (hind ▸ hasSum_subtype_iff_indicator.mp hS)

lemma IsBianchiCuspFunction.norm_bianchiFourierCoeff_apply_zero (hK : finrank ℚ K = 2)
    (hx : (σ x).im ≠ 0) (hk' : Even k) (hk : k ≠ 0) (hδ : δ ^ 2 = discr K)
    (hH : IsBianchiCuspFunction σ k H) (hper : ∀ a : 𝓞 K, glSlash σ k (glUpper a) H = H)
    (hc : HasBianchiWhittakerExpansion σ δ k (extend H) c) {α : 𝓞 K} (hα : α ≠ 0) {y : ℝ}
    (hy : 0 < y) : ‖bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx))
      (σ (α : K) / δ) H y 0‖ = ‖c α‖ * y * ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π * ‖σ α / δ‖ * y)‖ := by
  have hδ₀ : δ ≠ 0 := ne_zero_of_sq_eq_discr K hδ
  have hν : σ (α : K) / δ ≠ 0 :=
    div_ne_zero ((map_ne_zero σ).mpr (RingOfIntegers.coe_ne_zero_iff.mpr hα)) hδ₀
  have hF : IsBianchiModularForm σ (glUnipotents K) k H := hH.isBianchiModularForm hk' hper
  have : Countable (Submodule.span ℤ (range (integralLatticeBasis σ hK hx))).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (range (integralLatticeBasis σ hK hx))))
  have hdual : ∀ l ∈ (Submodule.span ℤ (range (integralLatticeBasis σ hK hx))).toAddSubgroup,
      cexp (2 * π * I * (σ (α : K) / δ * l + conj (σ (α : K) / δ * l))) = 1 := by
    intro l hl
    rw [toAddSubgroup_span_integralLatticeBasis hK hx] at hl
    rcases mem_bianchiScaledLattice.mp hl with ⟨a, rfl⟩
    have e : σ (α : K) / δ * σ (1 * (a : K)) = σ ((α * a : 𝓞 K) : K) / δ := by
      simp only [one_mul, map_mul]
      ring1
    rw [e]
    exact cexp_two_pi_mul_eq_one hK hx hδ _
  have hPb : Bornology.IsBounded (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) :=
    ZSpan.fundamentalDomain_isBounded _
  have hmode : bianchiFourierMode (σ α / δ) (bianchiFourierCoeff
      (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) (σ α / δ) H) =
        (bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) (σ α / δ) H
          1 0 / bianchiWhittakerVector k (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ α / δ‖) 0) •
            bianchiWhittakerFunction (σ α / δ) k :=
    hF.fourierMode_eq_smul_bianchiWhittakerFunction _
      (span_integralLatticeBasis_le_cuspTranslations hK hx exists_mem_glUnipotents) hk hν
      (ZSpan.isAddFundamentalDomain' _ volume) hPb hdual
  have hcα : c α = bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx))
      (σ α / δ) H 1 0 / bianchiWhittakerVector k (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ α / δ‖) 0 :=
    hc.coeff_eq hK hx hδ (hH.hasBianchiWhittakerExpansion hK hx hk' hk hδ hper) hα
  have hz : bianchiFourierMode (σ α / δ) (bianchiFourierCoeff
      (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) (σ α / δ) H)
        (.mk (WithLp.toLp 2 (0, y)) hy) 0 =
      ((bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) (σ α / δ) H
        1 0 / bianchiWhittakerVector k (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ α / δ‖) 0) •
          bianchiWhittakerFunction (σ α / δ) k) (.mk (WithLp.toLp 2 (0, y)) hy) 0 :=
    congrFun (congrFun hmode (.mk (WithLp.toLp 2 (0, y)) hy)) 0
  have hco : coords (.mk (WithLp.toLp 2 (0, y)) hy) = (0, y) := rfl
  simp only [bianchiFourierMode, bianchiWhittakerFunction, hco, mul_zero, map_zero, add_zero,
    Complex.exp_zero, Pi.smul_apply, smul_eq_mul, mul_one, one_mul] at hz
  rw [← hcα] at hz
  have hu : ‖σ (α : K) / δ / ‖σ (α : K) / δ‖‖ = 1 := norm_div_norm_eq_one hν
  have hW0 : ‖bianchiWhittakerVector k (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ (α : K) / δ‖ * y) 0‖ =
      ‖besselK (((0 : Fin (k + 1)) : ℕ) - (k : ℂ) / 2) (4 * π * ‖σ (α : K) / δ‖ * y)‖ :=
    norm_bianchiWhittakerVector_apply k _ hu 0
  have h0 : (((0 : Fin (k + 1)) : ℕ) : ℂ) - (k : ℂ) / 2 = -((k / 2 : ℝ) : ℂ) := by
    push_cast [Fin.val_zero]
    ring1
  rw [h0, besselK_neg] at hW0
  rw [hz, norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hy.le, hW0, ← mul_assoc]

lemma IsBianchiCuspFunction.norm_coeff_mul_norm_besselK_le (hK : finrank ℚ K = 2)
    (hx : (σ x).im ≠ 0) (hk' : Even k) (hk : k ≠ 0) (hδ : δ ^ 2 = discr K)
    (hH : IsBianchiCuspFunction σ k H) (hper : ∀ a : 𝓞 K, glSlash σ k (glUpper a) H = H)
    (hc : HasBianchiWhittakerExpansion σ δ k (extend H) c) {α : 𝓞 K} (hα : α ≠ 0) {y A : ℝ}
    (hy : 0 < y) (hA : ∀ w : ℂ, ‖extend H (w, y)‖ ≤ A) :
    ‖c α‖ * y * ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π * ‖σ α / δ‖ * y)‖ ≤ A := by
  rw [← hH.norm_bianchiFourierCoeff_apply_zero hK hx hk' hk hδ hper hc hα hy]
  exact (norm_le_pi_norm _ 0).trans
    (norm_bianchiFourierCoeff_le_of_forall (ZSpan.fundamentalDomain_isBounded _) hA)

lemma le_mul_norm_div_mul (hK : finrank ℚ K = 2) (hδ₀ : δ ≠ 0) {y₁ : ℝ} (hy₁ : 0 < y₁) {α : 𝓞 K}
    (hα : α ≠ 0) : 4 * π * y₁ / ‖δ‖ ≤ 4 * π * ‖σ α / δ‖ * y₁ := by
  have hδ' : 0 < ‖δ‖ := norm_pos_iff.mpr hδ₀
  have h₁ : 4 * π * y₁ / ‖δ‖ * 1 ≤ 4 * π * y₁ / ‖δ‖ * ‖σ α‖ :=
    mul_le_mul_of_nonneg_left (one_le_norm_apply hK hα) (by positivity)
  have e : 4 * π * ‖σ α / δ‖ * y₁ = 4 * π * y₁ / ‖δ‖ * ‖σ α‖ := by
    rw [norm_div]
    ring1
  rw [e]
  rwa [mul_one] at h₁

/-- **The invariant norm of a periodic cuspidal function is bounded above any height**: for `K`
imaginary quadratic and `H` a cuspidal function of even weight `k ≥ 1`, periodic for `σ(𝒪_K)`, the
function `y^k ⟨H, H⟩_k` is bounded on the points of height at least `y₁ > 0`: at height
`y₂ = y₁ / 2`, `H` is bounded, say by `C`, so that `|c(α)| y₂ K_{k/2}(4π|μ|y₂) ≤ C`, and
`K_{k/2}(t) ≥ e^{-5t/4} / 2`. -/
lemma IsBianchiCuspFunction.exists_bianchiNormSq_le (hK : finrank ℚ K = 2) (hk' : Even k)
    (hk : k ≠ 0) (hH : IsBianchiCuspFunction σ k H)
    (hper : ∀ a : 𝓞 K, glSlash σ k (glUpper a) H = H) {y₁ : ℝ} (hy₁ : 0 < y₁) :
    ∃ M : ℝ, ∀ z : HyperbolicThreeSpace, y₁ ≤ z.height → bianchiNormSq H z ≤ M := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  have hδ : ((discr K : ℂ) ^ (2⁻¹ : ℂ)) ^ 2 = discr K := cpow_ofNat_inv_pow _ 2
  have hδ₀ : (discr K : ℂ) ^ (2⁻¹ : ℂ) ≠ 0 := ne_zero_of_sq_eq_discr K hδ
  generalize (discr K : ℂ) ^ (2⁻¹ : ℂ) = δ at hδ hδ₀
  have hδ' : 0 < ‖δ‖ := norm_pos_iff.mpr hδ₀
  have hc : HasBianchiWhittakerExpansion σ δ k (extend H) fun α ↦
      bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) (σ α / δ) H 1 0 /
        bianchiWhittakerVector k (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ α / δ‖) 0 :=
    hH.hasBianchiWhittakerExpansion hK hx hk' hk hδ hper
  have hy₂ : 0 < y₁ / 2 := half_pos hy₁
  rcases hH.exists_norm_extend_le hK hx hper hy₂ with ⟨C, hC⟩
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hr : 1 ≤ (k / 2 : ℝ) := one_le_div_two hk' hk
  have hE : 0 ≤ 2 * C * (y₁ / 2)⁻¹ * ‖δ‖ ^ (k / 2 + 1) := by
    positivity
  have hcE (α : 𝓞 K) (hα : α ≠ 0) : ‖bianchiFourierCoeff (ZSpan.fundamentalDomain
      (integralLatticeBasis σ hK hx)) (σ α / δ) H 1 0 / bianchiWhittakerVector k
        (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ α / δ‖) 0‖ ≤ 2 * C * (y₁ / 2)⁻¹ * ‖δ‖ ^ (k / 2 + 1) *
          ‖σ α / δ‖ ^ (k / 2 + 1) * rexp (5 / 2 * π * ‖σ α / δ‖ * y₁) := by
    have hs : 0 < ‖σ (α : K) / δ‖ := norm_pos_iff.mpr (div_ne_zero ((map_ne_zero σ).mpr
      (RingOfIntegers.coe_ne_zero_iff.mpr hα)) hδ₀)
    have h₁ : ‖bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx))
        (σ α / δ) H 1 0 / bianchiWhittakerVector k (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ α / δ‖) 0‖ *
          (y₁ / 2) * ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π * ‖σ α / δ‖ * (y₁ / 2))‖ ≤ C :=
      hH.norm_coeff_mul_norm_besselK_le hK hx hk' hk hδ hper hc hα hy₂ hC
    have ht : 0 < 4 * π * ‖σ (α : K) / δ‖ * (y₁ / 2) := by
      positivity
    have h₂ : 2⁻¹ * rexp (-(5 / 4 * (4 * π * ‖σ (α : K) / δ‖ * (y₁ / 2)))) ≤
        ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π * ‖σ (α : K) / δ‖ * (y₁ / 2))‖ :=
      exp_le_norm_besselK hr ht
    have e₁ : 5 / 4 * (4 * π * ‖σ (α : K) / δ‖ * (y₁ / 2)) = 5 / 2 * π * ‖σ (α : K) / δ‖ * y₁ := by
      ring1
    rw [e₁, Real.exp_neg] at h₂
    have hc₀ : 0 ≤ ‖bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx))
        (σ α / δ) H 1 0 / bianchiWhittakerVector k (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ α / δ‖) 0‖ :=
      norm_nonneg _
    generalize ‖bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx))
      (σ α / δ) H 1 0 / bianchiWhittakerVector k (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ α / δ‖) 0‖ = c₀
        at h₁ hc₀ ⊢
    have he : 0 < rexp (5 / 2 * π * ‖σ (α : K) / δ‖ * y₁) := exp_pos _
    generalize rexp (5 / 2 * π * ‖σ (α : K) / δ‖ * y₁) = e at h₂ he ⊢
    have h₃ : c₀ * (y₁ / 2) * (2⁻¹ * e⁻¹) ≤ C :=
      (mul_le_mul_of_nonneg_left h₂ (by positivity)).trans h₁
    have h₄ : c₀ ≤ 2 * C * (y₁ / 2)⁻¹ * e := by
      have h₅ : c₀ * (y₁ / 2) * (2⁻¹ * e⁻¹) * (2 * (y₁ / 2)⁻¹ * e) ≤ C * (2 * (y₁ / 2)⁻¹ * e) :=
        mul_le_mul_of_nonneg_right h₃ (by positivity)
      have e₂ : c₀ * (y₁ / 2) * (2⁻¹ * e⁻¹) * (2 * (y₁ / 2)⁻¹ * e) = c₀ := by
        field_simp
      rw [e₂] at h₅
      linarith
    have h₆ : 1 ≤ ‖δ‖ ^ (k / 2 + 1) * ‖σ (α : K) / δ‖ ^ (k / 2 + 1) := by
      rw [← mul_pow, norm_div, mul_div_cancel₀ _ hδ'.ne']
      exact one_le_pow₀ (one_le_norm_apply hK hα)
    have e₃ : 2 * C * (y₁ / 2)⁻¹ * ‖δ‖ ^ (k / 2 + 1) * ‖σ (α : K) / δ‖ ^ (k / 2 + 1) * e =
        2 * C * (y₁ / 2)⁻¹ * e * (‖δ‖ ^ (k / 2 + 1) * ‖σ (α : K) / δ‖ ^ (k / 2 + 1)) := by
      ring1
    rw [e₃]
    exact h₄.trans (le_mul_of_one_le_right (by positivity) h₆)
  have ht₁ : 0 < 4 * π * y₁ / ‖δ‖ := by
    positivity
  have hsum : HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦ rexp (-(3 / 4 * π * ‖σ α.1 / δ‖ * y₁)))
      (∑' α : {α : 𝓞 K // α ≠ 0}, rexp (-(3 / 4 * π * ‖σ α.1 / δ‖ * y₁))) :=
    (summable_exp_neg_norm_div hK hx hδ₀ hy₁).hasSum
  refine ⟨2 ^ k * (2 * C * (y₁ / 2)⁻¹ * ‖δ‖ ^ (k / 2 + 1) *
    bianchiTailConstant k (4 * π * y₁ / ‖δ‖) *
      ∑' b : {α : 𝓞 K // α ≠ 0}, rexp (-(3 / 4 * π * ‖σ b.1 / δ‖ * y₁))) ^ 2, fun z hz ↦ ?_⟩
  have h₁ : z.height ^ (k / 2) * ‖H z‖ ≤ 2 * C * (y₁ / 2)⁻¹ * ‖δ‖ ^ (k / 2 + 1) *
      bianchiTailConstant k (4 * π * y₁ / ‖δ‖) *
        ∑' α : {α : 𝓞 K // α ≠ 0}, rexp (-(3 / 4 * π * ‖σ α.1 / δ‖ * y₁)) :=
    height_pow_mul_norm_le_of_hasSum (norm_eq_sqrt_of_sq_eq_discr hδ) hc ht₁
      (fun α hα ↦ div_ne_zero ((map_ne_zero σ).mpr (RingOfIntegers.coe_ne_zero_iff.mpr hα)) hδ₀)
      (fun α hα ↦ le_mul_norm_div_mul hK hδ₀ hy₁ hα) hE hcE hsum (fun _ ↦ (exp_pos _).le)
      (fun α ↦ Or.inr le_rfl) hz
  refine (bianchiNormSq_le_of_even hk' z).trans ?_
  have h₂ : 0 ≤ z.height ^ (k / 2) * ‖H z‖ :=
    mul_nonneg (pow_nonneg z.height_pos.le _) (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h₂ h₁ 2) (by positivity)

variable (σ) in
/-- **The Sturm bound**: for `K` imaginary quadratic, an even weight `k ≥ 1` and `y₁ > 0`, there is
`B` such that if `H` is a cuspidal function, periodic for `σ(𝒪_K)`, with `y^k ⟨H, H⟩_k ≤ M` on `ℋ₃`,
whose Fourier–Bessel coefficients `c(α)` vanish for `|σ(α)| ≤ B`, then `y^k ⟨H, H⟩_k ≤ M / 2` at
height at least `y₁`: the Fourier coefficient at height `1 / |μ|` gives
`|c(α)| ≤ |μ|^{k/2+1} √M / K_{k/2}(4π)`, and the terms of the Fourier–Bessel series with
`|σ(α)| > B` have a sum tending to `0` with `B⁻¹`. -/
lemma exists_bianchiNormSq_le_half (hK : finrank ℚ K = 2) (hk' : Even k) (hk : k ≠ 0) {y₁ : ℝ}
    (hy₁ : 0 < y₁) : ∃ B : ℝ, ∀ (H : HyperbolicThreeSpace → Fin (k + 1) → ℂ) (c : 𝓞 K → ℂ)
      (M : ℝ), IsBianchiCuspFunction σ k H → (∀ a : 𝓞 K, glSlash σ k (glUpper a) H = H) →
        HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend H) c →
          (∀ z, bianchiNormSq H z ≤ M) → (∀ α : 𝓞 K, α ≠ 0 → ‖σ α‖ ≤ B → c α = 0) →
            ∀ z : HyperbolicThreeSpace, y₁ ≤ z.height → bianchiNormSq H z ≤ M / 2 := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  have hδ : ((discr K : ℂ) ^ (2⁻¹ : ℂ)) ^ 2 = discr K := cpow_ofNat_inv_pow _ 2
  have hδ₀ : (discr K : ℂ) ^ (2⁻¹ : ℂ) ≠ 0 := ne_zero_of_sq_eq_discr K hδ
  generalize (discr K : ℂ) ^ (2⁻¹ : ℂ) = δ at hδ hδ₀
  have hδ' : 0 < ‖δ‖ := norm_pos_iff.mpr hδ₀
  have ht₁ : 0 < 4 * π * y₁ / ‖δ‖ := by
    positivity
  have hT : 0 ≤ bianchiTailConstant k (4 * π * y₁ / ‖δ‖) := bianchiTailConstant_nonneg _
  have hκ : 0 < ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π)‖ :=
    norm_pos_iff.mpr (besselK_ofReal_ne_zero _ (by positivity))
  have hε : 0 < ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π)‖ /
      ((bianchiTailConstant k (4 * π * y₁ / ‖δ‖) + 1) * 2 ^ (k + 1)) := by
    positivity
  have hsum : Summable fun α : {α : 𝓞 K // α ≠ 0} ↦ rexp (-(3 / 4 * π * ‖σ α.1 / δ‖ * y₁)) :=
    summable_exp_neg_norm_div hK hx hδ₀ hy₁
  rcases ((tendsto_tsum_compl_atTop_zero fun α : {α : 𝓞 K // α ≠ 0} ↦
    rexp (-(3 / 4 * π * ‖σ α.1 / δ‖ * y₁))).eventually (gt_mem_nhds hε)).exists with ⟨S, hS⟩
  rcases (S.image fun α ↦ ‖σ (α.1 : K)‖).exists_le with ⟨B, hB⟩
  refine ⟨B, fun H c M hH hper hc hM hc₀ z hz ↦ ?_⟩
  have hM₀ : 0 ≤ M := (bianchiNormSq_nonneg H z).trans (hM z)
  have hE : 0 ≤ √M / ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π)‖ := by
    positivity
  have hcE (α : 𝓞 K) (hα : α ≠ 0) : ‖c α‖ ≤ √M / ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π)‖ *
      ‖σ α / δ‖ ^ (k / 2 + 1) * rexp (5 / 2 * π * ‖σ α / δ‖ * y₁) := by
    have hs : 0 < ‖σ (α : K) / δ‖ := norm_pos_iff.mpr (div_ne_zero ((map_ne_zero σ).mpr
      (RingOfIntegers.coe_ne_zero_iff.mpr hα)) hδ₀)
    have hy : 0 < ‖σ (α : K) / δ‖⁻¹ := inv_pos.mpr hs
    have h₁ : ‖c α‖ * ‖σ (α : K) / δ‖⁻¹ *
        ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π * ‖σ (α : K) / δ‖ * ‖σ (α : K) / δ‖⁻¹)‖ ≤
          (‖σ (α : K) / δ‖⁻¹ ^ (k / 2))⁻¹ * √M :=
      hH.norm_coeff_mul_norm_besselK_le hK hx hk' hk hδ hper hc hα hy
        (norm_extend_le_of_bianchiNormSq_le hM hk' hy)
    have e : 4 * π * ‖σ (α : K) / δ‖ * ‖σ (α : K) / δ‖⁻¹ = 4 * π := by
      field_simp
    rw [e, inv_pow, inv_inv] at h₁
    have h₂ : 1 ≤ rexp (5 / 2 * π * ‖σ (α : K) / δ‖ * y₁) := Real.one_le_exp (by positivity)
    have h₃ : ‖c α‖ ≤ √M / ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π)‖ * ‖σ (α : K) / δ‖ ^ (k / 2 + 1) := by
      have e₂ : ‖c α‖ = ‖c α‖ * ‖σ (α : K) / δ‖⁻¹ * ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π)‖ *
          (‖σ (α : K) / δ‖ / ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π)‖) := by
        field_simp
      rw [e₂]
      refine (mul_le_mul_of_nonneg_right h₁ (by positivity)).trans_eq ?_
      rw [pow_succ]
      ring1
    exact h₃.trans (le_mul_of_one_le_right (by positivity) h₂)
  have hg : HasSum (({α | α ∉ S} : Set {α : 𝓞 K // α ≠ 0}).indicator
      fun α ↦ rexp (-(3 / 4 * π * ‖σ α.1 / δ‖ * y₁)))
      (∑' a : {x // x ∉ S}, rexp (-(3 / 4 * π * ‖σ a.1.1 / δ‖ * y₁))) :=
    hasSum_subtype_iff_indicator.mp (hsum.subtype _).hasSum
  have h₁ : z.height ^ (k / 2) * ‖H z‖ ≤ √M / ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π)‖ *
      bianchiTailConstant k (4 * π * y₁ / ‖δ‖) *
        ∑' a : {x // x ∉ S}, rexp (-(3 / 4 * π * ‖σ a.1.1 / δ‖ * y₁)) := by
    refine height_pow_mul_norm_le_of_hasSum (norm_eq_sqrt_of_sq_eq_discr hδ) hc ht₁
      (fun α hα ↦ div_ne_zero ((map_ne_zero σ).mpr (RingOfIntegers.coe_ne_zero_iff.mpr hα)) hδ₀)
      (fun α hα ↦ le_mul_norm_div_mul hK hδ₀ hy₁ hα) hE hcE hg
      (fun α ↦ Set.indicator_nonneg (fun _ _ ↦ (exp_pos _).le) α) (fun α ↦ ?_) hz
    by_cases hα : α ∈ S
    · exact Or.inl (hc₀ α α.2 (hB _ (Finset.mem_image_of_mem _ hα)))
    · exact Or.inr (Set.indicator_of_mem (s := {α | α ∉ S}) hα
        (fun α ↦ rexp (-(3 / 4 * π * ‖σ α.1 / δ‖ * y₁)))).symm.le
  refine (bianchiNormSq_le_of_even hk' z).trans ?_
  have h₂ : 0 ≤ z.height ^ (k / 2) * ‖H z‖ :=
    mul_nonneg (pow_nonneg z.height_pos.le _) (norm_nonneg _)
  have h₃ : z.height ^ (k / 2) * ‖H z‖ ≤ √M / 2 ^ (k + 1) := by
    refine h₁.trans ?_
    refine (mul_le_mul_of_nonneg_left hS.le (mul_nonneg hE hT)).trans ?_
    have h₄ : bianchiTailConstant k (4 * π * y₁ / ‖δ‖) / (bianchiTailConstant k
        (4 * π * y₁ / ‖δ‖) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have e : √M / ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π)‖ * bianchiTailConstant k (4 * π * y₁ / ‖δ‖) *
        (‖besselK ((k / 2 : ℝ) : ℂ) (4 * π)‖ / ((bianchiTailConstant k (4 * π * y₁ / ‖δ‖) + 1) *
          2 ^ (k + 1))) = √M / 2 ^ (k + 1) * (bianchiTailConstant k (4 * π * y₁ / ‖δ‖) /
            (bianchiTailConstant k (4 * π * y₁ / ‖δ‖) + 1)) := by
      field_simp
    rw [e]
    exact mul_le_of_le_one_right (by positivity) h₄
  have h₅ : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h₂ h₃ 2) (by positivity)).trans ?_
  rw [div_pow, Real.sq_sqrt hM₀, pow_succ (2 : ℝ) k]
  have e : (2 : ℝ) ^ k * (M / (2 ^ k * 2) ^ 2) = M / (4 * 2 ^ k) := by
    field_simp
    ring1
  rw [e]
  exact div_le_div_of_nonneg_left hM₀ (by norm_num) (by linarith)

end HyperbolicThreeSpace
