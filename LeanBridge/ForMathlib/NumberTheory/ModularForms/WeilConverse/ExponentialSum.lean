import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import TauCeti.Analysis.Complex.UpperHalfPlane.ResToImagAxis

/-!
# Exponential sums with polynomially bounded coefficients

For a sequence `c` with `c n = O(n ^ m)`, the sum `∑ c n e(n z)`, where `e(x) = e^{2πix}`, is a
holomorphic `1`-periodic function on the upper half plane. If `c 0 = 0`, its restriction to the
imaginary axis has Mellin transform `(2π) ^ (-s) Γ(s) ∑ c n n ^ (-s)` where the Dirichlet series
converges. This is the dictionary of Hecke's and Weil's converse theorems.

## Main definitions

* `ModularForm.HasPolyGrowth`: `c n = O(n ^ m)` for some natural number `m`.
* `ModularForm.HasModerateGrowth`: `|f z| ≤ K (1 + (Im z) ^ (-M))` on `ℍ`.
* `ModularForm.expSum`: the exponential sum `∑ c n e(n z)`.
* `ModularForm.completedLSeries`: the completed Dirichlet series `(2π) ^ (-s) Γ(s) ∑ c n n ^ (-s)`.

## Main results

* `ModularForm.mdifferentiable_expSum`: the exponential sum is holomorphic.
* `ModularForm.exists_norm_expSum_le`: without constant term, it is `O((Im z) ^ (-M))`.
* `ModularForm.mellinConvergent_resToImagAxis_expSum`: its Mellin transform converges.
* `ModularForm.mellin_resToImagAxis_expSum`: its Mellin transform is the completed Dirichlet series.
-/

open Asymptotics Complex Filter Function Topology Set

open scoped Real Manifold

open UpperHalfPlane hiding I I_re I_im

namespace ModularForm

/-- The sequence `c` has **polynomial growth**: `c n = O(n ^ m)` for some natural number `m`. The
term `c 0` is not constrained. -/
def HasPolyGrowth (c : ℕ → ℂ) : Prop :=
  ∃ (C : ℝ) (m : ℕ), ∀ n : ℕ, n ≠ 0 → ‖c n‖ ≤ C * (n : ℝ) ^ m

/-- A function on `ℍ` has **moderate growth** if `|f z| ≤ K (1 + (Im z) ^ (-M))` for some `K` and
`M`. -/
def HasModerateGrowth (f : ℍ → ℂ) : Prop :=
  ∃ (K : ℝ) (M : ℕ), ∀ z : ℍ, ‖f z‖ ≤ K * (1 + z.im ^ (-(M : ℝ)))

/-- The **exponential sum** `∑ c n e(n z)` of a sequence `c`, with `e(x) = e^{2πix}`, on the upper
half plane. -/
noncomputable def expSum (c : ℕ → ℂ) (z : ℍ) : ℂ :=
  ∑' n : ℕ, c n * cexp (2 * π * I * n * z)

/-- The **completed Dirichlet series** `(2π) ^ (-s) Γ(s) ∑ c n n ^ (-s)` of a sequence `c`: the
Mellin transform of the exponential sum of `c` on the imaginary axis, when `c 0 = 0`. -/
noncomputable def completedLSeries (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  (2 * π : ℂ) ^ (-s) * Gamma s * LSeries c s

variable {c : ℕ → ℂ} {y : ℝ}

lemma qParam_one_pow (z : ℍ) (n : ℕ) :
    Periodic.qParam 1 (z : ℂ) ^ n = cexp (2 * π * I * n * z) := by
  rw [Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring1

lemma norm_cexp_two_pi_I_mul (n : ℕ) (w : ℂ) :
    ‖cexp (2 * π * I * n * w)‖ = Real.exp (-(2 * π * w.im) * n) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [mul_re, mul_im, re_ofNat, im_ofNat, ofReal_re, ofReal_im, I_re, I_im, natCast_re,
    natCast_im]
  ring1

lemma HasPolyGrowth.summable_norm_mul_exp (hc : HasPolyGrowth c) (hy : 0 < y) :
    Summable fun n : ℕ ↦ ‖c n‖ * Real.exp (-(2 * π * y) * n) := by
  rcases hc with ⟨C, m, hC⟩
  have hr : 0 < 2 * π * y := by positivity
  refine (summable_nat_add_iff 1).mp ?_
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
    (((summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul m hr)).mul_left |C|)
  have h1 : ‖c (n + 1)‖ ≤ |C| * ((n + 1 : ℕ) : ℝ) ^ m :=
    (hC (n + 1) n.succ_ne_zero).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

lemma HasPolyGrowth.summable_mul_cexp (hc : HasPolyGrowth c) {w : ℂ} (hw : 0 < w.im) :
    Summable fun n : ℕ ↦ c n * cexp (2 * π * I * n * w) := by
  refine Summable.of_norm ?_
  simpa only [norm_mul, norm_cexp_two_pi_I_mul] using hc.summable_norm_mul_exp hw

/-- **The exponential sum of a sequence of polynomial growth is holomorphic.** -/
lemma mdifferentiable_expSum (hc : HasPolyGrowth c) : MDiff (expSum c) := by
  refine UpperHalfPlane.mdifferentiable_iff.mpr fun w hw ↦ ?_
  have hw' : 0 < w.im := hw
  have hy : 0 < w.im / 2 := half_pos hw'
  have hopen : IsOpen {z : ℂ | w.im / 2 < z.im} := isOpen_lt continuous_const continuous_im
  have hmem : {z : ℂ | w.im / 2 < z.im} ∈ 𝓝 w := hopen.mem_nhds (half_lt_self hw')
  have hdiff : DifferentiableOn ℂ (fun z : ℂ ↦ ∑' n : ℕ, c n * cexp (2 * π * I * n * z))
      {z : ℂ | w.im / 2 < z.im} :=
    differentiableOn_tsum_of_summable_norm (hc.summable_norm_mul_exp hy)
      (fun n ↦ by fun_prop) hopen fun n z hz ↦ by
        rw [norm_mul, norm_cexp_two_pi_I_mul]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
        have hz' : w.im / 2 < z.im := hz
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith [mul_nonneg (mul_nonneg two_pos.le Real.pi_pos.le) hn,
          mul_le_mul_of_nonneg_left hz'.le (mul_nonneg (mul_nonneg two_pos.le Real.pi_pos.le) hn)]
  refine ((hdiff.differentiableAt hmem).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with z hz
  simp [expSum, ofComplex_apply_of_im_pos hz]

lemma resToImagAxis_expSum_eq (ht : 0 < y) :
    resToImagAxis (expSum c) y = ∑' n : ℕ, c n * Real.exp (-(2 * π * n) * y) := by
  rw [resToImagAxis_of_pos _ ht, expSum]
  refine tsum_congr fun n ↦ ?_
  congr 1
  push_cast
  congr 1
  linear_combination (2 * π * n * y : ℂ) * I_sq

lemma HasPolyGrowth.continuousOn_resToImagAxis (hc : HasPolyGrowth c) :
    ContinuousOn (resToImagAxis (expSum c)) (Ioi 0) :=
  fun _ ht ↦ (differentiableAt_resToImagAxis_of_mDiffAt _ ht
    (mdifferentiable_expSum hc _)).continuousAt.continuousWithinAt

variable {C : ℝ} {m M : ℕ} {s : ℂ}

private lemma exists_tsum_norm_mul_exp_le (hC : ∀ n : ℕ, n ≠ 0 → ‖c n‖ ≤ C * (n : ℝ) ^ m)
    (h0 : c 0 = 0) (hM : m + 2 ≤ M) : ∃ K : ℝ, ∀ t : ℝ, 0 < t →
      ∑' n : ℕ, ‖c n‖ * Real.exp (-(2 * π * t) * n) ≤ K * t ^ (-(M : ℝ)) := by
  have hc : HasPolyGrowth c := ⟨C, m, hC⟩
  have hs : Summable fun n : ℕ ↦ 1 / (n : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
  refine ⟨|C| * (M.factorial : ℝ) / (2 * π) ^ M * ∑' n : ℕ, 1 / (n : ℝ) ^ 2, fun t ht ↦ ?_⟩
  rw [Real.rpow_neg ht.le, Real.rpow_natCast, ← tsum_mul_left, ← tsum_mul_right]
  refine (hc.summable_norm_mul_exp ht).tsum_le_tsum (fun n ↦ ?_) ((hs.mul_left _).mul_right _)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [h0]
  have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)
  have hn0 : (0 : ℝ) < n := by linarith
  have hx : 0 < 2 * π * n * t := by positivity
  have hexp : Real.exp (-(2 * π * t) * n) ≤ (M.factorial : ℝ) / (2 * π * n * t) ^ M := by
    have h1 : (2 * π * n * t) ^ M / (M.factorial : ℝ) ≤ Real.exp (2 * π * n * t) :=
      Real.pow_div_factorial_le_exp _ hx.le M
    rw [show -(2 * π * t) * n = -(2 * π * n * t) by ring1, Real.exp_neg,
      inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    exact h1
  have hpow : (n : ℝ) ^ m / (n : ℝ) ^ M ≤ 1 / (n : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
    exact pow_le_pow_right₀ hn' (by omega)
  have hb : ‖c n‖ ≤ |C| * (n : ℝ) ^ m :=
    (hC n hn).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  refine (mul_le_mul hb hexp (Real.exp_pos _).le (by positivity)).trans ?_
  rw [show |C| * (n : ℝ) ^ m * ((M.factorial : ℝ) / (2 * π * n * t) ^ M) =
    |C| * (M.factorial : ℝ) / (2 * π) ^ M * ((n : ℝ) ^ m / (n : ℝ) ^ M * (t ^ M)⁻¹) by
      rw [mul_pow, mul_pow]
      field_simp]
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (by positivity))
    (by positivity)).trans_eq ?_
  ring1

/-- **The growth of an exponential sum**: `|∑ c n e(n z)| ≤ K (Im z) ^ (-M)` on `ℍ`, for every
`M ≥ m + 2`, if `c n = O(n ^ m)` and `c 0 = 0`. -/
lemma exists_norm_expSum_le (hC : ∀ n : ℕ, n ≠ 0 → ‖c n‖ ≤ C * (n : ℝ) ^ m) (h0 : c 0 = 0)
    (hM : m + 2 ≤ M) : ∃ K : ℝ, ∀ z : ℍ, ‖expSum c z‖ ≤ K * z.im ^ (-(M : ℝ)) := by
  have hc : HasPolyGrowth c := ⟨C, m, hC⟩
  rcases exists_tsum_norm_mul_exp_le hC h0 hM with ⟨K, hK⟩
  refine ⟨K, fun z ↦ ?_⟩
  have h1 : Summable fun n : ℕ ↦ ‖c n * cexp (2 * π * I * n * z)‖ :=
    (hc.summable_norm_mul_exp z.im_pos).congr fun n ↦ by
      rw [norm_mul, norm_cexp_two_pi_I_mul]
      rfl
  refine (norm_tsum_le_tsum_norm h1).trans (le_trans (le_of_eq ?_) (hK _ z.im_pos))
  simp only [norm_mul, norm_cexp_two_pi_I_mul]
  rfl

lemma HasPolyGrowth.update_zero (hc : HasPolyGrowth c) : HasPolyGrowth (update c 0 0) := by
  rcases hc with ⟨C, m, hC⟩
  exact ⟨C, m, fun n hn ↦ by rw [update_of_ne hn]; exact hC n hn⟩

lemma expSum_eq_add_expSum_update (hc : HasPolyGrowth c) (z : ℍ) :
    expSum c z = c 0 + expSum (update c 0 0) z := by
  rw [expSum, expSum, (hc.summable_mul_cexp z.im_pos).tsum_eq_zero_add,
    (hc.update_zero.summable_mul_cexp z.im_pos).tsum_eq_zero_add]
  simp

lemma completedLSeries_update : completedLSeries (update c 0 0) s = completedLSeries c s := by
  rw [completedLSeries, completedLSeries, LSeries_congr (g := c) (fun hn ↦ update_of_ne hn _ _)]

lemma HasPolyGrowth.hasModerateGrowth (hc : HasPolyGrowth c) : HasModerateGrowth (expSum c) := by
  rcases hc.update_zero with ⟨C, m, hC⟩
  rcases exists_norm_expSum_le hC (update_self _ _ _) le_rfl with ⟨K, hK⟩
  refine ⟨‖c 0‖ + |K|, m + 2, fun z ↦ ?_⟩
  have h1 : 0 ≤ z.im ^ (-((m + 2 : ℕ) : ℝ)) := Real.rpow_nonneg z.im_pos.le _
  rw [expSum_eq_add_expSum_update hc]
  nlinarith [norm_add_le (c 0) (expSum (update c 0 0) z), hK z, abs_nonneg K,
    mul_le_mul_of_nonneg_right (le_abs_self K) h1, mul_nonneg (norm_nonneg (c 0)) h1]

private lemma exists_norm_resToImagAxis_le (hC : ∀ n : ℕ, n ≠ 0 → ‖c n‖ ≤ C * (n : ℝ) ^ m)
    (h0 : c 0 = 0) (hM : m + 2 ≤ M) :
    ∃ K : ℝ, ∀ t : ℝ, 0 < t → ‖resToImagAxis (expSum c) t‖ ≤ K * t ^ (-(M : ℝ)) := by
  rcases exists_norm_expSum_le hC h0 hM with ⟨K, hK⟩
  refine ⟨K, fun t ht ↦ ?_⟩
  rw [resToImagAxis_of_pos _ ht]
  refine (hK _).trans_eq ?_
  congr 2
  simp

/-- **The restriction of an exponential sum to the imaginary axis is Mellin-convergent** on
`Re s > m + 2`, if `c n = O(n ^ m)` and `c 0 = 0`. -/
lemma mellinConvergent_resToImagAxis_expSum (hC : ∀ n : ℕ, n ≠ 0 → ‖c n‖ ≤ C * (n : ℝ) ^ m)
    (h0 : c 0 = 0) (hs : (m : ℝ) + 2 < s.re) : MellinConvergent (resToImagAxis (expSum c)) s := by
  have hc : HasPolyGrowth c := ⟨C, m, hC⟩
  have hbd : ∀ M : ℕ, m + 2 ≤ M → ∃ K : ℝ, ∀ t : ℝ, 0 < t →
      ‖resToImagAxis (expSum c) t‖ ≤ K * ‖t ^ (-(M : ℝ))‖ := fun M hM ↦ by
    rcases exists_norm_resToImagAxis_le hC h0 hM with ⟨K, hK⟩
    refine ⟨K, fun t ht ↦ ?_⟩
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
    exact hK t ht
  have hbig : ∀ M : ℕ, m + 2 ≤ M → (resToImagAxis (expSum c)) =O[𝓝[>] 0] (· ^ (-(M : ℝ))) :=
    fun M hM ↦ by
      rcases hbd M hM with ⟨K, hK⟩
      exact IsBigO.of_bound K (eventually_mem_nhdsWithin.mono fun t ht ↦ hK t ht)
  have hbig' : ∀ M : ℕ, m + 2 ≤ M → (resToImagAxis (expSum c)) =O[atTop] (· ^ (-(M : ℝ))) :=
    fun M hM ↦ by
      rcases hbd M hM with ⟨K, hK⟩
      exact IsBigO.of_bound K ((eventually_gt_atTop 0).mono fun t ht ↦ hK t ht)
  rcases exists_nat_gt s.re with ⟨M, hM⟩
  have hM' : m + 2 ≤ m + 2 + M := by omega
  refine mellinConvergent_of_isBigO_rpow (a := ((m + 2 + M : ℕ) : ℝ)) (b := ((m + 2 : ℕ) : ℝ))
    (hc.continuousOn_resToImagAxis.locallyIntegrableOn measurableSet_Ioi) (hbig' _ hM') ?_
    (hbig _ le_rfl) (by push_cast; exact hs)
  push_cast
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- **The Mellin transform of an exponential sum is the completed Dirichlet series**: for
`c n = O(n ^ m)`, `c 0 = 0` and `Re s > m + 2`, the Mellin transform of `t ↦ ∑ c n e^{-2πnt}` is
`(2π) ^ (-s) Γ(s) ∑ c n n ^ (-s)`. -/
lemma mellin_resToImagAxis_expSum (hC : ∀ n : ℕ, n ≠ 0 → ‖c n‖ ≤ C * (n : ℝ) ^ m) (h0 : c 0 = 0)
    (hs : (m : ℝ) + 2 < s.re) : mellin (resToImagAxis (expSum c)) s = completedLSeries c s := by
  have hc : HasPolyGrowth c := ⟨C, m, hC⟩
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs0 : 0 < s.re := by linarith
  have hL : LSeriesSummable c s := LSeriesSummable_of_le_const_mul_rpow (x := (m : ℝ) + 1)
    (by linarith) ⟨C, fun n hn ↦ by
      rw [add_sub_cancel_right, Real.rpow_natCast]
      exact hC n hn⟩
  have hp : ∀ i : ℕ, c i = 0 ∨ 0 < 2 * π * (i : ℝ) := fun i ↦ by
    rcases eq_or_ne i 0 with rfl | hi
    · exact Or.inl h0
    · exact Or.inr (mul_pos (by positivity) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hi)))
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun i : ℕ ↦ c i * Real.exp (-(2 * π * i) * t))
      (resToImagAxis (expSum c) t) := fun t ht ↦ by
    rw [resToImagAxis_expSum_eq ht]
    refine Summable.hasSum (Summable.of_norm ?_)
    refine (hc.summable_norm_mul_exp ht).congr fun n ↦ ?_
    rw [norm_mul, norm_real, Real.norm_eq_abs, Real.abs_exp]
    congr 2
    ring1
  have hsum : Summable fun i : ℕ ↦ ‖c i‖ / (2 * π * (i : ℝ)) ^ s.re := by
    refine (hL.norm.mul_left ((2 * π) ^ (-s.re))).congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [h0]
    rw [LSeries.norm_term_eq]
    simp only [hn, ↓reduceIte]
    rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg n), Real.rpow_neg (by positivity)]
    field_simp
  have h1 : HasSum (fun i : ℕ ↦ Gamma s * c i / ((2 * π * (i : ℝ) : ℝ) : ℂ) ^ s)
      (mellin (resToImagAxis (expSum c)) s) :=
    hasSum_mellin hp hs0 hF hsum
  rw [← h1.tsum_eq, completedLSeries, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [h0]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h2 : ((2 * π * (n : ℝ) : ℝ) : ℂ) ^ s = (2 * π : ℂ) ^ s * (n : ℂ) ^ s := by
    simpa using mul_cpow_ofReal_nonneg (a := 2 * π) (b := (n : ℝ)) (by positivity)
      (Nat.cast_nonneg n) s
  rw [h2, LSeries.term_of_ne_zero hn, cpow_neg]
  have h4 : (2 * π : ℂ) ^ s ≠ 0 := by simp
  have h5 : (n : ℂ) ^ s ≠ 0 := by simp [hn']
  field_simp

end ModularForm
