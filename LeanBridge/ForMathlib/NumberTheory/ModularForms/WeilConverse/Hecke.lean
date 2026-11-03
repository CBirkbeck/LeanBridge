import LeanBridge.ForMathlib.NumberTheory.ModularForms.WeilConverse.ExponentialSum
import LeanBridge.ForMathlib.NumberTheory.ModularForms.WeilConverse.HeckePoles
import LeanBridge.ForMathlib.NumberTheory.ModularForms.WeilConverse.VerticalStrip
import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.ModularForms.Basic
import TauCeti.NumberTheory.ModularForms.LFunction.FunctionalEquation

/-!
# Hecke's lemma: from a functional equation to a transformation law

Let `c, d` be sequences of polynomial growth, with constant terms `c₀` and `d₀`. Suppose that the
completed Dirichlet series `Λ` of `c` continues to `E(s) - c₀ / s - R / (κ - s)`, with `E` entire
and bounded on vertical strips and `R = ε N ^ (-κ / 2) d₀`, and that
`Λ(s) = ε N ^ (κ / 2 - s) Λ'(κ - s)`, where `Λ'` is the completed Dirichlet series of `d`. Then the
exponential sums `F` of `c` and `G` of `d` are related by the Fricke involution:
`F ∣[κ] W_N = ε i ^ (-κ) N ^ (κ / 2 - 1) G`. The proof is Mellin inversion, a shift of the line of
integration from `Re s = σ` to `Re s = κ - σ`, the functional equation, and the identity principle
on the imaginary axis. The poles are treated by Perron's formula, and the vertical decay of the
completed series comes from the bound on `Γ` on a vertical line, without Stirling's formula. The
function `E` only decays like `1 / |Im s|` on vertical strips, because of the poles, so the
integrals of the shift are truncated.

## Main definitions

* `ModularForm.addPoles`: the function `E(s) - c₀ / s - R / (κ - s)`.

## Main results

* `ModularForm.exists_norm_completedLSeries_le`: a completed Dirichlet series decays on a vertical
  line of absolute convergence.
* `ModularForm.resToImagAxis_expSum_eq_of_functional_equation`: Hecke's lemma on the imaginary axis.
* `ModularForm.eq_of_resToImagAxis_eq`: the identity principle on the imaginary axis.
* `ModularForm.expSum_slash_frickeGL_eq_of_functional_equation`: Hecke's lemma.

## References

* E. Hecke, *Über die Bestimmung Dirichletscher Reihen durch ihre Funktionalgleichung*, Math. Ann.
  112 (1936), 664–699.
-/

open Complex Filter Function Topology Set MeasureTheory TauCeti

open scoped Real Manifold ModularForm

open UpperHalfPlane hiding I I_re I_im

namespace ModularForm

/-- The function `E(s) - c₀ / s - R / (κ - s)`, for an entire function `E`: the shape of a completed
Dirichlet series with constant term `c₀`, with simple poles at `0` and at the weight `κ`. -/
noncomputable def addPoles (E : ℂ → ℂ) (c₀ R : ℂ) (κ : ℤ) (s : ℂ) : ℂ :=
  E s - c₀ / s - R / (κ - s)

variable {c d : ℕ → ℂ} {σ A y a b : ℝ} {s : ℂ}

/-- A completed Dirichlet series decays on a vertical line of absolute convergence. -/
lemma exists_norm_completedLSeries_le (hσ : 1 ≤ σ) (hL : LSeriesSummable c σ) :
    ∃ K : ℝ, ∀ s : ℂ, s.re = σ → ‖completedLSeries c s‖ ≤ K / (1 + s.im ^ 2) := by
  have hσ0 : 0 < σ := by linarith
  refine ⟨(2 * π) ^ (-σ) * Real.Gamma (σ + 2) * ∑' n : ℕ, ‖LSeries.term c σ n‖, fun s hs ↦ ?_⟩
  have hre : (0 : ℝ) < s.re := hs ▸ hσ0
  have hnorm : ∀ n : ℕ, ‖LSeries.term c s n‖ = ‖LSeries.term c σ n‖ := fun n ↦ by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hs]
    simp
  have hL' : Summable fun n : ℕ ↦ ‖LSeries.term c s n‖ := by
    simpa only [hnorm] using hL.norm
  have h1 : ‖LSeries c s‖ ≤ ∑' n : ℕ, ‖LSeries.term c σ n‖ := by
    simp only [← hnorm]
    exact norm_tsum_le_tsum_norm hL'
  have h2 : ‖(2 * π : ℂ) ^ (-s)‖ = (2 * π) ^ (-σ) := by
    have h3 : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
    rw [h3, norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re, hs]
  have h4 : 1 + s.im ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    have h5 : ‖s‖ ≤ ‖s + 1‖ := by
      refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
      rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
      simp only [add_re, one_re, add_im, one_im]
      nlinarith
    have h6 : ‖s‖ * ‖s‖ = s.re ^ 2 + s.im ^ 2 := by
      rw [← sq, ← normSq_eq_norm_sq, normSq_apply]
      ring1
    have h7 : 1 ≤ s.re ^ 2 := by
      rw [hs]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h5 (norm_nonneg s)]
  have h8 : ‖Gamma s‖ ≤ Real.Gamma (σ + 2) / (1 + s.im ^ 2) := by
    have h9 : ‖Gamma s‖ ≤ Real.Gamma (s.re + 2) / (‖s‖ * ‖s + 1‖) := norm_Gamma_le_div hre
    rw [hs] at h9
    refine h9.trans (div_le_div_of_nonneg_left ?_ (by positivity) h4)
    exact (Real.Gamma_pos_of_pos (by linarith)).le
  rw [completedLSeries, norm_mul, norm_mul, h2]
  have h10 : 0 ≤ ∑' n : ℕ, ‖LSeries.term c σ n‖ := tsum_nonneg fun n ↦ norm_nonneg _
  have h11 : 0 ≤ Real.Gamma (σ + 2) / (1 + s.im ^ 2) := (norm_nonneg _).trans h8
  refine (mul_le_mul (mul_le_mul_of_nonneg_left h8 (by positivity)) h1 (norm_nonneg _)
    (by positivity)).trans_eq ?_
  ring1

private lemma cpow_identity (hy : 0 < y) (hA : 0 < A) (κ w : ℂ) : (y : ℂ) ^ (-(κ - w)) *
    (A : ℂ) ^ (κ / 2 - (κ - w)) =
      (y : ℂ) ^ (-κ) * (A : ℂ) ^ (-κ / 2) * ((1 / (A * y) : ℝ) : ℂ) ^ (-w) := by
  have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have hAc : (A : ℂ) ≠ 0 := ofReal_ne_zero.mpr hA.ne'
  have hAy : 0 < A * y := mul_pos hA hy
  have h1 : ((1 / (A * y) : ℝ) : ℂ) ^ (-w) = (A : ℂ) ^ w * (y : ℂ) ^ w := by
    have h2 : ((1 / (A * y) : ℝ) : ℂ) = ((A * y : ℝ) : ℂ)⁻¹ := by
      rw [one_div, ofReal_inv]
    have harg : ((A * y : ℝ) : ℂ).arg ≠ π := by
      rw [arg_ofReal_of_nonneg hAy.le]
      exact Real.pi_pos.ne
    rw [h2, inv_cpow _ _ harg, cpow_neg, inv_inv, ofReal_mul,
      mul_cpow_ofReal_nonneg hA.le hy.le]
  have h3 : -(κ - w) = -κ + w := by ring1
  have h4 : κ / 2 - (κ - w) = -κ / 2 + w := by ring1
  rw [h1, h3, h4, cpow_add _ _ hyc, cpow_add _ _ hAc]
  ring1

private lemma norm_ofReal_cpow_neg_le (hy : 0 < y) (h1 : a ≤ s.re) (h2 : s.re ≤ b) :
    ‖(y : ℂ) ^ (-s)‖ ≤ y ^ (-a) + y ^ (-b) := by
  rw [norm_cpow_eq_rpow_re_of_pos hy, neg_re]
  have ha : 0 ≤ y ^ (-a) := (Real.rpow_pos_of_pos hy _).le
  have hb : 0 ≤ y ^ (-b) := (Real.rpow_pos_of_pos hy _).le
  rcases le_total 1 y with h | h
  · have h3 : y ^ (-s.re) ≤ y ^ (-a) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    linarith
  · have h3 : y ^ (-s.re) ≤ y ^ (-b) := Real.rpow_le_rpow_of_exponent_ge hy h (by linarith)
    linarith

variable {E : ℂ → ℂ} {κ : ℤ} {ε c₀ R : ℂ} {C D K σ₀ : ℝ} {m : ℕ}

private lemma continuous_completedLSeries_vertical (hC : ∀ n : ℕ, n ≠ 0 → ‖c n‖ ≤ C * (n : ℝ) ^ m)
    (hσ : (m : ℝ) + 2 < σ) : Continuous fun t : ℝ ↦ completedLSeries c (σ + t * I) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hre : ∀ t : ℝ, (σ + t * I : ℂ).re = σ := fun t ↦ by simp
  have hline : Continuous fun t : ℝ ↦ (σ + t * I : ℂ) := by fun_prop
  have habs : LSeries.abscissaOfAbsConv c ≤ ((m : ℝ) + 1 : ℝ) := by
    refine LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow ⟨C, fun n hn ↦ ?_⟩
    rw [Real.rpow_natCast]
    exact hC n hn
  have hL : Continuous fun t : ℝ ↦ LSeries c (σ + t * I) := by
    refine (LSeries_differentiableOn c).continuousOn.comp_continuous hline fun t ↦ ?_
    have h1 : (m : ℝ) + 1 < (σ + t * I : ℂ).re := by
      rw [hre t]
      linarith
    exact lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr h1)
  have hG : Continuous fun t : ℝ ↦ Gamma (σ + t * I) := by
    refine continuous_iff_continuousAt.mpr fun t ↦ ContinuousAt.comp
      (differentiableAt_Gamma _ fun n hn ↦ ?_).continuousAt hline.continuousAt
    have h1 : (σ + t * I : ℂ).re = -(n : ℝ) := by
      rw [hn]
      simp
    rw [hre t] at h1
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hP : Continuous fun t : ℝ ↦ (2 * π : ℂ) ^ (-(σ + t * I : ℂ)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl (by simp))
  exact (hP.mul hG).mul hL

private lemma resToImagAxis_expSum_sub_eq_integral (hC : ∀ n : ℕ, n ≠ 0 → ‖c n‖ ≤ C * (n : ℝ) ^ m)
    (hσ : (m : ℝ) + 2 < σ) (hint : Integrable fun t : ℝ ↦ completedLSeries c (σ + t * I)) {x : ℝ}
    (hx : 0 < x) : resToImagAxis (expSum c) x - c 0 =
      (1 / (2 * π)) • ∫ t : ℝ, (x : ℂ) ^ (-(σ + t * I)) * completedLSeries c (σ + t * I) := by
  have hc : HasPolyGrowth c := ⟨C, m, hC⟩
  have hC' : ∀ n : ℕ, n ≠ 0 → ‖update c 0 0 n‖ ≤ C * (n : ℝ) ^ m := fun n hn ↦ by
    rw [update_of_ne hn]
    exact hC n hn
  have hre : ∀ t : ℝ, (σ + t * I : ℂ).re = σ := fun t ↦ by simp
  have heq : ∀ t : ℝ, mellin (resToImagAxis (expSum (update c 0 0))) (σ + t * I) =
      completedLSeries c (σ + t * I) := fun t ↦
    (mellin_resToImagAxis_expSum hC' (update_self _ _ _) (by rw [hre]; exact hσ)).trans
      completedLSeries_update
  have hMC : MellinConvergent (resToImagAxis (expSum (update c 0 0))) σ :=
    mellinConvergent_resToImagAxis_expSum hC' (update_self _ _ _) (by simpa using hσ)
  have hVI : VerticalIntegrable (mellin (resToImagAxis (expSum (update c 0 0)))) σ := by
    rw [VerticalIntegrable]
    simpa only [heq] using hint
  have hcont : ContinuousAt (resToImagAxis (expSum (update c 0 0))) x :=
    hc.update_zero.continuousOn_resToImagAxis.continuousAt (Ioi_mem_nhds hx)
  have h1 : mellinInv σ (mellin (resToImagAxis (expSum (update c 0 0)))) x =
      resToImagAxis (expSum (update c 0 0)) x :=
    mellinInv_mellin_eq σ _ hx hMC hVI hcont
  rw [mellinInv] at h1
  simp only [heq, smul_eq_mul] at h1
  rw [h1, resToImagAxis_of_pos _ hx, resToImagAxis_of_pos _ hx, expSum_eq_add_expSum_update hc]
  ring1

private lemma norm_add_ofReal_div_le {w : ℂ} (hw : 1 ≤ |w.re|) (x : ℝ) :
    ‖(w + x) / w‖ ≤ 1 + |x| := by
  have h1 : 1 ≤ ‖w‖ := hw.trans (abs_re_le_norm w)
  have h0 : w ≠ 0 := norm_pos_iff.mp (by linarith)
  have e : (w + x) / w = 1 + x / w := by
    field_simp
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_one, norm_div, norm_real, Real.norm_eq_abs]
  have h2 : |x| / ‖w‖ ≤ |x| := div_le_self (abs_nonneg x) h1
  linarith

private lemma norm_mul_norm_le_of_addPoles (h1 : a ≤ s.re) (h2 : s.re ≤ b) (h3 : 1 ≤ |s.re|)
    (h4 : 1 ≤ |(κ : ℝ) - s.re|) (h5 : ‖addPoles E c₀ R κ s‖ ≤ K / (1 + s.im ^ 2)) : ‖s - a + 1‖ *
      ‖E s‖ ≤ ((b - a + 1) ^ 2 + 1) * K + ‖c₀‖ * (1 + |1 - a|) +
        ‖R‖ * (1 + |-((κ : ℝ) - a + 1)|) := by
  have h6 : ‖s - a + 1‖ * ‖addPoles E c₀ R κ s‖ ≤ ((b - a + 1) ^ 2 + 1) * K :=
    norm_sub_add_one_mul_le h1 h2 (norm_nonneg _) h5
  have h7 : ‖(s - a + 1) / s‖ ≤ 1 + |1 - a| := by
    have e : s - a + 1 = s + ((1 - a : ℝ) : ℂ) := by
      push_cast
      ring1
    rw [e]
    exact norm_add_ofReal_div_le h3 _
  have h8 : ‖(s - a + 1) / ((κ : ℂ) - s)‖ ≤ 1 + |-((κ : ℝ) - a + 1)| := by
    have e : (s - a + 1) / ((κ : ℂ) - s) =
        -((((κ : ℂ) - s) + ((-((κ : ℝ) - a + 1) : ℝ) : ℂ)) / ((κ : ℂ) - s)) := by
      rw [← neg_div]
      congr 1
      push_cast
      ring1
    have h9 : 1 ≤ |((κ : ℂ) - s).re| := by
      simpa using h4
    rw [e, norm_neg]
    exact norm_add_ofReal_div_le h9 _
  have e : (s - a + 1) * E s = (s - a + 1) * addPoles E c₀ R κ s + c₀ * ((s - a + 1) / s) +
      R * ((s - a + 1) / ((κ : ℂ) - s)) := by
    rw [addPoles]
    ring1
  rw [← norm_mul, e]
  refine (norm_add₃_le).trans ?_
  rw [norm_mul, norm_mul, norm_mul]
  exact add_le_add (add_le_add h6 (mul_le_mul_of_nonneg_left h7 (norm_nonneg _)))
    (mul_le_mul_of_nonneg_left h8 (norm_nonneg _))

private lemma intervalIntegral_cpow_mul_addPoles (hE : Differentiable ℂ E) (hy : 0 < y) {w : ℝ}
    (hw : w ≠ 0) (hwκ : w ≠ κ) (T : ℝ) : ∫ t in -T..T, (y : ℂ) ^ (-((w : ℂ) + t * I)) *
      addPoles E c₀ R κ (w + t * I) =
        (∫ t in -T..T, (y : ℂ) ^ (-((w : ℂ) + t * I)) * E (w + t * I)) -
          c₀ * (∫ t in -T..T, (y : ℂ) ^ (-((w : ℂ) + t * I)) / ((w : ℂ) + t * I)) -
            R * ∫ t in -T..T, (y : ℂ) ^ (-((w : ℂ) + t * I)) /
              (((κ : ℝ) : ℂ) - ((w : ℂ) + t * I)) := by
  have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have hc₁ : Continuous fun t : ℝ ↦ (y : ℂ) ^ (-((w : ℂ) + t * I)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl hyc)
  have hne₁ : ∀ t : ℝ, (w : ℂ) + t * I ≠ 0 := fun t h ↦ hw (by simpa using congrArg Complex.re h)
  have hne₂ : ∀ t : ℝ, ((κ : ℝ) : ℂ) - ((w : ℂ) + t * I) ≠ 0 := fun t h ↦
    hwκ (by simpa [sub_eq_zero, eq_comm] using congrArg Complex.re h)
  have hi₁ : IntervalIntegrable (fun t : ℝ ↦ (y : ℂ) ^ (-((w : ℂ) + t * I)) * E (w + t * I)) volume
      (-T) T :=
    (hc₁.mul (hE.continuous.comp (by fun_prop))).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun t : ℝ ↦ c₀ * ((y : ℂ) ^ (-((w : ℂ) + t * I)) /
      ((w : ℂ) + t * I))) volume (-T) T :=
    ((hc₁.div (by fun_prop) hne₁).const_mul c₀).intervalIntegrable _ _
  have hi₃ : IntervalIntegrable (fun t : ℝ ↦ R * ((y : ℂ) ^ (-((w : ℂ) + t * I)) /
      (((κ : ℝ) : ℂ) - ((w : ℂ) + t * I)))) volume (-T) T :=
    ((hc₁.div (by fun_prop) hne₂).const_mul R).intervalIntegrable _ _
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub hi₁ hi₂, ← intervalIntegral.integral_sub (hi₁.sub hi₂) hi₃]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  simp only [addPoles]
  push_cast
  ring1

/-- **Hecke's lemma on the imaginary axis.** Let `c, d` be sequences of polynomial growth, `κ > 0`,
and let `E` be entire and bounded on vertical strips. Put `R = ε A ^ (-κ / 2) d₀` and
`Λ(s) = E(s) - c₀ / s - R / (κ - s)`. If `Λ` agrees with the completed Dirichlet series of `c` on a
right half plane and `Λ(s) = ε A ^ (κ / 2 - s) Λ'(κ - s)` on a left half plane, where `Λ'` is the
completed Dirichlet series of `d`, the exponential sums satisfy
`φ_c(y) = ε A ^ (-κ / 2) y ^ (-κ) φ_d(1 / (A y))` for `y > 0`. The proof is Mellin inversion and the
shift of the line of integration from `Re s = σ` to `Re s = κ - σ`, across the poles. -/
lemma resToImagAxis_expSum_eq_of_functional_equation (hC : ∀ n : ℕ, n ≠ 0 → ‖c n‖ ≤ C * (n : ℝ) ^ m)
    (hD : ∀ n : ℕ, n ≠ 0 → ‖d n‖ ≤ D * (n : ℝ) ^ m) (hκ : 0 < κ) (hA : 0 < A)
    (hE : Differentiable ℂ E) (hbd : ∀ a b : ℝ, ∃ M : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖E s‖ ≤ M)
    (hΛc : ∀ s : ℂ, σ₀ < s.re →
      completedLSeries c s = addPoles E (c 0) (ε * (A : ℂ) ^ (-(κ : ℂ) / 2) * d 0) κ s)
    (hΛd : ∀ s : ℂ, s.re < κ - σ₀ → addPoles E (c 0) (ε * (A : ℂ) ^ (-(κ : ℂ) / 2) * d 0) κ s =
      ε * (A : ℂ) ^ ((κ : ℂ) / 2 - s) * completedLSeries d (κ - s)) (hy : 0 < y) :
    resToImagAxis (expSum c) y = ε * ((y : ℂ) ^ (-(κ : ℂ)) * (A : ℂ) ^ (-(κ : ℂ) / 2)) *
      resToImagAxis (expSum d) (1 / (A * y)) := by
  let σ : ℝ := max ((m : ℝ) + 3) (max (σ₀ + 1) ((κ : ℝ) + 1))
  let a : ℝ := (κ : ℝ) - σ
  let R : ℂ := ε * (A : ℂ) ^ (-(κ : ℂ) / 2) * d 0
  have h1 : (m : ℝ) + 3 ≤ σ := le_max_left _ _
  have h2 : σ₀ + 1 ≤ σ := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : (κ : ℝ) + 1 ≤ σ := (le_max_right _ _).trans (le_max_right _ _)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hκ1 : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hσ1 : 1 ≤ σ := by linarith
  have hσm : (m : ℝ) + 2 < σ := by linarith
  have hab : a < σ := by simp only [a]; linarith
  have ha1 : a ≤ -1 := by simp only [a]; linarith
  have hsum : ∀ {e : ℕ → ℂ} {B : ℝ}, (∀ n : ℕ, n ≠ 0 → ‖e n‖ ≤ B * (n : ℝ) ^ m) →
      LSeriesSummable e (σ : ℂ) := fun {e B} hB ↦
    LSeriesSummable_of_le_const_mul_rpow (x := (m : ℝ) + 1) (by simp; linarith) ⟨B, fun n hn ↦ by
      rw [add_sub_cancel_right, Real.rpow_natCast]
      exact hB n hn⟩
  rcases exists_norm_completedLSeries_le hσ1 (hsum hC) with ⟨K₁, hK₁⟩
  rcases exists_norm_completedLSeries_le hσ1 (hsum hD) with ⟨K₂, hK₂⟩
  let P : ℝ := ‖ε‖ * A ^ ((κ : ℝ) / 2 - a)
  have hP : 0 ≤ P := by positivity
  have hright : ∀ s : ℂ, s.re = σ → ‖addPoles E (c 0) R κ s‖ ≤ K₁ / (1 + s.im ^ 2) := fun s hs ↦ by
    rw [← hΛc s (by rw [hs]; linarith)]
    exact hK₁ s hs
  have hleft : ∀ s : ℂ, s.re = a → ‖addPoles E (c 0) R κ s‖ ≤ P * K₂ / (1 + s.im ^ 2) := by
    intro s hs
    have h4 : ((κ : ℂ) - s).re = σ := by
      simp [hs, a]
    have h5 : ((κ : ℂ) - s).im = -s.im := by simp
    have h6 : ‖completedLSeries d ((κ : ℂ) - s)‖ ≤ K₂ / (1 + ((κ : ℂ) - s).im ^ 2) := hK₂ _ h4
    rw [h5, neg_sq] at h6
    have h7 : ((κ : ℂ) / 2 - s).re = (κ : ℝ) / 2 - a := by
      simp [hs]
    rw [hΛd s (by rw [hs]; simp only [a]; linarith), norm_mul, norm_mul,
      norm_cpow_eq_rpow_re_of_pos hA, h7, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h6 hP
  rcases hbd a σ with ⟨M, hM⟩
  let B : ℝ := ((σ - a + 1) ^ 2 + 1) * max K₁ (P * K₂) + ‖c 0‖ * (1 + |1 - a|) +
    ‖R‖ * (1 + |-((κ : ℝ) - a + 1)|)
  have hedge : ∀ K : ℝ, K ≤ max K₁ (P * K₂) → ∀ s : ℂ, a ≤ s.re → s.re ≤ σ → 1 ≤ |s.re| →
      1 ≤ |(κ : ℝ) - s.re| → ‖addPoles E (c 0) R κ s‖ ≤ K / (1 + s.im ^ 2) →
        ‖s - a + 1‖ * ‖E s‖ ≤ B := fun K hK s h4 h5 h6 h7 h8 ↦
    norm_mul_norm_le_of_addPoles h4 h5 h6 h7
      (h8.trans (div_le_div_of_nonneg_right hK (by positivity)))
  have hdecay : ∀ s : ℂ, a ≤ s.re → s.re ≤ σ → ‖E s‖ * |s.im| ≤ B := fun s h4 h5 ↦ by
    refine norm_mul_abs_im_le_of_strip hE hab hM (fun z hz ↦ ?_) (fun z hz ↦ ?_) h4 h5
    · refine hedge _ (le_max_right _ _) z hz.ge (by linarith) ?_ ?_ (hleft z hz)
      · rw [hz, abs_of_neg (by linarith)]
        linarith
      · rw [hz]
        simp only [a]
        rw [sub_sub_cancel, abs_of_pos (by linarith)]
        exact hσ1
    · refine hedge _ (le_max_left _ _) z (by linarith) hz.le ?_ ?_ (hright z hz)
      · rw [hz, abs_of_pos (by linarith)]
        exact hσ1
      · rw [hz, abs_of_neg (by linarith)]
        linarith
  have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have hH : Differentiable ℂ fun s : ℂ ↦ (y : ℂ) ^ (-s) * E s :=
    (differentiable_id.neg.const_cpow (Or.inl hyc)).mul hE
  have hHdec :
      ∀ s : ℂ, a ≤ s.re → s.re ≤ σ → ‖(y : ℂ) ^ (-s) * E s‖ * |s.im| ≤ (y ^ (-a) + y ^ (-σ)) * B :=
    fun s h4 h5 ↦ by
      have h6 : 0 ≤ y ^ (-a) + y ^ (-σ) := (norm_nonneg _).trans (norm_ofReal_cpow_neg_le hy h4 h5)
      rw [norm_mul, mul_assoc]
      exact mul_le_mul (norm_ofReal_cpow_neg_le hy h4 h5) (hdecay s h4 h5) (by positivity) h6
  have hshift : Tendsto (fun T : ℝ ↦
      (∫ t in -T..T, (y : ℂ) ^ (-((σ : ℂ) + t * I)) * E (σ + t * I)) -
        ∫ t in -T..T, (y : ℂ) ^ (-((a : ℂ) + t * I)) * E (a + t * I)) atTop (𝓝 0) :=
    tendsto_sub_intervalIntegral_vertical hH hab.le hHdec
  have ha0 : a ≠ 0 := by linarith
  have haκ : a ≠ κ := by linarith
  have hσ0 : σ ≠ 0 := by linarith
  have hσκ : σ ≠ κ := by linarith
  have hlim₁ : Tendsto (fun T : ℝ ↦ (∫ t in -T..T, (y : ℂ) ^ (-((σ : ℂ) + t * I)) *
      addPoles E (c 0) R κ (σ + t * I)) - ∫ t in -T..T, (y : ℂ) ^ (-((a : ℂ) + t * I)) *
        addPoles E (c 0) R κ (a + t * I)) atTop
      (𝓝 (0 - c 0 * ((2 * π : ℝ) : ℂ) -
        R * (-(y : ℂ) ^ (-((κ : ℝ) : ℂ)) * ((2 * π : ℝ) : ℂ)))) := by
    refine ((hshift.sub ((tendsto_sub_integral_cpow_div hy (a := a) (b := σ) (by linarith)
      (by linarith)).const_mul (c 0))).sub ((tendsto_sub_integral_cpow_div_sub hy (x := (κ : ℝ))
        (a := a) (b := σ) (by linarith) (by linarith)).const_mul R)).congr fun T ↦ ?_
    rw [intervalIntegral_cpow_mul_addPoles hE hy hσ0 hσκ, intervalIntegral_cpow_mul_addPoles hE hy
      ha0 haκ]
    ring1
  have hx : 0 < 1 / (A * y) := by positivity
  have hintc : Integrable fun t : ℝ ↦ completedLSeries c (σ + t * I) :=
    integrable_vertical_of_decay (continuous_completedLSeries_vertical hC hσm) hK₁
  have hintd : Integrable fun t : ℝ ↦ completedLSeries d (σ + t * I) :=
    integrable_vertical_of_decay (continuous_completedLSeries_vertical hD hσm) hK₂
  have hic : resToImagAxis (expSum c) y - c 0 =
      (1 / (2 * π)) • ∫ t : ℝ, (y : ℂ) ^ (-(σ + t * I)) * completedLSeries c (σ + t * I) :=
    resToImagAxis_expSum_sub_eq_integral hC hσm hintc hy
  have hid : resToImagAxis (expSum d) (1 / (A * y)) - d 0 = (1 / (2 * π)) •
      ∫ t : ℝ, ((1 / (A * y) : ℝ) : ℂ) ^ (-(σ + t * I)) * completedLSeries d (σ + t * I) :=
    resToImagAxis_expSum_sub_eq_integral hD hσm hintd hx
  have hvert : ∀ {e : ℕ → ℂ} {x : ℝ}, 0 < x →
      Integrable (fun t : ℝ ↦ completedLSeries e (σ + t * I)) →
        Integrable fun t : ℝ ↦ (x : ℂ) ^ (-(σ + t * I)) * completedLSeries e (σ + t * I) :=
    fun {e x} hx₀ he ↦ by
      refine he.bdd_mul (c := x ^ (-σ)) (Continuous.aestronglyMeasurable
        (Continuous.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr hx₀.ne'))))
        (Eventually.of_forall fun t ↦ ?_)
      rw [norm_cpow_eq_rpow_re_of_pos hx₀]
      simp
  have hre : ∀ x t : ℝ, ((x : ℂ) + t * I).re = x := fun x t ↦ by simp
  have hline : ∀ t : ℝ, (y : ℂ) ^ (-(σ + t * I)) * addPoles E (c 0) R κ (σ + t * I) =
      (y : ℂ) ^ (-(σ + t * I)) * completedLSeries c (σ + t * I) := fun t ↦ by
    rw [hΛc _ (by rw [hre]; linarith)]
  have hleftline : ∀ t : ℝ, (y : ℂ) ^ (-((a : ℂ) + t * I)) * addPoles E (c 0) R κ (a + t * I) =
      ε * ((y : ℂ) ^ (-(κ : ℂ)) * (A : ℂ) ^ (-(κ : ℂ) / 2)) *
        (((1 / (A * y) : ℝ) : ℂ) ^ (-(σ + ((-t : ℝ) : ℂ) * I)) *
          completedLSeries d (σ + ((-t : ℝ) : ℂ) * I)) := fun t ↦ by
    have e1 : ((a : ℂ) + t * I) = (κ : ℂ) - (σ + ((-t : ℝ) : ℂ) * I) := by
      simp only [a]
      push_cast
      ring1
    have e2 : (κ : ℂ) - ((κ : ℂ) - (σ + ((-t : ℝ) : ℂ) * I)) = σ + ((-t : ℝ) : ℂ) * I := by ring1
    rw [hΛd _ (by rw [hre]; simp only [a]; linarith), e1, e2]
    linear_combination (norm := skip) (ε * completedLSeries d (σ + ((-t : ℝ) : ℂ) * I)) *
      cpow_identity hy hA (κ : ℂ) (σ + ((-t : ℝ) : ℂ) * I)
    ring1
  have hinta :
      Integrable fun t : ℝ ↦ (y : ℂ) ^ (-((a : ℂ) + t * I)) * addPoles E (c 0) R κ (a + t * I) := by
    simp only [hleftline]
    exact ((hvert hx hintd).comp_neg).const_mul _
  have hints :
      Integrable fun t : ℝ ↦ (y : ℂ) ^ (-(σ + t * I)) * addPoles E (c 0) R κ (σ + t * I) := by
    simp only [hline]
    exact hvert hy hintc
  have hlim₂ : Tendsto (fun T : ℝ ↦ (∫ t in -T..T, (y : ℂ) ^ (-((σ : ℂ) + t * I)) *
      addPoles E (c 0) R κ (σ + t * I)) - ∫ t in -T..T, (y : ℂ) ^ (-((a : ℂ) + t * I)) *
        addPoles E (c 0) R κ (a + t * I)) atTop
      (𝓝 ((∫ t : ℝ, (y : ℂ) ^ (-(σ + t * I)) * addPoles E (c 0) R κ (σ + t * I)) -
        ∫ t : ℝ, (y : ℂ) ^ (-((a : ℂ) + t * I)) * addPoles E (c 0) R κ (a + t * I))) :=
    (intervalIntegral_tendsto_integral hints tendsto_neg_atTop_atBot tendsto_id).sub
      (intervalIntegral_tendsto_integral hinta tendsto_neg_atTop_atBot tendsto_id)
  have hlim : (∫ t : ℝ, (y : ℂ) ^ (-(σ + t * I)) * addPoles E (c 0) R κ (σ + t * I)) -
      ∫ t : ℝ, (y : ℂ) ^ (-((a : ℂ) + t * I)) * addPoles E (c 0) R κ (a + t * I) =
        0 - c 0 * ((2 * π : ℝ) : ℂ) - R * (-(y : ℂ) ^ (-((κ : ℝ) : ℂ)) * ((2 * π : ℝ) : ℂ)) :=
    tendsto_nhds_unique hlim₂ hlim₁
  have hright' : ∫ t : ℝ, (y : ℂ) ^ (-(σ + t * I)) * addPoles E (c 0) R κ (σ + t * I) =
      ∫ t : ℝ, (y : ℂ) ^ (-(σ + t * I)) * completedLSeries c (σ + t * I) := by
    simp only [hline]
  have hleft' : ∫ t : ℝ, (y : ℂ) ^ (-((a : ℂ) + t * I)) * addPoles E (c 0) R κ (a + t * I) =
      ε * ((y : ℂ) ^ (-(κ : ℂ)) * (A : ℂ) ^ (-(κ : ℂ) / 2)) *
        ∫ t : ℝ, ((1 / (A * y) : ℝ) : ℂ) ^ (-(σ + t * I)) * completedLSeries d (σ + t * I) := by
    rw [← integral_neg_eq_self (fun t : ℝ ↦ ((1 / (A * y) : ℝ) : ℂ) ^ (-(σ + t * I)) *
      completedLSeries d (σ + t * I)), ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hleftline)
  rw [hright', hleft'] at hlim
  have hX : ((1 / (2 * π) : ℝ) : ℂ) * ((2 * π : ℝ) : ℂ) = 1 := by
    rw [← ofReal_mul, one_div, inv_mul_cancel₀ (by positivity), ofReal_one]
  rw [real_smul] at hic hid
  rw [ofReal_intCast] at hlim
  simp only [R] at hlim
  linear_combination hic - ε * ((y : ℂ) ^ (-(κ : ℂ)) * (A : ℂ) ^ (-(κ : ℂ) / 2)) * hid +
    ((1 / (2 * π) : ℝ) : ℂ) * hlim + (-c 0 + ε * (A : ℂ) ^ (-(κ : ℂ) / 2) * d 0 *
      (y : ℂ) ^ (-(κ : ℂ))) * hX

/-- **The identity principle on the imaginary axis**: holomorphic functions on `ℍ` that agree on the
imaginary axis are equal. -/
lemma eq_of_resToImagAxis_eq {f g : ℍ → ℂ} (hf : MDiff f) (hg : MDiff g)
    (h : ∀ t : ℝ, 0 < t → resToImagAxis f t = resToImagAxis g t) : f = g := by
  have hIm : ∀ t : ℝ, 0 < t → 0 < (I * t : ℂ).im := fun t ht ↦ by simpa using ht
  have hcont : ContinuousAt (fun t : ℝ ↦ ofComplex (I * t)) 1 := by
    have h1 : ContinuousAt (ofComplex : ℂ → ℍ) (I * ((1 : ℝ) : ℂ)) :=
      contMDiffAt_ofComplex (n := 0) (hIm 1 one_pos) |>.continuousAt
    exact ContinuousAt.comp (f := fun t : ℝ ↦ (I * t : ℂ)) h1 (by fun_prop)
  have hval : ∀ t : ℝ, 0 < t → ((ofComplex (I * t) : ℍ) : ℂ) = I * t := fun t ht ↦ by
    rw [ofComplex_apply_of_im_pos (hIm t ht)]
  have hu :
      Tendsto (fun t : ℝ ↦ ofComplex (I * t)) (𝓝[≠] 1) (𝓝[≠] (ofComplex (I * ((1 : ℝ) : ℂ)))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hcont.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)] with
      t ht ht0
    intro heq
    have h2 : ((ofComplex (I * t) : ℍ) : ℂ) = (ofComplex (I * ((1 : ℝ) : ℂ)) : ℍ) :=
      congrArg (fun z : ℍ ↦ (z : ℂ)) heq
    simp only [hval t ht0, hval 1 one_pos] at h2
    have h3 : (t : ℂ) = ((1 : ℝ) : ℂ) := mul_left_cancel₀ I_ne_zero h2
    exact ht (ofReal_injective h3)
  have hfreq : ∃ᶠ t : ℝ in 𝓝[≠] 1, (f - g) (ofComplex (I * t)) = 0 := by
    refine Eventually.frequently ?_
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)] with t ht
    have ht0 : 0 < t := ht
    have h2 : resToImagAxis f t = resToImagAxis g t := h t ht0
    rw [resToImagAxis_of_pos _ ht0, resToImagAxis_of_pos _ ht0] at h2
    have h3 : ofComplex (I * t) = ⟨I * t, hIm t ht0⟩ := ofComplex_apply_of_im_pos (hIm t ht0)
    rw [h3, Pi.sub_apply, sub_eq_zero]
    exact h2
  have h0 : f - g = 0 := UpperHalfPlane.eq_zero_of_frequently (MDifferentiable.sub hf hg)
    (hu.frequently hfreq)
  exact sub_eq_zero.mp h0

variable (κ) in
lemma natCast_cpow_div_two_eq (N : ℕ) : (N : ℂ) ^ ((κ : ℂ) / 2) = ((Real.sqrt N : ℝ) : ℂ) ^ κ := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow hN, ofReal_natCast]
  rw [h1, ← cpow_int_mul]
  congr 1
  push_cast
  ring1

variable {N : ℕ} [NeZero N]

variable (N κ) in
lemma natCast_cpow_div_two_sub_one :
    (N : ℂ) ^ ((κ : ℂ) / 2 - 1) = ((Real.sqrt N : ℝ) : ℂ) ^ (κ - 2) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hQ : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  have hNc : (N : ℂ) = ((Real.sqrt N : ℝ) : ℂ) ^ 2 := by
    rw [sq, ← ofReal_mul, Real.mul_self_sqrt hN.le, ofReal_natCast]
  rw [cpow_sub _ _ (Nat.cast_ne_zero.mpr (NeZero.ne N)), natCast_cpow_div_two_eq, cpow_one,
    zpow_sub₀ hQ, ← hNc.symm]
  rfl

/-- **Hecke's lemma.** Let `c, d` be sequences of polynomial growth, `κ > 0`, and let `E` be entire
and bounded on vertical strips. Put `R = ε N ^ (-κ / 2) d₀` and
`Λ(s) = E(s) - c₀ / s - R / (κ - s)`. If `Λ` agrees with the completed Dirichlet series of `c` on a
right half plane and `Λ(s) = ε N ^ (κ / 2 - s) Λ'(κ - s)` on a left half plane, where `Λ'` is the
completed Dirichlet series of `d`, the exponential sums `F` of `c` and `G` of `d` satisfy
`F ∣[κ] W_N = ε i ^ (-κ) N ^ (κ / 2 - 1) G`, that is,
`F(-1 / (N z)) = ε i ^ (-κ) N ^ (κ / 2) z ^ κ G(z)`. -/
lemma expSum_slash_frickeGL_eq_of_functional_equation (hc : HasPolyGrowth c) (hd : HasPolyGrowth d)
    (hκ : 0 < κ) (hE : Differentiable ℂ E)
    (hbd : ∀ a b : ℝ, ∃ M : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖E s‖ ≤ M)
    (hΛc : ∀ s : ℂ, σ₀ < s.re →
      completedLSeries c s = addPoles E (c 0) (ε * (N : ℂ) ^ (-(κ : ℂ) / 2) * d 0) κ s)
    (hΛd : ∀ s : ℂ, s.re < κ - σ₀ → addPoles E (c 0) (ε * (N : ℂ) ^ (-(κ : ℂ) / 2) * d 0) κ s =
      ε * (N : ℂ) ^ ((κ : ℂ) / 2 - s) * completedLSeries d (κ - s)) :
    expSum c ∣[κ] frickeGL ℝ N = (ε * I ^ (-κ) * (N : ℂ) ^ ((κ : ℂ) / 2 - 1)) • expSum d := by
  rcases hc with ⟨C₁, m₁, hC₁⟩
  rcases hd with ⟨C₂, m₂, hC₂⟩
  have hup : ∀ {e : ℕ → ℂ} {B : ℝ} {k : ℕ}, (∀ n : ℕ, n ≠ 0 → ‖e n‖ ≤ B * (n : ℝ) ^ k) →
      k ≤ max m₁ m₂ → ∀ n : ℕ, n ≠ 0 → ‖e n‖ ≤ |B| * (n : ℝ) ^ max m₁ m₂ :=
    fun {e B k} hB hk n hn ↦ by
    have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)
    refine (hB n hn).trans ?_
    exact mul_le_mul (le_abs_self B) (pow_le_pow_right₀ hn' hk) (by positivity) (abs_nonneg B)
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  refine eq_of_resToImagAxis_eq (MDifferentiable.slash (mdifferentiable_expSum ⟨C₁, m₁, hC₁⟩) κ _)
    ((mdifferentiable_expSum ⟨C₂, m₂, hC₂⟩).const_smul _) fun y hy ↦ ?_
  have hQ : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hQ2 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN.le
  have hy' : 0 < 1 / ((N : ℝ) * y) := by positivity
  have hmax₁ : m₁ ≤ max m₁ m₂ := le_max_left _ _
  have hmax₂ : m₂ ≤ max m₁ m₂ := le_max_right _ _
  have h₁ : resToImagAxis (expSum c ∣[κ] frickeGL ℝ N) (y * Real.sqrt N / Real.sqrt N) =
      ((Real.sqrt N : ℝ) : ℂ) ^ (κ - 2) * I ^ (-κ) * ((y * Real.sqrt N : ℝ) : ℂ) ^ (-κ) *
        resToImagAxis (expSum c) (1 / (y * Real.sqrt N) / Real.sqrt N) :=
    UpperHalfPlane.resToImagAxis_slash_frickeGL (N := N) (k := κ) (expSum c) (mul_pos hy hQ)
  have e₁ : y * Real.sqrt N / Real.sqrt N = y := mul_div_cancel_right₀ y hQ.ne'
  have e₂ : 1 / (y * Real.sqrt N) / Real.sqrt N = 1 / ((N : ℝ) * y) := by
    rw [div_div, mul_assoc, hQ2, mul_comm]
  have e₃ : 1 / ((N : ℝ) * (1 / ((N : ℝ) * y))) = y := by
    field_simp
  have h₂ : resToImagAxis (expSum c) (1 / ((N : ℝ) * y)) = ε * (((1 / ((N : ℝ) * y) : ℝ) : ℂ) ^
      (-(κ : ℂ)) * ((N : ℝ) : ℂ) ^ (-(κ : ℂ) / 2)) *
        resToImagAxis (expSum d) (1 / ((N : ℝ) * (1 / ((N : ℝ) * y)))) :=
    resToImagAxis_expSum_eq_of_functional_equation (σ₀ := σ₀) (hup hC₁ hmax₁) (hup hC₂ hmax₂) hκ hN
      hE hbd (fun s hs ↦ by rw [ofReal_natCast]; exact hΛc s hs)
      (fun s hs ↦ by rw [ofReal_natCast]; exact hΛd s hs) hy'
  rw [e₃] at h₂
  rw [e₁, e₂, h₂] at h₁
  rw [h₁, resToImagAxis_smul, Pi.smul_apply, smul_eq_mul]
  have hQc : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hQ.ne'
  have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have hNc : (N : ℂ) = ((Real.sqrt N : ℝ) : ℂ) ^ 2 := by
    rw [sq, ← ofReal_mul, hQ2, ofReal_natCast]
  have ha : ((Real.sqrt N : ℝ) : ℂ) ^ κ ≠ 0 := zpow_ne_zero _ hQc
  have hb : (y : ℂ) ^ κ ≠ 0 := zpow_ne_zero _ hyc
  have e₄ : ((1 / ((N : ℝ) * y) : ℝ) : ℂ) ^ (-(κ : ℂ)) =
      (((Real.sqrt N : ℝ) : ℂ) ^ κ) ^ 2 * (y : ℂ) ^ κ := by
    have e₉ : (N : ℂ) ^ κ = (((Real.sqrt N : ℝ) : ℂ) ^ κ) ^ 2 := by
      rw [hNc, ← zpow_natCast _ 2, ← zpow_natCast _ 2, ← zpow_mul, ← zpow_mul, mul_comm]
    rw [cpow_neg, cpow_intCast]
    push_cast
    rw [one_div, inv_zpow, inv_inv, mul_zpow, e₉]
  have e₅ : ((N : ℝ) : ℂ) ^ (-(κ : ℂ) / 2) = (((Real.sqrt N : ℝ) : ℂ) ^ κ)⁻¹ := by
    rw [neg_div, cpow_neg, ofReal_natCast, natCast_cpow_div_two_eq]
  have e₈ : ((y * Real.sqrt N : ℝ) : ℂ) ^ (-κ) = ((y : ℂ) ^ κ * ((Real.sqrt N : ℝ) : ℂ) ^ κ)⁻¹ := by
    rw [zpow_neg, ofReal_mul, mul_zpow]
  rw [e₄, e₅, natCast_cpow_div_two_sub_one, e₈]
  field_simp

end ModularForm
