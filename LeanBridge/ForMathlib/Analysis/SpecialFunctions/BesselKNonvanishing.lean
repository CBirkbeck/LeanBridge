import LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselKUnique
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The `K`-Bessel function does not vanish identically

For every order `ν ∈ ℂ`, the `K`-Bessel function `K_ν` (`Complex.besselK`, LMFDB
`specialfunction.k_bessel`) takes a nonzero value on `(0, ∞)`. For `Re ν > 0`, the substitution
`t = 2s/x` in `K_ν(x) = ½ ∫₀^∞ t^(ν - 1) e^(-(x/2)(t + 1/t)) dt` gives
`(x/2)^ν K_ν(x) = ½ ∫₀^∞ e^(-s - x²/(4s)) s^(ν - 1) ds`, which tends to `½ Γ(ν) ≠ 0` as `x → 0`
(dominated convergence). In general, if `K_ν` vanished on `(0, ∞)`, so would
`K_{ν + 1} = -K_ν' + (ν/x) K_ν`, hence every `K_{ν + n}`, `n ∈ ℕ`. For real `ν` the function has no
zero at all (`Complex.besselK_ofReal_ne_zero`), but `K_{ir}` has zeros for real `r ≠ 0`: this is the
non-vanishing used for the Fourier coefficients of Maass forms of spectral parameter `r`.

## Main results

* `Complex.exists_besselK_ne_zero`: `K_ν(x) ≠ 0` for some `x > 0`.
-/

open Filter MeasureTheory Real Set Topology

namespace Complex

variable (ν : ℂ) {x : ℝ}

variable (x) in
/-- The integrand `s ↦ e^(-s - x²/(4s)) s^(ν - 1)` of `(x/2)^ν K_ν(x)`, which is the integrand of
`Γ(ν)` at `x = 0`. -/
private noncomputable def besselKGammaIntegrand (s : ℝ) : ℂ :=
  (rexp (-(s + x ^ 2 / 4 / s)) : ℂ) * (s : ℂ) ^ (ν - 1)

lemma integral_besselKIntegrand_eq (hx : 0 < x) : ∫ t in Ioi 0, besselKIntegrand ν x t =
    ((2 / x : ℝ) : ℂ) * ((2 / x : ℝ) : ℂ) ^ (ν - 1) *
        ∫ s in Ioi 0, besselKGammaIntegrand ν x s := by
  have hb : 0 < 2 / x := div_pos two_pos hx
  have h : (2 / x) • ∫ s in Ioi 0, besselKIntegrand ν x (2 / x * s) =
      ∫ t in Ioi (2 / x * 0), besselKIntegrand ν x t :=
    integral_comp_mul_left_Ioi' (besselKIntegrand ν x) 0 hb
  rw [mul_zero] at h
  rw [mul_assoc, ← h, real_smul, ← integral_const_mul (((2 / x : ℝ) : ℂ) ^ (ν - 1))]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_
  have he : -(x / 2) * (2 / x * s + (2 / x * s)⁻¹) = -(s + x ^ 2 / 4 / s) := by
    field_simp
    ring1
  rw [besselKIntegrand, besselKGammaIntegrand, ofReal_mul, mul_cpow_ofReal_nonneg hb.le hs.le, he]
  ring1

lemma tendsto_integral_besselKGammaIntegrand (hν : 0 < ν.re) :
    Tendsto (fun x ↦ ∫ s in Ioi 0, besselKGammaIntegrand ν x s) (𝓝 0) (𝓝 (Gamma ν)) := by
  have h0 : Gamma ν = ∫ s in Ioi 0, besselKGammaIntegrand ν 0 s := by
    rw [Gamma_eq_integral hν, GammaIntegral]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ ↦ ?_
    simp [besselKGammaIntegrand]
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence (fun s ↦ ‖besselKGammaIntegrand ν 0 s‖)
    (.of_forall fun x ↦ ?_) (.of_forall fun x ↦ ?_) ?_ (.of_forall fun s ↦ ?_)
  · exact (by unfold besselKGammaIntegrand; fun_prop :
      Measurable (besselKGammaIntegrand ν x)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun s (hs : 0 < s) ↦ ?_)
    rw [besselKGammaIntegrand, besselKGammaIntegrand, norm_mul, norm_mul, norm_real, norm_real,
      Real.norm_of_nonneg (exp_pos _).le, Real.norm_of_nonneg (exp_pos _).le]
    refine mul_le_mul_of_nonneg_right (exp_le_exp.mpr ?_) (norm_nonneg _)
    norm_num
    positivity
  · refine IntegrableOn.congr_fun (GammaIntegral_convergent hν).norm (fun s _ ↦ ?_)
      measurableSet_Ioi
    simp [besselKGammaIntegrand]
  · exact (by unfold besselKGammaIntegrand; fun_prop :
      Continuous fun x ↦ besselKGammaIntegrand ν x s).tendsto 0

lemma exists_besselK_ne_zero_of_re_pos (hν : 0 < ν.re) : ∃ x, 0 < x ∧ besselK ν x ≠ 0 := by
  have hJ : ∀ᶠ x in 𝓝[>] 0, ∫ s in Ioi 0, besselKGammaIntegrand ν x s ≠ 0 :=
    ((tendsto_integral_besselKGammaIntegrand ν hν).mono_left nhdsWithin_le_nhds).eventually_ne
      (Gamma_ne_zero_of_re_pos hν)
  rcases (hJ.and self_mem_nhdsWithin).exists with ⟨x, hJx, hx⟩
  have hb : ((2 / x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (div_pos two_pos hx).ne'
  refine ⟨x, hx, ?_⟩
  rw [besselK, integral_besselKIntegrand_eq ν hx]
  exact mul_ne_zero (by norm_num) <| mul_ne_zero (mul_ne_zero hb (by simp [hx.ne'])) hJx

lemma besselK_add_one_eq_zero (h : ∀ x, 0 < x → besselK ν x = 0) (hx : 0 < x) :
    besselK (ν + 1) x = 0 := by
  have h1 : HasDerivAt (fun x ↦ besselK ν x) 0 x :=
    (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq <|
      (eventually_gt_nhds hx).mono fun y hy ↦ h y hy
  have h2 : -besselK (ν + 1) x + ν / x * besselK ν x = 0 :=
    (hasDerivAt_besselK_eq_add ν hx).unique h1
  rwa [h x hx, mul_zero, add_zero, neg_eq_zero] at h2

/-- **The `K`-Bessel function does not vanish identically on `(0, ∞)`**: for every order `ν ∈ ℂ`,
`K_ν(x) ≠ 0` for some `x > 0`. -/
lemma exists_besselK_ne_zero : ∃ x, 0 < x ∧ besselK ν x ≠ 0 := by
  by_contra! h
  have hn (n : ℕ) : ∀ x, 0 < x → besselK (ν + n) x = 0 := by
    induction n with
    | zero => simpa using h
    | succ n ih =>
      intro x hx
      rw [Nat.cast_succ, ← add_assoc]
      exact besselK_add_one_eq_zero _ ih hx
  have hre : 0 < (ν + (⌈-ν.re⌉₊ + 1 : ℕ)).re := by
    rw [add_re, natCast_re]
    push_cast
    linarith [Nat.le_ceil (-ν.re)]
  rcases exists_besselK_ne_zero_of_re_pos _ hre with ⟨x, hx, hK⟩
  exact hK <| hn _ x hx

end Complex
