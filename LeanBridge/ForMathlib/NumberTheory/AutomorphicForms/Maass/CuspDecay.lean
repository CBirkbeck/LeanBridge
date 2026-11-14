import LeanBridge.ForMathlib.Analysis.Complex.UpperHalfPlane.PortraitMoebius
import LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselKLowerBound
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CuspNewformExpansion
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.NewformAtkinLehner
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The portraits of Maass forms: decay at the cusp and real values

The LMFDB draws a Maass newform `f` on the unit disc through the Möbius transformation
`μ(z) = (1 - iz) / (z - i)` (LMFDB `portrait.maass`, `UpperHalfPlane.portraitMoebius`), and states
two facts about the pictures: the forms all vanish near the top of the disc, and they take only real
values when the level is squarefree. The LMFDB's Maass forms are cusp newforms of weight `0` on
`Γ₀(N)` with trivial character and squarefree level `N` (LMFDB `rcs.cande.maass_rigor`), each stored
with its symmetry, even or odd, and normalised by `a(1) = 1` in the cosine or sine expansion of
that symmetry (`UpperHalfPlane.IsMaassCuspNewform`, `UpperHalfPlane.maassNormalisedNewform`).

* **Decay.** A Maass form in `M(N, χ, λ)` whose constant term at `∞` vanishes tends to `0` at the
  cusp `i∞`, uniformly in `x`. Its Fourier coefficients are `a_n(y) = c(n) √y K_{iR}(2π|n|y)`, and
  at a fixed height `y₀` they are bounded by the maximum of `|f|` on a horizontal segment. Since
  `|K_{iR}(x)| ≥ e^{-2x}` at large `x` (`Complex.eventually_exp_le_norm_besselK`), the coefficients
  `c(n)` grow at most like `e^{4π|n|y₀}`. As `|K_{iR}(x)| ≤ C e^{-x}`, the series `∑ |a_n(y)|` is
  then at most a constant times `√y e^{-2πy}` for `y ≥ 2y₀ + 1`. As `μ` maps the horodiscs
  `B(i(1 - r), r)` at the top `i` of the disc onto the neighbourhoods `{Im w > (1 - r) / r}` of
  `i∞` (`UpperHalfPlane.bijOn_portraitMoebius_ball`), a function on `ℍ` tends to `0` at `i∞` exactly
  when its composition with `μ` is small on the horodiscs at `i`, and in this sense a cusp newform
  vanishes near the top of the disc. It is not small on the Euclidean neighbourhoods of `i` in the
  disc: being invariant under `z ↦ z + 1`, a form takes each of its values in every one of them.
* **Real values.** The normalised newform of a cusp newform is real-valued, at every level, not only
  at squarefree levels (`UpperHalfPlane.IsMaassCuspNewform.conj_maassNormalisedNewform`): for an
  even or odd cusp newform by LeanBridge's real coefficients, while a cusp newform that is neither
  has no cosine or sine expansion, and its normalised newform is the junk value `0`. That every
  Maass cusp newform of trivial character is even or odd is not proved here; the LMFDB stores a
  symmetry for each of its forms, and its normalisation `a(1) = 1` is the one of that symmetry.

## Main results

* `UpperHalfPlane.isZeroAtImInfty_of_mem_maassSpace` (LMFDB `portrait.maass`): a Maass form with
  vanishing constant term at `∞` tends to `0` at `i∞`.
* `UpperHalfPlane.isZeroAtImInfty_iff_forall_exists_forall_mem_ball_norm_lt`: a function on `ℍ`
  tends to `0` at `i∞` if and only if its composition with `μ` is small on the horodiscs at the top
  of the disc.
* `UpperHalfPlane.exists_mem_ball_dist_lt_comp_portraitMoebius_eq`: a function on `ℍ` invariant
  under `z ↦ z + 1` takes each of its values at `μ(z)` for `z` in the disc arbitrarily close to `i`.
* `UpperHalfPlane.IsMaassCuspNewform.isZeroAtImInfty`: a Maass cusp newform tends to `0` at `i∞`.
* `UpperHalfPlane.IsMaassCuspNewform.isZeroAtImInfty_maassNormalisedNewform`: so does the LMFDB's
  normalised newform.
* `UpperHalfPlane.IsMaassCuspNewform.exists_forall_mem_ball_norm_lt` (LMFDB `portrait.maass`): the
  normalised newform composed with `μ` vanishes near the top of the disc.
-/

open Filter Function MeasureTheory Real Set Topology

namespace UpperHalfPlane

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {R : ℂ} {F f : ℍ → ℂ}

private lemma summable_exp_neg_two_pi_mul_abs :
    Summable fun n : ℤ ↦ rexp (-(2 * π * |(n : ℝ)|)) := by
  have h : Summable fun n : ℕ ↦ rexp (n * -(2 * π)) :=
    summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr two_pi_pos)
  refine .of_nat_of_neg (h.congr fun n ↦ ?_) (h.congr fun n ↦ ?_)
  · rw [Int.cast_natCast, abs_of_nonneg n.cast_nonneg, mul_neg, mul_comm]
  · rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg n.cast_nonneg, mul_neg, mul_comm]

/-- **A Maass form with vanishing constant term tends to `0` at the cusp `i∞`** (LMFDB
`portrait.maass`: "these Maass forms all vanish near the top of the disk"): an element `F` of
`M(N, χ, 1/4 + R²)` with `∫_0^1 F(t + iy) dt = 0` for every `y > 0`, such as a cusp form, satisfies
`F(x + iy) → 0` as `y → ∞`, uniformly in `x`. -/
lemma isZeroAtImInfty_of_mem_maassSpace (hF : F ∈ maassSpace N χ (maassEigenvalue R))
    (h0 : ∀ y : ℝ, 0 < y → ∫ t in (0 : ℝ)..1, (F ∘ ofComplex) (t + y * Complex.I) = 0) :
    IsZeroAtImInfty F := by
  have hper (z : ℂ) (hz : 0 < z.im) : (F ∘ ofComplex) (z + 1) = (F ∘ ofComplex) z :=
    comp_add_one_of_mem_maassSpace hF hz
  rcases eventually_atTop.mp (Complex.eventually_exp_le_norm_besselK (Complex.I * R)) with ⟨X, hX⟩
  set y₀ : ℝ := max 1 (X / (2 * π))
  have hy₀ : 1 ≤ y₀ := le_max_left _ _
  have hy₀X : X ≤ 2 * π * y₀ := by
    rw [← div_le_iff₀' (by positivity)]
    exact le_max_right _ _
  have hcont : ContinuousOn (fun t : ℝ ↦ (F ∘ ofComplex) (t + y₀ * Complex.I)) (Icc 0 1) :=
    (hF.1.continuousOn.comp_continuous (by fun_prop) fun t ↦ by
      simpa using (by linarith : (0 : ℝ) < y₀)).continuousOn
  rcases isCompact_Icc.exists_bound_of_continuousOn hcont with ⟨M, hM⟩
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  set D : ℝ := 2⁻¹ * ∫ t in Ioi 0, ‖(Complex.I * R).besselKIntegrand 1 t‖
  have hD₀ : 0 ≤ D :=
    mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi fun _ _ ↦ norm_nonneg _)
  set C : ℝ := M * D * rexp 1 / √y₀ with hC_def
  have hC₀ : 0 ≤ C := by positivity
  set Y : ℝ := 2 * y₀ + 1 with hY_def
  -- the bound on the Fourier coefficients
  have hbound (n : ℤ) {y : ℝ} (hy : Y ≤ y) :
      ‖∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) *
        (F ∘ ofComplex) (t + y * Complex.I)‖ ≤
      C * rexp (-(2 * π * |(n : ℝ)|)) * (√y * rexp (-(2 * π * (y - Y)))) := by
    have hy0 : 0 < y := by linarith
    rcases eq_or_ne n 0 with rfl | hn
    · have h : ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * ((0 : ℤ) : ℂ)) * t) *
          (F ∘ ofComplex) (t + y * Complex.I) = 0 := by
        simpa using h0 y hy0
      rw [h, norm_zero]
      positivity
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn
    have hX' : X ≤ 2 * π * |(n : ℝ)| * y₀ :=
      hy₀X.trans (by nlinarith [mul_le_mul_of_nonneg_left hn1 (by positivity : 0 ≤ 2 * π * y₀)])
    have hK₀ : rexp (-(2 * (2 * π * |(n : ℝ)| * y₀))) ≤
        ‖(Complex.I * R).besselK (2 * π * |(n : ℝ)| * y₀)‖ :=
      hX _ hX'
    have hK₀ne : (Complex.I * R).besselK (2 * π * |(n : ℝ)| * y₀) ≠ 0 :=
      norm_pos_iff.mp ((exp_pos _).trans_le hK₀)
    have hny : 1 ≤ 2 * π * |(n : ℝ)| * y := by
      have h1 : 1 ≤ |(n : ℝ)| * y := by nlinarith
      nlinarith [two_le_pi]
    have hK : ‖(Complex.I * R).besselK (2 * π * |(n : ℝ)| * y)‖ ≤
        rexp (-(2 * π * |(n : ℝ)| * y - 1)) * D :=
      Complex.norm_besselK_le _ hny
    rw [fourierCoeff_eq_div_mul_sqrt_mul_besselK_of_integrableOn hF.1 hper hF.2.2.2 hn
      (integrableOn_norm_fourierCoeff_div_sq n hF) (by linarith) hK₀ne hy0]
    have ha₀ : ‖∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * n) * t) *
        (F ∘ ofComplex) (t + y₀ * Complex.I)‖ ≤ M :=
      norm_integral_exp_mul_le n hM
    rw [norm_mul, norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (sqrt_nonneg _), Real.norm_of_nonneg (sqrt_nonneg _)]
    have hsy₀ : 0 < √y₀ := sqrt_pos.mpr (by linarith)
    have hden : 0 < √y₀ * rexp (-(2 * (2 * π * |(n : ℝ)| * y₀))) := by positivity
    refine (mul_le_mul (div_le_div₀ hM₀ ha₀ hden (mul_le_mul_of_nonneg_left hK₀ hsy₀.le))
      (mul_le_mul_of_nonneg_left hK (sqrt_nonneg _)) (by positivity) (by positivity)).trans ?_
    have hexp : rexp (-(2 * π * |(n : ℝ)| * y - 1)) * rexp (2 * (2 * π * |(n : ℝ)| * y₀)) ≤
        rexp 1 * (rexp (-(2 * π * |(n : ℝ)|)) * rexp (-(2 * π * (y - Y)))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, exp_le_exp]
      nlinarith [pi_pos, mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr hy)]
    have key : M / (√y₀ * rexp (-(2 * (2 * π * |(n : ℝ)| * y₀)))) *
        (√y * (rexp (-(2 * π * |(n : ℝ)| * y - 1)) * D)) = M * D / √y₀ * √y *
        (rexp (-(2 * π * |(n : ℝ)| * y - 1)) * rexp (2 * (2 * π * |(n : ℝ)| * y₀))) := by
      rw [Real.exp_neg (2 * (2 * π * |(n : ℝ)| * y₀))]
      field_simp
    rw [key, hC_def]
    exact (mul_le_mul_of_nonneg_left hexp (by positivity)).trans_eq (by ring1)
  -- the series of the coefficients
  have hsum : HasSum (fun n : ℤ ↦ C * rexp (-(2 * π * |(n : ℝ)|)))
      (∑' n : ℤ, C * rexp (-(2 * π * |(n : ℝ)|))) :=
    (summable_exp_neg_two_pi_mul_abs.mul_left C).hasSum
  set S : ℝ := ∑' n : ℤ, C * rexp (-(2 * π * |(n : ℝ)|))
  have hle (z : ℍ) (hz : Y ≤ z.im) : ‖F z‖ ≤ S * (√z.im * rexp (-(2 * π * (z.im - Y)))) := by
    have hz' : (z : ℂ) = z.re + z.im * Complex.I := (Complex.re_add_im z).symm
    have hFz : F z = (F ∘ ofComplex) (z.re + z.im * Complex.I) := by
      rw [comp_apply, ← hz', ofComplex_apply]
    rw [hFz]
    refine (hasSum_fourierCoeffOn_mul_exp z.re hF.1 hper z.im_pos).norm_le_of_bounded
      (hsum.mul_right _) fun n ↦ ?_
    rw [fourierCoeffOn_eq_integral_exp, norm_mul, Complex.norm_exp]
    simpa using hbound n hz
  have htend : Tendsto (fun y : ℝ ↦ S * (√y * rexp (-(2 * π * (y - Y))))) atTop (𝓝 0) := by
    have h : Tendsto (fun y : ℝ ↦ S * rexp (2 * π * Y) * (y ^ (1 / 2 : ℝ) * rexp (-(2 * π) * y)))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (2 * π)
        two_pi_pos).const_mul (S * rexp (2 * π * Y))
    refine h.congr fun y ↦ ?_
    have he : rexp (-(2 * π * (y - Y))) = rexp (2 * π * Y) * rexp (-(2 * π) * y) := by
      rw [← Real.exp_add]
      congr 1
      ring1
    rw [sqrt_eq_rpow, he]
    ring1
  exact squeeze_zero_norm' ((atImInfty_mem _).mpr ⟨Y, hle⟩) (htend.comp tendsto_comap)

/-- **Vanishing at the cusp `i∞` is vanishing near the top of the disc**: a function `f` on `ℍ`
tends to `0` at `i∞`, uniformly in `x`, if and only if for every `ε > 0` there is a horodisc
`B(i(1 - r), r)` with `0 < r ≤ 1`, the disc of radius `r` tangent to the unit circle at its top `i`,
on which `|f(μ(z))| < ε`, where `μ` is the Möbius transformation of the LMFDB's portraits: `μ` maps
the horodiscs at `i` onto the neighbourhoods `{Im w > c}` of `i∞`. -/
lemma isZeroAtImInfty_iff_forall_exists_forall_mem_ball_norm_lt : IsZeroAtImInfty f ↔
    ∀ ε : ℝ, 0 < ε → ∃ r ∈ Ioc (0 : ℝ) 1, ∀ z ∈ Metric.ball (Complex.I * (1 - r : ℝ)) r,
      ‖f (ofComplex (portraitMoebius z))‖ < ε := by
  refine isZeroAtImInfty_iff.trans ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
  · rcases h (ε / 2) (half_pos hε) with ⟨A, hA⟩
    have hr₀ : 0 < (|A| + 2)⁻¹ := by positivity
    have hr₁ : (|A| + 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [abs_nonneg A])
    refine ⟨(|A| + 2)⁻¹, ⟨hr₀, hr₁⟩, fun z hz ↦ ?_⟩
    have hw : (1 - (|A| + 2)⁻¹) / (|A| + 2)⁻¹ < (portraitMoebius z).im :=
      (bijOn_portraitMoebius_ball hr₀ hr₁).mapsTo hz
    have hY : (1 - (|A| + 2)⁻¹) / (|A| + 2)⁻¹ = |A| + 1 := by
      field_simp
      ring1
    rw [hY] at hw
    have him : 0 < (portraitMoebius z).im := by linarith [abs_nonneg A]
    refine (hA _ ?_).trans_lt (half_lt_self hε)
    rw [ofComplex_apply_of_im_pos him, mk_im]
    linarith [le_abs_self A]
  · rcases h ε hε with ⟨r, ⟨hr₀, hr₁⟩, hr⟩
    refine ⟨(1 - r) / r + 1, fun w hw ↦ ?_⟩
    have hw' : (1 - r) / r < (w : ℂ).im := by
      rw [coe_im]
      linarith
    rcases (bijOn_portraitMoebius_ball hr₀ hr₁).surjOn hw' with ⟨z, hz, hzw⟩
    have hfz : ‖f (ofComplex (portraitMoebius z))‖ < ε := hr z hz
    rw [hzw, ofComplex_apply] at hfz
    exact hfz.le

/-- **A periodic function is not small on the Euclidean neighbourhoods of the top of the disc**: a
function `f` on `ℍ` invariant under `z ↦ z + 1`, such as a Maass form on `Γ₀(N)`, takes each of its
values at points `μ(z)` with `z` in the unit disc arbitrarily close to its top `i`, as
`|μ⁻¹(w) - i| = 2 / |w + i|` is small for `w = τ + n` with `n` large. So the composition with `μ` of
a nonzero Maass form does not tend to `0` at the point `i`: it vanishes near the top of the disc on
the horodiscs at `i` only (`isZeroAtImInfty_iff_forall_exists_forall_mem_ball_norm_lt`). -/
lemma exists_mem_ball_dist_lt_comp_portraitMoebius_eq (hf : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ) (τ : ℍ)
    {δ : ℝ} (hδ : 0 < δ) : ∃ z ∈ Metric.ball (0 : ℂ) 1, dist z Complex.I < δ ∧
      f (ofComplex (portraitMoebius z)) = f τ := by
  have hn (n : ℕ) : f ((n : ℝ) +ᵥ τ) = f τ := by
    induction n with
    | zero => rw [Nat.cast_zero, zero_vadd]
    | succ n ih => rw [Nat.cast_succ, add_comm, add_vadd, hf, ih]
  rcases exists_nat_gt (2 / δ - τ.re) with ⟨n, hnδ⟩
  rcases bijOn_portraitMoebius.surjOn ((n : ℝ) +ᵥ τ).im_pos with ⟨z, hz, hzw⟩
  refine ⟨z, hz, ?_, by rw [hzw, ofComplex_apply, hn]⟩
  have hzi : z - Complex.I ≠ 0 := by
    rintro h
    rw [sub_eq_zero.mp h] at hz
    simp at hz
  have h2 : (portraitMoebius z + Complex.I) * (z - Complex.I) = 2 := by
    rw [portraitMoebius, add_mul, div_mul_cancel₀ _ hzi]
    linear_combination -Complex.I_mul_I
  have hre : 2 / δ < ‖portraitMoebius z + Complex.I‖ := by
    refine (Complex.re_le_norm _).trans_lt' ?_
    rw [hzw, Complex.add_re, Complex.I_re, add_zero, coe_re, vadd_re]
    linarith
  have h2' : ‖portraitMoebius z + Complex.I‖ * dist z Complex.I = 2 := by
    rw [Complex.dist_eq, ← norm_mul, h2, RCLike.norm_ofNat]
  rw [div_lt_iff₀ hδ] at hre
  by_contra hcon
  nlinarith [not_lt.mp hcon, norm_nonneg (portraitMoebius z + Complex.I)]

variable [NeZero N]

/-- **A Maass cusp newform tends to `0` at the cusp `i∞`** (LMFDB `portrait.maass`): its constant
term at `∞` vanishes. -/
lemma IsMaassCuspNewform.isZeroAtImInfty (hF : IsMaassCuspNewform N R F) : IsZeroAtImInfty F :=
  isZeroAtImInfty_of_mem_maassSpace hF.1.1.1 fun _ hy ↦ hF.integral_eq_zero hy

/-- **The LMFDB's normalised Maass newform tends to `0` at the cusp `i∞`** (LMFDB
`portrait.maass`): the normalised newform `f = F / a(1)` of a Maass cusp newform `F` is a multiple
of `F`. -/
lemma IsMaassCuspNewform.isZeroAtImInfty_maassNormalisedNewform (hF : IsMaassCuspNewform N R F) :
    IsZeroAtImInfty (maassNormalisedNewform R F) :=
  hF.isZeroAtImInfty.smul _

/-- **Maass cusp newforms vanish near the top of the disc** (LMFDB `portrait.maass`: "these Maass
forms all vanish near the top of the disk"): for the normalised newform `f` of a Maass cusp newform
and every `ε > 0`, `|f(μ(z))| < ε` on a horodisc `B(i(1 - r), r)` with `0 < r ≤ 1`, the disc of
radius `r` tangent to the unit circle at its top `i`, where `μ` is the Möbius transformation of the
LMFDB's portraits. -/
lemma IsMaassCuspNewform.exists_forall_mem_ball_norm_lt (hF : IsMaassCuspNewform N R F) {ε : ℝ}
    (hε : 0 < ε) : ∃ r ∈ Ioc (0 : ℝ) 1, ∀ z ∈ Metric.ball (Complex.I * (1 - r : ℝ)) r,
      ‖maassNormalisedNewform R F (ofComplex (portraitMoebius z))‖ < ε :=
  isZeroAtImInfty_iff_forall_exists_forall_mem_ball_norm_lt.mp
    hF.isZeroAtImInfty_maassNormalisedNewform ε hε

end UpperHalfPlane
