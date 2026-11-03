import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.EigenvalueReal
import TauCeti.Analysis.Calculus.ParametricIntegral

/-!
# Radial kernels whose radial Laplacian is a difference of two bumps

The radial Laplacian `radialLaplacian φ (c) = ((c² - 1) φ'(c))'` of a function of `c = cosh d` is a
total derivative. So the difference `(2n + 2) θ((2n + 2)(c - 1)) - (n + 1) θ((n + 1)(c - 1))` of the
bumps `coshDistBump (2n + 1)` and `coshDistBump n` (with `θ(x) = smoothTransition (2 - x)`, equal to
`1` for `x ≤ 1` and to `0` for `x ≥ 2`), having integral `0` over `[1, ∞)`, is the radial Laplacian
of the smooth function `radialGreen n`, with
`(c² - 1) (radialGreen n)'(c) = ∫_{(n + 1)(c - 1)}^{2(n + 1)(c - 1)} θ`. The function
`radialGreen n` vanishes for `c ≥ 1 + 2/(n + 1)` and lies in `[-1, 0]` for `c ≥ 1`.

Green's identity on `ℍ` for the constant function `1` then shows that the mass of
`coshDistBump (2n + 1)` is half that of `coshDistBump n`, with no polar coordinates on `ℍ`. So the
kernels `radialGreen n`, bounded by `1` with supports shrinking to `c = 1`, have a small mass, which
is what the comparison of the averages of a Maass form over balls of different radii uses
(`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.KernelPair`), in the place of Selberg's
theorem that a Maass form is an eigenfunction of the integral operators with a point-pair invariant
as a kernel.

## Main definitions

* `UpperHalfPlane.radialProfile`: the average `∫_0^1 θ((1 + u) x) du` of `θ` over `[x, 2x]`.
* `UpperHalfPlane.radialInv`: the function `(c + 1)⁻¹` for `c ≥ 1/2`, modified to be smooth on `ℝ`.
* `UpperHalfPlane.radialGreenDeriv`: the derivative of `radialGreen n`.
* `UpperHalfPlane.radialGreen`: the function with radial Laplacian
  `(2n + 2) θ((2n + 2)(c - 1)) - (n + 1) θ((n + 1)(c - 1))`.
* `UpperHalfPlane.bumpMass`: the mass of `coshDistBump n` as a kernel on `ℍ`.

## Main results

* `UpperHalfPlane.radialLaplacian_radialGreen`: the radial Laplacian of `radialGreen n`.
* `UpperHalfPlane.bumpMass_two_mul_add_one`: the mass of `coshDistBump (2n + 1)` is half that of
  `coshDistBump n`.
-/

open MeasureTheory Real Set Topology

open scoped ContDiff

namespace UpperHalfPlane

variable (n : ℕ) {c x : ℝ}

variable (x) in
/-- The average `∫_0^1 θ((1 + u) x) du` of `θ(y) = smoothTransition (2 - y)` over `[x, 2x]`. -/
noncomputable def radialProfile : ℝ :=
  ∫ u in Icc (0 : ℝ) 1, smoothTransition (2 - (1 + u) * x)

lemma contDiff_radialProfile : ContDiff ℝ ∞ radialProfile :=
  contDiff_integral_Icc_of_contDiff ⊤ (fun x u ↦ smoothTransition (2 - (1 + u) * x))
    (smoothTransition.contDiff.comp (by fun_prop))

variable (x) in
lemma radialProfile_nonneg : 0 ≤ radialProfile x :=
  integral_nonneg fun _ ↦ smoothTransition.nonneg _

variable (x) in
lemma radialProfile_le_one : radialProfile x ≤ 1 := by
  have h : ∫ u in Icc (0 : ℝ) 1, smoothTransition (2 - (1 + u) * x) ≤ ∫ _ in Icc (0 : ℝ) 1, 1 :=
    setIntegral_mono_on ((smoothTransition.continuous.comp (by fun_prop)).integrableOn_Icc)
      (continuous_const.integrableOn_Icc) measurableSet_Icc fun _ _ ↦ smoothTransition.le_one _
  simpa [radialProfile] using h

lemma radialProfile_eq_zero (hx : 2 ≤ x) : radialProfile x = 0 :=
  setIntegral_eq_zero_of_forall_eq_zero fun u hu ↦ smoothTransition.zero_of_nonpos <| by
    nlinarith [hu.1, hu.2]

lemma radialProfile_eq_one (hx : x ≤ 1 / 2) : radialProfile x = 1 := by
  have h :
      ∫ u in Icc (0 : ℝ) 1, smoothTransition (2 - (1 + u) * x) = ∫ _ in Icc (0 : ℝ) 1, (1 : ℝ) :=
    setIntegral_congr_fun measurableSet_Icc fun u hu ↦ smoothTransition.one_of_one_le <| by
      nlinarith [hu.1, hu.2]
  simpa [radialProfile] using h

variable (x) in
lemma mul_radialProfile : x * radialProfile x = ∫ y in x..2 * x, smoothTransition (2 - y) := by
  have h : radialProfile x = ∫ u in (0 : ℝ)..1, smoothTransition (2 - (x * u + x)) := by
    rw [radialProfile, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    congr 2
    ring1
  have h1 : x • ∫ u in (0 : ℝ)..1, smoothTransition (2 - (x * u + x)) =
      ∫ y in x * 0 + x..x * 1 + x, smoothTransition (2 - y) :=
    intervalIntegral.smul_integral_comp_mul_add (fun y ↦ smoothTransition (2 - y)) x x
  rw [h, ← smul_eq_mul, h1]
  congr 1 <;> ring1

variable (x) in
lemma hasDerivAt_mul_radialProfile : HasDerivAt (fun x ↦ x * radialProfile x)
    (2 * smoothTransition (2 - 2 * x) - smoothTransition (2 - x)) x := by
  have hc : Continuous fun y ↦ smoothTransition (2 - y) :=
    smoothTransition.continuous.comp (by fun_prop)
  have hΘ (y : ℝ) : HasDerivAt (fun y ↦ ∫ t in (0 : ℝ)..y, smoothTransition (2 - t))
      (smoothTransition (2 - y)) y :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have h : (fun x ↦ x * radialProfile x) = fun x ↦ (∫ t in (0 : ℝ)..2 * x,
      smoothTransition (2 - t)) - ∫ t in (0 : ℝ)..x, smoothTransition (2 - t) := by
    funext y
    rw [mul_radialProfile, intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  rw [h]
  have h2 : HasDerivAt (fun x : ℝ ↦ 2 * x) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have h3 : HasDerivAt (fun x ↦ ∫ t in (0 : ℝ)..2 * x, smoothTransition (2 - t))
      (smoothTransition (2 - 2 * x) * 2) x := (hΘ (2 * x)).comp x h2
  exact (h3.sub (hΘ x)).congr_deriv (by ring1)

variable (c) in
/-- The function `(c + 1)⁻¹` for `c ≥ 1/2`, modified to be smooth on `ℝ`. -/
noncomputable def radialInv : ℝ :=
  smoothTransition (2 * c) / (c + 1)

lemma contDiff_radialInv : ContDiff ℝ ∞ radialInv := by
  refine contDiff_iff_contDiffAt.mpr fun c ↦ ?_
  rcases lt_or_ge c 0 with hc | hc
  · have h : radialInv =ᶠ[𝓝 c] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds hc] with e he
      have he' : e < 0 := he
      rw [radialInv, smoothTransition.zero_of_nonpos (by linarith), zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq h
  · refine ContDiffAt.div (smoothTransition.contDiffAt.comp c (by fun_prop)) (by fun_prop) ?_
    linarith

lemma radialInv_eq (hc : 1 / 2 ≤ c) : radialInv c = (c + 1)⁻¹ := by
  rw [radialInv, smoothTransition.one_of_one_le (by linarith), one_div]

variable (c) in
/-- The derivative of `radialGreen n`: for `c ≥ 1/2`, it is
`(c² - 1)⁻¹ ∫_{(n + 1)(c - 1)}^{2(n + 1)(c - 1)} θ`, smooth at `c = 1`
(`mul_radialGreenDeriv_eq`). -/
noncomputable def radialGreenDeriv : ℝ :=
  (n + 1) * radialProfile ((n + 1) * (c - 1)) * radialInv c

lemma contDiff_radialGreenDeriv : ContDiff ℝ ∞ (radialGreenDeriv n) :=
  (contDiff_const.mul (contDiff_radialProfile.comp (by fun_prop))).mul contDiff_radialInv

lemma mul_radialGreenDeriv_eq (hc : 1 / 2 ≤ c) :
    (c ^ 2 - 1) * radialGreenDeriv n c = (n + 1) * (c - 1) * radialProfile ((n + 1) * (c - 1)) := by
  have h : c + 1 ≠ 0 := by
    linarith
  rw [radialGreenDeriv, radialInv_eq hc]
  field_simp
  ring1

lemma radialGreenDeriv_nonneg (hc : 1 ≤ c) : 0 ≤ radialGreenDeriv n c := by
  rw [radialGreenDeriv, radialInv_eq (by linarith)]
  have h : 0 ≤ radialProfile ((n + 1) * (c - 1)) := radialProfile_nonneg _
  have h1 : (0 : ℝ) < c + 1 := by
    linarith
  positivity

lemma radialGreenDeriv_le (hc : 1 ≤ c) : radialGreenDeriv n c ≤ (n + 1) / 2 := by
  rw [radialGreenDeriv, radialInv_eq (by linarith)]
  have h : radialProfile ((n + 1) * (c - 1)) ≤ 1 := radialProfile_le_one _
  have h0 : 0 ≤ radialProfile ((n + 1) * (c - 1)) := radialProfile_nonneg _
  have h1 : (c + 1)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le two_pos (by linarith)
  have h2 : (0 : ℝ) < n + 1 := by
    positivity
  have h3 : (0 : ℝ) < (c + 1)⁻¹ := inv_pos.mpr (by linarith)
  have h4 : ((n : ℝ) + 1) * radialProfile ((n + 1) * (c - 1)) * (c + 1)⁻¹ ≤ (n + 1) * 1 * (1 / 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h h2.le) h1 h3.le (by positivity)
  linarith

lemma radialGreenDeriv_eq_zero (hc : 1 + 2 / (n + 1) ≤ c) : radialGreenDeriv n c = 0 := by
  have h : (0 : ℝ) < n + 1 := by
    positivity
  have h1 : 2 ≤ ((n : ℝ) + 1) * (c - 1) := by
    have h2 : 2 / ((n : ℝ) + 1) ≤ c - 1 := by
      linarith
    rwa [div_le_iff₀' h] at h2
  rw [radialGreenDeriv, radialProfile_eq_zero h1, mul_zero, zero_mul]

variable (c) in
/-- The smooth function with derivative `radialGreenDeriv n` vanishing on `[1 + 2/(n + 1), ∞)`,
whose radial Laplacian is `(2n + 2) θ((2n + 2)(c - 1)) - (n + 1) θ((n + 1)(c - 1))`
(`radialLaplacian_radialGreen`), with `θ(x) = smoothTransition (2 - x)`. It lies in `[-1, 0]` on
`[1, ∞)`. -/
noncomputable def radialGreen : ℝ :=
  ∫ e in (1 + 2 / ((n : ℝ) + 1))..c, radialGreenDeriv n e

variable (c) in
lemma hasDerivAt_radialGreen : HasDerivAt (radialGreen n) (radialGreenDeriv n c) c :=
  intervalIntegral.integral_hasDerivAt_right
    ((contDiff_radialGreenDeriv n).continuous.intervalIntegrable _ _)
    ((contDiff_radialGreenDeriv n).continuous.stronglyMeasurableAtFilter _ _)
    (contDiff_radialGreenDeriv n).continuous.continuousAt

lemma deriv_radialGreen : deriv (radialGreen n) = radialGreenDeriv n :=
  funext fun c ↦ (hasDerivAt_radialGreen n c).deriv

lemma contDiff_radialGreen : ContDiff ℝ ∞ (radialGreen n) :=
  contDiff_infty_iff_deriv.mpr ⟨fun c ↦ (hasDerivAt_radialGreen n c).differentiableAt,
    (deriv_radialGreen n).symm ▸ contDiff_radialGreenDeriv n⟩

lemma radialGreen_eq_zero (hc : 1 + 2 / (n + 1) ≤ c) : radialGreen n c = 0 := by
  rw [radialGreen, intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun e he ↦ ?_]
  · simp
  · rw [uIcc_of_le hc] at he
    exact radialGreenDeriv_eq_zero n he.1

lemma radialGreen_eq_neg_integral :
    radialGreen n c = -∫ e in c..(1 + 2 / ((n : ℝ) + 1)), radialGreenDeriv n e :=
  intervalIntegral.integral_symm _ _

lemma intervalIntegrable_radialGreenDeriv (a b : ℝ) :
    IntervalIntegrable (radialGreenDeriv n) volume a b :=
  (contDiff_radialGreenDeriv n).continuous.intervalIntegrable _ _

lemma radialGreen_nonpos (hc : 1 ≤ c) : radialGreen n c ≤ 0 := by
  rcases le_total (1 + 2 / ((n : ℝ) + 1)) c with h | h
  · exact (radialGreen_eq_zero n h).le
  · rw [radialGreen_eq_neg_integral, neg_nonpos]
    exact intervalIntegral.integral_nonneg h fun e he ↦ radialGreenDeriv_nonneg n (hc.trans he.1)

lemma neg_one_le_radialGreen (hc : 1 ≤ c) : -1 ≤ radialGreen n c := by
  rcases le_total (1 + 2 / ((n : ℝ) + 1)) c with h | h
  · rw [radialGreen_eq_zero n h]
    norm_num
  · have h0 : (0 : ℝ) < n + 1 := by
      positivity
    rw [radialGreen_eq_neg_integral, neg_le_neg_iff]
    have h1 : ∫ e in c..(1 + 2 / ((n : ℝ) + 1)), radialGreenDeriv n e ≤
        ∫ _ in c..(1 + 2 / ((n : ℝ) + 1)), ((n : ℝ) + 1) / 2 :=
      intervalIntegral.integral_mono_on h (intervalIntegrable_radialGreenDeriv n _ _)
        intervalIntegrable_const fun e he ↦ radialGreenDeriv_le n (hc.trans he.1)
    refine h1.trans ?_
    rw [intervalIntegral.integral_const, smul_eq_mul]
    have h2 : 1 + 2 / ((n : ℝ) + 1) - c ≤ 2 / ((n : ℝ) + 1) := by
      linarith
    have h3 : 2 / ((n : ℝ) + 1) * (((n : ℝ) + 1) / 2) = 1 := by
      field_simp
    have h4 : (1 + 2 / ((n : ℝ) + 1) - c) * (((n : ℝ) + 1) / 2) ≤
        2 / ((n : ℝ) + 1) * (((n : ℝ) + 1) / 2) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    linarith

lemma radialGreen_le_neg (hc : 1 ≤ c) (hc' : c ≤ 1 + 1 / (4 * (n + 1))) :
    radialGreen n c ≤ -(1 / 12) := by
  have h0 : (1 : ℝ) ≤ n + 1 := by
    simp
  have h0' : (0 : ℝ) < n + 1 := by
    positivity
  have hd : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) two_pos]
    linarith
  have h14 : 1 / (4 * ((n : ℝ) + 1)) ≤ 1 / (2 * ((n : ℝ) + 1)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have h12 : 1 / (2 * ((n : ℝ) + 1)) ≤ 2 / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) h0']
    linarith
  rw [radialGreen_eq_neg_integral, neg_le_neg_iff]
  have hsub : ∫ e in (1 + 1 / (4 * ((n : ℝ) + 1)))..(1 + 1 / (2 * ((n : ℝ) + 1))),
      radialGreenDeriv n e ≤ ∫ e in c..(1 + 2 / ((n : ℝ) + 1)), radialGreenDeriv n e := by
    refine intervalIntegral.integral_mono_interval hc' (by linarith) (by linarith) ?_
      (intervalIntegrable_radialGreenDeriv n _ _)
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun e he ↦ ?_)
    exact radialGreenDeriv_nonneg n (hc.trans he.1.le)
  refine le_trans ?_ hsub
  have hconst : ∫ _ in (1 + 1 / (4 * ((n : ℝ) + 1)))..(1 + 1 / (2 * ((n : ℝ) + 1))),
      ((n : ℝ) + 1) / 3 ≤ ∫ e in (1 + 1 / (4 * ((n : ℝ) + 1)))..(1 + 1 / (2 * ((n : ℝ) + 1))),
        radialGreenDeriv n e := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (intervalIntegrable_radialGreenDeriv n _ _) fun e he ↦ ?_
    have he1 : 1 ≤ e := by
      have h : (0 : ℝ) ≤ 1 / (4 * ((n : ℝ) + 1)) := by
        positivity
      linarith [he.1]
    have hx : ((n : ℝ) + 1) * (e - 1) ≤ 1 / 2 := by
      have h : e - 1 ≤ 1 / (2 * ((n : ℝ) + 1)) := by
        linarith [he.2]
      have h1 : ((n : ℝ) + 1) * (e - 1) ≤ ((n : ℝ) + 1) * (1 / (2 * ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left h h0'.le
      have h2 : ((n : ℝ) + 1) * (1 / (2 * ((n : ℝ) + 1))) = 1 / 2 := by
        field_simp
      linarith
    rw [radialGreenDeriv, radialProfile_eq_one hx, mul_one, radialInv_eq (by linarith),
      div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ h0'.le
    exact inv_anti₀ (by linarith) (by linarith [he.2])
  refine le_trans ?_ hconst
  rw [intervalIntegral.integral_const, smul_eq_mul]
  have h3 : (1 + 1 / (2 * ((n : ℝ) + 1)) - (1 + 1 / (4 * ((n : ℝ) + 1)))) * (((n : ℝ) + 1) / 3) =
      1 / 12 := by
    field_simp
    ring1
  exact h3.ge

/-- **The radial Laplacian of `radialGreen n`**: for `c > 1/2`, it is
`(2n + 2) coshDistBump (2n + 1) c - (n + 1) coshDistBump n c`, the function
`(c² - 1) (radialGreen n)'(c)` being `∫_{(n + 1)(c - 1)}^{2(n + 1)(c - 1)} θ`. -/
lemma radialLaplacian_radialGreen (hc : 1 / 2 < c) : radialLaplacian (radialGreen n) c =
    2 * (n + 1) * coshDistBump (2 * n + 1) c - (n + 1) * coshDistBump n c := by
  have hB : HasDerivAt (radialGreenDeriv n) (deriv (radialGreenDeriv n) c) c :=
    ((contDiff_radialGreenDeriv n).differentiable (by simp) c).hasDerivAt
  have h1 : HasDerivAt (fun e ↦ (e ^ 2 - 1) * radialGreenDeriv n e)
      (2 * c * radialGreenDeriv n c + (c ^ 2 - 1) * deriv (radialGreenDeriv n) c) c := by
    refine (((hasDerivAt_pow 2 c).sub_const 1).mul hB).congr_deriv ?_
    norm_num
  have h2 : HasDerivAt (fun e : ℝ ↦ ((n : ℝ) + 1) * (e - 1)) ((n : ℝ) + 1) c := by
    simpa using ((hasDerivAt_id c).sub_const 1).const_mul ((n : ℝ) + 1)
  have h3 : HasDerivAt
      (fun e : ℝ ↦ ((n : ℝ) + 1) * (e - 1) * radialProfile (((n : ℝ) + 1) * (e - 1)))
      ((2 * smoothTransition (2 - 2 * (((n : ℝ) + 1) * (c - 1))) -
        smoothTransition (2 - ((n : ℝ) + 1) * (c - 1))) * ((n : ℝ) + 1)) c :=
    HasDerivAt.comp (h₂ := fun x ↦ x * radialProfile x) c
      (hasDerivAt_mul_radialProfile (((n : ℝ) + 1) * (c - 1))) h2
  have hev : (fun e ↦ (e ^ 2 - 1) * radialGreenDeriv n e) =ᶠ[𝓝 c]
      fun e : ℝ ↦ ((n : ℝ) + 1) * (e - 1) * radialProfile (((n : ℝ) + 1) * (e - 1)) := by
    filter_upwards [Ioi_mem_nhds hc] with e he
    exact mul_radialGreenDeriv_eq n (le_of_lt he)
  have h4 : 2 * c * radialGreenDeriv n c + (c ^ 2 - 1) * deriv (radialGreenDeriv n) c =
      (2 * smoothTransition (2 - 2 * (((n : ℝ) + 1) * (c - 1))) -
        smoothTransition (2 - ((n : ℝ) + 1) * (c - 1))) * ((n : ℝ) + 1) :=
    h1.unique (h3.congr_of_eventuallyEq hev)
  have hc1 : (((2 * n + 1 : ℕ) : ℝ) + 1) * (c - 1) = 2 * (((n : ℝ) + 1) * (c - 1)) := by
    push_cast
    ring1
  rw [radialLaplacian, deriv_radialGreen, coshDistBump, coshDistBump, hc1]
  linear_combination h4

/-- The **mass** of the bump `coshDistBump n` as a radial kernel on `ℍ`, the integral of
`coshDistBump n (cosh d(i, w))`; it does not depend on the centre (`integral_kernel_eq`). -/
noncomputable def bumpMass : ℝ :=
  ∫ w, coshDistBump n (dist I w).cosh

lemma bumpMass_pos : 0 < bumpMass n :=
  integral_coshDistBump_pos

lemma radialGreen_eq_zero_of_three_le (hc : 3 ≤ c) : radialGreen n c = 0 := by
  refine radialGreen_eq_zero n ?_
  have h : (2 : ℝ) / (n + 1) ≤ 2 := div_le_self two_pos.le (by simp)
  linarith

/-- **The mass of `coshDistBump (2n + 1)` is half that of `coshDistBump n`**: Green's identity on
`ℍ` for the constant function `1` and the kernel `radialGreen n` gives
`(2n + 2) bumpMass (2n + 1) = (n + 1) bumpMass n`, with no polar coordinates. -/
lemma bumpMass_two_mul_add_one : bumpMass (2 * n + 1) = bumpMass n / 2 := by
  have h : ∫ w : ℍ, (radialGreen n (dist I w).cosh : ℂ) *
      hyperbolicLaplacian (fun _ ↦ (1 : ℂ)) w = ∫ w : ℍ,
        (radialLaplacian (radialGreen n) (dist I w).cosh : ℂ) * (1 : ℂ) :=
    integral_kernel_mul_hyperbolicLaplacian I (contDiff_radialGreen n)
      (fun _ hc ↦ radialGreen_eq_zero_of_three_le n hc) contDiffOn_const
  have h0 (w : ℍ) : hyperbolicLaplacian (fun _ ↦ (1 : ℂ)) w = 0 := by
    simp [hyperbolicLaplacian]
  simp only [h0, mul_zero, integral_zero, mul_one] at h
  have h1 (w : ℍ) : radialLaplacian (radialGreen n) (dist I w).cosh =
      2 * (n + 1) * coshDistBump (2 * n + 1) (dist I w).cosh -
        (n + 1) * coshDistBump n (dist I w).cosh :=
    radialLaplacian_radialGreen n (by linarith [(dist I w).one_le_cosh])
  rw [integral_complex_ofReal] at h
  simp only [h1] at h
  have h2 : ∫ w : ℍ, (2 * ((n : ℝ) + 1) * coshDistBump (2 * n + 1) (dist I w).cosh -
      ((n : ℝ) + 1) * coshDistBump n (dist I w).cosh) = 0 :=
    Complex.ofReal_eq_zero.mp h.symm
  rw [integral_sub ((integrable_kernel I contDiff_coshDistBump.continuous
    fun _ hc ↦ coshDistBump_eq_zero hc).const_mul _)
    ((integrable_kernel I contDiff_coshDistBump.continuous
    fun _ hc ↦ coshDistBump_eq_zero hc).const_mul _), integral_const_mul, integral_const_mul] at h2
  have h3 : ((n : ℝ) + 1) ≠ 0 := by
    positivity
  have h4 : ((n : ℝ) + 1) * (2 * bumpMass (2 * n + 1) - bumpMass n) = 0 := by
    simp only [bumpMass]
    linear_combination h2
  have h5 : 2 * bumpMass (2 * n + 1) - bumpMass n = 0 := (mul_eq_zero.mp h4).resolve_left h3
  linarith

lemma bumpMass_eight_mul_add_seven : bumpMass (8 * n + 7) = bumpMass n / 8 := by
  have h : 8 * n + 7 = 2 * (2 * (2 * n + 1) + 1) + 1 := by
    ring1
  rw [h, bumpMass_two_mul_add_one, bumpMass_two_mul_add_one, bumpMass_two_mul_add_one]
  ring1

variable (c) in
lemma coshDistBump_eq_mul : coshDistBump n c = bumpMass n * coshDistNormalBump n c := by
  rw [coshDistNormalBump, ← bumpMass, mul_inv_cancel_left₀ (bumpMass_pos n).ne']

lemma radialLaplacian_radialGreen_eq_mul (hc : 1 / 2 < c) : radialLaplacian (radialGreen n) c =
    (n + 1) * bumpMass n * (coshDistNormalBump (2 * n + 1) c - coshDistNormalBump n c) := by
  rw [radialLaplacian_radialGreen n hc, coshDistBump_eq_mul (2 * n + 1), coshDistBump_eq_mul n,
    bumpMass_two_mul_add_one]
  ring1

lemma neg_radialGreen_le_coshDistBump (hc : 1 ≤ c) :
    -radialGreen (2 * n + 1) c ≤ coshDistBump n c := by
  have h0 : (0 : ℝ) < n + 1 := by
    positivity
  have he : (((2 * n + 1 : ℕ) : ℝ) + 1) = 2 * ((n : ℝ) + 1) := by
    push_cast
    ring1
  rcases le_total c (1 + 1 / ((n : ℝ) + 1)) with h | h
  · have h1 : ((n : ℝ) + 1) * (c - 1) ≤ 1 := by
      have h2 : c - 1 ≤ 1 / ((n : ℝ) + 1) := by
        linarith
      rwa [le_div_iff₀' h0] at h2
    have h3 : coshDistBump n c = 1 := smoothTransition.one_of_one_le (by linarith)
    rw [h3]
    linarith [neg_one_le_radialGreen (2 * n + 1) hc]
  · have h1 : 1 + 2 / (((2 * n + 1 : ℕ) : ℝ) + 1) ≤ c := by
      rw [he]
      refine le_trans (le_of_eq ?_) h
      field_simp
    rw [radialGreen_eq_zero (2 * n + 1) h1, neg_zero]
    exact coshDistBump_nonneg c

lemma coshDistBump_le_neg_radialGreen (hc : 1 ≤ c) :
    1 / 12 * coshDistBump (8 * n + 7) c ≤ -radialGreen n c := by
  have h0 : (0 : ℝ) < n + 1 := by
    positivity
  rcases le_total c (1 + 1 / (4 * ((n : ℝ) + 1))) with h | h
  · have h1 : coshDistBump (8 * n + 7) c ≤ 1 := smoothTransition.le_one _
    have h2 : radialGreen n c ≤ -(1 / 12) := radialGreen_le_neg n hc h
    linarith
  · have h1 : coshDistBump (8 * n + 7) c = 0 := by
      refine smoothTransition.zero_of_nonpos ?_
      have h2 : 1 / (4 * ((n : ℝ) + 1)) ≤ c - 1 := by
        linarith
      rw [div_le_iff₀' (by positivity)] at h2
      push_cast
      linarith
    rw [h1, mul_zero]
    exact neg_nonneg.mpr (radialGreen_nonpos n hc)

end UpperHalfPlane
