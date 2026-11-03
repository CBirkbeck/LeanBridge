import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CuspNewformExpansion
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.KernelPair
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# The average of a cuspidal function over a ball is bounded by its norm

A cuspidal function on `Γ₀(N) \ ℍ` with character `χ` (`UpperHalfPlane.maassCuspidalSpace`) is a
continuous square-integrable function `g` with `g(γz) = χ(d) g(z)` for `γ ∈ Γ₀(N)` whose constant
term vanishes at every cusp. Let `φ` be a function of class `C¹` vanishing on `[3, ∞)`. Then there
is a constant `C`, depending on `N` and `φ`, such that the square of the average
`∫_ℍ φ(cosh d(z, w)) g(w) dμ(w)` is at most `C ‖g‖²`, for every cuspidal `g` and every `z` in the
fundamental domain `UpperHalfPlane.gammaZeroDomain N`
(`UpperHalfPlane.exists_sq_norm_integral_kernel_mul_le`). So this average is a bounded linear
functional on the cuspidal functions, uniformly in `z`, which fails without the vanishing of the
constant terms. This is the estimate behind the compactness of the integral operators on the
cuspidal space, as in Gelfand, Piatetski-Shapiro and Godement (cf. Iwaniec, *Spectral Methods of
Automorphic Forms*, Chapter 4).

Write `z = σ z'` with `σ ∈ SL(2, ℤ)` and `z'` in the standard domain `𝒟ᵒ`.

* If `Im z' ≥ 6`, the average of `g` around `z` is that of `u = g ∘ σ` around `z'`, and the support
  of the kernel lies above height `1`. In coordinates `w = t + iv`, the inner integral over `t` of
  the kernel against `u`, which has period `N` and mean `0`, is integrated by parts against a
  primitive of `u`, which is periodic and bounded by `∫_{-1/2}^{N - 1/2} |u(s + iv)| ds`; the kernel
  has total variation bounded in `t`, uniformly in `v` and `z'`
  (`UpperHalfPlane.norm_integral_radial_mul_le`). This gives a bound by the integrals of `|u|` on
  the rectangles `(j - 1/2, j + 1/2) × (1, ∞)`, `j < N` (`UpperHalfPlane.maassRectangle`), each of
  them lying in a translate `T^j 𝒟ᵒ` (`UpperHalfPlane.norm_integral_kernel_mul_le`), and the
  integral of `|g|²` on a translate of `𝒟ᵒ` is at most `‖g‖²`
  (`UpperHalfPlane.sq_norm_integral_kernel_mul_comp_smul_le`).
* If `Im z' < 6`, the support of the kernel lies in a compact set independent of `z'`, which is
  covered a bounded number of times by the translates of a fundamental domain, as `SL(2, ℤ)` acts
  properly discontinuously on `ℍ` (`UpperHalfPlane.exists_lintegral_le_mul_of_isCompact`).

## Main definitions

* `UpperHalfPlane.maassCuspidalSpace`: the cuspidal functions on `Γ₀(N) \ ℍ` with character `χ`.
* `UpperHalfPlane.maassRectangle`: the rectangle `(j - 1/2, j + 1/2) × (1, ∞)`.

## Main results

* `UpperHalfPlane.norm_integral_radial_mul_le`: the bound for the integral of a radial kernel
  against a periodic function with mean `0` on a horizontal line.
* `UpperHalfPlane.setIntegral_re_im_mem_prod`, `UpperHalfPlane.integrableOn_re_im_mem_prod_iff'`:
  the invariant integral on a product region in coordinates.
* `UpperHalfPlane.norm_integral_kernel_mul_le`: the bound for the average of a function with
  vanishing constant term high in the cusp.
* `UpperHalfPlane.maassCuspidal_period`: `N` is a period of `g ∘ σ`.
* `UpperHalfPlane.sq_norm_integral_kernel_mul_comp_smul_le`: the bound for a cuspidal function high
  in the cusp.
* `UpperHalfPlane.exists_lintegral_le_mul_of_isCompact`: a compact set is covered a bounded number
  of times by the translates of a fundamental domain.
* `UpperHalfPlane.exists_sq_norm_integral_kernel_mul_le`: the bound for a cuspidal function.
-/

open Function TauCeti MeasureTheory CongruenceSubgroup Matrix Set Topology

open scoped MatrixGroups NNReal Pointwise

namespace UpperHalfPlane

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {g : ℍ → ℂ} {φ : ℝ → ℝ} {A v : ℝ} {z : ℍ} {K : Set ℍ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s t : Set ℝ} (σ : SL(2, ℤ)) (j : ℕ)

/-- **The integral of a radial kernel against a periodic function with mean `0`**: for `φ` of class
`C¹` vanishing on `[3, ∞)`, with `|φ'| ≤ A` on `[1, ∞)`, and `u` continuous with period `h > 0` and
mean `0`, `|∫_ℝ φ(((t - x)² + v² + y²) / (2 y v)) u(t) dt| ≤ 12 A ∫_{-1/2}^{-1/2 + h} |u|`, whatever
`x`, `y > 0` and `v > 0`: integrate by parts against a primitive of `u` on the interval
`|t - x| ≤ √(6 y v)` that contains the support of the kernel. -/
lemma norm_integral_radial_mul_le {x y h : ℝ} {u : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hA : ∀ c, 1 ≤ c → |deriv φ c| ≤ A) (hφ0 : ∀ c, 3 ≤ c → φ c = 0) (hy : 0 < y) (hv : 0 < v)
    (hh : 0 < h) (hu : Continuous u) (hper : Periodic u h)
    (hmean : ∫ t in (-(1 / 2) : ℝ)..-(1 / 2) + h, u t = 0) :
    ‖∫ t, (φ (((t - x) ^ 2 + v ^ 2 + y ^ 2) / (2 * y * v)) : ℂ) * u t‖ ≤
      12 * A * ∫ t in (-(1 / 2) : ℝ)..-(1 / 2) + h, ‖u t‖ := by
  let c : ℝ → ℝ := fun t ↦ ((t - x) ^ 2 + v ^ 2 + y ^ 2) / (2 * y * v)
  let T : ℝ := √(6 * y * v)
  have hT : T ^ 2 = 6 * y * v := Real.sq_sqrt (by positivity)
  have hT0 : 0 < T := Real.sqrt_pos.mpr (by positivity)
  have hd : 0 < 2 * y * v := by
    positivity
  have hyv : y * v ≠ 0 := (mul_pos hy hv).ne'
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 1 le_rfl)
  have hc1 (t : ℝ) : 1 ≤ c t := by
    rw [le_div_iff₀ hd]
    nlinarith [sq_nonneg (v - y), sq_nonneg (t - x)]
  have hc3 (t : ℝ) (ht : T ≤ |t - x|) : 3 ≤ c t := by
    rw [le_div_iff₀ hd]
    have h1 : T ^ 2 ≤ (t - x) ^ 2 := by
      rw [← sq_abs (t - x)]
      exact pow_le_pow_left₀ hT0.le ht 2
    nlinarith [sq_nonneg v, sq_nonneg y]
  have hc' (t : ℝ) : HasDerivAt c ((t - x) / (y * v)) t := by
    have h1 : HasDerivAt (fun t ↦ (t - x) ^ 2 + v ^ 2 + y ^ 2) (2 * (t - x)) t := by
      simpa using ((((hasDerivAt_id t).sub_const x).pow 2).add_const (v ^ 2)).add_const (y ^ 2)
    refine (h1.div_const (2 * y * v)).congr_deriv ?_
    field_simp
  have hφd (c₀ : ℝ) : HasDerivAt φ (deriv φ c₀) c₀ :=
    (hφ.differentiable one_ne_zero c₀).hasDerivAt
  have hg' (t : ℝ) : HasDerivAt (fun t ↦ φ (c t)) (deriv φ (c t) * ((t - x) / (y * v))) t :=
    (hφd (c t)).comp t (hc' t)
  let U : ℝ → ℂ := fun t ↦ ∫ s in (-(1 / 2) : ℝ)..t, u s
  have hU (t : ℝ) : HasDerivAt U (u t) t :=
    intervalIntegral.integral_hasDerivAt_right (hu.intervalIntegrable _ _)
      (hu.stronglyMeasurableAtFilter _ _) hu.continuousAt
  have hUper : Periodic U h := fun t ↦ by
    have h1 : U (t + h) = U t + ∫ s in t..t + h, u s :=
      (intervalIntegral.integral_add_adjacent_intervals (hu.intervalIntegrable _ _)
        (hu.intervalIntegrable _ _)).symm
    rw [h1, hper.intervalIntegral_add_eq t (-(1 / 2)), hmean, add_zero]
  have hUb (t : ℝ) : ‖U t‖ ≤ ∫ t in (-(1 / 2) : ℝ)..-(1 / 2) + h, ‖u t‖ := by
    rcases hUper.exists_mem_Ico hh t (-(1 / 2)) with ⟨s, hs, hts⟩
    rw [hts]
    have hs0 : (-(1 / 2) : ℝ) ≤ s := hs.1
    refine (intervalIntegral.norm_integral_le_integral_norm hs0).trans ?_
    refine intervalIntegral.integral_mono_interval le_rfl hs0 hs.2.le ?_
      (hu.norm.intervalIntegrable _ _)
    exact .of_forall fun s ↦ norm_nonneg _
  have hg0 (t : ℝ) (ht : T ≤ |t - x|) : φ (c t) = 0 := hφ0 _ (hc3 t ht)
  have hsupp : support (fun t ↦ (φ (c t) : ℂ) * u t) ⊆ Ioc (x - T) (x + T) := by
    intro t ht
    have h1 : φ (c t) ≠ 0 := fun h0 ↦ ht (by simp [h0])
    have h2 : |t - x| < T := not_le.mp fun h3 ↦ h1 (hg0 t h3)
    exact ⟨by linarith [(abs_lt.mp h2).1], by linarith [(abs_lt.mp h2).2]⟩
  have hbyparts : ∫ t in (x - T)..x + T, (φ (c t) : ℂ) * u t =
      -∫ t in (x - T)..x + T, ((deriv φ (c t) * ((t - x) / (y * v)) : ℝ) : ℂ) * U t := by
    have hgc : Continuous fun t ↦ ((deriv φ (c t) * ((t - x) / (y * v)) : ℝ) : ℂ) := by
      have hcc : Continuous c := continuous_iff_continuousAt.mpr fun t ↦ (hc' t).continuousAt
      exact Complex.continuous_ofReal.comp (((hφ.continuous_deriv le_rfl).comp hcc).mul
        ((continuous_id.sub continuous_const).div_const _))
    have h1 : ∫ t in (x - T)..x + T, (φ (c t) : ℂ) * u t =
        (φ (c (x + T)) : ℂ) * U (x + T) - (φ (c (x - T)) : ℂ) * U (x - T) -
          ∫ t in (x - T)..x + T, ((deriv φ (c t) * ((t - x) / (y * v)) : ℝ) : ℂ) * U t :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t _ ↦ (hg' t).ofReal_comp)
        (fun t _ ↦ hU t) (hgc.intervalIntegrable _ _) (hu.intervalIntegrable _ _)
    have h2 : φ (c (x + T)) = 0 := hg0 _ (by simp [abs_of_pos hT0])
    have h3 : φ (c (x - T)) = 0 := hg0 _ (by simp [abs_of_pos hT0])
    rw [h1, h2, h3]
    simp
  have hbound : ‖∫ t in (x - T)..x + T, ((deriv φ (c t) * ((t - x) / (y * v)) : ℝ) : ℂ) * U t‖ ≤
      A * (T / (y * v)) * (∫ t in (-(1 / 2) : ℝ)..-(1 / 2) + h, ‖u t‖) * |x + T - (x - T)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
    rw [uIoc_of_le (by linarith)] at ht
    have h1 : |t - x| ≤ T := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (mul_pos hy hv)]
    have h2 : |t - x| / (y * v) ≤ T / (y * v) :=
      div_le_div_of_nonneg_right h1 (mul_pos hy hv).le
    exact mul_le_mul (mul_le_mul (hA _ (hc1 t)) h2 (by positivity) hA0) (hUb t) (norm_nonneg _)
      (by positivity)
  have heq : ∫ t, (φ (c t) : ℂ) * u t = ∫ t in (x - T)..x + T, (φ (c t) : ℂ) * u t :=
    (intervalIntegral.integral_eq_integral_of_support_subset hsupp).symm
  have hle : A * (T / (y * v)) * (∫ t in (-(1 / 2) : ℝ)..-(1 / 2) + h, ‖u t‖) * |x + T - (x - T)| =
      12 * A * ∫ t in (-(1 / 2) : ℝ)..-(1 / 2) + h, ‖u t‖ := by
    have h1 : x + T - (x - T) = 2 * T := by
      ring1
    rw [h1, abs_of_pos (by positivity)]
    have h2 : T / (y * v) * (2 * T) = 12 := by
      field_simp
      rw [hT]
      ring1
    linear_combination (A * ∫ t in (-(1 / 2) : ℝ)..-(1 / 2) + h, ‖u t‖) * h2
  rw [heq, hbyparts, norm_neg, ← hle]
  exact hbound

/-- **The integral over a product region in coordinates**: for measurable `s, t ⊆ ℝ` with
`t ⊆ (0, ∞)`, the integral over `{z ∈ ℍ | Re z ∈ s, Im z ∈ t}` for the invariant measure is the
Lebesgue integral over `s × t` of `y⁻² G(x + iy)`. -/
lemma setIntegral_re_im_mem_prod (G : ℍ → E) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (ht0 : t ⊆ Ioi 0) : ∫ z in {z : ℍ | z.re ∈ s ∧ z.im ∈ t}, G z = ∫ p in s ×ˢ t,
      ((p.2 ^ 2)⁻¹ : ℝ) • G (ofComplex (p.1 + p.2 * Complex.I)) := by
  have hm : MeasurableSet {z : ℍ | z.re ∈ s ∧ z.im ∈ t} :=
    (hs.preimage continuous_re.measurable).inter (ht.preimage continuous_im.measurable)
  rw [volume_def, setIntegral_withDensity_eq_setIntegral_smul measurable_volume_density _ hm]
  have h1 : ∫ z in {z : ℍ | z.re ∈ s ∧ z.im ∈ t}, ((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) • G z
      ∂(Measure.comap UpperHalfPlane.coe volume) =
        ∫ z in UpperHalfPlane.coe ⁻¹' (UpperHalfPlane.coe '' {z : ℍ | z.re ∈ s ∧ z.im ∈ t}),
          ((((z : ℂ).im ^ 2)⁻¹ : ℝ) • G (ofComplex (z : ℂ)))
            ∂(Measure.comap UpperHalfPlane.coe volume) := by
    rw [preimage_image_eq _ measurableEmbedding_coe.injective]
    refine setIntegral_congr_fun hm fun z _ ↦ ?_
    rw [ofComplex_apply, NNReal.smul_def]
    simp
  refine h1.trans <| (measurableEmbedding_coe.setIntegral_map
    (fun c : ℂ ↦ (((c.im ^ 2)⁻¹ : ℝ) • G (ofComplex c))) _).symm.trans ?_
  rw [measurableEmbedding_coe.map_comap,
    Measure.restrict_restrict_of_subset (image_subset_range _ _), image_coe_re_im_mem_prod ht0]
  refine Eq.trans ?_ (Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding _ _)
  refine setIntegral_congr_fun ?_ fun c _ ↦ ?_
  · exact Complex.measurableEquivRealProd.measurable (hs.prod ht)
  · simp

/-- **Integrability over a product region in coordinates**: for measurable `s, t ⊆ ℝ` with
`t ⊆ (0, ∞)`, `G` is integrable on `{z ∈ ℍ | Re z ∈ s, Im z ∈ t}` for the invariant measure exactly
when `y⁻² G(x + iy)` is Lebesgue integrable on `s × t`. This is
`UpperHalfPlane.integrableOn_re_im_mem_prod_iff` for functions with values in a normed space. -/
lemma integrableOn_re_im_mem_prod_iff' {G : ℍ → E} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (ht0 : t ⊆ Ioi 0) : IntegrableOn G {z : ℍ | z.re ∈ s ∧ z.im ∈ t} ↔ IntegrableOn
      (fun p : ℝ × ℝ ↦ ((p.2 ^ 2)⁻¹ : ℝ) • G (ofComplex (p.1 + p.2 * Complex.I))) (s ×ˢ t) := by
  have hm : MeasurableSet {z : ℍ | z.re ∈ s ∧ z.im ∈ t} :=
    (hs.preimage continuous_re.measurable).inter (ht.preimage continuous_im.measurable)
  rw [IntegrableOn, volume_def, restrict_withDensity hm,
    integrable_withDensity_iff_integrable_smul measurable_volume_density, ← IntegrableOn]
  have h1 : IntegrableOn (fun z : ℍ ↦ ((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) • G z)
      {z : ℍ | z.re ∈ s ∧ z.im ∈ t} (Measure.comap UpperHalfPlane.coe volume) ↔
        IntegrableOn ((fun c : ℂ ↦ ((c.im ^ 2)⁻¹ : ℝ) • G (ofComplex c)) ∘ UpperHalfPlane.coe)
          (UpperHalfPlane.coe ⁻¹' (UpperHalfPlane.coe '' {z : ℍ | z.re ∈ s ∧ z.im ∈ t}))
            (Measure.comap UpperHalfPlane.coe volume) := by
    rw [preimage_image_eq _ measurableEmbedding_coe.injective]
    refine integrableOn_congr_fun (fun z _ ↦ ?_) hm
    simp [NNReal.smul_def]
  rw [h1, ← measurableEmbedding_coe.integrableOn_map_iff, measurableEmbedding_coe.map_comap,
    IntegrableOn, Measure.restrict_restrict_of_subset (image_subset_range _ _), ← IntegrableOn,
    image_coe_re_im_mem_prod ht0,
    ← Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding]
  refine integrableOn_congr_fun (fun c _ ↦ ?_)
    (Complex.measurableEquivRealProd.measurable (hs.prod ht))
  simp

lemma continuous_ofComplex_add_mul_I (hv : 0 < v) :
    Continuous fun t : ℝ ↦ ofComplex ((t : ℂ) + v * Complex.I) := by
  refine isEmbedding_coe.continuous_iff.mpr ?_
  have h : (UpperHalfPlane.coe ∘ fun t : ℝ ↦ ofComplex ((t : ℂ) + v * Complex.I)) =
      fun t : ℝ ↦ (t : ℂ) + v * Complex.I := by
    funext t
    exact coe_ofComplex_of_im_pos (by simpa using hv)
  rw [h]
  fun_prop

/-- The rectangle `(j - 1/2, j + 1/2) × (1, ∞)` of `ℍ`, which lies in the translate `T^j 𝒟ᵒ` of the
open standard fundamental domain. -/
def maassRectangle : Set ℍ :=
  {w : ℍ | w.re ∈ Ioo ((j : ℝ) - 1 / 2) (j + 1 / 2) ∧ w.im ∈ Ioi 1}

variable (z) in
lemma integrable_kernel_mul_of_continuous (hφ : Continuous φ) (hφ0 : ∀ c, 3 ≤ c → φ c = 0)
    (hg : Continuous g) : Integrable fun w : ℍ ↦ (φ (Real.cosh (dist z w)) : ℂ) * g w := by
  refine ((Complex.continuous_ofReal.comp (continuous_kernel_right z hφ)).mul hg
    |>.integrable_of_hasCompactSupport ?_)
  have h1 : HasCompactSupport fun w ↦ φ (Real.cosh (dist z w)) := hasCompactSupport_kernel z hφ0
  exact (h1.comp_left (g := fun x : ℝ ↦ (x : ℂ)) (by simp)).mul_right

variable (N) in
lemma sum_setIntegral_Ioo_eq {h : ℝ → ℝ} (hc : Continuous h) : ∑ j ∈ Finset.range N,
    ∫ s in Ioo ((j : ℝ) - 1 / 2) (j + 1 / 2), h s = ∫ s in (-(1 / 2) : ℝ)..-(1 / 2) + N, h s := by
  have hterm (j : ℕ) : ∫ s in ((j : ℝ) - 1 / 2)..(((j + 1 : ℕ) : ℝ) - 1 / 2), h s =
      ∫ s in Ioo ((j : ℝ) - 1 / 2) (j + 1 / 2), h s := by
    have e : ((j + 1 : ℕ) : ℝ) - 1 / 2 = j + 1 / 2 := by
      push_cast
      ring1
    rw [e, intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  have h2 : ∑ j ∈ Finset.range N, ∫ s in ((j : ℝ) - 1 / 2)..(((j + 1 : ℕ) : ℝ) - 1 / 2), h s =
      ∫ s in (((0 : ℕ) : ℝ) - 1 / 2)..((N : ℝ) - 1 / 2), h s :=
    intervalIntegral.sum_integral_adjacent_intervals fun k _ ↦ hc.intervalIntegrable _ _
  have e0 : ((0 : ℕ) : ℝ) - 1 / 2 = -(1 / 2) := by
    norm_num
  have eN : (N : ℝ) - 1 / 2 = -(1 / 2) + N := by
    ring1
  simp only [hterm] at h2
  rwa [e0, eN] at h2

/-- **The average of a function with vanishing constant term high in the cusp**: for `φ` of class
`C¹` vanishing on `[3, ∞)`, with `|φ'| ≤ A` on `[1, ∞)`, and `u` continuous on `ℍ`, periodic of
period `N ≠ 0` with `∫_0^N u(t + iv) dt = 0` for every `v > 0`, and `Im z ≥ 6`,
`|∫_ℍ φ(cosh d(z, w)) u(w) dμ(w)| ≤ 12 A ∑_{j < N} ∫_{R_j} |u| dμ`, for the rectangles
`R_j = (j - 1/2, j + 1/2) × (1, ∞)` of the strip above height `1`. -/
lemma norm_integral_kernel_mul_le {u : ℍ → ℂ} (hN : 0 < N) (hφ : ContDiff ℝ 1 φ)
    (hA : ∀ c, 1 ≤ c → |deriv φ c| ≤ A) (hφ0 : ∀ c, 3 ≤ c → φ c = 0) (hu : Continuous u)
    (hper : ∀ t v : ℝ, 0 < v → u (ofComplex (((t + N : ℝ) : ℂ) + v * Complex.I)) =
      u (ofComplex ((t : ℂ) + v * Complex.I)))
    (hmean : ∀ v : ℝ, 0 < v → ∫ t in (0 : ℝ)..N, u (ofComplex ((t : ℂ) + v * Complex.I)) = 0)
    (hint : ∀ j : ℕ, IntegrableOn (fun w ↦ ‖u w‖) (maassRectangle j)) (hz : 6 ≤ z.im) :
    ‖∫ w : ℍ, (φ (Real.cosh (dist z w)) : ℂ) * u w‖ ≤
      12 * A * ∑ j ∈ Finset.range N, ∫ w in maassRectangle j, ‖u w‖ := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hy : 0 < z.im := z.im_pos
  let c : ℝ → ℝ → ℝ := fun v t ↦ ((t - z.re) ^ 2 + v ^ 2 + z.im ^ 2) / (2 * z.im * v)
  have hcosh (v t : ℝ) (hv : 0 < v) :
      Real.cosh (dist z (ofComplex ((t : ℂ) + v * Complex.I))) = c v t := by
    rw [cosh_dist_eq_coshDist, coshDist, coe_ofComplex_of_im_pos (by simpa using hv)]
    simp [c]
  have hG : Integrable fun w : ℍ ↦ (φ (Real.cosh (dist z w)) : ℂ) * u w :=
    integrable_kernel_mul_of_continuous z hφ.continuous hφ0 hu
  have hset : {w : ℍ | w.re ∈ (univ : Set ℝ) ∧ w.im ∈ Ioi 0} = univ := by
    ext w
    simpa using w.im_pos
  have hcoord : IntegrableOn (fun p : ℝ × ℝ ↦ ((p.2 ^ 2)⁻¹ : ℝ) •
      ((φ (Real.cosh (dist z (ofComplex (p.1 + p.2 * Complex.I)))) : ℂ) *
        u (ofComplex (p.1 + p.2 * Complex.I)))) (univ ×ˢ Ioi 0) :=
    (integrableOn_re_im_mem_prod_iff' MeasurableSet.univ measurableSet_Ioi subset_rfl).mp
      (by rw [hset]; exact hG.integrableOn)
  rw [Measure.volume_eq_prod] at hcoord
  have hfub : ∫ w : ℍ, (φ (Real.cosh (dist z w)) : ℂ) * u w = ∫ v in Ioi (0 : ℝ),
      ((v ^ 2)⁻¹ : ℝ) • ∫ t : ℝ, (φ (c v t) : ℂ) * u (ofComplex ((t : ℂ) + v * Complex.I)) := by
    rw [← setIntegral_univ, ← hset, setIntegral_re_im_mem_prod _ MeasurableSet.univ
      measurableSet_Ioi subset_rfl, Measure.volume_eq_prod, ← setIntegral_prod_swap]
    refine (setIntegral_prod _ hcoord.swap).trans ?_
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv ↦ ?_
    rw [Measure.restrict_univ]
    simp only [Function.comp_apply, Prod.swap_prod_mk]
    rw [integral_smul]
    refine congrArg _ (integral_congr_ae (.of_forall fun t ↦ ?_))
    dsimp only
    rw [hcosh v t hv]
  have hlow (v : ℝ) (hv : v ∈ Ioi (0 : ℝ) \ Ioi 1) :
      ((v ^ 2)⁻¹ : ℝ) • ∫ t : ℝ, (φ (c v t) : ℂ) * u (ofComplex ((t : ℂ) + v * Complex.I)) = 0 := by
    have hv0 : 0 < v := hv.1
    have hv2 : v ≤ 1 := not_lt.mp hv.2
    have h1 (t : ℝ) : φ (c v t) = 0 := hφ0 _ <| by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (t - z.re), sq_nonneg v, mul_le_mul_of_nonneg_left hv2 hy.le,
        mul_le_mul_of_nonneg_left hz hy.le]
    simp [h1]
  rw [hfub, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi zero_le_one) hlow]
  have hcoordj (j : ℕ) : Integrable
      (fun p : ℝ × ℝ ↦ ((p.2 ^ 2)⁻¹ : ℝ) • ‖u (ofComplex (p.1 + p.2 * Complex.I))‖)
      ((volume.restrict (Ioo ((j : ℝ) - 1 / 2) (j + 1 / 2))).prod (volume.restrict (Ioi 1))) := by
    have h : IntegrableOn
        (fun p : ℝ × ℝ ↦ ((p.2 ^ 2)⁻¹ : ℝ) • ‖u (ofComplex (p.1 + p.2 * Complex.I))‖)
        (Ioo ((j : ℝ) - 1 / 2) (j + 1 / 2) ×ˢ Ioi 1) :=
      (integrableOn_re_im_mem_prod_iff' measurableSet_Ioo measurableSet_Ioi
        (Ioi_subset_Ioi zero_le_one)).mp (hint j)
    rwa [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  have hR (j : ℕ) : ∫ w in maassRectangle j, ‖u w‖ =
      ∫ v in Ioi (1 : ℝ), ∫ s in Ioo ((j : ℝ) - 1 / 2) (j + 1 / 2),
        ((v ^ 2)⁻¹ : ℝ) • ‖u (ofComplex ((s : ℂ) + v * Complex.I))‖ := by
    rw [maassRectangle, setIntegral_re_im_mem_prod _ measurableSet_Ioo measurableSet_Ioi
      (Ioi_subset_Ioi zero_le_one), Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integral_prod_symm _ (hcoordj j)
  simp only [hR]
  rw [← integral_finsetSum _ fun j _ ↦ (hcoordj j).integral_prod_right, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (((integrable_finsetSum _
    fun j _ ↦ (hcoordj j).integral_prod_right)).const_mul _)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun v hv ↦ ?_)
  have hv0 : 0 < v := zero_lt_one.trans hv
  have huv : Continuous fun t : ℝ ↦ u (ofComplex ((t : ℂ) + v * Complex.I)) :=
    hu.comp (continuous_ofComplex_add_mul_I hv0)
  have hperv : Periodic (fun t : ℝ ↦ u (ofComplex ((t : ℂ) + v * Complex.I))) (N : ℝ) :=
    fun t ↦ hper t v hv0
  have hmeanv :
      ∫ t in (-(1 / 2) : ℝ)..-(1 / 2) + N, u (ofComplex ((t : ℂ) + v * Complex.I)) = 0 := by
    rw [hperv.intervalIntegral_add_eq (-(1 / 2)) 0, zero_add]
    exact hmean v hv0
  have h1 : ‖∫ t : ℝ, (φ (c v t) : ℂ) * u (ofComplex ((t : ℂ) + v * Complex.I))‖ ≤
      12 * A * ∫ t in (-(1 / 2) : ℝ)..-(1 / 2) + N, ‖u (ofComplex ((t : ℂ) + v * Complex.I))‖ :=
    norm_integral_radial_mul_le hφ hA hφ0 hy hv0 hN' huv hperv hmeanv
  rw [← sum_setIntegral_Ioo_eq N huv.norm] at h1
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have h3 : (v ^ 2)⁻¹ * ‖∫ t : ℝ, (φ (c v t) : ℂ) * u (ofComplex ((t : ℂ) + v * Complex.I))‖ ≤
      (v ^ 2)⁻¹ * (12 * A * ∑ j ∈ Finset.range N, ∫ s in Ioo ((j : ℝ) - 1 / 2) (j + 1 / 2),
        ‖u (ofComplex ((s : ℂ) + v * Complex.I))‖) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  refine h3.trans (le_of_eq ?_)
  simp only [smul_eq_mul, integral_const_mul, ← Finset.mul_sum]
  ring1

lemma continuous_sl_smul : Continuous fun τ : ℍ ↦ σ • τ :=
  continuous_const_smul (SpecialLinearGroup.mapGL ℝ σ)

lemma continuous_smul_ofComplex_add_mul_I (hg : Continuous g) (hv : 0 < v) :
    Continuous fun t : ℝ ↦ g (σ • ofComplex ((t : ℂ) + v * Complex.I)) :=
  hg.comp ((continuous_sl_smul σ).comp (continuous_ofComplex_add_mul_I hv))

variable (N χ) in
/-- The space of the **cuspidal functions** on `Γ₀(N) \ ℍ` with character `χ`: the continuous
functions `g` on `ℍ` with `g(γz) = χ(d) g(z)` for `γ = !![a, b; c, d] ∈ Γ₀(N)`, square-integrable on
`Γ₀(N) \ ℍ`, whose constant term vanishes at every cusp: `∫_0^N g(γ(t + iy)) dt = 0` for every
`γ ∈ SL(2, ℤ)` and `y > 0` (`N` being a period of `g ∘ γ`, `maassCuspidal_period`), as for
`IsMaassCuspNewform`. The elements of this space are not assumed to be eigenfunctions of the
Laplacian: it contains the finite sums of Maass cusp forms with different eigenvalues. -/
noncomputable def maassCuspidalSpace : Submodule ℂ (ℍ → ℂ) where
  carrier := {g | Continuous g ∧ (∀ γ ∈ Gamma0 N, ∀ τ : ℍ, g (γ • τ) = χ (γ 1 1 : ℤ) * g τ) ∧
    IntegrableOn (fun z ↦ ‖g z‖ ^ 2) (gammaZeroDomain N) ∧ ∀ γ : SL(2, ℤ), ∀ y : ℝ, 0 < y →
      ∫ t in (0 : ℝ)..N, g (γ • ofComplex ((t : ℂ) + y * Complex.I)) = 0}
  add_mem' {g h} hg hh := by
    refine ⟨hg.1.add hh.1, fun γ hγ τ ↦ ?_, ?_, fun γ y hy ↦ ?_⟩
    · simp only [Pi.add_apply]
      rw [hg.2.1 γ hγ τ, hh.2.1 γ hγ τ]
      ring1
    · refine (memLp_two_iff_integrable_sq_norm (hg.1.add hh.1).aestronglyMeasurable).mp ?_
      exact ((memLp_two_iff_integrable_sq_norm hg.1.aestronglyMeasurable).mpr hg.2.2.1).add
        ((memLp_two_iff_integrable_sq_norm hh.1.aestronglyMeasurable).mpr hh.2.2.1)
    · simp only [Pi.add_apply]
      rw [intervalIntegral.integral_add
        ((continuous_smul_ofComplex_add_mul_I γ hg.1 hy).intervalIntegrable _ _)
        ((continuous_smul_ofComplex_add_mul_I γ hh.1 hy).intervalIntegrable _ _), hg.2.2.2 γ y hy,
        hh.2.2.2 γ y hy, add_zero]
  zero_mem' := ⟨continuous_const, by simp, by simp, by simp⟩
  smul_mem' c g hg := by
    refine ⟨continuous_const.smul hg.1, fun γ hγ τ ↦ ?_, ?_, fun γ y hy ↦ ?_⟩
    · simp only [Pi.smul_apply]
      rw [hg.2.1 γ hγ τ]
      ring1
    · simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
      exact hg.2.2.1.const_mul _
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [intervalIntegral.integral_const_mul, hg.2.2.2 γ y hy, mul_zero]

lemma norm_smul_eq_of_mem_maassCuspidalSpace (hg : g ∈ maassCuspidalSpace N χ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) (τ : ℍ) : ‖g (γ • τ)‖ = ‖g τ‖ := by
  rw [hg.2.1 γ hγ τ, norm_mul, norm_dirichletCharacter_of_mem_gamma0 χ hγ, one_mul]

lemma setIntegral_sl_smul_eq {ψ : ℍ → ℝ} (k : SL(2, ℤ)) (hψ : ∀ u, ψ (k • u) = ψ u) :
    ∫ u in k • K, ψ u = ∫ u in K, ψ u := by
  have h : ∫ u in (k • ·) ⁻¹' (k • K), ψ (k • u) = ∫ u in k • K, ψ u :=
    (measurePreserving_smul k volume).setIntegral_preimage_emb
      (measurableEmbedding_const_smul k) ψ (k • K)
  rw [← h, Set.preimage_smul, inv_smul_smul]
  exact integral_congr_ae (.of_forall hψ)

variable (τ : SL(2, ℤ))

lemma exists_mem_gamma0_eq_mul_out_inv :
    ∃ k ∈ Gamma0 N, ∃ q : SL(2, ℤ) ⧸ (Gamma0 N).withCenter, τ = k * (q.out : SL(2, ℤ))⁻¹ := by
  rcases QuotientGroup.mk_out_eq_mul (Gamma0 N).withCenter τ⁻¹ with ⟨k, hk⟩
  refine ⟨k, (Subgroup.withCenter_eq_self_iff.mpr <| CongruenceSubgroup.center_le_Gamma0 N).le k.2,
    QuotientGroup.mk τ⁻¹, ?_⟩
  rw [hk]
  group

lemma out_inv_smul_fdo_subset (q : SL(2, ℤ) ⧸ (Gamma0 N).withCenter) :
    (q.out : SL(2, ℤ))⁻¹ • ModularGroup.fdo ⊆ gammaZeroDomain N :=
  subset_iUnion (fun q : SL(2, ℤ) ⧸ (Gamma0 N).withCenter ↦
    (q.out : SL(2, ℤ))⁻¹ • ModularGroup.fdo) q

lemma integrableOn_norm_sq_smul_fdo_of_mem (hg : g ∈ maassCuspidalSpace N χ) :
    IntegrableOn (fun u ↦ ‖g u‖ ^ 2) (τ • ModularGroup.fdo) := by
  rcases exists_mem_gamma0_eq_mul_out_inv (N := N) τ with ⟨k, hk, q, rfl⟩
  rw [mul_smul, integrableOn_sl_smul_iff k _ fun u ↦ by
    rw [norm_smul_eq_of_mem_maassCuspidalSpace hg (inv_mem hk)]]
  exact hg.2.2.1.mono_set (out_inv_smul_fdo_subset q)

lemma setIntegral_norm_sq_smul_fdo_le (hg : g ∈ maassCuspidalSpace N χ) :
    ∫ u in τ • ModularGroup.fdo, ‖g u‖ ^ 2 ≤ ∫ u in gammaZeroDomain N, ‖g u‖ ^ 2 := by
  rcases exists_mem_gamma0_eq_mul_out_inv (N := N) τ with ⟨k, hk, q, rfl⟩
  rw [mul_smul, setIntegral_sl_smul_eq k fun u ↦ by
    rw [norm_smul_eq_of_mem_maassCuspidalSpace hg hk]]
  exact setIntegral_mono_set hg.2.2.1 (.of_forall fun u ↦ by positivity)
    (out_inv_smul_fdo_subset q).eventuallyLE

lemma integrableOn_norm_sq_comp_sl_smul (hg : g ∈ maassCuspidalSpace N χ) :
    IntegrableOn (fun w ↦ ‖g (σ • w)‖ ^ 2) (τ • ModularGroup.fdo) := by
  have h : IntegrableOn ((fun u ↦ ‖g u‖ ^ 2) ∘ (σ • ·)) ((σ • ·) ⁻¹' ((σ * τ) • ModularGroup.fdo)) ↔
      IntegrableOn (fun u ↦ ‖g u‖ ^ 2) ((σ * τ) • ModularGroup.fdo) :=
    (measurePreserving_smul σ volume).integrableOn_comp_preimage (measurableEmbedding_const_smul σ)
  rw [Set.preimage_smul, smul_smul, inv_mul_cancel_left] at h
  exact h.mpr (integrableOn_norm_sq_smul_fdo_of_mem _ hg)

lemma setIntegral_norm_sq_comp_smul_le (hg : g ∈ maassCuspidalSpace N χ) :
    ∫ w in τ • ModularGroup.fdo, ‖g (σ • w)‖ ^ 2 ≤ ∫ u in gammaZeroDomain N, ‖g u‖ ^ 2 := by
  have h : ∫ w in (σ • ·) ⁻¹' ((σ * τ) • ModularGroup.fdo), ‖g (σ • w)‖ ^ 2 =
      ∫ u in (σ * τ) • ModularGroup.fdo, ‖g u‖ ^ 2 :=
    (measurePreserving_smul σ volume).setIntegral_preimage_emb
      (measurableEmbedding_const_smul σ) (fun u ↦ ‖g u‖ ^ 2) ((σ * τ) • ModularGroup.fdo)
  rw [Set.preimage_smul, smul_smul, inv_mul_cancel_left] at h
  rw [h]
  exact setIntegral_norm_sq_smul_fdo_le _ hg

/-- **`N` is a period of `g ∘ σ`** for a function `g` transforming under `Γ₀(N)` with a character
modulo `N` and `σ ∈ SL(2, ℤ)`, as `σ T^N σ⁻¹ ∈ Γ(N)`. -/
lemma maassCuspidal_period (hg : ∀ γ ∈ Gamma0 N, ∀ τ : ℍ, g (γ • τ) = χ (γ 1 1 : ℤ) * g τ) (x : ℝ)
    (hv : 0 < v) : g (σ • ofComplex (((x + N : ℝ) : ℂ) + v * Complex.I)) =
      g (σ • ofComplex ((x : ℂ) + v * Complex.I)) := by
  have hw : 0 < ((x : ℂ) + v * Complex.I).im := by
    simpa using hv
  have hT : ModularGroup.T ^ (N : ℤ) ∈ Gamma N := by
    simpa using ModularGroup_T_pow_mem_Gamma (N : ℤ) N dvd_rfl
  have hγ : σ * ModularGroup.T ^ (N : ℤ) * σ⁻¹ ∈ Gamma N :=
    (Gamma_normal N).conj_mem _ hT σ
  have h1 : ofComplex (((x + N : ℝ) : ℂ) + v * Complex.I) =
      ModularGroup.T ^ (N : ℤ) • ofComplex ((x : ℂ) + v * Complex.I) := by
    ext
    rw [ModularGroup.coe_T_zpow_smul_eq, coe_ofComplex_of_im_pos hw,
      coe_ofComplex_of_im_pos (by simpa using hv)]
    push_cast
    ring1
  have h2 : σ • ModularGroup.T ^ (N : ℤ) • ofComplex ((x : ℂ) + v * Complex.I) =
      (σ * ModularGroup.T ^ (N : ℤ) * σ⁻¹) • σ • ofComplex ((x : ℂ) + v * Complex.I) := by
    rw [smul_smul, smul_smul, inv_mul_cancel_right]
  rw [h1, h2, hg _ (Gamma0_mem.mpr (Gamma_mem.mp hγ).2.2.1), (Gamma_mem.mp hγ).2.2.2, map_one,
    one_mul]

lemma rectangle_subset_smul_fdo :
    maassRectangle j ⊆ (ModularGroup.T ^ (j : ℤ)) • ModularGroup.fdo := by
  rintro w ⟨hx, hy⟩
  refine Set.mem_smul_set.mpr ⟨(ModularGroup.T ^ (j : ℤ))⁻¹ • w, ?_, smul_inv_smul _ w⟩
  have h : ((w : ℂ)) = ((ModularGroup.T ^ (j : ℤ))⁻¹ • w : ℍ) + (j : ℤ) := by
    rw [← ModularGroup.coe_T_zpow_smul_eq, smul_inv_smul]
  have hre : ((ModularGroup.T ^ (j : ℤ))⁻¹ • w : ℍ).re = w.re - j := by
    have h1 : (w : ℂ).re = (((ModularGroup.T ^ (j : ℤ))⁻¹ • w : ℍ) + ((j : ℤ) : ℂ) : ℂ).re :=
      congrArg Complex.re h
    simp only [Complex.add_re, Int.cast_natCast, Complex.natCast_re, coe_re] at h1
    linarith
  have him : ((ModularGroup.T ^ (j : ℤ))⁻¹ • w : ℍ).im = w.im := by
    have h1 : (w : ℂ).im = (((ModularGroup.T ^ (j : ℤ))⁻¹ • w : ℍ) + ((j : ℤ) : ℂ) : ℂ).im :=
      congrArg Complex.im h
    simp only [Complex.add_im, Int.cast_natCast, Complex.natCast_im, add_zero] at h1
    exact h1.symm
  have hx1 : (j : ℝ) - 1 / 2 < w.re := hx.1
  have hx2 : w.re < (j : ℝ) + 1 / 2 := hx.2
  have hy1 : 1 < w.im := hy
  refine ⟨?_, ?_⟩
  · rw [Complex.normSq_apply, coe_re, coe_im, hre, him]
    nlinarith [mul_self_nonneg (w.re - j)]
  · rw [hre, abs_lt]
    constructor <;> linarith

lemma volume_rectangle_le : volume (maassRectangle j) ≤ volume ModularGroup.fd := by
  refine (measure_mono (rectangle_subset_smul_fdo j)).trans ?_
  rw [measure_smul, measure_congr ModularGroup.fd_ae_eq_fdo]

lemma volume_rectangle_lt_top : volume (maassRectangle j) < ⊤ :=
  (volume_rectangle_le j).trans_lt ModularGroup.volume_fd_lt_top

lemma integrableOn_norm_sq_rectangle (hg : g ∈ maassCuspidalSpace N χ) :
    IntegrableOn (fun w ↦ ‖g (σ • w)‖ ^ 2) (maassRectangle j) :=
  (integrableOn_norm_sq_comp_sl_smul σ _ hg).mono_set (rectangle_subset_smul_fdo j)

lemma setIntegral_norm_sq_rectangle_le (hg : g ∈ maassCuspidalSpace N χ) :
    ∫ w in maassRectangle j, ‖g (σ • w)‖ ^ 2 ≤ ∫ u in gammaZeroDomain N, ‖g u‖ ^ 2 :=
  (setIntegral_mono_set (integrableOn_norm_sq_comp_sl_smul σ _ hg)
    (.of_forall fun u ↦ by positivity) (rectangle_subset_smul_fdo j).eventuallyLE).trans
      (setIntegral_norm_sq_comp_smul_le σ _ hg)

lemma integrableOn_norm_rectangle (hg : g ∈ maassCuspidalSpace N χ) :
    IntegrableOn (fun w ↦ ‖g (σ • w)‖) (maassRectangle j) := by
  have hc : Continuous fun w ↦ g (σ • w) := hg.1.comp (continuous_sl_smul σ)
  have hfin : IsFiniteMeasure (volume.restrict (maassRectangle j)) :=
    ⟨by simpa using volume_rectangle_lt_top j⟩
  exact (((memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    (integrableOn_norm_sq_rectangle σ j hg)).integrable one_le_two).norm

lemma sq_setIntegral_norm_rectangle_le (hg : g ∈ maassCuspidalSpace N χ) :
    (∫ w in maassRectangle j, ‖g (σ • w)‖) ^ 2 ≤
      volume.real ModularGroup.fd * ∫ u in gammaZeroDomain N, ‖g u‖ ^ 2 := by
  refine (sq_setIntegral_le_measureReal_mul_setIntegral_sq _ _
    (volume_rectangle_lt_top j).ne (integrableOn_norm_rectangle σ j hg)
    (integrableOn_norm_sq_rectangle σ j hg)).trans ?_
  exact mul_le_mul (ENNReal.toReal_mono ModularGroup.volume_fd_lt_top.ne (volume_rectangle_le j))
    (setIntegral_norm_sq_rectangle_le σ j hg) (integral_nonneg fun u ↦ by positivity)
    ENNReal.toReal_nonneg

/-- **The average of a cuspidal function high in the cusp**: for `g` cuspidal on `Γ₀(N)`, `N ≠ 0`,
`σ ∈ SL(2, ℤ)`, `φ` of class `C¹` vanishing on `[3, ∞)` with `|φ'| ≤ A` on `[1, ∞)`, and
`Im z ≥ 6`, `|∫_ℍ φ(cosh d(z, w)) g(σ w) dμ(w)|² ≤ (12 A N)² vol(𝒟) ‖g‖²`. -/
lemma sq_norm_integral_kernel_mul_comp_smul_le (hN : 0 < N) (hφ : ContDiff ℝ 1 φ)
    (hA : ∀ c, 1 ≤ c → |deriv φ c| ≤ A) (hφ0 : ∀ c, 3 ≤ c → φ c = 0)
    (hg : g ∈ maassCuspidalSpace N χ) (hz : 6 ≤ z.im) :
    ‖∫ w : ℍ, (φ (Real.cosh (dist z w)) : ℂ) * g (σ • w)‖ ^ 2 ≤
      (12 * A * N) ^ 2 * (volume.real ModularGroup.fd * ∫ u in gammaZeroDomain N, ‖g u‖ ^ 2) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 1 le_rfl)
  have hE : 0 ≤ volume.real ModularGroup.fd * ∫ u in gammaZeroDomain N, ‖g u‖ ^ 2 :=
    mul_nonneg ENNReal.toReal_nonneg (integral_nonneg fun u ↦ by positivity)
  have h1 : ‖∫ w : ℍ, (φ (Real.cosh (dist z w)) : ℂ) * g (σ • w)‖ ≤
      12 * A * ∑ j ∈ Finset.range N, ∫ w in maassRectangle j, ‖g (σ • w)‖ :=
    norm_integral_kernel_mul_le hN hφ hA hφ0 (hg.1.comp (continuous_sl_smul σ))
      (fun t _ hv ↦ maassCuspidal_period σ hg.2.1 t hv) (fun v hv ↦ hg.2.2.2 σ v hv)
      (fun j ↦ integrableOn_norm_rectangle σ j hg) hz
  have h2 (j : ℕ) : ∫ w in maassRectangle j, ‖g (σ • w)‖ ≤
      √(volume.real ModularGroup.fd * ∫ u in gammaZeroDomain N, ‖g u‖ ^ 2) :=
    Real.le_sqrt_of_sq_le (sq_setIntegral_norm_rectangle_le σ j hg)
  have h3 : ∑ j ∈ Finset.range N, ∫ w in maassRectangle j, ‖g (σ • w)‖ ≤
      N * √(volume.real ModularGroup.fd * ∫ u in gammaZeroDomain N, ‖g u‖ ^ 2) := by
    refine (Finset.sum_le_card_nsmul _ _ _ fun j _ ↦ h2 j).trans (le_of_eq ?_)
    simp
  have h4 : ‖∫ w : ℍ, (φ (Real.cosh (dist z w)) : ℂ) * g (σ • w)‖ ≤ 12 * A * N *
      √(volume.real ModularGroup.fd * ∫ u in gammaZeroDomain N, ‖g u‖ ^ 2) := by
    refine h1.trans ?_
    rw [mul_assoc (12 * A)]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : ‖∫ w : ℍ, (φ (Real.cosh (dist z w)) : ℂ) * g (σ • w)‖ ^ 2 ≤ (12 * A * N *
      √(volume.real ModularGroup.fd * ∫ u in gammaZeroDomain N, ‖g u‖ ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h4 2
  rwa [mul_pow, Real.sq_sqrt hE] at h5

lemma finite_setOf_sl_smul_inter_nonempty (hK : IsCompact K) :
    {γ : SL(2, ℤ) | ((γ • ·) '' K ∩ K).Nonempty}.Finite := by
  have h : {g : 𝒮ℒ | ((g • ·) '' K ∩ K).Nonempty}.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image hK hK
  have hι : Injective fun γ : SL(2, ℤ) ↦ (⟨SpecialLinearGroup.mapGL ℝ γ, γ, rfl⟩ : 𝒮ℒ) :=
    fun _ _ hab ↦ SpecialLinearGroup.mapGL_injective (congrArg Subtype.val hab)
  exact h.preimage hι.injOn

/-- **A compact set is covered finitely often by a fundamental domain**: for a compact set `K` of
`ℍ` there is a number `M` such that `∫_K f dμ ≤ M ∫_{Γ₀(N) \ ℍ} f dμ` for every measurable function
`f ≥ 0` invariant under `Γ₀(N)`, the group `SL(2, ℤ)` acting properly discontinuously on `ℍ`. -/
lemma exists_lintegral_le_mul_of_isCompact (hK : IsCompact K) : ∃ M : ℕ, ∀ f : ℍ → ENNReal,
    Measurable f → (∀ γ ∈ Gamma0 N, ∀ τ : ℍ, f (γ • τ) = f τ) → ∫⁻ x in K, f x ≤
      M * ∫⁻ x in gammaZeroDomain N, f x := by
  let G : Subgroup PSL(2, ℤ) := (Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))
  have hD : IsFundamentalDomain G (gammaZeroDomain N) volume :=
    isFundamentalDomain_gammaZeroDomain N
  have hsmul (g : G) {γ : SL(2, ℤ)} (hγ : QuotientGroup.mk' (Subgroup.center SL(2, ℤ)) γ = g)
      (x : ℍ) : g • x = γ • x := by
    rw [Subgroup.smul_def, ← hγ, QuotientGroup.mk'_apply, pslMk_smul]
  have hfin : {g : G | ((g • ·) '' K ∩ K).Nonempty}.Finite := by
    refine (((finite_setOf_sl_smul_inter_nonempty hK).image
      (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).preimage
      Subtype.val_injective.injOn).subset fun g hg ↦ ?_
    rcases g.2 with ⟨γ, -, hγ⟩
    rcases hg with ⟨_, ⟨x, hx, rfl⟩, hgx⟩
    exact ⟨γ, ⟨γ • x, ⟨x, hx, rfl⟩, by rwa [← hsmul g hγ x]⟩, hγ⟩
  have hK0 : MeasurableSet K := hK.isClosed.measurableSet
  have hcount (x : ℍ) :
      ∑' g : G, K.indicator (fun _ ↦ (1 : ENNReal)) (g • x) ≤ hfin.toFinset.card := by
    by_cases hx : ∃ g₀ : G, g₀ • x ∈ K
    · rcases hx with ⟨g₀, hg₀⟩
      rw [← (Equiv.mulRight g₀).tsum_eq, tsum_eq_sum (s := hfin.toFinset) fun g hg ↦ ?_]
      · refine (Finset.sum_le_card_nsmul _ _ 1 fun g _ ↦ ?_).trans (by simp)
        exact indicator_le_self' (fun _ _ ↦ zero_le_one) _ |>.trans (by simp)
      · refine indicator_of_notMem (fun hmem ↦ hg ?_) _
        rw [Finite.mem_toFinset]
        refine ⟨(g * g₀) • x, ⟨g₀ • x, hg₀, ?_⟩, hmem⟩
        simp [mul_smul]
    · have h0 (g : G) : K.indicator (fun _ ↦ (1 : ENNReal)) (g • x) = 0 :=
        indicator_of_notMem (fun hg ↦ hx ⟨g, hg⟩) _
      simp [h0]
  refine ⟨hfin.toFinset.card, fun f hf hinv ↦ ?_⟩
  have hinv' (g : G) (x : ℍ) : f (g • x) = f x := by
    rcases g.2 with ⟨γ, hγ, hg⟩
    rw [hsmul g hg, hinv γ hγ]
  have hterm (g : G) (x : ℍ) :
      K.indicator f (g • x) = K.indicator (fun _ ↦ (1 : ENNReal)) (g • x) * f x := by
    by_cases hx : g • x ∈ K
    · rw [indicator_of_mem hx, indicator_of_mem hx, one_mul, hinv']
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
  have hm (g : G) : Measurable fun x : ℍ ↦ K.indicator (fun _ ↦ (1 : ENNReal)) (g • x) :=
    (measurable_const.indicator hK0).comp (measurable_const_smul g)
  have hm2 (g : G) : AEMeasurable (fun x : ℍ ↦ K.indicator (fun _ ↦ (1 : ENNReal)) (g • x) * f x)
      (volume.restrict (gammaZeroDomain N)) := ((hm g).mul hf).aemeasurable
  rw [← lintegral_indicator hK0, hD.lintegral_eq_tsum'']
  simp only [hterm]
  rw [← lintegral_tsum hm2, ← lintegral_const_mul _ hf]
  refine lintegral_mono fun x ↦ ?_
  dsimp only
  rw [ENNReal.tsum_mul_right]
  exact mul_le_mul_left (hcount x) _

lemma exists_setIntegral_norm_sq_le_of_isCompact (hK : IsCompact K) : ∃ M : ℕ,
    ∀ g ∈ maassCuspidalSpace N χ, ∫ x in K, ‖g x‖ ^ 2 ≤
      M * ∫ x in gammaZeroDomain N, ‖g x‖ ^ 2 := by
  rcases exists_lintegral_le_mul_of_isCompact (N := N) hK with ⟨M, hM⟩
  refine ⟨M, fun g hg ↦ ?_⟩
  have hc : Continuous fun x ↦ ‖g x‖ ^ 2 := hg.1.norm.pow 2
  have h1 : ∫⁻ x in K, ENNReal.ofReal (‖g x‖ ^ 2) ≤
      M * ∫⁻ x in gammaZeroDomain N, ENNReal.ofReal (‖g x‖ ^ 2) :=
    hM _ (ENNReal.measurable_ofReal.comp hc.measurable) fun γ hγ τ ↦ by
      rw [norm_smul_eq_of_mem_maassCuspidalSpace hg hγ]
  rw [← ofReal_integral_eq_lintegral_ofReal (hc.continuousOn.integrableOn_compact hK)
    (.of_forall fun x ↦ by positivity), ← ofReal_integral_eq_lintegral_ofReal hg.2.2.1
    (.of_forall fun x ↦ by positivity), ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul
    (Nat.cast_nonneg M)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg M)
    (integral_nonneg fun x ↦ by positivity))).mp h1

lemma sq_norm_integral_kernel_mul_le_of_subset {B : ℝ} (hK : IsCompact K)
    (hB : ∀ c, 1 ≤ c → |φ c| ≤ B) (hg : Continuous g)
    (hsupp : ∀ w, φ (Real.cosh (dist z w)) ≠ 0 → w ∈ K) :
    ‖∫ w : ℍ, (φ (Real.cosh (dist z w)) : ℂ) * g w‖ ^ 2 ≤
      B ^ 2 * (volume.real K * ∫ w in K, ‖g w‖ ^ 2) := by
  have h1 : ∫ w : ℍ, (φ (Real.cosh (dist z w)) : ℂ) * g w =
      ∫ w in K, (φ (Real.cosh (dist z w)) : ℂ) * g w := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw ↦ ?_).symm
    have h0 : φ (Real.cosh (dist z w)) = 0 := by
      by_contra hne
      exact hw (hsupp w hne)
    simp [h0]
  have hgn : IntegrableOn (fun w ↦ ‖g w‖) K := hg.norm.continuousOn.integrableOn_compact hK
  have hgs : IntegrableOn (fun w ↦ ‖g w‖ ^ 2) K :=
    (hg.norm.pow 2).continuousOn.integrableOn_compact hK
  have h2 : ‖∫ w in K, (φ (Real.cosh (dist z w)) : ℂ) * g w‖ ≤ ∫ w in K, B * ‖g w‖ := by
    refine norm_integral_le_of_norm_le (hgn.const_mul B) (.of_forall fun w ↦ ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB _ (Real.one_le_cosh _)) (norm_nonneg _)
  rw [integral_const_mul] at h2
  have h3 : (∫ w in K, ‖g w‖) ^ 2 ≤ volume.real K * ∫ w in K, ‖g w‖ ^ 2 :=
    sq_setIntegral_le_measureReal_mul_setIntegral_sq _ K hK.measure_lt_top.ne hgn hgs
  have h4 : ‖∫ w in K, (φ (Real.cosh (dist z w)) : ℂ) * g w‖ ^ 2 ≤ (B * ∫ w in K, ‖g w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow] at h4
  rw [h1]
  exact h4.trans (mul_le_mul_of_nonneg_left h3 (by positivity))

lemma dist_sl_smul (a b : ℍ) : dist (σ • a) (σ • b) = dist a b :=
  dist_smul (SpecialLinearGroup.map (Int.castRingHom ℝ) σ) a b

lemma dist_le_of_mem_fdo_of_im_le (hz : z ∈ ModularGroup.fdo) (hy : z.im ≤ 6) : dist I z ≤ 94 := by
  have h1 : 1 < Complex.normSq z := hz.1
  have h2 : |z.re| < 1 / 2 := hz.2
  rw [Complex.normSq_apply, coe_re, coe_im] at h1
  have hx2 : z.re * z.re < 1 / 4 := by
    nlinarith [(abs_lt.mp h2).1, (abs_lt.mp h2).2]
  have hy0 : 0 < z.im := z.im_pos
  have hy1 : 1 / 2 < z.im := by
    by_contra hn
    nlinarith [not_lt.mp hn]
  have h4 : dist I z / 2 ≤ Real.cosh (dist I z) := half_le_cosh (dist I z)
  rw [cosh_dist_eq_coshDist, coshDist] at h4
  simp only [I_re, I_im, coe_re, coe_im] at h4
  have h5 : ((z.re - 0) ^ 2 + z.im ^ 2 + 1 ^ 2) / (2 * 1 * z.im) ≤ 38 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **The average of a cuspidal function over a ball is bounded by its norm**: for `N ≠ 0` and `φ`
of class `C¹` vanishing on `[3, ∞)`, there is a constant `C` such that
`|∫_ℍ φ(cosh d(z, w)) g(w) dμ(w)|² ≤ C ‖g‖²` for every cuspidal function `g` on `Γ₀(N) \ ℍ` and
every `z` in the fundamental domain `gammaZeroDomain N`. If `z = σ z'` with `z' ∈ 𝒟ᵒ`, then when
`Im z' ≥ 6` this comes from the vanishing of the constant term of `g ∘ σ`
(`sq_norm_integral_kernel_mul_comp_smul_le`), and when `Im z' < 6` from the finiteness of the
covering of a compact set by the translates of a fundamental domain
(`exists_lintegral_le_mul_of_isCompact`). -/
lemma exists_sq_norm_integral_kernel_mul_le [NeZero N] (hφ : ContDiff ℝ 1 φ)
    (hφ0 : ∀ c, 3 ≤ c → φ c = 0) : ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ maassCuspidalSpace N χ,
      ∀ z ∈ gammaZeroDomain N, ‖∫ w : ℍ, (φ (Real.cosh (dist z w)) : ℂ) * g w‖ ^ 2 ≤
        C * ∫ u in gammaZeroDomain N, ‖g u‖ ^ 2 := by
  have hN : 0 < N := NeZero.pos N
  rcases (isCompact_Icc (a := (1 : ℝ)) (b := 3)).exists_bound_of_continuousOn
    (hφ.continuous_deriv le_rfl).continuousOn with ⟨A, hA1⟩
  rcases (isCompact_Icc (a := (1 : ℝ)) (b := 3)).exists_bound_of_continuousOn
    hφ.continuous.continuousOn with ⟨B, hB1⟩
  have h13 : (1 : ℝ) ∈ Icc (1 : ℝ) 3 := ⟨le_rfl, by norm_num⟩
  have hA : ∀ c, 1 ≤ c → |deriv φ c| ≤ A := fun c hc ↦ by
    rcases le_or_gt c 3 with h | h
    · exact hA1 c ⟨hc, h⟩
    · have h0 : φ =ᶠ[𝓝 c] fun _ ↦ 0 := by
        filter_upwards [Ioi_mem_nhds h] with e he
        exact hφ0 e (le_of_lt he)
      rw [h0.deriv_eq, deriv_const, abs_zero]
      exact (norm_nonneg _).trans (hA1 1 h13)
  have hB : ∀ c, 1 ≤ c → |φ c| ≤ B := fun c hc ↦ by
    rcases le_or_gt c 3 with h | h
    · exact hB1 c ⟨hc, h⟩
    · rw [hφ0 c h.le, abs_zero]
      exact (norm_nonneg _).trans (hB1 1 h13)
  let K : Set ℍ := ⋃ q : SL(2, ℤ) ⧸ (Gamma0 N).withCenter,
    Metric.closedBall ((q.out : SL(2, ℤ))⁻¹ • I) 100
  have hK : IsCompact K := isCompact_iUnion fun q ↦ isCompact_closedBall _ _
  rcases exists_setIntegral_norm_sq_le_of_isCompact (N := N) (χ := χ) hK with ⟨M, hM⟩
  refine ⟨max ((12 * A * N) ^ 2 * volume.real ModularGroup.fd) (B ^ 2 * (volume.real K * M)),
    le_max_of_le_left (mul_nonneg (by positivity) ENNReal.toReal_nonneg), fun g hg z hz ↦ ?_⟩
  have hE : 0 ≤ ∫ u in gammaZeroDomain N, ‖g u‖ ^ 2 := integral_nonneg fun u ↦ by positivity
  rcases mem_iUnion.mp hz with ⟨q, hq⟩
  rcases mem_smul_set.mp hq with ⟨z', hz', rfl⟩
  rcases le_or_gt 6 z'.im with hy | hy
  · have h : ∫ w : ℍ, (φ (Real.cosh (dist ((q.out : SL(2, ℤ))⁻¹ • z') w)) : ℂ) * g w =
        ∫ w : ℍ, (φ (Real.cosh (dist z' w)) : ℂ) * g ((q.out : SL(2, ℤ))⁻¹ • w) := by
      rw [← (measurePreserving_smul (q.out : SL(2, ℤ))⁻¹ volume).integral_comp
        (measurableEmbedding_const_smul _)]
      simp only [dist_sl_smul]
    rw [h]
    refine (sq_norm_integral_kernel_mul_comp_smul_le _ hN hφ hA hφ0 hg hy).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hE
  · have hsupp (w : ℍ) (hw : φ (Real.cosh (dist ((q.out : SL(2, ℤ))⁻¹ • z') w)) ≠ 0) : w ∈ K := by
      have h1 : Real.cosh (dist ((q.out : SL(2, ℤ))⁻¹ • z') w) < 3 :=
        not_le.mp fun h ↦ hw (hφ0 _ h)
      have h2 :
          dist ((q.out : SL(2, ℤ))⁻¹ • z') w / 2 ≤ Real.cosh (dist ((q.out : SL(2, ℤ))⁻¹ • z') w) :=
        half_le_cosh _
      have h3 : dist ((q.out : SL(2, ℤ))⁻¹ • I) ((q.out : SL(2, ℤ))⁻¹ • z') ≤ 94 := by
        rw [dist_sl_smul]
        exact dist_le_of_mem_fdo_of_im_le hz' hy.le
      refine mem_iUnion.mpr ⟨q, Metric.mem_closedBall.mpr ?_⟩
      have h4 : dist w ((q.out : SL(2, ℤ))⁻¹ • I) ≤ dist w ((q.out : SL(2, ℤ))⁻¹ • z') +
          dist ((q.out : SL(2, ℤ))⁻¹ • z') ((q.out : SL(2, ℤ))⁻¹ • I) := dist_triangle _ _ _
      have h5 : dist w ((q.out : SL(2, ℤ))⁻¹ • z') = dist ((q.out : SL(2, ℤ))⁻¹ • z') w :=
        dist_comm _ _
      have h6 : dist ((q.out : SL(2, ℤ))⁻¹ • z') ((q.out : SL(2, ℤ))⁻¹ • I) =
          dist ((q.out : SL(2, ℤ))⁻¹ • I) ((q.out : SL(2, ℤ))⁻¹ • z') := dist_comm _ _
      linarith
    refine (sq_norm_integral_kernel_mul_le_of_subset hK hB hg.1 hsupp).trans ?_
    have h5 : volume.real K * ∫ w in K, ‖g w‖ ^ 2 ≤
        volume.real K * (M * ∫ u in gammaZeroDomain N, ‖g u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hM g hg) ENNReal.toReal_nonneg
    refine (mul_le_mul_of_nonneg_left h5 (by positivity)).trans ?_
    rw [← mul_assoc, ← mul_assoc, mul_assoc (B ^ 2)]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hE

end UpperHalfPlane
