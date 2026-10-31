import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.NumberTheory.ModularForms.Petersson

/-!
# Petersson integrals over a vertical strip

The invariant measure `dx dy / y²` on `ℍ` restricted to the vertical strip `S_w = {0 ≤ Re z < w}`
is the Lebesgue measure on `[0, w) × (0, ∞)` with density `y⁻²`. For a function
`F(z) = Σ_{m ≥ 0} a_m e^{2πi m z / w}` on `ℍ`, the expansion converges absolutely (it converges at
height `y / 2`), the integral over `[0, w)` of `conj(e^{2πi n z / w}) F(z)` at height `y` picks out
`w a_n e^{-4π n y / w}`, and the Petersson integral over the strip is
`∫_{S_w} conj(e^{2πi n z / w}) F(z) y^k dμ = w (w / 4πn)^{k-1} Γ(k - 1) a_n` for `n ≥ 1`, `k ≥ 2`.
This is the last step of the unfolding of the Petersson product of a Poincaré series against a cusp
form (LMFDB `specialfunction.poincare`).

## Main results

* `UpperHalfPlane.setIntegral_re_mem_Ico`, `UpperHalfPlane.integrableOn_re_mem_Ico_iff`: the
  integral over the strip in coordinates.
* `UpperHalfPlane.integral_conj_exp_mul_eq`: the Fourier coefficient at height `y`.
* `UpperHalfPlane.setIntegral_petersson_exp_eq`: the Petersson integral over the strip.
-/

open Complex MeasureTheory Set

open scoped NNReal ComplexConjugate

namespace UpperHalfPlane

variable (w n : ℕ) (a : ℕ → ℂ) (k : ℤ) (b y : ℝ) (g : ℍ → ℂ) {F : ℍ → ℂ}

lemma image_coe_re_mem_Ico : ((↑) : ℍ → ℂ) '' {z : ℍ | z.re ∈ Ico 0 b} =
    measurableEquivRealProd ⁻¹' (Ico 0 b ×ˢ Ioi 0) := by
  ext c
  refine ⟨?_, fun hc ↦ ⟨⟨c, hc.2⟩, hc.1, rfl⟩⟩
  rintro ⟨z, hz, rfl⟩
  exact ⟨hz, z.im_pos⟩

lemma measurable_volume_density :
    Measurable fun z : ℍ ↦ ((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) := by
  refine measurable_coe_nnreal_real_iff.mp ?_
  simp only [NNReal.coe_pow]
  exact (measurable_const.div continuous_im.measurable).pow_const 2

lemma measurableSet_re_mem_Ico : MeasurableSet {z : ℍ | z.re ∈ Ico 0 b} :=
  measurableSet_Ico.preimage continuous_re.measurable

/-- **The integral over a vertical strip in coordinates**: the integral over
`{z ∈ ℍ | 0 ≤ Re z < b}` for the invariant measure is the Lebesgue integral over
`[0, b) × (0, ∞)` of `y⁻² g(x + iy)`. -/
lemma setIntegral_re_mem_Ico : ∫ z in {z : ℍ | z.re ∈ Ico 0 b}, g z =
    ∫ p in Ico 0 b ×ˢ Ioi 0, ((p.2 ^ 2)⁻¹ : ℝ) • g (ofComplex (p.1 + p.2 * Complex.I)) := by
  rw [volume_def, setIntegral_withDensity_eq_setIntegral_smul measurable_volume_density _
    (measurableSet_re_mem_Ico b)]
  have h1 : ∫ z in {z : ℍ | z.re ∈ Ico 0 b}, ((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) • g z
      ∂(Measure.comap UpperHalfPlane.coe volume) =
        ∫ z in UpperHalfPlane.coe ⁻¹' (UpperHalfPlane.coe '' {z : ℍ | z.re ∈ Ico 0 b}),
          ((((z : ℂ).im ^ 2)⁻¹ : ℝ) • g (ofComplex (z : ℂ)))
            ∂(Measure.comap UpperHalfPlane.coe volume) := by
    rw [preimage_image_eq _ measurableEmbedding_coe.injective]
    refine setIntegral_congr_fun (measurableSet_re_mem_Ico b) fun z _ ↦ ?_
    rw [ofComplex_apply, NNReal.smul_def]
    simp
  refine h1.trans <| (measurableEmbedding_coe.setIntegral_map
    (fun c : ℂ ↦ (((c.im ^ 2)⁻¹ : ℝ) • g (ofComplex c))) _).symm.trans ?_
  rw [measurableEmbedding_coe.map_comap,
    Measure.restrict_restrict_of_subset (image_subset_range _ _), image_coe_re_mem_Ico]
  refine Eq.trans ?_ (volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    measurableEquivRealProd.measurableEmbedding _ _)
  refine setIntegral_congr_fun ?_ fun c _ ↦ ?_
  · exact measurableEquivRealProd.measurable (measurableSet_Ico.prod measurableSet_Ioi)
  · simp

variable {g} in
/-- **Integrability over a vertical strip in coordinates**: `g` is integrable on
`{z ∈ ℍ | 0 ≤ Re z < b}` for the invariant measure exactly when `y⁻² g(x + iy)` is Lebesgue
integrable on `[0, b) × (0, ∞)`. -/
lemma integrableOn_re_mem_Ico_iff : IntegrableOn g {z : ℍ | z.re ∈ Ico 0 b} ↔ IntegrableOn
    (fun p : ℝ × ℝ ↦ ((p.2 ^ 2)⁻¹ : ℝ) • g (ofComplex (p.1 + p.2 * Complex.I)))
      (Ico 0 b ×ˢ Ioi 0) := by
  rw [IntegrableOn, volume_def, restrict_withDensity (measurableSet_re_mem_Ico b),
    integrable_withDensity_iff_integrable_smul measurable_volume_density, ← IntegrableOn]
  have h1 : IntegrableOn (fun z : ℍ ↦ ((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) • g z)
      {z : ℍ | z.re ∈ Ico 0 b} (Measure.comap UpperHalfPlane.coe volume) ↔
        IntegrableOn ((fun c : ℂ ↦ (((c.im ^ 2)⁻¹ : ℝ) • g (ofComplex c))) ∘ UpperHalfPlane.coe)
          (UpperHalfPlane.coe ⁻¹' (UpperHalfPlane.coe '' {z : ℍ | z.re ∈ Ico 0 b}))
            (Measure.comap UpperHalfPlane.coe volume) := by
    rw [preimage_image_eq _ measurableEmbedding_coe.injective]
    refine integrableOn_congr_fun (fun z _ ↦ ?_) (measurableSet_re_mem_Ico b)
    simp [NNReal.smul_def]
  rw [h1, ← measurableEmbedding_coe.integrableOn_map_iff, measurableEmbedding_coe.map_comap,
    IntegrableOn, Measure.restrict_restrict_of_subset (image_subset_range _ _), ← IntegrableOn,
    image_coe_re_mem_Ico, ← volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      measurableEquivRealProd.measurableEmbedding]
  refine integrableOn_congr_fun (fun c _ ↦ ?_)
    (measurableEquivRealProd.measurable (measurableSet_Ico.prod measurableSet_Ioi))
  simp

lemma conj_exp_mul_exp (m : ℕ) (x : ℝ) :
    conj (exp (2 * Real.pi * Complex.I * (n / w) * (x + y * Complex.I))) *
      exp (2 * Real.pi * Complex.I * (m / w) * (x + y * Complex.I)) =
        exp (2 * Real.pi * Complex.I * ((m - n : ℤ) / w : ℂ) * x) *
          (Real.exp (-(2 * Real.pi * ((m + n : ℕ) / w) * y)) : ℂ) := by
  rw [← exp_conj, ofReal_exp, ← exp_add, ← exp_add]
  congr 1
  simp [map_ofNat]
  linear_combination (2 * Real.pi * (n + m) / w * y) * I_sq

lemma integral_exp_two_pi_I_mul (hw : 0 < w) (j : ℤ) : ∫ x in (0 : ℝ)..w,
    exp (2 * Real.pi * Complex.I * (j / w : ℂ) * x) = if j = 0 then (w : ℂ) else 0 := by
  have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  split_ifs with hj
  · simp [hj]
  · have hc : 2 * Real.pi * Complex.I * (j / w : ℂ) ≠ 0 := by
      simp [hj, hw']
    rw [integral_exp_mul_complex hc]
    have h1 : exp (2 * Real.pi * Complex.I * (j / w : ℂ) * (w : ℝ)) = 1 := by
      rw [← exp_int_mul_two_pi_mul_I j]
      congr 1
      push_cast
      field_simp
    rw [h1]
    simp

/-- **The Fourier coefficient at height `y`**: if `G(x + iy) = Σ_m a_m e^{2πi m (x + iy) / w}`
for every `x` with `Σ |a_m| e^{-2π m y / w} < ∞`, then
`∫_0^w conj(e^{2πi n (x + iy) / w}) G(x + iy) dx = w e^{-4π n y / w} a_n`. -/
lemma integral_conj_exp_mul_eq (hw : 0 < w) (G : ℂ → ℂ)
    (hG : ∀ x : ℝ, HasSum (fun m : ℕ ↦
      a m * exp (2 * Real.pi * Complex.I * (m / w) * (x + y * Complex.I))) (G (x + y * Complex.I)))
    (hGs : Summable fun m : ℕ ↦ ‖a m‖ * Real.exp (-(2 * Real.pi * (m / w) * y))) :
    ∫ x in (0 : ℝ)..w, conj (exp (2 * Real.pi * Complex.I * (n / w) * (x + y * Complex.I))) *
      G (x + y * Complex.I) = w * Real.exp (-(2 * Real.pi * ((n + n : ℕ) / w) * y)) * a n := by
  have hF (m : ℕ) (x : ℝ) : conj (exp (2 * Real.pi * Complex.I * (n / w) * (x + y * Complex.I))) *
      (a m * exp (2 * Real.pi * Complex.I * (m / w) * (x + y * Complex.I))) =
        a m * Real.exp (-(2 * Real.pi * ((m + n : ℕ) / w) * y)) *
          exp (2 * Real.pi * Complex.I * ((m - n : ℤ) / w : ℂ) * x) := by
    rw [mul_left_comm, conj_exp_mul_exp]
    ring1
  have hexp (m : ℕ) : Real.exp (-(2 * Real.pi * ((m + n : ℕ) / w) * y)) =
      Real.exp (-(2 * Real.pi * (m / w) * y)) * Real.exp (-(2 * Real.pi * (n / w) * y)) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring1
  refine (intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0)
    (b := (w : ℝ)) (F := fun (m : ℕ) (x : ℝ) ↦ conj (exp (2 * Real.pi * Complex.I * (n / w) *
      (x + y * Complex.I))) * (a m * exp (2 * Real.pi * Complex.I * (m / w) * (x + y * Complex.I))))
    (fun m _ ↦ ‖a m‖ * Real.exp (-(2 * Real.pi * ((m + n : ℕ) / w) * y)))
    (fun m ↦ by
      simp_rw [hF]
      exact (continuous_const.mul (by fun_prop)).aestronglyMeasurable)
    (fun m ↦ .of_forall fun x _ ↦ by
      have h1 : ‖exp (2 * Real.pi * Complex.I * ((m - n : ℤ) / w : ℂ) * x)‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      rw [hF, norm_mul, norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, h1,
        mul_one])
    (.of_forall fun x _ ↦ by
      simp_rw [hexp, ← mul_assoc]
      exact hGs.mul_right _)
    intervalIntegrable_const
    (.of_forall fun x _ ↦ (hG x).mul_left _)).unique ?_
  convert hasSum_ite_eq n (w * Real.exp (-(2 * Real.pi * ((n + n : ℕ) / w) * y)) * a n) using 1
  funext m
  simp_rw [hF]
  rw [intervalIntegral.integral_const_mul, integral_exp_two_pi_I_mul w hw]
  rcases eq_or_ne m n with rfl | hmn
  · rw [sub_self, ite_eq_left rfl, ite_eq_left rfl]
    ring1
  · simp [sub_eq_zero, hmn]

lemma summable_norm_mul_exp_of_hasSum (hw : 0 < w)
    (hF : ∀ z : ℍ, HasSum (fun m : ℕ ↦ a m * exp (2 * Real.pi * Complex.I * (m / w) * z)) (F z))
    (hy : 0 < y) : Summable fun m : ℕ ↦ ‖a m‖ * Real.exp (-(2 * Real.pi * (m / w) * y)) := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  let z₀ : ℍ := ⟨((y / 2 : ℝ) : ℂ) * Complex.I, by simpa using half_pos hy⟩
  have hnorm (m : ℕ) : ‖a m * exp (2 * Real.pi * Complex.I * (m / w) * z₀)‖ =
      ‖a m‖ * Real.exp (-(Real.pi * (m / w) * y)) := by
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp [z₀]
    ring1
  have hev : ∀ᶠ m : ℕ in Filter.atTop, ‖a m * exp (2 * Real.pi * Complex.I * (m / w) * z₀)‖ < 1 :=
    (hF z₀).summable.tendsto_atTop_zero.norm.eventually (gt_mem_nhds (by simp))
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun m : ℕ ↦ Real.exp (-(Real.pi / w * y)) ^ m)
    (summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr ?_)) ?_
  · exact neg_neg_of_pos (by positivity)
  · filter_upwards [hev] with m hm
    rw [hnorm] at hm
    have h2 : Real.exp (-(2 * Real.pi * (m / w) * y)) =
        Real.exp (-(Real.pi * (m / w) * y)) * Real.exp (-(Real.pi * (m / w) * y)) := by
      rw [← Real.exp_add]
      congr 1
      ring1
    have h3 : (m : ℝ) * -(Real.pi / w * y) = -(Real.pi * (m / w) * y) := by
      ring1
    rw [Real.norm_of_nonneg (by positivity), ← Real.exp_nat_mul, h2, h3, ← mul_assoc]
    exact mul_le_of_le_one_left (Real.exp_pos _).le hm.le

/-- **The Petersson integral against `e^{2πi n z / w}` over a vertical strip** (LMFDB
`specialfunction.poincare`): if `F(z) = Σ_{m ≥ 0} a_m e^{2πi m z / w}` on `ℍ` (the expansion then
converges absolutely), `n ≥ 1`, `k ≥ 2`, and the integrand is integrable, then
`∫_{0 ≤ Re z < w} conj(e^{2πi n z / w}) F(z) y^k dμ = w (w / 4πn)^{k-1} Γ(k - 1) a_n`. -/
lemma setIntegral_petersson_exp_eq (hw : 0 < w) (hn : 0 < n) (hk : 2 ≤ k)
    (hF : ∀ z : ℍ, HasSum (fun m : ℕ ↦ a m * exp (2 * Real.pi * Complex.I * (m / w) * z)) (F z))
    (hint : IntegrableOn (petersson k (fun z : ℍ ↦ exp (2 * Real.pi * Complex.I * (n / w) * z)) F)
      {z : ℍ | z.re ∈ Ico 0 (w : ℝ)}) :
    ∫ z in {z : ℍ | z.re ∈ Ico 0 (w : ℝ)},
      petersson k (fun z : ℍ ↦ exp (2 * Real.pi * Complex.I * (n / w) * z)) F z =
        (w * (w / (4 * Real.pi * n)) ^ ((k : ℝ) - 1) * Real.Gamma (k - 1) : ℝ) * a n := by
  rw [integrableOn_re_mem_Ico_iff, Measure.volume_eq_prod] at hint
  rw [setIntegral_re_mem_Ico, Measure.volume_eq_prod, ← setIntegral_prod_swap]
  refine (setIntegral_prod _ hint.swap).trans ?_
  have hinner (y : ℝ) (hy : y ∈ Ioi 0) : ∫ x in Ico 0 (w : ℝ), (((y, x).swap.2 ^ 2)⁻¹ : ℝ) •
      petersson k (fun z : ℍ ↦ exp (2 * Real.pi * Complex.I * (n / w) * z)) F
        (ofComplex ((y, x).swap.1 + (y, x).swap.2 * Complex.I)) =
          ((y ^ ((k : ℝ) - 1 - 1) * Real.exp (-(4 * Real.pi * n / w * y)) : ℝ) : ℂ) *
            (w * a n) := by
    have hy0 : 0 < y := hy
    have hc (x : ℝ) : ((ofComplex (x + y * Complex.I) : ℍ) : ℂ) = x + y * Complex.I := by
      rw [ofComplex_apply_of_im_pos (by simpa using hy0)]
    have hi (x : ℝ) : (ofComplex (x + y * Complex.I)).im = y := by
      rw [← UpperHalfPlane.coe_im, hc]
      simp
    have hpt : ∀ x ∈ Ico 0 (w : ℝ), (((y, x).swap.2 ^ 2)⁻¹ : ℝ) •
        petersson k (fun z : ℍ ↦ exp (2 * Real.pi * Complex.I * (n / w) * z)) F
          (ofComplex ((y, x).swap.1 + (y, x).swap.2 * Complex.I)) =
            ((((y ^ 2)⁻¹ : ℝ) : ℂ) * (y : ℂ) ^ k) *
              (conj (exp (2 * Real.pi * Complex.I * (n / w) * (x + y * Complex.I))) *
                F (ofComplex (x + y * Complex.I))) := by
      intro x _
      simp only [Prod.swap_prod_mk, petersson, hc, hi, Complex.real_smul]
      ring1
    rw [setIntegral_congr_fun measurableSet_Ico hpt, integral_const_mul,
      integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (Nat.cast_nonneg w),
      integral_conj_exp_mul_eq w n a y hw (fun c ↦ F (ofComplex c))
        (fun x ↦ by simpa only [hc] using hF (ofComplex (x + y * Complex.I)))
        (summable_norm_mul_exp_of_hasSum w a y hw hF hy0)]
    have h1 : y ^ ((k : ℝ) - 1 - 1) = y ^ (k - 2) := by
      rw [← Real.rpow_intCast]
      congr 1
      push_cast
      ring1
    have h2 : Real.exp (-(2 * Real.pi * ((n + n : ℕ) / w) * y)) =
        Real.exp (-(4 * Real.pi * n / w * y)) := by
      congr 1
      push_cast
      ring1
    rw [h1, h2]
    push_cast
    rw [zpow_sub₀ (by exact_mod_cast hy0.ne'), zpow_two]
    ring1
  refine (setIntegral_congr_fun measurableSet_Ioi hinner).trans ?_
  have hk' : 0 < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hr : 0 < 4 * Real.pi * n / w := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hw' : (0 : ℝ) < w := by exact_mod_cast hw
    positivity
  rw [integral_mul_const, integral_complex_ofReal, Real.integral_rpow_mul_exp_neg_mul_Ioi hk' hr,
    one_div_div]
  push_cast
  ring1

end UpperHalfPlane
