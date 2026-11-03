import LeanBridge.ForMathlib.Analysis.Complex.UpperHalfPlane.StripIntegral

/-!
# The Rankin–Selberg integral in coordinates

The Rankin–Selberg integral of a function `h` on the upper half plane is the integral of
`h(τ) (Im τ) ^ σ` over the strip `0 ≤ Re τ < 1`, against the invariant measure `dx dy / y ^ 2`. This
file writes it in the coordinates `τ = x + i y`, and shows that for `1 < σ ≤ 2` the integrand is
integrable as soon as `h` and `h(τ) (Im τ) ^ 2` are bounded.

## Main definitions

* `RankinSelberg.coordPoint`: the point `x + i y` of the upper half plane.
* `RankinSelberg.strip`: the strip `0 ≤ Re τ < 1`.
* `RankinSelberg.stripFun`: the function `1_{strip}(τ) h(τ) (Im τ) ^ σ`.

## Main results

* `RankinSelberg.integrable_stripFun`: the strip function is integrable.
* `RankinSelberg.integral_stripFun_eq`: the Rankin–Selberg integral as an iterated integral.
-/

open MeasureTheory UpperHalfPlane Set

namespace RankinSelberg

variable {p : ℝ × ℝ} {h : ℍ → ℂ} {σ : ℝ}

variable (p) in
/-- The point `x + i y` of the upper half plane, for `p = (x, y)` with `y > 0`. -/
noncomputable def coordPoint : ℍ :=
  ofComplex (p.1 + p.2 * Complex.I)

lemma coordPoint_im (hp : 0 < p.2) : (coordPoint p).im = p.2 := by
  rw [coordPoint, ofComplex_apply_of_im_pos (by simpa using hp)]
  simp

/-- The strip `0 ≤ Re τ < 1` of the upper half plane, a fundamental domain for the translations
`τ ↦ τ + n`. -/
def strip : Set ℍ :=
  {τ | τ.re ∈ Ico (0 : ℝ) 1}

lemma measurableSet_strip : MeasurableSet strip :=
  measurableSet_re_mem_Ico 1

variable (h σ) in
/-- The function `1_{strip}(τ) h(τ) (Im τ) ^ σ`, whose integral against the invariant measure is
the Rankin–Selberg integral of `h`. -/
noncomputable def stripFun : ℍ → ℂ :=
  strip.indicator fun τ ↦ h τ * ((τ.im ^ σ : ℝ) : ℂ)

private lemma stripFun_coordPoint_eqOn : EqOn
    (fun p : ℝ × ℝ ↦ (p.2 ^ 2)⁻¹ • (h (coordPoint p) * (((coordPoint p).im ^ σ : ℝ) : ℂ)))
    (fun p : ℝ × ℝ ↦ (p.2 ^ 2)⁻¹ • (h (coordPoint p) * ((p.2 ^ σ : ℝ) : ℂ)))
    (Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := fun p hp ↦ by
  simp only [coordPoint_im hp.2]

private lemma integrable_stripFun_iff : Integrable (stripFun h σ) ↔ IntegrableOn
    (fun p : ℝ × ℝ ↦ (p.2 ^ 2)⁻¹ • (h (coordPoint p) * ((p.2 ^ σ : ℝ) : ℂ)))
    (Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := by
  rw [stripFun, integrable_indicator_iff measurableSet_strip, strip, integrableOn_re_mem_Ico_iff]
  exact integrableOn_congr_fun stripFun_coordPoint_eqOn (measurableSet_Ico.prod measurableSet_Ioi)

lemma integrableOn_rpow_ite (hσ : σ ∈ Ioc (1 : ℝ) 2) :
    IntegrableOn (fun y : ℝ ↦ if y ≤ 1 then y ^ (σ - 2) else y ^ (-2 : ℝ)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun y : ℝ ↦ y ^ (σ - 2)) (Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith [hσ.1])).1
    exact h1.congr_fun (fun y hy ↦ (ite_eq_left hy.2).symm) measurableSet_Ioc
  · have h1 : IntegrableOn (fun y : ℝ ↦ y ^ (-2 : ℝ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
    exact h1.congr_fun (fun y hy ↦ (ite_eq_right (not_le.mpr hy)).symm) measurableSet_Ioi

private lemma aemeasurable_coordPoint :
    AEMeasurable coordPoint (volume.restrict (Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ))) := by
  have hcont : Continuous fun p : ℝ × ℝ ↦ (p.1 + p.2 * Complex.I : ℂ) := by fun_prop
  refine (ofComplex.continuousOn.comp hcont.continuousOn fun p hp ↦ ?_).aemeasurable
    (measurableSet_Ico.prod measurableSet_Ioi)
  simpa [ofComplex] using hp.2

/-- **The strip function is integrable**, for `1 < σ ≤ 2`, if `h` is continuous and both `h` and
`h(τ) (Im τ) ^ 2` are bounded. -/
lemma integrable_stripFun {C : ℝ} (hh : Continuous h) (hC : ∀ τ, ‖h τ‖ ≤ C)
    (hC' : ∀ τ, ‖h τ‖ * τ.im ^ 2 ≤ C) (hσ : σ ∈ Ioc (1 : ℝ) 2) : Integrable (stripFun h σ) := by
  have hmajor : IntegrableOn (fun p : ℝ × ℝ ↦ C * if p.2 ≤ 1 then p.2 ^ (σ - 2) else p.2 ^ (-2 : ℝ))
      (Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact ((integrableOn_rpow_ite hσ).const_mul C).comp_snd _
  refine integrable_stripFun_iff.mpr <| hmajor.mono' ?_ <|
    ae_restrict_of_forall_mem (measurableSet_Ico.prod measurableSet_Ioi) fun p hp ↦ ?_
  · have h1 : Measurable fun p : ℝ × ℝ ↦ (p.2 ^ 2)⁻¹ := by fun_prop
    have h2 : AEMeasurable (fun p : ℝ × ℝ ↦ h (coordPoint p))
        (volume.restrict (Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ))) :=
      hh.measurable.comp_aemeasurable aemeasurable_coordPoint
    have h3 : Measurable fun p : ℝ × ℝ ↦ ((p.2 ^ σ : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp <| measurable_snd.pow_const σ
    exact (h1.aemeasurable.smul <| h2.mul h3.aemeasurable).aestronglyMeasurable
  · have hy : 0 < p.2 := hp.2
    have hA : 0 < (p.2 ^ 2)⁻¹ := by positivity
    have hB : 0 < p.2 ^ σ := Real.rpow_pos_of_pos hy σ
    rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hA.le,
      Real.norm_of_nonneg hB.le]
    split_ifs with hy1
    · have heq : p.2 ^ (σ - 2) = p.2 ^ σ * (p.2 ^ 2)⁻¹ := by
        rw [Real.rpow_sub hy, Real.rpow_two, div_eq_mul_inv]
      have h1 : ‖h (coordPoint p)‖ * (p.2 ^ σ * (p.2 ^ 2)⁻¹) ≤ C * (p.2 ^ σ * (p.2 ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_right (hC (coordPoint p)) (mul_pos hB hA).le
      rw [heq]
      nlinarith
    · have heq : p.2 ^ (-2 : ℝ) = (p.2 ^ 2)⁻¹ := by
        rw [Real.rpow_neg hy.le, Real.rpow_two]
      have hpow : p.2 ^ σ ≤ p.2 ^ 2 := by
        rw [← Real.rpow_two]
        exact Real.rpow_le_rpow_of_exponent_le (not_le.mp hy1).le hσ.2
      have hH : ‖h (coordPoint p)‖ * p.2 ^ 2 ≤ C := coordPoint_im hy ▸ hC' (coordPoint p)
      have h4 : ‖h (coordPoint p)‖ * p.2 ^ σ ≤ C :=
        (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans hH
      rw [heq]
      nlinarith

private lemma integrable_prod_of_integrable_stripFun (hint : Integrable (stripFun h σ)) : Integrable
    (fun p : ℝ × ℝ ↦ (p.2 ^ 2)⁻¹ • (h (coordPoint p) * ((p.2 ^ σ : ℝ) : ℂ)))
    ((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact integrable_stripFun_iff.mp hint

lemma integrableOn_integral_stripFun (hint : Integrable (stripFun h σ)) : IntegrableOn
    (fun y : ℝ ↦ ∫ x in Ico (0 : ℝ) 1, (y ^ 2)⁻¹ • (h (coordPoint (x, y)) * ((y ^ σ : ℝ) : ℂ)))
    (Ioi 0) :=
  (integrable_prod_of_integrable_stripFun hint).integral_prod_right

/-- **The Rankin–Selberg integral in coordinates.** -/
lemma integral_stripFun_eq (hint : Integrable (stripFun h σ)) : ∫ τ, stripFun h σ τ =
    ∫ y in Ioi (0 : ℝ), ∫ x in Ico (0 : ℝ) 1, (y ^ 2)⁻¹ •
      (h (coordPoint (x, y)) * ((y ^ σ : ℝ) : ℂ)) := by
  rw [stripFun, integral_indicator measurableSet_strip, strip, setIntegral_re_mem_Ico]
  refine (setIntegral_congr_fun (measurableSet_Ico.prod measurableSet_Ioi)
    stripFun_coordPoint_eqOn).trans ?_
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_prod_symm _ (integrable_prod_of_integrable_stripFun hint)]

end RankinSelberg
