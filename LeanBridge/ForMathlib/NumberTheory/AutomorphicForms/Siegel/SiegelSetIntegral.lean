import LeanBridge.ForMathlib.MeasureTheory.Group.FundamentalDomainCover
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Jacobi.CoefficientGrowth
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SiegelReduction
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrals over the Siegel set

On the Siegel set `Z = X + iY` of `ℋ₂`, `y₀₀, y₁₁ ≥ 4/5` and `det Y ≥ (3/4) y₀₀ y₁₁ ≥ 12/25`, so the
density `det(Y)^{-3}` of the invariant measure is bounded, and `y₀₀ + y₁₁` bounds `|y₀₁|`. So a
function decaying exponentially in `y₀₀ + y₁₁` is integrable on the Siegel set: it is dominated by a
product of integrable functions of the three coordinates `z₀₀`, `z₀₁` and `z₁₁`.

## Main results

* The instance `SigmaFinite (invariantMeasure l)`.
* `SiegelUpperHalfSpace.mul_le_det_im`: `det Y ≥ (3/4) y₀₀ y₁₁` on the Siegel set.
* `SiegelUpperHalfSpace.lintegral_siegelSet_lt_top`: exponential decay is integrable on the Siegel
  set.
* `SiegelUpperHalfSpace.lintegral_siegelSet_mul_pow_lt_top`: so is exponential decay times a
  polynomial.
-/

open Complex Matrix TauCeti MeasureTheory Real Set

open scoped ENNReal

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] [DecidableEq l]

private lemma sigmaFinite_withDensity_coordDensity :
    SigmaFinite ((volume : Measure (Sym2 l → ℂ)).withDensity (coordDensity l)) :=
  SigmaFinite.withDensity_ofReal _

instance : SigmaFinite (invariantMeasure l) := by
  have : SigmaFinite ((volume : Measure (Sym2 l → ℂ)).withDensity (coordDensity l)) :=
    sigmaFinite_withDensity_coordDensity
  let ν : Measure (Sym2 l → ℂ) := (volume : Measure (Sym2 l → ℂ)).withDensity (coordDensity l)
  refine ⟨⟨{ set := fun n ↦ toCoords ⁻¹' spanningSets ν n
             set_mem := fun _ ↦ trivial
             finite := fun n ↦ ?_
             spanning := ?_ }⟩⟩
  · rw [invariantMeasure, measurableEmbedding_toCoords.comap_apply]
    exact (measure_mono (image_preimage_subset _ _)).trans_lt (measure_spanningSets_lt_top ν n)
  · rw [← preimage_iUnion, iUnion_spanningSets, preimage_univ]

variable {Z : SiegelUpperHalfSpace (Fin 2)}

/-! ### Inequalities on the Siegel set -/

lemma four_fifths_le_im_zero_zero (hZ : Z ∈ siegelSet) : 4 / 5 ≤ (Z.val 0 0).im := by
  have h : 8 / 5 ≤ √3 := Real.le_sqrt_of_sq_le (by norm_num)
  linarith [hZ.2.2.2]

lemma four_fifths_le_im_one_one (hZ : Z ∈ siegelSet) : 4 / 5 ≤ (Z.val 1 1).im :=
  (four_fifths_le_im_zero_zero hZ).trans hZ.2.2.1

lemma abs_im_zero_one_le (hZ : Z ∈ siegelSet) : |(Z.val 0 1).im| ≤ (Z.val 0 0).im := by
  have h₁ : 0 ≤ |(Z.val 0 1).im| := abs_nonneg _
  linarith [hZ.2.1]

/-- On the Siegel set, `det Y ≥ (3/4) y₀₀ y₁₁`. -/
lemma mul_le_det_im (hZ : Z ∈ siegelSet) :
    3 / 4 * ((Z.val 0 0).im * (Z.val 1 1).im) ≤ (Z.val.map im).det := by
  have hZs : Z.val 1 0 = Z.val 0 1 := congrFun (congrFun Z.transpose_val 0) 1
  have h₀ : 0 < (Z.val 0 0).im := by
    linarith [four_fifths_le_im_zero_zero hZ]
  have h₁ : (Z.val 0 1).im ^ 2 ≤ ((Z.val 0 0).im / 2) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (by linarith [hZ.2.1]) 2
  rw [det_fin_two]
  simp only [map_apply, hZs]
  nlinarith [hZ.2.2.1, mul_le_mul_of_nonneg_left hZ.2.2.1 h₀.le]

lemma twelve_div_le_det_im (hZ : Z ∈ siegelSet) : 12 / 25 ≤ (Z.val.map im).det := by
  have h₀ : 4 / 5 ≤ (Z.val 0 0).im := four_fifths_le_im_zero_zero hZ
  have h₁ : 4 / 5 ≤ (Z.val 1 1).im := four_fifths_le_im_one_one hZ
  nlinarith [mul_le_det_im hZ, mul_le_mul h₀ h₁ (by norm_num) (by linarith)]

/-! ### Integrals -/

/-- The product of the indicator of `|Re z| ≤ 1/2` and of `e^{-c |Im z|}`. -/
private noncomputable def stripBound (c : ℝ) (z : ℂ) : ℝ :=
  (Icc (-(1 / 2) : ℝ) (1 / 2)).indicator (fun _ ↦ (1 : ℝ)) z.re * rexp (-c * |z.im|)

private lemma integrable_stripBound {c : ℝ} (hc : 0 < c) : Integrable (stripBound c) := by
  have h₁ : Integrable ((Icc (-(1 / 2) : ℝ) (1 / 2)).indicator fun _ ↦ (1 : ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp) (by simp))
  have h₂ : Integrable fun y : ℝ ↦ rexp (-c * |y|) :=
    integrable_comp_abs (f := fun y ↦ rexp (-c * y))
      (exp_neg_integrableOn_Ioi 0 hc)
  exact (Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding).mpr (h₁.mul_prod h₂)

variable {c : ℝ}

lemma toCoords_apply (τ : SiegelUpperHalfSpace (Fin 2)) (i j : Fin 2) :
    τ.toCoords s(i, j) = τ.val i j :=
  congrFun (congrFun (ofSymCoords_toCoords τ) i) j

private lemma coordDensity_toCoords_le (hZ : Z ∈ siegelSet) :
    coordDensity (Fin 2) Z.toCoords ≤ ENNReal.ofReal ((25 / 12) ^ 3) := by
  rw [coordDensity, ofSymCoords_toCoords]
  refine ENNReal.ofReal_le_ofReal ?_
  have h₁ : 12 / 25 ≤ (Z.val.map im).det := twelve_div_le_det_im hZ
  have h₂ : ((12 : ℝ) / 25) ^ 3 ≤ (Z.val.map im).det ^ (Fintype.card (Fin 2) + 1) := by
    simpa using pow_le_pow_left₀ (by norm_num) h₁ 3
  convert inv_anti₀ (by norm_num) h₂ using 1
  norm_num

private lemma rexp_le_prod_stripBound (hc : 0 < c) (hZ : Z ∈ siegelSet) :
    rexp (-c * ((Z.val 0 0).im + (Z.val 1 1).im)) ≤
      ∏ s : Sym2 (Fin 2), stripBound (c / 3) (Z.toCoords s) := by
  have huniv : (Finset.univ : Finset (Sym2 (Fin 2))) = {s(0, 0), s(0, 1), s(1, 1)} := by
    decide
  have hs (i j : Fin 2) :
      stripBound (c / 3) (Z.toCoords s(i, j)) = rexp (-(c / 3) * |(Z.val i j).im|) := by
    rw [stripBound, toCoords_apply,
      indicator_of_mem (show (Z.val i j).re ∈ _ from abs_le.mp (hZ.1 i j)), one_mul]
  rw [huniv, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, hs, hs, hs, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have h₀ : 4 / 5 ≤ (Z.val 0 0).im := four_fifths_le_im_zero_zero hZ
  have h₁ : 4 / 5 ≤ (Z.val 1 1).im := four_fifths_le_im_one_one hZ
  have h₂ : |(Z.val 0 1).im| ≤ (Z.val 0 0).im := abs_im_zero_one_le hZ
  rw [abs_of_nonneg (show 0 ≤ (Z.val 0 0).im by linarith),
    abs_of_nonneg (show 0 ≤ (Z.val 1 1).im by linarith)]
  nlinarith [abs_nonneg (Z.val 0 1).im]

/-- **Exponential decay is integrable on the Siegel set**, for the invariant measure: the density
`det(Y)^{-3}` is bounded there, and the function is dominated by a product of integrable functions
of the coordinates. -/
lemma lintegral_siegelSet_lt_top (hc : 0 < c) : ∫⁻ τ in siegelSet,
    ENNReal.ofReal (rexp (-c * ((τ.val 0 0).im + (τ.val 1 1).im))) ∂invariantMeasure (Fin 2) <
      ∞ := by
  have he : MeasurableEmbedding (toCoords (l := Fin 2)) := measurableEmbedding_toCoords
  let g : (Sym2 (Fin 2) → ℂ) → ℝ≥0∞ := fun h ↦
    ENNReal.ofReal (rexp (-c * ((h s(0, 0)).im + (h s(1, 1)).im)))
  have hg : Measurable g := by
    fun_prop
  have hA : MeasurableSet (toCoords '' siegelSet) :=
    he.measurableSet_image.mpr measurableSet_siegelSet
  have hsub : toCoords '' siegelSet ⊆ coordSet (Fin 2) := by
    rintro _ ⟨τ, -, rfl⟩
    exact toCoords_mem_coordSet τ
  have h₁ : ∫⁻ τ in siegelSet, ENNReal.ofReal (rexp (-c * ((τ.val 0 0).im + (τ.val 1 1).im)))
      ∂invariantMeasure (Fin 2) = ∫⁻ h in toCoords '' siegelSet, g h
        ∂(volume.withDensity (coordDensity (Fin 2))) := by
    have hmap : (invariantMeasure (Fin 2)).map toCoords =
        (volume.withDensity (coordDensity (Fin 2))).restrict (coordSet (Fin 2)) := by
      rw [invariantMeasure, he.map_comap, range_toCoords]
    rw [← Measure.restrict_restrict_of_subset hsub, ← hmap, he.restrict_map,
      he.injective.preimage_image, he.lintegral_map]
    exact lintegral_congr fun τ ↦ by
      simp only [g, toCoords_apply]
  have hprod :
      Integrable fun h : Sym2 (Fin 2) → ℂ ↦ (25 / 12 : ℝ) ^ 3 * ∏ s, stripBound (c / 3) (h s) :=
    (Integrable.fintype_prod fun _ ↦ integrable_stripBound (by positivity)).const_mul _
  rw [h₁, setLIntegral_withDensity_eq_setLIntegral_mul volume measurable_coordDensity hg hA]
  refine lt_of_le_of_lt ((setLIntegral_mono' hA ?_).trans (setLIntegral_le_lintegral _ _))
    hprod.lintegral_lt_top
  rintro _ ⟨τ, hτ, rfl⟩
  have hb : g τ.toCoords = ENNReal.ofReal (rexp (-c * ((τ.val 0 0).im + (τ.val 1 1).im))) := by
    simp only [g, toCoords_apply]
  rw [Pi.mul_apply, hb, ENNReal.ofReal_mul (by norm_num)]
  exact mul_le_mul' (coordDensity_toCoords_le hτ)
    (ENNReal.ofReal_le_ofReal (rexp_le_prod_stripBound hc hτ))

lemma mul_rexp_mul_pow_le (C : ℝ) (N : ℕ) (hc : 0 < c) {x : ℝ} (hx : 0 ≤ x) : C * rexp (-c * x) *
    (1 + x) ^ N ≤ |C| * (N.factorial / (c / 2) ^ N * rexp (c / 2)) * rexp (-(c / 2) * x) := by
  have h₁ : (1 + x) ^ N ≤ N.factorial / (c / 2) ^ N * rexp (c / 2 * (1 + x)) :=
    ModularForm.one_add_pow_le_mul_rexp N (by positivity) hx
  have h₂ : C * rexp (-c * x) * (1 + x) ^ N ≤
      |C| * rexp (-c * x) * (N.factorial / (c / 2) ^ N * rexp (c / 2 * (1 + x))) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_nonneg _)) h₁
      (pow_nonneg (by linarith) N) (by positivity)
  refine h₂.trans_eq ?_
  have e : rexp (-c * x) * rexp (c / 2 * (1 + x)) = rexp (c / 2) * rexp (-(c / 2) * x) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring1
  linear_combination (|C| * (N.factorial / (c / 2) ^ N)) * e

/-- **Exponential decay times a polynomial is integrable on the Siegel set.** -/
lemma lintegral_siegelSet_mul_pow_lt_top (C : ℝ) (N : ℕ) (hc : 0 < c) : ∫⁻ τ in siegelSet,
    ENNReal.ofReal (C * rexp (-c * ((τ.val 0 0).im + (τ.val 1 1).im)) *
      (1 + (τ.val 0 0).im + (τ.val 1 1).im) ^ N) ∂invariantMeasure (Fin 2) < ∞ := by
  have hbound : ∀ τ ∈ siegelSet, ENNReal.ofReal (C * rexp (-c * ((τ.val 0 0).im + (τ.val 1 1).im)) *
      (1 + (τ.val 0 0).im + (τ.val 1 1).im) ^ N) ≤
        ENNReal.ofReal (|C| * (N.factorial / (c / 2) ^ N * rexp (c / 2))) *
          ENNReal.ofReal (rexp (-(c / 2) * ((τ.val 0 0).im + (τ.val 1 1).im))) := by
    intro τ hτ
    rw [← ENNReal.ofReal_mul (by positivity), add_assoc]
    exact ENNReal.ofReal_le_ofReal <| mul_rexp_mul_pow_le C N hc <| by
      linarith [four_fifths_le_im_zero_zero hτ, four_fifths_le_im_one_one hτ]
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_siegelSet hbound) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_siegelSet_lt_top (by positivity))

end SiegelUpperHalfSpace
