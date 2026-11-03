import LeanBridge.ForMathlib.Analysis.Complex.UpperHalfPlane.StripIntegral
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraIntegral
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraSeed

/-!
# The seed of Niwa's kernel over a vertical strip

The seed `φ` of the Petersson integrand of `g ∈ S_{k/2}(N, χ)`, `k = 2 l + 1`, against Niwa's kernel
is a sum over `(n, b) ∈ ℕ+ × ℤ` of explicit terms. Hecke's bound makes them integrable on the strip
`0 ≤ x < 1`, with summable `L¹` norms. The integral of a term is `a(b²)` times an integral in `y`,
which vanishes for `b > 0` and `l ≥ 1` and is explicit for `b < 0`; the term `b = 0` vanishes since
`a(0) = 0`. So the integral of `φ` is `(i v² / 2) ^ l / l!` times `∑ A(n) e(n w)`, `A = Sh₁(a)`.

## Main definitions

* `ModularForm.shimuraSeedTerm`: a term of the seed.
* `ModularForm.shimuraSeedIntegralBound`: the bound of the integral of a term.
* `ModularForm.shimuraYIntegral`: the integral in `y`.

## Main results

* `ModularForm.integrableOn_shimuraSeed`: the seed is integrable on the strip.
* `ModularForm.hasSum_setIntegral_shimuraSeedTerm`: its integral is the sum of those of its terms.
* `ModularForm.eq_of_forall_hasSum_cexp`: Fourier coefficients on `ℍ` are unique.
* `ModularForm.setIntegral_shimuraSeed`: the Fourier expansion of the integral of the seed.
-/

open Complex CongruenceSubgroup Filter MeasureTheory ModularGroup Set

open scoped Real MatrixGroups ComplexConjugate Nat ENNReal

open UpperHalfPlane hiding I I_re I_im

namespace ModularForm

lemma integrable_tsum_of_summable_integral_norm {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [Countable ι] {F : ι → α → ℂ} (hF_int : ∀ i, Integrable (F i) μ)
    (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) (hF : ∀ a, Summable fun i ↦ F i a) :
    Integrable (fun a ↦ ∑' i, F i a) μ := by
  have hm : AEStronglyMeasurable (fun a ↦ ∑' i, F i a) μ :=
    aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι)) (f := fun s a ↦ ∑ i ∈ s, F i a)
      (fun s ↦ Finset.aestronglyMeasurable_fun_sum s fun i _ ↦ (hF_int i).aestronglyMeasurable)
      (.of_forall fun a ↦ (hF a).hasSum)
  refine ⟨hm, ?_⟩
  have h1 (i : ι) : ∫⁻ a, ‖F i a‖ₑ ∂μ = ‖∫ a, ‖F i a‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF_int i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun a ↦ norm_nonneg (F i a)))]
    simp only [coe_nnnorm]
  have h2 : ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ ≠ ⊤ := by
    rw [funext h1]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hF_sum.abs
  refine lt_of_le_of_lt ?_ h2.lt_top
  rw [← lintegral_tsum fun i ↦ (hF_int i).aestronglyMeasurable.enorm]
  exact lintegral_mono fun a ↦ enorm_tsum_le_tsum_enorm

section RealAnalysis

variable {s B : ℝ}

lemma integrableOn_rpow_neg_sub_one_mul_exp_neg_div (hs : 0 < s) (hB : 0 < B) :
    IntegrableOn (fun y : ℝ ↦ y ^ (-s - 1) * Real.exp (-(B / y))) (Ioi 0) := by
  have hG : IntegrableOn (fun t : ℝ ↦ t ^ (s - 1) * Real.exp (-(B * t))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using integrableOn_rpow_mul_exp_neg_mul_rpow (s := s - 1)
      (p := 1) (by linarith) one_pos hB
  refine ((integrableOn_Ioi_comp_rpow_iff' _ (p := -1) (by norm_num)).mpr hG).congr <|
    (ae_restrict_iff' measurableSet_Ioi).mpr <| .of_forall fun y hy ↦ ?_
  have hy0 : 0 < y := hy
  have e : (y ^ (-1 : ℝ)) ^ (s - 1) = y ^ (-1 * (s - 1)) := (Real.rpow_mul hy0.le _ _).symm
  simp only [smul_eq_mul]
  rw [e, ← mul_assoc, ← Real.rpow_add hy0, Real.rpow_neg_one]
  congr 2
  ring1

lemma integral_rpow_neg_sub_one_mul_exp_neg_div (hs : 0 < s) (hB : 0 < B) :
    ∫ y in Ioi (0 : ℝ), y ^ (-s - 1) * Real.exp (-(B / y)) = (1 / B) ^ s * Real.Gamma s := by
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hs hB, ← integral_comp_rpow_Ioi
    (fun t : ℝ ↦ t ^ (s - 1) * Real.exp (-(B * t))) (p := -1) (by norm_num)]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
  have hy0 : 0 < y := hy
  have e : (y ^ (-1 : ℝ)) ^ (s - 1) = y ^ (-1 * (s - 1)) := (Real.rpow_mul hy0.le _ _).symm
  simp only [smul_eq_mul]
  rw [e, abs_neg, abs_one, one_mul, ← mul_assoc, ← Real.rpow_add hy0, Real.rpow_neg_one]
  congr 2
  ring1

lemma exp_neg_pi_mul_sq_le {y : ℝ} (hy : 0 < y) (b : ℝ) :
    Real.exp (-(π * y) * b ^ 2) ≤ (1 + y⁻¹) * (1 + b ^ 2)⁻¹ := by
  have hp : 3 < π := Real.pi_gt_three
  have h1 : π * y * b ^ 2 + 1 ≤ Real.exp (π * y * b ^ 2) := Real.add_one_le_exp _
  have h2 : Real.exp (-(π * y) * b ^ 2) = (Real.exp (π * y * b ^ 2))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring1
  have h3 : 0 < π * y * b ^ 2 + 1 := by positivity
  rw [h2]
  refine (inv_anti₀ h3 h1).trans ?_
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ h3 (by positivity)]
  have h4 : 0 ≤ (π - 1) * b ^ 2 := mul_nonneg (by linarith) (sq_nonneg b)
  have h5 : (1 + y⁻¹) * (π * y * b ^ 2 + 1) = π * y * b ^ 2 + π * b ^ 2 + 1 + y⁻¹ := by
    field_simp
    ring1
  have h6 : 0 < y⁻¹ := inv_pos.mpr hy
  have h7 : 0 ≤ π * y * b ^ 2 := by positivity
  rw [h5]
  nlinarith

end RealAnalysis

section Strip

variable {f : ℍ → ℂ} {h : ℝ → ℝ}

private lemma coe_ofComplex {x y : ℝ} (hy : 0 < y) :
    ((ofComplex ((x : ℂ) + y * I) : ℍ) : ℂ) = x + y * I := by
  rw [ofComplex_apply_of_im_pos (by simpa using hy)]

private lemma im_ofComplex {x y : ℝ} (hy : 0 < y) : (ofComplex ((x : ℂ) + y * I)).im = y := by
  rw [← UpperHalfPlane.coe_im, coe_ofComplex hy]
  simp

lemma integrableOn_im_sq_mul (hh : IntegrableOn h (Ioi 0)) :
    IntegrableOn (fun z : ℍ ↦ z.im ^ 2 * h z.im) {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)} := by
  have h1 : IntegrableOn (fun p : ℝ × ℝ ↦ h p.2) (Ico 0 1 ×ˢ Ioi 0) (volume.prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact Integrable.comp_snd hh _
  rw [integrableOn_re_mem_Ico_iff, Measure.volume_eq_prod]
  refine h1.congr <| (ae_restrict_iff' (measurableSet_Ico.prod measurableSet_Ioi)).mpr <|
    .of_forall fun p hp ↦ ?_
  have hy : 0 < p.2 := hp.2
  simp only [smul_eq_mul, im_ofComplex hy]
  field_simp

lemma setIntegral_im_sq_mul :
    ∫ z in {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)}, z.im ^ 2 * h z.im = ∫ y in Ioi 0, h y := by
  rw [setIntegral_re_mem_Ico, Measure.volume_eq_prod]
  have e : ∫ p in Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ), ((p.2 ^ 2)⁻¹ : ℝ) •
      ((ofComplex ((p.1 : ℂ) + p.2 * I)).im ^ 2 * h (ofComplex ((p.1 : ℂ) + p.2 * I)).im)
        ∂(volume.prod volume) = ∫ p in Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ), (1 : ℝ) * h p.2
          ∂(volume.prod volume) := by
    refine setIntegral_congr_fun (measurableSet_Ico.prod measurableSet_Ioi) fun p hp ↦ ?_
    have hy : 0 < p.2 := hp.2
    simp only [smul_eq_mul, im_ofComplex hy]
    field_simp
  rw [e, setIntegral_prod_mul (fun _ ↦ (1 : ℝ)) h (Ico 0 1) (Ioi 0)]
  simp

lemma integrableOn_strip_of_le (hf : Continuous f) (hh : IntegrableOn h (Ioi 0))
    (hb : ∀ z : ℍ, (z.im ^ 2)⁻¹ * ‖f z‖ ≤ h z.im) : IntegrableOn f {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)} :=
  (integrableOn_im_sq_mul hh).mono' hf.aestronglyMeasurable (.of_forall fun z ↦
    (inv_mul_le_iff₀ (pow_pos z.im_pos 2)).mp (hb z))

lemma integral_norm_strip_le (hf : Continuous f) (hh : IntegrableOn h (Ioi 0))
    (hb : ∀ z : ℍ, (z.im ^ 2)⁻¹ * ‖f z‖ ≤ h z.im) :
    ∫ z in {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)}, ‖f z‖ ≤ ∫ y in Ioi 0, h y := by
  rw [← setIntegral_im_sq_mul]
  exact integral_mono (integrableOn_strip_of_le hf hh hb).norm (integrableOn_im_sq_mul hh) fun z ↦
    (inv_mul_le_iff₀ (pow_pos z.im_pos 2)).mp (hb z)

end Strip

lemma continuous_shimuraKernelTerm (w : ℍ) (C μ b : ℤ) (l : ℕ) :
    Continuous fun z : ℍ ↦ shimuraKernelTerm z w C μ b l := by
  have him : Continuous fun z : ℍ ↦ (z.im : ℂ) := continuous_ofReal.comp continuous_im
  have hz : Continuous fun z : ℍ ↦ (z : ℂ) := continuous_coe
  have hc : Continuous fun z : ℍ ↦ conj (z : ℂ) := continuous_conj.comp hz
  have h0 (z : ℍ) : (4 * (z.im : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr z.im_ne_zero)
  have hq : Continuous fun z : ℍ ↦ (w.im : ℂ) / (4 * (z.im : ℂ)) :=
    continuous_const.div (continuous_const.mul him) h0
  have hq' : Continuous fun z : ℍ ↦ (π : ℂ) * (w.im : ℂ) ^ 2 / (4 * (z.im : ℂ)) :=
    continuous_const.div (continuous_const.mul him) h0
  have hτ : Continuous fun z : ℍ ↦ (C : ℂ) * z + μ := (continuous_const.mul hz).add continuous_const
  have hτb : Continuous fun z : ℍ ↦ (C : ℂ) * conj (z : ℂ) + μ :=
    (continuous_const.mul hc).add continuous_const
  have hE : Continuous fun z : ℍ ↦ shimuraKernelTermExp z w C μ b :=
    ((hq'.neg.mul hτ).mul hτb).add
      (continuous_const.mul ((continuous_const.mul hz).add continuous_const))
  have hα : Continuous fun z : ℍ ↦ shimuraKernelAlpha z w C μ b :=
    continuous_const.mul (continuous_const.sub (hq.mul hτb))
  have hβ : Continuous fun z : ℍ ↦ ((shimuraKernelBeta z w : ℝ) : ℂ) := by
    unfold shimuraKernelBeta
    refine continuous_ofReal.comp (continuous_const.div (continuous_const.mul continuous_im)
      fun z ↦ ?_)
    have hp : 0 < π := Real.pi_pos
    exact (mul_pos (mul_pos (by norm_num) hp) z.im_pos).ne'
  have hG : Continuous ((fun p : ℂ × ℂ ↦ gaussCoeff l p.1 p.2) ∘
      fun z : ℍ ↦ (shimuraKernelAlpha z w C μ b, ((shimuraKernelBeta z w : ℝ) : ℂ))) :=
    (continuous_gaussCoeff l).comp (hα.prodMk hβ)
  unfold shimuraKernelTerm
  exact (continuous_const.mul hE.cexp).mul hG

variable {N : ℕ} (ψ : DirichletCharacter ℂ N) (g : ℍ → ℂ) (w : ℍ) (l : ℕ)

/-- The term `g(z) conj(ψ⁻¹(n) T_b(z)) y^{k/2}` of the seed of **Niwa's kernel** (LMFDB
`cmf.shimura_correspondence`), with `T_b` the `b`-th term of `S^(l)(z, w; 0, n)`. -/
noncomputable def shimuraSeedTerm (x : ℕ+ × ℤ) (z : ℍ) : ℂ :=
  g z * conj (ψ⁻¹ (((x.1 : ℕ) : ℤ) : ZMod N) * shimuraKernelTerm z w 0 ((x.1 : ℕ) : ℤ) x.2 l) *
    ((z.im ^ (((2 * l + 1 : ℤ) : ℝ) / 2) : ℝ) : ℂ)

variable {g} {K : ℝ} {χ : DirichletCharacter ℂ N}

private lemma seed_bound_algebra {P G c T E₁ E₂ E₃ M₁ X Z y C : ℝ} (hP : 0 ≤ P) (hG : 0 ≤ G)
    (hc : c ≤ 1) (hT : 0 ≤ T) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) (hE₃ : 0 ≤ E₃) (hK : G * E₁ ≤ K)
    (hM : T * E₂ ≤ M₁ * (X * Z)) (hZ : Z ≤ (1 + y) * C) (hK0 : 0 ≤ K) (hM₁ : 0 ≤ M₁) (hX : 0 ≤ X) :
    P * (G * (c * T) * (E₁ * E₂ * E₃)) ≤ K * M₁ * C * (P * E₃ * X + P * E₃ * y * X) := by
  have h1 : (G * E₁) * (T * E₂) ≤ K * (M₁ * (X * ((1 + y) * C))) :=
    mul_le_mul hK (hM.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZ hX) hM₁))
      (mul_nonneg hT hE₂) hK0
  have h2 : c * ((G * E₁) * (T * E₂)) ≤ (G * E₁) * (T * E₂) :=
    mul_le_of_le_one_left (by positivity) hc
  have e1 : P * (G * (c * T) * (E₁ * E₂ * E₃)) = P * E₃ * (c * ((G * E₁) * (T * E₂))) := by
    ring1
  have e2 : K * M₁ * C * (P * E₃ * X + P * E₃ * y * X) =
      P * E₃ * (K * (M₁ * (X * ((1 + y) * C)))) := by
    ring1
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left (h2.trans h1) (mul_nonneg hP hE₃)

lemma norm_shimuraSeedTerm_le (hK0 : 0 ≤ K)
    (hK : ∀ z : ℍ, ‖g z‖ * z.im ^ (((2 * l + 1 : ℤ) : ℝ) / 4) ≤ K) (x : ℕ+ × ℤ) (z : ℍ) :
    (z.im ^ 2)⁻¹ * ‖shimuraSeedTerm ψ g w l x z‖ ≤
      (K * (w.im / 2 * Real.exp (7 * w.im ^ 2 / (16 * π))) * (1 + (x.2 : ℝ) ^ 2)⁻¹) *
        (z.im ^ (-(3 / 4 : ℝ) - 1) * Real.exp (-(π * w.im ^ 2 / 8 * ((x.1 : ℕ) : ℝ) ^ 2 / z.im)) +
          z.im ^ (-(7 / 4 : ℝ) - 1) *
            Real.exp (-(π * w.im ^ 2 / 8 * ((x.1 : ℕ) : ℝ) ^ 2 / z.im))) := by
  have hy : 0 < z.im := z.im_pos
  have hv : 0 < w.im := w.im_pos
  have hp : 0 < π := Real.pi_pos
  have hmaj : ‖shimuraKernelTerm z w 0 ((x.1 : ℕ) : ℤ) x.2 l‖ * Real.sqrt z.im ^ l ≤
      shimuraKernelMajorant z w 0 ((x.1 : ℕ) : ℤ) x.2 (Real.sqrt z.im) :=
    norm_shimuraKernelTerm_mul_pow_le z w 0 ((x.1 : ℕ) : ℤ) x.2 l (Real.sqrt_nonneg z.im)
  have hn : normSq ((((0 : ℤ) : ℂ)) * z + (((x.1 : ℕ) : ℤ) : ℂ)) = ((x.1 : ℕ) : ℝ) ^ 2 := by
    rw [normSq_apply]
    simp
    ring1
  have hM : shimuraKernelMajorant z w 0 ((x.1 : ℕ) : ℤ) x.2 (Real.sqrt z.im) =
      w.im / 2 * Real.exp (7 * w.im ^ 2 / (16 * π)) *
        (Real.exp (-(π * w.im ^ 2 / 8 * ((x.1 : ℕ) : ℝ) ^ 2 / z.im)) *
          Real.exp (-(π * z.im) * (x.2 : ℝ) ^ 2)) := by
    rw [shimuraKernelMajorant, hn, Real.sq_sqrt hy.le]
    have e1 : 7 * z.im * w.im ^ 2 / (16 * π * z.im) = 7 * w.im ^ 2 / (16 * π) := by
      field_simp
    have e2 : -(π * w.im ^ 2 / (8 * z.im)) * ((x.1 : ℕ) : ℝ) ^ 2 =
        -(π * w.im ^ 2 / 8 * ((x.1 : ℕ) : ℝ) ^ 2 / z.im) := by
      field_simp
    rw [e1, e2]
    simp
  rw [hM] at hmaj
  have hc : ‖ψ⁻¹ (((x.1 : ℕ) : ℤ) : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one ψ⁻¹ _
  have hsqrt : Real.sqrt z.im ^ l = z.im ^ ((l : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    congr 1
    ring1
  have hY : z.im ^ (((2 * l + 1 : ℤ) : ℝ) / 2) =
      z.im ^ (((2 * l + 1 : ℤ) : ℝ) / 4) * Real.sqrt z.im ^ l * z.im ^ (1 / 4 : ℝ) := by
    rw [hsqrt, ← Real.rpow_add hy, ← Real.rpow_add hy]
    congr 1
    push_cast
    ring1
  have hP₁ : (z.im ^ 2)⁻¹ * z.im ^ (1 / 4 : ℝ) = z.im ^ (-(3 / 4 : ℝ) - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hy.le, ← Real.rpow_add hy]
    norm_num
  have hP₂ : z.im ^ (-(7 / 4 : ℝ) - 1) = z.im ^ (-(3 / 4 : ℝ) - 1) * z.im⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hy]
    norm_num
  have hE₃ : 0 ≤ z.im ^ (1 / 4 : ℝ) := by positivity
  rw [shimuraSeedTerm, norm_mul, norm_mul, RCLike.norm_conj, norm_mul, norm_real,
    Real.norm_of_nonneg (by positivity), hY, hP₂, ← hP₁]
  exact seed_bound_algebra (by positivity) (norm_nonneg _) hc (norm_nonneg _) (by positivity)
    (by positivity) hE₃ (hK z) hmaj (exp_neg_pi_mul_sq_le hy (x.2 : ℝ)) hK0 (by positivity)
    (by positivity)

/-- The bound of the integral over the strip of a term of the seed. -/
noncomputable def shimuraSeedIntegralBound (A : ℝ) (n : ℕ+) : ℝ :=
  (1 / (A * ((n : ℕ) : ℝ) ^ 2)) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4) +
    (1 / (A * ((n : ℕ) : ℝ) ^ 2)) ^ (7 / 4 : ℝ) * Real.Gamma (7 / 4)

private lemma integrable_bound {A : ℝ} (hA : 0 < A) (n : ℕ+) : IntegrableOn (fun y : ℝ ↦
    y ^ (-(3 / 4 : ℝ) - 1) * Real.exp (-(A * ((n : ℕ) : ℝ) ^ 2 / y)) +
      y ^ (-(7 / 4 : ℝ) - 1) * Real.exp (-(A * ((n : ℕ) : ℝ) ^ 2 / y))) (Ioi 0) := by
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := Nat.cast_pos.mpr n.pos
  exact (integrableOn_rpow_neg_sub_one_mul_exp_neg_div (by norm_num) (by positivity)).add
    (integrableOn_rpow_neg_sub_one_mul_exp_neg_div (by norm_num) (by positivity))

private lemma integral_bound {A : ℝ} (hA : 0 < A) (n : ℕ+) : ∫ y in Ioi (0 : ℝ),
    (y ^ (-(3 / 4 : ℝ) - 1) * Real.exp (-(A * ((n : ℕ) : ℝ) ^ 2 / y)) +
      y ^ (-(7 / 4 : ℝ) - 1) * Real.exp (-(A * ((n : ℕ) : ℝ) ^ 2 / y))) =
        shimuraSeedIntegralBound A n := by
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := Nat.cast_pos.mpr n.pos
  rw [integral_add (integrableOn_rpow_neg_sub_one_mul_exp_neg_div (by norm_num) (by positivity))
    (integrableOn_rpow_neg_sub_one_mul_exp_neg_div (by norm_num) (by positivity)),
    integral_rpow_neg_sub_one_mul_exp_neg_div (by norm_num) (by positivity),
    integral_rpow_neg_sub_one_mul_exp_neg_div (by norm_num) (by positivity),
    shimuraSeedIntegralBound]

private lemma summable_one_div_mul_sq_rpow {A s : ℝ} (hA : 0 < A) (hs : 1 / 2 < s) :
    Summable fun n : ℕ+ ↦ (1 / (A * ((n : ℕ) : ℝ) ^ 2)) ^ s := by
  have h1 : Summable fun n : ℕ ↦ (((n : ℝ)) ^ (2 * s))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  refine ((h1.comp_injective PNat.coe_injective).mul_left ((1 / A) ^ s)).congr fun n ↦ ?_
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := Nat.cast_pos.mpr n.pos
  have e : 1 / (A * ((n : ℕ) : ℝ) ^ 2) = (1 / A) * (((n : ℕ) : ℝ) ^ 2)⁻¹ := by
    field_simp
  rw [e, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul hn.le]
  simp

lemma summable_shimuraSeedIntegralBound {A : ℝ} (hA : 0 < A) :
    Summable (shimuraSeedIntegralBound A) :=
  ((summable_one_div_mul_sq_rpow hA (by norm_num)).mul_right _).add
    ((summable_one_div_mul_sq_rpow hA (by norm_num)).mul_right _)

lemma shimuraSeedIntegralBound_nonneg {A : ℝ} (hA : 0 < A) (n : ℕ+) :
    0 ≤ shimuraSeedIntegralBound A n := by
  have h1 : 0 < Real.Gamma (3 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have h2 : 0 < Real.Gamma (7 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  rw [shimuraSeedIntegralBound]
  positivity

lemma summable_inv_one_add_sq : Summable fun b : ℤ ↦ (1 + (b : ℝ) ^ 2)⁻¹ := by
  refine Summable.of_norm_bounded_eventually (g := fun b : ℤ ↦ 1 / (b : ℝ) ^ 2)
    (Real.summable_one_div_int_pow.mpr one_lt_two) ?_
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with b hb
  have hb' : (0 : ℝ) < (b : ℝ) ^ 2 := by
    have h : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    positivity
  rw [Real.norm_of_nonneg (by positivity), one_div]
  exact inv_anti₀ hb' (by linarith)

variable (χ) in
lemma continuous_shimuraSeedTerm {k : ℤ} (hg : g ∈ halfIntegralWeightSpace χ k) (x : ℕ+ × ℤ) :
    Continuous (shimuraSeedTerm ψ g w l x) := by
  have hg' : Continuous g := hg.1.continuous
  have h2 : Continuous fun z : ℍ ↦ ((z.im ^ (((2 * l + 1 : ℤ) : ℝ) / 2) : ℝ) : ℂ) := by
    refine continuous_ofReal.comp <| continuous_im.rpow_const fun z ↦ .inl z.im_ne_zero
  unfold shimuraSeedTerm
  exact (hg'.mul (continuous_conj.comp (continuous_const.mul
    (continuous_shimuraKernelTerm w 0 ((x.1 : ℕ) : ℤ) x.2 l)))).mul h2

lemma integral_conj_cexp_mul_of_hasSum {a : ℕ → ℂ}
    (ha : ∀ z : ℍ, HasSum (fun j : ℕ ↦ a j * cexp (2 * π * I * j * z)) (g z)) (m : ℕ) {y : ℝ}
    (hy : 0 < y) : ∫ x in (0 : ℝ)..1, conj (cexp (2 * π * I * (m : ℂ) * ((x : ℂ) + y * I))) *
      g (ofComplex ((x : ℂ) + y * I)) = ((Real.exp (-(4 * π * m * y)) : ℝ) : ℂ) * a m := by
  have hF (z : ℍ) : HasSum (fun j : ℕ ↦ a j *
      cexp (2 * π * I * ((j : ℂ) / ((1 : ℕ) : ℂ)) * z)) (g z) := by
    simpa only [Nat.cast_one, div_one] using ha z
  have e : 4 * π * m * y = 2 * π * ((m + m : ℕ) : ℝ) * y := by
    push_cast
    ring1
  rw [e]
  simpa only [Nat.cast_one, div_one, one_mul] using integral_conj_exp_mul_eq 1 m a y one_pos
    (fun c ↦ g (ofComplex c)) (fun x ↦ by
      simpa only [coe_ofComplex hy] using hF (ofComplex ((x : ℂ) + y * I)))
    (summable_norm_mul_exp_of_hasSum 1 _ y one_pos hF hy)

/-- **The Fourier coefficients of a function on `ℍ` are unique.** -/
lemma eq_of_forall_hasSum_cexp {a b : ℕ → ℂ}
    (ha : ∀ z : ℍ, HasSum (fun j : ℕ ↦ a j * cexp (2 * π * I * j * z)) (g z))
    (hb : ∀ z : ℍ, HasSum (fun j : ℕ ↦ b j * cexp (2 * π * I * j * z)) (g z)) (m : ℕ) :
    a m = b m :=
  mul_left_cancel₀ (ofReal_ne_zero.mpr (Real.exp_pos _).ne')
    ((integral_conj_cexp_mul_of_hasSum ha m one_pos).symm.trans
      (integral_conj_cexp_mul_of_hasSum hb m one_pos))

lemma coeff_qExpansion_eq_of_hasSum {k : ℤ} (hg : g ∈ halfIntegralWeightCuspSpace χ k) {b : ℕ → ℂ}
    (hb : ∀ z : ℍ, HasSum (fun j : ℕ ↦ b j * cexp (2 * π * I * j * z)) (g z)) (m : ℕ) :
    (qExpansion 1 g).coeff m = b m :=
  eq_of_forall_hasSum_cexp (hasSum_qExpansion_of_mem_halfIntegralWeightCuspSpace g hg) hb m

lemma integral_conj_cexp_mul_apply (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1)) (m : ℕ)
    {y : ℝ} (hy : 0 < y) : ∫ x in (0 : ℝ)..1,
      conj (cexp (2 * π * I * (m : ℂ) * ((x : ℂ) + y * I))) * g (ofComplex ((x : ℂ) + y * I)) =
        ((Real.exp (-(4 * π * m * y)) : ℝ) : ℂ) * (qExpansion 1 g).coeff m :=
  integral_conj_cexp_mul_of_hasSum (hasSum_qExpansion_of_mem_halfIntegralWeightCuspSpace g hg) m hy

private lemma natAbs_sq_cast (b : ℤ) : ((b.natAbs ^ 2 : ℕ) : ℂ) = (b : ℂ) ^ 2 := by
  have h : ((b.natAbs ^ 2 : ℕ) : ℤ) = b ^ 2 := by
    exact_mod_cast Int.natAbs_sq b
  rw [← Int.cast_natCast, h, Int.cast_pow]

private lemma natAbs_sq_cast_real (b : ℤ) : ((b.natAbs ^ 2 : ℕ) : ℝ) = (b : ℝ) ^ 2 := by
  have h : ((b.natAbs ^ 2 : ℕ) : ℤ) = b ^ 2 := by
    exact_mod_cast Int.natAbs_sq b
  rw [← Int.cast_natCast, h, Int.cast_pow]

private lemma conj_alpha_zero (z : ℍ) (n b : ℤ) : conj (shimuraKernelAlpha z w 0 n b) =
    -I * (w.im : ℂ) * b + I * (w.im : ℂ) ^ 2 * n / (4 * (z.im : ℂ)) := by
  have hy : (z.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr z.im_ne_zero
  simp only [shimuraKernelAlpha, map_mul, map_sub, map_div₀, conj_I, conj_ofReal, map_intCast,
    Int.cast_zero, zero_mul, zero_div, add_zero, zero_add, map_ofNat]
  field_simp
  ring1

private lemma conj_cexp_termExp (z : ℍ) (n b : ℤ) : conj (cexp (shimuraKernelTermExp z w 0 n b)) =
    ((Real.exp (-(π * w.im ^ 2 / (4 * z.im)) * (n : ℝ) ^ 2) : ℝ) : ℂ) *
      cexp (-(2 * π * I * n * w.re * b)) *
        conj (cexp (2 * π * I * ((b.natAbs ^ 2 : ℕ) : ℂ) * z)) := by
  rw [← exp_conj, ← exp_conj, ofReal_exp, ← exp_add, ← exp_add]
  congr 1
  rw [natAbs_sq_cast]
  simp only [shimuraKernelTermExp, map_add, map_mul, map_neg, map_div₀, map_pow, conj_I,
    conj_ofReal, map_intCast, map_ofNat, Int.cast_zero, zero_mul, zero_div, zero_add, add_zero]
  push_cast
  ring1

private lemma shimuraSeedTerm_eq (x : ℕ+ × ℤ) (z : ℍ) : shimuraSeedTerm ψ g w l x z =
    (((z.im ^ (((2 * l + 1 : ℤ) : ℝ) / 2) : ℝ) : ℂ) * ψ (((x.1 : ℕ) : ℤ) : ZMod N) *
      ((w.im : ℂ) / 2) *
        ((Real.exp (-(π * w.im ^ 2 / (4 * z.im)) * (((x.1 : ℕ) : ℤ) : ℝ) ^ 2) : ℝ) : ℂ) *
          cexp (-(2 * π * I * ((x.1 : ℕ) : ℤ) * w.re * x.2)) *
            gaussCoeff l (-I * (w.im : ℂ) * x.2 +
              I * (w.im : ℂ) ^ 2 * ((x.1 : ℕ) : ℤ) / (4 * (z.im : ℂ)))
                (shimuraKernelBeta z w : ℂ)) *
      (conj (cexp (2 * π * I * ((x.2.natAbs ^ 2 : ℕ) : ℂ) * z)) * g z) := by
  have hv : conj ((w.im : ℂ) / 2) = (w.im : ℂ) / 2 := by
    rw [map_div₀, conj_ofReal, map_ofNat]
  simp only [shimuraSeedTerm, shimuraKernelTerm, map_mul, conj_inv_apply, conj_gaussCoeff,
    conj_alpha_zero, conj_ofReal, conj_cexp_termExp, hv]
  ring1

variable [NeZero N]

lemma summable_shimuraSeedTerm (z : ℍ) : Summable fun x : ℕ+ × ℤ ↦ shimuraSeedTerm ψ g w l x z := by
  have hinj : Function.Injective fun x : ℕ+ × ℤ ↦ (((0 : ℤ), ((x.1 : ℕ) : ℤ)), x.2) := by
    rintro ⟨n, b⟩ ⟨n', b'⟩ h
    simp only [Prod.mk_inj, true_and, Nat.cast_inj] at h
    rw [PNat.coe_injective h.1, h.2]
  refine (((Complex.summable_conj.mpr
    ((summable_inv_mul_shimuraKernelTerm ψ z w l).comp_injective hinj)).mul_left (g z)).mul_right
      ((z.im ^ (((2 * l + 1 : ℤ) : ℝ) / 2) : ℝ) : ℂ)).congr fun x ↦ ?_
  simp [shimuraSeedTerm]

lemma shimuraSeed_eq_tsum (z : ℍ) :
    shimuraSeed ψ g w l z = ∑' x : ℕ+ × ℤ, shimuraSeedTerm ψ g w l x z := by
  rw [(summable_shimuraSeedTerm ψ w l z).tsum_prod, shimuraSeed]
  refine tsum_congr fun n ↦ ?_
  simp only [halfIntegralPeterssonIntegrand, shimuraPairTerm, shimuraSeedTerm, shimuraKernelCoeff]
  rw [← tsum_mul_left, Complex.conj_tsum, ← tsum_mul_left, ← tsum_mul_right]

private lemma exists_bound_of_mem (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1))
    (h4 : 4 ∣ N) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ, ‖g z‖ * z.im ^ (((2 * l + 1 : ℤ) : ℝ) / 4) ≤ K :=
  exists_norm_mul_rpow_le_of_mem_halfIntegralWeightCuspSpace hg (by simp) h4

private lemma pi_mul_sq_div_pos : 0 < π * w.im ^ 2 / 8 := by
  have hv : 0 < w.im := w.im_pos
  positivity

lemma integrableOn_shimuraSeedTerm (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1)) (h4 : 4 ∣ N)
    (x : ℕ+ × ℤ) : IntegrableOn (shimuraSeedTerm ψ g w l x) {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)} := by
  rcases exists_bound_of_mem l hg h4 with ⟨K, hK0, hK⟩
  exact integrableOn_strip_of_le (continuous_shimuraSeedTerm ψ w l χ hg.1 x)
    ((integrable_bound (pi_mul_sq_div_pos w) x.1).const_mul _)
    (norm_shimuraSeedTerm_le ψ w l hK0 hK x)

lemma summable_integral_norm_shimuraSeedTerm (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1))
    (h4 : 4 ∣ N) : Summable fun x : ℕ+ × ℤ ↦ ∫ z in {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)},
      ‖shimuraSeedTerm ψ g w l x z‖ := by
  rcases exists_bound_of_mem l hg h4 with ⟨K, hK0, hK⟩
  have hv : 0 < w.im := w.im_pos
  have hp : 0 < π := Real.pi_pos
  have hA : 0 < π * w.im ^ 2 / 8 := pi_mul_sq_div_pos w
  refine Summable.of_nonneg_of_le (fun x ↦ integral_nonneg fun z ↦ norm_nonneg _) (fun x ↦ ?_)
    (((summable_shimuraSeedIntegralBound hA).mul_of_nonneg summable_inv_one_add_sq
      (shimuraSeedIntegralBound_nonneg hA) fun b ↦ by positivity).mul_left
        (K * (w.im / 2 * Real.exp (7 * w.im ^ 2 / (16 * π)))))
  refine (integral_norm_strip_le (continuous_shimuraSeedTerm ψ w l χ hg.1 x)
    ((integrable_bound hA x.1).const_mul _) (norm_shimuraSeedTerm_le ψ w l hK0 hK x)).trans_eq ?_
  rw [integral_const_mul, integral_bound hA]
  ring1

/-- **The seed is integrable on the strip** (LMFDB `cmf.shimura_correspondence`). -/
lemma integrableOn_shimuraSeed (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1)) (h4 : 4 ∣ N) :
    IntegrableOn (shimuraSeed ψ g w l) {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)} := by
  simp_rw [funext (shimuraSeed_eq_tsum ψ w l)]
  exact integrable_tsum_of_summable_integral_norm (integrableOn_shimuraSeedTerm ψ w l hg h4)
    (summable_integral_norm_shimuraSeedTerm ψ w l hg h4) (summable_shimuraSeedTerm ψ w l)

/-- **The integral of the seed is the sum of the integrals of its terms** (LMFDB
`cmf.shimura_correspondence`). -/
lemma hasSum_setIntegral_shimuraSeedTerm (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1))
    (h4 : 4 ∣ N) : HasSum (fun x : ℕ+ × ℤ ↦ ∫ z in {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)},
      shimuraSeedTerm ψ g w l x z) (∫ z in {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)},
        shimuraSeed ψ g w l z) := by
  simp_rw [shimuraSeed_eq_tsum ψ w l]
  exact hasSum_integral_of_summable_integral_norm (integrableOn_shimuraSeedTerm ψ w l hg h4)
    (summable_integral_norm_shimuraSeedTerm ψ w l hg h4)

/-- The integral
`∫₀^∞ y ^ (-3/2) e^{-4 π b² y - π v² n² / (4 y)} G_l(-i v b y + i v² n / 4, v² y / (16 π)) dy`
in the unfolding of the Petersson product against **Niwa's kernel** (LMFDB
`cmf.shimura_correspondence`), for `G_l = gaussCoeff l`. -/
noncomputable def shimuraYIntegral (v n : ℝ) (b : ℤ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), ((y ^ (-(3 / 2) : ℝ) * Real.exp (-(4 * π * (b : ℝ) ^ 2 * y) -
    π * v ^ 2 * n ^ 2 / 4 / y) : ℝ) : ℂ) * gaussCoeff l (-I * v * b * y + I * (v : ℂ) ^ 2 * n / 4)
      ((v ^ 2 * y / (16 * π) : ℝ) : ℂ)

lemma setIntegral_shimuraSeedTerm (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1)) (h4 : 4 ∣ N)
    (x : ℕ+ × ℤ) : ∫ z in {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)}, shimuraSeedTerm ψ g w l x z =
      ψ (((x.1 : ℕ) : ℤ) : ZMod N) * ((w.im : ℂ) / 2) *
        cexp (-(2 * π * I * ((x.1 : ℕ) : ℤ) * w.re * x.2)) *
          (qExpansion 1 g).coeff (x.2.natAbs ^ 2) *
            shimuraYIntegral l w.im (((x.1 : ℕ) : ℝ)) x.2 := by
  have hint : IntegrableOn (shimuraSeedTerm ψ g w l x) {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)} :=
    integrableOn_shimuraSeedTerm ψ w l hg h4 x
  rw [integrableOn_re_mem_Ico_iff, Measure.volume_eq_prod] at hint
  rw [setIntegral_re_mem_Ico, Measure.volume_eq_prod, ← setIntegral_prod_swap]
  refine (setIntegral_prod _ hint.swap).trans ?_
  rw [shimuraYIntegral, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
  have hy0 : 0 < y := hy
  have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy0.ne'
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [Function.comp_apply, Prod.swap_prod_mk]
  have hpt : ∀ t ∈ Ico (0 : ℝ) 1, ((y ^ 2)⁻¹ : ℝ) • shimuraSeedTerm ψ g w l x
      (ofComplex ((t : ℂ) + y * I)) = ((((y ^ 2)⁻¹ : ℝ) : ℂ) *
        (((y ^ (((2 * l + 1 : ℤ) : ℝ) / 2) : ℝ) : ℂ) * ψ (((x.1 : ℕ) : ℤ) : ZMod N) *
          ((w.im : ℂ) / 2) *
            ((Real.exp (-(π * w.im ^ 2 / (4 * y)) * (((x.1 : ℕ) : ℤ) : ℝ) ^ 2) : ℝ) : ℂ) *
              cexp (-(2 * π * I * ((x.1 : ℕ) : ℤ) * w.re * x.2)) *
                gaussCoeff l (-I * (w.im : ℂ) * x.2 +
                  I * (w.im : ℂ) ^ 2 * ((x.1 : ℕ) : ℤ) / (4 * (y : ℂ)))
                    ((w.im ^ 2 / (16 * π * y) : ℝ) : ℂ))) *
        (conj (cexp (2 * π * I * ((x.2.natAbs ^ 2 : ℕ) : ℂ) * ((t : ℂ) + y * I))) *
          g (ofComplex ((t : ℂ) + y * I))) := by
    intro t _
    rw [Complex.real_smul, shimuraSeedTerm_eq, coe_ofComplex hy0, shimuraKernelBeta,
      im_ofComplex hy0]
    ring1
  rw [setIntegral_congr_fun measurableSet_Ico hpt, integral_const_mul,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_conj_cexp_mul_apply l hg _ hy0]
  have e3 : gaussCoeff l (-I * (w.im : ℂ) * x.2 * y + I * (w.im : ℂ) ^ 2 * ((x.1 : ℕ) : ℝ) / 4)
      ((w.im ^ 2 * y / (16 * π) : ℝ) : ℂ) = gaussCoeff l (-I * (w.im : ℂ) * x.2 +
        I * (w.im : ℂ) ^ 2 * ((x.1 : ℕ) : ℤ) / (4 * (y : ℂ)))
          ((w.im ^ 2 / (16 * π * y) : ℝ) : ℂ) * (y : ℂ) ^ l := by
    rw [← gaussCoeff_mul_mul_sq]
    congr 1
    · push_cast
      field_simp
    · push_cast
      field_simp
  have e1 : (y ^ 2)⁻¹ * y ^ (((2 * l + 1 : ℤ) : ℝ) / 2) = y ^ (-(3 / 2) : ℝ) * y ^ l := by
    rw [← Real.rpow_natCast y 2, ← Real.rpow_neg hy0.le, ← Real.rpow_add hy0,
      ← Real.rpow_natCast y l, ← Real.rpow_add hy0]
    congr 1
    push_cast
    ring1
  have e2 : Real.exp (-(π * w.im ^ 2 / (4 * y)) * (((x.1 : ℕ) : ℤ) : ℝ) ^ 2) *
      Real.exp (-(4 * π * ((x.2.natAbs ^ 2 : ℕ) : ℝ) * y)) =
        Real.exp (-(4 * π * (x.2 : ℝ) ^ 2 * y) - π * w.im ^ 2 * ((x.1 : ℕ) : ℝ) ^ 2 / 4 / y) := by
    rw [← Real.exp_add, natAbs_sq_cast_real]
    congr 1
    push_cast
    field_simp
    ring1
  have hc1 : (((y ^ 2)⁻¹ : ℝ) : ℂ) * ((y ^ (((2 * l + 1 : ℤ) : ℝ) / 2) : ℝ) : ℂ) =
      ((y ^ (-(3 / 2) : ℝ) : ℝ) : ℂ) * (y : ℂ) ^ l := by
    exact_mod_cast e1
  have hc2 : ((Real.exp (-(π * w.im ^ 2 / (4 * y)) * (((x.1 : ℕ) : ℤ) : ℝ) ^ 2) : ℝ) : ℂ) *
      ((Real.exp (-(4 * π * ((x.2.natAbs ^ 2 : ℕ) : ℝ) * y)) : ℝ) : ℂ) =
        ((Real.exp (-(4 * π * (x.2 : ℝ) ^ 2 * y) -
          π * w.im ^ 2 * ((x.1 : ℕ) : ℝ) ^ 2 / 4 / y) : ℝ) : ℂ) := by
    exact_mod_cast e2
  rw [e3, ofReal_mul]
  generalize gaussCoeff l (-I * (w.im : ℂ) * x.2 +
    I * (w.im : ℂ) ^ 2 * ((x.1 : ℕ) : ℤ) / (4 * (y : ℂ))) ((w.im ^ 2 / (16 * π * y) : ℝ) : ℂ) = G₀
  generalize (qExpansion 1 g).coeff (x.2.natAbs ^ 2) = a
  generalize cexp (-(2 * π * I * ((x.1 : ℕ) : ℤ) * w.re * x.2)) = c
  generalize ψ (((x.1 : ℕ) : ℤ) : ZMod N) = p
  generalize ((Real.exp (-(π * w.im ^ 2 / (4 * y)) * (((x.1 : ℕ) : ℤ) : ℝ) ^ 2) : ℝ) : ℂ) = X
    at hc2 ⊢
  generalize ((Real.exp (-(4 * π * ((x.2.natAbs ^ 2 : ℕ) : ℝ) * y)) : ℝ) : ℂ) = E at hc2 ⊢
  generalize ((y ^ (-(3 / 2) : ℝ) : ℝ) : ℂ) = Q at hc1 ⊢
  generalize (y : ℂ) ^ l = yl at hc1 ⊢
  linear_combination (p * ((w.im : ℂ) / 2) * c * G₀ * a * (X * E)) * hc1 +
    (p * ((w.im : ℂ) / 2) * c * G₀ * a * (Q * yl)) * hc2

lemma setIntegral_shimuraSeedTerm_of_pos (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1))
    (h4 : 4 ∣ N) (hl : l ≠ 0) {x : ℕ+ × ℤ} (hb : 0 < x.2) :
    ∫ z in {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)}, shimuraSeedTerm ψ g w l x z = 0 := by
  have hn : (0 : ℝ) < ((x.1 : ℕ) : ℝ) := Nat.cast_pos.mpr x.1.pos
  rw [setIntegral_shimuraSeedTerm ψ w l hg h4, shimuraYIntegral,
    integral_mul_gaussCoeff_of_pos l hb w.im_pos hn hl, mul_zero]

lemma setIntegral_shimuraSeedTerm_of_eq_zero (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1))
    (h4 : 4 ∣ N) {x : ℕ+ × ℤ} (hb : x.2 = 0) :
    ∫ z in {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)}, shimuraSeedTerm ψ g w l x z = 0 := by
  rw [setIntegral_shimuraSeedTerm ψ w l hg h4, hb]
  simp [coeff_zero_qExpansion_of_mem_halfIntegralWeightCuspSpace g hg]

lemma setIntegral_shimuraSeedTerm_of_neg (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1))
    (h4 : 4 ∣ N) (n B : ℕ+) : ∫ z in {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)},
      shimuraSeedTerm ψ g w l (n, -(((B : ℕ) : ℤ))) z = ψ (((n : ℕ) : ℤ) : ZMod N) *
        ((n : ℂ) ^ ((l : ℂ) - 1)) * (qExpansion 1 g).coeff ((B : ℕ) ^ 2) *
          cexp (2 * π * I * (((n * B : ℕ+) : ℕ) : ℂ) * w) *
            ((I * (w.im : ℂ) ^ 2 / 2) ^ l / (l ! : ℂ)) := by
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := Nat.cast_pos.mpr n.pos
  have hB : (-(((B : ℕ) : ℤ))) < 0 := by
    simp
  rw [setIntegral_shimuraSeedTerm ψ w l hg h4, shimuraYIntegral,
    integral_mul_gaussCoeff_of_neg l hB w.im_pos hn]
  dsimp only
  have hnat : (-(((B : ℕ) : ℤ))).natAbs = (B : ℕ) := by
    simp
  have hB' : (0 : ℝ) < ((B : ℕ) : ℝ) := Nat.cast_pos.mpr B.pos
  have habs : |((-(((B : ℕ) : ℤ)) : ℤ) : ℝ)| = ((B : ℕ) : ℝ) := by
    push_cast
    rw [abs_neg, abs_of_pos hB']
  have hw : (w : ℂ) = (w.re : ℂ) + (w.im : ℂ) * I := (Complex.re_add_im (w : ℂ)).symm
  have e1 : cexp (-(2 * π * I * ((n : ℕ) : ℤ) * w.re * ((-(((B : ℕ) : ℤ)) : ℤ) : ℂ))) *
      ((Real.exp (-(2 * π * w.im * ((n : ℕ) : ℝ) * ((B : ℕ) : ℝ))) : ℝ) : ℂ) =
        cexp (2 * π * I * (((n * B : ℕ+) : ℕ) : ℂ) * w) := by
    rw [ofReal_exp, ← exp_add]
    congr 1
    rw [hw]
    push_cast
    linear_combination (-(2 * (π : ℂ) * ((n : ℕ) : ℂ) * ((B : ℕ) : ℂ) * (w.im : ℂ))) * I_sq
  have hnc : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hvc : (w.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr w.im_ne_zero
  have e2 : ((n : ℂ)) ^ ((l : ℂ) - 1) = ((n : ℕ) : ℂ) ^ l / ((n : ℕ) : ℂ) := by
    have e3 : (n : ℂ) = ((n : ℕ) : ℂ) := rfl
    rw [e3, Complex.cpow_sub _ _ hnc, Complex.cpow_natCast, Complex.cpow_one]
  rw [hnat, habs, e2, ← e1]
  simp only [ofReal_mul, ofReal_div, ofReal_ofNat, ofReal_natCast]
  have e4 : (I * (w.im : ℂ) ^ 2 * ((n : ℕ) : ℂ) / 2) ^ l =
      (I * (w.im : ℂ) ^ 2 / 2) ^ l * ((n : ℕ) : ℂ) ^ l := by
    rw [← mul_pow]
    congr 1
    ring1
  rw [e4]
  generalize (I * (w.im : ℂ) ^ 2 / 2) ^ l = Q
  generalize ((n : ℕ) : ℂ) ^ l = nl
  generalize ((l ! : ℕ) : ℂ) = f
  field_simp

private lemma hasSum_pnat_prod (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1)) (h4 : 4 ∣ N)
    (hl : l ≠ 0) : HasSum (fun p : ℕ+ × ℕ+ ↦ ψ (((p.1 : ℕ) : ℤ) : ZMod N) *
      ((p.1 : ℂ) ^ ((l : ℂ) - 1)) * (qExpansion 1 g).coeff ((p.2 : ℕ) ^ 2) *
        cexp (2 * π * I * (((p.1 * p.2 : ℕ+) : ℕ) : ℂ) * w) *
          ((I * (w.im : ℂ) ^ 2 / 2) ^ l / (l ! : ℂ)))
      (∫ z in {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)}, shimuraSeed ψ g w l z) := by
  have hinj : Function.Injective fun p : ℕ+ × ℕ+ ↦ (p.1, -(((p.2 : ℕ) : ℤ))) := by
    rintro ⟨n, B⟩ ⟨n', B'⟩ h'
    simp only [Prod.mk_inj, neg_inj, Nat.cast_inj] at h'
    rw [h'.1, PNat.coe_injective h'.2]
  have hzero : ∀ x ∉ Set.range fun p : ℕ+ × ℕ+ ↦ (p.1, -(((p.2 : ℕ) : ℤ))),
      ∫ z in {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)}, shimuraSeedTerm ψ g w l x z = 0 := by
    intro x hx
    rcases lt_trichotomy x.2 0 with hb | hb | hb
    · refine (hx ⟨(x.1, ⟨(-x.2).toNat, by omega⟩), Prod.ext rfl ?_⟩).elim
      simp only [PNat.mk_coe]
      omega
    · exact setIntegral_shimuraSeedTerm_of_eq_zero ψ w l hg h4 hb
    · exact setIntegral_shimuraSeedTerm_of_pos ψ w l hg h4 hl hb
  convert (hinj.hasSum_iff hzero).mpr (hasSum_setIntegral_shimuraSeedTerm ψ w l hg h4) using 1
  exact funext fun p ↦ (setIntegral_shimuraSeedTerm_of_neg ψ w l hg h4 p.1 p.2).symm

/-- **The Fourier expansion of the integral of the seed** (LMFDB `cmf.shimura_correspondence`): for
`g = ∑ a(n) qⁿ ∈ S_{k/2}(N, χ)`, `k = 2 l + 1`, `l ≥ 1`, `4 ∣ N`, the integral of the seed over the
strip is `(i v² / 2) ^ l / l!` times the exponential sum of the coefficients
`∑_{d ∣ n} χ_1(d) d ^ (l - 1) a((n / d)²)` of the Shimura lift `Sh₁(g)`. -/
lemma setIntegral_shimuraSeed (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1)) (h4 : 4 ∣ N)
    (hl : l ≠ 0) : ∫ z in {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)},
      shimuraSeed (shimuraThetaCharacter χ l h4) g w l z =
        expSum (shimuraCoeff χ (2 * l + 1) 1 fun m ↦ (qExpansion 1 g).coeff m) w *
          ((I * (w.im : ℂ) ^ 2 / 2) ^ l / (l ! : ℂ)) := by
  have e0 : ((2 * (l : ℤ) + 1 - 1) / 2 : ℤ) = l := by omega
  have h3 : HasSum (fun m : ℕ ↦ shimuraCoeff χ (2 * l + 1) 1 (fun m ↦ (qExpansion 1 g).coeff m) m *
      cexp (2 * π * I * (m : ℂ) * w) * ((I * (w.im : ℂ) ^ 2 / 2) ^ l / (l ! : ℂ)))
        (∫ z in {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)},
          shimuraSeed (shimuraThetaCharacter χ l h4) g w l z) := by
    refine (PNat.coe_injective.hasSum_iff fun x hx ↦ ?_).mp ?_
    · have hx0 : x = 0 := by
        by_contra hne
        exact hx ⟨⟨x, Nat.pos_of_ne_zero hne⟩, rfl⟩
      rw [hx0, shimuraCoeff, LSeries.convolution_map_zero, zero_mul, zero_mul]
    refine (sigmaAntidiagonalEquivProd.hasSum_iff.mpr <|
      hasSum_pnat_prod (shimuraThetaCharacter χ l h4) w l hg h4 hl).sigma (g := fun m : ℕ+ ↦
        shimuraCoeff χ (2 * l + 1) 1 (fun m ↦ (qExpansion 1 g).coeff m) m *
          cexp (2 * π * I * ((m : ℕ) : ℂ) * w) * ((I * (w.im : ℂ) ^ 2 / 2) ^ l / (l ! : ℂ)))
        fun m ↦ ?_
    convert hasSum_fintype _ using 1
    rw [shimuraCoeff, LSeries.convolution_def, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_coe_sort]
    refine Fintype.sum_congr _ _ fun c ↦ ?_
    have hm :
        ((sigmaAntidiagonalEquivProd ⟨m, c⟩).1 * (sigmaAntidiagonalEquivProd ⟨m, c⟩).2 : ℕ+) = m :=
      PNat.coe_injective (divisorsAntidiagonalFactors_eq c)
    simp only [Function.comp_apply, hm]
    have e1 : (((sigmaAntidiagonalEquivProd ⟨m, c⟩).1 : ℕ) : ℕ) = c.1.1 := rfl
    have e2 : (((sigmaAntidiagonalEquivProd ⟨m, c⟩).2 : ℕ) : ℕ) = c.1.2 := rfl
    rw [e1, e2, e0, Int.cast_natCast, Int.cast_natCast, shimuraThetaCharacter_natCast, one_mul]
  rw [expSum, ← tsum_mul_right]
  exact h3.tsum_eq.symm

end ModularForm
