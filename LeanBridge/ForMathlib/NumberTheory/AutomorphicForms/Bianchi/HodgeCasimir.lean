import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.HarmonicOneForm

/-!
# Hodge harmonicity and the Casimir equations in weight 2

LMFDB `mf.bianchi.weight2` describes a weight 2 Bianchi modular form as a real analytic
`F : ℋ₃ → ℂ³` whose 1-form `F₁β₁ + F₂β₂ + F₃β₃` (`weightTwoOneForm`) is harmonic and invariant,
and LMFDB `mf.bianchi` as a function `y⁻¹ F` killed by both Casimir operators of `SL(2, ℂ)`
(`IsBianchiHarmonic 2`). The two descriptions agree once these harmonicity conditions do
(`isBianchiWeightTwoForm_iff_isBianchiModularForm`). For a single function they do not: the
1-form `x₂ dx₁`, `x = x₁ + i x₂`, has vanishing Hodge Laplacian `dδ + δd`, as `δ(x₂ dx₁) = 0` and
`δ(dx₂ ∧ dx₁) = 0`, but it is not closed, and the first Casimir operator `Ψ` does not kill the lift
of the corresponding `y⁻¹ F`: on the middle coordinate of that lift, `Φ₁ = αβ` with
`α(g) = Im(a c̄ + b d̄)` and `β(g) = Re(c d) / (|c|² + |d|²)³` for `g = (a, b; c, d)`, both
vanishing at the identity, so `ΨΦ₁(1) = ∑ (X α)(Y β) + (Y α)(X β)` over the terms `XY` of `Ψ`, which
is `-i/2`. Numerically, `Ψ + Ψ'` vanishes on this lift and `Ψ - Ψ'` does not: the Casimir equations
seem to be the Hodge harmonicity together with closedness, as for the cuspidal forms of the
knowl, whose harmonic 1-forms are closed (not proved here). The 1-form `x₂ dx₁` is not invariant
under any lattice of translations of `ℂ`, so it only shows that the two conditions differ for
functions on `ℋ₃`; whether they agree for `Γ`-invariant forms of moderate growth is not decided
here.

## Main definitions

* `HyperbolicThreeSpace.nonClosedHarmonicFunction`: the function
  `F(x, y) = (-y x₂ / 2, 0, y x₂ / 2)` of the 1-form `x₂ dx₁`.

## Main results

* `HyperbolicThreeSpace.isHarmonicOneForm_nonClosedHarmonicFunction`: `x₂ dx₁` is harmonic.
* `HyperbolicThreeSpace.not_isBianchiHarmonic_nonClosedHarmonicFunction`: the Casimir equations
  fail for `y⁻¹ F`.
* `HyperbolicThreeSpace.not_forall_isHarmonicOneForm_iff_isBianchiHarmonic`: the harmonicity of
  `F₁β₁ + F₂β₂ + F₃β₃` is not equivalent to `IsBianchiHarmonic 2` for `y⁻¹ F`.
-/

open Complex Matrix

open scoped ComplexConjugate MatrixGroups

namespace Complex

variable {n : WithTop ℕ∞}

@[fun_prop]
lemma contDiff_conj : ContDiff ℝ n fun z : ℂ ↦ conj z :=
  conjCLE.contDiff

@[fun_prop]
lemma contDiff_ofReal : ContDiff ℝ n fun x : ℝ ↦ (x : ℂ) :=
  ofRealCLM.contDiff

@[fun_prop]
lemma contDiff_re : ContDiff ℝ n fun z : ℂ ↦ z.re :=
  reCLM.contDiff

@[fun_prop]
lemma contDiff_im : ContDiff ℝ n fun z : ℂ ↦ z.im :=
  imCLM.contDiff

@[fun_prop]
lemma contDiff_normSq : ContDiff ℝ n fun z : ℂ ↦ normSq z := by
  simpa [normSq_eq_norm_sq] using contDiff_norm_sq ℝ (E := ℂ) (n := n)

end Complex

namespace HyperbolicThreeSpace

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] (b b' : Fin 3) (w : ℂ) (L : V →L[ℂ] W) {Φ : SL(2, ℂ) → V}
  {f₁ f₂ : SL(2, ℂ) → ℂ}

lemma lieDeriv_clm_comp (h : IsLieDifferentiable Φ) : lieDeriv b w (L ∘ Φ) = L ∘ lieDeriv b w Φ :=
  funext fun g ↦ ((L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (h g b w).hasDerivAt).deriv

lemma lieDerivOne_clm_comp (h : IsLieDifferentiable Φ) :
    lieDerivOne b (L ∘ Φ) = L ∘ lieDerivOne b Φ := by
  funext g
  simp [lieDerivOne, lieDeriv_clm_comp _ _ L h]

lemma casimirOne_clm_comp (h : IsLieSmooth Φ) : casimirOne (L ∘ Φ) = L ∘ casimirOne Φ := by
  have h₁ (b : Fin 3) : lieDerivOne b (L ∘ Φ) = L ∘ lieDerivOne b Φ :=
    lieDerivOne_clm_comp b L h.isLieDifferentiable
  have h₂ (b b' : Fin 3) :
      lieDerivOne b (L ∘ lieDerivOne b' Φ) = L ∘ lieDerivOne b (lieDerivOne b' Φ) :=
    lieDerivOne_clm_comp b L (h.isLieDifferentiable_lieDerivOne b')
  funext g
  simp [casimirOne, h₁, h₂]

lemma IsLieDifferentiable.mul (h₁ : IsLieDifferentiable f₁) (h₂ : IsLieDifferentiable f₂) :
    IsLieDifferentiable (f₁ * f₂) :=
  fun g b w ↦ (h₁ g b w).mul (h₂ g b w)

lemma lieDeriv_mul (h₁ : IsLieDifferentiable f₁) (h₂ : IsLieDifferentiable f₂) :
    lieDeriv b w (f₁ * f₂) = lieDeriv b w f₁ * f₂ + f₁ * lieDeriv b w f₂ := by
  funext g
  have h : HasDerivAt (fun t : ℝ ↦ f₁ (g * sl2Exp b (t * w)) * f₂ (g * sl2Exp b (t * w)))
      (lieDeriv b w f₁ g * f₂ (g * sl2Exp b ((0 : ℝ) * w)) +
        f₁ (g * sl2Exp b ((0 : ℝ) * w)) * lieDeriv b w f₂ g) 0 :=
    (h₁ g b w).hasDerivAt.mul (h₂ g b w).hasDerivAt
  rw [ofReal_zero, zero_mul, sl2Exp_zero, mul_one] at h
  exact h.deriv

lemma lieDerivOne_mul (h₁ : IsLieDifferentiable f₁) (h₂ : IsLieDifferentiable f₂) :
    lieDerivOne b (f₁ * f₂) = lieDerivOne b f₁ * f₂ + f₁ * lieDerivOne b f₂ := by
  funext g
  simp [lieDerivOne, lieDeriv_mul _ _ h₁ h₂]
  ring1

lemma lieDerivOne_lieDerivOne_mul (h₁ : IsLieSmooth f₁) (h₂ : IsLieSmooth f₂) :
    lieDerivOne b (lieDerivOne b' (f₁ * f₂)) = lieDerivOne b (lieDerivOne b' f₁) * f₂ +
      lieDerivOne b' f₁ * lieDerivOne b f₂ +
        (lieDerivOne b f₁ * lieDerivOne b' f₂ + f₁ * lieDerivOne b (lieDerivOne b' f₂)) := by
  rw [lieDerivOne_mul b' h₁.isLieDifferentiable h₂.isLieDifferentiable,
    lieDerivOne_add b ((h₁.isLieDifferentiable_lieDerivOne b').mul h₂.isLieDifferentiable)
      (h₁.isLieDifferentiable.mul (h₂.isLieDifferentiable_lieDerivOne b')),
    lieDerivOne_mul b (h₁.isLieDifferentiable_lieDerivOne b') h₂.isLieDifferentiable,
    lieDerivOne_mul b h₁.isLieDifferentiable (h₂.isLieDifferentiable_lieDerivOne b')]

lemma lieDerivOne_lieDerivOne_mul_of_eq_zero (h₁ : IsLieSmooth f₁) (h₂ : IsLieSmooth f₂)
    {g : SL(2, ℂ)} (hf₁ : f₁ g = 0) (hf₂ : f₂ g = 0) :
    lieDerivOne b (lieDerivOne b' (f₁ * f₂)) g =
      lieDerivOne b' f₁ g * lieDerivOne b f₂ g + lieDerivOne b f₁ g * lieDerivOne b' f₂ g := by
  rw [lieDerivOne_lieDerivOne_mul b b' h₁ h₂]
  simp [hf₁, hf₂]

private lemma contDiff_sl2Exp_apply' (i j : Fin 2) :
    ContDiff ℝ 2 fun s : ℝ ↦ (sl2Exp b (s * w) : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  fin_cases b <;> fin_cases i <;> fin_cases j <;> simp [sl2Exp] <;> fun_prop

private lemma contDiff_mul_apply' {γ₁ γ₂ : ℝ × ℝ → SL(2, ℂ)}
    (h₁ : ∀ i j, ContDiff ℝ 2 fun st ↦ (γ₁ st : Matrix (Fin 2) (Fin 2) ℂ) i j)
    (h₂ : ∀ i j, ContDiff ℝ 2 fun st ↦ (γ₂ st : Matrix (Fin 2) (Fin 2) ℂ) i j) (i j : Fin 2) :
    ContDiff ℝ 2 fun st ↦ ((γ₁ st * γ₂ st : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  simp only [SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two]
  exact ((h₁ i 0).mul (h₂ 0 j)).add ((h₁ i 1).mul (h₂ 1 j))

lemma isLieSmooth_of_contDiff (h : ∀ γ : ℝ × ℝ → SL(2, ℂ),
    (∀ i j, ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) i j) → ContDiff ℝ 2 (Φ ∘ γ)) :
    IsLieSmooth Φ :=
  fun _ b₁ w₁ b₂ w₂ ↦ h _ <| contDiff_mul_apply' (contDiff_mul_apply' (fun _ _ ↦ contDiff_const)
    fun i j ↦ (contDiff_sl2Exp_apply' b₁ w₁ i j).comp contDiff_fst)
      fun i j ↦ (contDiff_sl2Exp_apply' b₂ w₂ i j).comp contDiff_snd

/-- `Im(a c̄ + b d̄)` for `g = (a, b; c, d)`. -/
private noncomputable def topIm (g : SL(2, ℂ)) : ℂ :=
  ((g 0 0 * conj (g 1 0) + g 0 1 * conj (g 1 1)).im : ℂ)

/-- `Re(c d) / (|c|² + |d|²)³` for `g = (a, b; c, d)`. -/
private noncomputable def bottomRe (g : SL(2, ℂ)) : ℂ :=
  ((g 1 0 * g 1 1).re / (normSq (g 1 0) + normSq (g 1 1)) ^ 3 : ℝ)

private lemma normSq_add_normSq_pos (g : SL(2, ℂ)) : 0 < normSq (g 1 0) + normSq (g 1 1) := by
  simpa [moebiusDenom, add_comm] using moebiusDenom_pos g (p := (0, 1)) one_pos

private lemma isLieSmooth_topIm : IsLieSmooth topIm :=
  isLieSmooth_of_contDiff fun γ hγ ↦ by
    have h₀₀ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := hγ 0 0
    have h₀₁ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := hγ 0 1
    have h₁₀ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := hγ 1 0
    have h₁₁ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := hγ 1 1
    simp only [Function.comp_def, topIm]
    fun_prop

private lemma isLieSmooth_bottomRe : IsLieSmooth bottomRe :=
  isLieSmooth_of_contDiff fun γ hγ ↦ by
    have h₁₀ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := hγ 1 0
    have h₁₁ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := hγ 1 1
    have hN (st : ℝ × ℝ) : (normSq (γ st 1 0) + normSq (γ st 1 1)) ^ 3 ≠ 0 :=
      pow_ne_zero 3 (normSq_add_normSq_pos (γ st)).ne'
    simp only [Function.comp_def, bottomRe]
    fun_prop (disch := exact hN _)

private lemma lieDeriv_topIm_one : lieDeriv 1 w topIm 1 = w.im := by
  have e : (fun t : ℝ ↦ topIm (1 * sl2Exp 1 (t * w))) = fun t ↦ ((t * w.im : ℝ) : ℂ) := by
    funext t
    simp only [one_mul]
    simp [topIm, sl2Exp]
  rw [lieDeriv, e]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w.im).ofReal_comp.deriv

private lemma lieDeriv_bottomRe_zero : lieDeriv 0 w bottomRe 1 = 0 := by
  simp only [lieDeriv, one_mul]
  simp [bottomRe, sl2Exp]

private lemma lieDeriv_bottomRe_one : lieDeriv 1 w bottomRe 1 = 0 := by
  simp only [lieDeriv, one_mul]
  simp [bottomRe, sl2Exp]

private lemma lieDeriv_bottomRe_two : lieDeriv 2 w bottomRe 1 = w.re := by
  have e : (fun t : ℝ ↦ bottomRe (1 * sl2Exp 2 (t * w))) =
      fun t ↦ ((t * w.re / (t ^ 2 * normSq w + 1) ^ 3 : ℝ) : ℂ) := by
    funext t
    simp only [one_mul]
    simp [bottomRe, sl2Exp]
    ring1
  rw [lieDeriv, e]
  simpa using (((hasDerivAt_id (0 : ℝ)).mul_const w.re).div
    ((((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (normSq w)).add_const 1 |>.pow 3)
      (by norm_num)).ofReal_comp.deriv

private lemma casimirOne_topIm_mul_bottomRe : casimirOne (topIm * bottomRe) 1 = -I / 2 := by
  have h₁ : topIm 1 = 0 := by
    simp [topIm]
  have h₂ : bottomRe 1 = 0 := by
    simp [bottomRe]
  simp only [casimirOne, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    lieDerivOne_lieDerivOne_mul_of_eq_zero _ _ isLieSmooth_topIm isLieSmooth_bottomRe h₁ h₂]
  simp [lieDerivOne, lieDeriv_topIm_one, lieDeriv_bottomRe_zero, lieDeriv_bottomRe_one,
    lieDeriv_bottomRe_two]
  ring1

/-- The function `F(x, y) = (-y x₂ / 2, 0, y x₂ / 2)`, `x = x₁ + i x₂`, on `ℂ × ℝ`, whose 1-form
`F₁β₁ + F₂β₂ + F₃β₃` (`weightTwoOneForm`) is `x₂ dx₁` on `ℋ₃`: a harmonic 1-form which is not
closed, and a counterexample to the equivalence of its harmonicity with the Casimir equations of
`y⁻¹ F`. -/
noncomputable def nonClosedHarmonicFunction (p : ℂ × ℝ) : Fin 3 → ℂ :=
  ![-((p.2 : ℂ) * p.1.im) / 2, 0, (p.2 : ℂ) * p.1.im / 2]

private lemma proj_comp_bianchiLift : (ContinuousLinearMap.proj 1 : (Fin 3 → ℂ) →L[ℂ] ℂ) ∘
    bianchiLift 2 (fun z ↦ (z.coords.2 : ℂ)⁻¹ • nonClosedHarmonicFunction z.coords) =
      topIm * bottomRe := by
  funext g
  have hN : ((normSq (g 1 0) + normSq (g 1 1) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (normSq_add_normSq_pos g).ne'
  have hpos : 0 < (moebius g (0, 1)).2 := moebius_snd_pos g one_pos
  have hD : moebiusDenom g (0, 1) = normSq (g 1 0) + normSq (g 1 1) := by
    simp [moebiusDenom, add_comm]
  have h₂ : ((moebius g (0, 1)).2 : ℂ) = ((normSq (g 1 0) + normSq (g 1 1) : ℝ) : ℂ)⁻¹ := by
    simp [moebius, hD]
  have h₁ : ((moebius g (0, 1)).1.im : ℂ) = ((g 0 0 * conj (g 1 0) + g 0 1 * conj (g 1 1)).im : ℂ) /
      ((normSq (g 1 0) + normSq (g 1 1) : ℝ) : ℂ) := by
    simp only [moebius, hD, div_ofReal_im, mul_zero, zero_add, one_pow, ofReal_one, mul_one, add_im]
    push_cast
    ring1
  simp only [Function.comp_apply, ContinuousLinearMap.proj_apply, Pi.mul_apply]
  rw [bianchiLift_apply, extend_inv_smul _ hpos, inv_automorphyFactor, hD]
  simp only [nonClosedHarmonicFunction, h₁, h₂, topIm, bottomRe]
  simp only [ofReal_div, im_eq_sub_conj, re_eq_add_conj]
  simp [symPowMatrix, mulVec, dotProduct, Fin.sum_univ_three, Finset.sum_range_succ]
  field_simp
  ring1

@[fun_prop]
private lemma analyticAt_im' (z : ℂ) : AnalyticAt ℝ (fun z : ℂ ↦ z.im) z :=
  imCLM.analyticAt z

lemma analyticAt_nonClosedHarmonicFunction (p : ℂ × ℝ) :
    AnalyticAt ℝ nonClosedHarmonicFunction p := by
  refine analyticAt_pi_iff.mpr fun i ↦ ?_
  fin_cases i <;> simp [nonClosedHarmonicFunction] <;> fun_prop

/-- **The Casimir equations fail for the function of the harmonic 1-form `x₂ dx₁`**: for
`F = nonClosedHarmonicFunction`, `y⁻¹ F` is not harmonic in the sense of the Casimir operators
(`IsBianchiHarmonic 2`, LMFDB `mf.bianchi`): the first Casimir operator `Ψ` takes the value `-i/2`
at the identity on the middle coordinate of the lift of `y⁻¹ F`, which vanishes there. -/
lemma not_isBianchiHarmonic_nonClosedHarmonicFunction :
    ¬IsBianchiHarmonic 2 fun z ↦ (z.coords.2 : ℂ)⁻¹ • nonClosedHarmonicFunction z.coords := by
  intro h
  have hS : IsLieSmooth
      (bianchiLift 2 fun z ↦ (z.coords.2 : ℂ)⁻¹ • nonClosedHarmonicFunction z.coords) :=
    isLieSmooth_bianchiLift <| analyticAt_iff_analyticAt_extend_inv_smul.mp fun p _ ↦
      analyticAt_nonClosedHarmonicFunction p
  have h₁ : casimirOne (topIm * bottomRe) 1 = 0 := by
    rw [← proj_comp_bianchiLift, casimirOne_clm_comp _ hS, Function.comp_apply, h.1]
    norm_num [harmonicEigenvalue]
  norm_num [casimirOne_topIm_mul_bottomRe] at h₁

private lemma eventuallyEq_weightTwoOneForm {q : ℂ × ℝ} (hq : 0 < q.2) :
    (weightTwoOneForm · nonClosedHarmonicFunction) =ᶠ[nhds q] fun r ↦ ![(r.1.im : ℂ), 0, 0] := by
  filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hq] with r hr
  have hy : (r.2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  ext i
  fin_cases i
  · simp [weightTwoOneForm, nonClosedHarmonicFunction]
    field_simp
    ring1
  · simp only [weightTwoOneForm, nonClosedHarmonicFunction]
    simp
    exact Or.inr (by ring1)
  · simp [weightTwoOneForm, nonClosedHarmonicFunction]

private lemma coordDeriv_eq_deriv {f : ℂ × ℝ → ℂ} {q : ℂ × ℝ} (hf : DifferentiableAt ℝ f q)
    (i : Fin 3) : coordDeriv q i f = deriv (fun t : ℝ ↦ f (q + t • coordVector i)) 0 := by
  have hl : HasDerivAt (fun t : ℝ ↦ q + t • coordVector i) (coordVector i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordVector i)).const_add q
  exact (hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)).deriv.symm

private lemma oneFormCodiff_nonClosedHarmonicFunction {q : ℂ × ℝ} (hq : 0 < q.2) :
    oneFormCodiff (weightTwoOneForm · nonClosedHarmonicFunction) q = 0 := by
  have hy : (q.2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq.ne'
  have h (i : Fin 3) : coordDeriv q i
      (fun r ↦ (r.2 : ℂ)⁻¹ * weightTwoOneForm r nonClosedHarmonicFunction i) = 0 := by
    have he : (fun r ↦ (r.2 : ℂ)⁻¹ * weightTwoOneForm r nonClosedHarmonicFunction i) =ᶠ[nhds q]
        fun r ↦ (r.2 : ℂ)⁻¹ * ![(r.1.im : ℂ), 0, 0] i :=
      (eventuallyEq_weightTwoOneForm hq).mono fun r hr ↦ by
        simp only at hr ⊢
        rw [hr]
    have hd : DifferentiableAt ℝ (fun r : ℂ × ℝ ↦ (r.2 : ℂ)⁻¹ * ![(r.1.im : ℂ), 0, 0] i) q := by
      fin_cases i <;> simp
      fun_prop (disch := exact hy)
    rw [coordDeriv, he.fderiv_eq, ← coordDeriv, coordDeriv_eq_deriv hd]
    fin_cases i <;> simp [coordVector]
  simp [oneFormCodiff, h]

private lemma coordDeriv_congr {f f' : ℂ × ℝ → ℂ} {q : ℂ × ℝ} (h : f =ᶠ[nhds q] f') (i : Fin 3) :
    coordDeriv q i f = coordDeriv q i f' := by
  rw [coordDeriv, coordDeriv, h.fderiv_eq]

private lemma deriv_ofReal_snd_mul (q v : ℂ × ℝ) (c : ℂ) :
    deriv (fun t : ℝ ↦ ((q + t • v).2 : ℂ) * c) 0 = (v.2 : ℂ) * c := by
  simpa using
    ((((hasDerivAt_id (0 : ℝ)).mul_const v.2).const_add q.2).ofReal_comp.mul_const c).deriv

private lemma deriv_ofReal_fst_im (q v : ℂ × ℝ) :
    deriv (fun t : ℝ ↦ ((q + t • v).1.im : ℂ)) 0 = (v.1.im : ℂ) := by
  simpa using (((hasDerivAt_id (0 : ℝ)).mul_const v.1.im).const_add q.1.im).ofReal_comp.deriv

private lemma coordDeriv_imVector (q : ℂ × ℝ) (i j : Fin 3) :
    coordDeriv q i (fun r ↦ ![(r.1.im : ℂ), 0, 0] j) = ![((coordVector i).1.im : ℂ), 0, 0] j := by
  have hd : DifferentiableAt ℝ (fun r : ℂ × ℝ ↦ ![(r.1.im : ℂ), 0, 0] j) q := by
    fin_cases j <;> simp
    fun_prop
  rw [coordDeriv_eq_deriv hd]
  fin_cases j
  · exact deriv_ofReal_fst_im q (coordVector i)
  · simp
  · simp

private lemma oneFormExtDeriv_nonClosedHarmonicFunction {q : ℂ × ℝ} (hq : 0 < q.2) (i j : Fin 3) :
    oneFormExtDeriv (weightTwoOneForm · nonClosedHarmonicFunction) q i j =
      ![((coordVector i).1.im : ℂ), 0, 0] j - ![((coordVector j).1.im : ℂ), 0, 0] i := by
  have he (k : Fin 3) : (fun r ↦ weightTwoOneForm r nonClosedHarmonicFunction k) =ᶠ[nhds q]
      fun r ↦ ![(r.1.im : ℂ), 0, 0] k :=
    (eventuallyEq_weightTwoOneForm hq).mono fun r hr ↦ by
      simp only at hr ⊢
      rw [hr]
  rw [oneFormExtDeriv, coordDeriv_congr (he j), coordDeriv_congr (he i), coordDeriv_imVector,
    coordDeriv_imVector]

/-- **The 1-form `x₂ dx₁` is harmonic** (LMFDB `mf.bianchi.weight2`): the 1-form
`F₁β₁ + F₂β₂ + F₃β₃` of `F = nonClosedHarmonicFunction` is `x₂ dx₁` on `ℋ₃`, whose codifferential
vanishes and whose exterior derivative `dx₂ ∧ dx₁` is co-closed, so that its Hodge Laplacian
`dδ + δd` vanishes, although it is not closed. -/
lemma isHarmonicOneForm_nonClosedHarmonicFunction :
    IsHarmonicOneForm (weightTwoOneForm · nonClosedHarmonicFunction) := by
  intro p hp
  funext j
  have hU : ∀ᶠ q in nhds p, 0 < q.2 := (isOpen_lt continuous_const continuous_snd).mem_nhds hp
  have h₁ : coordDeriv p j (oneFormCodiff (weightTwoOneForm · nonClosedHarmonicFunction)) = 0 := by
    rw [coordDeriv_congr (hU.mono fun q hq ↦ oneFormCodiff_nonClosedHarmonicFunction hq) j]
    simp [coordDeriv]
  have h₂ (i : Fin 3) : coordDeriv p i (fun q ↦ (q.2 : ℂ) *
      oneFormExtDeriv (weightTwoOneForm · nonClosedHarmonicFunction) q i j) =
        ((coordVector i).2 : ℂ) *
          (![((coordVector i).1.im : ℂ), 0, 0] j - ![((coordVector j).1.im : ℂ), 0, 0] i) := by
    rw [coordDeriv_congr (hU.mono fun q hq ↦ by
      rw [oneFormExtDeriv_nonClosedHarmonicFunction hq]), coordDeriv_eq_deriv (by fun_prop),
      deriv_ofReal_snd_mul]
  simp only [hodgeLaplacianOneForm, twoFormCodiff, h₁, h₂, Fin.sum_univ_three]
  fin_cases j <;> simp [coordVector]

lemma oneFormExtDeriv_nonClosedHarmonicFunction_ne_zero {p : ℂ × ℝ} (hp : 0 < p.2) :
    oneFormExtDeriv (weightTwoOneForm · nonClosedHarmonicFunction) p 1 0 ≠ 0 := by
  simp [oneFormExtDeriv_nonClosedHarmonicFunction hp, coordVector]

/-- **Hodge harmonicity of `F₁β₁ + F₂β₂ + F₃β₃` is not equivalent to the Casimir equations of
`y⁻¹ F`** (LMFDB `mf.bianchi.weight2`, `mf.bianchi`): for the real analytic function
`F = nonClosedHarmonicFunction`, whose 1-form `x₂ dx₁` is harmonic, `y⁻¹ F` is not harmonic in the
sense of `IsBianchiHarmonic 2`. So the hypothesis of
`isBianchiWeightTwoForm_iff_isBianchiModularForm` does not hold for every real analytic `F`. -/
lemma not_forall_isHarmonicOneForm_iff_isBianchiHarmonic :
    ¬∀ F : ℂ × ℝ → Fin 3 → ℂ, (∀ p : ℂ × ℝ, 0 < p.2 → AnalyticAt ℝ F p) →
      (IsHarmonicOneForm (weightTwoOneForm · F) ↔
        IsBianchiHarmonic 2 fun z ↦ (z.coords.2 : ℂ)⁻¹ • F z.coords) :=
  fun h ↦ not_isBianchiHarmonic_nonClosedHarmonicFunction <|
    (h _ fun p _ ↦ analyticAt_nonClosedHarmonicFunction p).mp
      isHarmonicOneForm_nonClosedHarmonicFunction

end HyperbolicThreeSpace
