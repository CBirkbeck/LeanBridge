import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Fourier series of periodic holomorphic functions on a tube

Let `Ω ⊆ ℝ^d` be open and convex, and `g` a holomorphic function on the tube
`T = {z ∈ ℂ^d : Im z ∈ Ω}` with `g(z + m) = g(z)` for `m ∈ ℤ^d`. Then `g` is the sum of an
absolutely convergent Fourier series `g(z) = ∑_{k ∈ ℤ^d} c(k) e^{2πi k·z}` on `T`.

For `y ∈ Ω`, the coefficient of the Fourier series of `x ↦ g(x + iy)` on the torus `(ℝ / ℤ)^d` is
`c_y(k) = ∫ g(x + iy) e^{-2πi k·x} dx`. The integral
`c_y(k) e^{2π k·y} = ∫ g(x + iy) e^{-2πi k·(x + iy)} dx` does not depend on `y`: the integral
`Ψ(w) = ∫ G(x + i(y + w(y' - y))) dx` of a holomorphic function `G` is holomorphic in `w`, it is
constant on the imaginary axis by the invariance of the measure of the torus, and so it is constant
on its connected domain. As `|c_y(k)|` is bounded by the supremum of `|g(x + iy)|`, moving `y` by
`ε` in the direction of `-sign(k)` gives `|c(k) e^{2πi k·z}| ≤ C e^{-2πε ∑ |kᵢ|}`, so the series
converges absolutely, and its sum is `g` by Fourier inversion on the torus.

## Main definitions

* `tubeOver`: the tube `{z ∈ ℂ^d : Im z ∈ Ω}`.
* `tubeFourierCoeff`: the Fourier coefficient `∫ g(x + iy) e^{-2πi k·(x + iy)} dx`.

## Main results

* `differentiableOn_integral_of_continuousAt`: an integral over a compact space of functions
  depending holomorphically and jointly continuously on a parameter is holomorphic.
* `tubeFourierCoeff_eq`: the coefficient does not depend on `y`.
* `tubeFourierCoeff_eq_cexp_mul`: the coefficients under a real period.
* `hasSum_tubeFourierCoeff_mul_cexp`: `g` is the sum of its Fourier series.
-/

open Complex Filter Function MeasureTheory Metric Set UnitAddTorus

open scoped Real Topology

private noncomputable local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

private local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

private local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- **An integral depending holomorphically on a parameter is holomorphic**: if `X` is compact with
a finite measure, `Φ` is jointly continuous and holomorphic in the second variable on the open set
`U`, then `w ↦ ∫ Φ(x, w) dμ(x)` is holomorphic on `U`. The derivatives are dominated through the
Cauchy estimates. -/
lemma differentiableOn_integral_of_continuousAt {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {U : Set ℂ}
    {Φ : X → ℂ → ℂ} (hU : IsOpen U) (hc : ∀ x, ∀ w ∈ U, ContinuousAt (uncurry Φ) (x, w))
    (hd : ∀ x, DifferentiableOn ℂ (Φ x) U) : DifferentiableOn ℂ (fun w ↦ ∫ x, Φ x w ∂μ) U := by
  intro w₀ hw₀
  have hU' : U ∈ 𝓝 w₀ := hU.mem_nhds hw₀
  rcases nhds_basis_closedBall.mem_iff.mp hU' with ⟨r, hr, hsub⟩
  have hε : 0 < r / 2 := half_pos hr
  have hK : IsCompact ((univ : Set X) ×ˢ closedBall w₀ r) :=
    isCompact_univ.prod (isCompact_closedBall w₀ r)
  have hcont : ContinuousOn (uncurry Φ) ((univ : Set X) ×ˢ closedBall w₀ r) := fun p hp ↦
    (hc p.1 p.2 (hsub hp.2)).continuousWithinAt
  rcases hK.exists_bound_of_continuousOn hcont with ⟨M, hM⟩
  have hball : ball w₀ (r / 2) ⊆ U := (ball_subset_closedBall.trans (closedBall_subset_closedBall
    (by linarith))).trans hsub
  have hcont₁ {w : ℂ} (hw : w ∈ U) : Continuous fun x ↦ Φ x w :=
    continuous_iff_continuousAt.mpr fun x ↦ ContinuousAt.comp (f := fun y ↦ (y, w)) (hc x w hw)
      (continuousAt_id.prodMk continuousAt_const)
  have hF_meas : ∀ᶠ w in 𝓝 w₀, AEStronglyMeasurable (fun x ↦ Φ x w) μ :=
    eventually_of_mem hU' fun w hw ↦ (hcont₁ hw).aestronglyMeasurable
  have hF_int : Integrable (fun x ↦ Φ x w₀) μ :=
    Integrable.of_bound (hcont₁ hw₀).aestronglyMeasurable M <| ae_of_all _ fun x ↦
      hM (x, w₀) ⟨mem_univ _, mem_closedBall_self hr.le⟩
  have hder (x : X) {w : ℂ} (hw : w ∈ U) : HasDerivAt (Φ x) (deriv (Φ x) w) w :=
    ((hd x).differentiableAt (hU.mem_nhds hw)).hasDerivAt
  have hF'_meas : AEStronglyMeasurable (fun x ↦ deriv (Φ x) w₀) μ := by
    have hseq : Tendsto (fun n : ℕ ↦ w₀ + ((r / 2 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝[≠] w₀) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
      · have h : Tendsto (fun n : ℕ ↦ (r / 2 / ((n : ℝ) + 2) : ℝ)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop
            (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
        simpa using tendsto_const_nhds.add (continuous_ofReal.tendsto' 0 0 ofReal_zero |>.comp h)
      · have h₀ : (r / 2 / ((n : ℝ) + 2) : ℝ) ≠ 0 := by positivity
        exact add_ne_left.mpr (ofReal_ne_zero.mpr h₀)
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun (n : ℕ) x ↦
      slope (Φ x) w₀ (w₀ + ((r / 2 / ((n : ℝ) + 2) : ℝ) : ℂ))) (fun n ↦ ?_)
        (ae_of_all _ fun x ↦ (hder x hw₀).tendsto_slope.comp hseq)
    have hmem : w₀ + ((r / 2 / ((n : ℝ) + 2) : ℝ) : ℂ) ∈ U := by
      refine hball ?_
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real,
        Real.norm_of_nonneg (by positivity)]
      exact div_lt_self hε (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    simp only [slope_def_field]
    exact (((hcont₁ hmem).sub (hcont₁ hw₀)).div_const _).aestronglyMeasurable
  have h_bound : ∀ᵐ x ∂μ, ∀ w ∈ ball w₀ (r / 2), ‖deriv (Φ x) w‖ ≤ M / (r / 2) :=
    ae_of_all _ fun x w hw ↦ by
      have hsph : closedBall w (r / 2) ⊆ closedBall w₀ r := closedBall_subset_closedBall' <| by
        have h : dist w w₀ < r / 2 := hw
        linarith
      exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε
        ((hd x).diffContOnCl_ball (hsph.trans hsub)) fun z hz ↦
          hM (x, z) ⟨mem_univ _, hsph (sphere_subset_closedBall hz)⟩
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F' := fun w x ↦ deriv (Φ x) w)
    (ball_mem_nhds w₀ hε) hF_meas hF_int hF'_meas h_bound (integrable_const _)
    (ae_of_all _ fun x w hw ↦ hder x (hball hw))).2.differentiableAt.differentiableWithinAt

variable {d : Type*} {Ω : Set (d → ℝ)} {g : (d → ℂ) → ℂ} {y y' : d → ℝ} (t : UnitAddTorus d)
    (x : d → ℝ)

variable (Ω) in
/-- The **tube** `{z ∈ ℂ^d : Im z ∈ Ω}` over a subset `Ω` of `ℝ^d`. -/
def tubeOver : Set (d → ℂ) :=
  {z | (fun i ↦ (z i).im) ∈ Ω}

lemma mem_tubeOver {z : d → ℂ} : z ∈ tubeOver Ω ↔ (fun i ↦ (z i).im) ∈ Ω :=
  Iff.rfl

lemma isOpen_tubeOver (hΩ : IsOpen Ω) : IsOpen (tubeOver Ω) :=
  hΩ.preimage (by fun_prop)

/-- The representative in `ℝ^d` of a point of the torus `(ℝ / ℤ)^d`. -/
private noncomputable def torusRep : d → ℝ :=
  fun i ↦ (t i).out

private lemma coe_torusRep : (fun i ↦ (torusRep t i : UnitAddCircle)) = t :=
  funext fun i ↦ QuotientAddGroup.out_eq' (t i)

private lemma exists_torusRep_coe :
    ∃ m : d → ℤ, torusRep (fun i ↦ (x i : UnitAddCircle)) = fun i ↦ x i + m i := by
  have h (i : d) : ∃ m : ℤ, ((x i : UnitAddCircle)).out = x i + m := by
    rcases QuotientAddGroup.mk_out_eq_add (AddSubgroup.zmultiples (1 : ℝ)) (x i) with
      ⟨⟨_, n, rfl⟩, hn⟩
    exact ⟨n, by simpa using hn⟩
  choose m hm using h
  exact ⟨m, funext hm⟩

/-- The projection `ℝ^d → (ℝ / ℤ)^d`. -/
private def torusMk : UnitAddTorus d :=
  fun i ↦ (x i : UnitAddCircle)

private lemma isOpenQuotientMap_torusMk : IsOpenQuotientMap (torusMk (d := d)) :=
  IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk

/-- The point `x + u` of `ℂ^d`, for a point `t` of the torus with representative `x`. -/
private noncomputable def torusPt (u : d → ℂ) : d → ℂ :=
  fun i ↦ (torusRep t i : ℂ) + u i

private lemma apply_torusPt_coe (hper : ∀ (m : d → ℤ) z, g (fun i ↦ z i + m i) = g z) (u : d → ℂ) :
    g (torusPt (torusMk x) u) = g fun i ↦ (x i : ℂ) + u i := by
  rcases exists_torusRep_coe x with ⟨m, hm⟩
  have h : torusPt (torusMk x) u = fun i ↦ ((x i : ℂ) + u i) + m i := by
    funext i
    have e : torusRep (torusMk x) i = x i + m i := congrFun hm i
    rw [torusPt, e]
    push_cast
    ring1
  rw [h, hper]

variable (y) in
/-- The vector `iy` of `ℂ^d`. -/
private def iVec : d → ℂ :=
  fun i ↦ I * y i

variable (Ω y y') in
/-- The real line in the direction `y' - y` inside `Ω` gives an open convex set of parameters. -/
private def segmentParam : Set ℂ :=
  {w | (fun i ↦ y i + w.re * (y' i - y i)) ∈ Ω}

private lemma isOpen_segmentParam (hΩo : IsOpen Ω) : IsOpen (segmentParam Ω y y') :=
  hΩo.preimage (by fun_prop)

private lemma isPreconnected_segmentParam (hΩc : Convex ℝ Ω) :
    IsPreconnected (segmentParam Ω y y') := by
  refine Convex.isPreconnected fun w₁ hw₁ w₂ hw₂ a b ha hb hab ↦ ?_
  have h :
      (a • fun i ↦ y i + w₁.re * (y' i - y i)) + (b • fun i ↦ y i + w₂.re * (y' i - y i)) ∈ Ω :=
    hΩc hw₁ hw₂ ha hb hab
  have e : (a • fun i ↦ y i + w₁.re * (y' i - y i)) + (b • fun i ↦ y i + w₂.re * (y' i - y i)) =
      fun i ↦ y i + (a • w₁ + b • w₂).re * (y' i - y i) := by
    funext i
    have hb' : b = 1 - a := by linarith
    subst hb'
    simp
    ring1
  rwa [e] at h

private lemma torusPt_mem_tubeOver {w : ℂ} (hw : w ∈ segmentParam Ω y y') :
    torusPt t (fun i ↦ I * y i + w * (I * (y' i - y i))) ∈ tubeOver Ω := by
  have e : (fun i ↦ (torusPt t (fun i ↦ I * y i + w * (I * (y' i - y i))) i).im) =
      fun i ↦ y i + w.re * (y' i - y i) := by
    funext i
    simp [torusPt]
  rw [tubeOver, mem_ofPred_eq, e]
  exact hw

private lemma continuousAt_torusPt (hΩo : IsOpen Ω) (hg : DifferentiableOn ℂ g (tubeOver Ω))
    (hper : ∀ (m : d → ℤ) z, g (fun i ↦ z i + m i) = g z) {w : ℂ} (hw : w ∈ segmentParam Ω y y') :
    ContinuousAt (uncurry fun (t : UnitAddTorus d) (w : ℂ) ↦
      g (torusPt t fun i ↦ I * y i + w * (I * (y' i - y i)))) (t, w) := by
  rcases isOpenQuotientMap_torusMk.surjective t with ⟨x, rfl⟩
  refine ((isOpenQuotientMap_torusMk.prodMap IsOpenQuotientMap.id).continuousAt_comp_iff
    (x := (x, w))).mp ?_
  have e : (uncurry fun (t : UnitAddTorus d) (w : ℂ) ↦
      g (torusPt t fun i ↦ I * y i + w * (I * (y' i - y i)))) ∘ Prod.map torusMk id =
        fun p : (d → ℝ) × ℂ ↦ g fun i ↦ (p.1 i : ℂ) + (I * y i + p.2 * (I * (y' i - y i))) :=
    funext fun p ↦ apply_torusPt_coe p.1 hper _
  rw [e]
  have hmem : (fun i ↦ (x i : ℂ) + (I * y i + w * (I * (y' i - y i)))) ∈ tubeOver Ω := by
    have e₁ : (fun i ↦ ((x i : ℂ) + (I * y i + w * (I * (y' i - y i)))).im) =
        fun i ↦ y i + w.re * (y' i - y i) := by
      funext i
      simp
    rw [tubeOver, mem_ofPred_eq, e₁]
    exact hw
  refine (hg.continuousOn.continuousAt ((isOpen_tubeOver hΩo).mem_nhds hmem)).comp ?_
  exact continuous_pi (fun i ↦ by fun_prop) |>.continuousAt

variable [Fintype d]

private lemma differentiableOn_torusPt (hg : DifferentiableOn ℂ g (tubeOver Ω)) : DifferentiableOn ℂ
    (fun w ↦ g (torusPt t fun i ↦ I * y i + w * (I * (y' i - y i)))) (segmentParam Ω y y') :=
  hg.comp (Differentiable.differentiableOn <| differentiable_pi.mpr fun i ↦ by
    simp only [torusPt]
    fun_prop) fun _ hw ↦ torusPt_mem_tubeOver t hw

private lemma integral_torusPt_mul_I (hper : ∀ (m : d → ℤ) z, g (fun i ↦ z i + m i) = g z) (r : ℝ) :
    ∫ t, g (torusPt t fun i ↦ I * y i + (r * I) * (I * (y' i - y i))) =
      ∫ t, g (torusPt t (iVec y)) := by
  rw [← integral_add_right_eq_self (fun t ↦ g (torusPt t (iVec y)))
    (torusMk fun i ↦ -(r * (y' i - y i)))]
  refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
  have e : t + torusMk (fun i ↦ -(r * (y' i - y i))) =
      torusMk fun i ↦ torusRep t i + -(r * (y' i - y i)) := by
    funext i
    conv_lhs => rw [← coe_torusRep t]
    simp [torusMk]
  beta_reduce
  rw [e, apply_torusPt_coe _ hper]
  congr 1
  funext i
  have hI : I * I = -1 := I_mul_I
  simp only [torusPt, iVec]
  push_cast
  linear_combination (r * (y' i - y i) : ℂ) * hI

private lemma integral_torusPt_eq (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hg : DifferentiableOn ℂ g (tubeOver Ω)) (hper : ∀ (m : d → ℤ) z, g (fun i ↦ z i + m i) = g z)
    (hy : y ∈ Ω) (hy' : y' ∈ Ω) : ∫ t : UnitAddTorus d, g (torusPt t (iVec y)) =
      ∫ t : UnitAddTorus d, g (torusPt t (iVec y')) := by
  have hS : IsOpen (segmentParam Ω y y') := isOpen_segmentParam hΩo
  have hΨ : DifferentiableOn ℂ (fun w ↦ ∫ t : UnitAddTorus d,
      g (torusPt t fun i ↦ I * y i + w * (I * (y' i - y i)))) (segmentParam Ω y y') :=
    differentiableOn_integral_of_continuousAt volume hS
      (fun t _ hw ↦ continuousAt_torusPt t hΩo hg hper hw) (differentiableOn_torusPt · hg)
  have h₀ : (0 : ℂ) ∈ segmentParam Ω y y' := by
    simpa [segmentParam] using hy
  have h₁ : (1 : ℂ) ∈ segmentParam Ω y y' := by
    simpa [segmentParam] using hy'
  have he₁ : (fun i ↦ I * y i + (1 : ℂ) * (I * (y' i - y i))) = iVec y' := by
    funext i
    simp only [iVec]
    ring1
  have hseq : Tendsto (fun n : ℕ ↦ ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
    · have h : Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (continuous_ofReal.tendsto' 0 0 ofReal_zero |>.comp h).mul_const I
    · have h₂ : (1 / ((n : ℝ) + 1) : ℝ) ≠ 0 := by positivity
      exact mul_ne_zero (ofReal_ne_zero.mpr h₂) I_ne_zero
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), (∫ t : UnitAddTorus d,
      g (torusPt t fun i ↦ I * y i + w * (I * (y' i - y i)))) =
        ∫ t : UnitAddTorus d, g (torusPt t (iVec y)) :=
    hseq.frequently (Frequently.of_forall fun n ↦ integral_torusPt_mul_I hper _)
  have h : (∫ t : UnitAddTorus d, g (torusPt t fun i ↦ I * y i + (1 : ℂ) * (I * (y' i - y i)))) =
      ∫ t : UnitAddTorus d, g (torusPt t (iVec y)) :=
    (hΨ.analyticOnNhd hS).eqOn_of_preconnected_of_frequently_eq
      analyticOnNhd_const (isPreconnected_segmentParam hΩc) h₀ hfreq h₁
  rw [← he₁]
  exact h.symm

variable (g y) in
/-- The **Fourier coefficient** `c(k) = ∫ g(x + iy) e^{-2πi k·(x + iy)} dx` over the torus
`(ℝ / ℤ)^d`, of a function `g` on a tube, at a height `y`. For a periodic holomorphic function it
does not depend on `y` (`tubeFourierCoeff_eq`). -/
noncomputable def tubeFourierCoeff (k : d → ℤ) : ℂ :=
  ∫ t : UnitAddTorus d, g (torusPt t (iVec y)) *
    cexp (-(2 * π * I * ∑ i, (k i : ℂ) * torusPt t (iVec y) i))

variable (k : d → ℤ)

private lemma cexp_sum_add_intCast (z : d → ℂ) (m : d → ℤ) :
    cexp (-(2 * π * I * ∑ i, (k i : ℂ) * (z i + m i))) =
      cexp (-(2 * π * I * ∑ i, (k i : ℂ) * z i)) := by
  have h : -(2 * π * I * ∑ i, (k i : ℂ) * (z i + m i)) = -(2 * π * I * ∑ i, (k i : ℂ) * z i) +
      ((-∑ i, k i * m i : ℤ) : ℂ) * (2 * π * I) := by
    push_cast
    simp only [mul_add, Finset.sum_add_distrib]
    ring1
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The Fourier coefficient does not depend on the height**: for `g` holomorphic on the tube over
an open convex `Ω`, periodic under `ℤ^d`, the integral `∫ g(x + iy) e^{-2πi k·(x + iy)} dx` is the
same for all `y ∈ Ω`. -/
lemma tubeFourierCoeff_eq (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hg : DifferentiableOn ℂ g (tubeOver Ω)) (hper : ∀ (m : d → ℤ) z, g (fun i ↦ z i + m i) = g z)
    (hy : y ∈ Ω) (hy' : y' ∈ Ω) : tubeFourierCoeff g y k = tubeFourierCoeff g y' k :=
  integral_torusPt_eq (g := fun z ↦ g z * cexp (-(2 * π * I * ∑ i, (k i : ℂ) * z i))) hΩo hΩc
    (hg.mul (Differentiable.differentiableOn <| by fun_prop)) (fun m z ↦ by
      rw [hper, cexp_sum_add_intCast]) hy hy'

/-- **The Fourier coefficients under a real period**: if `g(z + v) = g(z)` for a real vector `v`,
then `c(k) = e^{-2πi k·v} c(k)`, by the invariance of the measure of the torus. So `k·v ∈ ℤ` as soon
as `c(k) ≠ 0`. -/
lemma tubeFourierCoeff_eq_cexp_mul (hper : ∀ (m : d → ℤ) z, g (fun i ↦ z i + m i) = g z) (v : d → ℝ)
    (hv : ∀ z, g (fun i ↦ z i + v i) = g z) : tubeFourierCoeff g y k =
      cexp (-(2 * π * I * ∑ i, (k i : ℂ) * v i)) * tubeFourierCoeff g y k := by
  rw [tubeFourierCoeff, ← integral_const_mul]
  conv_lhs => rw [← integral_add_right_eq_self _ (torusMk v)]
  refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
  have e : t + torusMk v = torusMk fun i ↦ torusRep t i + v i := by
    funext i
    conv_lhs => rw [← coe_torusRep t]
    simp [torusMk]
  rcases exists_torusRep_coe (fun i ↦ torusRep t i + v i) with ⟨m, hm⟩
  have e₁ : torusPt (t + torusMk v) (iVec y) = fun i ↦ (torusPt t (iVec y) i + v i) + m i := by
    funext i
    have e₂ : torusRep (t + torusMk v) i = torusRep t i + v i + m i := by
      rw [e]
      exact congrFun hm i
    simp only [torusPt]
    rw [e₂]
    push_cast
    ring1
  beta_reduce
  rw [e₁, hper, hv, cexp_sum_add_intCast]
  have e₃ : -(2 * π * I * ∑ i, (k i : ℂ) * (torusPt t (iVec y) i + v i)) =
      -(2 * π * I * ∑ i, (k i : ℂ) * v i) +
        -(2 * π * I * ∑ i, (k i : ℂ) * torusPt t (iVec y) i) := by
    simp only [mul_add, Finset.sum_add_distrib]
    ring1
  rw [e₃, Complex.exp_add]
  ring1

lemma exists_sum_eq_intCast_of_tubeFourierCoeff_ne_zero
    (hper : ∀ (m : d → ℤ) z, g (fun i ↦ z i + m i) = g z) (v : d → ℝ)
    (hv : ∀ z, g (fun i ↦ z i + v i) = g z) (hc : tubeFourierCoeff g y k ≠ 0) :
    ∃ m : ℤ, ∑ i, (k i : ℝ) * v i = m := by
  have h₁ : cexp (-(2 * π * I * ∑ i, (k i : ℂ) * v i)) = 1 :=
    (mul_eq_right₀ hc).mp (tubeFourierCoeff_eq_cexp_mul k hper v hv).symm
  rcases Complex.exp_eq_one_iff.mp h₁ with ⟨m, hm⟩
  refine ⟨-m, ?_⟩
  have h₂ : ∑ i, (k i : ℂ) * v i = ((-m : ℤ) : ℂ) := by
    refine mul_left_cancel₀ two_pi_I_ne_zero ?_
    push_cast
    linear_combination -hm
  exact_mod_cast h₂

/-- The function `t ↦ g(x + iy)` on the torus, for `t` the class of `x`. -/
private noncomputable def torusLift (hg : DifferentiableOn ℂ g (tubeOver Ω))
    (hper : ∀ (m : d → ℤ) z, g (fun i ↦ z i + m i) = g z) (hy : y ∈ Ω) : C(UnitAddTorus d, ℂ) where
  toFun t := g (torusPt t (iVec y))
  continuous_toFun := by
    refine isOpenQuotientMap_torusMk.continuous_comp_iff.mp ?_
    have e : (fun t ↦ g (torusPt t (iVec y))) ∘ torusMk =
        fun x : d → ℝ ↦ g fun i ↦ (x i : ℂ) + iVec y i :=
      funext fun x ↦ apply_torusPt_coe x hper _
    rw [e]
    refine hg.continuousOn.comp_continuous (continuous_pi fun i ↦ ?_) fun x ↦ ?_
    · simp only [iVec]
      fun_prop
    · have e₁ : (fun i ↦ ((x i : ℂ) + iVec y i).im) = y := by
        funext i
        simp [iVec]
      rw [tubeOver, mem_ofPred_eq, e₁]
      exact hy

lemma mFourier_coe_apply :
    mFourier k (fun i ↦ (x i : UnitAddCircle)) = cexp (2 * π * I * ∑ i, (k i : ℂ) * x i) := by
  simp only [mFourier, ContinuousMap.coe_mk, fourier_coe_apply, ← Complex.exp_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp
  ring1

private lemma mFourier_neg_apply :
    mFourier (-k) t = cexp (-(2 * π * I * ∑ i, (k i : ℂ) * torusRep t i)) := by
  conv_lhs => rw [← coe_torusRep t]
  rw [mFourier_coe_apply]
  congr 1
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring1

private lemma tubeFourierCoeff_eq_mFourierCoeff (hg : DifferentiableOn ℂ g (tubeOver Ω))
    (hper : ∀ (m : d → ℤ) z, g (fun i ↦ z i + m i) = g z) (hy : y ∈ Ω) : tubeFourierCoeff g y k =
    mFourierCoeff (torusLift hg hper hy) k * cexp (2 * π * ∑ i, (k i : ℂ) * y i) := by
  rw [mFourierCoeff, tubeFourierCoeff, ← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
  beta_reduce
  rw [mFourier_neg_apply, smul_eq_mul]
  have e₀ : torusLift hg hper hy t = g (torusPt t (iVec y)) := rfl
  rw [e₀]
  have h : -(2 * π * I * ∑ i, (k i : ℂ) * torusPt t (iVec y) i) =
      -(2 * π * I * ∑ i, (k i : ℂ) * torusRep t i) + 2 * π * ∑ i, (k i : ℂ) * y i := by
    simp only [torusPt, iVec, mul_add, Finset.sum_add_distrib]
    have e : ∑ i, (k i : ℂ) * (I * y i) = I * ∑ i, (k i : ℂ) * y i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring1
    rw [e]
    linear_combination (-(2 * π * ∑ i, (k i : ℂ) * y i) : ℂ) * I_mul_I
  rw [h, Complex.exp_add]
  ring1

private lemma norm_mFourierCoeff_le (f : C(UnitAddTorus d, ℂ)) {B : ℝ} (hB : ∀ t, ‖f t‖ ≤ B) :
    ‖mFourierCoeff f k‖ ≤ B := by
  have h : ‖mFourierCoeff f k‖ ≤ B * (volume : Measure (UnitAddTorus d)).real univ :=
    norm_integral_le_of_norm_le_const <| ae_of_all _ fun t ↦ by
      rw [norm_smul]
      have h₁ : ‖mFourier (-k) t‖ ≤ 1 := by
        simpa [mFourier_norm] using (mFourier (-k)).norm_coe_le_norm t
      exact (mul_le_of_le_one_left (norm_nonneg _) h₁).trans (hB t)
  simpa using h

lemma summable_rexp_neg_mul_abs_int {a : ℝ} (ha : 0 < a) :
    Summable fun t : ℤ ↦ rexp (-(a * |(t : ℝ)|)) := by
  have h : Summable fun n : ℕ ↦ rexp (n * -a) := Real.summable_exp_nat_mul_iff.mpr (by linarith)
  refine (h.congr fun n ↦ ?_).of_nat_of_neg (h.congr fun n ↦ ?_)
  · rw [Int.cast_natCast, Nat.abs_cast]
    congr 1
    ring1
  · rw [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]
    congr 1
    ring1

private lemma summable_rexp_neg_mul_sum_abs_fin {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Summable fun k : Fin n → ℤ ↦ rexp (-(a * ∑ i, |(k i : ℝ)|)) := by
  induction n with
  | zero => exact (hasSum_fintype _).summable
  | succ n ih =>
    refine (Fin.consEquiv fun _ : Fin (n + 1) ↦ ℤ).summable_iff.mp ?_
    refine ((summable_rexp_neg_mul_abs_int ha).mul_of_nonneg ih (fun _ ↦ Real.exp_nonneg _)
      fun _ ↦ Real.exp_nonneg _).congr fun p ↦ ?_
    simp only [Function.comp_apply, Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ, ← Real.exp_add]
    congr 1
    ring1

private lemma summable_rexp_neg_mul_sum_abs {a : ℝ} (ha : 0 < a) :
    Summable fun k : d → ℤ ↦ rexp (-(a * ∑ i, |(k i : ℝ)|)) := by
  refine ((Equiv.arrowCongr (Fintype.equivFin d) (Equiv.refl ℤ)).summable_iff.mpr
    (summable_rexp_neg_mul_sum_abs_fin ha (Fintype.card d))).congr fun k ↦ ?_
  simp only [Function.comp_apply, Equiv.arrowCongr_apply]
  congr 3
  exact (Fintype.equivFin d).symm.sum_comp fun i ↦ |(k i : ℝ)|

/-- **The Fourier series of a periodic holomorphic function on a tube**: if `g` is holomorphic on
the tube `T = {z : Im z ∈ Ω}` over an open convex set `Ω ⊆ ℝ^d` and `g(z + m) = g(z)` for
`m ∈ ℤ^d`, then, for `y₀ ∈ Ω` and every `z ∈ T`, `g(z) = ∑_{k ∈ ℤ^d} c(k) e^{2πi k·z}`, the sum
converging absolutely, with `c(k) = ∫ g(x + iy₀) e^{-2πi k·(x + iy₀)} dx`. -/
lemma hasSum_tubeFourierCoeff_mul_cexp (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hg : DifferentiableOn ℂ g (tubeOver Ω)) (hper : ∀ (m : d → ℤ) z, g (fun i ↦ z i + m i) = g z)
    (hy : y ∈ Ω) {z : d → ℂ} (hz : z ∈ tubeOver Ω) :
    HasSum (fun k ↦ tubeFourierCoeff g y k * cexp (2 * π * I * ∑ i, (k i : ℂ) * z i)) (g z) := by
  classical
  have hz' : (fun i ↦ (z i).im) ∈ Ω := hz
  generalize hy₀ : (fun i ↦ (z i).im) = y₀ at hz'
  have hzim (i : d) : (z i).im = y₀ i := congrFun hy₀ i
  rcases Metric.isOpen_iff.mp hΩo y₀ hz' with ⟨r, hr, hball⟩
  have hε : 0 < r / 2 := half_pos hr
  have hyσ (σ : d → Bool) : (fun i ↦ y₀ i - r / 2 * (if σ i then 1 else -1)) ∈ Ω := by
    refine hball (mem_ball_iff_norm.mpr ?_)
    refine (pi_norm_lt_iff hr).mpr fun i ↦ ?_
    simp only [Pi.sub_apply, sub_sub_cancel_left, norm_neg, norm_mul, Real.norm_of_nonneg hε.le]
    split_ifs <;> simp <;> linarith
  have hB (σ : d → Bool) : ∃ B : ℝ, ∀ t, ‖torusLift hg hper (hyσ σ) t‖ ≤ B :=
    ⟨_, (torusLift hg hper (hyσ σ)).norm_coe_le_norm⟩
  choose B hB using hB
  have hbound (k : d → ℤ) (σ : d → Bool) :
      ‖mFourierCoeff (torusLift hg hper (hyσ σ)) k‖ ≤ ∑ σ, |B σ| :=
    (norm_mFourierCoeff_le k _ (hB σ)).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun σ ↦ |B σ|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ σ)))
  have hexp (k : d → ℤ) :
      ‖cexp (2 * π * I * ∑ i, (k i : ℂ) * z i)‖ = rexp (-(2 * π * ∑ i, (k i : ℝ) * y₀ i)) := by
    rw [Complex.norm_exp]
    congr 1
    have h : (2 * π * I * ∑ i, (k i : ℂ) * z i).re = -(2 * π * (∑ i, (k i : ℂ) * z i).im) := by
      have e :
          2 * π * I * ∑ i, (k i : ℂ) * z i = ((2 * π : ℝ) : ℂ) * (I * ∑ i, (k i : ℂ) * z i) := by
        push_cast
        ring1
      rw [e, re_ofReal_mul, I_mul_re]
      ring1
    rw [h, im_sum]
    simp [hzim]
  have hterm (k : d → ℤ) : ‖tubeFourierCoeff g y k * cexp (2 * π * I * ∑ i, (k i : ℂ) * z i)‖ ≤
      (∑ σ, |B σ|) * rexp (-(2 * π * (r / 2) * ∑ i, |(k i : ℝ)|)) := by
    have hk : (∑ i, (k i : ℝ) * (y₀ i - r / 2 * (if decide (0 ≤ k i) then 1 else -1))) -
        ∑ i, (k i : ℝ) * y₀ i = -(r / 2 * ∑ i, |(k i : ℝ)|) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases h : 0 ≤ k i
      · have h' : (0 : ℝ) ≤ k i := by exact_mod_cast h
        simp [h, abs_of_nonneg h']
        ring1
      · have h' : (k i : ℝ) < 0 := by exact_mod_cast not_le.mp h
        simp [h, abs_of_neg h']
        ring1
    have hσ : (fun i ↦ y₀ i - r / 2 * (if decide (0 ≤ k i) then 1 else -1)) ∈ Ω :=
      hyσ fun i ↦ decide (0 ≤ k i)
    rw [tubeFourierCoeff_eq k hΩo hΩc hg hper hy hσ, tubeFourierCoeff_eq_mFourierCoeff k hg hper hσ,
      norm_mul, norm_mul, hexp, Complex.norm_exp, mul_assoc]
    refine mul_le_mul (hbound k _) (le_of_eq ?_) (by positivity)
      (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    rw [← Real.exp_add]
    congr 1
    have h : (2 * π * ∑ i, (k i : ℂ) * ((y₀ i - r / 2 * (if decide (0 ≤ k i) then 1 else -1) : ℝ) :
        ℂ)).re =
          2 * π * ∑ i, (k i : ℝ) * (y₀ i - r / 2 * (if decide (0 ≤ k i) then 1 else -1)) := by
      have e : 2 * π * ∑ i, (k i : ℂ) * ((y₀ i - r / 2 * (if decide (0 ≤ k i) then 1 else -1) : ℝ) :
          ℂ) = ((2 * π * ∑ i, (k i : ℝ) * (y₀ i - r / 2 * (if decide (0 ≤ k i) then 1 else -1)) :
            ℝ) : ℂ) := by
        push_cast
        rfl
      rw [e, ofReal_re]
    rw [h]
    linear_combination (2 * π) * hk
  have hsummable :
      Summable fun k ↦ ‖tubeFourierCoeff g y k * cexp (2 * π * I * ∑ i, (k i : ℂ) * z i)‖ :=
    (summable_rexp_neg_mul_sum_abs (mul_pos (mul_pos two_pos Real.pi_pos) hε)).mul_left _
      |>.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm
  have hcoe (k : d → ℤ) : mFourierCoeff (torusLift hg hper hz') k *
      cexp (2 * π * I * ∑ i, (k i : ℂ) * (z i).re) =
        tubeFourierCoeff g y k * cexp (2 * π * I * ∑ i, (k i : ℂ) * z i) := by
    rw [tubeFourierCoeff_eq k hΩo hΩc hg hper hy hz',
      tubeFourierCoeff_eq_mFourierCoeff k hg hper hz',
      mul_assoc (mFourierCoeff (torusLift hg hper hz') k), ← Complex.exp_add]
    congr 2
    have e (i : d) : z i = (z i).re + (y₀ i : ℂ) * I := by
      rw [← hzim i]
      exact (re_add_im (z i)).symm
    conv_rhs => rw [funext e]
    simp only [mul_add, Finset.sum_add_distrib]
    have e₂ : ∑ i, (k i : ℂ) * ((y₀ i : ℂ) * I) = (∑ i, (k i : ℂ) * y₀ i) * I := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ by ring1
    rw [e₂]
    linear_combination (-(2 * π * ∑ i, (k i : ℂ) * y₀ i) : ℂ) * I_mul_I
  have hs₀ : Summable (mFourierCoeff (torusLift hg hper hz')) := by
    refine Summable.of_norm ?_
    refine hsummable.congr fun k ↦ ?_
    have hnorm : ‖cexp (2 * π * I * ∑ i, (k i : ℂ) * (z i).re)‖ = 1 := by
      have e : 2 * π * I * ∑ i, (k i : ℂ) * (z i).re =
          ((2 * π * ∑ i, (k i : ℝ) * (z i).re : ℝ) : ℂ) * I := by
        push_cast
        ring1
      rw [e, Complex.norm_exp_ofReal_mul_I]
    rw [← hcoe, norm_mul, hnorm, mul_one]
  have h : HasSum (fun k ↦ mFourierCoeff (torusLift hg hper hz') k •
      mFourier k fun i ↦ ((z i).re : UnitAddCircle))
        (torusLift hg hper hz' fun i ↦ ((z i).re : UnitAddCircle)) :=
    hasSum_mFourier_series_apply_of_summable hs₀ fun i ↦ ((z i).re : UnitAddCircle)
  have hval : torusLift hg hper hz' (fun i ↦ ((z i).re : UnitAddCircle)) = g z := by
    have e : g (torusPt (torusMk fun i ↦ (z i).re) (iVec y₀)) = g z := by
      rw [apply_torusPt_coe _ hper]
      congr 1
      funext i
      simp only [iVec]
      rw [← hzim i, mul_comm I]
      exact re_add_im (z i)
    exact e
  rw [hval] at h
  refine h.congr_fun fun k ↦ ?_
  rw [smul_eq_mul, mFourier_coe_apply, hcoe]
