import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.ConstantTerm
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CuspSpectrum
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.LevelOperators

/-!
# Square-integrable Maass forms with eigenvalue at least `1/4` are cusp forms

For `F` in `M(N, χ, 1/4 + r²)` (`UpperHalfPlane.maassSpace`), `r` real and `N ≠ 0`, the constant
term of `F` vanishes at every cusp: `∫_0^N F(σ(t + iy)) dt = 0` for every `σ ∈ SL(2, ℤ)` and
`y > 0`. At the cusp `∞` this is `UpperHalfPlane.integral_eq_zero_of_mem_maassSpace`. In general,
the function `f(z) = F(σ(Nz))` is `1`-periodic with eigenvalue `1/4 + r²`, so that its constant term
solves the Euler equation `y² a'' + (1/4 + r²) a = 0` (`UpperHalfPlane.fourierCoeff_ode`), and it is
square-integrable on `(1, ∞)` for `dy / y²`, the rectangles `(j - 1/2, j + 1/2) × (1, ∞)` lying in
translates of the standard fundamental domain, on which `F ∘ σ` is square-integrable. So it
vanishes (`Complex.eq_zero_of_euler_ode_of_integrableOn`).

Hence the spectrum of the square-integrable Maass forms and that of the Maass cusp forms
(`UpperHalfPlane.maassCuspSpectrum`) have the same elements in `[1/4, ∞)`, and these eigenspaces are
finite-dimensional.

## Main results

* `UpperHalfPlane.integral_comp_add_mul_I_eq_zero_of_euler`: the constant term of a `1`-periodic
  eigenfunction with real spectral parameter vanishes, if it is square-integrable.
* `UpperHalfPlane.integral_sl_smul_eq_zero_of_mem_maassSpace`: the constant term at every cusp of
  an element of `M(N, χ, 1/4 + r²)`, `r` real, vanishes.
* `UpperHalfPlane.mem_maassCuspSpace_of_mem_maassSpace`: `M(N, χ, 1/4 + r²)` consists of cusp forms.
* `UpperHalfPlane.finite_maassSpace`: it is finite-dimensional.
* `UpperHalfPlane.maassMultiplicity_lt_aleph0`: the multiplicity of `1/4 + r²` is finite.
-/

open Function MeasureTheory Real Set

open scoped ContDiff MatrixGroups Pointwise

namespace UpperHalfPlane

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {F H : ℍ → ℂ} {f : ℂ → ℂ} {r y : ℝ} {a : ℂ}

/-- **The constant term of a `1`-periodic eigenfunction with real spectral parameter vanishes**, if
it is square-integrable on `(1, ∞)` for `dy / y²`, as it solves the Euler equation. -/
lemma integral_comp_add_mul_I_eq_zero_of_euler (hf : ContDiffOn ℝ ∞ f {z | 0 < z.im})
    (hper : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (hΔ : ∀ z : ℂ, 0 < z.im → hyperbolicLaplacian f z + maassEigenvalue r * f z = 0)
    (hint : IntegrableOn (fun y : ℝ ↦ ‖∫ t in (0 : ℝ)..1, f (t + y * Complex.I)‖ ^ 2 / y ^ 2)
      (Ioi 1)) (hy : 0 < y) : ∫ t in (0 : ℝ)..1, f (t + y * Complex.I) = 0 := by
  have he : Continuous fun t : ℝ ↦ Complex.exp (-(2 * π * Complex.I * ((0 : ℤ) : ℂ)) * t) := by
    fun_prop
  have h : ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * ((0 : ℤ) : ℂ)) * t) *
      f (t + y * Complex.I) = 0 :=
    Complex.eq_zero_of_euler_ode_of_integrableOn (r := r)
      (fun _ ↦ hasDerivAt_integral_comp_add_mul_I hf he)
      (fun _ ↦ hasDerivAt_integral_comp_add_mul_I (contDiffOn_fderiv_apply Complex.I hf) he)
      (fun x hx ↦ by
        simpa [maassEigenvalue] using fourierCoeff_ode 0 hf hper hΔ hx)
      (by simpa using hint) hy
  simpa using h

variable (σ : SL(2, ℤ))

lemma integrableOn_norm_sq_rectangle_of_mem_maassTileSpace (hH : H ∈ maassTileSpace a) (j : ℕ) :
    IntegrableOn (fun w ↦ ‖H w‖ ^ 2) (maassRectangle j) := by
  have hc :
      AEStronglyMeasurable H (volume.restrict ((ModularGroup.T ^ (j : ℤ)) • ModularGroup.fdo)) :=
    (hH.2.1 _).aestronglyMeasurable
  have h : IntegrableOn (fun w ↦ ‖H w‖ ^ 2) ((ModularGroup.T ^ (j : ℤ)) • ModularGroup.fdo) :=
    (memLp_two_iff_integrable_sq_norm hc).mp (hH.2.1 _)
  exact h.mono_set (rectangle_subset_smul_fdo j)

variable [NeZero N]

lemma integrableOn_inv_sq_mul_integral_norm_sq (hF : F ∈ maassSpace N χ a) : IntegrableOn
    (fun v : ℝ ↦ (v ^ 2)⁻¹ * ∫ s in (0 : ℝ)..N, ‖F (σ • ofComplex ((s : ℂ) + v * Complex.I))‖ ^ 2)
    (Ioi 1) := by
  have hH : (fun τ ↦ F (σ • τ)) ∈ maassTileSpace a := comp_sl_smul_mem_maassTileSpace hF σ
  have hFc : Continuous F := continuous_of_mem_maassSpace hF
  have hcoordj (j : ℕ) : Integrable
      (fun p : ℝ × ℝ ↦ ((p.2 ^ 2)⁻¹ : ℝ) • ‖F (σ • ofComplex (p.1 + p.2 * Complex.I))‖ ^ 2)
      ((volume.restrict (Ioo ((j : ℝ) - 1 / 2) (j + 1 / 2))).prod (volume.restrict (Ioi 1))) := by
    have h : IntegrableOn
        (fun p : ℝ × ℝ ↦ ((p.2 ^ 2)⁻¹ : ℝ) • ‖F (σ • ofComplex (p.1 + p.2 * Complex.I))‖ ^ 2)
        (Ioo ((j : ℝ) - 1 / 2) (j + 1 / 2) ×ˢ Ioi 1) :=
      (integrableOn_re_im_mem_prod_iff' measurableSet_Ioo measurableSet_Ioi
        (Ioi_subset_Ioi zero_le_one)).mp (integrableOn_norm_sq_rectangle_of_mem_maassTileSpace hH j)
    rwa [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  refine (integrable_finsetSum (Finset.range N) fun j _ ↦ (hcoordj j).integral_prod_right).congr ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun v hv ↦ ?_)
  have hv0 : 0 < v := zero_lt_one.trans hv
  have huv : Continuous fun t : ℝ ↦ ‖F (σ • ofComplex ((t : ℂ) + v * Complex.I))‖ ^ 2 :=
    (continuous_smul_ofComplex_add_mul_I σ hFc hv0).norm.pow 2
  have hperv : Periodic (fun t : ℝ ↦ ‖F (σ • ofComplex ((t : ℂ) + v * Complex.I))‖ ^ 2) (N : ℝ) :=
    fun t ↦ by
      dsimp only
      rw [maassCuspidal_period σ (χ := χ) (fun γ hγ τ ↦ smul_eq_of_mem_maassSpace hF hγ) t hv0]
  have h2 : ∑ j ∈ Finset.range N, ∫ s in Ioo ((j : ℝ) - 1 / 2) (j + 1 / 2),
      ‖F (σ • ofComplex ((s : ℂ) + v * Complex.I))‖ ^ 2 =
        ∫ s in (-(1 / 2) : ℝ)..-(1 / 2) + N, ‖F (σ • ofComplex ((s : ℂ) + v * Complex.I))‖ ^ 2 :=
    sum_setIntegral_Ioo_eq N huv
  rw [hperv.intervalIntegral_add_eq (-(1 / 2)) 0, zero_add] at h2
  dsimp only
  rw [← h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [smul_eq_mul]
  rw [integral_const_mul]

/-- **The constant term of a square-integrable Maass form with real spectral parameter vanishes at
every cusp**: for `F` in `M(N, χ, 1/4 + r²)`, `r` real and `N ≠ 0`, `∫_0^N F(σ(t + iy)) dt = 0` for
every `σ ∈ SL(2, ℤ)` and `y > 0`. -/
lemma integral_sl_smul_eq_zero_of_mem_maassSpace (hF : F ∈ maassSpace N χ (maassEigenvalue r))
    (hy : 0 < y) : ∫ t in (0 : ℝ)..N, F (σ • ofComplex ((t : ℂ) + y * Complex.I)) = 0 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast NeZero.pos N
  have hN0 : (N : ℝ) ≠ 0 := hN.ne'
  have hH : (fun τ ↦ F (σ • τ)) ∈ maassTileSpace (maassEigenvalue r) :=
    comp_sl_smul_mem_maassTileSpace hF σ
  have hFc : Continuous F := continuous_of_mem_maassSpace hF
  let g : ℂ → ℂ := (fun τ ↦ F (σ • τ)) ∘ ofComplex
  let f : ℂ → ℂ := fun u ↦ g ((N : ℝ) * u + (0 : ℝ))
  have hf : ContDiffOn ℝ ∞ f {z | 0 < z.im} := fun _ hz ↦
    (contDiffAt_comp_affine hH.1 hN 0 hz).contDiffWithinAt
  have hg (t v : ℝ) : ((N : ℝ) * ((t : ℂ) + v * Complex.I) + (0 : ℝ) : ℂ) =
      ((N * t : ℝ) : ℂ) + (N * v : ℝ) * Complex.I := by
    push_cast
    ring1
  have hper : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z := fun z hz ↦ by
    have hz' : z = (z.re : ℂ) + z.im * Complex.I := (Complex.re_add_im z).symm
    have e : ((N : ℝ) * (z + 1) + (0 : ℝ) : ℂ) =
        ((N * z.re + N : ℝ) : ℂ) + (N * z.im : ℝ) * Complex.I := by
      conv_lhs => rw [hz']
      push_cast
      ring1
    have e2 : ((N : ℝ) * z + (0 : ℝ) : ℂ) = ((N * z.re : ℝ) : ℂ) + (N * z.im : ℝ) * Complex.I := by
      conv_lhs => rw [hz', hg]
    simp only [f]
    rw [e, e2]
    exact maassCuspidal_period σ (χ := χ) (fun γ hγ τ ↦ smul_eq_of_mem_maassSpace hF hγ) _
      (mul_pos hN hz)
  have hΔ : ∀ z : ℂ, 0 < z.im → hyperbolicLaplacian f z + maassEigenvalue r * f z = 0 := by
    intro z hz
    rw [hyperbolicLaplacian_comp_affine]
    exact hH.2.2 _ (by simpa using mul_pos hN hz)
  have hfpt (t v : ℝ) : f ((t : ℂ) + v * Complex.I) =
      F (σ • ofComplex (((N * t : ℝ) : ℂ) + (N * v : ℝ) * Complex.I)) := by
    simp only [f, g, Function.comp_apply]
    rw [hg]
  have hQ : IntegrableOn (fun v : ℝ ↦ (v ^ 2)⁻¹ * ∫ s in (0 : ℝ)..N,
      ‖F (σ • ofComplex ((s : ℂ) + v * Complex.I))‖ ^ 2) (Ioi 1) :=
    integrableOn_inv_sq_mul_integral_norm_sq σ hF
  have he : Continuous fun t : ℝ ↦ Complex.exp (-(2 * π * Complex.I * ((0 : ℤ) : ℂ)) * t) := by
    fun_prop
  have hint : IntegrableOn (fun y : ℝ ↦ ‖∫ t in (0 : ℝ)..1, f (t + y * Complex.I)‖ ^ 2 / y ^ 2)
      (Ioi 1) := by
    have hQ2 : IntegrableOn (fun y : ℝ ↦ N * (((N * y) ^ 2)⁻¹ * ∫ s in (0 : ℝ)..N,
        ‖F (σ • ofComplex ((s : ℂ) + (N * y : ℝ) * Complex.I))‖ ^ 2)) (Ioi 1) :=
      ((integrableOn_Ioi_comp_mul_left_iff _ 1 hN).mpr
        (hQ.mono_set (Ioi_subset_Ioi (by linarith)))).const_mul _
    refine hQ2.mono' (ContinuousOn.aestronglyMeasurable (fun v hv ↦ ?_) measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun v hv ↦ ?_))
    · have hv0 : 0 < v := zero_lt_one.trans hv
      have h : HasDerivAt (fun s : ℝ ↦ ∫ t in (0 : ℝ)..1,
          Complex.exp (-(2 * π * Complex.I * ((0 : ℤ) : ℂ)) * t) * f (t + s * Complex.I))
          (∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * ((0 : ℤ) : ℂ)) * t) *
            fderiv ℝ f (t + v * Complex.I) Complex.I) v :=
        hasDerivAt_integral_comp_add_mul_I hf he hv0
      simp only [Int.cast_zero, mul_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul] at h
      exact (h.continuousAt.norm.pow 2 |>.div (continuous_pow 2).continuousAt
        (pow_ne_zero 2 hv0.ne')).continuousWithinAt
    · have hv0 : 0 < v := zero_lt_one.trans hv
      have hNv : 0 < (N : ℝ) * v := mul_pos hN hv0
      have hcg : Continuous fun s : ℝ ↦ ‖F (σ • ofComplex ((s : ℂ) + (N * v : ℝ) * Complex.I))‖ :=
        (continuous_smul_ofComplex_add_mul_I σ hFc hNv).norm
      have hcf : Continuous fun t : ℝ ↦ ‖f ((t : ℂ) + v * Complex.I)‖ := by
        simp only [hfpt]
        exact hcg.comp (continuous_const.mul continuous_id)
      have h1 : ‖∫ t in (0 : ℝ)..1, f (t + v * Complex.I)‖ ^ 2 ≤
          ∫ t in (0 : ℝ)..1, ‖f ((t : ℂ) + v * Complex.I)‖ ^ 2 :=
        (pow_le_pow_left₀ (norm_nonneg _)
          (intervalIntegral.norm_integral_le_integral_norm zero_le_one) 2).trans
            (sq_intervalIntegral_le hcf)
      have h2 : ∫ t in (0 : ℝ)..1, ‖f ((t : ℂ) + v * Complex.I)‖ ^ 2 =
          (N : ℝ)⁻¹ * ∫ s in (0 : ℝ)..N,
            ‖F (σ • ofComplex ((s : ℂ) + (N * v : ℝ) * Complex.I))‖ ^ 2 := by
        simp only [hfpt]
        rw [intervalIntegral.integral_comp_mul_left
          (fun s : ℝ ↦ ‖F (σ • ofComplex ((s : ℂ) + (N * v : ℝ) * Complex.I))‖ ^ 2) hN0, mul_zero,
          mul_one, smul_eq_mul]
      have hI :
          0 ≤ ∫ s in (0 : ℝ)..N, ‖F (σ • ofComplex ((s : ℂ) + (N * v : ℝ) * Complex.I))‖ ^ 2 :=
        intervalIntegral.integral_nonneg hN.le fun s _ ↦ by positivity
      rw [Real.norm_of_nonneg (by positivity)]
      refine (div_le_div_of_nonneg_right (h1.trans h2.le) (by positivity)).trans (le_of_eq ?_)
      field_simp
  have h0 : ∫ t in (0 : ℝ)..1, f (t + (y / N : ℝ) * Complex.I) = 0 :=
    integral_comp_add_mul_I_eq_zero_of_euler hf hper hΔ hint (div_pos hy hN)
  simp only [hfpt] at h0
  have e5 : (N : ℝ) * (y / N) = y := by
    field_simp
  simp only [e5] at h0
  have h4 : ∫ t in (0 : ℝ)..1, F (σ • ofComplex (((N * t : ℝ) : ℂ) + y * Complex.I)) =
      (N : ℝ)⁻¹ • ∫ t in (0 : ℝ)..N, F (σ • ofComplex ((t : ℂ) + y * Complex.I)) := by
    rw [intervalIntegral.integral_comp_mul_left
      (fun s : ℝ ↦ F (σ • ofComplex ((s : ℂ) + y * Complex.I))) hN0, mul_zero, mul_one]
  rw [h0, Complex.real_smul] at h4
  refine (mul_eq_zero.mp h4.symm).resolve_left ?_
  exact_mod_cast inv_ne_zero hN0

/-- **Maass forms with eigenvalue at least `1/4` are cusp forms**: for `r` real and `N ≠ 0`, every
element of `M(N, χ, 1/4 + r²)` lies in the space of Maass cusp forms. -/
lemma mem_maassCuspSpace_of_mem_maassSpace (hF : F ∈ maassSpace N χ (maassEigenvalue r)) :
    F ∈ maassCuspSpace N χ (maassEigenvalue r) :=
  mem_maassCuspSpace_iff.mpr ⟨hF, continuous_of_mem_maassSpace hF,
    fun _ hγ _ ↦ smul_eq_of_mem_maassSpace hF hγ, integrableOn_norm_sq_of_mem_maassSpace hF,
    fun γ _ hy ↦ integral_sl_smul_eq_zero_of_mem_maassSpace γ hF hy⟩

/-- **The eigenspaces with eigenvalue at least `1/4` are finite-dimensional** (LMFDB
`mf.maass.mwf.dimension`): for `r` real and `N ≠ 0`, `M(N, χ, 1/4 + r²)` has finite dimension. -/
lemma finite_maassSpace : Module.Finite ℂ (maassSpace N χ (maassEigenvalue r)) := by
  have h : maassSpace N χ (maassEigenvalue r) = maassCuspSpace N χ (maassEigenvalue r) :=
    le_antisymm (fun _ hF ↦ mem_maassCuspSpace_of_mem_maassSpace hF) inf_le_left
  rw [h]
  exact finite_maassCuspSpace _

/-- **The multiplicity of an eigenvalue at least `1/4` is finite** (LMFDB
`mf.maass.mwf.dimension`): for `r` real and `N ≠ 0`, the new space of `M(N, χ, 1/4 + r²)` has
finite dimension. -/
lemma maassMultiplicity_lt_aleph0 :
    maassMultiplicity N χ (maassEigenvalue r) < Cardinal.aleph0 := by
  have h : FiniteDimensional ℂ (maassSpace N χ (maassEigenvalue r)) := finite_maassSpace
  have h1 : FiniteDimensional ℂ (maassNewSpace N χ (maassEigenvalue r)) :=
    Submodule.finiteDimensional_of_le (maassNewSpace_le N χ _)
  exact Module.rank_lt_aleph0 ℂ _

end UpperHalfPlane
