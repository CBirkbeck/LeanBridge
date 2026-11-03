import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CuspNewformExpansion

/-!
# The constant term of a square-integrable Maass form with real spectral parameter

Let `F` be a Maass form in `M(N, χ, λ)` (`UpperHalfPlane.maassSpace`, square-integrable on
`Γ₀(N) \ ℍ`, and `1`-periodic as `T ∈ Γ₀(N)`) with Laplace eigenvalue `λ = 1/4 + r²` for a real
`r`, that is `λ ≥ 1/4`. Its constant term `a_0(y) = ∫_0^1 F(t + iy) dt` at `∞` vanishes: it
solves the Euler equation `y² a_0'' + (1/4 + r²) a_0 = 0`, whose solutions
`α y^{1/2 + ir} + β y^{1/2 - ir}` (`√y (α + β log y)` for `r = 0`) are not square-integrable on
`(1, ∞)` for `dy / y²` unless `0`, while `∫_1^∞ |a_0(y)|² dy / y² ≤ ∫∫ |F|² dx dy / y²` over the
rectangle `(-1/2, 1/2) × (1, ∞)` of the standard fundamental domain (Cauchy–Schwarz and Fubini,
`UpperHalfPlane.integrableOn_sq_norm_fourierCoeff_div_sq`). In the proof the Wronskian
`W = u a_0' - u' a_0` with `u(y) = y^{1/2 + ir}` is constant, and integrating it against the bump
`φ(y) = log y (L - log y) / y` over `[1, e^L]` gives `|W| L³ / 6 ≤ C L^{5/2}`, so `W = 0` and
`a_0 = a_0(1) u`, with `|a_0(y)|² / y² = |a_0(1)|² / y`.

So for real spectral parameter `R` (the case of the LMFDB's Maass forms, `λ > 1/4`) the
cuspidality hypothesis at `∞` of the expansion theorems is automatic: every even (odd) Maass
newform `F` of weight `0` on `Γ₀(N)` with trivial character (`UpperHalfPlane.IsMaassNewform`, the
LMFDB's definition `mf.maass.mwf`, without cuspidality) and real `R` has the cosine (sine)
expansion with the coefficients `maassCoefficients R F` (LMFDB `mf.maass.mwf.coefficients`), and
the normalised coefficients `a(m) / a(1)`, `m` prime to `N`, are real. The constant newform `1`
of level `1` (`UpperHalfPlane.isMaassNewform_const_one`), which has no expansion, has eigenvalue
`0` and non-real spectral parameter `R = ±i/2`.

## Main results

* `Complex.eq_zero_of_euler_ode_of_integrableOn`: a solution of `y² v'' + (1/4 + r²) v = 0` with
  `∫_1^∞ |v(y)|² dy / y² < ∞` vanishes, for real `r`.
* `UpperHalfPlane.integral_eq_zero_of_mem_maassSpace`: the constant term at `∞` of an element of
  `M(N, χ, 1/4 + r²)` vanishes for real `r`.
* `UpperHalfPlane.IsMaassNewform.hasMaassCosineExpansion_ofReal`,
  `UpperHalfPlane.IsMaassNewform.hasMaassSineExpansion_ofReal`: the cosine (sine) expansion of an
  even (odd) Maass newform with real spectral parameter.
* `UpperHalfPlane.IsMaassNewform.conj_maassCoefficients_div_of_isEven_ofReal`,
  `UpperHalfPlane.IsMaassNewform.conj_maassCoefficients_div_of_isOdd_ofReal`: its normalised
  coefficients prime to `N` are real.
* `UpperHalfPlane.IsMaassNewform.maassCoefficients_one_ne_zero_of_isEven_ofReal`,
  `UpperHalfPlane.IsMaassNewform.maassCoefficients_one_ne_zero_of_isOdd_ofReal`: at level `1`,
  `a(1) ≠ 0`.
-/

open Filter MeasureTheory Real Set Topology

open scoped ComplexConjugate

namespace Complex

variable {r : ℝ} {v v' v'' : ℝ → ℂ}

lemma hasDerivAt_ofReal_cpow {s : ℂ} {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ s) (s * (y : ℂ) ^ (s - 1)) y :=
  (hasStrictDerivAt_cpow_const (ofReal_mem_slitPlane.mpr hy)).hasDerivAt.comp_ofReal

/-- **The Euler equation has no square-integrable solution**: for real `r`, a solution `v` of
`y² v'' + (1/4 + r²) v = 0` on `(0, ∞)` with `∫_1^∞ |v(y)|² dy / y² < ∞` vanishes. The Wronskian
`W = u v' - u' v` with `u(y) = y^{1/2 + ir}` is constant; integrating `W φ` for
`φ(y) = log y (L - log y) / y` over `[1, e^L]` and moving the derivative of `v` onto `u φ` gives
`|W| L³ / 6 ≤ (|1/2 + ir| + 1) L^{5/2} (1 + ∫_1^∞ |v|² dy / y²)` (as `|u(y)| = √y`), so `W = 0`,
`v = v(1) u` and `|v(y)|² / y² = |v(1)|² / y` is integrable on `(1, ∞)` only if `v(1) = 0`. -/
lemma eq_zero_of_euler_ode_of_integrableOn (hv : ∀ x, 0 < x → HasDerivAt v (v' x) x)
    (hv' : ∀ x, 0 < x → HasDerivAt v' (v'' x) x)
    (hode : ∀ x : ℝ, 0 < x → (x : ℂ) ^ 2 * v'' x + (1 / 4 + (r : ℂ) ^ 2) * v x = 0)
    (hint : IntegrableOn (fun x ↦ ‖v x‖ ^ 2 / x ^ 2) (Ioi 1)) {x : ℝ} (hx : 0 < x) : v x = 0 := by
  let s : ℂ := 1 / 2 + I * r
  have hs : s * (s - 1) = -(1 / 4 + (r : ℂ) ^ 2) := by
    simp only [s]
    linear_combination (r : ℂ) ^ 2 * I_sq
  have hs1 : s.re = 1 / 2 := by
    simp [s]
  have hpow (y : ℝ) (hy : 0 < y) : (y : ℂ) ^ 2 * (y : ℂ) ^ (s - 1 - 1) = (y : ℂ) ^ s := by
    rw [← cpow_natCast, ← cpow_add _ _ (ofReal_ne_zero.mpr hy.ne')]
    congr 1
    push_cast
    ring1
  let W : ℝ → ℂ := fun y ↦ (y : ℂ) ^ s * v' y - s * (y : ℂ) ^ (s - 1) * v y
  have hW (y : ℝ) (hy : 0 < y) : HasDerivAt W 0 y := by
    refine (((hasDerivAt_ofReal_cpow hy).mul (hv' y hy)).sub
      (((hasDerivAt_ofReal_cpow hy).const_mul s).mul (hv y hy))).congr_deriv ?_
    have hy2 : (y : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (ofReal_ne_zero.mpr hy.ne')
    refine mul_left_cancel₀ hy2 ?_
    rw [mul_zero]
    linear_combination (y : ℂ) ^ s * hode y hy - s * (s - 1) * v y * hpow y hy -
      (y : ℂ) ^ s * v y * hs
  have hconst (y : ℝ) (hy : 0 < y) : W y = W 1 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun z hz ↦ (hW z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hW z hz).deriv) hy (mem_Ioi.mpr one_pos)
  have hW₁ : W 1 = 0 := by
    let I₂ : ℝ := ∫ y in Ioi 1, ‖v y‖ ^ 2 / y ^ 2
    have hI₂ : 0 ≤ I₂ := setIntegral_nonneg measurableSet_Ioi fun y _ ↦ by positivity
    have hbound (T : ℝ) (hT : 1 ≤ T) : ‖W 1‖ ≤ 6 * (‖s‖ + 1) * (I₂ + 1) / T := by
      let L : ℝ := T ^ 2
      have hL : 1 ≤ L := one_le_pow₀ hT
      have hB : 1 ≤ rexp L := one_le_exp (by positivity)
      let φ : ℝ → ℝ := fun y ↦ Real.log y * (L - Real.log y) / y
      let φ' : ℝ → ℝ := fun y ↦ ((L - 2 * Real.log y) - Real.log y * (L - Real.log y)) / y ^ 2
      let g : ℝ → ℂ := fun y ↦ -(v y * (2 * (s * (y : ℂ) ^ (s - 1)) * (φ y : ℂ) +
        (y : ℂ) ^ s * (φ' y : ℂ)))
      let H : ℝ → ℂ := fun y ↦ W 1 * ((L * Real.log y ^ 2 / 2 - Real.log y ^ 3 / 3 : ℝ) : ℂ) -
        (y : ℂ) ^ s * v y * (φ y : ℂ)
      have hH (y : ℝ) (hy : y ∈ uIcc 1 (rexp L)) : HasDerivAt H (g y) y := by
        rw [uIcc_of_le hB] at hy
        have hy0 : 0 < y := one_pos.trans_le hy.1
        have hlog : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy0.ne'
        have hΦ : HasDerivAt (fun y ↦ L * Real.log y ^ 2 / 2 - Real.log y ^ 3 / 3) (φ y) y := by
          refine (((hlog.pow 2).const_mul L).div_const 2 |>.sub
            ((hlog.pow 3).div_const 3)).congr_deriv ?_
          simp only [φ]
          field_simp
          ring1
        have hφ : HasDerivAt φ (φ' y) y := by
          refine ((hlog.mul (hlog.const_sub L)).div (hasDerivAt_id y) hy0.ne').congr_deriv ?_
          simp only [φ', id, Pi.mul_apply]
          field_simp
          ring1
        refine ((hΦ.ofReal_comp.const_mul (W 1)).sub (((hasDerivAt_ofReal_cpow hy0).mul
          (hv y hy0)).mul hφ.ofReal_comp)).congr_deriv ?_
        rw [← hconst y hy0]
        simp only [Pi.mul_apply]
        ring1
      have hg : IntervalIntegrable g volume 1 (rexp L) := by
        refine ContinuousOn.intervalIntegrable fun y hy ↦ ContinuousAt.continuousWithinAt ?_
        rw [uIcc_of_le hB] at hy
        have hy0 : 0 < y := one_pos.trans_le hy.1
        have hv0 : ContinuousAt v y := (hv y hy0).continuousAt
        have hu0 : ContinuousAt (fun y : ℝ ↦ (y : ℂ) ^ s) y :=
          (hasDerivAt_ofReal_cpow hy0).continuousAt
        have hu1 : ContinuousAt (fun y : ℝ ↦ (y : ℂ) ^ (s - 1)) y :=
          (hasDerivAt_ofReal_cpow hy0).continuousAt
        have hlog : ContinuousAt Real.log y := Real.continuousAt_log hy0.ne'
        have hy1 : y ≠ 0 := hy0.ne'
        fun_prop (disch := first | exact hy1 | exact pow_ne_zero 2 hy1)
      have hFTC : ∫ y in (1 : ℝ)..rexp L, g y = W 1 * ((L ^ 3 / 6 : ℝ) : ℂ) := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hH hg]
        simp only [H, φ, Real.log_exp, Real.log_one]
        push_cast
        ring1
      let bnd : ℝ → ℝ := fun y ↦ L ^ 2 * (‖s‖ + 1) * (T * (‖v y‖ ^ 2 / y ^ 2) + T⁻¹ * y⁻¹)
      have hpt : ∀ᵐ y ∂volume, y ∈ Ioc 1 (rexp L) → ‖g y‖ ≤ bnd y := by
        refine ae_of_all _ fun y hy ↦ ?_
        have hy0 : 0 < y := one_pos.trans hy.1
        have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy.1.le
        have hlogL : Real.log y ≤ L := by
          rw [← Real.log_exp L]
          exact Real.log_le_log hy0 hy.2
        have hP : |Real.log y * (L - Real.log y)| ≤ L ^ 2 := by
          rw [abs_le]
          constructor <;> nlinarith
        have hQ : |(L - 2 * Real.log y) - Real.log y * (L - Real.log y)| ≤ 2 * L ^ 2 := by
          rw [abs_le]
          constructor <;> nlinarith
        have h1 : ‖g y‖ ≤ ‖v y‖ * (2 * (‖s‖ * ‖(y : ℂ) ^ (s - 1)‖) * (L ^ 2 / y) +
            ‖(y : ℂ) ^ s‖ * (2 * L ^ 2 / y ^ 2)) := by
          simp only [g]
          rw [norm_neg, norm_mul]
          refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (norm_nonneg _)
          rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_real, norm_real, RCLike.norm_ofNat,
            Real.norm_eq_abs, Real.norm_eq_abs]
          simp only [φ']
          rw [abs_div, abs_div, abs_of_pos hy0, abs_of_pos (pow_pos hy0 2)]
          gcongr
        rw [norm_cpow_eq_rpow_re_of_pos hy0, norm_cpow_eq_rpow_re_of_pos hy0, sub_re, one_re,
          hs1] at h1
        refine h1.trans ?_
        rcases (⟨√y, Real.sqrt_pos.mpr hy0, (Real.sq_sqrt hy0.le).symm⟩ :
          ∃ q : ℝ, 0 < q ∧ y = q ^ 2) with ⟨q, hq, rfl⟩
        have e1 : (q ^ 2) ^ (1 / 2 : ℝ) = q := by
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hq.le]
        have e2 : (q ^ 2) ^ (1 / 2 - 1 : ℝ) = q⁻¹ := by
          rw [Real.rpow_sub hy0, Real.rpow_one, e1]
          field_simp
        have hT0 : 0 < T := one_pos.trans_le hT
        have key : bnd (q ^ 2) - ‖v (q ^ 2)‖ * (2 * (‖s‖ * q⁻¹) * (L ^ 2 / q ^ 2) +
            q * (2 * L ^ 2 / (q ^ 2) ^ 2)) =
              L ^ 2 * (‖s‖ + 1) * (T * ‖v (q ^ 2)‖ - q) ^ 2 / (T * q ^ 4) := by
          simp only [bnd]
          field_simp
          ring1
        rw [e1, e2]
        have hk : 0 ≤ L ^ 2 * (‖s‖ + 1) * (T * ‖v (q ^ 2)‖ - q) ^ 2 / (T * q ^ 4) := by
          positivity
        linarith
      have hvI : IntervalIntegrable (fun y ↦ ‖v y‖ ^ 2 / y ^ 2) volume 1 (rexp L) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hB).mpr (hint.mono_set Ioc_subset_Ioi_self)
      have hinvI : IntervalIntegrable (fun y : ℝ ↦ y⁻¹) volume 1 (rexp L) := by
        refine (continuousOn_id.inv₀ fun y hy ↦ ?_).intervalIntegrable
        rw [uIcc_of_le hB] at hy
        exact (one_pos.trans_le hy.1).ne'
      have hbI : IntervalIntegrable bnd volume 1 (rexp L) :=
        ((hvI.const_mul T).add (hinvI.const_mul T⁻¹)).const_mul (L ^ 2 * (‖s‖ + 1))
      have hle : ∫ y in (1 : ℝ)..rexp L, bnd y ≤ L ^ 2 * (‖s‖ + 1) * (T * I₂ + T⁻¹ * L) := by
        simp only [bnd]
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hvI.const_mul T)
          (hinvI.const_mul T⁻¹), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos (exp_pos L), div_one,
          Real.log_exp]
        gcongr
        rw [intervalIntegral.integral_of_le hB]
        exact setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Ioi).mpr
          (.of_forall fun y _ ↦ by positivity)) Ioc_subset_Ioi_self.eventuallyLE
      have h : ‖∫ y in (1 : ℝ)..rexp L, g y‖ ≤ L ^ 2 * (‖s‖ + 1) * (T * I₂ + T⁻¹ * L) :=
        (intervalIntegral.norm_integral_le_of_norm_le hB hpt hbI).trans hle
      have hT0 : 0 < T := one_pos.trans_le hT
      have e : T⁻¹ * L = T := by
        simp only [L]
        field_simp
      rw [hFTC, norm_mul, norm_real, Real.norm_of_nonneg (by positivity), e] at h
      rw [le_div_iff₀ hT0]
      refine le_of_mul_le_mul_right ?_ (by positivity : 0 < T ^ 5 / 6)
      simp only [L] at h
      linear_combination h
    have hlim : Tendsto (fun T : ℝ ↦ 6 * (‖s‖ + 1) * (I₂ + 1) / T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    exact norm_le_zero_iff.mp (ge_of_tendsto hlim ((eventually_ge_atTop 1).mono hbound))
  let G : ℝ → ℂ := fun y ↦ v y * (y : ℂ) ^ (-s)
  have hG (y : ℝ) (hy : 0 < y) : HasDerivAt G 0 y := by
    refine ((hv y hy).mul (hasDerivAt_ofReal_cpow hy)).congr_deriv ?_
    have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
    have hp : (y : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hy')
    have h0 : (y : ℂ) ^ s * v' y - s * (y : ℂ) ^ (s - 1) * v y = 0 := (hconst y hy).trans hW₁
    rw [cpow_sub _ _ hy', cpow_one] at h0
    have h0' : (y : ℂ) ^ s * (v' y - s * v y / y) = 0 := by
      rw [← h0]
      ring1
    rw [sub_eq_zero.mp ((mul_eq_zero.mp h0').resolve_left hp), cpow_sub _ _ hy', cpow_one]
    ring1
  have hGc (y : ℝ) (hy : 0 < y) : G y = G 1 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun z hz ↦ (hG z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hG z hz).deriv) hy (mem_Ioi.mpr one_pos)
  have hvy (y : ℝ) (hy : 0 < y) : v y = v 1 * (y : ℂ) ^ s := by
    have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
    have hp : (y : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hy')
    have h : v y * ((y : ℂ) ^ s)⁻¹ = v 1 := by
      simpa only [G, ofReal_one, one_cpow, cpow_neg, inv_one, mul_one] using hGc y hy
    rw [← h, inv_mul_cancel_right₀ hp]
  by_contra hx0
  have hv1 : v 1 ≠ 0 := by
    intro h1
    exact hx0 (by rw [hvy x hx, h1, zero_mul])
  refine not_integrableOn_Ioi_inv (a := (1 : ℝ)) ?_
  refine IntegrableOn.congr_fun (hint.const_mul (‖v 1‖ ^ 2)⁻¹) (fun y hy ↦ ?_) measurableSet_Ioi
  have hy0 : 0 < y := one_pos.trans hy
  have hn : ‖(y : ℂ) ^ s‖ ^ 2 = y := by
    rw [norm_cpow_eq_rpow_re_of_pos hy0, hs1, ← Real.sqrt_eq_rpow, Real.sq_sqrt hy0.le]
  have hv1' : ‖v 1‖ ≠ 0 := norm_ne_zero_iff.mpr hv1
  rw [hvy y hy0, norm_mul, mul_pow, hn]
  field_simp

end Complex

namespace UpperHalfPlane

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {F : ℍ → ℂ} {r : ℝ}

/-- **The constant term of a square-integrable Maass form with real spectral parameter
vanishes**: for `F` in `M(N, χ, 1/4 + r²)` (`maassSpace`) with `r` real,
`∫_0^1 F(t + iy) dt = 0` for every `y > 0`: the constant term solves the Euler equation
`y² a'' + (1/4 + r²) a = 0` (`fourierCoeff_ode`) and is square-integrable on `(1, ∞)` for
`dy / y²` (`integrableOn_sq_norm_fourierCoeff_div_sq`), so it vanishes
(`Complex.eq_zero_of_euler_ode_of_integrableOn`). -/
lemma integral_eq_zero_of_mem_maassSpace (hF : F ∈ maassSpace N χ (maassEigenvalue r)) {y : ℝ}
    (hy : 0 < y) : ∫ t in (0 : ℝ)..1, (F ∘ ofComplex) (t + y * Complex.I) = 0 := by
  have he : Continuous fun t : ℝ ↦ Complex.exp (-(2 * π * Complex.I * ((0 : ℤ) : ℂ)) * t) := by
    fun_prop
  have h : ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * ((0 : ℤ) : ℂ)) * t) *
      (F ∘ ofComplex) (t + y * Complex.I) = 0 :=
    Complex.eq_zero_of_euler_ode_of_integrableOn (r := r)
      (fun _ ↦ hasDerivAt_integral_comp_add_mul_I hF.1 he)
      (fun _ ↦ hasDerivAt_integral_comp_add_mul_I (contDiffOn_fderiv_apply Complex.I hF.1) he)
      (fun x hx ↦ by
        simpa [maassEigenvalue] using
          fourierCoeff_ode 0 hF.1 (fun _ ↦ comp_add_one_of_mem_maassSpace hF) hF.2.2.2 hx)
      (integrableOn_sq_norm_fourierCoeff_div_sq 0 hF) hy
  simpa using h

/-- **The cosine expansion of an even Maass newform with real spectral parameter** (LMFDB
`mf.maass.mwf.coefficients`): an even Maass newform `F` of weight `0` on `Γ₀(N)` with trivial
character and eigenvalue `1/4 + r²`, `r` real, has the cosine expansion
`F(x + iy) = ∑_{n ≥ 1} a(n) √y K_{ir}(2πny) cos(2πnx)` with the coefficients
`a = maassCoefficients r F`, with no cuspidality or growth hypothesis. -/
lemma IsMaassNewform.hasMaassCosineExpansion_ofReal (hF : IsMaassNewform N 1 (maassEigenvalue r) F)
    (hs : IsEvenMaassForm (F ∘ ofComplex)) :
    HasMaassCosineExpansion (F ∘ ofComplex) r (maassCoefficients r (F ∘ ofComplex)) :=
  hF.hasMaassCosineExpansion_of_integral_eq_zero (fun _ ↦ integral_eq_zero_of_mem_maassSpace hF.1.1)
    hs

/-- **The sine expansion of an odd Maass newform with real spectral parameter** (LMFDB
`mf.maass.mwf.coefficients`): an odd Maass newform `F` of weight `0` on `Γ₀(N)` with trivial
character and eigenvalue `1/4 + r²`, `r` real, has the sine expansion
`F(x + iy) = ∑_{n ≥ 1} a(n) √y K_{ir}(2πny) sin(2πnx)` with the coefficients
`a = maassCoefficients r F`, with no cuspidality or growth hypothesis. -/
lemma IsMaassNewform.hasMaassSineExpansion_ofReal (hF : IsMaassNewform N 1 (maassEigenvalue r) F)
    (hs : IsOddMaassForm (F ∘ ofComplex)) :
    HasMaassSineExpansion (F ∘ ofComplex) r (maassCoefficients r (F ∘ ofComplex)) :=
  hF.hasMaassSineExpansion_of_integral_eq_zero (fun _ ↦ integral_eq_zero_of_mem_maassSpace hF.1.1)
    hs

variable [NeZero N]

/-- **The normalised coefficients of an even Maass newform with real spectral parameter are
real** at the indices prime to the level (LMFDB `mf.maass.mwf.coefficients`): for an even Maass
newform `F` on `Γ₀(N)` with eigenvalue `1/4 + r²`, `r` real, and coefficients
`a = maassCoefficients r F` with `a(1) ≠ 0` (which holds at every level `N ≠ 0`,
`IsMaassNewform.maassCoefficients_one_ne_zero_of_even_ofReal`), `a(m) / a(1)` is real for every `m`
prime to `N`. -/
lemma IsMaassNewform.conj_maassCoefficients_div_of_isEven_ofReal
    (hF : IsMaassNewform N 1 (maassEigenvalue r) F) (hs : IsEvenMaassForm (F ∘ ofComplex))
    (h1 : maassCoefficients r (F ∘ ofComplex) 1 ≠ 0) {m : ℕ+} (hm : (m : ℕ).Coprime N) :
    conj (maassCoefficients r (F ∘ ofComplex) m / maassCoefficients r (F ∘ ofComplex) 1) =
      maassCoefficients r (F ∘ ofComplex) m / maassCoefficients r (F ∘ ofComplex) 1 :=
  hF.conj_coeff_div_of_hasMaassCosineExpansion (hF.hasMaassCosineExpansion_ofReal hs) h1 hm

/-- **The normalised coefficients of an odd Maass newform with real spectral parameter are real**
at the indices prime to the level (LMFDB `mf.maass.mwf.coefficients`): for an odd Maass newform
`F` on `Γ₀(N)` with eigenvalue `1/4 + r²`, `r` real, and coefficients `a = maassCoefficients r F`
with `a(1) ≠ 0` (which holds at every level `N ≠ 0`,
`IsMaassNewform.maassCoefficients_one_ne_zero_of_odd_ofReal`), `a(m) / a(1)` is real for every `m`
prime to `N`. -/
lemma IsMaassNewform.conj_maassCoefficients_div_of_isOdd_ofReal
    (hF : IsMaassNewform N 1 (maassEigenvalue r) F) (hs : IsOddMaassForm (F ∘ ofComplex))
    (h1 : maassCoefficients r (F ∘ ofComplex) 1 ≠ 0) {m : ℕ+} (hm : (m : ℕ).Coprime N) :
    conj (maassCoefficients r (F ∘ ofComplex) m / maassCoefficients r (F ∘ ofComplex) 1) =
      maassCoefficients r (F ∘ ofComplex) m / maassCoefficients r (F ∘ ofComplex) 1 :=
  hF.conj_coeff_div_of_hasMaassSineExpansion (hF.hasMaassSineExpansion_ofReal hs) h1 hm

/-- **An even Maass newform of level `1` with real spectral parameter has `a(1) ≠ 0`**, so that
all the coefficients `a(n) / a(1)` of the normalised newform are real
(`conj_maassCoefficients_div_of_isEven_ofReal`). -/
lemma IsMaassNewform.maassCoefficients_one_ne_zero_of_isEven_ofReal
    (hF : IsMaassNewform 1 1 (maassEigenvalue r) F) (hs : IsEvenMaassForm (F ∘ ofComplex)) :
    maassCoefficients r (F ∘ ofComplex) 1 ≠ 0 :=
  hF.coeff_one_ne_zero_of_hasMaassCosineExpansion (hF.hasMaassCosineExpansion_ofReal hs)

/-- **An odd Maass newform of level `1` with real spectral parameter has `a(1) ≠ 0`**, so that
all the coefficients `a(n) / a(1)` of the normalised newform are real
(`conj_maassCoefficients_div_of_isOdd_ofReal`). -/
lemma IsMaassNewform.maassCoefficients_one_ne_zero_of_isOdd_ofReal
    (hF : IsMaassNewform 1 1 (maassEigenvalue r) F) (hs : IsOddMaassForm (F ∘ ofComplex)) :
    maassCoefficients r (F ∘ ofComplex) 1 ≠ 0 :=
  hF.coeff_one_ne_zero_of_hasMaassSineExpansion (hF.hasMaassSineExpansion_ofReal hs)

end UpperHalfPlane
