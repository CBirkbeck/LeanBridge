import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.PoincareSpan
import TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex
import TauCeti.NumberTheory.ModularForms.SturmBound

/-!
# Poincaré series span the cusp forms of trivial multiplier

Let `G` be a subgroup of finite index of `SL(2, ℤ)`, `k ≥ 3` an integral weight, and
`s = γ_s ∞` a cusp of `G` of width `w`: some `t ∈ G` has `γ_s⁻¹ t γ_s = ±T^w`, and `w` divides
the translation of every `γ_s⁻¹ h γ_s = ±T^b`, `h ∈ G_s`. For the trivial multiplier, with
`(±1)^k = 1` on `G_s` (`k` even at an irregular cusp, or when `-I ∈ G`), the `m`-th Poincaré
series `P_m` at `s` (LMFDB `specialfunction.poincare`) is a cusp form of weight `k` on `G` for
`m ≥ 1` (`ModularForm.poincareCuspForm`), and this file proves, with no further hypothesis, that
these Poincaré series span the space `S_k(G)` of cusp forms. The general spanning theorem
`ModularForm.span_poincareSeries_eq_multiplierCuspSpace` needs three facts about the cusp forms,
which hold for the trivial multiplier:

* `S_k(G)` is finite-dimensional, by Tau Ceti's `TauCeti.finiteDimensional_cuspForm_finiteIndex`
  (the instance `FiniteDimensional ℂ (multiplierCuspSpace k (multiplierMapGL 1))`);
* every `f ∈ S_k(G)` has a Fourier expansion `(f ∣[k] γ_s)(z) = Σ_{j ≥ 0} a_j e^{2πi j z / w}`
  without constant term: `f ∣[k] γ_s` is holomorphic, tends to `0` at `i∞` (Mathlib's
  `CuspFormClass.zero_at_infty_slash`) and has period `w`, since `f ∣[k] t = (±1)^k f` for
  `γ_s⁻¹ t γ_s = ±T^w`, so Mathlib's `q`-expansion in `q = e^{2πi z / w}` applies; the `a_j` are
  the coefficients of `UpperHalfPlane.qExpansion w (f ∣[k] γ_s)`. This holds for any function
  with these three properties, also with a multiplier `v` with `v(t) = (±1)^k`
  (`PoincareSpanFiniteOrder.lean`);
* the Petersson integrands are integrable: on the strip `{0 ≤ Re z < w}`, against
  `e^{2πi m z / w}`, since `y^{k/2} |(f ∣[k] γ_s)(z)|` is bounded (Mathlib's
  `CuspFormClass.petersson_bounded_left`) and `y^{k/2 - 2} e^{-2π m y / w}` is integrable on
  `(0, ∞)` for `k ≥ 3`; and on Tau Ceti's fundamental domain
  `⋃_{q ∈ SL(2, ℤ) / ±G} q⁻¹ 𝒟ᵒ`, which has finite measure, by Tau Ceti's
  `UpperHalfPlane.integrableOn_petersson_of_measure_lt_top`.

With them, the unfolding of `PoincareUnfolding.lean` computes the Petersson product of `P_m`
with a cusp form as a multiple of its `m`-th Fourier coefficient at `s`.

## Main results

* `UpperHalfPlane.integrableOn_petersson_exp_re_mem_Ico`: if `|F(z)| ≤ C y^{-k/2}` with `k ≥ 3`,
  then `conj(e^{2πi m z / w}) F(z) y^k` is integrable on the strip `{0 ≤ Re z < w}`.
* `ModularForm.hasSum_qExpansion_slash`, `ModularForm.qExpansion_slash_coeff_zero`: the Fourier
  expansion at `s`, without constant term, of a function `F` with `F ∣[k] t = (±1)^k F` and
  `F ∣[k] γ_s` holomorphic and tending to `0` at `i∞`, such as a cusp form.
* `ModularForm.peterssonInner_poincareSeries_one_eq`: the Petersson product of `P_m` with a cusp
  form `f` is `w (w / 4πm)^{k-1} Γ(k - 1)` times the `m`-th coefficient of the `q`-expansion of
  `f ∣[k] γ_s`.
* `ModularForm.span_poincareSeries_one_eq_multiplierCuspSpace`,
  `ModularForm.span_range_poincareCuspForm_eq_top`: the Poincaré series `P_m`, `m ≥ 1`, span the
  cusp forms of weight `k ≥ 3` on `G`.
-/

open UpperHalfPlane Matrix SpecialLinearGroup ModularGroup MeasureTheory Set Function

open scoped MatrixGroups ComplexConjugate ModularForm Manifold Pointwise

namespace UpperHalfPlane

variable {w n : ℕ} {k : ℤ} {F : ℍ → ℂ} {C : ℝ}

/-- **Petersson integrands of slowly growing functions are integrable on a vertical strip**: if
`F` is continuous with `|F(z)| ≤ C y^{-k/2}` on `ℍ`, `k ≥ 3`, `n ≥ 1` and `w ≥ 1`, then
`conj(e^{2πi n z / w}) F(z) y^k` is integrable on `{0 ≤ Re z < w}` for the invariant measure, being
bounded by `C e^{-2π n y / w} y^{k/2}` there, and `y^{k/2 - 2} e^{-2π n y / w}` is integrable on
`(0, ∞)`. Cusp forms satisfy the bound (`CuspFormClass.exists_bound`). -/
lemma integrableOn_petersson_exp_re_mem_Ico (hw : 0 < w) (hn : 0 < n) (hk : 3 ≤ k)
    (hF : Continuous F) (hC : ∀ z : ℍ, ‖F z‖ ≤ C / z.im ^ ((k : ℝ) / 2)) : IntegrableOn
    (petersson k (fun z : ℍ ↦ Complex.exp (2 * Real.pi * Complex.I * (n / w) * z)) F)
      {z : ℍ | z.re ∈ Ico 0 (w : ℝ)} := by
  have hb : 0 < 2 * Real.pi * (n / w) := by positivity
  have hs : -1 < (k : ℝ) / 2 - 2 := by
    have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hg : IntegrableOn (fun z : ℍ ↦ ((C * (Real.exp (-(2 * Real.pi * (n / w) * z.im)) *
      z.im ^ ((k : ℝ) / 2)) : ℝ) : ℂ)) {z : ℍ | z.re ∈ Ico 0 (w : ℝ)} := by
    rw [integrableOn_re_mem_Ico_iff]
    refine IntegrableOn.congr_fun (f := fun p : ℝ × ℝ ↦ ((C * (p.2 ^ ((k : ℝ) / 2 - 2) *
      Real.exp (-(2 * Real.pi * (n / w)) * p.2 ^ (1 : ℝ))) : ℝ) : ℂ)) ?_ ?_
      (measurableSet_Ico.prod measurableSet_Ioi)
    · rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
      exact (((integrableOn_rpow_mul_exp_neg_mul_rpow hs one_pos hb).const_mul C).ofReal
        (𝕜 := ℂ)).comp_snd _
    · rintro ⟨x, y⟩ ⟨-, hy⟩
      have hy0 : 0 < y := hy
      have hi : (ofComplex (x + y * Complex.I)).im = y := by
        rw [ofComplex_apply_of_im_pos (by simpa using hy0)]
        simp
      simp only [hi, Real.rpow_one, Real.rpow_sub hy0, Real.rpow_two, Complex.real_smul]
      push_cast
      field_simp
  refine Integrable.mono hg ((petersson_continuous k (by fun_prop) hF).aestronglyMeasurable)
    (ae_of_all _ fun z ↦ ?_)
  have hy : 0 < z.im := z.im_pos
  have h1 : ‖F z‖ * z.im ^ ((k : ℝ) / 2) ≤ C :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hy _)).mp (hC z)
  have hnorm : ‖petersson k (fun z : ℍ ↦ Complex.exp (2 * Real.pi * Complex.I * (n / w) * z)) F z‖ =
      Real.exp (-(2 * Real.pi * (n / w) * z.im)) * ‖F z‖ *
          (z.im ^ ((k : ℝ) / 2) * z.im ^ ((k : ℝ) / 2)) := by
    rw [← Real.rpow_add hy, add_halves, Real.rpow_intCast, petersson, norm_mul, norm_mul,
      Complex.norm_conj, Complex.norm_exp]
    simp [abs_of_pos hy]
  rw [hnorm, Complex.norm_real, Real.norm_eq_abs]
  refine le_trans ?_ (le_abs_self _)
  linarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg (Real.exp_pos
    (-(2 * Real.pi * (n / w) * z.im))).le (Real.rpow_nonneg hy.le ((k : ℝ) / 2)))]

end UpperHalfPlane

namespace ModularGroup

lemma volume_iUnion_out_inv_smul_fdo_lt_top (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    volume (⋃ q : SL(2, ℤ) ⧸ Γ.withCenter, (q.out : SL(2, ℤ))⁻¹ • fdo) < ⊤ :=
  (measure_iUnion_fintype_le _ _).trans_lt <| ENNReal.sum_lt_top.mpr fun q _ ↦ by
    rw [measure_smul]
    exact (measure_congr fd_ae_eq_fdo).symm.trans_lt volume_fd_lt_top

end ModularGroup

namespace ModularForm

variable {G : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ)) {k : ℤ} {w m : ℕ} {t : G} {F : ℍ → ℂ}
    (f : CuspForm (G.map (mapGL ℝ)) k)

lemma mem_multiplierCuspSpace_multiplierMapGL_one_iff : F ∈ multiplierCuspSpace k
    (multiplierMapGL (1 : G →* Circle)) ↔ ∃ g : CuspForm (G.map (mapGL ℝ)) k, ⇑g = F := by
  rw [multiplierMapGL, MonoidHom.one_comp, mem_multiplierCuspSpace_one_iff]

lemma periodic_slash_comp_ofComplex
    (hF : F ∣[k] (t : SL(2, ℤ)) = ((γ⁻¹ * (t : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k • F)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ)) :
    Periodic ((F ∣[k] γ) ∘ ofComplex) (w : ℝ) := by
  refine periodic_comp_ofComplex fun τ ↦ ?_
  have h1 : (F ∣[k] γ) ∣[k] (γ⁻¹ * (t : SL(2, ℤ)) * γ) =
      ((γ⁻¹ * (t : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k • F ∣[k] γ := by
    rw [← SlashAction.slash_mul, ← mul_assoc, mul_inv_cancel_left, SlashAction.slash_mul, hF,
      SL_smul_slash]
  have hsmul : (γ⁻¹ * (t : SL(2, ℤ)) * γ) • τ = (w : ℝ) +ᵥ τ := by
    rcases ht with h | h <;> rw [h] <;> simpa using modular_T_zpow_smul τ w
  have hden :
      denom (γ⁻¹ * (t : SL(2, ℤ)) * γ : SL(2, ℤ)) τ = ((γ⁻¹ * (t : SL(2, ℤ)) * γ) 1 1 : ℂ) := by
    rw [ModularGroup.denom_apply,
      (mem_cuspStabilizer_iff γ).mp (mem_cuspStabilizer_of_eq_T_zpow γ w ht)]
    simp
  have hd :
      ((γ⁻¹ * (t : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k * ((γ⁻¹ * (t : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k = 1 := by
    rw [← mul_zpow]
    rcases ht with h | h
    · rw [h, coe_T_zpow]
      simp
    · rw [h, SpecialLinearGroup.coe_neg, coe_T_zpow]
      simp
  have h2 : ((F ∣[k] γ) ∣[k] (γ⁻¹ * (t : SL(2, ℤ)) * γ)) τ =
      ((γ⁻¹ * (t : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k * (F ∣[k] γ) τ := congrFun h1 τ
  rw [SL_slash_apply, hsmul, hden, zpow_neg (_ : ℂ) k, inv_eq_of_mul_eq_one_right hd] at h2
  exact mul_right_cancel₀ (left_ne_zero_of_mul_eq_one hd) (h2.trans (mul_comm _ _))

/-- **The Fourier expansion at a cusp** (LMFDB `specialfunction.poincare`): let `s = γ_s ∞` be a
cusp of width `w ≥ 1` (some `t ∈ G` has `γ_s⁻¹ t γ_s = ±T^w`) and `F` a function with
`F ∣[k] t = (±1)^k F`, `F ∣[k] γ_s` holomorphic and tending to `0` at `i∞` (a cusp form of weight
`k` on `G`, with a multiplier `v` with `v(t) = (±1)^k`). Then `F ∣[k] γ_s` has period `w` and
`(F ∣[k] γ_s)(z) = Σ_{j ≥ 0} a_j e^{2πi j z / w}` on `ℍ`, where the `a_j` are the coefficients of
its `q`-expansion in `q = e^{2πi z / w}`. -/
lemma hasSum_qExpansion_slash (hw₀ : 0 < w)
    (hF : F ∣[k] (t : SL(2, ℤ)) = ((γ⁻¹ * (t : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k • F)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ))
    (hFhol : MDiff (F ∣[k] γ)) (hFzero : IsZeroAtImInfty (F ∣[k] γ)) (z : ℍ) : HasSum
    (fun j : ℕ ↦ (qExpansion w (F ∣[k] γ)).coeff j *
      Complex.exp (2 * Real.pi * Complex.I * (j / w) * z)) ((F ∣[k] γ) z) := by
  have he (j : ℕ) :
      Periodic.qParam w z ^ j = Complex.exp (2 * Real.pi * Complex.I * (j / w) * z) := by
    rw [Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring1
  simpa only [smul_eq_mul, he] using UpperHalfPlane.hasSum_qExpansion (by exact_mod_cast hw₀)
    (periodic_slash_comp_ofComplex γ hF ht) hFhol hFzero.isBoundedAtImInfty z

/-- **No constant term at a cusp** (LMFDB `specialfunction.poincare`): under the hypotheses of
`hasSum_qExpansion_slash`, the constant coefficient `a_0` of the expansion of `F ∣[k] γ_s`
vanishes, its value at `i∞`. -/
lemma qExpansion_slash_coeff_zero (hw₀ : 0 < w)
    (hF : F ∣[k] (t : SL(2, ℤ)) = ((γ⁻¹ * (t : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k • F)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ))
    (hFhol : MDiff (F ∣[k] γ)) (hFzero : IsZeroAtImInfty (F ∣[k] γ)) :
    (qExpansion w (F ∣[k] γ)).coeff 0 = 0 := by
  have hpos : (0 : ℝ) < w := by exact_mod_cast hw₀
  have hper : Periodic ((F ∣[k] γ) ∘ ofComplex) (w : ℝ) := periodic_slash_comp_ofComplex γ hF ht
  rw [qExpansion_coeff_zero hpos (analyticAt_cuspFunction_zero hpos hper hFhol
    hFzero.isBoundedAtImInfty) hper]
  exact hFzero.valueAtInfty_eq_zero

lemma slash_coe_eq (g : G) : ⇑f ∣[k] (g : SL(2, ℤ)) = ⇑f :=
  SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ g.2)

lemma mdifferentiable_slash : MDiff (⇑f ∣[k] γ) :=
  (ModularFormClass.holo f).slash k (mapGL ℝ γ)

lemma slash_eq_smul_of_pow_eq_one (hv : ((γ⁻¹ * (t : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k = 1) :
    ⇑f ∣[k] (t : SL(2, ℤ)) = ((γ⁻¹ * (t : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k • ⇑f := by
  rw [hv, one_smul]
  exact slash_coe_eq f t

variable [G.FiniteIndex]

instance : FiniteDimensional ℂ (multiplierCuspSpace k (multiplierMapGL (1 : G →* Circle))) :=
  FiniteDimensional.of_surjective
    ({ toFun := fun f ↦ ⟨⇑f, mem_multiplierCuspSpace_multiplierMapGL_one_iff.mpr ⟨f, rfl⟩⟩
       map_add' := fun _ _ ↦ rfl
       map_smul' := fun _ _ ↦ rfl } : CuspForm (G.map (mapGL ℝ)) k →ₗ[ℂ]
        multiplierCuspSpace k (multiplierMapGL (1 : G →* Circle)))
    fun f ↦ (mem_multiplierCuspSpace_multiplierMapGL_one_iff.mp f.2).imp fun _ hg ↦ Subtype.ext hg

lemma exists_norm_slash_le : ∃ C : ℝ, ∀ z : ℍ, ‖(⇑f ∣[k] γ) z‖ ≤ C / z.im ^ ((k : ℝ) / 2) := by
  rcases CuspFormClass.petersson_bounded_left k _ f f with ⟨C, hC⟩
  refine ⟨C.sqrt, fun z ↦ (le_div_iff₀ (by positivity)).mpr (Real.le_sqrt_of_sq_le ?_)⟩
  have hy : 0 < z.im := z.im_pos
  have h : ‖petersson k (⇑f ∣[k] γ) (⇑f ∣[k] γ) z‖ ≤ C := by
    rw [petersson_slash_SL]
    exact hC _
  simpa [petersson, abs_of_pos hy, ← Real.rpow_mul_natCast hy.le, field] using h

lemma integrableOn_petersson_exp_slash (hw₀ : 0 < w) (hm : 0 < m) (hk : 3 ≤ k) : IntegrableOn
    (petersson k (fun u : ℍ ↦ Complex.exp (2 * Real.pi * Complex.I * (m / w) * u)) (⇑f ∣[k] γ))
      {z : ℍ | z.re ∈ Ico 0 (w : ℝ)} :=
  (exists_norm_slash_le γ f).elim fun _ ↦
    integrableOn_petersson_exp_re_mem_Ico hw₀ hm hk (mdifferentiable_slash γ f).continuous

/-- **The Petersson product of a Poincaré series with a cusp form** (LMFDB
`specialfunction.poincare`): for `G` of finite index, the trivial multiplier, `k ≥ 3`, `m ≥ 1`,
`s = γ_s ∞` a cusp of width `w` (some `t ∈ G` has `γ_s⁻¹ t γ_s = ±T^w`, and `w` divides the
translations of the `γ_s⁻¹ h γ_s = ±T^b`, `h ∈ G_s`) with `(±1)^k = 1` on `G_s`, and `D` a
fundamental domain for the image of `G` in `PSL(2, ℤ)`, the Petersson product
`⟨P_m, f⟩ = ∫_D conj(P_m) f y^k dμ` of the `m`-th Poincaré series at `s` with a cusp form `f` is
`w (w / 4πm)^{k-1} Γ(k - 1) a_m`, where `a_m` is the `m`-th coefficient of the `q`-expansion of
`f ∣[k] γ_s` in `q = e^{2πi z / w}`. -/
lemma peterssonInner_poincareSeries_one_eq (hw₀ : 0 < w) (hm : 0 < m) (hk : 3 ≤ k) {D : Set ℍ}
    (hD : IsFundamentalDomain (G.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) D volume)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ))
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k = 1) :
    peterssonInner k D (poincareSeries γ (1 : G →* Circle) k m w) f =
      (w * (w / (4 * Real.pi * m)) ^ ((k : ℝ) - 1) * Real.Gamma (k - 1) : ℝ) *
          (qExpansion w (⇑f ∣[k] γ)).coeff m :=
  setIntegral_petersson_poincareSeries_eq_psl γ 1 k w m hw₀ hm (by omega) hD ht hw
    (fun h hh ↦ (hv h hh).symm ▸ rfl) (fun g ↦ (slash_coe_eq f g).trans (one_smul ℂ _).symm)
    (hasSum_qExpansion_slash γ hw₀
      (slash_eq_smul_of_pow_eq_one γ f (hv t (mem_cuspStabilizer_of_eq_T_zpow γ w ht))) ht
        (mdifferentiable_slash γ f) (CuspFormClass.zero_at_infty_slash f γ))
    (integrableOn_petersson_exp_slash γ f hw₀ hm hk)

/-- **Poincaré series span the cusp forms** (LMFDB `specialfunction.poincare`), for the trivial
multiplier: for `G` of finite index in `SL(2, ℤ)`, `k ≥ 3`, and `s = γ_s ∞` a cusp of width `w`
(some `t ∈ G` has `γ_s⁻¹ t γ_s = ±T^w`, and `w` divides the translations of the
`γ_s⁻¹ h γ_s = ±T^b`, `h ∈ G_s`) with `(±1)^k = 1` on `G_s`, the Poincaré series `P_m`, `m ≥ 1`,
at `s` span the space `S_k(G)` of cusp forms of weight `k` on `G`, as functions on `ℍ`. -/
lemma span_poincareSeries_one_eq_multiplierCuspSpace (hw₀ : 0 < w) (hk : 3 ≤ k)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ))
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k = 1) :
    Submodule.span ℂ {P | ∃ m : ℕ, 0 < m ∧ poincareSeries γ (1 : G →* Circle) k m w = P} =
      multiplierCuspSpace k (multiplierMapGL (1 : G →* Circle)) := by
  refine span_poincareSeries_eq_multiplierCuspSpace γ 1 k w hw₀ hk
    (isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter G) ht hw
    (fun h hh ↦ (hv h hh).symm ▸ rfl) (fun f hf ↦ ?_) (fun f hf m hm ↦ ?_) (fun f hf g hg ↦ ?_) <;>
    rcases mem_multiplierCuspSpace_multiplierMapGL_one_iff.mp hf with ⟨f, rfl⟩
  · have hF : ⇑f ∣[k] (t : SL(2, ℤ)) = ((γ⁻¹ * (t : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k • ⇑f :=
      slash_eq_smul_of_pow_eq_one γ f (hv t (mem_cuspStabilizer_of_eq_T_zpow γ w ht))
    have hFhol : MDiff (⇑f ∣[k] γ) := mdifferentiable_slash γ f
    have hFzero : IsZeroAtImInfty (⇑f ∣[k] γ) := CuspFormClass.zero_at_infty_slash f γ
    exact ⟨_, qExpansion_slash_coeff_zero γ hw₀ hF ht hFhol hFzero,
      hasSum_qExpansion_slash γ hw₀ hF ht hFhol hFzero⟩
  · exact integrableOn_petersson_exp_slash γ f hw₀ hm hk
  · rcases mem_multiplierCuspSpace_multiplierMapGL_one_iff.mp hg with ⟨g, rfl⟩
    exact integrableOn_petersson_of_measure_lt_top k _ _ f g volume
      (volume_iUnion_out_inv_smul_fdo_lt_top G)

/-- **Poincaré series span the cusp forms** (LMFDB `specialfunction.poincare`), as Mathlib cusp
forms: under the hypotheses of `span_poincareSeries_one_eq_multiplierCuspSpace`, the Poincaré
series `P_m`, `m ≥ 1`, at `s`, as cusp forms of weight `k` on `G` (`ModularForm.poincareCuspForm`),
span the space `CuspForm (G.map (mapGL ℝ)) k` of these cusp forms. -/
lemma span_range_poincareCuspForm_eq_top (hk : 3 ≤ k) (hw₀ : 0 < w)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ))
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k = 1) : Submodule.span ℂ
    (range fun m : ℕ+ ↦ poincareCuspForm γ hk (Int.natCast_pos.mpr m.pos) hw₀ hw hv) = ⊤ := by
  let ι : CuspForm (G.map (mapGL ℝ)) k →ₗ[ℂ] ℍ → ℂ :=
    { toFun := (⇑)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hι : Injective ι := DFunLike.coe_injective
  have hrange : LinearMap.range ι = multiplierCuspSpace k (multiplierMapGL (1 : G →* Circle)) :=
    Submodule.ext fun _ ↦ mem_multiplierCuspSpace_multiplierMapGL_one_iff.symm
  refine Submodule.map_injective_of_injective hι ?_
  rw [Submodule.map_span, Submodule.map_top, hrange,
    ← span_poincareSeries_one_eq_multiplierCuspSpace γ hw₀ hk ht hw hv]
  congr 1
  ext P
  refine ⟨?_, fun ⟨m, hm, hP⟩ ↦ ⟨_, ⟨⟨m, hm⟩, rfl⟩, hP⟩⟩
  rintro ⟨_, ⟨m, rfl⟩, rfl⟩
  exact ⟨m, m.pos, rfl⟩

end ModularForm
