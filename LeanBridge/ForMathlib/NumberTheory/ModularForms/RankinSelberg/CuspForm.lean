import LeanBridge.ForMathlib.NumberTheory.ModularForms.RankinSelberg.Parseval
import LeanBridge.ForMathlib.NumberTheory.ModularForms.RankinSelberg.Unfolding
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.DiamondOperators
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# The Rankin–Selberg method for cusp forms, near `σ = 1`

For cusp forms `F ∈ S_k(Γ₁(L), χ₁)` and `G ∈ S_k(Γ₁(L), χ₂)`, this file studies the Rankin–Selberg
integral `I_σ(F, G) = ∫_{strip} F(τ) conj(G(τ)) (Im τ) ^ (k + σ) dμ(τ)` for `σ ∈ (1, 2]`. It equals
the Dirichlet series `∑ a_n(F) conj(a_n(G)) Γ(s) (4 π n) ^ (-s)`, for `s = k + σ - 1`. As `σ → 1⁺`:

* `(σ - 1) I_σ(F, G) → 0` if `χ₁ ≠ χ₂`, as the Petersson integrand then has a nontrivial character;
* `(σ - 1) I_σ(F, F)` stays above a positive constant if `F ≠ 0`.

This is a weak form of the Rankin–Selberg method, with no analytic continuation, functional
equation or Euler product, and with no information on `I_σ(F, G)` when `χ₁ = χ₂` and `F ≠ G`. In
particular it says nothing on the nonvanishing of the Rankin–Selberg `L`-function at `s = 1`.

## Main results

* `RankinSelberg.tendsto_sub_one_mul_integral_stripFun_petersson`: no pole for two forms of
  different nebentypus.
* `RankinSelberg.exists_le_sub_one_mul_re_integral_stripFun_petersson`: a pole for a nonzero form
  against itself.
* `RankinSelberg.eq_of_forall_mul_re_integral_le_norm_integral`: two forms whose Rankin–Selberg
  integrals are comparable have the same nebentypus.
* `RankinSelberg.hasSum_norm_sq_mul_mellinKernel_stripFun`: the Rankin–Selberg integral of a form
  against itself is a Dirichlet series.
* `RankinSelberg.hasSum_coeff_mul_conj_mul_mellinKernel_stripFun`: the Rankin–Selberg integral of
  two forms is a Dirichlet series.
-/

open MeasureTheory UpperHalfPlane Set ModularGroup Matrix SpecialLinearGroup Filter Topology
    CongruenceSubgroup TauCeti ConjAct Subgroup

open scoped ComplexConjugate ModularForm Pointwise

namespace RankinSelberg

variable {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} (W W' : CuspForm Γ k)

lemma one_add_sq_mul_exp_neg_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (1 + x ^ 2) * Real.exp (-(a * x)) ≤ 1 + 2 / a ^ 2 := by
  have hax : 0 ≤ a * x := by positivity
  have h1 : 1 + a * x + (a * x) ^ 2 / 2 ≤ Real.exp (a * x) := Real.quadratic_le_exp_of_nonneg hax
  have hexp : 0 < Real.exp (a * x) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hexp]
  have h2 : (1 + 2 / a ^ 2) * (1 + a * x + (a * x) ^ 2 / 2) ≤ (1 + 2 / a ^ 2) * Real.exp (a * x) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  refine le_trans ?_ h2
  have h3 : (1 + 2 / a ^ 2) * (1 + a * x + (a * x) ^ 2 / 2) = 1 + x ^ 2 + a * x + (a * x) ^ 2 / 2 +
      2 / a ^ 2 * (1 + a * x) := by
    field_simp
    ring1
  rw [h3]
  have h4 : 0 ≤ 2 / a ^ 2 * (1 + a * x) := by positivity
  nlinarith

variable [Γ.IsArithmetic] in
lemma hasDecay_petersson : HasDecay (petersson k W' W) := by
  intro γ
  have hconj : ((toConjAct (γ : GL (Fin 2) ℝ)⁻¹) • Γ).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl)] using! IsArithmetic.conj Γ (mapGL ℚ γ)⁻¹
  rcases (CuspFormClass.zero_at_infty (CuspForm.translate W' γ)).petersson_exp_decay_left k _
    (ModularForm.translate W γ) with ⟨a, ha, hO⟩
  rcases hO.bound with ⟨C₁, hC₁⟩
  rcases (atImInfty_mem _).mp hC₁ with ⟨A, hA⟩
  rcases CuspFormClass.petersson_bounded_left k Γ W' W with ⟨C₂, hC₂⟩
  have hC₂' : ∀ τ, ‖petersson k W' W (γ • τ)‖ ≤ C₂ := fun τ ↦ hC₂ _
  have hslash : ∀ τ, petersson k (CuspForm.translate W' γ) (ModularForm.translate W γ) τ =
      petersson k W' W (γ • τ) := fun τ ↦ petersson_slash_SL k W' W γ τ
  refine ⟨|C₁| * (1 + 2 / a ^ 2) + |C₂| * (1 + A ^ 2), fun τ ↦ ?_⟩
  by_cases hτA : A ≤ τ.im
  · have h1 : ‖petersson k W' W (γ • τ)‖ ≤ C₁ * ‖Real.exp (-a * τ.im)‖ := hslash τ ▸ hA τ hτA
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h1
    have h2 : ‖petersson k W' W (γ • τ)‖ * (1 + τ.im ^ 2) ≤
        |C₁| * ((1 + τ.im ^ 2) * Real.exp (-(a * τ.im))) := by
      have h3 : C₁ * Real.exp (-a * τ.im) ≤ |C₁| * Real.exp (-(a * τ.im)) := by
        rw [neg_mul]
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      refine (mul_le_mul_of_nonneg_right (h1.trans h3) (by positivity)).trans_eq ?_
      ring1
    have h6 : |C₁| * ((1 + τ.im ^ 2) * Real.exp (-(a * τ.im))) ≤ |C₁| * (1 + 2 / a ^ 2) :=
      mul_le_mul_of_nonneg_left (one_add_sq_mul_exp_neg_le ha τ.im_pos) (abs_nonneg C₁)
    have h7 : 0 ≤ |C₂| * (1 + A ^ 2) := by positivity
    linarith
  · have hτ : 0 < τ.im := τ.im_pos
    have hA0 : τ.im < A := not_le.mp hτA
    have h1 : τ.im ^ 2 ≤ A ^ 2 := by nlinarith
    have h2 : ‖petersson k W' W (γ • τ)‖ * (1 + τ.im ^ 2) ≤ |C₂| * (1 + A ^ 2) :=
      mul_le_mul ((hC₂' τ).trans (le_abs_self _)) (by linarith) (by positivity) (abs_nonneg _)
    have h3 : 0 ≤ |C₁| * (1 + 2 / a ^ 2) := by positivity
    linarith

lemma petersson_self_eq (f : ℍ → ℂ) (τ : ℍ) :
    petersson k f f τ = ((‖f τ‖ ^ 2 * τ.im ^ k : ℝ) : ℂ) := by
  rw [petersson_self_eq_ofReal, Complex.normSq_eq_norm_sq]

variable {W} in
lemma exists_mem_fdo_ne_zero (hW : W ≠ 0) : ∃ τ ∈ fdo, W τ ≠ 0 := by
  by_contra hn
  push Not at hn
  have hτ₀ : (⟨⟨0, 2⟩, by norm_num⟩ : ℍ) ∈ fdo := ⟨by norm_num, by norm_num⟩
  have h : (fun τ : ℍ ↦ W τ) = 0 := eq_zero_of_frequently (CuspFormClass.holo W)
    ((eventually_of_mem (isOpen_fdo.mem_nhds hτ₀) hn).filter_mono nhdsWithin_le_nhds).frequently
  exact hW <| DFunLike.coe_injective h

variable {L : ℕ} (χ : (ZMod L)ˣ →* ℂˣ) {χ₁ χ₂ : (ZMod L)ˣ →* ℂˣ} {σ : ℝ}
    {F G : CuspForm ((Gamma1 L).map (mapGL ℝ)) k}

lemma norm_coe_char (u : (ZMod L)ˣ) : ‖(χ u : ℂ)‖ = 1 :=
  (((Units.coeHom ℂ).comp χ).isOfFinOrder (isOfFinOrder_of_finite u)).norm_eq_one

lemma hasNebentypus_petersson (hF : F ∈ cuspFormCharSpace k χ₁) (hG : G ∈ cuspFormCharSpace k χ₂) :
    HasNebentypus (petersson k G F) (χ₁ * χ₂⁻¹) := by
  intro γ u hc hd τ
  let g : Gamma0 L := ⟨γ, Gamma0_mem.mpr hc⟩
  have hg : (Gamma0Map L).toHomUnits g = u := Units.ext (by
    rw [MonoidHom.coe_toHomUnits, Gamma0Map_apply]
    exact hd)
  have h3 : petersson k (⇑G ∣[k] γ) (⇑F ∣[k] γ) τ = petersson k G F (γ • τ) :=
    petersson_slash_SL k G F γ τ
  have h4 : ⇑G ∣[k] γ = (χ₂ u : ℂ) • ⇑G :=
    hg ▸ (mem_cuspFormCharSpace_iff_nebentypus k χ₂ G).mp hG g
  have h5 : ⇑F ∣[k] γ = (χ₁ u : ℂ) • ⇑F :=
    hg ▸ (mem_cuspFormCharSpace_iff_nebentypus k χ₁ F).mp hF g
  rw [← h3, h4, h5]
  simp only [petersson, Pi.smul_apply, smul_eq_mul, map_mul, MonoidHom.mul_apply,
    MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [← Complex.inv_eq_conj (norm_coe_char χ₂ u)]
  ring1

variable [NeZero L]

/-- **Rankin–Selberg for two forms of different nebentypus**: `(σ - 1)` times the Rankin–Selberg
integral of `F ∈ S_k(Γ₁(L), χ₁)` against `G ∈ S_k(Γ₁(L), χ₂)`, `χ₁ ≠ χ₂`, tends to `0` as
`σ → 1⁺`. -/
lemma tendsto_sub_one_mul_integral_stripFun_petersson (hF : F ∈ cuspFormCharSpace k χ₁)
    (hG : G ∈ cuspFormCharSpace k χ₂) (hχ : χ₁ ≠ χ₂) :
    Tendsto (fun σ : ℝ ↦ ((σ - 1 : ℝ) : ℂ) * ∫ τ, stripFun (petersson k G F) σ τ) (𝓝[>] 1) (𝓝 0) :=
  tendsto_sub_one_mul_integral_stripFun (petersson_continuous k (ModularFormClass.continuous G)
    (ModularFormClass.continuous F)) (hasNebentypus_petersson hF hG) (hasDecay_petersson F G)
    fun h1 ↦ hχ (mul_inv_eq_one.mp h1)

variable {χ} in
/-- **Rankin–Selberg for a form against itself**: `(σ - 1)` times the Rankin–Selberg integral of a
nonzero `F ∈ S_k(Γ₁(L), χ)` against itself stays above a positive constant as `σ → 1⁺`. -/
lemma exists_le_sub_one_mul_re_integral_stripFun_petersson (hF : F ∈ cuspFormCharSpace k χ)
    (hF0 : F ≠ 0) :
    ∃ c > 0, ∀ᶠ σ : ℝ in 𝓝[>] 1, c ≤ (σ - 1) * (∫ τ, stripFun (petersson k F F) σ τ).re := by
  rcases exists_mem_fdo_ne_zero hF0 with ⟨τ₀, hτ₀, hne⟩
  have hpet : petersson k F F = fun τ ↦ ((‖F τ‖ ^ 2 * τ.im ^ k : ℝ) : ℂ) :=
    funext (petersson_self_eq F)
  have hpos : 0 < ‖F τ₀‖ ^ 2 * τ₀.im ^ k :=
    mul_pos (pow_pos (norm_pos_iff.mpr hne) 2) (zpow_pos τ₀.im_pos k)
  have hucont : Continuous fun τ : ℍ ↦ ‖F τ‖ ^ 2 * τ.im ^ k :=
    ((ModularFormClass.continuous F).norm.pow 2).mul
      (continuous_im.zpow₀ k fun τ ↦ Or.inl τ.im_ne_zero)
  have hh : HasNebentypus (fun τ ↦ ((‖F τ‖ ^ 2 * τ.im ^ k : ℝ) : ℂ)) (1 : (ZMod L)ˣ →* ℂˣ) :=
    hpet ▸ mul_inv_cancel χ ▸ hasNebentypus_petersson hF hF
  have hdec : HasDecay fun τ ↦ ((‖F τ‖ ^ 2 * τ.im ^ k : ℝ) : ℂ) := hpet ▸ hasDecay_petersson F F
  rw [hpet]
  exact exists_le_sub_one_mul_re_integral_stripFun hucont
    (fun τ ↦ mul_nonneg (by positivity) (zpow_nonneg τ.im_pos.le k)) hh hdec hτ₀ hpos

/-- **Two forms whose Rankin–Selberg integrals are comparable have the same nebentypus**: if
`F ≠ 0` lies in `S_k(Γ₁(L), χ₁)`, `G` lies in `S_k(Γ₁(L), χ₂)` and `δ I_σ(F, F) ≤ |I_σ(F, G)|` for
some `δ > 0` and all `σ ∈ (1, 2]`, then `χ₁ = χ₂`. -/
lemma eq_of_forall_mul_re_integral_le_norm_integral {δ : ℝ} (hδ : 0 < δ)
    (hF : F ∈ cuspFormCharSpace k χ₁) (hG : G ∈ cuspFormCharSpace k χ₂) (hF0 : F ≠ 0)
    (h : ∀ σ ∈ Ioc (1 : ℝ) 2, δ * (∫ τ, stripFun (petersson k F F) σ τ).re ≤
      ‖∫ τ, stripFun (petersson k G F) σ τ‖) : χ₁ = χ₂ := by
  by_contra hne
  rcases exists_le_sub_one_mul_re_integral_stripFun_petersson hF hF0 with ⟨c, hc, hev⟩
  have hsmall :
      ∀ᶠ σ : ℝ in 𝓝[>] 1, ‖((σ - 1 : ℝ) : ℂ) * ∫ τ, stripFun (petersson k G F) σ τ‖ < δ * c :=
    (tendsto_sub_one_mul_integral_stripFun_petersson hF hG hne).norm.eventually
      (by simpa using gt_mem_nhds (mul_pos hδ hc))
  rcases (hsmall.and (hev.and (Ioc_mem_nhdsGT one_lt_two))).exists with ⟨σ, h1, h2, hσ⟩
  have hσ1 : 0 ≤ σ - 1 := sub_nonneg.mpr hσ.1.le
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ1] at h1
  have h3 : (σ - 1) * (δ * (∫ τ, stripFun (petersson k F F) σ τ).re) ≤
      (σ - 1) * ‖∫ τ, stripFun (petersson k G F) σ τ‖ :=
    mul_le_mul_of_nonneg_left (h σ hσ) hσ1
  have h4 : δ * c ≤ δ * ((σ - 1) * (∫ τ, stripFun (petersson k F F) σ τ).re) :=
    mul_le_mul_of_nonneg_left h2 hδ.le
  linarith

variable (F G) in
lemma integrable_stripFun_petersson (hσ : σ ∈ Ioc (1 : ℝ) 2) :
    Integrable (stripFun (petersson k G F) σ) :=
  integrable_stripFun_of_hasDecay (petersson_continuous k (ModularFormClass.continuous G)
    (ModularFormClass.continuous F)) (hasDecay_petersson F G) hσ

variable (F) in
/-- **The Rankin–Selberg integral of a form against itself is a Dirichlet series.** -/
lemma hasSum_norm_sq_mul_mellinKernel_stripFun (hσ : σ ∈ Ioc (1 : ℝ) 2) (hs : 0 < (k : ℝ) + σ - 1) :
    HasSum (fun n : ℕ ↦
      ((‖(qExpansion 1 F).coeff n‖ ^ 2 * mellinKernel ((k : ℝ) + σ - 1) n : ℝ) : ℂ))
      (∫ τ, stripFun (petersson k F F) σ τ) := by
  have hint : Integrable (stripFun (petersson k F F) σ) := integrable_stripFun_petersson F F hσ
  have hinner : ∀ y ∈ Ioi (0 : ℝ), (∫ x in Ico (0 : ℝ) 1, (y ^ 2)⁻¹ •
      (petersson k F F (coordPoint (x, y)) * ((y ^ σ : ℝ) : ℂ))) =
      ((y ^ ((k : ℝ) + σ - 1 - 1) *
        ∫ x in Ico (0 : ℝ) 1, ‖F (coordPoint (x, y))‖ ^ 2 : ℝ) : ℂ) := by
    intro y hy
    have hy' : 0 < y := hy
    have hpow : y ^ ((k : ℝ) + σ - 1 - 1) = (y ^ 2)⁻¹ * y ^ k * y ^ σ := by
      rw [Real.rpow_sub_one hy'.ne', Real.rpow_sub_one hy'.ne', Real.rpow_add hy',
        Real.rpow_intCast]
      field_simp
    rw [← integral_const_mul, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ico fun x _ ↦ ?_
    have him : (coordPoint (x, y)).im = y := coordPoint_im hy'
    simp only [petersson_self_eq, him]
    rw [hpow, Complex.real_smul]
    push_cast
    ring1
  have hreal : IntegrableOn (fun y : ℝ ↦ y ^ ((k : ℝ) + σ - 1 - 1) *
      ∫ x in Ico (0 : ℝ) 1, ‖F (coordPoint (x, y))‖ ^ 2) (Ioi 0) := by
    simpa using ((integrableOn_integral_stripFun hint).congr_fun hinner measurableSet_Ioi).re
  rw [integral_stripFun_eq hint, setIntegral_congr_fun measurableSet_Ioi hinner,
    integral_complex_ofReal]
  exact Complex.hasSum_ofReal.mpr
    (hasSum_norm_sq_mul_mellinKernel F (one_mem_strictPeriods_Gamma1_map L) hs hreal)

lemma conj_mul_eq_polarization (a b : ℂ) : conj b * a = (1 / 4 : ℂ) * (((‖a + b‖ ^ 2 : ℝ) : ℂ) -
    ((‖a - b‖ ^ 2 : ℝ) : ℂ) + Complex.I * ((‖a + Complex.I * b‖ ^ 2 : ℝ) : ℂ) -
      Complex.I * ((‖a - Complex.I * b‖ ^ 2 : ℝ) : ℂ)) := by
  simp only [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, map_add, map_sub, map_mul,
    Complex.conj_I]
  linear_combination (1 / 2 : ℂ) * (conj b * a - conj a * b) * Complex.I_sq

variable (F G) in
/-- **The Rankin–Selberg integral of two forms is a Dirichlet series**:
`∫_{strip} F(τ) conj(G(τ)) (Im τ) ^ (k + σ) dμ(τ) = ∑ a_n(F) conj(a_n(G)) Γ(s) (4 π n) ^ (-s)` for
`s = k + σ - 1`. -/
lemma hasSum_coeff_mul_conj_mul_mellinKernel_stripFun (hσ : σ ∈ Ioc (1 : ℝ) 2)
    (hs : 0 < (k : ℝ) + σ - 1) :
    HasSum (fun n : ℕ ↦ (qExpansion 1 F).coeff n * conj ((qExpansion 1 G).coeff n) *
      (mellinKernel ((k : ℝ) + σ - 1) n : ℂ)) (∫ τ, stripFun (petersson k G F) σ τ) := by
  have hΓ : (1 : ℝ) ∈ ((Gamma1 L).map (mapGL ℝ)).strictPeriods := one_mem_strictPeriods_Gamma1_map L
  let W₁ : CuspForm ((Gamma1 L).map (mapGL ℝ)) k := F + G
  let W₂ : CuspForm ((Gamma1 L).map (mapGL ℝ)) k := F - G
  let W₃ : CuspForm ((Gamma1 L).map (mapGL ℝ)) k := F + Complex.I • G
  let W₄ : CuspForm ((Gamma1 L).map (mapGL ℝ)) k := F - Complex.I • G
  have hc : ∀ (n : ℕ) (W : CuspForm ((Gamma1 L).map (mapGL ℝ)) k),
      CuspForm.qExpansionCoeffₗ one_pos hΓ k n W = (qExpansion 1 W).coeff n := fun n W ↦
    CuspForm.qExpansionCoeffₗ_apply one_pos hΓ n W
  have hc₁ : ∀ n, (qExpansion 1 W₁).coeff n = (qExpansion 1 F).coeff n + (qExpansion 1 G).coeff n :=
    fun n ↦ by simp only [W₁, ← hc, map_add]
  have hc₂ : ∀ n, (qExpansion 1 W₂).coeff n = (qExpansion 1 F).coeff n - (qExpansion 1 G).coeff n :=
    fun n ↦ by simp only [W₂, ← hc, map_sub]
  have hc₃ : ∀ n, (qExpansion 1 W₃).coeff n = (qExpansion 1 F).coeff n +
      Complex.I * (qExpansion 1 G).coeff n :=
    fun n ↦ by simp only [W₃, ← hc, map_add, map_smul, smul_eq_mul]
  have hc₄ : ∀ n, (qExpansion 1 W₄).coeff n = (qExpansion 1 F).coeff n -
      Complex.I * (qExpansion 1 G).coeff n :=
    fun n ↦ by simp only [W₄, ← hc, map_sub, map_smul, smul_eq_mul]
  have hS : ∀ W : CuspForm ((Gamma1 L).map (mapGL ℝ)) k, HasSum
      (fun n : ℕ ↦ ((‖(qExpansion 1 W).coeff n‖ ^ 2 * mellinKernel ((k : ℝ) + σ - 1) n : ℝ) : ℂ))
      (∫ τ, stripFun (petersson k W W) σ τ) := fun W ↦
    hasSum_norm_sq_mul_mellinKernel_stripFun W hσ hs
  have hfun : stripFun (petersson k G F) σ = fun τ ↦ (1 / 4 : ℂ) *
      (stripFun (petersson k W₁ W₁) σ τ - stripFun (petersson k W₂ W₂) σ τ +
        Complex.I * stripFun (petersson k W₃ W₃) σ τ -
        Complex.I * stripFun (petersson k W₄ W₄) σ τ) := by
    funext τ
    by_cases hτ : τ ∈ strip
    · simp only [stripFun, indicator_of_mem hτ, petersson_self_eq]
      have hval₁ : W₁ τ = F τ + G τ := rfl
      have hval₂ : W₂ τ = F τ - G τ := rfl
      have hval₃ : W₃ τ = F τ + Complex.I * G τ := rfl
      have hval₄ : W₄ τ = F τ - Complex.I * G τ := rfl
      rw [hval₁, hval₂, hval₃, hval₄]
      simp only [petersson]
      rw [conj_mul_eq_polarization (F τ) (G τ)]
      push_cast
      ring1
    · simp only [stripFun, indicator_of_notMem hτ]
      ring1
  have hI :
      ∀ W : CuspForm ((Gamma1 L).map (mapGL ℝ)) k, Integrable (stripFun (petersson k W W) σ) :=
    fun W ↦ integrable_stripFun_petersson W W hσ
  have hA :
      Integrable fun τ ↦ stripFun (petersson k W₁ W₁) σ τ - stripFun (petersson k W₂ W₂) σ τ :=
    (hI W₁).sub (hI W₂)
  have hB : Integrable fun τ ↦ stripFun (petersson k W₁ W₁) σ τ - stripFun (petersson k W₂ W₂) σ τ +
      Complex.I * stripFun (petersson k W₃ W₃) σ τ :=
    hA.add <| (hI W₃).const_mul _
  have hval : ∫ τ, stripFun (petersson k G F) σ τ = (1 / 4 : ℂ) *
      ((∫ τ, stripFun (petersson k W₁ W₁) σ τ) - (∫ τ, stripFun (petersson k W₂ W₂) σ τ) +
        Complex.I * (∫ τ, stripFun (petersson k W₃ W₃) σ τ) -
        Complex.I * ∫ τ, stripFun (petersson k W₄ W₄) σ τ) := by
    rw [hfun, integral_const_mul, integral_sub hB ((hI W₄).const_mul _),
      integral_add hA ((hI W₃).const_mul _), integral_sub (hI W₁) (hI W₂), integral_const_mul,
      integral_const_mul]
  rw [hval]
  refine (((((hS W₁).sub (hS W₂)).add ((hS W₃).mul_left Complex.I)).sub
    ((hS W₄).mul_left Complex.I)).mul_left (1 / 4 : ℂ)).congr_fun fun n ↦ ?_
  rw [hc₁, hc₂, hc₃, hc₄, mul_comm ((qExpansion 1 F).coeff n),
    conj_mul_eq_polarization ((qExpansion 1 F).coeff n) ((qExpansion 1 G).coeff n)]
  push_cast
  ring1

end RankinSelberg
