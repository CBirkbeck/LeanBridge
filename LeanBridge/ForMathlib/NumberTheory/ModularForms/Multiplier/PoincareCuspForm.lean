import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.CuspForm
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.PoincareConvergence

/-!
# Poincaré series are cusp forms

The `n`-th Poincaré series of weight `k` and multiplier `v` on `G ≤ SL(2, ℤ)` at the cusp
`s = γ_s ∞` of width `w` (LMFDB `specialfunction.poincare`) is
`P(z) = Σ_{g ∈ G_s \ G} conj(v(g)) e^{2πi (n/w) γ_s⁻¹ g z} j(γ_s⁻¹ g, z)^{-k}`
(`ModularForm.poincareSeries`). This file proves that for `k ≥ 3` and `n ≥ 1` it is a cusp form of
weight `k` and multiplier `v` on `G`.

* The transformation law `P ∣[k] g = v(g) P` for `g ∈ G` holds as soon as the terms are constant on
  the cosets `G_s g'` (`w` divides the translations of the `γ_s⁻¹ h γ_s = ±T^b`, `h ∈ G_s`, and
  `v(h) = (±1)^k` there): `P(gz) j(g, z)^{-k}` is `v(g)` times the sum of the terms at the
  `g' g`, and right multiplication by `g` permutes the cosets.
* Vanishing at the cusps: for every `δ ∈ SL(2, ℤ)`, `P ∣[k] δ` is the sum over the cosets of
  `conj(v(g)) e^{2πi (n/w) M z} j(M, z)^{-k}` with `M = γ_s⁻¹ g δ`, whose bottom rows `(c, d)` are
  distinct. On the strip `|Re z| ≤ 1/2`, `Im z ≥ 1`, a term with `c = 0` (so `d = ±1`) has modulus
  `e^{-2π n y / w}`, and one with `c ≠ 0` at most `|cz + d|^{-k} ≤ y^{-1/2} r^{-(k - 1/2)}
  ‖(c, d)‖^{-(k - 1/2)}`, where `|cz + d| ≥ |c| y ≥ y` and `|cz + d| ≥ r ‖(c, d)‖` (Mathlib's bound
  for Eisenstein series). Summing over the distinct rows gives
  `|P ∣[k] δ (z)| ≤ (e^{-2π n y / w} + C y^{-1/2}) Σ_{x ∈ ℤ²} ‖x‖^{-(k - 1/2)}` there, and since
  `(P ∣[k] δ)(z + m) = (P ∣[k] δ T^m)(z)`, the same bound holds wherever `Im z ≥ 1`. It tends to
  `0` as `Im z → ∞`. So `P` vanishes at every cusp `δ ∞ ∈ ℙ¹(ℚ)`, whatever the index of `G`.

For the trivial multiplier this makes `P` a cusp form in Mathlib's sense.

## Main definitions

* `ModularForm.poincareCuspForm`: for `v = 1`, the Poincaré series as a Mathlib `CuspForm`.

## Main results

* `ModularForm.poincareSeries_slash`: the transformation law `P ∣[k] g = v(g) P`, `g ∈ G`.
* `ModularForm.isZeroAtImInfty_poincareSeries_slash`: for `k ≥ 3`, `n ≥ 1` and `w ≥ 1`,
  `P ∣[k] δ` tends to `0` at `i∞` for every `δ ∈ SL(2, ℤ)`.
* `ModularForm.isZeroAt_poincareSeries`: `P` vanishes at every cusp of `G`.
* `ModularForm.poincareSeries_mem_multiplierCuspSpace`: `P` is a cusp form of weight `k` and
  multiplier `v` on `G`.
-/

open UpperHalfPlane Matrix SpecialLinearGroup OnePoint EisensteinSeries ModularGroup Filter

open scoped MatrixGroups ComplexConjugate Manifold ModularForm Topology

namespace ModularForm

variable {G : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ)) (v : G →* Circle) (k n : ℤ) (w : ℕ) (z : ℍ)
    (δ : SL(2, ℤ)) (g g₀ : G)

lemma denom_mul_SL (A B : SL(2, ℤ)) :
    denom (A * B : SL(2, ℤ)) z = denom A ↑(B • z) * denom B z := by
  rw [map_mul, map_mul, denom_cocycle_σ]
  simp [σ]

lemma poincareTerm_smul_mul_denom : poincareTerm γ v k n w (δ • z) g * denom δ z ^ (-k) =
    conj (v g : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (n / w) * ↑((γ⁻¹ * (g : SL(2, ℤ)) * δ) • z)) *
        denom (γ⁻¹ * (g : SL(2, ℤ)) * δ : SL(2, ℤ)) z ^ (-k) := by
  rw [poincareTerm_eq_denom, mul_smul (γ⁻¹ * (g : SL(2, ℤ))), denom_mul_SL _ (γ⁻¹ * g), mul_zpow,
    mul_assoc]

lemma conj_mul_mul : conj (v (g * g₀) : ℂ) * v g₀ = conj (v g : ℂ) := by
  rw [map_mul, Circle.coe_mul, map_mul, mul_assoc, Complex.conj_mul']
  simp

lemma poincareTerm_smul_mul_denom_of_mem :
    poincareTerm γ v k n w ((g₀ : SL(2, ℤ)) • z) g * denom (g₀ : SL(2, ℤ)) z ^ (-k) =
      v g₀ * poincareTerm γ v k n w z (g * g₀) := by
  rw [poincareTerm_smul_mul_denom, poincareTerm_eq_denom, Subgroup.coe_mul, ← mul_assoc γ⁻¹,
    ← mul_assoc (v g₀ : ℂ), ← mul_assoc (v g₀ : ℂ), mul_comm (v g₀ : ℂ), conj_mul_mul]

lemma tsum_poincareTerm_mul
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k) :
    ∑' q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)),
      poincareTerm γ v k n w z (q.out * g) = poincareSeries γ v k n w z := by
  let e : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) ≃
      Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) :=
    Quotient.congr (Equiv.mulRight g) fun a b ↦ by
      simp [QuotientGroup.rightRel_apply]
  rw [poincareSeries, ← e.tsum_eq fun q ↦ poincareTerm γ v k n w z q.out]
  exact tsum_congr fun q ↦ (poincareTerm_eq_of_rightRel γ v k n w z hw hv <|
    Quotient.exact ((congrArg e q.out_eq).trans (Quotient.out_eq (e q)).symm)).symm

/-- **The transformation law of Poincaré series** (LMFDB `specialfunction.poincare`): when the
terms are constant on the cosets `G_s g'` (`w` divides the translations of the
`γ_s⁻¹ h γ_s = ±T^b`, `h ∈ G_s`, and `v(h) = (±1)^k` there), `P ∣[k] g = v(g) P` for every
`g ∈ G`, since right multiplication by `g` permutes the cosets. -/
lemma poincareSeries_slash (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k) :
    poincareSeries γ v k n w ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • poincareSeries γ v k n w := by
  ext z
  rw [SL_slash_apply, Pi.smul_apply, smul_eq_mul, poincareSeries, ← tsum_mul_right]
  simp_rw [poincareTerm_smul_mul_denom_of_mem]
  rw [tsum_mul_left, tsum_poincareTerm_mul γ v k n w z g hw hv]

lemma injective_poincareBottomRow_mul :
    Function.Injective fun q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) ↦
      ![(γ⁻¹ * (q.out : SL(2, ℤ)) * δ) 1 0, (γ⁻¹ * (q.out : SL(2, ℤ)) * δ) 1 1] := by
  intro q q' hqq
  have hrow (A : SL(2, ℤ)) (j : Fin 2) : A 1 j = (A * δ) 1 0 * δ⁻¹ 0 j + (A * δ) 1 1 * δ⁻¹ 1 j := by
    have h : (A * δ * δ⁻¹ : SL(2, ℤ)) 1 j = (A * δ) 1 0 * δ⁻¹ 0 j + (A * δ) 1 1 * δ⁻¹ 1 j := by
      rw [(A * δ).coe_mul δ⁻¹, Matrix.mul_apply, Fin.sum_univ_two]
    rwa [mul_inv_cancel_right] at h
  have h₀ : (γ⁻¹ * (q.out : SL(2, ℤ)) * δ) 1 0 = (γ⁻¹ * (q'.out : SL(2, ℤ)) * δ) 1 0 :=
    congrFun hqq 0
  have h₁ : (γ⁻¹ * (q.out : SL(2, ℤ)) * δ) 1 1 = (γ⁻¹ * (q'.out : SL(2, ℤ)) * δ) 1 1 :=
    congrFun hqq 1
  refine injective_poincareBottomRow γ ?_
  beta_reduce
  rw [hrow (γ⁻¹ * q.out) 0, hrow (γ⁻¹ * q.out) 1, hrow (γ⁻¹ * q'.out) 0, hrow (γ⁻¹ * q'.out) 1,
    h₀, h₁]

variable {k n w z} in
lemma norm_exp_mul_norm_denom_zpow_le (hk : 3 ≤ k) (hn : 0 ≤ n) (hz : z ∈ verticalStrip (1 / 2) 1) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (n / w) * ↑(δ • z))‖ * ‖denom δ z‖ ^ (-k) ≤
      (Real.exp (-(2 * Real.pi * (n / w) * z.im)) +
        z.im ^ (-(1 / 2 : ℝ)) * r ⟨⟨1 / 2, 1⟩, one_pos⟩ ^ (-(k - 1 / 2 : ℝ))) *
          ‖![δ 1 0, δ 1 1]‖ ^ (-(k - 1 / 2 : ℝ)) := by
  have hy : 0 < z.im := z.im_pos
  have hexp (u : ℍ) : ‖Complex.exp (2 * Real.pi * Complex.I * (n / w) * u)‖ =
      Real.exp (-(2 * Real.pi * (n / w) * u.im)) := by
    rw [Complex.norm_exp]
    simp
  rw [hexp]
  rcases eq_or_ne (δ 1 0) 0 with hc | hc
  · have hdet : δ 0 0 * δ 1 1 = 1 := by
      have hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := δ.det_coe
      rwa [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hδ
    have hd : |(δ 1 1 : ℝ)| = 1 := by
      exact_mod_cast Int.isUnit_iff_abs_eq.mp (IsUnit.of_mul_eq_one_right _ hdet)
    have hden : ‖denom δ z‖ = 1 := by
      rw [ModularGroup.denom_apply, hc]
      simpa using hd
    have hnorm : ‖![δ 1 0, δ 1 1]‖ = 1 := by
      rw [norm_eq_max_natAbs]
      simpa [hc] using hd
    have him : (δ • z).im = z.im := by
      rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq, hden]
      simp
    rw [hden, him, hnorm, one_zpow, mul_one, Real.one_rpow, mul_one]
    exact le_add_of_nonneg_right <| mul_nonneg (Real.rpow_nonneg hy.le _)
      (Real.rpow_nonneg (r_pos _).le _)
  · have hexp1 : Real.exp (-(2 * Real.pi * (n / w) * (δ • z).im)) ≤ 1 := by
      have hδz : 0 < (δ • z).im := (δ • z).im_pos
      exact Real.exp_le_one_iff.mpr <| neg_nonpos.mpr <| by positivity
    have hyden : z.im ≤ ‖denom δ z‖ := by
      rw [ModularGroup.denom_apply]
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      have h1 : (1 : ℝ) ≤ |(δ 1 0 : ℝ)| := by exact_mod_cast Int.one_le_abs hc
      simpa [abs_of_pos hy] using le_mul_of_one_le_left hy.le h1
    have hsplit : ‖denom δ z‖ ^ (-k) =
        ‖denom δ z‖ ^ (-(1 / 2 : ℝ)) * ‖denom δ z‖ ^ (-(k - 1 / 2 : ℝ)) := by
      rw [← Real.rpow_intCast, ← Real.rpow_add (hy.trans_le hyden)]
      congr 1
      push_cast
      ring1
    have h1 : ‖denom δ z‖ ^ (-(1 / 2 : ℝ)) ≤ z.im ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hy hyden (by norm_num)
    have h2 : ‖denom δ z‖ ^ (-(k - 1 / 2 : ℝ)) ≤
        r ⟨⟨1 / 2, 1⟩, one_pos⟩ ^ (-(k - 1 / 2 : ℝ)) * ‖![δ 1 0, δ 1 1]‖ ^ (-(k - 1 / 2 : ℝ)) := by
      have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
      simpa [ModularGroup.denom_apply] using
        summand_bound_of_mem_verticalStrip (k := (k - 1 / 2 : ℝ)) (by linarith) ![δ 1 0, δ 1 1]
          one_pos hz
    rw [hsplit]
    refine (mul_le_mul hexp1 (mul_le_mul h1 h2 (by positivity) (by positivity)) (by positivity)
      zero_le_one).trans ?_
    rw [one_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Real.exp_pos _).le) (by positivity)

variable {k n z} in
lemma norm_poincareSeries_slash_le (hk : 3 ≤ k) (hn : 0 ≤ n) (hz : z ∈ verticalStrip (1 / 2) 1) :
    ‖(poincareSeries γ v k n w ∣[k] δ) z‖ ≤ (Real.exp (-(2 * Real.pi * (n / w) * z.im)) +
      z.im ^ (-(1 / 2 : ℝ)) * r ⟨⟨1 / 2, 1⟩, one_pos⟩ ^ (-(k - 1 / 2 : ℝ))) *
        ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-(k - 1 / 2 : ℝ)) := by
  have hk' : (2 : ℝ) < k - 1 / 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hB : 0 ≤ Real.exp (-(2 * Real.pi * (n / w) * z.im)) +
      z.im ^ (-(1 / 2 : ℝ)) * r ⟨⟨1 / 2, 1⟩, one_pos⟩ ^ (-(k - 1 / 2 : ℝ)) :=
    add_nonneg (Real.exp_pos _).le <| mul_nonneg (Real.rpow_nonneg z.im_pos.le _)
      (Real.rpow_nonneg (r_pos _).le _)
  have hs : Summable fun q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) ↦
      ‖![(γ⁻¹ * (q.out : SL(2, ℤ)) * δ) 1 0, (γ⁻¹ * (q.out : SL(2, ℤ)) * δ) 1 1]‖ ^
        (-(k - 1 / 2 : ℝ)) :=
    (summable_one_div_norm_rpow hk').comp_injective (injective_poincareBottomRow_mul γ δ)
  have hb (q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ))) :
      ‖poincareTerm γ v k n w (δ • z) q.out * denom δ z ^ (-k)‖ ≤
        (Real.exp (-(2 * Real.pi * (n / w) * z.im)) +
          z.im ^ (-(1 / 2 : ℝ)) * r ⟨⟨1 / 2, 1⟩, one_pos⟩ ^ (-(k - 1 / 2 : ℝ))) *
            ‖![(γ⁻¹ * (q.out : SL(2, ℤ)) * δ) 1 0, (γ⁻¹ * (q.out : SL(2, ℤ)) * δ) 1 1]‖ ^
              (-(k - 1 / 2 : ℝ)) := by
    rw [poincareTerm_smul_mul_denom, norm_mul, norm_mul, Complex.norm_conj, Circle.norm_coe,
      one_mul, norm_zpow]
    exact norm_exp_mul_norm_denom_zpow_le _ hk hn hz
  have hs' : Summable fun q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) ↦
      ‖poincareTerm γ v k n w (δ • z) q.out * denom δ z ^ (-k)‖ :=
    (hs.mul_left _).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb
  rw [SL_slash_apply, poincareSeries, ← tsum_mul_right]
  refine (norm_tsum_le_tsum_norm hs').trans <| (hs'.tsum_le_tsum hb (hs.mul_left _)).trans ?_
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj (summable_one_div_norm_rpow hk')
    (fun _ ↦ by positivity) (injective_poincareBottomRow_mul γ δ)) hB

variable {k n w} in
/-- **Poincaré series of weight `k ≥ 3` and index `n ≥ 1` vanish at every cusp of `SL(2, ℤ)`**
(LMFDB `specialfunction.poincare`): `P ∣[k] δ` tends to `0` at `i∞` for every `δ ∈ SL(2, ℤ)`,
being bounded by `(e^{-2π n y / w} + C y^{-1/2}) Σ_{x ∈ ℤ²} ‖x‖^{-(k - 1/2)}` for `y = Im z ≥ 1`. -/
lemma isZeroAtImInfty_poincareSeries_slash (hk : 3 ≤ k) (hn : 0 < n) (hw : 0 < w) :
    IsZeroAtImInfty (poincareSeries γ v k n w ∣[k] δ) := by
  have hbound (z : ℍ) (hz : 1 ≤ z.im) : ‖(poincareSeries γ v k n w ∣[k] δ) z‖ ≤
      (Real.exp (-(2 * Real.pi * (n / w) * z.im)) +
        z.im ^ (-(1 / 2 : ℝ)) * r ⟨⟨1 / 2, 1⟩, one_pos⟩ ^ (-(k - 1 / 2 : ℝ))) *
          ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-(k - 1 / 2 : ℝ)) := by
    have hz' : ((T ^ (-round z.re) • z : ℍ) : ℂ) = z + ↑(-round z.re) := coe_T_zpow_smul_eq z
    have him : (T ^ (-round z.re) • z).im = z.im := by
      rw [← UpperHalfPlane.coe_im, hz']
      simp
    have hstrip : T ^ (-round z.re) • z ∈ verticalStrip (1 / 2) 1 := by
      refine ⟨?_, him ▸ hz⟩
      rw [← UpperHalfPlane.coe_re, hz']
      simpa [← sub_eq_add_neg] using abs_sub_round z.re
    have hslash : (poincareSeries γ v k n w ∣[k] δ) z =
        (poincareSeries γ v k n w ∣[k] (δ * T ^ round z.re)) (T ^ (-round z.re) • z) := by
      rw [SlashAction.slash_mul, SL_slash_apply _ (T ^ round z.re), ← mul_smul, ← zpow_add,
        add_neg_cancel, zpow_zero, one_smul, ModularGroup.denom_apply]
      simp [coe_T_zpow]
    rw [hslash, ← him]
    exact norm_poincareSeries_slash_le γ v w _ hk hn.le hstrip
  have hc : 0 < 2 * Real.pi * (n / w) := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hw' : (0 : ℝ) < w := by exact_mod_cast hw
    positivity
  have hlim : Tendsto (fun t : ℝ ↦ (Real.exp (-(2 * Real.pi * (n / w) * t)) +
      t ^ (-(1 / 2 : ℝ)) * r ⟨⟨1 / 2, 1⟩, one_pos⟩ ^ (-(k - 1 / 2 : ℝ))) *
        ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-(k - 1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)).add
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).mul_const _)).mul_const _
  exact squeeze_zero_norm' ((atImInfty_mem _).mpr ⟨1, hbound⟩) (hlim.comp tendsto_comap)

variable {k n w} in
/-- **Poincaré series of weight `k ≥ 3` and index `n ≥ 1` vanish at every cusp of `G`** (LMFDB
`specialfunction.poincare`), indeed at every point of `ℙ¹(ℚ)`, whatever the index of `G`. -/
lemma isZeroAt_poincareSeries (hk : 3 ≤ k) (hn : 0 < n) (hw : 0 < w) {c : OnePoint ℝ}
    (hc : IsCusp c (G.map (mapGL ℝ))) : c.IsZeroAt (poincareSeries γ v k n w) k :=
  (isZeroAt_iff_forall_SL2Z (hc.mono (Subgroup.map_le_range _ _))).mpr fun δ _ ↦
    isZeroAtImInfty_poincareSeries_slash γ v δ hk hn hw

variable {k n w} in
/-- **Poincaré series are cusp forms** (LMFDB `specialfunction.poincare`): for `k ≥ 3`, `n ≥ 1` and
`w ≥ 1`, when the terms are constant on the cosets `G_s g` (`w` divides the translations of the
`γ_s⁻¹ h γ_s = ±T^b`, `h ∈ G_s`, and `v(h) = (±1)^k` there), the `n`-th Poincaré series is a cusp
form of weight `k` and multiplier `v` on `G` (on the image of `G` in `GL(2, ℝ)`): holomorphic on
`ℍ`, with `P ∣[k] g = v(g) P` for `g ∈ G`, and vanishing at every cusp. -/
lemma poincareSeries_mem_multiplierCuspSpace (hk : 3 ≤ k) (hn : 0 < n) (hw₀ : 0 < w)
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k) :
    poincareSeries γ v k n w ∈ multiplierCuspSpace k (multiplierMapGL v) := by
  refine ⟨⟨mdifferentiable_poincareSeries γ v w hk hn.le, fun g' ↦ ?_,
    fun hc g hg ↦ (isZeroAt_poincareSeries γ v hk hn hw₀ hc g hg).boundedAtFilter⟩,
      fun hc ↦ isZeroAt_poincareSeries γ v hk hn hw₀ hc⟩
  rcases g' with ⟨_, g, hg, rfl⟩
  rw [multiplierMapGL_apply_mapGL v ⟨g, hg⟩]
  exact poincareSeries_slash γ v k n w ⟨g, hg⟩ hw hv

variable {k n w} in
/-- The `n`-th **Poincaré series** (LMFDB `specialfunction.poincare`) of weight `k ≥ 3` and trivial
multiplier on `G` at the cusp `γ_s ∞` of width `w`, for `n ≥ 1`, as a cusp form for the image of
`G` in `GL(2, ℝ)` (Mathlib's `CuspForm`), when `w` divides the translations of the
`γ_s⁻¹ h γ_s = ±T^b`, `h ∈ G_s`, and `(±1)^k = 1` there (`k` even at an irregular cusp). -/
noncomputable def poincareCuspForm (hk : 3 ≤ k) (hn : 0 < n) (hw₀ : 0 < w)
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k = 1) :
    CuspForm (G.map (mapGL ℝ)) k :=
  haveI hP : poincareSeries γ 1 k n w ∈ multiplierCuspSpace k (multiplierMapGL (1 : G →* Circle)) :=
    poincareSeries_mem_multiplierCuspSpace γ 1 hk hn hw₀ hw fun h hh ↦ (hv h hh).symm ▸ rfl
  { toFun := poincareSeries γ 1 k n w
    slash_action_eq' := fun g hg ↦ by simpa [multiplierMapGL] using hP.1.2.1 ⟨g, hg⟩
    holo' := hP.1.1
    zero_at_cusps' := hP.2 }

end ModularForm
