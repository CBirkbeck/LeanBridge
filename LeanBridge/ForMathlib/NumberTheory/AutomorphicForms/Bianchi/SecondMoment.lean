import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.FunctionalEquation

/-!
# The second moment of the Fourier–Bessel coefficients of a Bianchi cusp form

Let `K` be an imaginary quadratic field of class number `1`, embedded in `ℂ` by `σ`. For a Bianchi
cusp form `F` of even weight `k ≥ 1`, with Fourier–Bessel coefficients `c(α)`, the invariant norm
`y^k ⟨F, F⟩_k` is bounded. So Bessel's inequality for the characters `x ↦ ψ(σ(α)x / √Δ)` of
`ℂ / σ(𝒪_K)` (`HyperbolicThreeSpace.sum_sq_norm_setIntegral_le`), at the height `y = 1 / Y`, gives
`∑_{Y ≤ |α| < 2Y} |c(α)|² ≪ Y^{k+2}`, whence
`∑_{α ≠ 0} |c(α)|² |α|^{-r} < ∞` for `r > k + 2`
(`HyperbolicThreeSpace.IsBianchiCuspFunction.summable_sq_norm_coeff_mul_rpow`). By the inequality of
Cauchy and Schwarz, `∑_{α ≠ 0} |c(α)| |α|^{-s} < ∞` for `s > k/2 + 2`
(`HyperbolicThreeSpace.BianchiNewformOfWeight.summable_norm_coeff_mul_rpow`, for a newform). This is
the absolute convergence of the L-function of `F` for `Re s > 1` in the analytic normalisation,
without the Rankin–Selberg method: this method gives more, the asymptotics of the second moment.

## Main definitions

* `HyperbolicThreeSpace.bianchiCharacter`: the character `x ↦ ψ(μx) = e^{2πi(μx + conj(μx))}` of
  `ℂ`.

## Main results

* `HyperbolicThreeSpace.sum_sq_norm_setIntegral_le`: Bessel's inequality for the characters of a
  lattice.
* `HyperbolicThreeSpace.IsBianchiCuspFunction.summable_sq_norm_coeff_mul_rpow`: the second moment of
  the coefficients of a periodic cuspidal function.
* `HyperbolicThreeSpace.IsBianchiCuspFunction.summable_norm_coeff_mul_rpow`: the first moment of the
  coefficients of a periodic cuspidal function.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.summable_norm_coeff_mul_rpow`: the first moment of
  the coefficients of a newform.
-/

open Bornology Complex Matrix MeasureTheory Module NumberField HilbertModularGroup Set

open scoped ComplexConjugate MatrixGroups nonZeroDivisors Pointwise Real

namespace HyperbolicThreeSpace

/-- The character `x ↦ ψ(μx) = e^{2πi(μx + conj(μx))}` of `ℂ`, for `μ ∈ ℂ`. -/
noncomputable def bianchiCharacter (μ x : ℂ) : ℂ :=
  cexp (2 * π * I * (μ * x + conj (μ * x)))

lemma continuous_bianchiCharacter (μ : ℂ) : Continuous (bianchiCharacter μ) :=
  continuous_exp.comp (continuous_const.mul ((continuous_const.mul continuous_id).add
    (continuous_conj.comp (continuous_const.mul continuous_id))))

lemma norm_bianchiCharacter (μ x : ℂ) : ‖bianchiCharacter μ x‖ = 1 := by
  have hre : (2 * π * I * (μ * x + conj (μ * x))).re = 0 := by
    rw [add_conj]
    simp
  rw [bianchiCharacter, Complex.norm_exp, hre, Real.exp_zero]

lemma conj_bianchiCharacter_mul (μ ν x : ℂ) :
    conj (bianchiCharacter μ x) * bianchiCharacter ν x = bianchiCharacter (ν - μ) x := by
  simp only [bianchiCharacter, ← exp_conj, ← Complex.exp_add, map_mul, map_add, conj_conj, conj_I,
    conj_ofReal, map_ofNat]
  congr 1
  simp only [map_sub]
  ring1

lemma bianchiCharacter_add (μ a b : ℂ) :
    bianchiCharacter μ (a + b) = bianchiCharacter μ a * bianchiCharacter μ b := by
  simp only [bianchiCharacter, ← Complex.exp_add, mul_add, map_add]
  congr 1
  ring1

variable {Λ : AddSubgroup ℂ} [Countable Λ] {P : Set ℂ}

lemma setIntegral_bianchiCharacter_eq_zero (hP : IsAddFundamentalDomain Λ P) {θ : ℂ} (hθ : θ ≠ 0)
    (hdual : ∀ l ∈ Λ, bianchiCharacter θ l = 1) : ∫ x in P, bianchiCharacter θ x = 0 := by
  have ht : bianchiCharacter θ (4 * θ)⁻¹ = -1 := by
    have e₁ : θ * (4 * θ)⁻¹ = 4⁻¹ := by
      field_simp
    have e₂ : 2 * π * I * (θ * (4 * θ)⁻¹ + conj (θ * (4 * θ)⁻¹)) = π * I := by
      rw [e₁, map_inv₀, map_ofNat]
      ring1
    rw [bianchiCharacter, e₂, Complex.exp_pi_mul_I]
  have h₁ : ∫ s in P, bianchiCharacter θ ((4 * θ)⁻¹ + s) = ∫ s in P, bianchiCharacter θ s :=
    setIntegral_add_left_eq Λ hP (fun l hl s ↦ by rw [bianchiCharacter_add, hdual l hl, one_mul]) _
  simp only [bianchiCharacter_add, ht, neg_mul, one_mul] at h₁
  rw [integral_neg] at h₁
  linear_combination (-1 / 2 : ℂ) * h₁

/-- **Bessel's inequality for the characters of a lattice**: for a bounded fundamental domain `P` of
a countable subgroup `Λ` of `ℂ`, distinct frequencies `μᵢ` with `ψ(μᵢ l) = 1` on `Λ`, and a
continuous function `g` bounded by `B`, `∑ᵢ |∫_P ψ(-μᵢ x) g(x) dx|² ≤ vol(P)² B²`. -/
lemma sum_sq_norm_setIntegral_le (hP : IsAddFundamentalDomain Λ P) (hPb : IsBounded P) {ι : Type*}
    (S : Finset ι) {μ : ι → ℂ} (hμ : Function.Injective μ)
    (hdual : ∀ i, ∀ l ∈ Λ, bianchiCharacter (μ i) l = 1) {g : ℂ → ℂ} (hg : Continuous g) {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B) :
    ∑ i ∈ S, ‖∫ x in P, conj (bianchiCharacter (μ i) x) * g x‖ ^ 2 ≤ volume.real P ^ 2 * B ^ 2 := by
  classical
  have hV : 0 < volume.real P :=
    ENNReal.toReal_pos (hP.measure_ne_zero (NeZero.ne _)) hPb.measure_lt_top.ne
  have hfin : IsFiniteMeasure (volume.restrict P) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hPb.measure_lt_top⟩
  have hinner {f h : ℂ → ℂ} (hf : MemLp f 2 (volume.restrict P))
      (hh : MemLp h 2 (volume.restrict P)) :
      inner ℂ (hf.toLp f) (hh.toLp h) = ∫ x in P, conj (f x) * h x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hh.coeFn_toLp] with x h₁ h₂
    rw [h₁, h₂, RCLike.inner_apply, mul_comm]
  have hmem (i : ι) : MemLp (bianchiCharacter (μ i)) 2 (volume.restrict P) :=
    MemLp.of_bound (continuous_bianchiCharacter _).aestronglyMeasurable 1
      (ae_of_all _ fun x ↦ (norm_bianchiCharacter _ _).le)
  have hmemg : MemLp g 2 (volume.restrict P) :=
    MemLp.of_bound hg.aestronglyMeasurable B (ae_of_all _ hB)
  have hs : (((√(volume.real P) : ℝ) : ℂ)⁻¹) * ((√(volume.real P) : ℝ) : ℂ)⁻¹ =
      ((volume.real P : ℝ) : ℂ)⁻¹ := by
    rw [← mul_inv, ← ofReal_mul, Real.mul_self_sqrt hV.le]
  have hc : conj ((√(volume.real P) : ℝ) : ℂ)⁻¹ = ((√(volume.real P) : ℝ) : ℂ)⁻¹ := by
    rw [map_inv₀, conj_ofReal]
  have hw : Orthonormal ℂ fun i ↦ ((√(volume.real P) : ℝ) : ℂ)⁻¹ • (hmem i).toLp _ := by
    refine orthonormal_iff_ite.mpr fun i j ↦ ?_
    rw [inner_smul_left, inner_smul_right, hinner, hc, ← mul_assoc, hs]
    simp only [conj_bianchiCharacter_mul]
    split_ifs with hij
    · have h₁ (x : ℂ) : bianchiCharacter (μ j - μ i) x = 1 := by
        simp [hij, bianchiCharacter]
      have hV' : ((volume.real P : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hV.ne'
      simp only [h₁, setIntegral_const, real_smul, mul_one]
      exact inv_mul_cancel₀ hV'
    · have h₁ : μ j - μ i ≠ 0 := sub_ne_zero.mpr fun h ↦ hij (hμ h).symm
      rw [setIntegral_bianchiCharacter_eq_zero hP h₁ fun l hl ↦ ?_, mul_zero]
      rw [← conj_bianchiCharacter_mul, hdual i l hl, hdual j l hl, map_one, one_mul]
  have hb : ∑ i ∈ S, ‖inner ℂ (((√(volume.real P) : ℝ) : ℂ)⁻¹ • (hmem i).toLp _)
      (hmemg.toLp g)‖ ^ 2 ≤ ‖hmemg.toLp g‖ ^ 2 := Orthonormal.sum_inner_products_le _ hw
  have hG : ‖hmemg.toLp g‖ ^ 2 ≤ B ^ 2 * volume.real P := by
    have h₂ : ‖∫ x in P, conj (g x) * g x‖ ≤ B ^ 2 * volume.real P :=
      norm_setIntegral_le_of_norm_le_const hPb.measure_lt_top fun x _ ↦ by
        have hB₀ : 0 ≤ B := (norm_nonneg _).trans (hB x)
        rw [norm_mul, RCLike.norm_conj, sq]
        exact mul_le_mul (hB x) (hB x) (norm_nonneg _) hB₀
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hinner]
    exact (RCLike.re_le_norm _).trans h₂
  have hterm (i : ι) : ‖inner ℂ (((√(volume.real P) : ℝ) : ℂ)⁻¹ • (hmem i).toLp _)
      (hmemg.toLp g)‖ ^ 2 = (volume.real P)⁻¹ *
        ‖∫ x in P, conj (bianchiCharacter (μ i) x) * g x‖ ^ 2 := by
    rw [inner_smul_left, hinner, hc, norm_mul, mul_pow, norm_inv, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hV.le]
  simp only [hterm, ← Finset.mul_sum] at hb
  have h₁ : (volume.real P)⁻¹ * ∑ i ∈ S, ‖∫ x in P, conj (bianchiCharacter (μ i) x) * g x‖ ^ 2 ≤
      B ^ 2 * volume.real P := hb.trans hG
  rw [inv_mul_le_iff₀ hV] at h₁
  linarith

variable {K : Type*} [Field K] {σ : K →+* ℂ} {δ : ℂ} {x : K} {k : ℕ} {c : 𝓞 K → ℂ}
  {H : HyperbolicThreeSpace → Fin (k + 1) → ℂ} [NumberField K] [IsTotallyComplex K]

lemma IsBianchiCuspFunction.sum_sq_le (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) (hk' : Even k)
    (hk : k ≠ 0) (hδ : δ ^ 2 = discr K) (hH : IsBianchiCuspFunction σ k H)
    (hper : ∀ a : 𝓞 K, glSlash σ k (glUpper a) H = H)
    (hc : HasBianchiWhittakerExpansion σ δ k (extend H) c) {M : ℝ} (hM : ∀ z, bianchiNormSq H z ≤ M)
    {y : ℝ} (hy : 0 < y) (S : Finset {α : 𝓞 K // α ≠ 0}) :
    ∑ α ∈ S, (‖c α‖ * y * ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π * ‖σ α.1 / δ‖ * y)‖) ^ 2 ≤
      ((y ^ (k / 2))⁻¹ * √M) ^ 2 := by
  have hδ₀ : δ ≠ 0 := ne_zero_of_sq_eq_discr K hδ
  have hP : IsAddFundamentalDomain (bianchiScaledLattice σ 1)
      (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) volume :=
    isAddFundamentalDomain_bianchiScaledLattice_one hK hx
  have hPb : IsBounded (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) :=
    ZSpan.fundamentalDomain_isBounded _
  have hV : 0 < volume.real (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) :=
    ENNReal.toReal_pos (hP.measure_ne_zero (NeZero.ne _)) hPb.measure_lt_top.ne
  have hcont : Continuous fun w : ℂ ↦ extend H (w, y) := continuous_extend_mk hH.analyticAt hy
  have hμ : Function.Injective fun α : {α : 𝓞 K // α ≠ 0} ↦ σ (α.1 : K) / δ := fun α β h ↦
    Subtype.ext (RingOfIntegers.coe_injective (σ.injective ((div_left_inj' hδ₀).mp h)))
  have hdual (α : {α : 𝓞 K // α ≠ 0}) (l : ℂ) (hl : l ∈ bianchiScaledLattice σ 1) :
      bianchiCharacter (σ (α.1 : K) / δ) l = 1 := by
    rcases mem_bianchiScaledLattice.mp hl with ⟨a, rfl⟩
    have e : σ (α.1 : K) / δ * σ (1 * (a : K)) = σ ((α.1 * a : 𝓞 K) : K) / δ := by
      simp only [one_mul, map_mul]
      ring1
    rw [bianchiCharacter, e]
    exact cexp_two_pi_mul_eq_one hK hx hδ _
  have hb : ∑ α ∈ S, ‖∫ w in ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx),
      conj (bianchiCharacter (σ (α.1 : K) / δ) w) * extend H (w, y) 0‖ ^ 2 ≤
        volume.real (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) ^ 2 *
          ((y ^ (k / 2))⁻¹ * √M) ^ 2 :=
    sum_sq_norm_setIntegral_le hP hPb S hμ (fun α l hl ↦ hdual α l hl)
      ((continuous_apply 0).comp hcont) fun w ↦
        (norm_le_pi_norm _ 0).trans (norm_extend_le_of_bianchiNormSq_le hM hk' hy w)
  have hterm (α : {α : 𝓞 K // α ≠ 0}) :
      ‖∫ w in ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx),
        conj (bianchiCharacter (σ (α.1 : K) / δ) w) * extend H (w, y) 0‖ =
          volume.real (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) *
            (‖c α‖ * y * ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π * ‖σ α.1 / δ‖ * y)‖) := by
    rw [← hH.norm_bianchiFourierCoeff_apply_zero hK hx hk' hk hδ hper hc α.2 hy,
      bianchiFourierCoeff]
    have hi : Integrable (fun w : ℂ ↦ cexp (-(2 * π * I * (σ (α.1 : K) / δ * w +
        conj (σ (α.1 : K) / δ * w)))) • extend H (w, y))
        (volume.restrict (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx))) := by
      have hc₁ : Continuous fun w : ℂ ↦ cexp (-(2 * π * I * (σ (α.1 : K) / δ * w +
          conj (σ (α.1 : K) / δ * w)))) • extend H (w, y) :=
        (continuous_exp.comp (continuous_const.mul ((continuous_const.mul continuous_id).add
          (continuous_conj.comp (continuous_const.mul continuous_id)))).neg).smul hcont
      exact (hc₁.continuousOn.integrableOn_compact hPb.isCompact_closure).mono_set subset_closure
    have h₁ : (∫ w in ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx),
        cexp (-(2 * π * I * (σ (α.1 : K) / δ * w + conj (σ (α.1 : K) / δ * w)))) •
          extend H (w, y)) 0 = ∫ w in ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx),
            conj (bianchiCharacter (σ (α.1 : K) / δ) w) * extend H (w, y) 0 := by
      have h₂ : ∫ w in ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx),
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (k + 1) ↦ ℂ) 0
            (cexp (-(2 * π * I * (σ (α.1 : K) / δ * w + conj (σ (α.1 : K) / δ * w)))) •
              extend H (w, y)) = ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (k + 1) ↦ ℂ) 0
            (∫ w in ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx),
              cexp (-(2 * π * I * (σ (α.1 : K) / δ * w + conj (σ (α.1 : K) / δ * w)))) •
                extend H (w, y)) :=
        ContinuousLinearMap.integral_comp_comm _ hi
      refine h₂.symm.trans (integral_congr_ae (ae_of_all _ fun w ↦ ?_))
      simp only [ContinuousLinearMap.proj_apply, Pi.smul_apply, bianchiCharacter, ← exp_conj,
        map_mul, map_add, conj_conj, conj_I, conj_ofReal, map_ofNat]
      congr 2
      ring1
    rw [Pi.smul_apply, h₁, smul_eq_mul, norm_mul, norm_inv, norm_real, Real.norm_eq_abs,
      abs_of_pos hV, mul_inv_cancel_left₀ hV.ne']
  simp only [hterm, mul_pow, ← Finset.mul_sum] at hb
  have hV' : 0 < volume.real (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) ^ 2 :=
    pow_pos hV 2
  simp only [mul_pow]
  exact (mul_le_mul_iff_right₀ hV').mp hb

variable {r s : ℝ}

lemma sq_mul_rpow_le {a t X κ A : ℝ} (hX : 0 < X) (hlo : X ≤ t) (hr : 0 ≤ r) (hκ : 0 < κ)
    (hA : κ ≤ A) : a ^ 2 * t ^ (-r) ≤ X ^ (-r) * X ^ 2 * κ⁻¹ ^ 2 * (a * X⁻¹ * A) ^ 2 := by
  have h₁ : t ^ (-r) ≤ X ^ (-r) := Real.rpow_le_rpow_of_nonpos hX hlo (neg_nonpos.mpr hr)
  have h₂ : 1 ≤ κ⁻¹ ^ 2 * A ^ 2 := by
    rw [← mul_pow]
    refine one_le_pow₀ ?_
    rw [inv_mul_eq_div]
    exact (one_le_div hκ).mpr hA
  have e :
      X ^ (-r) * X ^ 2 * κ⁻¹ ^ 2 * (a * X⁻¹ * A) ^ 2 = a ^ 2 * X ^ (-r) * (κ⁻¹ ^ 2 * A ^ 2) := by
    field_simp
  rw [e]
  have hXr : 0 ≤ X ^ (-r) := Real.rpow_nonneg hX.le _
  exact (mul_le_mul_of_nonneg_left h₁ (sq_nonneg a)).trans
    (le_mul_of_one_le_right (mul_nonneg (sq_nonneg a) hXr) h₂)

/-- **The second moment of the coefficients of a periodic cuspidal function**: for `K` imaginary
quadratic, `δ² = Δ`, a cuspidal function `H` of even weight `k ≥ 1`, periodic for `σ(𝒪_K)`, with
bounded invariant norm and Fourier–Bessel coefficients `c(α)`, and `r > k + 2`,
`∑_{α ≠ 0} |c(α)|² |α|^{-r} < ∞`. -/
lemma IsBianchiCuspFunction.summable_sq_norm_coeff_mul_rpow (hK : finrank ℚ K = 2)
    (hx : (σ x).im ≠ 0) (hk' : Even k) (hk : k ≠ 0) (hδ : δ ^ 2 = discr K)
    (hH : IsBianchiCuspFunction σ k H) (hper : ∀ a : 𝓞 K, glSlash σ k (glUpper a) H = H)
    (hc : HasBianchiWhittakerExpansion σ δ k (extend H) c) {M : ℝ} (hM : ∀ z, bianchiNormSq H z ≤ M)
    (hr : (k : ℝ) + 2 < r) : Summable fun α : {α : 𝓞 K // α ≠ 0} ↦ ‖c α‖ ^ 2 * ‖σ α.1‖ ^ (-r) := by
  classical
  have hδ₀ : 0 < ‖δ‖ := norm_pos_iff.mpr (ne_zero_of_sq_eq_discr K hδ)
  have hk₂ : (1 : ℝ) ≤ (k / 2 : ℝ) := by
    have h₁ : 2 ≤ k := by
      rcases hk' with ⟨m, rfl⟩
      omega
    have h₂ : (2 : ℝ) ≤ k := by
      exact_mod_cast h₁
    linarith
  have hj (α : {α : 𝓞 K // α ≠ 0}) :
      ∃ j : ℕ, (2 : ℝ) ^ j ≤ ‖σ (α.1 : K)‖ ∧ ‖σ (α.1 : K)‖ < 2 ^ (j + 1) :=
    exists_nat_pow_near (one_le_norm_apply hK α.2) one_lt_two
  choose g hg₁ hg₂ using hj
  rcases (⟨_, rfl⟩ : ∃ κ : ℝ, κ = 2⁻¹ * rexp (-(5 / 4 * (8 * π / ‖δ‖)))) with ⟨κ, hκdef⟩
  have hκ : 0 < κ := by
    rw [hκdef]
    positivity
  have hM₀ : 0 ≤ M :=
    (bianchiNormSq_nonneg H (.mk (WithLp.toLp 2 (0, 1)) one_pos)).trans (hM _)
  have hρ₀ : 0 < (2 : ℝ) ^ ((k : ℝ) + 2 - r) := by
    positivity
  have hρ₁ : (2 : ℝ) ^ ((k : ℝ) + 2 - r) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hfib (T : Finset {α : 𝓞 K // α ≠ 0}) (j : ℕ) : ∑ α ∈ T with g α = j, ‖c α‖ ^ 2 *
      ‖σ (α.1 : K)‖ ^ (-r) ≤ M / κ ^ 2 * ((2 : ℝ) ^ ((k : ℝ) + 2 - r)) ^ j := by
    rcases (⟨_, rfl⟩ : ∃ X : ℝ, X = 2 ^ j) with ⟨X, hXdef⟩
    have hX : 0 < X := by
      rw [hXdef]
      positivity
    have h₁ : ∑ α ∈ T with g α = j, (‖c α‖ * X⁻¹ *
        ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π * ‖σ (α.1 : K) / δ‖ * X⁻¹)‖) ^ 2 ≤
          ((X⁻¹ ^ (k / 2))⁻¹ * √M) ^ 2 :=
      hH.sum_sq_le hK hx hk' hk hδ hper hc hM (inv_pos.mpr hX) _
    have hterm (α : {α : 𝓞 K // α ≠ 0}) (hα : α ∈ T.filter fun α ↦ g α = j) :
        ‖c α‖ ^ 2 * ‖σ (α.1 : K)‖ ^ (-r) ≤ X ^ (-r) * X ^ 2 * κ⁻¹ ^ 2 * (‖c α‖ * X⁻¹ *
          ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π * ‖σ (α.1 : K) / δ‖ * X⁻¹)‖) ^ 2 := by
      have hgα : g α = j := (Finset.mem_filter.mp hα).2
      have hlo : X ≤ ‖σ (α.1 : K)‖ := hXdef ▸ hgα ▸ hg₁ α
      have hhi : ‖σ (α.1 : K)‖ < 2 * X := by
        have h₂ : ‖σ (α.1 : K)‖ < 2 ^ (j + 1) := hgα ▸ hg₂ α
        rwa [pow_succ, mul_comm, ← hXdef] at h₂
      have hα₀ : 0 < ‖σ (α.1 : K)‖ := hX.trans_le hlo
      have ht₀ : 0 < 4 * π * ‖σ (α.1 : K) / δ‖ * X⁻¹ := by
        rw [norm_div]
        positivity
      have ht₁ : 4 * π * ‖σ (α.1 : K) / δ‖ * X⁻¹ ≤ 8 * π / ‖δ‖ := by
        have e : 8 * π / ‖δ‖ - 4 * π * ‖σ (α.1 : K) / δ‖ * X⁻¹ =
            4 * π / ‖δ‖ * ((2 * X - ‖σ (α.1 : K)‖) * X⁻¹) := by
          rw [norm_div]
          field_simp
          ring1
        have h₂ : 0 ≤ 4 * π / ‖δ‖ * ((2 * X - ‖σ (α.1 : K)‖) * X⁻¹) :=
          mul_nonneg (by positivity) (mul_nonneg (sub_nonneg.mpr hhi.le) (inv_pos.mpr hX).le)
        rw [← e] at h₂
        exact sub_nonneg.mp h₂
      have hK₁ : κ ≤ ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π * ‖σ (α.1 : K) / δ‖ * X⁻¹)‖ := by
        refine le_trans ?_ (exp_le_norm_besselK hk₂ ht₀)
        rw [hκdef]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        linarith
      exact sq_mul_rpow_le hX hlo (by linarith) hκ hK₁
    have h₂ : ∑ α ∈ T with g α = j, ‖c α‖ ^ 2 * ‖σ (α.1 : K)‖ ^ (-r) ≤
        X ^ (-r) * X ^ 2 * κ⁻¹ ^ 2 * ∑ α ∈ T with g α = j, (‖c α‖ * X⁻¹ *
          ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π * ‖σ (α.1 : K) / δ‖ * X⁻¹)‖) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    have h₃ : ((X⁻¹ ^ (k / 2))⁻¹ * √M) ^ 2 = X ^ k * M := by
      rw [mul_pow, inv_pow, ← pow_mul, Nat.div_mul_cancel hk'.two_dvd, inv_pow, inv_inv,
        Real.sq_sqrt hM₀]
    have h₄ : ((2 : ℝ) ^ ((k : ℝ) + 2 - r)) ^ j = X ^ (-r) * X ^ 2 * X ^ k := by
      have e : (k : ℝ) + 2 - r = -r + 2 + k := by
        ring1
      rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, mul_comm, Real.rpow_mul zero_le_two,
        Real.rpow_natCast, ← hXdef, e, Real.rpow_add hX, Real.rpow_add hX, Real.rpow_two,
        Real.rpow_natCast]
    refine h₂.trans ((mul_le_mul_of_nonneg_left h₁ (by positivity)).trans_eq ?_)
    rw [h₃, h₄]
    ring1
  refine summable_of_sum_le (c := ∑' j : ℕ, M / κ ^ 2 * ((2 : ℝ) ^ ((k : ℝ) + 2 - r)) ^ j)
    (fun α ↦ by positivity) fun T ↦ ?_
  have h₁ : ∑ α ∈ T, ‖c α‖ ^ 2 * ‖σ (α.1 : K)‖ ^ (-r) = ∑ j ∈ T.image g, ∑ α ∈ T with g α = j,
      ‖c α‖ ^ 2 * ‖σ (α.1 : K)‖ ^ (-r) :=
    (Finset.sum_fiberwise_of_maps_to (fun α hα ↦ Finset.mem_image_of_mem g hα) _).symm
  have h₂ : Summable fun j : ℕ ↦ M / κ ^ 2 * ((2 : ℝ) ^ ((k : ℝ) + 2 - r)) ^ j :=
    (summable_geometric_of_lt_one hρ₀.le hρ₁).mul_left _
  rw [h₁]
  exact (Finset.sum_le_sum fun j _ ↦ hfib T j).trans (h₂.sum_le_tsum _ fun j _ ↦
    mul_nonneg (div_nonneg hM₀ (sq_nonneg _)) (pow_nonneg hρ₀.le _))

/-- **The first moment of the coefficients of a periodic cuspidal function**, under the hypotheses
of `IsBianchiCuspFunction.summable_sq_norm_coeff_mul_rpow`: for `s > k/2 + 2`,
`∑_{α ≠ 0} |c(α)| |α|^{-s} < ∞`. -/
lemma IsBianchiCuspFunction.summable_norm_coeff_mul_rpow (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hk' : Even k) (hk : k ≠ 0) (hδ : δ ^ 2 = discr K) (hH : IsBianchiCuspFunction σ k H)
    (hper : ∀ a : 𝓞 K, glSlash σ k (glUpper a) H = H)
    (hc : HasBianchiWhittakerExpansion σ δ k (extend H) c) {M : ℝ} (hM : ∀ z, bianchiNormSq H z ≤ M)
    (hs : (k : ℝ) / 2 + 2 < s) : Summable fun α : {α : 𝓞 K // α ≠ 0} ↦ ‖c α‖ * ‖σ α.1‖ ^ (-s) := by
  have h₁ : Summable fun α : {α : 𝓞 K // α ≠ 0} ↦ ‖c α‖ ^ 2 * ‖σ α.1‖ ^ (-((k : ℝ) / 2 + s)) :=
    hH.summable_sq_norm_coeff_mul_rpow hK hx hk' hk hδ hper hc hM (by linarith)
  have h₂ : Summable fun α : {α : 𝓞 K // α ≠ 0} ↦ ‖σ α.1‖ ^ ((k : ℝ) / 2 - s) :=
    summable_norm_rpow_apply hK hx (by linarith)
  refine Summable.of_nonneg_of_le (fun α ↦ by positivity) (fun α ↦ ?_) (h₁.add h₂)
  have ht : 0 < ‖σ (α.1 : K)‖ := one_pos.trans_le (one_le_norm_apply hK α.2)
  have e₁ : ‖σ (α.1 : K)‖ ^ (-s) = ‖σ (α.1 : K)‖ ^ (-((k : ℝ) / 2 + s) / 2) *
      ‖σ (α.1 : K)‖ ^ (((k : ℝ) / 2 - s) / 2) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring1
  have e₂ (w : ℝ) : (‖σ (α.1 : K)‖ ^ (w / 2)) ^ 2 = ‖σ (α.1 : K)‖ ^ w := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    norm_num
  have h₃ : 2 * (‖c α‖ * ‖σ (α.1 : K)‖ ^ (-((k : ℝ) / 2 + s) / 2)) *
      ‖σ (α.1 : K)‖ ^ (((k : ℝ) / 2 - s) / 2) ≤
        (‖c α‖ * ‖σ (α.1 : K)‖ ^ (-((k : ℝ) / 2 + s) / 2)) ^ 2 +
          (‖σ (α.1 : K)‖ ^ (((k : ℝ) / 2 - s) / 2)) ^ 2 :=
    two_mul_le_add_sq _ _
  rw [mul_pow, e₂, e₂] at h₃
  have h₄ : 0 ≤ ‖c α‖ * ‖σ (α.1 : K)‖ ^ (-((k : ℝ) / 2 + s) / 2) *
      ‖σ (α.1 : K)‖ ^ (((k : ℝ) / 2 - s) / 2) := by
    positivity
  rw [e₁, ← mul_assoc]
  linarith

variable [IsPrincipalIdealRing (𝓞 K)] {𝔑 : Ideal (𝓞 K)} [NeZero 𝔑]

/-- **The first moment of the coefficients of a Bianchi newform**: for `K` imaginary quadratic of
class number `1`, a newform of weight `k ≥ 1` with coefficients `c(α)`, and `s > k/2 + 2`,
`∑_{α ≠ 0} |c(α)| |α|^{-s} < ∞`. -/
lemma BianchiNewformOfWeight.summable_norm_coeff_mul_rpow (N : BianchiNewformOfWeight σ k 𝔑)
    (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hs : (k : ℝ) / 2 + 2 < s) :
    Summable fun α : {α : 𝓞 K // α ≠ 0} ↦ ‖N.coeff α‖ * ‖σ α.1‖ ^ (-s) := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  have hF : N.toFun ∈ bianchiCuspForms σ 𝔑.gamma0GL k :=
    bianchiNewSubspace_le σ k _ N.mem_bianchiNewSubspace
  have h𝔑 : 𝔑 ≠ ⊥ := NeZero.ne 𝔑
  rcases (mem_bianchiCuspForms_iff hK h𝔑).mp hF with ⟨hH, -⟩
  rcases exists_bianchiNormSq_le hK hk h𝔑 hF with ⟨M, hM⟩
  exact hH.summable_norm_coeff_mul_rpow hK hx (N.even hK) hk (cpow_ofNat_inv_pow _ 2)
    (hF.1.invariant.glSlash_glUpper h𝔑) N.hasWhittakerExpansion hM hs

end HyperbolicThreeSpace
