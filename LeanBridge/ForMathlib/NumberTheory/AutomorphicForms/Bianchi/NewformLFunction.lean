import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.LocalFactor
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# The analytic L-function of a Bianchi newform

Let `K` be an imaginary quadratic field of class number `1`, of discriminant `Δ`, embedded in `ℂ` by
`σ`, and `F` a Bianchi newform of weight `k ≥ 1` and level `𝔑 = (n)`, with sign `ε`. The Dirichlet
series `L(F, s) = ∑_𝔞 c(𝔞) N(𝔞)^{-s}` converges absolutely for `Re s > k/4 + 1`
(`HyperbolicThreeSpace.BianchiNewformOfWeight.summable_idealTerm`), and the completed L-function
`Λ(F, s)` of `F` is `(w / 16) (|n| |Δ|)^s Γ_ℂ(s)² L(F, s)` there, where `w` is the number of units
of `𝒪_K`. So `F` has an analytic L-function in the sense of the LMFDB
(`HyperbolicThreeSpace.BianchiNewformOfWeight.analyticLFunction`), of degree `4`, of conductor
`N(𝔑) Δ²`, with the gamma factor `Γ_ℂ(s + k/4)²` and with the sign `(-1)^{k/2+1} ε`. Hence the
analytic rank `r` of `F` exists
(`HyperbolicThreeSpace.BianchiNewformOfWeight.exists_isAnalyticRank`) and satisfies
`(-1)^{k/2+1} ε = (-1)^r`
(`HyperbolicThreeSpace.BianchiNewformOfWeight.neg_one_pow_mul_eq_neg_one_pow`): for `k = 2`, the
analytic rank of `F` is even when `F` has sign `+1`, and odd otherwise
(`HyperbolicThreeSpace.BianchiNewformOfWeight.eq_neg_one_pow_of_weight_two`).

## Main definitions

* `HyperbolicThreeSpace.BianchiNewformOfWeight.idealTerm`: the term `c(𝔞) N(𝔞)^{-z}` of the
  Dirichlet series.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.arithmeticL`: the entire function `L(F, z)`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.selbergData`: the data of the functional equation.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.analyticLFunction`: the analytic L-function of `F`.

## Main results

* `HyperbolicThreeSpace.BianchiNewformOfWeight.summable_idealTerm`: the Dirichlet series converges
  absolutely.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.hasSum_term`: the L-series in the analytic
  normalisation is the Dirichlet series over the ideals.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.exists_isAnalyticRank`: a newform has an analytic
  rank.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.neg_one_pow_mul_eq_neg_one_pow`: the sign and the
  parity of the analytic rank.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.eq_neg_one_pow_of_weight_two`: the same in weight
  `2`.
-/

open AnalyticLFunction Complex Module NumberField

open Submodule (IsPrincipal)

open scoped ComplexConjugate Real

namespace HyperbolicThreeSpace.BianchiNewformOfWeight

variable {z s : ℂ} {k : ℕ}

lemma natCast_half (hk' : Even k) : ((k / 2 : ℕ) : ℝ) = (k : ℝ) / 2 := by
  rcases hk' with ⟨m, rfl⟩
  have e : (m + m) / 2 = m := by
    omega
  rw [e]
  push_cast
  ring1

variable {K : Type*} [Field K] [NumberField K] {n : 𝓞 K} [NeZero n]

variable (n k) in
/-- The data of the functional equation of the L-function of a Bianchi newform of weight `k` and
level `(n)`, with sign `ε`: the conductor `N((n)) Δ²`, the gamma factor `Γ_ℂ(s + k/4)²` and the
sign `(-1)^{k/2+1} ε`. -/
noncomputable def selbergData (hk' : Even k) (hk : k ≠ 0) (ε : ℂ) :
    AnalyticLFunction.SelbergData where
  conductor := Ideal.absNorm (Ideal.span {n}) * (discr K).natAbs ^ 2
  μ := 0
  ν := {(k : ℂ) / 4, (k : ℂ) / 4}
  sign := (-1) ^ (k / 2 + 1) * ε
  conductor_pos := Nat.pos_of_ne_zero (mul_ne_zero
    ((Ideal.absNorm_eq_zero_iff).not.mpr (Ideal.span_singleton_eq_bot.not.mpr (NeZero.ne n)))
    (pow_ne_zero 2 (Int.natAbs_ne_zero.mpr (discr_ne_zero K))))
  re_eq_zero_or_one_of_mem_μ := by
    simp
  exists_two_mul_re_eq_of_mem_ν := by
    have h₀ : 0 < k / 2 := by
      rcases hk' with ⟨m, rfl⟩
      omega
    have h₁ : ∃ l : ℕ, 0 < l ∧ 2 * ((k : ℂ) / 4).re = l := by
      refine ⟨k / 2, h₀, ?_⟩
      rw [natCast_half hk']
      simp only [div_ofNat_re, natCast_re]
      ring1
    simpa using h₁
  im_sum_add_two_mul_sum := by
    simp

lemma degree_selbergData (hk' : Even k) (hk : k ≠ 0) (ε : ℂ) :
    (selbergData k n hk' hk ε).degree = 4 := by
  simp [SelbergData.degree, selbergData]

lemma gammaFactor_selbergData (hk' : Even k) (hk : k ≠ 0) (ε : ℂ) (w : ℂ) :
    (selbergData k n hk' hk ε).gammaFactor w = Gammaℂ (w + (k : ℂ) / 4) ^ 2 := by
  simp [SelbergData.gammaFactor, selbergData, sq]

lemma ofReal_norm_mul_abs_discr_ne_zero (τ : K →+* ℂ) :
    ((‖τ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ≠ 0 :=
  ofReal_ne_zero.mpr (mul_pos (norm_apply_pos τ n) (abs_discr_pos K)).ne'

variable [IsTotallyComplex K]

lemma card_units_ne_zero (τ : K →+* ℂ) (hK : finrank ℚ K = 2) : (Nat.card (𝓞 K)ˣ : ℂ) ≠ 0 :=
  have : Finite (𝓞 K)ˣ := finite_units τ hK
  Nat.cast_ne_zero.mpr Nat.card_pos.ne'

lemma natCast_absNorm_mul_eq (τ : K →+* ℂ) (hK : finrank ℚ K = 2) (a : 𝓞 K) :
    ((Ideal.absNorm (Ideal.span {a}) * (discr K).natAbs ^ 2 : ℕ) : ℝ) =
      (‖τ (a : K)‖ * |(discr K : ℝ)|) ^ 2 := by
  rw [mul_pow, sq_norm_apply_eq_absNorm τ hK]
  push_cast
  rw [Nat.cast_natAbs]
  push_cast
  rfl

variable [IsPrincipalIdealRing (𝓞 K)] {σ : K →+* ℂ} {𝔑 : Ideal (𝓞 K)} [NeZero 𝔑]
  (N : BianchiNewformOfWeight σ k 𝔑)

variable (z) in
/-- The term `c(𝔞) N(𝔞)^{-z}` of the Dirichlet series of a Bianchi newform over the ideals. -/
noncomputable def idealTerm (𝔞 : Ideal (𝓞 K)) : ℂ :=
  N.idealCoeff 𝔞 * (Ideal.absNorm 𝔞 : ℂ) ^ (-z)

lemma idealTerm_bot (hz : z ≠ 0) : N.idealTerm z ⊥ = 0 := by
  rw [idealTerm, Ideal.absNorm_bot, Nat.cast_zero, zero_cpow (neg_ne_zero.mpr hz), mul_zero]

/-- **The Dirichlet series of a Bianchi newform converges absolutely** for `Re z > k/4 + 1` (LMFDB
`mf.bianchi.anr`), by the second moment of its coefficients. -/
lemma summable_idealTerm (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hz : (k : ℝ) / 4 + 1 < z.re) :
    Summable (N.idealTerm z) := by
  have hz₀ : 0 < z.re := lt_of_le_of_lt (by positivity) hz
  have hz' : z ≠ 0 := fun h ↦ hz₀.ne' (by rw [h, zero_re])
  have h₁ : Summable fun α : {α : 𝓞 K // α ≠ 0} ↦ ‖N.coeff α‖ * ‖σ α.1‖ ^ (-(2 * z.re)) :=
    N.summable_norm_coeff_mul_rpow hK hk (by linarith)
  have hg : Function.Injective fun 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥} ↦
      (⟨IsPrincipal.generator 𝔞.1, generator_ne_zero 𝔞.2⟩ : {α : 𝓞 K // α ≠ 0}) := fun 𝔞 𝔟 h ↦ by
    have h₂ : IsPrincipal.generator 𝔞.1 = IsPrincipal.generator 𝔟.1 := congrArg Subtype.val h
    refine Subtype.ext ?_
    rw [← Ideal.span_singleton_generator 𝔞.1, ← Ideal.span_singleton_generator 𝔟.1, h₂]
  have h₂ : Summable fun 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥} ↦ ‖N.idealTerm z 𝔞.1‖ := by
    refine (h₁.comp_injective hg).congr fun 𝔞 ↦ ?_
    have hr : 0 < ‖σ ((IsPrincipal.generator 𝔞.1 : 𝓞 K) : K)‖ :=
      one_pos.trans_le (one_le_norm_apply hK (generator_ne_zero 𝔞.2))
    have hn : (Ideal.absNorm 𝔞.1 : ℝ) = ‖σ ((IsPrincipal.generator 𝔞.1 : 𝓞 K) : K)‖ ^ 2 :=
      (sq_norm_generator σ hK 𝔞.1).symm
    have hn₀ : 0 < (Ideal.absNorm 𝔞.1 : ℝ) := by
      rw [hn]
      positivity
    have e : ‖((Ideal.absNorm 𝔞.1 : ℕ) : ℂ) ^ (-z)‖ =
        ‖σ ((IsPrincipal.generator 𝔞.1 : 𝓞 K) : K)‖ ^ (-(2 * z.re)) := by
      have e₁ : ((Ideal.absNorm 𝔞.1 : ℕ) : ℂ) = ((Ideal.absNorm 𝔞.1 : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [e₁, norm_cpow_eq_rpow_re_of_pos hn₀, neg_re, hn, ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul hr.le]
      congr 1
      push_cast
      ring1
    simp only [idealTerm, norm_mul, e]
    rfl
  have h₃ : Summable (N.idealTerm z ∘ ((↑) : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥} → Ideal (𝓞 K))) :=
    h₂.of_norm
  refine (Subtype.val_injective.summable_iff fun 𝔞 h𝔞 ↦ ?_).mp h₃
  have h𝔞₀ : 𝔞 = ⊥ := by
    by_contra h₄
    exact h𝔞 ⟨⟨𝔞, h₄⟩, rfl⟩
  rw [h𝔞₀, N.idealTerm_bot hz']

lemma tsum_fiber_idealTerm (m : ℕ) :
    ∑' 𝔞 : Ideal.absNorm ⁻¹' {m}, N.idealTerm z 𝔞.1 = N.normCoeff m * (m : ℂ) ^ (-z) := by
  have hfin : Finite (Ideal.absNorm ⁻¹' {m} : Set (Ideal (𝓞 K))) :=
    (Ideal.finite_setOfPred_absNorm_eq m).to_subtype
  rw [tsum_eq_finsum (Set.toFinite _), finsum_set_coe_eq_finsum_mem, normCoeff, finsum_mem_mul]
  refine finsum_mem_congr rfl fun 𝔞 h𝔞 ↦ ?_
  have h₁ : Ideal.absNorm 𝔞 = m := h𝔞
  rw [idealTerm, h₁]

lemma term_eq (hs : s + (k : ℂ) / 4 ≠ 0) (m : ℕ) :
    LSeries.term N.lCoeff s m = N.normCoeff m * (m : ℂ) ^ (-(s + (k : ℂ) / 4)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [LSeries.term_zero, Nat.cast_zero, zero_cpow (neg_ne_zero.mpr hs), mul_zero]
  have hm₀ : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have e : (((m : ℝ) ^ ((k : ℝ) / 4) : ℝ) : ℂ) = (m : ℂ) ^ ((k : ℂ) / 4) := by
    rw [ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
  rw [LSeries.term_of_ne_zero hm, lCoeff_eq, e, neg_add, cpow_add _ _ hm₀, cpow_neg, cpow_neg]
  field_simp

/-- **The L-series of a Bianchi newform is its Dirichlet series over the ideals**, for `Re s > 1`,
in the analytic normalisation. -/
lemma hasSum_term (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hs : 1 < s.re) :
    HasSum (LSeries.term N.lCoeff s) (∑' 𝔞, N.idealTerm (s + (k : ℂ) / 4) 𝔞) := by
  have hre : (s + (k : ℂ) / 4).re = s.re + (k : ℝ) / 4 := by
    simp
  have hz : (k : ℝ) / 4 + 1 < (s + (k : ℂ) / 4).re := by
    rw [hre]
    linarith
  have hz₀ : s + (k : ℂ) / 4 ≠ 0 := fun h ↦ by
    have h₁ : (0 : ℝ) ≤ (k : ℝ) / 4 := by
      positivity
    rw [h, zero_re] at hz
    linarith
  have h₁ : HasSum (fun m ↦ ∑' 𝔞 : Ideal.absNorm ⁻¹' {m}, N.idealTerm (s + (k : ℂ) / 4) 𝔞.1)
      (∑' 𝔞, N.idealTerm (s + (k : ℂ) / 4) 𝔞) :=
    (N.summable_idealTerm hK hk hz).hasSum.tsum_fiberwise Ideal.absNorm
  simp only [N.tsum_fiber_idealTerm] at h₁
  exact h₁.congr_fun fun m ↦ N.term_eq hz₀ m

lemma lSeriesSummable_lCoeff (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hs : 1 < s.re) :
    LSeriesSummable N.lCoeff s :=
  (N.hasSum_term hK hk hs).summable

lemma lSeries_lCoeff (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hs : 1 < s.re) :
    LSeries N.lCoeff s = ∑' 𝔞, N.idealTerm (s + (k : ℂ) / 4) 𝔞 :=
  (N.hasSum_term hK hk hs).tsum_eq

lemma conj_lCoeff (hK : finrank ℚ K = 2) (hk : k ≠ 0) (m : ℕ) (hm : m ≠ 0) :
    conj (N.lCoeff m) = N.lCoeff m := by
  have hS : {𝔫 : Ideal (𝓞 K) | Ideal.absNorm 𝔫 = m}.Finite := Ideal.finite_setOfPred_absNorm_eq m
  have h₁ : conj (N.normCoeff m) = N.normCoeff m := by
    rw [normCoeff, finsum_mem_eq_finite_toFinset_sum _ hS, map_sum]
    refine Finset.sum_congr rfl fun 𝔞 h𝔞 ↦ N.conj_idealCoeff hK hk fun h₀ ↦ hm ?_
    have h₂ : Ideal.absNorm 𝔞 = m := hS.mem_toFinset.mp h𝔞
    rw [← h₂, h₀, Ideal.absNorm_bot]
  rw [lCoeff_eq, map_div₀, h₁, conj_ofReal]

variable (z) in
lemma mul_cpow_aux {d : ℝ} (hd : 0 < d) : ((4 * π / √d : ℝ) : ℂ) ^ (-(2 * z)) * (2 ^ (2 * z - 2)) =
    (d : ℂ) ^ z * ((2 * π : ℂ) ^ (-z)) ^ 2 / 4 := by
  have hs : 0 < √d := Real.sqrt_pos.mpr hd
  have e₁ : ((4 * π / √d : ℝ) : ℂ) = ((2 * (2 * π) : ℝ) : ℂ) * (((√d)⁻¹ : ℝ) : ℂ) := by
    rw [← ofReal_mul]
    congr 1
    rw [div_eq_mul_inv]
    ring1
  have e₂ : (((√d)⁻¹ : ℝ) : ℂ) ^ (-(2 * z)) = (d : ℂ) ^ z := by
    have h₁ : ((√d)⁻¹ : ℝ) ^ 2 = d⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hd.le]
    rw [cpow_neg_two_mul_eq (inv_pos.mpr hs), h₁, ofReal_inv, inv_cpow _ _ ?_, cpow_neg, inv_inv]
    rw [arg_ofReal_of_nonneg hd.le]
    exact Real.pi_pos.ne
  have e₃ : ((2 : ℝ) : ℂ) ^ (-(2 * z)) * 2 ^ (2 * z - 2) = 4⁻¹ := by
    have e₄ : (2 : ℂ) ^ (-(2 * z)) * 2 ^ (2 * z - 2) = 2 ^ (-(2 : ℂ)) := by
      rw [← cpow_add _ _ two_ne_zero]
      congr 1
      ring1
    rw [ofReal_ofNat, e₄, cpow_neg, cpow_ofNat]
    norm_num
  have e₅ : ((2 * π : ℝ) : ℂ) ^ (-(2 * z)) = ((2 * π : ℂ) ^ (-z)) ^ 2 := by
    have e₆ : -(2 * z) = ((2 : ℕ) : ℂ) * -z := by
      push_cast
      ring1
    rw [e₆, cpow_nat_mul]
    push_cast
    rfl
  have h2π : (0 : ℝ) ≤ 2 * π := by
    positivity
  rw [e₁, mul_cpow_ofReal_nonneg (by positivity) (inv_pos.mpr hs).le, ofReal_mul 2 (2 * π),
    mul_cpow_ofReal_nonneg zero_le_two h2π, e₂, e₅]
  linear_combination ((2 * π : ℂ) ^ (-z)) ^ 2 * (d : ℂ) ^ z * e₃

variable (F : BianchiNewformOfWeight σ k (Ideal.span {n})) {ε : ℂ}

lemma completedL_eq_tsum_idealTerm (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (hz : (k / 2 : ℕ) + 3 < (2 * z).re) : F.completedL z = (Nat.card (𝓞 K)ˣ : ℂ) / 16 *
    ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ z * Gammaℂ z ^ 2 * ∑' 𝔞, F.idealTerm z 𝔞 := by
  have hd : 0 < |(discr K : ℝ)| := abs_discr_pos K
  have hz₀ : z ≠ 0 := fun h ↦ by
    rw [h, mul_zero, zero_re] at hz
    have h₁ : (0 : ℝ) ≤ (k / 2 : ℕ) := Nat.cast_nonneg _
    linarith
  have hsub : ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥}, F.idealCoeff 𝔞 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-z) =
      ∑' 𝔞, F.idealTerm z 𝔞 :=
    tsum_subtype_eq_of_support_subset (f := F.idealTerm z) (s := {𝔞 : Ideal (𝓞 K) | 𝔞 ≠ ⊥})
      fun 𝔞 h𝔞 h₀ ↦ h𝔞 (h₀ ▸ F.idealTerm_bot hz₀)
  have h : ((4 * π / √|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(2 * z)) * (2 ^ (2 * z - 2)) =
      ((|(discr K : ℝ)| : ℝ) : ℂ) ^ z * ((2 * π : ℂ) ^ (-z)) ^ 2 / 4 := mul_cpow_aux z hd
  rw [completedL_eq_tsum hK hk hz, tsum_coeff_mul_norm_cpow_eq hK hk hz, hsub, ofReal_mul,
    mul_cpow_ofReal_nonneg (norm_nonneg _) hd.le, Gammaℂ_def]
  linear_combination (((‖σ (n : K)‖ : ℝ) : ℂ) ^ z * Gamma z ^ 2 * ((Nat.card (𝓞 K)ˣ : ℂ) *
    ∑' 𝔞, F.idealTerm z 𝔞)) * h

variable (z) in
/-- The L-function `L(F, z)` of a Bianchi newform `F` of level `(n)` in the arithmetic
normalisation: `(16 / w) (|n| |Δ|)^{-z} Γ_ℂ(z)^{-2} Λ(F, z)`, where `w` is the number of units of
`𝒪_K`. It is entire, and equal to the Dirichlet series `∑_𝔞 c(𝔞) N(𝔞)^{-z}` for `Re z` large. -/
noncomputable def arithmeticL : ℂ :=
  (16 / (Nat.card (𝓞 K)ˣ : ℂ)) * ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ (-z) *
    (Gammaℂ z)⁻¹ ^ 2 * F.completedL z

lemma arithmeticL_eq_tsum (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hz : (k / 2 : ℕ) + 3 < (2 * z).re) :
    F.arithmeticL z = ∑' 𝔞, F.idealTerm z 𝔞 := by
  have hR : ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := ofReal_norm_mul_abs_discr_ne_zero σ
  have hre : 0 < z.re := by
    have h₁ : (0 : ℝ) ≤ (k / 2 : ℕ) := Nat.cast_nonneg _
    have h₂ : (2 * z).re = 2 * z.re := by
      simp
    linarith
  have hG : Gammaℂ z ≠ 0 := Gammaℂ_ne_zero_of_re_pos hre
  have hw : (Nat.card (𝓞 K)ˣ : ℂ) ≠ 0 := card_units_ne_zero σ hK
  rw [arithmeticL, F.completedL_eq_tsum_idealTerm hK hk hz, cpow_neg]
  have hRz : ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ z ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl hR)
  field_simp

lemma differentiable_arithmeticL (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hs : F.HasSign ε) :
    Differentiable ℂ F.arithmeticL := by
  have h₁ : Differentiable ℂ fun w : ℂ ↦ ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ (-w) :=
    differentiable_id.neg.const_cpow (Or.inl (ofReal_norm_mul_abs_discr_ne_zero σ))
  have h₂ : Differentiable ℂ fun w : ℂ ↦ (Gammaℂ w)⁻¹ ^ 2 := differentiable_Gammaℂ_inv.pow 2
  exact ((h₁.const_mul _).mul h₂).mul (differentiable_completedL hK hk hs)

lemma arithmeticL_add_eq_lSeries (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hs : F.HasSign ε)
    (h : 1 < s.re) : F.arithmeticL (s + (k : ℂ) / 4) = LSeries F.lCoeff s := by
  have hk' : Even k := F.even hK
  have hf : AnalyticOnNhd ℂ (fun w ↦ F.arithmeticL (w + (k : ℂ) / 4)) {w | 1 < w.re} := fun w _ ↦
    (((F.differentiable_arithmeticL hK hk hs).comp (differentiable_id.add_const _)).analyticAt w)
  have habs : LSeries.abscissaOfAbsConv F.lCoeff ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun y hy ↦
      F.lSeriesSummable_lCoeff hK hk (by
        rw [ofReal_re]
        exact EReal.coe_lt_coe_iff.mp hy)
  have hg : AnalyticOnNhd ℂ (LSeries F.lCoeff) {w | 1 < w.re} :=
    (LSeries_analyticOnNhd F.lCoeff).mono fun w hw ↦
      lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hw)
  have he : (fun w ↦ F.arithmeticL (w + (k : ℂ) / 4)) =ᶠ[nhds (2 : ℂ)] LSeries F.lCoeff := by
    filter_upwards [(continuous_re.isOpen_preimage (Set.Ioi (3 / 2)) isOpen_Ioi).mem_nhds
      (by norm_num : (2 : ℂ) ∈ re ⁻¹' Set.Ioi (3 / 2))] with w hw
    have hw' : (3 / 2 : ℝ) < w.re := hw
    rw [F.arithmeticL_eq_tsum hK hk, F.lSeries_lCoeff hK hk (by linarith)]
    have e : (2 * (w + (k : ℂ) / 4)).re = 2 * w.re + (k : ℝ) / 2 := by
      simp only [mul_re, add_re, re_ofNat, im_ofNat, div_ofNat_re, natCast_re]
      ring1
    rw [e, natCast_half hk']
    linarith
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt 1).isPreconnected
    (by norm_num : (2 : ℂ) ∈ {w : ℂ | 1 < w.re}) he h

lemma conj_completedL (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hs : F.HasSign ε) (w : ℂ) :
    conj (F.completedL (conj w)) = F.completedL w := by
  have hd : Differentiable ℂ F.completedL := differentiable_completedL hK hk hs
  have hg : Differentiable ℂ (conj ∘ F.completedL ∘ conj) := fun v ↦ by
    simpa using (hd (conj v)).conj_conj
  have he : conj ∘ F.completedL ∘ conj =ᶠ[nhds ((((k / 2 : ℕ) : ℝ) + 4 : ℝ) : ℂ)] F.completedL := by
    have hm : (0 : ℝ) ≤ (k / 2 : ℕ) := Nat.cast_nonneg _
    filter_upwards [(continuous_re.isOpen_preimage (Set.Ioi (((k / 2 : ℕ) : ℝ) + 3))
      isOpen_Ioi).mem_nhds (by
        rw [Set.mem_preimage, Set.mem_Ioi, ofReal_re]
        linarith : (((((k / 2 : ℕ) : ℝ) + 4 : ℝ) : ℂ)) ∈ re ⁻¹' Set.Ioi (((k / 2 : ℕ) : ℝ) + 3))]
      with v hv
    have hv' : ((k / 2 : ℕ) : ℝ) + 3 < v.re := hv
    have hv₀ : v ≠ 0 := fun h ↦ by
      rw [h, zero_re] at hv'
      linarith
    have hre : (2 * v).re = 2 * v.re := by
      simp
    have hre' : (2 * conj v).re = 2 * v.re := by
      simp
    have h₁ : (k / 2 : ℕ) + 3 < (2 * v).re := by
      rw [hre]
      linarith
    have h₂ : (k / 2 : ℕ) + 3 < (2 * conj v).re := by
      rw [hre']
      linarith
    have hterm (𝔞 : Ideal (𝓞 K)) : conj (F.idealTerm (conj v) 𝔞) = F.idealTerm v 𝔞 := by
      rcases eq_or_ne 𝔞 ⊥ with rfl | h𝔞
      · rw [F.idealTerm_bot (by simpa using hv₀), F.idealTerm_bot hv₀, map_zero]
      · have e : -conj v = conj (-v) := by
          rw [map_neg]
        rw [idealTerm, idealTerm, map_mul, F.conj_idealCoeff hK hk h𝔞, e,
          Complex.conj_natCast_cpow_conj]
    simp only [Function.comp_apply]
    rw [F.completedL_eq_tsum_idealTerm hK hk h₂, F.completedL_eq_tsum_idealTerm hK hk h₁, map_mul,
      map_mul, map_mul, map_div₀, map_natCast, map_ofNat,
      conj_ofReal_cpow_conj (mul_nonneg (norm_nonneg _) (abs_nonneg _)), map_pow, ← Gammaℂ_conj,
      conj_conj, conj_tsum]
    simp only [hterm]
  exact congrFun (AnalyticOnNhd.eq_of_eventuallyEq (fun v _ ↦ hg.analyticAt v)
    (fun v _ ↦ hd.analyticAt v) he) w

lemma completed_eq_aux (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hk' : Even k) {w : ℂ} (h : 1 < w.re) :
    16 / (Nat.card (𝓞 K)ˣ : ℂ) * ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ (-((k : ℂ) / 4)) *
      F.completedL (w + (k : ℂ) / 4) = ((selbergData k n hk' hk ε).conductor : ℂ) ^ (w / 2) *
        (selbergData k n hk' hk ε).gammaFactor w * F.arithmeticL (w + (k : ℂ) / 4) := by
  have hR₀ : 0 < ‖σ (n : K)‖ * |(discr K : ℝ)| := mul_pos (norm_apply_pos σ n) (abs_discr_pos K)
  have hR : ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := ofReal_norm_mul_abs_discr_ne_zero σ
  have hre : 0 < (w + (k : ℂ) / 4).re := by
    have h₁ : (w + (k : ℂ) / 4).re = w.re + (k : ℝ) / 4 := by
      simp
    have h₂ : (0 : ℝ) ≤ (k : ℝ) / 4 := by
      positivity
    rw [h₁]
    linarith
  have hG : Gammaℂ (w + (k : ℂ) / 4) ≠ 0 := Gammaℂ_ne_zero_of_re_pos hre
  have hQ : ((selbergData k n hk' hk ε).conductor : ℂ) ^ (w / 2) =
      ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ w := by
    have e₀ : ((selbergData k n hk' hk ε).conductor : ℂ) =
        (((‖σ (n : K)‖ * |(discr K : ℝ)|) ^ 2 : ℝ) : ℂ) := by
      rw [← natCast_absNorm_mul_eq σ hK n]
      rfl
    have e₁ : ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ (-(2 * -(w / 2))) =
        (((‖σ (n : K)‖ * |(discr K : ℝ)|) ^ 2 : ℝ) : ℂ) ^ (- -(w / 2)) :=
      cpow_neg_two_mul_eq hR₀ _
    have e₂ : -(2 * -(w / 2)) = w := by
      ring1
    rw [e₂, neg_neg] at e₁
    rw [e₀, e₁]
  have e₃ : ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ (-((k : ℂ) / 4)) =
      ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ w *
        ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ (-(w + (k : ℂ) / 4)) := by
    rw [← cpow_add _ _ hR]
    congr 1
    ring1
  have h₁ : Gammaℂ (w + (k : ℂ) / 4) ^ 2 * (Gammaℂ (w + (k : ℂ) / 4))⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hG, one_pow]
  rw [hQ, gammaFactor_selbergData, arithmeticL, e₃]
  linear_combination (-(16 / (Nat.card (𝓞 K)ˣ : ℂ) *
    ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ w *
      ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ (-(w + (k : ℂ) / 4)) *
        F.completedL (w + (k : ℂ) / 4))) * h₁

lemma completed_eq_sign_mul_conj_aux (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hs : F.HasSign ε)
    (w : ℂ) : 16 / (Nat.card (𝓞 K)ˣ : ℂ) *
      ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ (-((k : ℂ) / 4)) *
        F.completedL (w + (k : ℂ) / 4) = ((-1) ^ (k / 2 + 1) * ε) *
          conj (16 / (Nat.card (𝓞 K)ˣ : ℂ) *
            ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ (-((k : ℂ) / 4)) *
              F.completedL (1 - conj w + (k : ℂ) / 4)) := by
  have hk' : Even k := F.even hK
  have hd : 0 ≤ |(discr K : ℝ)| := abs_nonneg _
  have hκ : conj ((k : ℂ) / 4) = (k : ℂ) / 4 := by
    rw [map_div₀, map_natCast, map_ofNat]
  have hm : ((k / 2 : ℕ) : ℂ) = (k : ℂ) / 2 := by
    have h : (((k / 2 : ℕ) : ℝ) : ℂ) = (((k : ℝ) / 2 : ℝ) : ℂ) := congrArg _ (natCast_half hk')
    push_cast at h
    exact h
  have e : 1 - conj w + (k : ℂ) / 4 = ((k / 2 : ℕ) : ℂ) + 1 - conj (w + (k : ℂ) / 4) := by
    rw [map_add, hκ, hm]
    ring1
  have hR : conj (((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ (-((k : ℂ) / 4))) =
      ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ (-((k : ℂ) / 4)) := by
    have h₁ : conj (((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ conj (-((k : ℂ) / 4))) =
        ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ (-((k : ℂ) / 4)) :=
      conj_ofReal_cpow_conj (mul_nonneg (norm_nonneg _) hd) _
    rwa [map_neg, hκ] at h₁
  have hρ : conj ((-1 : ℂ) ^ (k / 2 + 1) * ε) * ((-1) ^ (k / 2 + 1) * ε) = 1 := by
    rcases hs.eq_one_or_eq_neg_one (F.toFun_ne_zero hK) with rfl | rfl
    · rcases neg_one_pow_eq_or ℂ (k / 2 + 1) with h | h <;> simp [h]
    · rcases neg_one_pow_eq_or ℂ (k / 2 + 1) with h | h <;> simp [h]
  have hconj : conj (F.completedL (conj (w + (k : ℂ) / 4))) = F.completedL (w + (k : ℂ) / 4) :=
    F.conj_completedL hK hk hs _
  rw [e, completedL_add_one_sub hK hs, map_mul, map_mul, map_mul, map_div₀, map_natCast, map_ofNat,
    hR, hconj]
  linear_combination (-(16 / (Nat.card (𝓞 K)ˣ : ℂ)) *
    ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ (-((k : ℂ) / 4)) *
      F.completedL (w + (k : ℂ) / 4)) * hρ

/-- **The analytic L-function of a Bianchi newform** (LMFDB `lfunction`, `mf.bianchi.anr`,
`mf.bianchi.sign`): for `K` imaginary quadratic of class number `1`, a newform `F` of weight `k ≥ 1`
and level `(n)` with sign `ε` has an analytic L-function, of degree `4` and conductor `N((n)) Δ²`,
with the Dirichlet coefficients `aₘ = m^{-k/4} ∑_{N(𝔞) = m} c(𝔞)`, the gamma factor `Γ_ℂ(s + k/4)²`
and the sign `(-1)^{k/2+1} ε`. -/
noncomputable def analyticLFunction (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hs : F.HasSign ε) :
    AnalyticLFunction where
  coeff := F.lCoeff
  toFun w := F.arithmeticL (w + (k : ℂ) / 4)
  completed w := 16 / (Nat.card (𝓞 K)ˣ : ℂ) *
    ((‖σ (n : K)‖ * |(discr K : ℝ)| : ℝ) : ℂ) ^ (-((k : ℂ) / 4)) * F.completedL (w + (k : ℂ) / 4)
  selbergData := selbergData k n (F.even hK) hk ε
  coeff_one := F.lCoeff_one hK
  coeff_mul_of_coprime h := F.lCoeff_mul hK hk h
  exists_eulerFactor p hp := by
    rw [degree_selbergData]
    exact F.exists_eulerFactor hK hk hp
  LSeriesSummable_coeff h := F.lSeriesSummable_lCoeff hK hk h
  toFun_eq_LSeries h := F.arithmeticL_add_eq_lSeries hK hk hs h
  differentiableOn_toFun :=
    ((F.differentiable_arithmeticL hK hk hs).comp (differentiable_id.add_const _)).differentiableOn
  meromorphicAt_toFun :=
    (((F.differentiable_arithmeticL hK hk hs).comp
      (differentiable_id.add_const _)).analyticAt 1).meromorphicAt
  completed_eq h := F.completed_eq_aux hK hk (F.even hK) h
  differentiableOn_completed :=
    (((differentiable_completedL hK hk hs).comp
      (differentiable_id.add_const _)).const_mul _).differentiableOn
  completed_eq_sign_mul_conj {w} _ _ := F.completed_eq_sign_mul_conj_aux hK hk hs w

lemma coeff_analyticLFunction (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hs : F.HasSign ε) :
    (F.analyticLFunction hK hk hs).coeff = F.lCoeff :=
  rfl

lemma sign_analyticLFunction (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hs : F.HasSign ε) :
    (F.analyticLFunction hK hk hs).sign = (-1) ^ (k / 2 + 1) * ε :=
  rfl

variable {r : ℕ}

/-- **A Bianchi newform has an analytic rank** (LMFDB `mf.bianchi.anr`), for `K` imaginary quadratic
of class number `1` and in weight `k ≥ 1`: the level `𝔑` is principal, and `analyticLFunction` is an
analytic L-function with the Dirichlet coefficients of the newform. -/
lemma exists_isAnalyticRank (hK : finrank ℚ K = 2) (hk : k ≠ 0) : ∃ r, N.IsAnalyticRank r := by
  rcases exists_span_eq (NeZero.ne 𝔑) with ⟨n, rfl⟩
  exact ⟨_, N.analyticLFunction hK hk (N.hasSign_sign_exists (n : 𝓞 K) hK hk), fun _ _ ↦ rfl, rfl⟩

/-- **The sign of a Bianchi newform and the parity of its analytic rank** (LMFDB `mf.bianchi.sign`,
`mf.bianchi.anr`): for a newform of weight `k ≥ 1` and level `(n)`, with sign `ε` and analytic rank
`r`, `(-1)^{k/2+1} ε = (-1)^r`. -/
lemma neg_one_pow_mul_eq_neg_one_pow (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hs : F.HasSign ε)
    (hr : F.IsAnalyticRank r) : (-1) ^ (k / 2 + 1) * ε = (-1) ^ r :=
  hr.sign_eq_neg_one_pow (F.conj_lCoeff hK hk) (L := F.analyticLFunction hK hk hs) fun _ _ ↦ rfl

/-- **In weight `2`, the analytic rank of a Bianchi newform is even when its sign is `+1`, and odd
otherwise** (LMFDB `mf.bianchi.sign`): `ε = (-1)^r`. -/
lemma eq_neg_one_pow_of_weight_two {G : BianchiNewformOfWeight σ 2 (Ideal.span {n})}
    (hK : finrank ℚ K = 2) (hs : G.HasSign ε) (hr : G.IsAnalyticRank r) : ε = (-1) ^ r := by
  have h : (-1) ^ (2 / 2 + 1) * ε = (-1) ^ r :=
    G.neg_one_pow_mul_eq_neg_one_pow hK two_ne_zero hs hr
  norm_num at h
  exact h

end HyperbolicThreeSpace.BianchiNewformOfWeight
