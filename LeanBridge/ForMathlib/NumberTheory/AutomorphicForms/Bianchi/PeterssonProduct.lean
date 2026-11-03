import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.FiniteDimensional

/-!
# The Petersson product of Bianchi cusp forms

Let `K` be an imaginary quadratic field of class number `1`, embedded in `ℂ` by `σ`, and `𝔑 ≠ 0` an
ideal of `𝒪_K`. By reduction theory, `ℋ₃` is covered by the translates under `Γ̄₀(𝔑)` of a set of
finite hyperbolic volume, a finite union of translates of the Siegel set
`{(x, y) : x ∈ P, y ≥ y₀}`. So **the fundamental domains of `Γ̄₀(𝔑)` have finite volume**
(`HyperbolicThreeSpace.hyperbolicVolume_lt_top`). As the invariant norm of a cusp form is bounded
(`HyperbolicThreeSpace.exists_bianchiNormSq_le`), the function `y^k ⟨F, G⟩_k` is integrable on the
fundamental domains, for `F`, `G` in `S_k(𝔑)`, and the **Petersson product**
`⟨F, G⟩ = ∫_{Γ̄₀(𝔑) \ ℋ₃} y^k ⟨F, G⟩_k dμ` (`HyperbolicThreeSpace.bianchiPetersson`), which does not
depend on the fundamental domain (`HyperbolicThreeSpace.bianchiPetersson_eq`), is a positive
definite Hermitian form on `S_k(𝔑)`.

## Main definitions

* `HyperbolicThreeSpace.bianchiPetersson` (LMFDB `mf.bianchi.spaces`): the Petersson product.

## Main results

* `HyperbolicThreeSpace.exists_hyperbolicVolume_lt_top_forall_exists`: `ℋ₃` is covered by the
  translates under `Γ₀(𝔑)` of a set of finite volume.
* `HyperbolicThreeSpace.hyperbolicVolume_lt_top`: the fundamental domains of `Γ̄₀(𝔑)` have finite
  volume.
* `HyperbolicThreeSpace.integrableOn_bianchiPairing`: the Petersson integrand of two cusp forms is
  integrable on the fundamental domains.
* `HyperbolicThreeSpace.bianchiPetersson_eq`: the Petersson product is computed on any fundamental
  domain.
* `HyperbolicThreeSpace.conj_bianchiPetersson`: the Petersson product is Hermitian.
* `HyperbolicThreeSpace.bianchiPetersson_add_left`,
  `HyperbolicThreeSpace.bianchiPetersson_smul_left`: it is linear in the first variable.
* `HyperbolicThreeSpace.bianchiPetersson_self_eq_ofReal`: it is nonnegative on the diagonal.
* `HyperbolicThreeSpace.bianchiPetersson_self_eq_zero_iff`: it is definite on `S_k(𝔑)`.
* `HyperbolicThreeSpace.integrableOn_bianchiPairing_of_le`: integrability of the integrand of two
  bounded functions on a set of finite volume.
* `HyperbolicThreeSpace.bianchiOldforms_le_bianchiCuspForms`: the oldforms are cusp forms.
* `HyperbolicThreeSpace.mem_bianchiNewSubspace_iff`: the newspace is the orthogonal complement of
  the oldforms for the Petersson product.
-/

open Complex Matrix MeasureTheory Module NumberField HilbertModularGroup Set

open scoped ComplexConjugate ENNReal MatrixGroups nonZeroDivisors Pointwise Real

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] {σ : K →+* ℂ} {k : ℕ} {𝔑 : Ideal (𝓞 K)}
  {F G F' : HyperbolicThreeSpace → Fin (k + 1) → ℂ}

lemma hyperbolicVolume_siegelSet_lt_top {P : Set ℂ} (hP : Bornology.IsBounded P)
    (hPm : MeasurableSet P) {y₀ : ℝ} (hy₀ : 0 < y₀) :
    hyperbolicVolume {z : HyperbolicThreeSpace | z.coords.1 ∈ P ∧ y₀ ≤ z.coords.2} < ⊤ := by
  have hco : Continuous (coords : HyperbolicThreeSpace → ℂ × ℝ) := isOpenEmbedding_coords.continuous
  have hA : MeasurableSet {z : HyperbolicThreeSpace | z.coords.1 ∈ P ∧ y₀ ≤ z.coords.2} :=
    (hco.fst.measurable hPm).inter (hco.snd.measurable measurableSet_Ici)
  rw [hyperbolicVolume_apply hA]
  have hsub :
      coords '' {z : HyperbolicThreeSpace | z.coords.1 ∈ P ∧ y₀ ≤ z.coords.2} ⊆ P ×ˢ Ici y₀ := by
    rintro _ ⟨z, hz, rfl⟩
    exact hz
  refine (lintegral_mono_set hsub).trans_lt ?_
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ (by fun_prop)]
  simp only [lintegral_const]
  have hI : ∫⁻ y in Ici y₀, ENNReal.ofReal (y ^ 3)⁻¹ < ⊤ := by
    rw [setLIntegral_congr Ioi_ae_eq_Ici.symm]
    have hint : IntegrableOn (fun y : ℝ ↦ y ^ (-3 : ℝ)) (Ioi y₀) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) hy₀
    have he : ∫⁻ y in Ioi y₀, ENNReal.ofReal (y ^ 3)⁻¹ =
        ∫⁻ y in Ioi y₀, ENNReal.ofReal (y ^ (-3 : ℝ)) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
      have hy' : 0 < y := hy₀.trans hy
      rw [Real.rpow_neg hy'.le, Real.rpow_ofNat]
    rw [he]
    exact hint.lintegral_lt_top
  have hP' : volume P < ⊤ := hP.measure_lt_top
  rw [Measure.restrict_apply_univ]
  exact ENNReal.mul_lt_top hI hP'

variable (F G) in
lemma norm_bianchiPairing_le (z : HyperbolicThreeSpace) :
    ‖bianchiPairing F G z‖ ≤ (bianchiNormSq F z + bianchiNormSq G z) / 2 := by
  have hy : 0 ≤ z.height ^ k := pow_nonneg z.height_pos.le k
  rw [bianchiPairing, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg z.height_pos.le,
    symPowInner, bianchiNormSq, bianchiNormSq, ← mul_add, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hy
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [norm_mul, norm_mul, RCLike.norm_conj, norm_natCast]
  have h₀ : 0 ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg h₀ (sq_nonneg (‖F z i‖ - ‖G z i‖))]

lemma continuous_bianchiPairing (hF : Continuous F) (hG : Continuous G) :
    Continuous (bianchiPairing F G) := by
  have hco : Continuous (coords : HyperbolicThreeSpace → ℂ × ℝ) :=
    isOpenEmbedding_coords.continuous
  have hh : Continuous fun z : HyperbolicThreeSpace ↦ z.height := hco.snd
  have hi (i : Fin (k + 1)) : Continuous fun z ↦ F z i := (continuous_apply i).comp hF
  have hj (i : Fin (k + 1)) : Continuous fun z ↦ G z i := (continuous_apply i).comp hG
  unfold bianchiPairing symPowInner
  fun_prop

lemma bianchiPairing_smul_bianchiPSLGroup {Γ : Subgroup (GL (Fin 2) K)}
    (hF : F ∈ bianchiSlashInvariants σ k Γ) (hG : G ∈ bianchiSlashInvariants σ k Γ)
    (γ : bianchiPSLGroup σ Γ) (z : HyperbolicThreeSpace) :
    bianchiPairing F G (γ • z) = bianchiPairing F G z := by
  rcases γ with ⟨_, g, ⟨x, hx, hg⟩, rfl⟩
  have e : (⟨QuotientGroup.mk' _ g, g, ⟨x, hx, hg⟩, rfl⟩ : bianchiPSLGroup σ Γ) • z = g • z :=
    rfl
  rw [e, ← bianchiPairing_bianchiSlash, hF x hx g hg, hG x hx g hg]

lemma conj_bianchiPairing (z : HyperbolicThreeSpace) :
    conj (bianchiPairing F G z) = bianchiPairing G F z := by
  simp only [bianchiPairing, symPowInner, map_mul, map_pow, conj_ofReal, map_sum, map_natCast,
    Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by ring1

lemma bianchiPairing_add_left (z : HyperbolicThreeSpace) :
    bianchiPairing (F + F') G z = bianchiPairing F G z + bianchiPairing F' G z := by
  simp only [bianchiPairing, Pi.add_apply, symPowInner_add_left, mul_add]

lemma bianchiPairing_smul_left (a : ℂ) (z : HyperbolicThreeSpace) :
    bianchiPairing (a • F) G z = a * bianchiPairing F G z := by
  simp only [bianchiPairing, Pi.smul_apply, symPowInner_smul_left]
  ring1

variable [NumberField K] [IsTotallyComplex K]

open scoped Classical in
variable (σ k 𝔑 F G) in
/-- The **Petersson product** `⟨F, G⟩ = ∫_{Γ̄₀(𝔑) \ ℋ₃} y^k ⟨F(z), G(z)⟩_k dμ` (LMFDB
`mf.bianchi.spaces`) of `F`, `G` of level `Γ₀(𝔑)`: the integral over a fundamental domain of
`Γ̄₀(𝔑)`, which does not depend on it (`bianchiPetersson_eq`). -/
noncomputable def bianchiPetersson : ℂ :=
  if h : ∃ s, IsFundamentalDomain (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) s hyperbolicVolume then
    ∫ z in h.choose, bianchiPairing F G z ∂hyperbolicVolume else 0

/-- **The Petersson product is computed on any fundamental domain.** -/
lemma bianchiPetersson_eq (hF : F ∈ bianchiSlashInvariants σ k (bianchiGammaZero 𝔑))
    (hG : G ∈ bianchiSlashInvariants σ k (bianchiGammaZero 𝔑)) {s : Set HyperbolicThreeSpace}
    (hs : IsFundamentalDomain (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) s hyperbolicVolume) :
    bianchiPetersson σ k 𝔑 F G = ∫ z in s, bianchiPairing F G z ∂hyperbolicVolume := by
  have h : ∃ s, IsFundamentalDomain (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) s hyperbolicVolume :=
    ⟨s, hs⟩
  have : Countable (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) := countable_bianchiPSLGroup
  rw [bianchiPetersson, dite_eq_left h]
  exact h.choose_spec.setIntegral_eq hs (bianchiPairing_smul_bianchiPSLGroup hF hG)

/-- **The Petersson product is Hermitian** on forms of level `Γ₀(𝔑)`. -/
lemma conj_bianchiPetersson (hK : finrank ℚ K = 2)
    (hF : F ∈ bianchiSlashInvariants σ k (bianchiGammaZero 𝔑))
    (hG : G ∈ bianchiSlashInvariants σ k (bianchiGammaZero 𝔑)) :
    conj (bianchiPetersson σ k 𝔑 F G) = bianchiPetersson σ k 𝔑 G F := by
  rcases exists_isFundamentalDomain_bianchiPSLGroup (σ := σ) 𝔑 hK with ⟨s, -, hs⟩
  rw [bianchiPetersson_eq hF hG hs, bianchiPetersson_eq hG hF hs, ← integral_conj]
  simp only [conj_bianchiPairing]

/-- **The Petersson product is homogeneous in the first variable** on `S_k(𝔑)`. -/
lemma bianchiPetersson_smul_left (hK : finrank ℚ K = 2) (a : ℂ)
    (hF : F ∈ bianchiSlashInvariants σ k (bianchiGammaZero 𝔑))
    (hG : G ∈ bianchiSlashInvariants σ k (bianchiGammaZero 𝔑)) :
    bianchiPetersson σ k 𝔑 (a • F) G = a * bianchiPetersson σ k 𝔑 F G := by
  rcases exists_isFundamentalDomain_bianchiPSLGroup (σ := σ) 𝔑 hK with ⟨s, -, hs⟩
  rw [bianchiPetersson_eq (Submodule.smul_mem _ a hF) hG hs, bianchiPetersson_eq hF hG hs]
  simp only [bianchiPairing_smul_left]
  exact integral_const_mul _ _

/-- **The Petersson product is nonnegative on the diagonal**: `⟨F, F⟩` is the integral of
`y^k ⟨F, F⟩_k ≥ 0`. -/
lemma bianchiPetersson_self_eq_ofReal (hK : finrank ℚ K = 2)
    (hF : F ∈ bianchiSlashInvariants σ k (bianchiGammaZero 𝔑)) :
    ∃ r : ℝ, 0 ≤ r ∧ bianchiPetersson σ k 𝔑 F F = r := by
  rcases exists_isFundamentalDomain_bianchiPSLGroup (σ := σ) 𝔑 hK with ⟨s, -, hs⟩
  refine ⟨∫ z in s, bianchiNormSq F z ∂hyperbolicVolume, integral_nonneg (bianchiNormSq_nonneg F),
    ?_⟩
  rw [bianchiPetersson_eq hF hF hs, ← integral_complex_ofReal]
  simp only [bianchiPairing_self]

variable [IsPrincipalIdealRing (𝓞 K)]

variable (σ) in
/-- **`ℋ₃` is covered by the translates under `Γ₀(𝔑)` of a set of finite volume.** -/
lemma exists_hyperbolicVolume_lt_top_forall_exists (hK : finrank ℚ K = 2) (h𝔑 : 𝔑 ≠ ⊥) :
    ∃ U : Set HyperbolicThreeSpace, hyperbolicVolume U < ⊤ ∧ ∀ z : HyperbolicThreeSpace,
      ∃ γ ∈ 𝔑.gamma0GL, ∃ w ∈ U, z = glToPSL σ γ • w := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  rcases exists_le_height_smul (σ := σ) hK with ⟨y₀, hy₀, hred⟩
  rcases exists_finite_gamma0GL_cosets h𝔑 with ⟨R, hR, hcos⟩
  let P : Set ℂ := ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)
  let T : Set HyperbolicThreeSpace := {z | z.coords.1 ∈ P ∧ y₀ ≤ z.coords.2}
  have hT : hyperbolicVolume T < ⊤ := hyperbolicVolume_siegelSet_lt_top
    (ZSpan.fundamentalDomain_isBounded _) (ZSpan.fundamentalDomain_measurableSet _) hy₀
  refine ⟨⋃ r ∈ R, glToPSL σ r • T, ?_, fun z ↦ ?_⟩
  · refine measure_biUnion_lt_top hR fun r _ ↦ ?_
    rw [measure_smul]
    exact hT
  · rcases hred z with ⟨γ, hγ⟩
    rcases ZSpan.exist_unique_vadd_mem_fundamentalDomain (integralLatticeBasis σ hK hx)
      (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ • z).coords.1 with ⟨v, hv, -⟩
    rcases mem_bianchiScaledLattice.mp (coe_mem_bianchiScaledLattice_one hK hx v) with ⟨a, ha⟩
    rw [one_mul] at ha
    have hrep (g : SL(2, 𝓞 K)) : QuotientGroup.mk (SpecialLinearGroup.map
        (σ.comp (algebraMap (𝓞 K) K)) g) = glToPSL σ (SpecialLinearGroup.toGL g) :=
      mk_eq_glToPSL _ ⟨1, by
        ext i j
        simp⟩
    let u : SL(2, 𝓞 K) := ⟨!![1, a; 0, 1], by simp⟩
    let M : SL(2, ℂ) := SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) u
    have hM₁₀ : M 1 0 = 0 := map_zero (σ.comp (algebraMap (𝓞 K) K))
    have hM₀₀ : M 0 0 = 1 := map_one (σ.comp (algebraMap (𝓞 K) K))
    have hM₀₁ : M 0 1 = σ a := rfl
    have hmem : M • (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ • z) ∈ T := by
      have hco : (M • (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ • z)).coords =
          ((SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ • z).coords.1 + σ a,
            (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ • z).coords.2) := by
        rw [coords_smul, moebius_eq_of_apply_one_zero hM₁₀, hM₀₀, hM₀₁]
        simp
      refine ⟨?_, ?_⟩
      · rw [hco]
        have e : (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ • z).coords.1 + σ a =
            v +ᵥ (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ • z).coords.1 := by
          rw [ha, add_comm]
          rfl
        simp only
        rw [e]
        exact hv
      · rw [hco]
        exact hγ
    rcases hcos (SpecialLinearGroup.toGL (u * γ)⁻¹) with ⟨r, hr, hδ⟩
    refine ⟨_, hδ, glToPSL σ r • (M • (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ • z)),
      mem_biUnion hr (smul_mem_smul_set hmem), ?_⟩
    rw [smul_smul, ← glToPSL_mul, inv_mul_cancel_right]
    have e : glToPSL σ (SpecialLinearGroup.toGL (u * γ)⁻¹) =
        (QuotientGroup.mk (M * SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ))⁻¹ := by
      rw [← hrep, map_inv, ← map_mul]
      rfl
    rw [e, ← mul_smul, ← mk_smul_eq, inv_smul_smul]

/-- **The fundamental domains of `Γ̄₀(𝔑)` have finite hyperbolic volume**, for `K` imaginary
quadratic of class number `1` and `𝔑 ≠ 0`: `ℋ₃` is covered by the translates of a set `U` of finite
volume, and `vol(s) ≤ ∑_γ vol(γ U ∩ s) = vol(U)`. -/
lemma hyperbolicVolume_lt_top (hK : finrank ℚ K = 2) (h𝔑 : 𝔑 ≠ ⊥) {s : Set HyperbolicThreeSpace}
    (hs : IsFundamentalDomain (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) s hyperbolicVolume) :
    hyperbolicVolume s < ⊤ := by
  have : Countable (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) := countable_bianchiPSLGroup
  rcases exists_hyperbolicVolume_lt_top_forall_exists σ hK h𝔑 with ⟨U, hU, hcov⟩
  refine lt_of_le_of_lt ?_ hU
  rw [hs.measure_eq_tsum U]
  refine (measure_mono fun z hz ↦ ?_).trans (measure_iUnion_le _)
  rcases hcov z with ⟨γ, hγ, w, hw, rfl⟩
  refine mem_iUnion.mpr ⟨⟨glToPSL σ γ, slRepresentative σ
    (GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ), ⟨_, (mem_bianchiGammaZero_iff _).mpr
      ⟨γ, hγ, rfl⟩, isSLRepresentative_slRepresentative _⟩, rfl⟩, ?_, hz⟩
  exact smul_mem_smul_set hw

/-- **The Petersson integrand of two bounded functions is integrable** on a set of finite volume. -/
lemma integrableOn_bianchiPairing_of_le {A B : HyperbolicThreeSpace → Fin (k + 1) → ℂ}
    (hA : Continuous A) (hB : Continuous B) {M M' : ℝ} (hM : ∀ z, bianchiNormSq A z ≤ M)
    (hM' : ∀ z, bianchiNormSq B z ≤ M') {s : Set HyperbolicThreeSpace}
    (hs : hyperbolicVolume s < ⊤) : IntegrableOn (bianchiPairing A B) s hyperbolicVolume :=
  Measure.integrableOn_of_bounded hs.ne (continuous_bianchiPairing hA hB).aestronglyMeasurable
    (M := (M + M') / 2) (.of_forall fun z ↦ (norm_bianchiPairing_le A B z).trans <| by
      linarith [hM z, hM' z])

/-- **The Petersson integrand of two cusp forms is integrable** on a fundamental domain of
`Γ̄₀(𝔑)`, for `K` imaginary quadratic of class number `1`, `𝔑 ≠ 0` and `k ≥ 1`. -/
lemma integrableOn_bianchiPairing (hK : finrank ℚ K = 2) (hk : k ≠ 0) (h𝔑 : 𝔑 ≠ ⊥)
    (hF : F ∈ bianchiCuspForms σ 𝔑.gamma0GL k) (hG : G ∈ bianchiCuspForms σ 𝔑.gamma0GL k)
    {s : Set HyperbolicThreeSpace}
    (hs : IsFundamentalDomain (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) s hyperbolicVolume) :
    IntegrableOn (bianchiPairing F G) s hyperbolicVolume := by
  rcases exists_bianchiNormSq_le hK hk h𝔑 hF with ⟨M, hM⟩
  rcases exists_bianchiNormSq_le hK hk h𝔑 hG with ⟨M', hM'⟩
  exact integrableOn_bianchiPairing_of_le (continuous_of_analyticAt hF.1.analyticAt)
    (continuous_of_analyticAt hG.1.analyticAt) hM hM' (hyperbolicVolume_lt_top hK h𝔑 hs)

/-- **The Petersson product is additive in the first variable** on `S_k(𝔑)`. -/
lemma bianchiPetersson_add_left (hK : finrank ℚ K = 2) (hk : k ≠ 0) (h𝔑 : 𝔑 ≠ ⊥)
    (hF : F ∈ bianchiCuspForms σ 𝔑.gamma0GL k) (hF' : F' ∈ bianchiCuspForms σ 𝔑.gamma0GL k)
    (hG : G ∈ bianchiCuspForms σ 𝔑.gamma0GL k) : bianchiPetersson σ k 𝔑 (F + F') G =
      bianchiPetersson σ k 𝔑 F G + bianchiPetersson σ k 𝔑 F' G := by
  rcases exists_isFundamentalDomain_bianchiPSLGroup (σ := σ) 𝔑 hK with ⟨s, -, hs⟩
  have hinv {H : HyperbolicThreeSpace → Fin (k + 1) → ℂ}
      (hH : H ∈ bianchiCuspForms σ 𝔑.gamma0GL k) :
      H ∈ bianchiSlashInvariants σ k (bianchiGammaZero 𝔑) :=
    (isBianchiSlashInvariant_iff_mem 𝔑).mp hH.1.invariant
  rw [bianchiPetersson_eq (hinv (add_mem hF hF')) (hinv hG) hs, bianchiPetersson_eq (hinv hF)
    (hinv hG) hs, bianchiPetersson_eq (hinv hF') (hinv hG) hs]
  simp only [bianchiPairing_add_left]
  exact integral_add (integrableOn_bianchiPairing hK hk h𝔑 hF hG hs)
    (integrableOn_bianchiPairing hK hk h𝔑 hF' hG hs)

/-- **The Petersson product is definite** on `S_k(𝔑)`: `⟨F, F⟩ = 0` only for `F = 0`. -/
lemma bianchiPetersson_self_eq_zero_iff (hK : finrank ℚ K = 2) (hk : k ≠ 0) (h𝔑 : 𝔑 ≠ ⊥)
    (hF : F ∈ bianchiCuspForms σ 𝔑.gamma0GL k) : bianchiPetersson σ k 𝔑 F F = 0 ↔ F = 0 := by
  rcases exists_isFundamentalDomain_bianchiPSLGroup (σ := σ) 𝔑 hK with ⟨s, -, hs⟩
  have hinv : F ∈ bianchiSlashInvariants σ k (bianchiGammaZero 𝔑) :=
    (isBianchiSlashInvariant_iff_mem 𝔑).mp hF.1.invariant
  rw [bianchiPetersson_eq hinv hinv hs]
  refine ⟨fun h₀ ↦ eq_zero_of_setIntegral_eq_zero hF.1 hs
    (integrableOn_bianchiPairing hK hk h𝔑 hF hF hs) h₀, ?_⟩
  rintro rfl
  simp [bianchiPairing, symPowInner]

/-- **The oldforms are cusp forms** of level `Γ₀(𝔑)`, for `K` imaginary quadratic of class number
`1`. -/
lemma bianchiOldforms_le_bianchiCuspForms (hK : finrank ℚ K = 2) (h𝔑 : 𝔑 ≠ ⊥) :
    bianchiOldforms σ k 𝔑 ≤ bianchiCuspForms σ 𝔑.gamma0GL k := by
  rcases exists_span_eq h𝔑 with ⟨N, rfl⟩
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨𝔐, h𝔐, δ, hδ, hle, G, hG, rfl⟩
  rcases Nat.even_or_odd k with hk | hk
  · have h𝔐₀ : 𝔐 ≠ ⊥ := fun h ↦ (bot_le.trans_lt (h ▸ h𝔐)).ne' rfl |>.elim
    rcases exists_span_eq h𝔐₀ with ⟨M, rfl⟩
    have hδ₀ : δ ∈ (𝓞 K)⁰ := mem_nonZeroDivisors_of_ne_zero hδ
    have h₁ : bianchiLevelRaise σ k ⟨δ, hδ₀⟩ G ∈
      bianchiCuspForms σ (Ideal.span {((⟨δ, hδ₀⟩ * M : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL k :=
    bianchiLevelRaise_mem_bianchiCuspForms hK hk hG
    rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_le_span_singleton] at hle
    have h₂ :
        bianchiLevelRaise σ k ⟨δ, hδ₀⟩ G ∈ bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k :=
      bianchiCuspForms_mono (N := N) hK hle h₁
    rwa [rowScale_eq_heckeLower]
  · rw [hG.1.invariant.eq_zero_of_odd hk, bianchiSlash_zero]
    exact zero_mem _

/-- **The newspace is the orthogonal complement of the oldforms** (LMFDB `mf.bianchi.spaces`) in
`S_k(𝔑)` for the Petersson product, for `K` imaginary quadratic of class number `1`, `𝔑 ≠ 0` and
`k ≥ 1`. -/
lemma mem_bianchiNewSubspace_iff (hK : finrank ℚ K = 2) (hk : k ≠ 0) (h𝔑 : 𝔑 ≠ ⊥) : F ∈
    bianchiNewSubspace σ k 𝔑 ↔ F ∈ bianchiCuspForms σ 𝔑.gamma0GL k ∧
      ∀ G ∈ bianchiOldforms σ k 𝔑, bianchiPetersson σ k 𝔑 F G = 0 := by
  have hinv {H : HyperbolicThreeSpace → Fin (k + 1) → ℂ}
      (hH : H ∈ bianchiCuspForms σ 𝔑.gamma0GL k) :
      H ∈ bianchiSlashInvariants σ k (bianchiGammaZero 𝔑) :=
    (isBianchiSlashInvariant_iff_mem 𝔑).mp hH.1.invariant
  refine ⟨fun h ↦ ⟨h.1, fun G hG ↦ ?_⟩, fun h ↦ ⟨h.1, fun G hG s hs ↦ ?_⟩⟩
  · rcases exists_isFundamentalDomain_bianchiPSLGroup (σ := σ) 𝔑 hK with ⟨s, -, hs⟩
    rw [bianchiPetersson_eq (hinv h.1) (hinv (bianchiOldforms_le_bianchiCuspForms hK h𝔑 hG)) hs]
    exact (h.2 G hG s hs).2
  · have hG' : G ∈ bianchiCuspForms σ 𝔑.gamma0GL k := bianchiOldforms_le_bianchiCuspForms hK h𝔑 hG
    refine ⟨integrableOn_bianchiPairing hK hk h𝔑 h.1 hG' hs, ?_⟩
    have h₁ : bianchiPetersson σ k 𝔑 F G = 0 := h.2 G hG
    rwa [bianchiPetersson_eq (hinv h.1) (hinv hG') hs] at h₁

end HyperbolicThreeSpace
