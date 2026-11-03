import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.CuspFunction
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.HyperbolicVolume
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.PeterssonPairing
import TauCeti.Algebra.Group.Units.Countable
import TauCeti.Data.Matrix.Countable
import TauCeti.MeasureTheory.Group.ProperlyDiscontinuous

/-!
# Fundamental domains of `Γ₀(𝔑)` and the orthogonality of old and new forms

Let `K` be an imaginary quadratic field, embedded in `ℂ` by `σ`, and `𝔑` an ideal of `𝒪_K`. The
image `Γ̄₀(𝔑)` of the level `Γ₀(𝔑)` in `PSL(2, ℂ)` (`bianchiPSLGroup`) is countable, and it acts
properly discontinuously on `ℋ₃` (`properlyDiscontinuousSMul_bianchiPSLGroup`): if `g ∈ SL(2, ℂ)`
moves a point of a compact set `A` to a point of a compact set `B`, then the entries of `g` are
bounded in terms of `A` and `B` (`norm_apply_le_of_moebius`), while a representative of a matrix of
`GL₂(𝒪_K)` is that matrix up to a scalar of absolute value `1`, the units of `𝒪_K` having absolute
value `1`, and there are finitely many integers of `K` of bounded absolute value
(`finite_setOf_norm_apply_le`). A point of `ℋ₃` fixed by `g ≠ ±1` lies on a hemisphere or a line,
so that the fixed points of the elements of `Γ̄₀(𝔑)` form a set of hyperbolic volume `0`
(`hyperbolicVolume_setOf_smul_eq_self`). Hence `Γ̄₀(𝔑)` has a measurable fundamental domain
(`exists_isFundamentalDomain_bianchiPSLGroup`), and the orthogonality relation of
`IsBianchiPeterssonOrthogonal`, which runs over the fundamental domains of `Γ̄₀(𝔑)`, is not vacuous.

As the pairing `y^k ⟨F(z), G(z)⟩_k` is invariant (`bianchiPairing_bianchiSlash`), positive definite,
and the volume is invariant, a function of the old space which is orthogonal to the old space is
`0`: **the new space and the old space meet in `0`**
(`eq_zero_of_mem_bianchiOldforms_of_mem_bianchiNewSubspace`).

## Main results

* `HyperbolicThreeSpace.norm_apply_le_of_moebius`: the bound of the entries of a matrix moving a
  point of a compact set to a compact set.
* `HyperbolicThreeSpace.hyperbolicVolume_setOf_smul_eq_self`: the fixed points of `g ≠ ±1` form a
  null set.
* `HyperbolicThreeSpace.finite_setOf_norm_apply_le`: there are finitely many integers of bounded
  absolute value.
* `HyperbolicThreeSpace.norm_unit_eq_one`: the units have absolute value `1`.
* `HyperbolicThreeSpace.one_le_norm_apply`: a nonzero integer has absolute value at least `1`.
* `HyperbolicThreeSpace.properlyDiscontinuousSMul_bianchiPSLGroup`: `Γ̄₀(𝔑)` acts properly
  discontinuously on `ℋ₃`.
* `HyperbolicThreeSpace.exists_isFundamentalDomain_bianchiPSLGroup`: `Γ̄₀(𝔑)` has a measurable
  fundamental domain.
* `HyperbolicThreeSpace.eq_zero_of_mem_bianchiOldforms_of_mem_bianchiNewSubspace`: the new space and
  the old space meet in `0`.
-/

open Complex Matrix MeasureTheory Module NumberField Set HilbertModularGroup TauCeti

open scoped ComplexConjugate MatrixGroups Pointwise

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] {σ : K →+* ℂ} (g : SL(2, ℂ)) {p : ℂ × ℝ} {R : ℝ}

private lemma moebiusDenom_le (hR : 0 < R) (hp : 0 < p.2) (h₁ : p.2 ≤ R)
    (h₂ : R⁻¹ ≤ (moebius g p).2) : moebiusDenom g p ≤ R ^ 2 := by
  have hN : 0 < moebiusDenom g p := moebiusDenom_pos g hp
  have h₃ : (moebius g p).2 = p.2 / moebiusDenom g p :=
    rfl
  rw [h₃, inv_le_comm₀ hR (div_pos hp hN), inv_div, div_le_iff₀ hp] at h₂
  nlinarith

private lemma norm_add_le_of_moebius (hR : 0 < R) (hp : 0 < p.2) (h₁ : p.2 ≤ R)
    (h₂ : R⁻¹ ≤ (moebius g p).2) : ‖g 1 0 * p.1 + g 1 1‖ ≤ R := by
  have h₃ : ‖g 1 0 * p.1 + g 1 1‖ ^ 2 ≤ R ^ 2 := by
    have h₄ : moebiusDenom g p ≤ R ^ 2 := moebiusDenom_le g hR hp h₁ h₂
    rw [moebiusDenom, normSq_eq_norm_sq] at h₄
    have h₅ : 0 ≤ normSq (g 1 0) * p.2 ^ 2 := by
      positivity [normSq_nonneg (g 1 0)]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR.le two_ne_zero).mp h₃

private lemma norm_apply_one_zero_le (hR : 0 < R) (hp : 0 < p.2) (h₀ : R⁻¹ ≤ p.2) (h₁ : p.2 ≤ R)
    (h₂ : R⁻¹ ≤ (moebius g p).2) : ‖g 1 0‖ ≤ R ^ 2 := by
  have h₃ : (‖g 1 0‖ * p.2) ^ 2 ≤ R ^ 2 := by
    have h₄ : moebiusDenom g p ≤ R ^ 2 := moebiusDenom_le g hR hp h₁ h₂
    rw [moebiusDenom, normSq_eq_norm_sq, normSq_eq_norm_sq] at h₄
    nlinarith [sq_nonneg ‖g 1 0 * p.1 + g 1 1‖]
  have h₄ : ‖g 1 0‖ * p.2 ≤ R := (pow_le_pow_iff_left₀ (by positivity) hR.le two_ne_zero).mp h₃
  have h₅ : ‖g 1 0‖ * R⁻¹ ≤ ‖g 1 0‖ * p.2 := mul_le_mul_of_nonneg_left h₀ (norm_nonneg _)
  have h₆ : ‖g 1 0‖ * R⁻¹ ≤ R := h₅.trans h₄
  rwa [← div_eq_mul_inv, div_le_iff₀ hR, ← sq] at h₆

private lemma norm_apply_one_one_le (hR : 0 < R) (hp : 0 < p.2) (hx : ‖p.1‖ ≤ R) (h₀ : R⁻¹ ≤ p.2)
    (h₁ : p.2 ≤ R) (h₂ : R⁻¹ ≤ (moebius g p).2) : ‖g 1 1‖ ≤ R + R ^ 3 := by
  have h₃ : g 1 1 = (g 1 0 * p.1 + g 1 1) - g 1 0 * p.1 := by
    ring1
  rw [h₃]
  refine (norm_sub_le _ _).trans (add_le_add (norm_add_le_of_moebius g hR hp h₁ h₂) ?_)
  rw [norm_mul, pow_succ]
  exact mul_le_mul (norm_apply_one_zero_le g hR hp h₀ h₁ h₂) hx (norm_nonneg _) (by positivity)

/-- **The bound of the entries of a matrix moving a point of a compact set to a compact set**: if
`p = (x, y)` and `g p = (x', y')` satisfy `|x|, |x'| ≤ R` and `R⁻¹ ≤ y, y' ≤ R`, with `R ≥ 1`, then
the entries of `g ∈ SL(2, ℂ)` have absolute value at most `4 R⁴`. The lower row is bounded by
`y' = y / (|cx + d|² + |c|²y²)`, the upper row by the same applied to `g⁻¹` and by the relation
`ax + b = x'(cx + d) - y' c̄ y`. -/
lemma norm_apply_le_of_moebius (hR : 1 ≤ R) (hp : 0 < p.2) (hx : ‖p.1‖ ≤ R) (h₀ : R⁻¹ ≤ p.2)
    (h₁ : p.2 ≤ R) (hx' : ‖(moebius g p).1‖ ≤ R) (h₀' : R⁻¹ ≤ (moebius g p).2)
    (h₁' : (moebius g p).2 ≤ R) (i j : Fin 2) : ‖g i j‖ ≤ 4 * R ^ 4 := by
  have hR₀ : 0 < R := zero_lt_one.trans_le hR
  have hp' : 0 < (moebius g p).2 := moebius_snd_pos g hp
  have hinv : moebius g⁻¹ (moebius g p) = p := moebius_inv_moebius g hp
  have hc : ‖g 1 0‖ ≤ R ^ 2 := norm_apply_one_zero_le g hR₀ hp h₀ h₁ h₀'
  have hd : ‖g 1 1‖ ≤ R + R ^ 3 := norm_apply_one_one_le g hR₀ hp hx h₀ h₁ h₀'
  have ha : ‖g 0 0‖ ≤ R + R ^ 3 := by
    have h₂ : ‖((g⁻¹ : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ≤ R + R ^ 3 :=
    norm_apply_one_one_le g⁻¹ hR₀ hp' hx' h₀' h₁' (by rwa [hinv])
    rwa [SpecialLinearGroup.SL2_inv_expl] at h₂
  have hcx : ‖g 1 0 * p.1 + g 1 1‖ ≤ R := norm_add_le_of_moebius g hR₀ hp h₁ h₀'
  have hb : g 0 1 = (moebius g p).1 * (g 1 0 * p.1 + g 1 1) - (moebius g p).2 * conj (g 1 0) * p.2 -
      g 0 0 * p.1 := by
    have h₂ : (quatMatrix 1 0 (moebius g p) * automorphyFactor g p) 0 0 =
      quatMatrix (g 0 0) (g 0 1) p 0 0 :=
    congrFun (congrFun (quatMatrix_one_zero_moebius_mul g hp) 0) 0
    simp [quatMatrix, automorphyFactor_eq_quatMatrix] at h₂
    linear_combination -h₂
  have hR₂ : R ≤ R ^ 2 := by nlinarith
  have hR₃ : R ^ 2 ≤ R ^ 3 := by nlinarith [pow_pos hR₀ 2]
  have hR₄ : R ^ 3 ≤ R ^ 4 := by nlinarith [pow_pos hR₀ 3]
  have hR₅ : 0 ≤ R ^ 4 := by positivity
  have hb' : ‖g 0 1‖ ≤ 4 * R ^ 4 := by
    rw [hb]
    have h₂ : ‖(moebius g p).2 * conj (g 1 0) * p.2‖ ≤ R * R ^ 2 * R := by
      rw [norm_mul, norm_mul, norm_conj, norm_real, norm_real, Real.norm_of_nonneg hp'.le,
        Real.norm_of_nonneg hp.le]
      gcongr
    have h₃ : ‖(moebius g p).1 * (g 1 0 * p.1 + g 1 1)‖ ≤ R * R := by
      rw [norm_mul]
      gcongr
    have h₄ : ‖g 0 0 * p.1‖ ≤ (R + R ^ 3) * R := by
      rw [norm_mul]
      gcongr
    refine (norm_sub_le _ _).trans
      ((add_le_add ((norm_sub_le _ _).trans (add_le_add h₃ h₂)) h₄).trans
      ?_)
    nlinarith
  fin_cases i <;> fin_cases j
  · exact ha.trans (by nlinarith)
  · exact hb'
  · exact hc.trans (by nlinarith)
  · exact hd.trans (by nlinarith)

/-- **The fixed points of `g ≠ ±1` form a null set**: for `g = (a, b; c, d) ∈ SL(2, ℂ)`, a fixed
point `(x, y)` of `g` satisfies `|cx + d|² + |c|²y² = 1` when `c ≠ 0`, the equation of a graph over
`x`, and `a²x + ab = x` when `c = 0`, where `a² ≠ 1` unless `g = ±1`. -/
lemma hyperbolicVolume_setOf_smul_eq_self (h₁ : g ≠ 1) (h₂ : g ≠ -1) :
    hyperbolicVolume {z | g • z = z} = 0 := by
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [measurableEmbedding_coords.comap_apply]
  have hfix {z : HyperbolicThreeSpace} (hz : g • z = z) : moebius g z.coords = z.coords := by
    rw [← coords_smul, hz]
  by_cases hc : g 1 0 = 0
  · have hdet : g 0 0 * g 1 1 = 1 := mul_apply_one_one_eq_one_of_apply_one_zero hc
    have ha : g 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have hd : g 1 1 = (g 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
    have hfix' {z : HyperbolicThreeSpace} (hz : g • z = z) :
        g 0 0 ^ 2 * z.coords.1 + g 0 0 * g 0 1 = z.coords.1 := by
      have h₃ : moebius g z.coords = z.coords := hfix hz
      rw [moebius_eq_of_apply_one_zero hc] at h₃
      exact congrArg Prod.fst h₃
    by_cases ha2 : g 0 0 ^ 2 = 1
    · have hempty : {z : HyperbolicThreeSpace | g • z = z} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun z hz ↦ ?_
        have h₃ : g 0 0 ^ 2 * z.coords.1 + g 0 0 * g 0 1 = z.coords.1 := hfix' hz
        rw [ha2, one_mul, add_eq_left, mul_eq_zero, or_iff_right ha] at h₃
        rcases mul_self_eq_one_iff.mp (by rwa [← sq] : g 0 0 * g 0 0 = 1) with h₄ | h₄
        · refine h₁ (Subtype.ext ?_)
          ext i j
          fin_cases i <;> fin_cases j <;> simp [h₄, h₃, hc, hd]
        · refine h₂ (Subtype.ext ?_)
          ext i j
          fin_cases i <;> fin_cases j <;> simp [h₄, h₃, hc, hd]
      rw [hempty, image_empty, measure_empty]
    · have hsub : coords '' {z : HyperbolicThreeSpace | g • z = z} ⊆
          {g 0 0 * g 0 1 / (1 - g 0 0 ^ 2)} ×ˢ univ := by
        rintro _ ⟨z, hz, rfl⟩
        refine ⟨?_, mem_univ _⟩
        have h₃ : g 0 0 ^ 2 * z.coords.1 + g 0 0 * g 0 1 = z.coords.1 := hfix' hz
        have h₄ : 1 - g 0 0 ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha2)
        refine mem_singleton_iff.mpr ?_
        rw [eq_div_iff h₄]
        linear_combination -h₃
      refine measure_mono_null hsub ?_
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp
  · have hN {z : HyperbolicThreeSpace} (hz : g • z = z) : moebiusDenom g z.coords = 1 := by
      have h₃ : z.coords.2 / moebiusDenom g z.coords = z.coords.2 := congrArg Prod.snd (hfix hz)
      rwa [div_eq_iff (moebiusDenom_pos g (coords_snd_pos z)).ne', left_eq_mul₀
        (coords_snd_pos z).ne'] at h₃
    have hc' : normSq (g 1 0) ≠ 0 := normSq_eq_zero.not.mpr hc
    let s : Set (ℂ × ℝ) := {q | 0 < q.2} ∩ {q | moebiusDenom g q = 1}
    have hs : MeasurableSet s := by
      refine (measurableSet_lt measurable_const measurable_snd).inter (measurableSet_eq_fun ?_
        measurable_const)
      unfold moebiusDenom
      fun_prop
    have hsub : coords '' {z : HyperbolicThreeSpace | g • z = z} ⊆ s := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨coords_snd_pos z, hN hz⟩
    refine measure_mono_null hsub ?_
    rw [Measure.volume_eq_prod, Measure.measure_prod_null hs]
    refine .of_forall fun x ↦ Subsingleton.measure_zero ?_ _
    rintro y₁ ⟨hy₁, hN₁⟩ y₂ ⟨hy₂, hN₂⟩
    have hN₁' : normSq (g 1 0 * x + g 1 1) + normSq (g 1 0) * y₁ ^ 2 = 1 := hN₁
    have hN₂' : normSq (g 1 0 * x + g 1 1) + normSq (g 1 0) * y₂ ^ 2 = 1 := hN₂
    have h₃ : y₁ ^ 2 = y₂ ^ 2 := mul_left_cancel₀ hc' (by linarith)
    exact (sq_eq_sq₀ (le_of_lt hy₁) (le_of_lt hy₂)).mp h₃

noncomputable instance : ContinuousConstSMul PSL(2, ℂ) HyperbolicThreeSpace where
  continuous_const_smul γ := Quotient.inductionOn' γ fun g ↦ continuous_const_smul g

noncomputable instance : SMulInvariantMeasure PSL(2, ℂ) HyperbolicThreeSpace hyperbolicVolume where
  measure_preimage_smul γ _ hA := Quotient.inductionOn' γ fun g ↦
    SMulInvariantMeasure.measure_preimage_smul g hA

variable {𝔑 : Ideal (𝓞 K)} {γ : GL (Fin 2) (𝓞 K)}

variable (σ γ) in
/-- The class in `PSL(2, ℂ)` of a matrix of `GL₂(𝒪_K)`. -/
noncomputable def glToPSL : PSL(2, ℂ) :=
  QuotientGroup.mk (slRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ))

lemma mk_eq_glToPSL (hg : IsSLRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ) g) :
    (QuotientGroup.mk g : PSL(2, ℂ)) = glToPSL σ γ := by
  refine QuotientGroup.eq.mpr ?_
  rcases hg.eq_or_eq_neg (isSLRepresentative_slRepresentative _) with h | h
  · rw [h, inv_mul_cancel]
    exact one_mem _
  · rw [h, mul_neg, inv_mul_cancel]
    exact SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl)

variable (σ γ) in
lemma glToPSL_smul (z : HyperbolicThreeSpace) :
    glToPSL σ γ • z = slRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ) • z :=
  rfl

variable (σ γ) in
lemma glToPSL_mul (δ : GL (Fin 2) (𝓞 K)) : glToPSL σ (γ * δ) = glToPSL σ γ * glToPSL σ δ := by
  rw [← mk_eq_glToPSL (g := slRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ) *
    slRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ))]
  · rfl
  · rw [map_mul]
    exact (isSLRepresentative_slRepresentative _).mul (isSLRepresentative_slRepresentative _)

variable (σ) in
lemma glToPSL_one : glToPSL σ (1 : GL (Fin 2) (𝓞 K)) = 1 := by
  rw [← mk_eq_glToPSL (g := 1)]
  · rfl
  · exact ⟨1, by simp⟩

variable (σ γ) in
lemma glToPSL_inv : glToPSL σ γ⁻¹ = (glToPSL σ γ)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by
    rw [← glToPSL_mul, inv_mul_cancel, glToPSL_one]

variable [IsTotallyComplex K]

lemma exists_mem_gamma0GL_of_mem_bianchiPSLGroup {γ' : PSL(2, ℂ)}
    (hγ' : γ' ∈ bianchiPSLGroup σ (bianchiGammaZero 𝔑)) : ∃ γ ∈ 𝔑.gamma0GL, ∃ g : SL(2, ℂ),
      IsSLRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ) g ∧
        (QuotientGroup.mk g : PSL(2, ℂ)) = γ' := by
  rcases hγ' with ⟨g, ⟨x, hx, hg⟩, rfl⟩
  rcases (mem_bianchiGammaZero_iff x).mp hx with ⟨γ, hγ, rfl⟩
  exact ⟨γ, hγ, g, hg, rfl⟩

variable [NumberField K]

/-- **There are finitely many integers of bounded absolute value** in an imaginary quadratic
field. -/
lemma finite_setOf_norm_apply_le (hK : finrank ℚ K = 2) (C : ℝ) : {a : 𝓞 K | ‖σ a‖ ≤ C}.Finite := by
  have : Subsingleton (InfinitePlace K) := subsingleton_infinitePlace hK
  refine Finite.of_finite_image (f := fun a : 𝓞 K ↦ (a : K)) ?_
    RingOfIntegers.coe_injective.injOn
  refine (Embeddings.finite_of_norm_le K ℂ C).subset ?_
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨a.isIntegral_coe, fun φ ↦ ?_⟩
  have h₁ : InfinitePlace.mk φ = InfinitePlace.mk σ := Subsingleton.elim _ _
  have h₂ : ‖φ a‖ = ‖σ a‖ := by
    rw [← InfinitePlace.apply, h₁, InfinitePlace.apply]
  rw [h₂]
  exact ha

/-- **The units of `𝒪_K` have absolute value `1`**, for an imaginary quadratic field `K`. -/
lemma norm_unit_eq_one (hK : finrank ℚ K = 2) (u : (𝓞 K)ˣ) : ‖σ (u : 𝓞 K)‖ = 1 := by
  have h₁ : |Algebra.norm ℚ ((u : 𝓞 K) : K)| = 1 :=
    isUnit_iff_norm.mp u.isUnit
  have h₂ : ‖σ ((u : 𝓞 K) : K)‖ ^ 2 = ((|Algebra.norm ℚ ((u : 𝓞 K) : K)| : ℚ) : ℝ) :=
    norm_sq_apply_eq_abs_norm _ hK
  rw [h₁, Rat.cast_one] at h₂
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h₂

/-- **A nonzero integer has absolute value at least `1`**, for an imaginary quadratic field `K`. -/
lemma one_le_norm_apply (hK : finrank ℚ K = 2) {a : 𝓞 K} (ha : a ≠ 0) : 1 ≤ ‖σ a‖ := by
  have h₂ : ‖σ (a : K)‖ ^ 2 = ((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) :=
    norm_sq_apply_eq_abs_norm _ hK
  have h₁ : (1 : ℝ) ≤ ((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) := by
    rw [← Algebra.coe_norm_int a]
    have hn : Algebra.norm ℤ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
    have hn' : (1 : ℤ) ≤ |Algebra.norm ℤ a| := Int.one_le_abs hn
    exact_mod_cast hn'
  rw [← h₂] at h₁
  exact (one_le_pow_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h₁

lemma finite_units (τ : K →+* ℂ) (hK : finrank ℚ K = 2) : Finite (𝓞 K)ˣ :=
  have : Finite {a : 𝓞 K | ‖τ (a : K)‖ ≤ 1} := (finite_setOf_norm_apply_le hK 1).to_subtype
  Finite.of_injective (fun u : (𝓞 K)ˣ ↦ (⟨u, (norm_unit_eq_one hK u).le⟩ :
    {a : 𝓞 K | ‖τ (a : K)‖ ≤ 1})) fun _ _ h ↦ Units.ext (congrArg Subtype.val h)

lemma countable_bianchiPSLGroup : Countable (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) := by
  refine ((countable_range (glToPSL σ)).mono ?_).to_subtype
  intro γ' hγ'
  rcases exists_mem_gamma0GL_of_mem_bianchiPSLGroup hγ' with ⟨γ, -, g, hg, rfl⟩
  exact ⟨γ, (mk_eq_glToPSL g hg).symm⟩

lemma norm_apply_eq_of_isSLRepresentative (hK : finrank ℚ K = 2)
    (hg : IsSLRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ) g) (i j : Fin 2) :
    ‖σ ((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) i j : K)‖ = ‖g i j‖ := by
  rcases hg with ⟨s, hs⟩
  have hs₀ : s ≠ 0 := ne_zero_of_coe_eq_inv_smul hs
  have h₁ : (g : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := g.det_coe
  rw [hs, det_smul, Fintype.card_fin, inv_pow, inv_mul_eq_div,
    div_eq_one_iff_eq (pow_ne_zero 2 hs₀)] at h₁
  have h₂ : ((GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).map σ = (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map
        (σ.comp (algebraMap (𝓞 K) K)) := by
    ext i j
    rfl
  have h₃ : ‖s‖ ^ 2 = 1 := by
    rw [← norm_pow, ← h₁, h₂]
    have h₄ : ((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map (σ.comp (algebraMap (𝓞 K) K))).det =
        σ ((GeneralLinearGroup.det γ : (𝓞 K)ˣ) : 𝓞 K) := by
      rw [GeneralLinearGroup.val_det_apply]
      exact (RingHom.map_det (σ.comp (algebraMap (𝓞 K) K)) _).symm
    rw [h₄]
    exact norm_unit_eq_one hK _
  have h₅ : ‖s‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h₃
  rw [hs, h₂]
  simp [h₅]

variable (𝔑) in
/-- **`Γ̄₀(𝔑)` acts properly discontinuously on `ℋ₃`**, for an imaginary quadratic field `K`: the
matrices of `Γ₀(𝔑)` moving a point of a compact set to a point of a compact set have bounded entries
(`norm_apply_le_of_moebius`), so they are finitely many (`finite_setOf_norm_apply_le`). -/
lemma properlyDiscontinuousSMul_bianchiPSLGroup (hK : finrank ℚ K = 2) :
    ProperlyDiscontinuousSMul (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) HyperbolicThreeSpace where
  finite_disjoint_inter_image := by
    intro A B hA hB
    let f : HyperbolicThreeSpace → ℝ :=
      fun z ↦ max ‖z.coords.1‖ (max z.coords.2 z.coords.2⁻¹)
    have hco : Continuous (coords : HyperbolicThreeSpace → ℂ × ℝ) :=
      isOpenEmbedding_coords.continuous
    have hf : Continuous f := by
      refine (hco.fst.norm).max (hco.snd.max (hco.snd.inv₀ fun z ↦ (coords_snd_pos z).ne'))
    rcases (hA.union hB).exists_bound_of_continuousOn hf.continuousOn with ⟨C, hC⟩
    let R : ℝ := max C 1
    have hR : 1 ≤ R := le_max_right _ _
    have hR₀ : 0 < R := zero_lt_one.trans_le hR
    have hb {z : HyperbolicThreeSpace} (hz : z ∈ A ∪ B) : f z ≤ R :=
      (le_abs_self _).trans ((hC z hz).trans (le_max_left _ _))
    have hx {z : HyperbolicThreeSpace} (hz : z ∈ A ∪ B) : ‖z.coords.1‖ ≤ R :=
      (le_max_left _ _).trans (hb hz)
    have hy {z : HyperbolicThreeSpace} (hz : z ∈ A ∪ B) : z.coords.2 ≤ R :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans (hb hz)
    have hy' {z : HyperbolicThreeSpace} (hz : z ∈ A ∪ B) : R⁻¹ ≤ z.coords.2 := by
      have h₁ : z.coords.2⁻¹ ≤ R := ((le_max_right _ _).trans (le_max_right _ _)).trans (hb hz)
      exact (inv_le_comm₀ (coords_snd_pos z) hR₀).mp h₁
    have hT : {γ : GL (Fin 2) (𝓞 K) | ∀ i j, ‖σ ((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) i j : K)‖ ≤
        4 * R ^ 4}.Finite := by
      refine Finite.of_finite_image (f := fun γ : GL (Fin 2) (𝓞 K) ↦
        ((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) : Fin 2 → Fin 2 → 𝓞 K)) ?_
          (Units.val_injective.injOn)
      refine ((Finite.pi fun _ : Fin 2 ↦ Finite.pi fun _ : Fin 2 ↦
        finite_setOf_norm_apply_le (σ := σ) hK (4 * R ^ 4))).subset ?_
      rintro _ ⟨γ, hγ, rfl⟩ i - j -
      exact hγ i j
    refine Finite.of_finite_image (f := Subtype.val) ((hT.image (glToPSL σ)).subset ?_)
      Subtype.val_injective.injOn
    rintro _ ⟨⟨γ', hγ'⟩, ⟨_, ⟨z, hz, rfl⟩, hz'⟩, rfl⟩
    rcases exists_mem_gamma0GL_of_mem_bianchiPSLGroup hγ' with ⟨γ, -, g, hg, rfl⟩
    refine ⟨γ, fun i j ↦ ?_, (mk_eq_glToPSL g hg).symm⟩
    have hzA : z ∈ A ∪ B := Or.inl hz
    have hzB : g • z ∈ A ∪ B := Or.inr hz'
    rw [norm_apply_eq_of_isSLRepresentative g hK hg]
    exact norm_apply_le_of_moebius g hR (coords_snd_pos z) (hx hzA) (hy' hzA) (hy hzA)
      (hx hzB) (hy' hzB) (hy hzB) i j

variable (𝔑) in
/-- **`Γ̄₀(𝔑)` has a measurable fundamental domain**: for an imaginary quadratic field `K`, the
image `Γ̄₀(𝔑)` of `Γ₀(𝔑)` in `PSL(2, ℂ)` acts properly discontinuously on `ℋ₃`, and the points with
nontrivial stabiliser form a null set. So the orthogonality of `IsBianchiPeterssonOrthogonal` is not
vacuous. -/
lemma exists_isFundamentalDomain_bianchiPSLGroup (hK : finrank ℚ K = 2) :
    ∃ s : Set HyperbolicThreeSpace, MeasurableSet s ∧
      IsFundamentalDomain (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) s hyperbolicVolume := by
  have : ProperlyDiscontinuousSMul (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) HyperbolicThreeSpace :=
    properlyDiscontinuousSMul_bianchiPSLGroup 𝔑 hK
  have : Countable (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) := countable_bianchiPSLGroup
  have hnull : hyperbolicVolume (freeLocus (bianchiPSLGroup σ (bianchiGammaZero 𝔑))
      HyperbolicThreeSpace : Set HyperbolicThreeSpace)ᶜ = 0 := by
    have hsub : (freeLocus (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) HyperbolicThreeSpace :
        Set HyperbolicThreeSpace)ᶜ ⊆ ⋃ γ : {γ : bianchiPSLGroup σ (bianchiGammaZero 𝔑) // γ ≠ 1},
          {z | γ.1 • z = z} := by
      intro z hz
      have hz' : MulAction.stabilizer (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) z ≠ ⊥ := hz
      rcases Subgroup.ne_bot_iff_exists_ne_one.mp hz' with ⟨⟨γ, hγ⟩, hγ₁⟩
      exact mem_iUnion.mpr ⟨⟨γ, fun h ↦ hγ₁ (Subtype.ext h)⟩, hγ⟩
    refine measure_mono_null hsub (measure_iUnion_null fun γ ↦ ?_)
    rcases γ with ⟨⟨γ', hγ'⟩, hγ₁⟩
    rcases exists_mem_gamma0GL_of_mem_bianchiPSLGroup hγ' with ⟨γ, -, g, -, rfl⟩
    have hne₁ : g ≠ 1 := fun h ↦ hγ₁ <| Subtype.ext <| by
      have e : (QuotientGroup.mk g : PSL(2, ℂ)) = 1 := by
        rw [h]
        rfl
      exact e
    have hne₂ : g ≠ -1 := fun h ↦ hγ₁ <| Subtype.ext <| by
      have e : (QuotientGroup.mk g : PSL(2, ℂ)) = 1 := by
        rw [h]
        exact (QuotientGroup.eq_one_iff _).mpr
          (SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl))
      exact e
    exact hyperbolicVolume_setOf_smul_eq_self g hne₁ hne₂
  rcases Measure.exists_isFundamentalDomain_of_properlyDiscontinuousSMul hyperbolicVolume hnull with
    ⟨s, hs, -, hF⟩
  exact ⟨s, hs, hF⟩

instance : hyperbolicVolume.IsOpenPosMeasure where
  open_pos A hA hne := by
    rw [hyperbolicVolume_apply hA.measurableSet]
    have ho : IsOpen (coords '' A) := isOpenEmbedding_coords.isOpenMap A hA
    have hA₀ : (coords '' A).Nonempty := hne.image _
    have hpos : 0 < volume (coords '' A) := ho.measure_pos volume hA₀
    have hm : Measurable fun q : ℂ × ℝ ↦ ENNReal.ofReal (q.2 ^ 3)⁻¹ := by
      fun_prop
    refine ne_of_gt ((setLIntegral_pos_iff hm).mpr ?_)
    refine lt_of_lt_of_le hpos (measure_mono fun q hq ↦ ?_)
    rcases hq with ⟨z, hz, rfl⟩
    refine ⟨?_, ⟨z, hz, rfl⟩⟩
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.mpr (pow_pos (coords_snd_pos z) 3)

variable {k : ℕ} {F : HyperbolicThreeSpace → Fin (k + 1) → ℂ}

lemma continuous_of_analyticAt (hF : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords) :
    Continuous F := by
  have h : F = extend F ∘ coords := funext fun z ↦ (extend_coords z F).symm
  rw [h]
  exact continuous_iff_continuousAt.mpr fun z ↦
    (hF z).continuousAt.comp isOpenEmbedding_coords.continuous.continuousAt

lemma continuous_bianchiNormSq (hF : Continuous F) : Continuous (bianchiNormSq F) := by
  unfold bianchiNormSq
  have hco : Continuous (coords : HyperbolicThreeSpace → ℂ × ℝ) :=
    isOpenEmbedding_coords.continuous
  have hh : Continuous fun z : HyperbolicThreeSpace ↦ UpperHalfSpace.height z := hco.snd
  have hi (i : Fin (k + 1)) : Continuous fun z ↦ F z i := (continuous_apply i).comp hF
  fun_prop

lemma eq_zero_of_setIntegral_eq_zero (hF : IsBianchiModularForm σ 𝔑.gamma0GL k F)
    {s : Set HyperbolicThreeSpace}
    (hs : IsFundamentalDomain (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) s hyperbolicVolume)
    (hi : IntegrableOn (fun z ↦ (z.height ^ k : ℂ) * symPowInner k (F z) (F z)) s hyperbolicVolume)
    (h₀ : ∫ z in s, (z.height ^ k : ℂ) * symPowInner k (F z) (F z) ∂hyperbolicVolume = 0) :
    F = 0 := by
  have : Countable (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) := countable_bianchiPSLGroup
  have hc : Continuous F := continuous_of_analyticAt hF.analyticAt
  have he (z : HyperbolicThreeSpace) :
      (z.height ^ k : ℂ) * symPowInner k (F z) (F z) = (bianchiNormSq F z : ℂ) :=
    bianchiPairing_self F z
  simp only [he] at hi h₀
  have hi' : IntegrableOn (bianchiNormSq F) s hyperbolicVolume := by
    simpa using hi.re
  rw [integral_complex_ofReal, ofReal_eq_zero, setIntegral_eq_zero_iff_of_nonneg_ae
    (.of_forall (bianchiNormSq_nonneg F)) hi'] at h₀
  have hnull : hyperbolicVolume ({z | F z ≠ 0} ∩ s) = 0 := by
    have h₁ :
        ∀ᵐ x ∂hyperbolicVolume, x ∈ s → bianchiNormSq F x = (0 : HyperbolicThreeSpace → ℝ) x :=
      (ae_restrict_iff'₀ hs.nullMeasurableSet).mp h₀
    refine measure_mono_null ?_ (ae_iff.mp h₁)
    rintro z ⟨hz, hzs⟩
    simp only [Classical.not_imp]
    exact ⟨hzs, fun h ↦ hz ((bianchiNormSq_eq_zero_iff F z).mp h)⟩
  have hinv (γ' : bianchiPSLGroup σ (bianchiGammaZero 𝔑)) :
      γ' • {z : HyperbolicThreeSpace | F z ≠ 0} = {z | F z ≠ 0} := by
    rcases γ' with ⟨γ', hγ'⟩
    rcases exists_mem_gamma0GL_of_mem_bianchiPSLGroup hγ' with ⟨γ, hγ, g, hg, rfl⟩
    have hgF : bianchiSlash k g F = F := hF.mem_bianchiSlashInvariants _
      ((mem_bianchiGammaZero_iff _).mpr ⟨γ, hγ, rfl⟩) g hg
    have key (y : HyperbolicThreeSpace) : F (g • y) = 0 ↔ F y = 0 := by
      have h₁ : bianchiNormSq (bianchiSlash k g F) y = bianchiNormSq F (g • y) :=
      bianchiNormSq_bianchiSlash g F y
      rw [hgF] at h₁
      rw [← bianchiNormSq_eq_zero_iff F (g • y), ← bianchiNormSq_eq_zero_iff F y, h₁]
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have h₂ :
        x = g • ((⟨QuotientGroup.mk g, hγ'⟩ : bianchiPSLGroup σ (bianchiGammaZero 𝔑))⁻¹ • x) :=
      (smul_inv_smul (⟨QuotientGroup.mk g, hγ'⟩ : bianchiPSLGroup σ (bianchiGammaZero 𝔑)) x).symm
    simp only [mem_ofPred_eq, ne_eq]
    rw [← key _, ← h₂]
  have h₁ : hyperbolicVolume {z : HyperbolicThreeSpace | F z ≠ 0} = 0 :=
    hs.measure_zero_of_invariant _ hinv hnull
  have ho : IsOpen {z : HyperbolicThreeSpace | F z ≠ 0} := isOpen_ne_fun hc continuous_const
  have h₂ : {z | F z ≠ 0} = ∅ := ho.measure_eq_zero_iff hyperbolicVolume |>.mp h₁
  funext z
  by_contra hz
  have hz' : z ∈ {z : HyperbolicThreeSpace | F z ≠ 0} := hz
  rw [h₂] at hz'
  exact hz'

/-- **The new space and the old space meet in `0`** (LMFDB `mf.bianchi.spaces`): over an imaginary
quadratic field `K`, a function `F` which lies in the old space `bianchiOldforms σ k 𝔑` and in the
new space `bianchiNewSubspace σ k 𝔑` vanishes: on a fundamental domain `s` of `Γ̄₀(𝔑)`,
`∫_s y^k ⟨F(z), F(z)⟩_k dμ = 0` with a nonnegative invariant integrand. -/
lemma eq_zero_of_mem_bianchiOldforms_of_mem_bianchiNewSubspace (hK : finrank ℚ K = 2)
    (hold : F ∈ bianchiOldforms σ k 𝔑) (hnew : F ∈ bianchiNewSubspace σ k 𝔑) : F = 0 := by
  rcases exists_isFundamentalDomain_bianchiPSLGroup (σ := σ) 𝔑 hK with ⟨s, -, hs⟩
  rcases hnew.2 F hold s hs with ⟨hi, h₀⟩
  exact eq_zero_of_setIntegral_eq_zero hnew.1.1 hs hi h₀

end HyperbolicThreeSpace
