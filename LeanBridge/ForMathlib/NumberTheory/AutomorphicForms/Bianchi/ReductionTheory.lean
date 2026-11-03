import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.GammaZeroFundamentalDomain
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.LevelOperators
import Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-!
# Reduction theory for Bianchi groups

Let `K` be an imaginary quadratic field of class number `1`, embedded in `ℂ` by `σ`. Every point of
`ℋ₃` can be moved by `SL₂(𝒪_K)` to a height bounded below by a constant depending only on `K`
(`HyperbolicThreeSpace.exists_le_height_smul`): for `z = (x, y)`, Minkowski's theorem on the convex
body `{(c, d) ∈ ℂ² : |c| y ≤ ρ, |cx + d| ≤ ρ}`, of volume `π² ρ⁴ / y²`, applied to the lattice
`σ(𝒪_K)²`, gives a nonzero `(c, d)` with `|cx + d|² + |c|² y² ≤ C y`, and `(c, d)` can be taken
coprime, as `𝒪_K` is a principal ideal domain.

The level `Γ₀(𝔑)` has finitely many right cosets in `GL₂(𝒪_K)`, a right coset being determined by
the second row of a matrix modulo `𝔑` (`HyperbolicThreeSpace.exists_finite_gamma0GL_cosets`). So
the invariant function `y^k ⟨F, F⟩_k` of `F` invariant under `Γ₀(𝔑)` is determined by the functions
`y^k ⟨F ∣ r, F ∣ r⟩_k` on the set of the points of height at least `y₀`, for `r` in a finite set
depending only on `𝔑` (`HyperbolicThreeSpace.exists_finite_bianchiNormSq_eq`).

## Main results

* `HyperbolicThreeSpace.exists_ne_zero_norm_le`: Minkowski's theorem for `σ(𝒪_K)²`.
* `HyperbolicThreeSpace.exists_le_height_smul`: reduction theory for `SL₂(𝒪_K)`.
* `HyperbolicThreeSpace.exists_finite_gamma0GL_cosets`: `Γ₀(𝔑)` has finite index in `GL₂(𝒪_K)`.
* `HyperbolicThreeSpace.exists_finite_bianchiNormSq_eq`: the invariant norm of a form of level
  `Γ₀(𝔑)` is seen by finitely many translates above a fixed height.
-/

open Complex Ideal Matrix MeasureTheory Module NumberField Set

open Ideal renaming Quotient.mk → quotientMk

open scoped MatrixGroups Real

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] {σ : K →+* ℂ} {x : K} {k : ℕ}
  {F : HyperbolicThreeSpace → Fin (k + 1) → ℂ}

lemma volume_setOf_norm_mul_le {w : ℂ} {y ρ : ℝ} (hy : 0 < y) :
    volume {p : ℂ × ℂ | ‖p.1‖ * y ≤ ρ ∧ ‖p.1 * w + p.2‖ ≤ ρ} =
      ENNReal.ofReal (ρ / y) ^ 2 * NNReal.pi * (ENNReal.ofReal ρ ^ 2 * NNReal.pi) := by
  have hc : IsClosed {p : ℂ × ℂ | ‖p.1‖ * y ≤ ρ ∧ ‖p.1 * w + p.2‖ ≤ ρ} :=
    (isClosed_le (f := fun p : ℂ × ℂ ↦ ‖p.1‖ * y) (by fun_prop) continuous_const).inter
      (isClosed_le (f := fun p : ℂ × ℂ ↦ ‖p.1 * w + p.2‖) (by fun_prop) continuous_const)
  have hs (c : ℂ) : volume (Prod.mk c ⁻¹' {p : ℂ × ℂ | ‖p.1‖ * y ≤ ρ ∧ ‖p.1 * w + p.2‖ ≤ ρ}) =
      (Metric.closedBall (0 : ℂ) (ρ / y)).indicator
        (fun _ ↦ ENNReal.ofReal ρ ^ 2 * NNReal.pi) c := by
    by_cases hcρ : ‖c‖ * y ≤ ρ
    · have h₁ : Prod.mk c ⁻¹' {p : ℂ × ℂ | ‖p.1‖ * y ≤ ρ ∧ ‖p.1 * w + p.2‖ ≤ ρ} =
          Metric.closedBall (-(c * w)) ρ := by
        ext d
        simp [hcρ, dist_eq_norm, add_comm]
      have h₂ : c ∈ Metric.closedBall (0 : ℂ) (ρ / y) := by
        simpa [le_div_iff₀ hy] using hcρ
      rw [h₁, Complex.volume_closedBall, Set.indicator_of_mem h₂]
    · have h₁ : Prod.mk c ⁻¹' {p : ℂ × ℂ | ‖p.1‖ * y ≤ ρ ∧ ‖p.1 * w + p.2‖ ≤ ρ} = ∅ := by
        ext d
        simp [hcρ]
      have h₂ : c ∉ Metric.closedBall (0 : ℂ) (ρ / y) := by
        simpa [le_div_iff₀ hy] using hcρ
      rw [h₁, measure_empty, Set.indicator_of_notMem h₂]
  rw [Measure.volume_eq_prod, Measure.prod_apply hc.measurableSet]
  simp only [hs]
  rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet, setLIntegral_const,
    Complex.volume_closedBall, mul_comm]

lemma convex_setOf_norm_mul_le {w : ℂ} {y ρ : ℝ} (hy : 0 < y) :
    Convex ℝ {p : ℂ × ℂ | ‖p.1‖ * y ≤ ρ ∧ ‖p.1 * w + p.2‖ ≤ ρ} := by
  intro p hp q hq a b ha hb hab
  have hp₁ : ‖p.1‖ * y ≤ ρ := hp.1
  have hp₂ : ‖p.1 * w + p.2‖ ≤ ρ := hp.2
  have hq₁ : ‖q.1‖ * y ≤ ρ := hq.1
  have hq₂ : ‖q.1 * w + q.2‖ ≤ ρ := hq.2
  have hρ : ρ = a * ρ + b * ρ := by
    rw [← add_mul, hab, one_mul]
  have h₁ : ‖(a • p + b • q).1‖ ≤ a * ‖p.1‖ + b * ‖q.1‖ := by
    refine (norm_add_le _ _).trans_eq ?_
    rw [Prod.smul_fst, Prod.smul_fst, norm_smul, norm_smul, Real.norm_of_nonneg ha,
      Real.norm_of_nonneg hb]
  have h₂ :
      ‖(a • p + b • q).1 * w + (a • p + b • q).2‖ ≤ a * ‖p.1 * w + p.2‖ + b * ‖q.1 * w + q.2‖ := by
    have e :
        (a • p + b • q).1 * w + (a • p + b • q).2 = a • (p.1 * w + p.2) + b • (q.1 * w + q.2) := by
      simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, real_smul]
      ring1
    rw [e]
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  refine ⟨?_, h₂.trans ?_⟩
  · have h₃ : ‖(a • p + b • q).1‖ * y ≤ (a * ‖p.1‖ + b * ‖q.1‖) * y :=
      mul_le_mul_of_nonneg_right h₁ hy.le
    linarith [mul_le_mul_of_nonneg_left hp₁ ha, mul_le_mul_of_nonneg_left hq₁ hb]
  · linarith [mul_le_mul_of_nonneg_left hp₂ ha, mul_le_mul_of_nonneg_left hq₂ hb]

variable [NumberField K]

lemma exists_apply_eq_of_mem_span_prod (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) {p : ℂ × ℂ}
    (hp : p ∈ Submodule.span ℤ (Set.range
      ((integralLatticeBasis σ hK hx).prod (integralLatticeBasis σ hK hx)))) :
    ∃ c d : 𝓞 K, p = (σ c, σ d) := by
  have h₁ : p.1 ∈ Submodule.span ℤ (Set.range (integralLatticeBasis σ hK hx)) ∧ p.2 ∈
      Submodule.span ℤ (Set.range (integralLatticeBasis σ hK hx)) := by
    induction hp using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨i | i, rfl⟩
      · simpa using Submodule.subset_span (Set.mem_range_self i)
      · simpa using Submodule.subset_span (Set.mem_range_self i)
    | zero => exact ⟨zero_mem _, zero_mem _⟩
    | add y z _ _ hy hz => exact ⟨add_mem hy.1 hz.1, add_mem hy.2 hz.2⟩
    | smul a y _ hy => exact ⟨Submodule.smul_mem _ a hy.1, Submodule.smul_mem _ a hy.2⟩
  have h₂ (l : ℂ) (hl : l ∈ Submodule.span ℤ (Set.range (integralLatticeBasis σ hK hx))) :
      ∃ c : 𝓞 K, l = σ c := by
    have h₃ : l ∈ bianchiScaledLattice σ 1 := by
      rw [← toAddSubgroup_span_integralLatticeBasis hK hx]
      exact hl
    rcases mem_bianchiScaledLattice.mp h₃ with ⟨c, hc⟩
    exact ⟨c, by rw [← hc, one_mul]⟩
  rcases h₂ _ h₁.1 with ⟨c, hc⟩
  rcases h₂ _ h₁.2 with ⟨d, hd⟩
  exact ⟨c, d, Prod.ext hc hd⟩

/-- **Minkowski's theorem for `σ(𝒪_K)²`**: there is a constant `C > 0` such that for every `w ∈ ℂ`
and `y > 0` there is a nonzero `(c, d) ∈ 𝒪_K²` with `|cw + d|² ≤ C y` and `|c|² y² ≤ C y`. -/
lemma exists_ne_zero_norm_le (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) : ∃ C : ℝ, 0 < C ∧
    ∀ (w : ℂ) (y : ℝ), 0 < y → ∃ c d : 𝓞 K, (c ≠ 0 ∨ d ≠ 0) ∧ ‖σ c * w + σ d‖ ^ 2 ≤ C * y ∧
    ‖σ c‖ ^ 2 * y ^ 2 ≤ C * y := by
  let B : Basis _ ℝ (ℂ × ℂ) := (integralLatticeBasis σ hK hx).prod (integralLatticeBasis σ hK hx)
  have fund : IsAddFundamentalDomain (Submodule.span ℤ (Set.range B)).toAddSubgroup
      (ZSpan.fundamentalDomain B) (volume : Measure (ℂ × ℂ)) := ZSpan.isAddFundamentalDomain' B _
  have hfin : volume (ZSpan.fundamentalDomain B) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded B).measure_lt_top.ne
  have hv : 0 ≤ (volume (ZSpan.fundamentalDomain B)).toReal := ENNReal.toReal_nonneg
  have hC₀ : 0 < 16 * (volume (ZSpan.fundamentalDomain B)).toReal + 1 := by
    positivity
  refine ⟨_, hC₀, fun w y hy ↦ ?_⟩
  have hCy : 0 ≤ (16 * (volume (ZSpan.fundamentalDomain B)).toReal + 1) * y := (mul_pos hC₀ hy).le
  have : Countable (Submodule.span ℤ (Set.range B)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range B)))
  have : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hsq : √((16 * (volume (ZSpan.fundamentalDomain B)).toReal + 1) * y) ^ 2 =
      (16 * (volume (ZSpan.fundamentalDomain B)).toReal + 1) * y := Real.sq_sqrt hCy
  have hπ : ((NNReal.pi : NNReal) : ENNReal) = ENNReal.ofReal π := by
    rw [ENNReal.ofReal, ← NNReal.coe_real_pi, Real.toNNReal_coe]
  have hfr : finrank ℝ (ℂ × ℂ) = 4 := by
    rw [Module.finrank_prod, Complex.finrank_real_complex]
  have hvol : volume (ZSpan.fundamentalDomain B) * 2 ^ finrank ℝ (ℂ × ℂ) < volume {p : ℂ × ℂ |
        ‖p.1‖ * y ≤ √((16 * (volume (ZSpan.fundamentalDomain B)).toReal + 1) * y) ∧
        ‖p.1 * w + p.2‖ ≤ √((16 * (volume (ZSpan.fundamentalDomain B)).toReal + 1) * y)} := by
    have h₂ : (2 : ENNReal) ^ 4 = ENNReal.ofReal 16 := by
      rw [(by norm_num : (16 : ℝ) = (2 : ℝ) ^ 4), ENNReal.ofReal_pow zero_le_two,
        ENNReal.ofReal_ofNat]
    have hρy : 0 ≤ √((16 * (volume (ZSpan.fundamentalDomain B)).toReal + 1) * y) / y :=
      div_nonneg (Real.sqrt_nonneg _) hy.le
    rw [volume_setOf_norm_mul_le hy, hfr, h₂, hπ, ← ENNReal.ofReal_toReal hfin,
      ENNReal.toReal_ofReal ENNReal.toReal_nonneg, ← ENNReal.ofReal_pow hρy,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul hv,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_lt_ofReal_iff (by positivity), div_pow,
      hsq]
    have hπ₃ : 1 ≤ π := by
      linarith [Real.pi_gt_three]
    have e : (16 * (volume (ZSpan.fundamentalDomain B)).toReal + 1) * y / y ^ 2 * π *
        ((16 * (volume (ZSpan.fundamentalDomain B)).toReal + 1) * y * π) =
          (16 * (volume (ZSpan.fundamentalDomain B)).toReal + 1) ^ 2 * π ^ 2 := by
      field_simp
    rw [e]
    nlinarith [mul_nonneg hv hv, sq_nonneg (π - 1), mul_nonneg hC₀.le hC₀.le,
      mul_le_mul_of_nonneg_left (one_le_pow₀ hπ₃ (n := 2)) (mul_nonneg hC₀.le hC₀.le)]
  have hsymm : ∀ p ∈ {p : ℂ × ℂ | ‖p.1‖ * y ≤
      √((16 * (volume (ZSpan.fundamentalDomain B)).toReal + 1) * y) ∧
        ‖p.1 * w + p.2‖ ≤ √((16 * (volume (ZSpan.fundamentalDomain B)).toReal + 1) * y)}, -p ∈
      {p : ℂ × ℂ | ‖p.1‖ * y ≤ √((16 * (volume (ZSpan.fundamentalDomain B)).toReal + 1) * y) ∧
          ‖p.1 * w + p.2‖ ≤ √((16 * (volume (ZSpan.fundamentalDomain B)).toReal + 1) * y)} :=
    fun p hp ↦ ⟨by simpa using hp.1, by
      have e : (-p).1 * w + (-p).2 = -(p.1 * w + p.2) := by
        simp only [Prod.fst_neg, Prod.snd_neg]
        ring1
      rw [e, norm_neg]
      exact hp.2⟩
  rcases exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund hsymm
    (convex_setOf_norm_mul_le hy) hvol with ⟨⟨p, hp⟩, hp₀, hpS⟩
  rcases exists_apply_eq_of_mem_span_prod hK hx hp with ⟨c, d, rfl⟩
  refine ⟨c, d, ?_, ?_, ?_⟩
  · by_contra hcd
    push Not at hcd
    refine hp₀ (Subtype.ext ?_)
    simp [hcd.1, hcd.2]
  · have h₁ : ‖σ (c : K) * w + σ (d : K)‖ ^ 2 ≤
        √((16 * (volume (ZSpan.fundamentalDomain B)).toReal + 1) * y) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hpS.2 2
    rwa [hsq] at h₁
  · have h₁ :
        (‖σ (c : K)‖ * y) ^ 2 ≤ √((16 * (volume (ZSpan.fundamentalDomain B)).toReal + 1) * y) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hpS.1 2
    rwa [hsq, mul_pow] at h₁

lemma exists_isCoprime_mul {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {c d : R}
    (h : c ≠ 0 ∨ d ≠ 0) : ∃ g c' d' : R, g ≠ 0 ∧ c = g * c' ∧ d = g * d' ∧ IsCoprime c' d' := by
  rcases (IsPrincipalIdealRing.principal (Ideal.span {c, d})).principal with ⟨g, hg⟩
  rw [Ideal.submodule_span_eq] at hg
  have hc : c ∈ Ideal.span {g} := hg ▸ Ideal.subset_span (by simp)
  have hd : d ∈ Ideal.span {g} := hg ▸ Ideal.subset_span (by simp)
  rcases Ideal.mem_span_singleton.mp hc with ⟨c', rfl⟩
  rcases Ideal.mem_span_singleton.mp hd with ⟨d', rfl⟩
  have hg₀ : g ≠ 0 := by
    rintro rfl
    simp at h
  have hgm : g ∈ Ideal.span {g * c', g * d'} := hg ▸ Ideal.mem_span_singleton_self g
  rcases Ideal.mem_span_pair.mp hgm with ⟨u, v, huv⟩
  exact ⟨g, c', d', hg₀, rfl, rfl, u, v, mul_left_cancel₀ hg₀ (by linear_combination huv)⟩

/-- **The level `Γ₀(𝔑)` has finite index in `GL₂(𝒪_K)`**: there is a finite system of
representatives of the right cosets of `Γ₀(𝔑)` in `GL₂(𝒪_K)`, for `𝔑 ≠ 0`, as the right coset of a
matrix is determined by its second row modulo `𝔑`. -/
lemma exists_finite_gamma0GL_cosets {𝔑 : Ideal (𝓞 K)} (h𝔑 : 𝔑 ≠ ⊥) : ∃ R : Set (GL (Fin 2) (𝓞 K)),
    R.Finite ∧ ∀ γ : GL (Fin 2) (𝓞 K), ∃ r ∈ R, γ * r⁻¹ ∈ 𝔑.gamma0GL := by
  have : Finite (𝓞 K ⧸ 𝔑) := Ideal.finiteQuotientOfFreeOfNeBot 𝔑 h𝔑
  let f : GL (Fin 2) (𝓞 K) → (𝓞 K ⧸ 𝔑) × (𝓞 K ⧸ 𝔑) := fun γ ↦
    (quotientMk 𝔑 (γ.val 1 0), quotientMk 𝔑 (γ.val 1 1))
  choose g hg using fun v : Set.range f ↦ v.2
  refine ⟨Set.range g, Set.finite_range g, fun γ ↦ ⟨g ⟨f γ, γ, rfl⟩, Set.mem_range_self _, ?_⟩⟩
  have h : f (g ⟨f γ, γ, rfl⟩) = f γ := hg ⟨f γ, γ, rfl⟩
  have h₁ : (γ * (g ⟨f γ, γ, rfl⟩)⁻¹).val 1 0 =
      ((GeneralLinearGroup.det (g ⟨f γ, γ, rfl⟩))⁻¹ : (𝓞 K)ˣ).val *
        (γ.val 1 0 * (g ⟨f γ, γ, rfl⟩).val 1 1 - γ.val 1 1 * (g ⟨f γ, γ, rfl⟩).val 1 0) := by
    rw [Units.val_mul, coe_inv_gl]
    simp [mul_apply]
    ring1
  have h₃ : quotientMk 𝔑 ((g ⟨f γ, γ, rfl⟩).val 1 0) = quotientMk 𝔑 (γ.val 1 0) :=
    (Prod.ext_iff.mp h).1
  have h₄ : quotientMk 𝔑 ((g ⟨f γ, γ, rfl⟩).val 1 1) = quotientMk 𝔑 (γ.val 1 1) :=
    (Prod.ext_iff.mp h).2
  have h₂ : quotientMk 𝔑 ((γ * (g ⟨f γ, γ, rfl⟩)⁻¹).val 1 0) = 0 := by
    rw [h₁, map_mul, map_sub, map_mul, map_mul, h₃, h₄, mul_comm (quotientMk 𝔑 (γ.val 1 1)),
      sub_self, mul_zero]
  exact Quotient.eq_zero_iff_mem.mp h₂

variable [IsTotallyComplex K]

/-- **Reduction theory for `SL₂(𝒪_K)`**: for `K` imaginary quadratic of class number `1`, there is
`y₀ > 0` such that every point of `ℋ₃` can be moved by `SL₂(𝒪_K)` to a point of height at
least `y₀`. -/
lemma exists_le_height_smul [IsPrincipalIdealRing (𝓞 K)] (hK : finrank ℚ K = 2) : ∃ y₀ : ℝ, 0 < y₀ ∧
    ∀ z : HyperbolicThreeSpace, ∃ γ : SL(2, 𝓞 K), y₀ ≤
    (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ • z).height := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  rcases exists_ne_zero_norm_le hK hx with ⟨C, hC, h⟩
  refine ⟨(2 * C)⁻¹, by positivity, fun z ↦ ?_⟩
  have hy : 0 < z.coords.2 := coords_snd_pos z
  rcases h z.coords.1 z.coords.2 hy with ⟨c, d, hcd, h₁, h₂⟩
  rcases exists_isCoprime_mul hcd with ⟨g, c', d', hg, rfl, rfl, hcop⟩
  rcases hcop.exists_SL2_row 1 with ⟨γ, hγ₀, hγ₁⟩
  refine ⟨γ, ?_⟩
  have hg₁ : 1 ≤ ‖σ g‖ := one_le_norm_apply hK hg
  have hc' : ‖σ c'‖ ^ 2 * z.coords.2 ^ 2 ≤ C * z.coords.2 := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)) h₂
    have e : ‖σ ((g * c' : 𝓞 K) : K)‖ = ‖σ g‖ * ‖σ c'‖ := by
      rw [← norm_mul, ← map_mul]
      rfl
    rw [e, mul_pow]
    exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hg₁)
  have hd' : ‖σ c' * z.coords.1 + σ d'‖ ^ 2 ≤ C * z.coords.2 := by
    refine le_trans ?_ h₁
    have e : σ ((g * c' : 𝓞 K) : K) * z.coords.1 + σ ((g * d' : 𝓞 K) : K) =
        σ g * (σ c' * z.coords.1 + σ d') := by
      simp only [map_mul]
      ring1
    rw [e, norm_mul, mul_pow]
    exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hg₁)
  have hden : moebiusDenom (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ) z.coords ≤
      2 * C * z.coords.2 := by
    have e₀ : (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ) 1 0 = σ c' := by
      simp [hγ₀]
    have e₁ : (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ) 1 1 = σ d' := by
      simp [hγ₁]
    rw [moebiusDenom, e₀, e₁, normSq_eq_norm_sq, normSq_eq_norm_sq]
    linarith
  have hpos : 0 < moebiusDenom (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ) z.coords :=
    moebiusDenom_pos _ hy
  rw [height_smul, inv_le_iff_one_le_mul₀ (by positivity)]
  have hh : z.height = z.coords.2 := rfl
  rw [hh, div_mul_eq_mul_div, le_div_iff₀ hpos, one_mul]
  linarith

variable (σ) in
/-- **The invariant norm of a form of level `Γ₀(𝔑)` is seen by finitely many translates above a
fixed height**: for `K` imaginary quadratic of class number `1` and `𝔑 ≠ 0`, there are `y₀ > 0` and
a finite set `R ⊆ GL₂(𝒪_K)` such that for `F` invariant under `Γ₀(𝔑)`, in even weight, every value
`y^k ⟨F, F⟩_k(z)` is a value `y^k ⟨F ∣ r, F ∣ r⟩_k(w)`, with `r ∈ R` and `w` of height at
least `y₀`. -/
lemma exists_finite_bianchiNormSq_eq [IsPrincipalIdealRing (𝓞 K)] (hK : finrank ℚ K = 2)
    {𝔑 : Ideal (𝓞 K)} (h𝔑 : 𝔑 ≠ ⊥) : ∃ (y₀ : ℝ) (R : Set (GL (Fin 2) (𝓞 K))), 0 < y₀ ∧ R.Finite ∧
      ∀ (k : ℕ) (F : HyperbolicThreeSpace → Fin (k + 1) → ℂ), Even k →
        IsBianchiSlashInvariant σ 𝔑.gamma0GL k F → ∀ z : HyperbolicThreeSpace, ∃ r ∈ R,
          ∃ w : HyperbolicThreeSpace, y₀ ≤ w.height ∧ bianchiNormSq F z =
            bianchiNormSq (glSlash σ k r F) w := by
  rcases exists_le_height_smul (σ := σ) hK with ⟨y₀, hy₀, hred⟩
  rcases exists_finite_gamma0GL_cosets h𝔑 with ⟨R, hR, hcos⟩
  refine ⟨y₀, R, hy₀, hR, fun k F hk hF z ↦ ?_⟩
  rcases hred z with ⟨γ, hγ⟩
  rcases hcos (SpecialLinearGroup.toGL γ⁻¹) with ⟨r, hr, hδ⟩
  refine ⟨r, hr, _, hγ, ?_⟩
  have h₁ : glSlash σ k (SpecialLinearGroup.toGL γ⁻¹) F = glSlash σ k r F := by
    have e : SpecialLinearGroup.toGL γ⁻¹ = SpecialLinearGroup.toGL γ⁻¹ * r⁻¹ * r := by
      group
    rw [e, glSlash_mul hk, hF.glSlash_eq hδ]
  have h₂ : glSlash σ k (SpecialLinearGroup.toGL γ⁻¹) F =
      bianchiSlash k (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ)⁻¹ F := by
    have hrep (γ' : SL(2, 𝓞 K)) : IsSLRepresentative σ
        (GeneralLinearGroup.map (algebraMap (𝓞 K) K) (SpecialLinearGroup.toGL γ'))
        (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ') := ⟨1, by
      ext i j
      simp⟩
    rw [← map_inv]
    exact bianchiGLSlash_eq hk (hrep γ⁻¹)
  rw [← h₁, h₂, bianchiNormSq_bianchiSlash, inv_smul_smul]

end HyperbolicThreeSpace
