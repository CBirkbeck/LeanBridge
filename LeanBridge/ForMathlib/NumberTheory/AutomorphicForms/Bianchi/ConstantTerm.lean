import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.HeckeSelfAdjoint
import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# The constant terms of Bianchi modular forms, and the finite dimension of `M_k(𝔑)`

Let `K` be an imaginary quadratic field of class number `1`, embedded in `ℂ` by `σ`, and `𝔑 = (N)` a
nonzero ideal of `𝒪_K`. The cusp forms are the modular forms whose constant terms at all the cusps
vanish, and this is a finite number of linear conditions.

On the one hand the constant term `φ(y) = vol(P)⁻¹ ∫_P F(x, y) dx` of a harmonic function `F`
periodic for a lattice is a harmonic Fourier mode of frequency `0`. So the radial equations of `φ`
are uncoupled Euler equations: for `R_j = y^k φ_j`,
`y² R_j'' - (2j + 1) y R_j' + ((j + 1)² - k²/4) R_j = 0`, of exponents `j + 1 ± k/2`, and `φ` is
determined by `φ(1)` and `φ'(1)` (`HyperbolicThreeSpace.bianchiFourierCoeff_zero_eq_zero`).

On the other hand a matrix of `SL₂(K)` is the product of a matrix of `SL₂(𝒪_K)`, as `𝒪_K` is a
principal ideal domain, and of an upper triangular matrix, and `Γ₀(𝔑)` has finite index in
`GL₂(𝒪_K)`. So the constant terms of a form `F` of level `Γ₀(𝔑)` at all the cusps follow from those
of the functions `F ∣ r ∣ (N, 0; 0, 1)`, which are periodic for `σ(𝒪_K)`, for `r` in a finite set
(`HyperbolicThreeSpace.mem_bianchiCuspForms_of_setIntegral_eq_zero`).

Hence `M_k(𝔑) / S_k(𝔑)` is finite dimensional, and so is `M_k(𝔑)`, for `k ≥ 1`
(`HyperbolicThreeSpace.finiteDimensional_bianchiModularForms`).

## Main definitions

* `HyperbolicThreeSpace.bianchiConstantTermMap`: the linear map `F ↦ (φ_r(1), φ_r'(1))_r`, where
  `φ_r` is the constant term of `F ∣ r ∣ (N, 0; 0, 1)`.

## Main results

* `HyperbolicThreeSpace.bianchiFourierCoeff_zero_eq_zero`: the constant term of a periodic harmonic
  function is determined by its value and its derivative at `y = 1`.
* `HyperbolicThreeSpace.mem_bianchiCuspForms_of_setIntegral_eq_zero`: a form is a cusp form as soon
  as its constant terms vanish at finitely many cusps.
* `HyperbolicThreeSpace.finiteDimensional_bianchiModularForms`: `M_k(𝔑)` is finite dimensional.
-/

open Bornology Complex Matrix MeasureTheory Module NumberField HilbertModularGroup Set

open scoped MatrixGroups nonZeroDivisors OnePoint Topology

namespace HyperbolicThreeSpace

lemma eq_zero_of_mul_eq_mul {f f' : ℝ → ℂ} {c : ℂ} (hf : ∀ y, 0 < y → HasDerivAt f (f' y) y)
    (h : ∀ y : ℝ, 0 < y → y * f' y = c * f y) (h₁ : f 1 = 0) {y : ℝ} (hy : 0 < y) : f y = 0 := by
  have hg (t : ℝ) : HasDerivAt (fun t : ℝ ↦ cexp (-c * t) * f (Real.exp t)) 0 t := by
    have h₂ : HasDerivAt (fun t : ℝ ↦ cexp (-c * t)) (cexp (-c * t) * (-c * 1)) t :=
      ((hasDerivAt_id t).ofReal_comp.const_mul (-c)).cexp
    have h₃ : HasDerivAt (fun t : ℝ ↦ f (Real.exp t)) (Real.exp t • f' (Real.exp t)) t :=
      (hf _ (Real.exp_pos t)).scomp t (Real.hasDerivAt_exp t)
    convert h₂.mul h₃ using 1
    rw [real_smul, h _ (Real.exp_pos t)]
    ring1
  have h₂ : cexp (-c * (Real.log y : ℝ)) * f (Real.exp (Real.log y)) =
      cexp (-c * (0 : ℝ)) * f (Real.exp 0) :=
    is_const_of_deriv_eq_zero (fun t ↦ (hg t).differentiableAt) (fun t ↦ (hg t).deriv) _ _
  rw [Real.exp_log hy, Real.exp_zero, h₁, mul_zero] at h₂
  exact (mul_eq_zero.mp h₂).resolve_left (exp_ne_zero _)

lemma eq_zero_of_euler {R : ℝ → ℂ} {s₁ s₂ : ℂ} (hR : ContDiffOn ℝ 2 R (Ioi 0))
    (h : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv R) y - (s₁ + s₂ - 1) * y * deriv R y +
      s₁ * s₂ * R y = 0) (h₀ : R 1 = 0) (h₁ : deriv R 1 = 0) {y : ℝ} (hy : 0 < y) : R y = 0 := by
  have hd {y : ℝ} (hy : 0 < y) : HasDerivAt R (deriv R y) y :=
    ((hR.contDiffAt (Ioi_mem_nhds hy)).differentiableAt two_ne_zero).hasDerivAt
  have hd' {y : ℝ} (hy : 0 < y) : HasDerivAt (deriv R) (deriv (deriv R) y) y :=
    (((hR.deriv_of_isOpen isOpen_Ioi (m := 1) le_rfl).contDiffAt
      (Ioi_mem_nhds hy)).differentiableAt one_ne_zero).hasDerivAt
  have hS (y : ℝ) (hy : 0 < y) : (y : ℂ) * deriv R y - s₁ * R y = 0 := by
    refine eq_zero_of_mul_eq_mul (f := fun y : ℝ ↦ (y : ℂ) * deriv R y - s₁ * R y)
      (f' := fun y ↦ deriv R y + y * deriv (deriv R) y - s₁ * deriv R y) (c := s₂)
      (fun y hy ↦ ?_) (fun y hy ↦ ?_) ?_ hy
    · have h₂ : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) 1 y := (hasDerivAt_id y).ofReal_comp
      simpa only [one_mul] using (h₂.fun_mul (hd' hy)).fun_sub ((hd hy).const_mul s₁)
    · linear_combination h y hy
    · simp [h₀, h₁]
  exact eq_zero_of_mul_eq_mul (c := s₁) (fun y hy ↦ hd hy)
    (fun y hy ↦ by linear_combination hS y hy) h₀ hy

variable {K : Type*} [Field K] {σ : K →+* ℂ} {k : ℕ} {N : (𝓞 K)⁰}
  {F G : HyperbolicThreeSpace → Fin (k + 1) → ℂ} {φ : ℝ → Fin (k + 1) → ℂ} {y : ℝ} {P : Set ℂ}

lemma eq_zero_of_casimirOne (hφ : ContDiffOn ℝ 2 φ (Ioi 0))
    (h : casimirOne (bianchiLift k (bianchiFourierMode 0 φ)) =
      harmonicEigenvalue k • bianchiLift k (bianchiFourierMode 0 φ)) (h₀ : φ 1 = 0)
    (h₁ : deriv φ 1 = 0) (hy : 0 < y) : φ y = 0 := by
  funext i
  have hφd : HasDerivAt φ (deriv φ 1) 1 :=
    ((hφ.contDiffAt (Ioi_mem_nhds one_pos)).differentiableAt two_ne_zero).hasDerivAt
  have hR : fourierModeRadial φ (i : ℕ) y = 0 := by
    refine eq_zero_of_euler (s₁ := (i : ℕ) + 1 - (k : ℂ) / 2) (s₂ := (i : ℕ) + 1 + (k : ℂ) / 2)
      (contDiffOn_fourierModeRadial hφ _) (fun y hy ↦ ?_) ?_ ?_ hy
    · have h₂ : bianchiRadialOperator 0 k (fourierModeRadial φ) (i : ℕ) y = 0 :=
        bianchiRadialOperator_eq_zero_of_casimirOne hφ h (Nat.lt_succ_iff.mp i.2) hy
      rw [bianchiRadialOperator, map_zero, harmonicEigenvalue, ofReal_zero] at h₂
      linear_combination 2 * h₂
    · simp [fourierModeRadial, h₀]
    · have h₂ : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) 1 1 := (hasDerivAt_id (1 : ℝ)).ofReal_comp
      have h₃ : HasDerivAt (fourierModeRadial φ (i : ℕ)) (k * ((1 : ℝ) : ℂ) ^ (k - 1) * 1 *
          φ 1 (Fin.ofNat (k + 1) i) + ((1 : ℝ) : ℂ) ^ k * deriv φ 1 (Fin.ofNat (k + 1) i)) 1 :=
        (h₂.fun_pow k).mul (hasDerivAt_pi.mp hφd (Fin.ofNat (k + 1) i))
      rw [h₃.deriv]
      simp [h₀, h₁]
  have e : Fin.ofNat (k + 1) (i : ℕ) = i := Fin.ofNat_val_eq_self i
  rw [fourierModeRadial, e] at hR
  exact (mul_eq_zero.mp hR).resolve_left (pow_ne_zero _ (ofReal_ne_zero.mpr hy.ne'))

variable (F y) in
lemma bianchiFourierCoeff_zero_eq :
    bianchiFourierCoeff P 0 F y = (volume.real P : ℂ)⁻¹ • ∫ x in P, extend F (x, y) := by
  simp [bianchiFourierCoeff]

/-- **The constant term of a periodic harmonic function is determined by two values** (LMFDB
`mf.bianchi.spaces`): if `F : ℋ₃ → ℂ^{k+1}` is real analytic, harmonic and periodic for a countable
subgroup `Λ` of `ℂ` with a bounded fundamental domain `P`, its constant term `φ` over `P`
(`bianchiFourierCoeff P 0 F`) vanishes as soon as `φ(1)` and `φ'(1)` do, by the radial equations of
frequency `0`, which are uncoupled Euler equations. -/
lemma bianchiFourierCoeff_zero_eq_zero (Λ : AddSubgroup ℂ) [Countable Λ]
    (hFa : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords)
    (hF : IsBianchiHarmonic k F) (hP : IsAddFundamentalDomain Λ P) (hPb : IsBounded P)
    (hper : ∀ l ∈ Λ, ∀ p : ℂ × ℝ, extend F (l + p.1, p.2) = extend F p)
    (h₀ : bianchiFourierCoeff P 0 F 1 = 0) (h₁ : deriv (bianchiFourierCoeff P 0 F) 1 = 0)
    (hy : 0 < y) : bianchiFourierCoeff P 0 F y = 0 := by
  have hh : IsBianchiHarmonic k (bianchiFourierMode 0 (bianchiFourierCoeff P 0 F)) :=
    isBianchiHarmonic_bianchiFourierMode_bianchiFourierCoeff Λ hFa hF hP hPb hper fun l _ ↦ by simp
  exact eq_zero_of_casimirOne (contDiffOn_bianchiFourierCoeff hFa hPb 2) hh.1 h₀ h₁ hy

lemma integrable_extend (hFa : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords)
    (hPb : IsBounded P) (hy : 0 < y) : Integrable (fun x ↦ extend F (x, y)) (volume.restrict P) :=
  ((continuous_extend_mk hFa hy).continuousOn.integrableOn_compact hPb.isCompact_closure).mono_set
    subset_closure

lemma differentiableAt_bianchiFourierCoeff_zero
    (hFa : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords) (hPb : IsBounded P)
    (hy : 0 < y) : DifferentiableAt ℝ (bianchiFourierCoeff P 0 F) y :=
  ((contDiffOn_bianchiFourierCoeff hFa hPb 1).contDiffAt (Ioi_mem_nhds hy)).differentiableAt
    one_ne_zero

lemma bianchiFourierCoeff_zero_add
    (hFa : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords)
    (hGa : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend G) z.coords) (hPb : IsBounded P)
    (hy : 0 < y) : bianchiFourierCoeff P 0 (F + G) y = bianchiFourierCoeff P 0 F y +
      bianchiFourierCoeff P 0 G y := by
  simp only [bianchiFourierCoeff_zero_eq, extend_add, Pi.add_apply]
  rw [integral_add (integrable_extend hFa hPb hy) (integrable_extend hGa hPb hy), smul_add]

lemma deriv_bianchiFourierCoeff_zero_add
    (hFa : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords)
    (hGa : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend G) z.coords) (hPb : IsBounded P) :
    deriv (bianchiFourierCoeff P 0 (F + G)) 1 = deriv (bianchiFourierCoeff P 0 F) 1 +
      deriv (bianchiFourierCoeff P 0 G) 1 := by
  have h : bianchiFourierCoeff P 0 (F + G) =ᶠ[𝓝 1] fun y ↦ bianchiFourierCoeff P 0 F y +
      bianchiFourierCoeff P 0 G y :=
    Filter.eventually_of_mem (Ioi_mem_nhds one_pos) fun y hy ↦
      bianchiFourierCoeff_zero_add hFa hGa hPb hy
  exact h.deriv_eq.trans (deriv_fun_add (differentiableAt_bianchiFourierCoeff_zero hFa hPb one_pos)
    (differentiableAt_bianchiFourierCoeff_zero hGa hPb one_pos))

lemma bianchiFourierCoeff_zero_smul (c : ℂ) :
    bianchiFourierCoeff P 0 (c • F) = c • bianchiFourierCoeff P 0 F := by
  funext y
  simp only [bianchiFourierCoeff_zero_eq, extend_smul, Pi.smul_apply]
  rw [integral_smul, smul_comm]

lemma analyticAt_extend_bianchiLevelRaise_glSlash
    (hF : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords) (r : GL (Fin 2) (𝓞 K))
    (z : HyperbolicThreeSpace) :
    AnalyticAt ℝ (extend (bianchiLevelRaise σ k N (glSlash σ k r F))) z.coords :=
  analyticAt_extend_bianchiSlash _ (analyticAt_extend_bianchiSlash _ hF) z

variable [NumberField K] [IsPrincipalIdealRing (𝓞 K)]

lemma exists_eq_map_mul_heckeUpper (g : SL(2, K)) : ∃ (g₀ : SL(2, 𝓞 K)) (u : Kˣ) (b c : K), c ≠ 0 ∧
    (SpecialLinearGroup.toGL g : Matrix (Fin 2) (Fin 2) K) = c •
      ((GeneralLinearGroup.map (algebraMap (𝓞 K) K) (SpecialLinearGroup.toGL g₀) *
        heckeUpper u b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  classical
  rcases OnePoint.exists_mem_SL2 (𝓞 K) (SpecialLinearGroup.toGL g • (∞ : OnePoint K)) with
    ⟨g₀, hg₀⟩
  have e₀ : SpecialLinearGroup.mapGL K g₀ =
      GeneralLinearGroup.map (algebraMap (𝓞 K) K) (SpecialLinearGroup.toGL g₀) :=
    Units.ext rfl
  rcases (⟨_, rfl⟩ : ∃ τ : GL (Fin 2) K,
    τ = (SpecialLinearGroup.mapGL K g₀)⁻¹ * SpecialLinearGroup.toGL g) with ⟨τ, hτ⟩
  have h₁₀ : τ.val 1 0 = 0 := by
    refine OnePoint.smul_infty_eq_self_iff.mp ?_
    rw [hτ, mul_smul, ← hg₀, inv_smul_smul]
  have hdet : τ.val 0 0 * τ.val 1 1 ≠ 0 := by
    have h : τ.val 0 0 * τ.val 1 1 - τ.val 0 1 * τ.val 1 0 ≠ 0 := by
      rw [← det_fin_two]
      exact (GeneralLinearGroup.det τ).ne_zero
    rwa [h₁₀, mul_zero, sub_zero] at h
  have h₀₀ : τ.val 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have h₁₁ : τ.val 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  have e₁ : (τ : Matrix (Fin 2) (Fin 2) K) = τ.val 0 0 •
      (heckeUpper (Units.mk0 (τ.val 1 1 / τ.val 0 0) (div_ne_zero h₁₁ h₀₀))
        (τ.val 0 1 / τ.val 0 0) : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heckeUpper, h₁₀, mul_div_cancel₀, h₀₀]
  have e₂ : SpecialLinearGroup.toGL g = SpecialLinearGroup.mapGL K g₀ * τ := by
    rw [hτ, mul_inv_cancel_left]
  refine ⟨g₀, Units.mk0 (τ.val 1 1 / τ.val 0 0) (div_ne_zero h₁₁ h₀₀), τ.val 0 1 / τ.val 0 0,
    τ.val 0 0, h₀₀, ?_⟩
  rw [e₂, e₀, Units.val_mul, Units.val_mul, ← mul_smul_comm, ← e₁]

variable [IsTotallyComplex K]

/-- **A form whose constant terms vanish at finitely many cusps is a cusp form** (LMFDB
`mf.bianchi.spaces`): for `K` imaginary quadratic of class number `1`, `F` in `M_k((N))`, of even
weight, and `R` containing representatives of the cosets of `Γ₀(N)` in `GL₂(𝒪_K)`, if the means of
the functions `F ∣ r ∣ (N, 0; 0, 1)`, `r ∈ R`, over a fundamental domain `P` of `σ(𝒪_K)` vanish,
then `F` lies in `S_k((N))`. -/
lemma mem_bianchiCuspForms_of_setIntegral_eq_zero (hK : finrank ℚ K = 2) (hk : Even k)
    (hF : F ∈ bianchiModularForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k)
    {R : Set (GL (Fin 2) (𝓞 K))}
    (hR : ∀ γ : GL (Fin 2) (𝓞 K), ∃ r ∈ R, γ * r⁻¹ ∈ (Ideal.span {(N : 𝓞 K)}).gamma0GL)
    (hP : IsAddFundamentalDomain (bianchiScaledLattice σ 1) P volume)
    (h₀ : ∀ r ∈ R, ∀ y : ℝ, 0 < y →
      ∫ x in P, extend (bianchiLevelRaise σ k N (glSlash σ k r F)) (x, y) = 0) :
    F ∈ bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k := by
  have hF' : IsBianchiModularForm σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k F := hF
  refine (mem_bianchiCuspForms_iff hK (NeZero.ne _)).mpr
    ⟨⟨hF'.analyticAt, hF'.harmonic, hF'.growth, fun g ↦ ?_⟩, hF'.invariant⟩
  rcases exists_eq_map_mul_heckeUpper g with ⟨g₀, u, b, c, hc, he⟩
  rcases hR (SpecialLinearGroup.toGL g₀) with ⟨r, hr, hδ⟩
  have h₁ : bianchiSlash k (SpecialLinearGroup.map σ g) F =
      bianchiGLSlash σ k (heckeUpper u b) (glSlash σ k r F) := by
    have h₂ : glSlash σ k (SpecialLinearGroup.toGL g₀) F = glSlash σ k r F := by
      have e : SpecialLinearGroup.toGL g₀ = SpecialLinearGroup.toGL g₀ * r⁻¹ * r := by
        group
      rw [e, glSlash_mul hk, hF'.invariant.glSlash_eq hδ]
    rw [← bianchiGLSlash_eq hk (isSLRepresentative_toGL_map g),
      bianchiGLSlash_of_coe_eq_smul hk he hc, bianchiGLSlash_mul hk, ← h₂]
    rfl
  have hper : ∀ a : 𝓞 K, glSlash σ k (glUpper a) (bianchiLevelRaise σ k N (glSlash σ k r F)) =
      bianchiLevelRaise σ k N (glSlash σ k r F) :=
    glSlash_glUpper_bianchiLevelRaise_glSlash hk hF'.invariant r
  have h₃ : HasVanishingMean σ (bianchiLevelRaise σ k N (glSlash σ k r F)) 1 :=
    ⟨fun y hy l hl x ↦ extend_add_eq_of_glSlash_glUpper_eq hper hy hl x, fun y P' hy hP' ↦
      (hP'.setIntegral_eq hP fun l x ↦ extend_add_eq_of_glSlash_glUpper_eq hper hy l.2 x).trans
        (h₀ r hr y hy)⟩
  have h₄ : HasVanishingMean σ (bianchiLevelLower σ k N (bianchiLevelRaise σ k N (glSlash σ k r F)))
      (1 * (bianchiUnit N : K)) :=
    h₃.bianchiGLSlash_heckeUpper (bianchiUnit N) 0 hK one_ne_zero fun y hy ↦
      continuous_extend_mk (analyticAt_extend_bianchiLevelRaise_glSlash hF'.analyticAt r) hy
  rw [bianchiLevelLower_bianchiLevelRaise hk] at h₄
  have hN : 1 * (bianchiUnit N : K) ≠ 0 := mul_ne_zero one_ne_zero (bianchiUnit N).ne_zero
  have h₅ : HasVanishingMean σ (bianchiGLSlash σ k (heckeUpper u b) (glSlash σ k r F))
      (1 * (bianchiUnit N : K) * u) :=
    h₄.bianchiGLSlash_heckeUpper u b hK hN fun y hy ↦
      continuous_extend_mk (analyticAt_extend_bianchiSlash _ hF'.analyticAt) hy
  rw [← h₁] at h₅
  exact ⟨_, mul_ne_zero hN u.ne_zero, h₅⟩

variable (σ k N) in
/-- The linear map `F ↦ (φ_r(1), φ_r'(1))_r` on `M_k((N))`, where `φ_r` is the constant term over
`P` of `F ∣ r ∣ (N, 0; 0, 1)`, for `r ∈ GL₂(𝒪_K)`. -/
noncomputable def bianchiConstantTermMap (hPb : IsBounded P) :
    bianchiModularForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k →ₗ[ℂ] GL (Fin 2) (𝓞 K) →
      (Fin (k + 1) → ℂ) × (Fin (k + 1) → ℂ) where
  toFun Φ r := (bianchiFourierCoeff P 0 (bianchiLevelRaise σ k N (glSlash σ k r Φ)) 1,
    deriv (bianchiFourierCoeff P 0 (bianchiLevelRaise σ k N (glSlash σ k r Φ))) 1)
  map_add' Φ Ψ := by
    funext r
    have e : bianchiLevelRaise σ k N (glSlash σ k r (Φ + Ψ : bianchiModularForms σ _ k)) =
        bianchiLevelRaise σ k N (glSlash σ k r Φ) + bianchiLevelRaise σ k N (glSlash σ k r Ψ) := by
      rw [Submodule.coe_add, glSlash_add, bianchiLevelRaise_add]
    have hΦ : ∀ z : HyperbolicThreeSpace,
        AnalyticAt ℝ (extend (bianchiLevelRaise σ k N (glSlash σ k r Φ))) z.coords :=
      analyticAt_extend_bianchiLevelRaise_glSlash Φ.2.analyticAt r
    have hΨ : ∀ z : HyperbolicThreeSpace,
        AnalyticAt ℝ (extend (bianchiLevelRaise σ k N (glSlash σ k r Ψ))) z.coords :=
      analyticAt_extend_bianchiLevelRaise_glSlash Ψ.2.analyticAt r
    simp only [e]
    exact Prod.ext (bianchiFourierCoeff_zero_add hΦ hΨ hPb one_pos)
      (deriv_bianchiFourierCoeff_zero_add hΦ hΨ hPb)
  map_smul' c Φ := by
    funext r
    have e : bianchiLevelRaise σ k N (glSlash σ k r (c • Φ : bianchiModularForms σ _ k)) =
        c • bianchiLevelRaise σ k N (glSlash σ k r Φ) := by
      rw [Submodule.coe_smul, glSlash_smul, bianchiLevelRaise_smul]
    have hΦ : ∀ z : HyperbolicThreeSpace,
        AnalyticAt ℝ (extend (bianchiLevelRaise σ k N (glSlash σ k r Φ))) z.coords :=
      analyticAt_extend_bianchiLevelRaise_glSlash Φ.2.analyticAt r
    simp only [e, bianchiFourierCoeff_zero_smul]
    exact Prod.ext rfl
      (deriv_const_smul c (differentiableAt_bianchiFourierCoeff_zero hΦ hPb one_pos))

/-- **`M_k(𝔑)` is finite dimensional** (LMFDB `mf.bianchi.spaces`), for `K` imaginary quadratic of
class number `1`, `𝔑 ≠ 0` and `k ≥ 1`: the kernel of a linear map to a finite dimensional space,
given by the constant terms at finitely many cusps, consists of cusp forms, and `S_k(𝔑)` is finite
dimensional. -/
lemma finiteDimensional_bianchiModularForms (hK : finrank ℚ K = 2) (hk : k ≠ 0) {𝔑 : Ideal (𝓞 K)}
    (h𝔑 : 𝔑 ≠ ⊥) : FiniteDimensional ℂ (bianchiModularForms σ 𝔑.gamma0GL k) := by
  rcases Nat.even_or_odd k with hk' | hodd
  · rcases exists_span_eq h𝔑 with ⟨N, rfl⟩
    rcases exists_finite_gamma0GL_cosets h𝔑 with ⟨R, hR, hcos⟩
    rcases exists_isBounded_isAddFundamentalDomain_bianchiScaledLattice (σ := σ) hK
      (one_ne_zero : (1 : K) ≠ 0) with ⟨P, hPb, hP⟩
    have hfinR : Finite R := hR.to_subtype
    have hvol : volume.real P ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hP.measure_ne_zero (NeZero.ne _), hPb.measure_lt_top.ne⟩
    let T : bianchiModularForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k →ₗ[ℂ] R →
        (Fin (k + 1) → ℂ) × (Fin (k + 1) → ℂ) :=
      LinearMap.funLeft ℂ _ Subtype.val ∘ₗ bianchiConstantTermMap σ k N hPb
    have hker (Φ : bianchiModularForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k)
        (hΦ : Φ ∈ LinearMap.ker T) : (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈
          bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k := by
      refine mem_bianchiCuspForms_of_setIntegral_eq_zero hK hk' Φ.2 hcos hP fun r hr y hy ↦ ?_
      have h₁ : T Φ ⟨r, hr⟩ = 0 := congrFun (LinearMap.mem_ker.mp hΦ) ⟨r, hr⟩
      have hper : ∀ a : 𝓞 K, glSlash σ k (glUpper a) (bianchiLevelRaise σ k N (glSlash σ k r Φ)) =
          bianchiLevelRaise σ k N (glSlash σ k r Φ) :=
        glSlash_glUpper_bianchiLevelRaise_glSlash hk' Φ.2.invariant r
      have h₂ : bianchiFourierCoeff P 0 (bianchiLevelRaise σ k N (glSlash σ k r Φ)) y = 0 := by
        refine bianchiFourierCoeff_zero_eq_zero (bianchiScaledLattice σ 1)
          (analyticAt_extend_bianchiLevelRaise_glSlash Φ.2.analyticAt r)
          ((Φ.2.harmonic.bianchiSlash _).bianchiSlash _) hP hPb (fun l hl p ↦ ?_)
          (congrArg Prod.fst h₁) (congrArg Prod.snd h₁) hy
        rcases lt_or_ge 0 p.2 with hp | hp
        · exact extend_add_eq_of_glSlash_glUpper_eq hper hp hl p.1
        · have h (q : ℂ × ℝ) (hq : q.2 ≤ 0) :
              extend (bianchiLevelRaise σ k N (glSlash σ k r Φ)) q = 0 :=
            dite_eq_right (not_lt.mpr hq)
          rw [h (l + p.1, p.2) hp, h p hp]
      rw [bianchiFourierCoeff_zero_eq] at h₂
      exact (smul_eq_zero.mp h₂).resolve_left (inv_ne_zero (ofReal_ne_zero.mpr hvol))
    have hS : FiniteDimensional ℂ (bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k) :=
      finiteDimensional_bianchiCuspForms hK hk h𝔑
    have hS' : FiniteDimensional ℂ ((bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k).comap
        (bianchiModularForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k).subtype) :=
      LinearEquiv.finiteDimensional
        (Submodule.comapSubtypeEquivOfLe (bianchiCuspForms_le σ _ k)).symm
    have hT : FiniteDimensional ℂ (LinearMap.ker T) :=
      Submodule.finiteDimensional_of_le (S₂ := (bianchiCuspForms σ _ k).comap
        (bianchiModularForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k).subtype) hker
    have hq : FiniteDimensional ℂ
        (bianchiModularForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k ⧸ LinearMap.ker T) :=
      LinearEquiv.finiteDimensional T.quotKerEquivRange.symm
    exact Finite.of_submodule_quotient (LinearMap.ker T)
  · have : Subsingleton (bianchiModularForms σ 𝔑.gamma0GL k) :=
      ⟨fun Φ Ψ ↦ Subtype.ext <| by
        rw [Φ.2.invariant.eq_zero_of_odd hodd, Ψ.2.invariant.eq_zero_of_odd hodd]⟩
    infer_instance

end HyperbolicThreeSpace
