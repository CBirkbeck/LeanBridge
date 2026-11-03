import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.PointPairKernel
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.ProductFundamentalDomain

/-!
# The eigenvalues of square-integrable Maass forms are real

Every nonzero element of `M(N, χ, λ)` (`UpperHalfPlane.maassSpace`) has a real eigenvalue `λ`, with
no cuspidality or decay hypothesis (LMFDB `mf.maass.exceptional_eigenvalue`: "Each eigenvalue is
real"). The proof uses Selberg's point-pair invariants `k(z, w) = φ(cosh d(z, w))`, with `φ` real,
smooth and vanishing on `[C, ∞)`, and avoids any boundary term at the cusps, since Green's identity
is only applied on `ℍ` to the compactly supported function `w ↦ k(z, w)`.

For `F` in `M(N, χ, a)` and `G` in `M(N, χ, b)`, write
`B(φ; F, G) = ∫_{Γ₀(N) \ ℍ} ∫_ℍ φ(cosh d(z, w)) F(w) conj(G(z)) dμ(w) dμ(z)`
(`UpperHalfPlane.kernelPair`).

* `conj B(φ; F, G) = B(φ; G, F)`: the kernel is real and symmetric, and
  `Ψ(z, w) = k(z, w) G(w) conj(F(z))` is invariant under the diagonal action of `Γ₀(N)`, of which
  `D × ℍ` and `ℍ × D` are fundamental domains
  (`MeasureTheory.IsFundamentalDomain.integral_prod_swap_eq`).
* `B(radialLaplacian φ; F, G) = -a B(φ; F, G)`, by Green's identity in `w`.
* So if `a ≠ conj b`, `B(φ; F, G) = 0` for every `φ`.
* For `φ` of mass `M`, `∫∫ φ(cosh d(z, w)) |G(z) + F(w)|² = M (‖G‖² + ‖F‖²) + 2 Re B(φ; F, G)`. When
  `M = 1` and the support of `φ` shrinks to the point `c = 1`, the inner integral tends to
  `|G(z) + F(z)|²`, so that Fatou's lemma gives `‖G + F‖² ≤ liminf (‖G‖² + ‖F‖² + 2 Re B(φ; F, G))`.
* For `F = G` with a non-real eigenvalue this reads `4 ‖F‖² ≤ 2 ‖F‖²`, and `F = 0`.

## Main definitions

* `UpperHalfPlane.gammaZeroPairMeasure`: the measure on `(Γ₀(N) \ ℍ) × ℍ`.
* `UpperHalfPlane.kernelPair`: the pairing `B(φ; F, G)`.
* `UpperHalfPlane.coshDistBump`, `UpperHalfPlane.coshDistNormalBump`: the kernels whose support
  shrinks to the diagonal.

## Main results

* `UpperHalfPlane.integral_kernel_eq`: the mass of a radial kernel does not depend on the centre.
* `UpperHalfPlane.conj_kernelPair`: `conj B(φ; F, G) = B(φ; G, F)`.
* `UpperHalfPlane.kernelPair_radialLaplacian`: `B(radialLaplacian φ; F, G) = -a B(φ; F, G)`.
* `UpperHalfPlane.kernelPair_eq_zero`: `B(φ; F, G) = 0` if `a ≠ conj b`.
* `UpperHalfPlane.integral_kernel_mul_norm_add_sq`: the identity for `|G(z) + F(w)|²`.
* `UpperHalfPlane.ofReal_integral_le_liminf`: Fatou's lemma for the kernels `coshDistNormalBump n`.
* `UpperHalfPlane.conj_eigenvalue_of_mem_maassSpace`: the eigenvalue is real.
-/

open MeasureTheory Filter CongruenceSubgroup Matrix Real Topology

open scoped ComplexConjugate ContDiff MatrixGroups

namespace UpperHalfPlane

variable (z : ℍ) {N : ℕ} {χ : DirichletCharacter ℂ N} {eigenvalue a b : ℂ} {φ : ℝ → ℝ} {F G : ℍ → ℂ}
  {H : ℍ → ℝ} {C δ m : ℝ} {n : ℕ} {s : ℕ → ℕ}

variable (N) in
/-- The product of the invariant measure on `gammaZeroDomain N` and the invariant measure on `ℍ`:
the integrals over it are those over `Γ₀(N) \ (ℍ × ℍ)` for the diagonal action. -/
noncomputable abbrev gammaZeroPairMeasure : Measure (ℍ × ℍ) :=
  (volume.restrict (gammaZeroDomain N)).prod volume

lemma dist_sl_smul (σ : SL(2, ℤ)) (w : ℍ) : dist (σ • z) (σ • w) = dist z w :=
  dist_smul (SpecialLinearGroup.map (Int.castRingHom ℝ) σ) z w

lemma dist_smul_smul_of_mem_gamma0
    (g : (Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) (w : ℍ) :
    dist (g • z) (g • w) = dist z w := by
  rcases g.2 with ⟨γ, -, hg⟩
  rw [Subgroup.smul_def, Subgroup.smul_def, ← hg, QuotientGroup.mk'_apply, pslMk_smul, pslMk_smul]
  exact dist_sl_smul z γ w

lemma continuous_kernel (hφ : Continuous φ) : Continuous fun p : ℍ × ℍ ↦ φ (dist p.1 p.2).cosh :=
  hφ.comp (Real.continuous_cosh.comp continuous_dist)

lemma hasCompactSupport_kernel (hφ0 : ∀ c, C ≤ c → φ c = 0) :
    HasCompactSupport fun w ↦ φ (dist z w).cosh :=
  HasCompactSupport.intro (isCompact_closedBall z (2 * |C|)) fun _ hw ↦
    comp_cosh_dist_eq_zero z hφ0 hw

lemma continuous_kernel_right (hφ : Continuous φ) : Continuous fun w ↦ φ (dist z w).cosh :=
  hφ.comp (Real.continuous_cosh.comp (continuous_const.dist continuous_id))

lemma integrable_kernel (hφ : Continuous φ) (hφ0 : ∀ c, C ≤ c → φ c = 0) :
    Integrable fun w ↦ φ (dist z w).cosh :=
  (continuous_kernel_right z hφ).integrable_of_hasCompactSupport (hasCompactSupport_kernel z hφ0)

/-- **The mass of a radial kernel does not depend on the centre**, the group `SL(2, ℝ)` acting
transitively on `ℍ` by isometries that preserve the invariant measure. -/
lemma integral_kernel_eq (z' : ℍ) : ∫ w, φ (dist z w).cosh = ∫ w, φ (dist z' w).cosh := by
  rcases MulAction.exists_smul_eq SL(2, ℝ) z' z with ⟨g, rfl⟩
  rw [← (measurePreserving_smul g volume).integral_comp (measurableEmbedding_const_smul g)]
  simp only [dist_smul]

lemma norm_smul_eq_of_mem_maassSpace (hF : F ∈ maassSpace N χ eigenvalue)
    (g : (Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) : ‖F (g • z)‖ = ‖F z‖ := by
  have h : ‖(F ∘ ofComplex) ↑(g • z)‖ ^ 2 = ‖(F ∘ ofComplex) z‖ ^ 2 :=
    norm_sq_smul_eq hF.2.2.1 g z
  simp only [Function.comp_apply, ofComplex_apply] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

lemma integrable_kernel_mul_norm_sq_fst (hF : F ∈ maassSpace N χ eigenvalue) (hφ : Continuous φ)
    (hφ0 : ∀ c, C ≤ c → φ c = 0) :
    Integrable (fun p : ℍ × ℍ ↦ φ (dist p.1 p.2).cosh * ‖F p.1‖ ^ 2) (gammaZeroPairMeasure N) := by
  have hFc : Continuous F := continuous_of_mem_maassSpace hF
  have hm : Continuous fun p : ℍ × ℍ ↦ φ (dist p.1 p.2).cosh * ‖F p.1‖ ^ 2 :=
    (continuous_kernel hφ).mul ((hFc.comp continuous_fst).norm.pow 2)
  have hz (z : ℍ) : Integrable fun w ↦ φ (dist z w).cosh * ‖F z‖ ^ 2 :=
    (integrable_kernel z hφ hφ0).mul_const _
  refine (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨.of_forall hz, ?_⟩
  have h1 (z : ℍ) :
      ∫ w, ‖φ (dist z w).cosh * ‖F z‖ ^ 2‖ = (∫ w, |φ (dist I w).cosh|) * ‖F z‖ ^ 2 := by
    simp only [norm_mul, Real.norm_eq_abs, norm_pow, abs_norm]
    rw [integral_mul_const]
    congr 1
    exact integral_kernel_eq (φ := fun c ↦ |φ c|) z I
  simp only [h1]
  exact (integrableOn_norm_sq_of_mem_maassSpace hF).const_mul _

lemma integrable_kernel_mul_norm_sq_snd (hF : F ∈ maassSpace N χ eigenvalue) (hφ : Continuous φ)
    (hφ0 : ∀ c, C ≤ c → φ c = 0) :
    Integrable (fun p : ℍ × ℍ ↦ φ (dist p.1 p.2).cosh * ‖F p.2‖ ^ 2) (gammaZeroPairMeasure N) := by
  have hFc : Continuous F := continuous_of_mem_maassSpace hF
  have h1 :
      Integrable (fun p : ℍ × ℍ ↦ φ (dist p.1 p.2).cosh * ‖F p.1‖ ^ 2) (gammaZeroPairMeasure N) :=
    integrable_kernel_mul_norm_sq_fst hF hφ hφ0
  have hm : Continuous fun p : ℍ × ℍ ↦ φ (dist p.1 p.2).cosh * ‖F p.2‖ ^ 2 :=
    (continuous_kernel hφ).mul ((hFc.comp continuous_snd).norm.pow 2)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have h2 : ∫⁻ p, ‖φ (dist p.1 p.2).cosh * ‖F p.1‖ ^ 2‖ₑ ∂gammaZeroPairMeasure N =
      ∫⁻ p, ‖φ (dist p.swap.1 p.swap.2).cosh * ‖F p.swap.1‖ ^ 2‖ₑ ∂gammaZeroPairMeasure N :=
    (isFundamentalDomain_gammaZeroDomain N).lintegral_prod_swap_eq
      (Ψ := fun p : ℍ × ℍ ↦ ‖φ (dist p.1 p.2).cosh * ‖F p.1‖ ^ 2‖ₑ) fun g p ↦ by
        simp only [Prod.smul_fst, Prod.smul_snd, dist_smul_smul_of_mem_gamma0,
          norm_smul_eq_of_mem_maassSpace _ hF]
  have h3 (p : ℍ × ℍ) : ‖φ (dist p.1 p.2).cosh * ‖F p.2‖ ^ 2‖ₑ =
      ‖φ (dist p.swap.1 p.swap.2).cosh * ‖F p.swap.1‖ ^ 2‖ₑ := by
    rw [Prod.fst_swap, Prod.snd_swap, dist_comm]
  simp only [h3]
  rw [← h2]
  exact hasFiniteIntegral_iff_enorm.mp h1.2

lemma continuous_kernel_mul (hF : F ∈ maassSpace N χ a) (hG : G ∈ maassSpace N χ b)
    (hφ : Continuous φ) :
    Continuous fun p : ℍ × ℍ ↦ (φ (dist p.1 p.2).cosh : ℂ) * (F p.2 * conj (G p.1)) :=
  (Complex.continuous_ofReal.comp (continuous_kernel hφ)).mul
    (((continuous_of_mem_maassSpace hF).comp continuous_snd).mul
      (Complex.continuous_conj.comp ((continuous_of_mem_maassSpace hG).comp continuous_fst)))

lemma integrable_kernel_mul (hF : F ∈ maassSpace N χ a) (hG : G ∈ maassSpace N χ b)
    (hφ : Continuous φ) (hφ0 : ∀ c, C ≤ c → φ c = 0) : Integrable
      (fun p : ℍ × ℍ ↦ (φ (dist p.1 p.2).cosh : ℂ) * (F p.2 * conj (G p.1)))
      (gammaZeroPairMeasure N) := by
  have hφa : Continuous fun c ↦ |φ c| := hφ.abs
  have hφa0 : ∀ c, C ≤ c → |φ c| = 0 := fun c hc ↦ by
    rw [hφ0 c hc, abs_zero]
  refine ((integrable_kernel_mul_norm_sq_fst hG hφa hφa0).add
    (integrable_kernel_mul_norm_sq_snd hF hφa hφa0)).mono'
    (continuous_kernel_mul hF hG hφ).aestronglyMeasurable (.of_forall fun p ↦ ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj, Pi.add_apply]
  have h : 2 * ‖G p.1‖ * ‖F p.2‖ ≤ ‖G p.1‖ ^ 2 + ‖F p.2‖ ^ 2 := two_mul_le_add_sq _ _
  have h0 : 0 ≤ ‖G p.1‖ := norm_nonneg _
  have h1 : 0 ≤ ‖F p.2‖ := norm_nonneg _
  have h2 : 0 ≤ |φ (dist p.1 p.2).cosh| := abs_nonneg _
  nlinarith [mul_nonneg h2 (add_nonneg (sq_nonneg ‖G p.1‖) (sq_nonneg ‖F p.2‖)),
    mul_nonneg h2 (mul_nonneg h0 h1)]

variable (N φ F G) in
/-- The pairing `∫_{Γ₀(N) \ ℍ} ∫_ℍ φ(cosh d(z, w)) F(w) conj(G(z)) dμ(w) dμ(z)` of `F` and `G`
through the radial kernel `φ`, the point-pair invariant `φ(cosh d(z, w))`. -/
noncomputable def kernelPair : ℂ :=
  ∫ p : ℍ × ℍ, (φ (dist p.1 p.2).cosh : ℂ) * (F p.2 * conj (G p.1)) ∂gammaZeroPairMeasure N

/-- **The pairing with a real point-pair invariant is Hermitian**: `conj B(φ; F, G) = B(φ; G, F)`,
the kernel `φ(cosh d(z, w))` being real, symmetric and invariant under the diagonal action of
`Γ₀(N)`. -/
lemma conj_kernelPair (hF : F ∈ maassSpace N χ a) (hG : G ∈ maassSpace N χ b) :
    conj (kernelPair N φ F G) = kernelPair N φ G F := by
  have h : kernelPair N φ G F =
      ∫ p : ℍ × ℍ, (φ (dist p.swap.1 p.swap.2).cosh : ℂ) * (G p.swap.2 * conj (F p.swap.1))
        ∂gammaZeroPairMeasure N :=
    (isFundamentalDomain_gammaZeroDomain N).integral_prod_swap_eq
      (Ψ := fun p : ℍ × ℍ ↦ (φ (dist p.1 p.2).cosh : ℂ) * (G p.2 * conj (F p.1)))
      fun g p ↦ by
        have hc : G (g • p.2) * conj (F (g • p.1)) = G p.2 * conj (F p.1) := by
          rcases g.2 with ⟨γ, hγ, hg⟩
          have hu : χ (γ 1 1 : ℤ) * conj (χ (γ 1 1 : ℤ)) = 1 := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
              norm_dirichletCharacter_of_mem_gamma0 χ hγ]
            norm_num
          rw [Subgroup.smul_def, Subgroup.smul_def, ← hg, QuotientGroup.mk'_apply, pslMk_smul,
            pslMk_smul, smul_eq_of_mem_maassSpace hG hγ, smul_eq_of_mem_maassSpace hF hγ, map_mul]
          linear_combination G p.2 * conj (F p.1) * hu
        simp only [Prod.smul_fst, Prod.smul_snd, dist_smul_smul_of_mem_gamma0, hc]
  rw [kernelPair, ← integral_conj, h]
  refine integral_congr_ae (.of_forall fun p ↦ ?_)
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj, Prod.fst_swap, Prod.snd_swap]
  rw [dist_comm]
  ring1

lemma continuous_radialLaplacian (hφ : ContDiff ℝ ∞ φ) : Continuous (radialLaplacian φ) := by
  have h1 : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv φ)) := (contDiff_infty_iff_deriv.mp h1).2
  unfold radialLaplacian
  exact (((continuous_id.pow 2).sub continuous_const).mul h2.continuous).add
    ((continuous_const.mul continuous_id).mul h1.continuous)

lemma radialLaplacian_eq_zero (hφ0 : ∀ c, C ≤ c → φ c = 0) {c : ℝ} (hc : C + 1 ≤ c) :
    radialLaplacian φ c = 0 := by
  have hCc : C < c := by
    linarith
  have h1 {x : ℝ} (hx : C < x) : deriv φ x = 0 := by
    have h : φ =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact hφ0 y (le_of_lt hy)
    rw [h.deriv_eq, deriv_const]
  have h2 : deriv (deriv φ) c = 0 := by
    have h : deriv φ =ᶠ[𝓝 c] fun _ ↦ 0 := by
      filter_upwards [Ioi_mem_nhds hCc] with y hy
      exact h1 hy
    rw [h.deriv_eq, deriv_const]
  rw [radialLaplacian, h2, h1 hCc, mul_zero, mul_zero, add_zero]

/-- **The pairing with the radial Laplacian of a kernel**: for `F` in `M(N, χ, a)` and `φ` smooth
vanishing on `[C, ∞)`, `B(radialLaplacian φ; F, G) = -a B(φ; F, G)`, by Green's identity on `ℍ` in
the variable `w`. -/
lemma kernelPair_radialLaplacian (hF : F ∈ maassSpace N χ a) (hG : G ∈ maassSpace N χ b)
    (hφ : ContDiff ℝ ∞ φ) (hφ0 : ∀ c, C ≤ c → φ c = 0) :
    kernelPair N (radialLaplacian φ) F G = -a * kernelPair N φ F G := by
  have hφ1 : ∀ c, C + 1 ≤ c → radialLaplacian φ c = 0 := fun _ hc ↦ radialLaplacian_eq_zero hφ0 hc
  rw [kernelPair, kernelPair, integral_prod _ (integrable_kernel_mul hF hG
    (continuous_radialLaplacian hφ) hφ1), integral_prod _ (integrable_kernel_mul hF hG hφ.continuous
    hφ0), ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  dsimp only
  have h1 : ∫ w : ℍ, (radialLaplacian φ (dist z w).cosh : ℂ) * F w =
      -a * ∫ w : ℍ, (φ (dist z w).cosh : ℂ) * F w := by
    have h : ∫ w : ℍ, (φ (dist z w).cosh : ℂ) * hyperbolicLaplacian (F ∘ ofComplex) w =
        ∫ w : ℍ, (radialLaplacian φ (dist z w).cosh : ℂ) * (F ∘ ofComplex) w :=
      integral_kernel_mul_hyperbolicLaplacian z hφ hφ0 hF.1
    simp only [Function.comp_apply, ofComplex_apply] at h
    rw [← h, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun w ↦ ?_)
    have h2 : hyperbolicLaplacian (F ∘ ofComplex) w + a * (F ∘ ofComplex) w = 0 :=
      hF.2.2.2 w w.im_pos
    simp only [Function.comp_apply, ofComplex_apply] at h2
    dsimp only
    linear_combination (φ (dist z w).cosh : ℂ) * h2
  simp only [← mul_assoc]
  rw [integral_mul_const, integral_mul_const, h1]
  ring1

/-- **If the eigenvalues differ, all the pairings vanish**: for `a ≠ conj b`, `B(φ; F, G) = 0` for
every smooth kernel `φ` vanishing on `[C, ∞)`, the operator with kernel `radialLaplacian φ`
acting on `F` by `-a` and on `G` by `-b`. -/
lemma kernelPair_eq_zero (hF : F ∈ maassSpace N χ a) (hG : G ∈ maassSpace N χ b)
    (hφ : ContDiff ℝ ∞ φ) (hφ0 : ∀ c, C ≤ c → φ c = 0) (hab : a ≠ conj b) :
    kernelPair N φ F G = 0 := by
  have h1 : kernelPair N (radialLaplacian φ) F G = -a * kernelPair N φ F G :=
    kernelPair_radialLaplacian hF hG hφ hφ0
  have h2 : kernelPair N (radialLaplacian φ) G F = -b * kernelPair N φ G F :=
    kernelPair_radialLaplacian hG hF hφ hφ0
  have h3 : conj (kernelPair N (radialLaplacian φ) G F) = conj (-b * kernelPair N φ G F) :=
    congrArg conj h2
  rw [conj_kernelPair hG hF, map_mul, map_neg, conj_kernelPair hG hF, h1] at h3
  have h4 : (a - conj b) * kernelPair N φ F G = 0 := by
    linear_combination -h3
  exact (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hab)

lemma integral_kernel_mul_norm_sq_fst (hF : F ∈ maassSpace N χ eigenvalue) (hφ : Continuous φ)
    (hφ0 : ∀ c, C ≤ c → φ c = 0) : ∫ p : ℍ × ℍ, φ (dist p.1 p.2).cosh * ‖F p.1‖ ^ 2
      ∂gammaZeroPairMeasure N = (∫ w, φ (dist I w).cosh) * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := by
  rw [integral_prod _ (integrable_kernel_mul_norm_sq_fst hF hφ hφ0), ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  dsimp only
  rw [integral_mul_const, integral_kernel_eq z I]

lemma integral_kernel_mul_norm_sq_snd (hF : F ∈ maassSpace N χ eigenvalue) (hφ : Continuous φ)
    (hφ0 : ∀ c, C ≤ c → φ c = 0) : ∫ p : ℍ × ℍ, φ (dist p.1 p.2).cosh * ‖F p.2‖ ^ 2
      ∂gammaZeroPairMeasure N = (∫ w, φ (dist I w).cosh) * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := by
  rw [← integral_kernel_mul_norm_sq_fst hF hφ hφ0,
    (isFundamentalDomain_gammaZeroDomain N).integral_prod_swap_eq
    (Ψ := fun p : ℍ × ℍ ↦ φ (dist p.1 p.2).cosh * ‖F p.1‖ ^ 2) fun g p ↦ by
      simp only [Prod.smul_fst, Prod.smul_snd, dist_smul_smul_of_mem_gamma0,
        norm_smul_eq_of_mem_maassSpace _ hF]]
  refine integral_congr_ae (.of_forall fun p ↦ ?_)
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [dist_comm]

lemma mul_norm_add_sq_eq (t : ℝ) (x y : ℂ) :
    t * ‖x + y‖ ^ 2 = t * ‖x‖ ^ 2 + t * ‖y‖ ^ 2 + 2 * Complex.reCLM ((t : ℂ) * (y * conj x)) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.reCLM_apply, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.add_re,
    Complex.add_im]
  ring1

lemma integrable_kernel_mul_norm_add_sq (hF : F ∈ maassSpace N χ a) (hG : G ∈ maassSpace N χ b)
    (hφ : Continuous φ) (hφ0 : ∀ c, C ≤ c → φ c = 0) : Integrable
      (fun p : ℍ × ℍ ↦ φ (dist p.1 p.2).cosh * ‖G p.1 + F p.2‖ ^ 2) (gammaZeroPairMeasure N) := by
  simp only [mul_norm_add_sq_eq]
  exact ((integrable_kernel_mul_norm_sq_fst hG hφ hφ0).add
    (integrable_kernel_mul_norm_sq_snd hF hφ hφ0)).add
    ((Complex.reCLM.integrable_comp (integrable_kernel_mul hF hG hφ hφ0)).const_mul 2)

/-- **The identity for a pair of points**: for `φ` continuous vanishing on `[C, ∞)`, of mass `M`,
`∫∫ φ(cosh d(z, w)) |G(z) + F(w)|² dμ(w) dμ(z) = M (‖G‖² + ‖F‖²) + 2 Re B(φ; F, G)`, the pairing
being the cross term. -/
lemma integral_kernel_mul_norm_add_sq (hF : F ∈ maassSpace N χ a) (hG : G ∈ maassSpace N χ b)
    (hφ : Continuous φ) (hφ0 : ∀ c, C ≤ c → φ c = 0) : ∫ p : ℍ × ℍ,
      φ (dist p.1 p.2).cosh * ‖G p.1 + F p.2‖ ^ 2 ∂gammaZeroPairMeasure N =
        (∫ w, φ (dist I w).cosh) *
            ((∫ z in gammaZeroDomain N, ‖G z‖ ^ 2) + ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) +
          2 * (kernelPair N φ F G).re := by
  have hint : Integrable
      (fun p : ℍ × ℍ ↦ (φ (dist p.1 p.2).cosh : ℂ) * (F p.2 * conj (G p.1)))
      (gammaZeroPairMeasure N) := integrable_kernel_mul hF hG hφ hφ0
  have h12 : Integrable (fun p : ℍ × ℍ ↦ φ (dist p.1 p.2).cosh * ‖G p.1‖ ^ 2 +
      φ (dist p.1 p.2).cosh * ‖F p.2‖ ^ 2) (gammaZeroPairMeasure N) :=
    (integrable_kernel_mul_norm_sq_fst hG hφ hφ0).add (integrable_kernel_mul_norm_sq_snd hF hφ hφ0)
  simp only [mul_norm_add_sq_eq]
  rw [integral_add h12 ((Complex.reCLM.integrable_comp hint).const_mul 2),
    integral_add (integrable_kernel_mul_norm_sq_fst hG hφ hφ0)
    (integrable_kernel_mul_norm_sq_snd hF hφ hφ0), integral_const_mul,
    integral_kernel_mul_norm_sq_fst hG hφ hφ0, integral_kernel_mul_norm_sq_snd hF hφ hφ0,
    Complex.reCLM.integral_comp_comm hint, mul_add]
  rfl

lemma lintegral_kernel_mul_norm_add_sq (hF : F ∈ maassSpace N χ a) (hG : G ∈ maassSpace N χ b)
    (hφ : Continuous φ) (hφ0 : ∀ c, C ≤ c → φ c = 0) (hnn : ∀ c, 0 ≤ φ c)
    (hmass : ∫ w, φ (dist I w).cosh = 1) :
    ∫⁻ z in gammaZeroDomain N, ∫⁻ w, ENNReal.ofReal (φ (dist z w).cosh * ‖G z + F w‖ ^ 2) =
      ENNReal.ofReal ((∫ z in gammaZeroDomain N, ‖G z‖ ^ 2) +
        (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) + 2 * (kernelPair N φ F G).re) := by
  have hFc : Continuous F := continuous_of_mem_maassSpace hF
  have hGc : Continuous G := continuous_of_mem_maassSpace hG
  have hc : Continuous fun p : ℍ × ℍ ↦ φ (dist p.1 p.2).cosh * ‖G p.1 + F p.2‖ ^ 2 :=
    (continuous_kernel hφ).mul
      (((hGc.comp continuous_fst).add (hFc.comp continuous_snd)).norm.pow 2)
  have hm : AEMeasurable (fun p : ℍ × ℍ ↦
      ENNReal.ofReal (φ (dist p.1 p.2).cosh * ‖G p.1 + F p.2‖ ^ 2))
      (gammaZeroPairMeasure N) :=
    (ENNReal.measurable_ofReal.comp hc.measurable).aemeasurable
  have h : ∫ p : ℍ × ℍ, φ (dist p.1 p.2).cosh * ‖G p.1 + F p.2‖ ^ 2
      ∂gammaZeroPairMeasure N = (∫ w, φ (dist I w).cosh) *
        ((∫ z in gammaZeroDomain N, ‖G z‖ ^ 2) + ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) +
          2 * (kernelPair N φ F G).re :=
    integral_kernel_mul_norm_add_sq hF hG hφ hφ0
  rw [hmass, one_mul] at h
  rw [← h, ofReal_integral_eq_lintegral_ofReal (integrable_kernel_mul_norm_add_sq hF hG hφ hφ0)
    (.of_forall fun p ↦ mul_nonneg (hnn _) (sq_nonneg _))]
  exact (lintegral_prod _ hm).symm

lemma ofReal_le_lintegral_kernel_mul (hφ : Continuous φ) (hφ0 : ∀ c, C ≤ c → φ c = 0)
    (hnn : ∀ c, 0 ≤ φ c) (hmass : ∫ w, φ (dist z w).cosh = 1)
    (hm : ∀ w : ℍ, φ (dist z w).cosh ≠ 0 → m ≤ H w) :
    ENNReal.ofReal m ≤ ∫⁻ w : ℍ, ENNReal.ofReal (φ (dist z w).cosh * H w) := by
  have hnn' : 0 ≤ᵐ[(volume : Measure ℍ)] fun w : ℍ ↦ φ (dist z w).cosh :=
    .of_forall fun w ↦ hnn _
  have h1 : ∫⁻ w : ℍ, ENNReal.ofReal (φ (dist z w).cosh) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_kernel z hφ hφ0) hnn', hmass,
      ENNReal.ofReal_one]
  have hme : Measurable fun w : ℍ ↦ ENNReal.ofReal (φ (dist z w).cosh) :=
    ENNReal.measurable_ofReal.comp (continuous_kernel_right z hφ).measurable
  have h2 : ∫⁻ w : ℍ, ENNReal.ofReal (φ (dist z w).cosh) * ENNReal.ofReal m = ENNReal.ofReal m := by
    rw [lintegral_mul_const _ hme, h1, one_mul]
  refine h2.symm.le.trans <| lintegral_mono fun w ↦ ?_
  dsimp only
  rw [← ENNReal.ofReal_mul (hnn _)]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases h0 : φ (dist z w).cosh = 0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_left (hm w h0) (hnn _)

variable (n) in
/-- The smooth bump `c ↦ smoothTransition(2 - (n + 1)(c - 1))`, equal to `1` for
`c ≤ 1 + 1/(n + 1)` and to `0` for `c ≥ 1 + 2/(n + 1)`. -/
noncomputable def coshDistBump (c : ℝ) : ℝ :=
  smoothTransition (2 - (n + 1) * (c - 1))

variable (n) in
/-- The bump `coshDistBump n` normalised to have mass `1` as a kernel on `ℍ`. -/
noncomputable def coshDistNormalBump (c : ℝ) : ℝ :=
  (∫ w, coshDistBump n (dist I w).cosh)⁻¹ * coshDistBump n c

lemma contDiff_coshDistBump : ContDiff ℝ ∞ (coshDistBump n) :=
  smoothTransition.contDiff.comp (by fun_prop)

lemma coshDistBump_eq_zero {c : ℝ} (hc : 3 ≤ c) : coshDistBump n c = 0 := by
  refine smoothTransition.zero_of_nonpos ?_
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

lemma coshDistBump_nonneg (c : ℝ) : 0 ≤ coshDistBump n c :=
  smoothTransition.nonneg _

lemma integral_coshDistBump_pos : 0 < ∫ w, coshDistBump n (dist I w).cosh := by
  refine (continuous_kernel_right I
    contDiff_coshDistBump.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := I)
    (hasCompactSupport_kernel I fun _ hc ↦ coshDistBump_eq_zero hc)
    (fun w ↦ coshDistBump_nonneg _) ?_
  have h : coshDistBump n 1 = 1 := smoothTransition.one_of_one_le (by norm_num)
  simp [h]

lemma contDiff_coshDistNormalBump : ContDiff ℝ ∞ (coshDistNormalBump n) :=
  contDiff_const.mul contDiff_coshDistBump

lemma coshDistNormalBump_eq_zero {c : ℝ} (hc : 3 ≤ c) : coshDistNormalBump n c = 0 := by
  rw [coshDistNormalBump, coshDistBump_eq_zero hc, mul_zero]

lemma coshDistNormalBump_nonneg (c : ℝ) : 0 ≤ coshDistNormalBump n c :=
  mul_nonneg (inv_nonneg.mpr integral_coshDistBump_pos.le) (coshDistBump_nonneg c)

lemma integral_coshDistNormalBump : ∫ w, coshDistNormalBump n (dist z w).cosh = 1 := by
  simp only [coshDistNormalBump]
  rw [integral_const_mul, integral_kernel_eq z I]
  exact inv_mul_cancel₀ integral_coshDistBump_pos.ne'

lemma eventually_coshDistNormalBump_eq_zero (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℝ, δ ≤ d → coshDistNormalBump n d.cosh = 0 := by
  have hcosh : 0 < δ.cosh - 1 := sub_pos.mpr (Real.one_lt_cosh.mpr hδ.ne')
  rcases exists_nat_gt (2 / (δ.cosh - 1)) with ⟨k, hk⟩
  filter_upwards [eventually_ge_atTop k] with n hn d hd
  have h1 : δ.cosh ≤ d.cosh := Real.cosh_le_cosh.mpr <| by
    rw [abs_of_pos hδ, abs_of_pos (hδ.trans_le hd)]
    exact hd
  have h2 : 2 ≤ ((n : ℝ) + 1) * (d.cosh - 1) := by
    have h3 : 2 / (δ.cosh - 1) < (n : ℝ) + 1 := by
      have h4 : (k : ℝ) ≤ n := Nat.cast_le.mpr hn
      linarith
    have h5 : 2 < ((n : ℝ) + 1) * (δ.cosh - 1) := (div_lt_iff₀ hcosh).mp h3
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  rw [coshDistNormalBump, coshDistBump, smoothTransition.zero_of_nonpos (by linarith), mul_zero]

lemma ofReal_le_liminf_lintegral_kernel (hs : Tendsto s atTop atTop) (hH : Continuous H) :
    ENNReal.ofReal (H z) ≤ liminf (fun j : ℕ ↦ ∫⁻ w : ℍ, ENNReal.ofReal
      (coshDistNormalBump (s j) (dist z w).cosh * H w)) atTop := by
  have hle {ε : ℝ} (hε : 0 < ε) : ENNReal.ofReal (H z - ε) ≤ liminf (fun j : ℕ ↦ ∫⁻ w : ℍ,
      ENNReal.ofReal (coshDistNormalBump (s j) (dist z w).cosh * H w)) atTop := by
    have hev : ∀ᶠ w in 𝓝 z, H z - ε < H w :=
      hH.continuousAt.eventually_const_lt (by linarith)
    rcases Metric.eventually_nhds_iff.mp hev with ⟨δ, hδ, hball⟩
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hs.eventually (eventually_coshDistNormalBump_eq_zero hδ)] with j hj
    refine ofReal_le_lintegral_kernel_mul z contDiff_coshDistNormalBump.continuous
      (fun _ hc ↦ coshDistNormalBump_eq_zero hc) coshDistNormalBump_nonneg
      (integral_coshDistNormalBump z) fun w hw ↦ le_of_lt (hball ?_)
    by_contra hd
    exact hw (hj _ (not_lt.mp hd |>.trans_eq (dist_comm w z)))
  have ht : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (H z - ε)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (H z))) := by
    have hc : Continuous fun ε : ℝ ↦ ENNReal.ofReal (H z - ε) :=
      ENNReal.continuous_ofReal.comp (continuous_const.sub continuous_id)
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ht (eventually_mem_nhdsWithin.mono fun ε hε ↦ hle hε)

/-- **Fatou's lemma for the kernels shrinking to the diagonal**: for `F` in `M(N, χ, a)`, `G` in
`M(N, χ, b)` and a sequence `s_j` going to infinity,
`‖G + F‖² ≤ liminf (‖G‖² + ‖F‖² + 2 Re B(P_{s_j}; F, G))`, written with `ENNReal.ofReal`, for the
kernels `P_n = coshDistNormalBump n`. -/
lemma ofReal_integral_le_liminf (hF : F ∈ maassSpace N χ a) (hG : G ∈ maassSpace N χ b)
    (hs : Tendsto s atTop atTop) : ENNReal.ofReal (∫ z in gammaZeroDomain N, ‖G z + F z‖ ^ 2) ≤
      liminf (fun j : ℕ ↦ ENNReal.ofReal ((∫ z in gammaZeroDomain N, ‖G z‖ ^ 2) +
        (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) +
          2 * (kernelPair N (coshDistNormalBump (s j)) F G).re)) atTop := by
  have hFc : Continuous F := continuous_of_mem_maassSpace hF
  have hGc : Continuous G := continuous_of_mem_maassSpace hG
  have hL2 : IntegrableOn (fun z ↦ ‖G z + F z‖ ^ 2) (gammaZeroDomain N) :=
    (memLp_two_iff_integrable_sq_norm (hGc.add hFc).aestronglyMeasurable).mp <|
      (memLp_of_mem_maassSpace hG).add (memLp_of_mem_maassSpace hF)
  have hmeas (j : ℕ) : Measurable fun z : ℍ ↦ ∫⁻ w : ℍ,
      ENNReal.ofReal (coshDistNormalBump (s j) (dist z w).cosh * ‖G z + F w‖ ^ 2) := by
    have hc : Continuous fun p : ℍ × ℍ ↦
        coshDistNormalBump (s j) (dist p.1 p.2).cosh * ‖G p.1 + F p.2‖ ^ 2 :=
      (continuous_kernel contDiff_coshDistNormalBump.continuous).mul
        (((hGc.comp continuous_fst).add (hFc.comp continuous_snd)).norm.pow 2)
    exact Measurable.lintegral_prod_right' (ENNReal.measurable_ofReal.comp hc.measurable)
  have hlow (z : ℍ) : ENNReal.ofReal (‖G z + F z‖ ^ 2) ≤ liminf (fun j : ℕ ↦ ∫⁻ w : ℍ,
      ENNReal.ofReal (coshDistNormalBump (s j) (dist z w).cosh * ‖G z + F w‖ ^ 2)) atTop :=
    ofReal_le_liminf_lintegral_kernel z hs (H := fun w ↦ ‖G z + F w‖ ^ 2)
      ((continuous_const.add hFc).norm.pow 2)
  rw [ofReal_integral_eq_lintegral_ofReal hL2 (.of_forall fun z ↦ by positivity)]
  refine (lintegral_mono hlow).trans ((lintegral_liminf_le hmeas).trans ?_)
  simp only [lintegral_kernel_mul_norm_add_sq hF hG contDiff_coshDistNormalBump.continuous
    (fun _ hc ↦ coshDistNormalBump_eq_zero hc) coshDistNormalBump_nonneg
    (integral_coshDistNormalBump I), le_refl]

lemma le_of_forall_re_kernelPair_le (hF : F ∈ maassSpace N χ a)
    (hE : 0 < ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) (hs : Tendsto s atTop atTop) {B : ℝ}
    (hB : ∀ j, (kernelPair N (coshDistNormalBump (s j)) F F).re ≤ B) :
    ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 ≤ B := by
  have h : ENNReal.ofReal (∫ z in gammaZeroDomain N, ‖F z + F z‖ ^ 2) ≤ liminf (fun j : ℕ ↦
      ENNReal.ofReal ((∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) +
        (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) +
          2 * (kernelPair N (coshDistNormalBump (s j)) F F).re)) atTop :=
    ofReal_integral_le_liminf hF hF hs
  have h2 : liminf (fun j : ℕ ↦ ENNReal.ofReal ((∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) +
      (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) +
        2 * (kernelPair N (coshDistNormalBump (s j)) F F).re)) atTop ≤
          ENNReal.ofReal ((∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) +
            (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) + 2 * B) :=
    liminf_le_of_frequently_le' (.of_forall fun j ↦ ENNReal.ofReal_le_ofReal (by
      linarith [hB j]))
  have h6 :
      ∫ z in gammaZeroDomain N, ‖F z + F z‖ ^ 2 = 4 * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun z ↦ ?_)
    dsimp only
    rw [← two_mul, norm_mul, mul_pow]
    norm_num
  have h5 : ENNReal.ofReal (4 * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) ≤
      ENNReal.ofReal ((∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) +
        (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) + 2 * B) := by
    rw [← h6]
    exact h.trans h2
  rcases ENNReal.ofReal_le_ofReal_iff'.mp h5 with h7 | h7
  · linarith
  · linarith

/-- **Every eigenvalue of a square-integrable Maass form is real**: if `F ≠ 0` lies in `M(N, χ, λ)`,
then `λ` is real. If not, the pairing of `F` with every point-pair invariant vanishes
(`kernelPair_eq_zero`), so that `∫∫ φ(cosh d(z, w)) |F(z) + F(w)|² = 2 ‖F‖²` for every smooth
kernel of mass `1`; letting the support of the kernel shrink to the diagonal, Fatou's lemma gives
`4 ‖F‖² ≤ 2 ‖F‖²`, so `F = 0`. No cuspidality or decay at the cusps is used: Green's identity is
only applied on `ℍ` to the compactly supported kernels. -/
lemma conj_eigenvalue_of_mem_maassSpace (hF : F ∈ maassSpace N χ eigenvalue) (hF0 : F ≠ 0) :
    conj eigenvalue = eigenvalue := by
  by_contra hne
  have hE : 0 < ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := integral_norm_sq_pos hF hF0
  refine hE.not_ge <| le_of_forall_re_kernelPair_le hF hE tendsto_id fun j ↦ ?_
  rw [kernelPair_eq_zero hF hF contDiff_coshDistNormalBump
    (fun _ hc ↦ coshDistNormalBump_eq_zero hc) (Ne.symm hne), Complex.zero_re]

end UpperHalfPlane
