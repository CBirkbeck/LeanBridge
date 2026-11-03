import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.PointPairKernel
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.ProductFundamentalDomain
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The eigenvalues of square-integrable Maass forms are real

Every nonzero element of `M(N, χ, λ)` (`UpperHalfPlane.maassSpace`) has a real eigenvalue `λ`, with
no cuspidality or decay hypothesis (LMFDB `mf.maass.exceptional_eigenvalue`: "Each eigenvalue is
real"). The proof uses Selberg's point-pair invariants `k(z, w) = φ(cosh d(z, w))`, with `φ` real,
smooth and vanishing on `[C, ∞)`, and avoids any boundary term at the cusps, since Green's identity
is only applied on `ℍ` to the compactly supported function `w ↦ k(z, w)`.

Write `B(φ) = ∫_{Γ₀(N) \ ℍ} ∫_ℍ φ(cosh d(z, w)) F(w) conj(F(z)) dμ(w) dμ(z)`
(`UpperHalfPlane.kernelPairing`).

* `B(φ)` is real: the kernel is real and symmetric, and `Ψ(z, w) = k(z, w) F(w) conj(F(z))` is
  invariant under the diagonal action of `Γ₀(N)`, of which `D × ℍ` and `ℍ × D` are fundamental
  domains (`MeasureTheory.IsFundamentalDomain.integral_prod_swap_eq`).
* `B(radialLaplacian φ) = -λ B(φ)`, by Green's identity in `w`.
* So if `λ` is not real, `B(φ) = 0` for every `φ`.
* For `φ` of mass `1`, `∫∫ φ(cosh d(z, w)) |F(z) + F(w)|² = 2 ‖F‖² + 2 Re B(φ)`, which is `2 ‖F‖²`
  if `B(φ) = 0`. When the support of `φ` shrinks to the point `c = 1`, the inner integral tends to
  `4 |F(z)|²`, so that Fatou's lemma gives `4 ‖F‖² ≤ 2 ‖F‖²`, and `F = 0`.

## Main definitions

* `UpperHalfPlane.gammaZeroPairMeasure`: the measure on `(Γ₀(N) \ ℍ) × ℍ`.
* `UpperHalfPlane.kernelPairing`: the pairing `B(φ)`.
* `UpperHalfPlane.coshDistBump`, `UpperHalfPlane.coshDistNormalBump`: the kernels whose support
  shrinks to the diagonal.

## Main results

* `UpperHalfPlane.integral_kernel_eq`: the mass of a radial kernel does not depend on the centre.
* `UpperHalfPlane.conj_kernelPairing`: `B(φ)` is real.
* `UpperHalfPlane.kernelPairing_radialLaplacian`: `B(radialLaplacian φ) = -λ B(φ)`.
* `UpperHalfPlane.kernelPairing_eq_zero`: `B(φ) = 0` if `λ` is not real.
* `UpperHalfPlane.integral_kernel_mul_norm_add_sq`: the identity for `|F(z) + F(w)|²`.
* `UpperHalfPlane.conj_eigenvalue_of_mem_maassSpace`: the eigenvalue is real.
-/

open MeasureTheory Filter CongruenceSubgroup Matrix Real Topology

open scoped ComplexConjugate ContDiff MatrixGroups

namespace UpperHalfPlane

variable (z : ℍ) {N : ℕ} {χ : DirichletCharacter ℂ N} {eigenvalue : ℂ} {F : ℍ → ℂ} {φ : ℝ → ℝ}
  {C δ : ℝ} {n : ℕ} {m : ℝ}

variable (N) in
/-- The product of the invariant measure on `gammaZeroDomain N` and the invariant measure on `ℍ`:
the integrals over it are those over `Γ₀(N) \ (ℍ × ℍ)` for the diagonal action. -/
noncomputable abbrev gammaZeroPairMeasure : Measure (ℍ × ℍ) :=
  (volume.restrict (gammaZeroDomain N)).prod volume

lemma dist_smul_smul_of_mem_gamma0
    (g : (Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) (w : ℍ) :
    dist (g • z) (g • w) = dist z w := by
  rcases g.2 with ⟨γ, -, hg⟩
  rw [Subgroup.smul_def, Subgroup.smul_def, ← hg, QuotientGroup.mk'_apply, pslMk_smul, pslMk_smul]
  exact dist_smul (SpecialLinearGroup.map (Int.castRingHom ℝ) γ) z w

lemma continuous_kernel (hφ : Continuous φ) :
    Continuous fun p : ℍ × ℍ ↦ φ (Real.cosh (dist p.1 p.2)) :=
  hφ.comp (Real.continuous_cosh.comp continuous_dist)

lemma hasCompactSupport_kernel (hφ0 : ∀ c, C ≤ c → φ c = 0) :
    HasCompactSupport fun w ↦ φ (Real.cosh (dist z w)) :=
  HasCompactSupport.intro (isCompact_closedBall z (2 * |C|)) fun _ hw ↦
    comp_cosh_dist_eq_zero z hφ0 hw

lemma continuous_kernel_right (hφ : Continuous φ) : Continuous fun w ↦ φ (Real.cosh (dist z w)) :=
  hφ.comp (Real.continuous_cosh.comp (continuous_const.dist continuous_id))

lemma integrable_kernel (hφ : Continuous φ) (hφ0 : ∀ c, C ≤ c → φ c = 0) :
    Integrable fun w ↦ φ (Real.cosh (dist z w)) :=
  (continuous_kernel_right z hφ).integrable_of_hasCompactSupport (hasCompactSupport_kernel z hφ0)

/-- **The mass of a radial kernel does not depend on the centre**, the group `SL(2, ℝ)` acting
transitively on `ℍ` by isometries that preserve the invariant measure. -/
lemma integral_kernel_eq (z' : ℍ) :
    ∫ w, φ (Real.cosh (dist z w)) = ∫ w, φ (Real.cosh (dist z' w)) := by
  rcases MulAction.exists_smul_eq SL(2, ℝ) z' z with ⟨g, rfl⟩
  rw [← (measurePreserving_smul g volume).integral_comp (measurableEmbedding_const_smul g)]
  simp only [dist_smul]

lemma integrableOn_norm_sq_of_mem_maassSpace (hF : F ∈ maassSpace N χ eigenvalue) :
    IntegrableOn (fun z ↦ ‖F z‖ ^ 2) (gammaZeroDomain N) := by
  simpa using hF.2.1

lemma norm_smul_eq_of_mem_maassSpace (hF : F ∈ maassSpace N χ eigenvalue)
    (g : (Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) : ‖F (g • z)‖ = ‖F z‖ := by
  have h : ‖(F ∘ ofComplex) ↑(g • z)‖ ^ 2 = ‖(F ∘ ofComplex) z‖ ^ 2 :=
    norm_sq_smul_eq hF.2.2.1 g z
  simp only [Function.comp_apply, ofComplex_apply] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

lemma integrable_kernel_mul_norm_sq_fst (hF : F ∈ maassSpace N χ eigenvalue) (hφ : Continuous φ)
    (hφ0 : ∀ c, C ≤ c → φ c = 0) :
    Integrable (fun p : ℍ × ℍ ↦ φ (Real.cosh (dist p.1 p.2)) * ‖F p.1‖ ^ 2)
      (gammaZeroPairMeasure N) := by
  have hFc : Continuous F := continuous_of_mem_maassSpace hF
  have hm : Continuous fun p : ℍ × ℍ ↦ φ (Real.cosh (dist p.1 p.2)) * ‖F p.1‖ ^ 2 :=
    (continuous_kernel hφ).mul ((hFc.comp continuous_fst).norm.pow 2)
  have hz (z : ℍ) : Integrable fun w ↦ φ (Real.cosh (dist z w)) * ‖F z‖ ^ 2 :=
    (integrable_kernel z hφ hφ0).mul_const _
  refine (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨.of_forall hz, ?_⟩
  have h1 (z : ℍ) : ∫ w, ‖φ (Real.cosh (dist z w)) * ‖F z‖ ^ 2‖ =
      (∫ w, |φ (Real.cosh (dist I w))|) * ‖F z‖ ^ 2 := by
    simp only [norm_mul, Real.norm_eq_abs, norm_pow, abs_norm]
    rw [integral_mul_const]
    congr 1
    exact integral_kernel_eq (φ := fun c ↦ |φ c|) z I
  simp only [h1]
  exact (integrableOn_norm_sq_of_mem_maassSpace hF).const_mul _

lemma integrable_kernel_mul_norm_sq_snd (hF : F ∈ maassSpace N χ eigenvalue) (hφ : Continuous φ)
    (hφ0 : ∀ c, C ≤ c → φ c = 0) :
    Integrable (fun p : ℍ × ℍ ↦ φ (Real.cosh (dist p.1 p.2)) * ‖F p.2‖ ^ 2)
      (gammaZeroPairMeasure N) := by
  have hFc : Continuous F := continuous_of_mem_maassSpace hF
  have h1 : Integrable (fun p : ℍ × ℍ ↦ φ (Real.cosh (dist p.1 p.2)) * ‖F p.1‖ ^ 2)
      (gammaZeroPairMeasure N) := integrable_kernel_mul_norm_sq_fst hF hφ hφ0
  have hm : Continuous fun p : ℍ × ℍ ↦ φ (Real.cosh (dist p.1 p.2)) * ‖F p.2‖ ^ 2 :=
    (continuous_kernel hφ).mul ((hFc.comp continuous_snd).norm.pow 2)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have h2 : ∫⁻ p, ‖φ (Real.cosh (dist p.1 p.2)) * ‖F p.1‖ ^ 2‖ₑ ∂gammaZeroPairMeasure N =
      ∫⁻ p, ‖φ (Real.cosh (dist p.swap.1 p.swap.2)) * ‖F p.swap.1‖ ^ 2‖ₑ ∂gammaZeroPairMeasure N :=
    (isFundamentalDomain_gammaZeroDomain N).lintegral_prod_swap_eq
      (Ψ := fun p : ℍ × ℍ ↦ ‖φ (Real.cosh (dist p.1 p.2)) * ‖F p.1‖ ^ 2‖ₑ) fun g p ↦ by
        simp only [Prod.smul_fst, Prod.smul_snd, dist_smul_smul_of_mem_gamma0,
          norm_smul_eq_of_mem_maassSpace _ hF]
  have h3 (p : ℍ × ℍ) : ‖φ (Real.cosh (dist p.1 p.2)) * ‖F p.2‖ ^ 2‖ₑ =
      ‖φ (Real.cosh (dist p.swap.1 p.swap.2)) * ‖F p.swap.1‖ ^ 2‖ₑ := by
    rw [Prod.fst_swap, Prod.snd_swap, dist_comm]
  simp only [h3]
  rw [← h2]
  exact hasFiniteIntegral_iff_enorm.mp h1.2

lemma continuous_kernel_mul (hF : F ∈ maassSpace N χ eigenvalue) (hφ : Continuous φ) :
    Continuous fun p : ℍ × ℍ ↦ (φ (Real.cosh (dist p.1 p.2)) : ℂ) * (F p.2 * conj (F p.1)) := by
  have hFc : Continuous F := continuous_of_mem_maassSpace hF
  exact (Complex.continuous_ofReal.comp (continuous_kernel hφ)).mul
    ((hFc.comp continuous_snd).mul (Complex.continuous_conj.comp (hFc.comp continuous_fst)))

lemma integrable_kernel_mul (hF : F ∈ maassSpace N χ eigenvalue) (hφ : Continuous φ)
    (hφ0 : ∀ c, C ≤ c → φ c = 0) :
    Integrable (fun p : ℍ × ℍ ↦ (φ (Real.cosh (dist p.1 p.2)) : ℂ) * (F p.2 * conj (F p.1)))
      (gammaZeroPairMeasure N) := by
  have hφa : Continuous fun c ↦ |φ c| := hφ.abs
  have hφa0 : ∀ c, C ≤ c → |φ c| = 0 := fun c hc ↦ by
    rw [hφ0 c hc, abs_zero]
  refine ((integrable_kernel_mul_norm_sq_fst hF hφa hφa0).add
    (integrable_kernel_mul_norm_sq_snd hF hφa hφa0)).mono'
    (continuous_kernel_mul hF hφ).aestronglyMeasurable (.of_forall fun p ↦ ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj, Pi.add_apply]
  have h : 2 * ‖F p.1‖ * ‖F p.2‖ ≤ ‖F p.1‖ ^ 2 + ‖F p.2‖ ^ 2 := two_mul_le_add_sq _ _
  have h0 : 0 ≤ ‖F p.1‖ := norm_nonneg _
  have h1 : 0 ≤ ‖F p.2‖ := norm_nonneg _
  have h2 : 0 ≤ |φ (Real.cosh (dist p.1 p.2))| := abs_nonneg _
  nlinarith [mul_nonneg h2 (add_nonneg (sq_nonneg ‖F p.1‖) (sq_nonneg ‖F p.2‖)),
    mul_nonneg h2 (mul_nonneg h0 h1)]

variable (N F φ) in
/-- The pairing `∫_{Γ₀(N) \ ℍ} ∫_ℍ φ(cosh d(z, w)) F(w) conj(F(z)) dμ(w) dμ(z)` of `F` with itself
through the point-pair invariant `φ(cosh d(z, w))`. -/
noncomputable def kernelPairing : ℂ :=
  ∫ p : ℍ × ℍ, (φ (Real.cosh (dist p.1 p.2)) : ℂ) * (F p.2 * conj (F p.1)) ∂gammaZeroPairMeasure N

/-- **The pairing with a real point-pair invariant is real**: the kernel `φ(cosh d(z, w))` is real
and symmetric, and invariant under the diagonal action of `Γ₀(N)`. -/
lemma conj_kernelPairing (hF : F ∈ maassSpace N χ eigenvalue) :
    conj (kernelPairing N F φ) = kernelPairing N F φ := by
  have h : kernelPairing N F φ =
      ∫ p : ℍ × ℍ, (φ (Real.cosh (dist p.swap.1 p.swap.2)) : ℂ) * (F p.swap.2 * conj (F p.swap.1))
        ∂gammaZeroPairMeasure N :=
    (isFundamentalDomain_gammaZeroDomain N).integral_prod_swap_eq
      (Ψ := fun p : ℍ × ℍ ↦ (φ (Real.cosh (dist p.1 p.2)) : ℂ) * (F p.2 * conj (F p.1)))
      fun g p ↦ by
        have hc : F (g • p.2) * conj (F (g • p.1)) = F p.2 * conj (F p.1) := by
          rcases g.2 with ⟨γ, hγ, hg⟩
          have hu : χ (γ 1 1 : ℤ) * conj (χ (γ 1 1 : ℤ)) = 1 := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
              norm_dirichletCharacter_of_mem_gamma0 χ hγ]
            norm_num
          rw [Subgroup.smul_def, Subgroup.smul_def, ← hg, QuotientGroup.mk'_apply, pslMk_smul,
            pslMk_smul, smul_eq_of_mem_maassSpace hF hγ, smul_eq_of_mem_maassSpace hF hγ, map_mul]
          linear_combination F p.2 * conj (F p.1) * hu
        simp only [Prod.smul_fst, Prod.smul_snd, dist_smul_smul_of_mem_gamma0, hc]
  rw [kernelPairing, ← integral_conj]
  refine Eq.trans ?_ h.symm
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

/-- **The pairing with the radial Laplacian of a kernel**: for `F` in `M(N, χ, λ)` and `φ` smooth
vanishing on `[C, ∞)`, the pairing with `radialLaplacian φ` is `-λ` times the one with `φ`, by
Green's identity on `ℍ` in the variable `w`. -/
lemma kernelPairing_radialLaplacian (hF : F ∈ maassSpace N χ eigenvalue) (hφ : ContDiff ℝ ∞ φ)
    (hφ0 : ∀ c, C ≤ c → φ c = 0) :
    kernelPairing N F (radialLaplacian φ) = -eigenvalue * kernelPairing N F φ := by
  have hφ1 : ∀ c, C + 1 ≤ c → radialLaplacian φ c = 0 := fun _ hc ↦ radialLaplacian_eq_zero hφ0 hc
  rw [kernelPairing, kernelPairing, integral_prod _ (integrable_kernel_mul hF
    (continuous_radialLaplacian hφ) hφ1),
    integral_prod _ (integrable_kernel_mul hF hφ.continuous hφ0), ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  dsimp only
  have h1 : ∫ w : ℍ, (radialLaplacian φ (Real.cosh (dist z w)) : ℂ) * F w =
      -eigenvalue * ∫ w : ℍ, (φ (Real.cosh (dist z w)) : ℂ) * F w := by
    have h : ∫ w : ℍ, (φ (Real.cosh (dist z w)) : ℂ) * hyperbolicLaplacian (F ∘ ofComplex) w =
        ∫ w : ℍ, (radialLaplacian φ (Real.cosh (dist z w)) : ℂ) * (F ∘ ofComplex) w :=
      integral_kernel_mul_hyperbolicLaplacian z hφ hφ0 hF.1
    simp only [Function.comp_apply, ofComplex_apply] at h
    rw [← h, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun w ↦ ?_)
    have h2 : hyperbolicLaplacian (F ∘ ofComplex) w + eigenvalue * (F ∘ ofComplex) w = 0 :=
      hF.2.2.2 w w.im_pos
    simp only [Function.comp_apply, ofComplex_apply] at h2
    dsimp only
    linear_combination (φ (Real.cosh (dist z w)) : ℂ) * h2
  simp only [← mul_assoc]
  rw [integral_mul_const, integral_mul_const, h1]
  ring1

/-- **If the eigenvalue is not real, all the pairings vanish**: the pairings with `φ` and with
`radialLaplacian φ` are real, and the second is `-λ` times the first. -/
lemma kernelPairing_eq_zero (hF : F ∈ maassSpace N χ eigenvalue) (hφ : ContDiff ℝ ∞ φ)
    (hφ0 : ∀ c, C ≤ c → φ c = 0) (h : conj eigenvalue ≠ eigenvalue) : kernelPairing N F φ = 0 := by
  have h1 : kernelPairing N F (radialLaplacian φ) = -eigenvalue * kernelPairing N F φ :=
    kernelPairing_radialLaplacian hF hφ hφ0
  have h2 : conj (kernelPairing N F (radialLaplacian φ)) =
      conj (-eigenvalue * kernelPairing N F φ) := congrArg conj h1
  rw [conj_kernelPairing hF, map_mul, map_neg, conj_kernelPairing hF] at h2
  have h3 : (conj eigenvalue - eigenvalue) * kernelPairing N F φ = 0 := by
    linear_combination h2 - h1
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr h)

lemma integral_kernel_mul_norm_sq_fst (hF : F ∈ maassSpace N χ eigenvalue) (hφ : Continuous φ)
    (hφ0 : ∀ c, C ≤ c → φ c = 0) (hmass : ∀ z : ℍ, ∫ w, φ (Real.cosh (dist z w)) = 1) :
    ∫ p : ℍ × ℍ, φ (Real.cosh (dist p.1 p.2)) * ‖F p.1‖ ^ 2 ∂gammaZeroPairMeasure N =
      ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := by
  rw [integral_prod _ (integrable_kernel_mul_norm_sq_fst hF hφ hφ0)]
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  dsimp only
  rw [integral_mul_const, hmass, one_mul]

lemma integral_kernel_mul_norm_sq_snd (hF : F ∈ maassSpace N χ eigenvalue) (hφ : Continuous φ)
    (hφ0 : ∀ c, C ≤ c → φ c = 0) (hmass : ∀ z : ℍ, ∫ w, φ (Real.cosh (dist z w)) = 1) :
    ∫ p : ℍ × ℍ, φ (Real.cosh (dist p.1 p.2)) * ‖F p.2‖ ^ 2 ∂gammaZeroPairMeasure N =
      ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := by
  rw [← integral_kernel_mul_norm_sq_fst hF hφ hφ0 hmass,
    (isFundamentalDomain_gammaZeroDomain N).integral_prod_swap_eq
    (Ψ := fun p : ℍ × ℍ ↦ φ (Real.cosh (dist p.1 p.2)) * ‖F p.1‖ ^ 2) fun g p ↦ by
      simp only [Prod.smul_fst, Prod.smul_snd, dist_smul_smul_of_mem_gamma0,
        norm_smul_eq_of_mem_maassSpace _ hF]]
  refine integral_congr_ae (.of_forall fun p ↦ ?_)
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [dist_comm]

lemma mul_norm_add_sq_eq (t : ℝ) (a b : ℂ) :
    t * ‖a + b‖ ^ 2 = t * ‖a‖ ^ 2 + t * ‖b‖ ^ 2 + 2 * Complex.reCLM ((t : ℂ) * (b * conj a)) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.reCLM_apply, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.add_re,
    Complex.add_im]
  ring1

lemma integrable_kernel_mul_norm_add_sq (hF : F ∈ maassSpace N χ eigenvalue) (hφ : Continuous φ)
    (hφ0 : ∀ c, C ≤ c → φ c = 0) :
    Integrable (fun p : ℍ × ℍ ↦ φ (Real.cosh (dist p.1 p.2)) * ‖F p.1 + F p.2‖ ^ 2)
      (gammaZeroPairMeasure N) := by
  simp only [mul_norm_add_sq_eq]
  exact ((integrable_kernel_mul_norm_sq_fst hF hφ hφ0).add
    (integrable_kernel_mul_norm_sq_snd hF hφ hφ0)).add
    ((Complex.reCLM.integrable_comp (integrable_kernel_mul hF hφ hφ0)).const_mul 2)

/-- **Pythagoras for a pair of points**: for `φ` of mass `1` with `kernelPairing N F φ = 0`,
`∫∫ φ(cosh d(z, w)) |F(z) + F(w)|² dμ(w) dμ(z) = 2 ∫ |F|² dμ`, the pairing being the cross term. -/
lemma integral_kernel_mul_norm_add_sq (hF : F ∈ maassSpace N χ eigenvalue) (hφ : Continuous φ)
    (hφ0 : ∀ c, C ≤ c → φ c = 0) (hmass : ∀ z : ℍ, ∫ w, φ (Real.cosh (dist z w)) = 1)
    (h : kernelPairing N F φ = 0) :
    ∫ p : ℍ × ℍ, φ (Real.cosh (dist p.1 p.2)) * ‖F p.1 + F p.2‖ ^ 2 ∂gammaZeroPairMeasure N =
      2 * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := by
  have hint : Integrable
      (fun p : ℍ × ℍ ↦ (φ (Real.cosh (dist p.1 p.2)) : ℂ) * (F p.2 * conj (F p.1)))
      (gammaZeroPairMeasure N) := integrable_kernel_mul hF hφ hφ0
  have h12 : Integrable (fun p : ℍ × ℍ ↦ φ (Real.cosh (dist p.1 p.2)) * ‖F p.1‖ ^ 2 +
      φ (Real.cosh (dist p.1 p.2)) * ‖F p.2‖ ^ 2) (gammaZeroPairMeasure N) :=
    (integrable_kernel_mul_norm_sq_fst hF hφ hφ0).add (integrable_kernel_mul_norm_sq_snd hF hφ hφ0)
  simp only [mul_norm_add_sq_eq]
  rw [integral_add h12 ((Complex.reCLM.integrable_comp hint).const_mul 2),
    integral_add (integrable_kernel_mul_norm_sq_fst hF hφ hφ0)
    (integrable_kernel_mul_norm_sq_snd hF hφ hφ0), integral_const_mul,
    integral_kernel_mul_norm_sq_fst hF hφ hφ0 hmass,
    integral_kernel_mul_norm_sq_snd hF hφ hφ0 hmass, Complex.reCLM.integral_comp_comm hint]
  have h1 : ∫ p : ℍ × ℍ, (φ (Real.cosh (dist p.1 p.2)) : ℂ) * (F p.2 * conj (F p.1))
      ∂gammaZeroPairMeasure N = 0 := h
  rw [h1, map_zero, mul_zero, add_zero]
  ring1

lemma lintegral_kernel_mul_norm_add_sq (hF : F ∈ maassSpace N χ eigenvalue) (hφ : Continuous φ)
    (hφ0 : ∀ c, C ≤ c → φ c = 0) (hnn : ∀ c, 0 ≤ φ c)
    (hmass : ∀ z : ℍ, ∫ w, φ (Real.cosh (dist z w)) = 1) (h : kernelPairing N F φ = 0) :
    ∫⁻ z in gammaZeroDomain N, ∫⁻ w, ENNReal.ofReal (φ (Real.cosh (dist z w)) * ‖F z + F w‖ ^ 2) =
      ENNReal.ofReal (2 * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) := by
  have hFc : Continuous F := continuous_of_mem_maassSpace hF
  have hc : Continuous fun p : ℍ × ℍ ↦ φ (Real.cosh (dist p.1 p.2)) * ‖F p.1 + F p.2‖ ^ 2 :=
    (continuous_kernel hφ).mul
      (((hFc.comp continuous_fst).add (hFc.comp continuous_snd)).norm.pow 2)
  have hm : AEMeasurable (fun p : ℍ × ℍ ↦
      ENNReal.ofReal (φ (Real.cosh (dist p.1 p.2)) * ‖F p.1 + F p.2‖ ^ 2))
      (gammaZeroPairMeasure N) :=
    (ENNReal.measurable_ofReal.comp hc.measurable).aemeasurable
  rw [← integral_kernel_mul_norm_add_sq hF hφ hφ0 hmass h, ofReal_integral_eq_lintegral_ofReal
    (integrable_kernel_mul_norm_add_sq hF hφ hφ0) (.of_forall fun p ↦ mul_nonneg (hnn _)
      (sq_nonneg _))]
  exact (lintegral_prod _ hm).symm

lemma ofReal_le_lintegral_kernel_mul (hφ : Continuous φ) (hφ0 : ∀ c, C ≤ c → φ c = 0)
    (hnn : ∀ c, 0 ≤ φ c) (hmass : ∀ z : ℍ, ∫ w, φ (Real.cosh (dist z w)) = 1)
    (hm : ∀ w : ℍ, φ (Real.cosh (dist z w)) ≠ 0 → m ≤ ‖F z + F w‖ ^ 2) :
    ENNReal.ofReal m ≤ ∫⁻ w : ℍ, ENNReal.ofReal (φ (Real.cosh (dist z w)) * ‖F z + F w‖ ^ 2) := by
  have hnn' : 0 ≤ᵐ[(volume : Measure ℍ)] fun w : ℍ ↦ φ (Real.cosh (dist z w)) :=
    .of_forall fun w ↦ hnn _
  have h1 : ∫⁻ w : ℍ, ENNReal.ofReal (φ (Real.cosh (dist z w))) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_kernel z hφ hφ0) hnn', hmass,
      ENNReal.ofReal_one]
  have hme : Measurable fun w : ℍ ↦ ENNReal.ofReal (φ (Real.cosh (dist z w))) :=
    ENNReal.measurable_ofReal.comp (continuous_kernel_right z hφ).measurable
  have h2 : ∫⁻ w : ℍ, ENNReal.ofReal (φ (Real.cosh (dist z w))) * ENNReal.ofReal m =
      ENNReal.ofReal m := by
    rw [lintegral_mul_const _ hme, h1, one_mul]
  have h3 : ∫⁻ w : ℍ, ENNReal.ofReal (φ (Real.cosh (dist z w))) * ENNReal.ofReal m ≤
      ∫⁻ w : ℍ, ENNReal.ofReal (φ (Real.cosh (dist z w)) * ‖F z + F w‖ ^ 2) := by
    refine lintegral_mono fun w ↦ ?_
    dsimp only
    rw [← ENNReal.ofReal_mul (hnn _)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases h0 : φ (Real.cosh (dist z w)) = 0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_left (hm w h0) (hnn _)
  exact h2.symm.le.trans h3

variable (n) in
/-- The smooth bump `c ↦ smoothTransition(2 - (n + 1)(c - 1))`, equal to `1` for
`c ≤ 1 + 1/(n + 1)` and to `0` for `c ≥ 1 + 2/(n + 1)`. -/
noncomputable def coshDistBump (c : ℝ) : ℝ :=
  smoothTransition (2 - (n + 1) * (c - 1))

variable (n) in
/-- The bump `coshDistBump n` normalised to have mass `1` as a kernel on `ℍ`. -/
noncomputable def coshDistNormalBump (c : ℝ) : ℝ :=
  (∫ w, coshDistBump n (Real.cosh (dist I w)))⁻¹ * coshDistBump n c

lemma contDiff_coshDistBump : ContDiff ℝ ∞ (coshDistBump n) :=
  smoothTransition.contDiff.comp (by fun_prop)

lemma coshDistBump_eq_zero {c : ℝ} (hc : 3 ≤ c) : coshDistBump n c = 0 := by
  refine smoothTransition.zero_of_nonpos ?_
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

lemma coshDistBump_nonneg (c : ℝ) : 0 ≤ coshDistBump n c :=
  smoothTransition.nonneg _

lemma integral_coshDistBump_pos : 0 < ∫ w, coshDistBump n (Real.cosh (dist I w)) := by
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

lemma integral_coshDistNormalBump : ∫ w, coshDistNormalBump n (Real.cosh (dist z w)) = 1 := by
  simp only [coshDistNormalBump]
  rw [integral_const_mul, integral_kernel_eq z I]
  exact inv_mul_cancel₀ integral_coshDistBump_pos.ne'

lemma eventually_coshDistNormalBump_eq_zero (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℝ, δ ≤ d → coshDistNormalBump n (Real.cosh d) = 0 := by
  have hcosh : 0 < Real.cosh δ - 1 := sub_pos.mpr (Real.one_lt_cosh.mpr hδ.ne')
  rcases exists_nat_gt (2 / (Real.cosh δ - 1)) with ⟨k, hk⟩
  filter_upwards [eventually_ge_atTop k] with n hn d hd
  have h1 : Real.cosh δ ≤ Real.cosh d := Real.cosh_le_cosh.mpr <| by
    rw [abs_of_pos hδ, abs_of_pos (hδ.trans_le hd)]
    exact hd
  have h2 : 2 ≤ ((n : ℝ) + 1) * (Real.cosh d - 1) := by
    have h3 : 2 / (Real.cosh δ - 1) < (n : ℝ) + 1 := by
      have h4 : (k : ℝ) ≤ n := Nat.cast_le.mpr hn
      linarith
    have h5 : 2 < ((n : ℝ) + 1) * (Real.cosh δ - 1) := (div_lt_iff₀ hcosh).mp h3
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  rw [coshDistNormalBump, coshDistBump, smoothTransition.zero_of_nonpos (by linarith), mul_zero]

/-- **Every eigenvalue of a square-integrable Maass form is real**: if `F ≠ 0` lies in `M(N, χ, λ)`,
then `λ` is real. If not, the pairing of `F` with every point-pair invariant vanishes
(`kernelPairing_eq_zero`), so that `∫∫ φ(cosh d(z, w)) |F(z) + F(w)|² = 2 ‖F‖²` for every smooth
kernel of mass `1`; letting the support of the kernel shrink to the diagonal, Fatou's lemma gives
`4 ‖F‖² ≤ 2 ‖F‖²`, so `F = 0`. No cuspidality or decay at the cusps is used: Green's identity is
only applied on `ℍ` to the compactly supported kernels. -/
lemma conj_eigenvalue_of_mem_maassSpace (hF : F ∈ maassSpace N χ eigenvalue) (hF0 : F ≠ 0) :
    conj eigenvalue = eigenvalue := by
  by_contra hne
  refine hF0 (eq_zero_of_maassPetersson_self_eq_zero hF ?_)
  have hFc : Continuous F := continuous_of_mem_maassSpace hF
  have hL2 : IntegrableOn (fun z ↦ ‖F z‖ ^ 2) (gammaZeroDomain N) :=
    integrableOn_norm_sq_of_mem_maassSpace hF
  have hint (n : ℕ) : ∫⁻ z in gammaZeroDomain N, ∫⁻ w : ℍ,
      ENNReal.ofReal (coshDistNormalBump n (Real.cosh (dist z w)) * ‖F z + F w‖ ^ 2) =
        ENNReal.ofReal (2 * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) :=
    lintegral_kernel_mul_norm_add_sq hF contDiff_coshDistNormalBump.continuous
      (fun _ hc ↦ coshDistNormalBump_eq_zero hc) coshDistNormalBump_nonneg
      (fun z ↦ integral_coshDistNormalBump z) (kernelPairing_eq_zero hF contDiff_coshDistNormalBump
        (fun _ hc ↦ coshDistNormalBump_eq_zero hc) hne)
  have hmeas (n : ℕ) : Measurable fun z : ℍ ↦ ∫⁻ w : ℍ,
      ENNReal.ofReal (coshDistNormalBump n (Real.cosh (dist z w)) * ‖F z + F w‖ ^ 2) := by
    have hc : Continuous fun p : ℍ × ℍ ↦
        coshDistNormalBump n (Real.cosh (dist p.1 p.2)) * ‖F p.1 + F p.2‖ ^ 2 :=
      (continuous_kernel contDiff_coshDistNormalBump.continuous).mul
        (((hFc.comp continuous_fst).add (hFc.comp continuous_snd)).norm.pow 2)
    exact Measurable.lintegral_prod_right' (ENNReal.measurable_ofReal.comp hc.measurable)
  have hlow (z : ℍ) : ENNReal.ofReal (4 * ‖F z‖ ^ 2) ≤ liminf (fun n : ℕ ↦ ∫⁻ w : ℍ,
      ENNReal.ofReal (coshDistNormalBump n (Real.cosh (dist z w)) * ‖F z + F w‖ ^ 2)) atTop := by
    have hg : Continuous fun w : ℍ ↦ ‖F z + F w‖ ^ 2 := (continuous_const.add hFc).norm.pow 2
    have hgz : ‖F z + F z‖ ^ 2 = 4 * ‖F z‖ ^ 2 := by
      rw [← two_mul, norm_mul, mul_pow]
      norm_num
    have hle {ε : ℝ} (hε : 0 < ε) : ENNReal.ofReal (4 * ‖F z‖ ^ 2 - ε) ≤ liminf (fun n : ℕ ↦
        ∫⁻ w : ℍ, ENNReal.ofReal (coshDistNormalBump n (Real.cosh (dist z w)) *
          ‖F z + F w‖ ^ 2)) atTop := by
      have hzz : 4 * ‖F z‖ ^ 2 - ε < ‖F z + F z‖ ^ 2 := by
        rw [hgz]
        linarith
      have hev : ∀ᶠ w in 𝓝 z, 4 * ‖F z‖ ^ 2 - ε < ‖F z + F w‖ ^ 2 :=
        hg.continuousAt.eventually_const_lt hzz
      rcases Metric.eventually_nhds_iff.mp hev with ⟨δ, hδ, hball⟩
      refine le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [eventually_coshDistNormalBump_eq_zero hδ] with n hn
      refine ofReal_le_lintegral_kernel_mul z contDiff_coshDistNormalBump.continuous
        (fun _ hc ↦ coshDistNormalBump_eq_zero hc) coshDistNormalBump_nonneg
        (fun z ↦ integral_coshDistNormalBump z) fun w hw ↦ le_of_lt (hball ?_)
      by_contra hd
      exact hw (hn _ (not_lt.mp hd |>.trans_eq (dist_comm w z)))
    have ht : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (4 * ‖F z‖ ^ 2 - ε)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (4 * ‖F z‖ ^ 2))) := by
      have hc : Continuous fun ε : ℝ ↦ ENNReal.ofReal (4 * ‖F z‖ ^ 2 - ε) :=
        ENNReal.continuous_ofReal.comp (continuous_const.sub continuous_id)
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    exact le_of_tendsto ht (eventually_mem_nhdsWithin.mono fun ε hε ↦ hle hε)
  have hfatou : ∫⁻ z in gammaZeroDomain N, ENNReal.ofReal (4 * ‖F z‖ ^ 2) ≤
      ENNReal.ofReal (2 * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) := by
    refine (lintegral_mono hlow).trans ((lintegral_liminf_le hmeas).trans ?_)
    simp only [hint, liminf_const, le_refl]
  have hE : 0 ≤ ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 :=
    integral_nonneg fun z ↦ sq_nonneg _
  have h4 : ∫⁻ z in gammaZeroDomain N, ENNReal.ofReal (4 * ‖F z‖ ^ 2) =
      ENNReal.ofReal (4 * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) := by
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hL2.const_mul 4)
      (.of_forall fun z ↦ by positivity)]
  rw [h4, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hfatou
  have hE0 : ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 = 0 := by
    linarith
  have h5 (z : ℍ) : F z * conj (F z) = ((‖F z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [maassPetersson, h5]
  rw [integral_complex_ofReal, hE0, Complex.ofReal_zero]

end UpperHalfPlane
