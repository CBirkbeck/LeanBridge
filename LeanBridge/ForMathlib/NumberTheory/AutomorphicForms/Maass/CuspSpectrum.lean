import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CuspidalKernelBound
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.PoincareSpanCuspForm

/-!
# Discreteness of the spectrum of Maass cusp forms

The Maass cusp forms of weight `0` on `Γ₀(N)`, `N ≠ 0`, with character `χ` (the elements of
`M(N, χ, λ)` whose constant term vanishes at every cusp, `UpperHalfPlane.maassCuspSpace`) have
finitely many eigenvalues below every bound, and finite-dimensional eigenspaces (Selberg; LMFDB
`mf.maass.spectral_index`). The proof avoids the spectral decomposition of `L²(Γ₀(N) \ ℍ)`: it is a
Bessel inequality. Let `f_i` be a finite orthonormal family of Maass cusp forms with eigenvalues at
most `Λ`, and let `P` be the average over a ball of small radius, depending only on `Λ`, for the
kernel `coshDistNormalBump (2m + 1)`.

* `‖P f_i‖² ≥ 1/4`, by Green's identity on `ℍ`, as the average of a Maass form with bounded
  eigenvalue over a small ball is close to the form (`UpperHalfPlane.le_re_kernelPair_add`).
  Selberg's theorem that `P f_i` is a multiple of `f_i` is not used.
* `∑_i |P f_i(z)|² ≤ C` at every point `z` of the fundamental domain: the average at `z` is a
  bounded linear functional on the cuspidal functions, uniformly in `z`
  (`UpperHalfPlane.exists_sq_norm_integral_kernel_mul_le`), and applied to
  `g = ∑_i conj(P f_i(z)) f_i` this is Bessel's inequality.
* Integrating over the fundamental domain, of finite volume, gives `∑_i 1/4 ≤ C vol(Γ₀(N) \ ℍ)`.

Eigenforms with different eigenvalues being orthogonal
(`UpperHalfPlane.maassPetersson_eq_zero_of_ne`), this bounds the number of eigenvalues at most `Λ`,
and the Gram–Schmidt process bounds the dimension of an eigenspace. The eigenvalues are real
(`UpperHalfPlane.conj_eigenvalue_of_mem_maassSpace`) and positive
(`UpperHalfPlane.zero_lt_of_mem_maassCuspSpace`).

## Main definitions

* `UpperHalfPlane.maassCuspSpace`: the Maass cusp forms on `Γ₀(N)` with character `χ` and eigenvalue
  `λ`.
* `UpperHalfPlane.kernelAverage`: the average of a function around a point for a radial kernel.
* `UpperHalfPlane.maassCuspSpectrum`: the eigenvalues of the nonzero Maass cusp forms.

## Main results

* `UpperHalfPlane.sum_sq_norm_kernelAverage_le`: Bessel's inequality for the averages.
* `UpperHalfPlane.one_div_four_le_integral_sq_kernelAverage`: the average of a Maass form over a
  small ball keeps a quarter of the squared norm.
* `UpperHalfPlane.apply_eq_of_mem_maassSpace_zero`: a Maass form with eigenvalue `0` is constant.
* `UpperHalfPlane.exists_forall_card_le`: the number of orthonormal Maass cusp forms with bounded
  eigenvalues is bounded.
* `UpperHalfPlane.finite_of_forall_maassPetersson_eq_zero`: a pairwise orthogonal family of nonzero
  Maass cusp forms with bounded eigenvalues is finite.
* `UpperHalfPlane.finite_maassCuspSpectrum_inter_Iic`: the spectrum is discrete.
* `UpperHalfPlane.finite_maassCuspSpace`: the eigenspaces are finite-dimensional.
* `UpperHalfPlane.zero_lt_of_mem_maassCuspSpace`: the eigenvalues of Maass cusp forms are positive.
-/

open MeasureTheory Real Set

open scoped ComplexConjugate ContDiff InnerProductSpace MatrixGroups

namespace UpperHalfPlane

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {a : ℂ} {φ : ℝ → ℝ} {F G : ℍ → ℂ} {l Λ C : ℝ}
  {ι : Type*} [Fintype ι] {f : ι → ℍ → ℂ} (c : ι → ℂ) (x y : ℂ) (z : ℍ)

variable (N χ a) in
/-- The space of the **Maass cusp forms** of weight `0` on `Γ₀(N)` with character `χ` and eigenvalue
`λ`: the elements of `M(N, χ, λ)` (`maassSpace`) whose constant term vanishes at every cusp
(`maassCuspidalSpace`). -/
noncomputable def maassCuspSpace : Submodule ℂ (ℍ → ℂ) :=
  maassSpace N χ a ⊓ maassCuspidalSpace N χ

lemma mem_maassCuspSpace_iff :
    F ∈ maassCuspSpace N χ a ↔ F ∈ maassSpace N χ a ∧ F ∈ maassCuspidalSpace N χ :=
  Submodule.mem_inf

variable (φ F) in
/-- The average `∫_ℍ φ(cosh d(z, w)) F(w) dμ(w)` of `F` around `z` for the radial kernel `φ`. -/
noncomputable def kernelAverage : ℂ :=
  ∫ w : ℍ, (φ (dist z w).cosh : ℂ) * F w

lemma stronglyMeasurable_kernelAverage (hφ : Continuous φ) (hF : Continuous F) :
    StronglyMeasurable (kernelAverage φ F) := by
  have hc : Continuous fun p : ℍ × ℍ ↦ (φ (dist p.1 p.2).cosh : ℂ) * F p.2 :=
    (Complex.continuous_ofReal.comp (continuous_kernel hφ)).mul (hF.comp continuous_snd)
  exact hc.stronglyMeasurable.integral_prod_right'

lemma kernelAverage_sum (hφ : Continuous φ) (hφ0 : ∀ c, 3 ≤ c → φ c = 0)
    (hf : ∀ i, Continuous (f i)) :
    kernelAverage φ (∑ i, c i • f i) z = ∑ i, c i * kernelAverage φ (f i) z := by
  simp only [kernelAverage, Finset.sum_apply, Pi.smul_apply, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ ↦ ?_]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun w ↦ ?_)
    ring1
  · refine ((integrable_kernel_mul_of_continuous z hφ hφ0 (hf i)).const_mul (c i)).congr
      (.of_forall fun w ↦ ?_)
    ring1

lemma maassPetersson_sum_smul (hf : ∀ i, MemLp (f i) 2 (volume.restrict (gammaZeroDomain N))) :
    maassPetersson N (∑ i, c i • f i) (∑ i, c i • f i) =
      ∑ i, ∑ j, c i * conj (c j) * maassPetersson N (f i) (f j) := by
  have hint (i j : ι) :
      Integrable (fun z ↦ f i z * conj (f j z)) (volume.restrict (gammaZeroDomain N)) :=
    (hf i).integrable_mul (hf j).star
  have hpt (z : ℍ) : (∑ i, c i • f i) z * conj ((∑ i, c i • f i) z) =
      ∑ i, ∑ j, c i * conj (c j) * (f i z * conj (f j z)) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring1
  simp only [maassPetersson, hpt]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ (hint i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ (hint i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_const_mul]

lemma memLp_of_mem_maassCuspidalSpace (hF : F ∈ maassCuspidalSpace N χ) :
    MemLp F 2 (volume.restrict (gammaZeroDomain N)) :=
  (memLp_two_iff_integrable_sq_norm hF.1.aestronglyMeasurable).mpr hF.2.2.1

/-- **Bessel's inequality for the averages of an orthonormal family**: if
`|∫_ℍ φ(cosh d(z, w)) g(w) dμ(w)|² ≤ C ‖g‖²` for every cuspidal function `g`, at a point `z`, then
`∑_i |∫_ℍ φ(cosh d(z, w)) f_i(w) dμ(w)|² ≤ C` for every finite orthonormal family `f_i` of cuspidal
functions: apply the bound to `g = ∑_i conj(A_i) f_i`, where `A_i` is the average of `f_i`. -/
lemma sum_sq_norm_kernelAverage_le [DecidableEq ι] (hC0 : 0 ≤ C) (hφ : Continuous φ)
    (hφ0 : ∀ c, 3 ≤ c → φ c = 0) (hf : ∀ i, f i ∈ maassCuspidalSpace N χ)
    (horth : ∀ i j, maassPetersson N (f i) (f j) = if i = j then 1 else 0)
    (hz : ∀ g ∈ maassCuspidalSpace N χ, ‖kernelAverage φ g z‖ ^ 2 ≤
      C * ∫ u in gammaZeroDomain N, ‖g u‖ ^ 2) : ∑ i, ‖kernelAverage φ (f i) z‖ ^ 2 ≤ C := by
  let c : ι → ℂ := fun i ↦ conj (kernelAverage φ (f i) z)
  let S : ℝ := ∑ i, ‖kernelAverage φ (f i) z‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ by positivity
  have hg : ∑ i, c i • f i ∈ maassCuspidalSpace N χ :=
    Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (hf i)
  have h1 : kernelAverage φ (∑ i, c i • f i) z = (S : ℂ) := by
    rw [kernelAverage_sum c z hφ hφ0 fun i ↦ (hf i).1]
    push_cast [S]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [c]
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring1
  have h2 : ((∫ u in gammaZeroDomain N, ‖(∑ i, c i • f i) u‖ ^ 2 : ℝ) : ℂ) = (S : ℂ) := by
    rw [← maassPetersson_self, maassPetersson_sum_smul c fun i ↦
      memLp_of_mem_maassCuspidalSpace (hf i)]
    simp only [horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ]
    push_cast [S]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [c, Complex.conj_conj]
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring1
  have h3 : ‖kernelAverage φ (∑ i, c i • f i) z‖ ^ 2 ≤
      C * ∫ u in gammaZeroDomain N, ‖(∑ i, c i • f i) u‖ ^ 2 := hz _ hg
  rw [h1, Complex.ofReal_injective h2, Complex.norm_real, Real.norm_of_nonneg hS, sq] at h3
  exact le_of_not_gt fun hlt ↦ (mul_lt_mul_of_pos_right hlt (hC0.trans_lt hlt)).not_ge h3

lemma kernelPair_eq_setIntegral (hF : F ∈ maassSpace N χ a) (hG : G ∈ maassSpace N χ a)
    (hφ : Continuous φ) (hφ0 : ∀ c, 3 ≤ c → φ c = 0) :
    kernelPair N φ F G = ∫ z in gammaZeroDomain N, kernelAverage φ F z * conj (G z) := by
  rw [kernelPair, integral_prod _ (integrable_kernel_mul hF hG hφ hφ0)]
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  simp only [← mul_assoc]
  rw [integral_mul_const]
  rfl

lemma re_mul_conj_le : (x * conj y).re ≤ ‖x‖ ^ 2 + 1 / 4 * ‖y‖ ^ 2 := by
  have h : (x * conj y).re ≤ ‖x‖ * ‖y‖ := by
    simpa only [norm_mul, Complex.norm_conj] using Complex.re_le_norm (x * conj y)
  nlinarith [sq_nonneg (‖x‖ - 1 / 2 * ‖y‖)]

/-- **The average of a Maass form over a small ball keeps a quarter of the squared norm**: for `F`
in `M(N, χ, l)`, `l` real, with `‖F‖ = 1`, and `m + 1 ≥ 4 |l|`, the average of `F` for the kernel
`coshDistNormalBump (2m + 1)` has squared norm at least `1/4`, if it is square-integrable. -/
lemma one_div_four_le_integral_sq_kernelAverage {m : ℕ} (hF : F ∈ maassSpace N χ (l : ℂ))
    (hE : ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 = 1) (hm : 4 * |l| ≤ m + 1)
    (hA : IntegrableOn (fun z ↦ ‖kernelAverage (coshDistNormalBump (2 * m + 1)) F z‖ ^ 2)
      (gammaZeroDomain N)) :
    1 / 4 ≤ ∫ z in gammaZeroDomain N, ‖kernelAverage (coshDistNormalBump (2 * m + 1)) F z‖ ^ 2 := by
  have hm0 : (0 : ℝ) < m + 1 := by
    positivity
  have hP : Continuous (coshDistNormalBump (2 * m + 1)) := contDiff_coshDistNormalBump.continuous
  have hP0 : ∀ c, 3 ≤ c → coshDistNormalBump (2 * m + 1) c = 0 :=
    fun _ hc ↦ coshDistNormalBump_eq_zero hc
  have h1 : ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 ≤
      (kernelPair N (coshDistNormalBump (2 * m + 1)) F F).re +
        2 * (|l| * (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) / (m + 1)) :=
    le_re_kernelPair_add m hF (by rw [hE]; exact one_pos)
  rw [hE, mul_one, kernelPair_eq_setIntegral hF hF hP hP0] at h1
  have h2 : 2 * (|l| / ((m : ℝ) + 1)) ≤ 1 / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ hm0 two_pos]
    linarith
  have hint : IntegrableOn (fun z ↦ kernelAverage (coshDistNormalBump (2 * m + 1)) F z * conj (F z))
      (gammaZeroDomain N) := by
    refine (integrable_kernel_mul hF hF hP hP0).integral_prod_left.congr (.of_forall fun z ↦ ?_)
    simp only [← mul_assoc]
    rw [integral_mul_const]
    rfl
  have h3 : (∫ z in gammaZeroDomain N,
      kernelAverage (coshDistNormalBump (2 * m + 1)) F z * conj (F z)).re =
      ∫ z in gammaZeroDomain N,
        (kernelAverage (coshDistNormalBump (2 * m + 1)) F z * conj (F z)).re :=
    (Complex.reCLM.integral_comp_comm hint).symm
  have hL2 : IntegrableOn (fun z ↦ ‖F z‖ ^ 2) (gammaZeroDomain N) :=
    integrableOn_norm_sq_of_mem_maassSpace hF
  have h4 : ∫ z in gammaZeroDomain N,
      (kernelAverage (coshDistNormalBump (2 * m + 1)) F z * conj (F z)).re ≤
        ∫ z in gammaZeroDomain N, (‖kernelAverage (coshDistNormalBump (2 * m + 1)) F z‖ ^ 2 +
          1 / 4 * ‖F z‖ ^ 2) :=
    integral_mono (Complex.reCLM.integrable_comp hint) (hA.add (hL2.const_mul _)) fun z ↦
      re_mul_conj_le _ _
  rw [integral_add hA (hL2.const_mul _), integral_const_mul, hE] at h4
  rw [h3] at h1
  linarith

variable (N) in
lemma isOpen_gammaZeroDomain : IsOpen (gammaZeroDomain N) :=
  isOpen_iUnion fun _ ↦ ModularGroup.isOpen_smul_fdo _

lemma maassPetersson_inv_sqrt_smul_self (hF : F ∈ maassSpace N χ a) (hF0 : F ≠ 0) : maassPetersson N
    (((√(∫ z in gammaZeroDomain N, ‖F z‖ ^ 2))⁻¹ : ℂ) • F)
    (((√(∫ z in gammaZeroDomain N, ‖F z‖ ^ 2))⁻¹ : ℂ) • F) = 1 := by
  have hE : 0 < ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := integral_norm_sq_pos hF hF0
  have hs : √(∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hE).ne'
  have hs2 : √(∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) * √(∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) =
      ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := Real.mul_self_sqrt hE.le
  rw [maassPetersson_smul_smul, maassPetersson_self, map_inv₀, Complex.conj_ofReal, ← hs2]
  push_cast
  rw [hs2]
  have hs' : (√(∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast hs
  field_simp

variable (N χ) in
/-- The **spectrum of the Maass cusp forms** of weight `0` on `Γ₀(N)` with character `χ`: the real
numbers `x` that are the eigenvalue of a nonzero Maass cusp form. Every eigenvalue of a nonzero
Maass form is real (`conj_eigenvalue_of_mem_maassSpace`). -/
def maassCuspSpectrum : Set ℝ :=
  {x | ∃ F : ℍ → ℂ, F ≠ 0 ∧ F ∈ maassCuspSpace N χ (x : ℂ)}

lemma maassPetersson_eq_inner (hF : MemLp F 2 (volume.restrict (gammaZeroDomain N)))
    (hG : MemLp G 2 (volume.restrict (gammaZeroDomain N))) :
    maassPetersson N F G = ⟪hG.toLp G, hF.toLp F⟫_ℂ := by
  rw [L2.inner_def, maassPetersson]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with z hz1 hz2
  rw [hz1, hz2, RCLike.inner_apply]

/-- **A Maass form with eigenvalue `0` is constant**: for `F` in `M(N, χ, 0)`, the pairing of `F`
with itself through the kernel `P_1` equals `‖F‖²`, so that `F(z) = F(w)` for `d(z, w)` small, and
`F` is locally constant on `ℍ`, which is connected. -/
lemma apply_eq_of_mem_maassSpace_zero (hF : F ∈ maassSpace N χ 0) (w : ℍ) : F z = F w := by
  by_cases hF0 : F = 0
  · simp [hF0]
  have hF' : F ∈ maassSpace N χ ((0 : ℝ) : ℂ) := by
    simpa using hF
  have hE : 0 < ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 := integral_norm_sq_pos hF hF0
  have h1 : ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 ≤ (kernelPair N (coshDistNormalBump 1) F F).re +
      2 * (|(0 : ℝ)| * (∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) / ((0 : ℕ) + 1)) :=
    le_re_kernelPair_add 0 hF' hE
  have h2 : (kernelPair N (coshDistNormalBump 1) F F).re ≤ ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 :=
    re_kernelPair_le 1 hF'
  simp only [abs_zero, zero_mul, zero_div, mul_zero, add_zero] at h1
  have hP : Continuous (coshDistNormalBump 1) := contDiff_coshDistNormalBump.continuous
  have hP0 : ∀ c, 3 ≤ c → coshDistNormalBump 1 c = 0 := fun _ hc ↦ coshDistNormalBump_eq_zero hc
  have h3 : ∫ p : ℍ × ℍ, coshDistNormalBump 1 (dist p.1 p.2).cosh * ‖F p.1 - F p.2‖ ^ 2
      ∂gammaZeroPairMeasure N = (∫ w, coshDistNormalBump 1 (dist I w).cosh) *
        (2 * ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2) -
          2 * (kernelPair N (coshDistNormalBump 1) F F).re :=
    integral_kernel_mul_norm_sub_sq_eq hF' hP hP0
  rw [integral_coshDistNormalBump I, one_mul] at h3
  have h4 : ∫ p : ℍ × ℍ, coshDistNormalBump 1 (dist p.1 p.2).cosh * ‖F p.1 - F p.2‖ ^ 2
      ∂gammaZeroPairMeasure N = 0 := by
    rw [h3, le_antisymm h2 h1]
    ring1
  have hae : (fun p : ℍ × ℍ ↦ coshDistNormalBump 1 (dist p.1 p.2).cosh *
      ‖F p.1 - F p.2‖ ^ 2) =ᵐ[gammaZeroPairMeasure N] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun p ↦ mul_nonneg (coshDistNormalBump_nonneg _)
      (by positivity)) (integrable_kernel_mul_norm_sub_sq hF' hP hP0)).mp h4
  have hFc : Continuous F := continuous_of_mem_maassSpace hF
  let U : Set (ℍ × ℍ) := {p | coshDistNormalBump 1 (dist p.1 p.2).cosh * ‖F p.1 - F p.2‖ ^ 2 ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun ((continuous_kernel hP).mul
    (((hFc.comp continuous_fst).sub (hFc.comp continuous_snd)).norm.pow 2)) continuous_const
  have hnull : (volume.prod volume : Measure (ℍ × ℍ)) U = 0 := by
    refine (isFundamentalDomain_gammaZeroDomain N).prod_univ.measure_zero_of_invariant _
      (fun g ↦ ?_) ?_
    · ext p
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      have hd : dist (g⁻¹ • p.1) (g⁻¹ • p.2) = dist p.1 p.2 :=
        dist_smul_smul_of_mem_gamma0 p.1 g⁻¹ p.2
      have hn : ‖F (g⁻¹ • p.1) - F (g⁻¹ • p.2)‖ = ‖F p.1 - F p.2‖ := by
        rcases (g⁻¹).2 with ⟨γ, hγ, hg⟩
        have hgs (x : ℍ) : g⁻¹ • x = γ • x := by
          rw [Subgroup.smul_def, ← hg, QuotientGroup.mk'_apply, pslMk_smul]
        rw [hgs, hgs, smul_eq_of_mem_maassSpace hF hγ, smul_eq_of_mem_maassSpace hF hγ, ← mul_sub,
          norm_mul, norm_dirichletCharacter_of_mem_gamma0 χ hγ, one_mul]
      simp only [U, mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, hd, hn]
    · rw [← Measure.restrict_apply hU.measurableSet, ← prod_restrict_univ_left]
      exact ae_iff.mp hae
  have hempty : U = ∅ := (hU.measure_eq_zero_iff _).mp hnull
  have hpt (x y : ℍ) (hxy : (dist x y).cosh < 2) : F x = F y := by
    by_contra hne
    have h7 : coshDistNormalBump 1 (dist x y).cosh ≠ 0 := by
      rw [coshDistNormalBump]
      refine mul_ne_zero (inv_ne_zero integral_coshDistBump_pos.ne') ?_
      refine (smoothTransition.pos_of_pos ?_).ne'
      push_cast
      linarith
    have h6 : (x, y) ∈ U :=
      mul_ne_zero h7 (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)))
    rw [hempty] at h6
    exact h6
  have hloc : IsLocallyConstant F := (IsLocallyConstant.iff_eventually_eq F).mpr fun x ↦ by
    have hc : ContinuousAt (fun y ↦ (dist x y).cosh) x :=
      (Real.continuous_cosh.comp (continuous_const.dist continuous_id)).continuousAt
    have hv : (dist x x).cosh < 2 := by
      simp
    filter_upwards [hc.eventually_lt continuousAt_const hv] with y hy
    exact (hpt x y hy).symm
  exact hloc.apply_eq_of_preconnectedSpace z w

variable [NeZero N]

variable (χ Λ) in
/-- **A bound for the number of orthonormal Maass cusp forms with bounded eigenvalues**: for `N ≠ 0`
and `Λ` real there is a number `M` such that every finite orthonormal family of Maass cusp forms on
`Γ₀(N)` with character `χ` and eigenvalues at most `Λ` has at most `M` elements. Let `P` be the
average over a small ball, its radius depending on `Λ`. Then `‖P f‖² ≥ 1/4` for every member `f` of
the family (`one_div_four_le_integral_sq_kernelAverage`, from Green's identity), while
`∑ |P f(z)|² ≤ C` at every point `z` of the fundamental domain (`sum_sq_norm_kernelAverage_le` and
`exists_sq_norm_integral_kernel_mul_le`, from the vanishing of the constant terms), and the
fundamental domain has finite volume. -/
lemma exists_forall_card_le : ∃ M : ℕ, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ι → ℍ → ℂ)
    (l : ι → ℝ), (∀ i, f i ∈ maassCuspSpace N χ (l i : ℂ)) → (∀ i, l i ≤ Λ) →
      (∀ i j, maassPetersson N (f i) (f j) = if i = j then 1 else 0) → Fintype.card ι ≤ M := by
  rcases exists_nat_ge (4 * |Λ|) with ⟨m, hm⟩
  have hP : ContDiff ℝ ∞ (coshDistNormalBump (2 * m + 1)) := contDiff_coshDistNormalBump
  have hP0 : ∀ c, 3 ≤ c → coshDistNormalBump (2 * m + 1) c = 0 :=
    fun _ hc ↦ coshDistNormalBump_eq_zero hc
  rcases exists_sq_norm_integral_kernel_mul_le (χ := χ) (hP.of_le (by simp)) hP0 with ⟨C, hC0, hC⟩
  refine ⟨⌈4 * (C * volume.real (gammaZeroDomain N))⌉₊, fun ι _ _ f l hf hl horth ↦ ?_⟩
  have hfin : volume (gammaZeroDomain N) < ⊤ :=
    ModularGroup.volume_iUnion_out_inv_smul_fdo_lt_top (CongruenceSubgroup.Gamma0 N)
  have hDm : MeasurableSet (gammaZeroDomain N) := (isOpen_gammaZeroDomain N).measurableSet
  have hE (i : ι) : ∫ z in gammaZeroDomain N, ‖f i z‖ ^ 2 = 1 := by
    have h : maassPetersson N (f i) (f i) = if i = i then 1 else 0 := horth i i
    rw [maassPetersson_self, ite_eq_left rfl] at h
    exact_mod_cast h
  have hf0 (i : ι) : f i ≠ 0 := fun h0 ↦ by
    have h : ∫ z in gammaZeroDomain N, ‖f i z‖ ^ 2 = 1 := hE i
    rw [h0] at h
    simp at h
  have hf1 (i : ι) : f i ∈ maassSpace N χ (l i : ℂ) ∧ f i ∈ maassCuspidalSpace N χ :=
    mem_maassCuspSpace_iff.mp (hf i)
  have hlabs (i : ι) : 4 * |l i| ≤ m + 1 := by
    rw [abs_of_nonneg (zero_le_of_mem_maassSpace (hf1 i).1 (hf0 i))]
    have h1 : l i ≤ Λ := hl i
    have h2 : Λ ≤ |Λ| := le_abs_self Λ
    linarith
  have hbound (i : ι) (z : ℍ) (hz : z ∈ gammaZeroDomain N) :
      ‖kernelAverage (coshDistNormalBump (2 * m + 1)) (f i) z‖ ^ 2 ≤ C := by
    have h : ‖kernelAverage (coshDistNormalBump (2 * m + 1)) (f i) z‖ ^ 2 ≤
        C * ∫ u in gammaZeroDomain N, ‖f i u‖ ^ 2 := hC (f i) (hf1 i).2 z hz
    rwa [hE i, mul_one] at h
  have hint (i : ι) : IntegrableOn
      (fun z ↦ ‖kernelAverage (coshDistNormalBump (2 * m + 1)) (f i) z‖ ^ 2)
        (gammaZeroDomain N) := by
    refine Measure.integrableOn_of_bounded (M := C) hfin.ne
      ((stronglyMeasurable_kernelAverage hP.continuous (hf1 i).2.1).norm.pow 2).aestronglyMeasurable
      ?_
    refine (ae_restrict_iff' hDm).mpr (.of_forall fun z hz ↦ ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hbound i z hz
  have hsum : ∑ _i : ι, (1 / 4 : ℝ) ≤ ∫ _ in gammaZeroDomain N, C := by
    refine (Finset.sum_le_sum fun i _ ↦ one_div_four_le_integral_sq_kernelAverage (hf1 i).1 (hE i)
      (hlabs i) (hint i)).trans ?_
    rw [← integral_finsetSum _ fun i _ ↦ hint i]
    refine setIntegral_mono_on (integrable_finsetSum _ fun i _ ↦ hint i)
      (integrableOn_const hfin.ne) hDm fun z hz ↦ ?_
    exact sum_sq_norm_kernelAverage_le z hC0 hP.continuous hP0 (fun i ↦ (hf1 i).2) horth
      fun g hg ↦ hC g hg z hz
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, setIntegral_const, smul_eq_mul]
    at hsum
  have h2 : (Fintype.card ι : ℝ) ≤ ⌈4 * (C * volume.real (gammaZeroDomain N))⌉₊ :=
    le_trans (by linarith) (Nat.le_ceil _)
  exact_mod_cast h2

/-- **A family of pairwise orthogonal Maass cusp forms with bounded eigenvalues is finite**: for
`N ≠ 0`, nonzero Maass cusp forms `ψ a`, `a ∈ S`, on `Γ₀(N)` with character `χ` and eigenvalues at
most `Λ`, pairwise orthogonal, have a finite index set, by normalising them
(`exists_forall_card_le`). -/
lemma finite_of_forall_maassPetersson_eq_zero {α : Type} {S : Set α} {ψ : α → ℍ → ℂ} {e : α → ℝ}
    (hf0 : ∀ a ∈ S, ψ a ≠ 0) (hf : ∀ a ∈ S, ψ a ∈ maassCuspSpace N χ (e a : ℂ))
    (hl : ∀ a ∈ S, e a ≤ Λ) (horth : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → maassPetersson N (ψ a) (ψ b) = 0) :
    S.Finite := by
  classical
  refine not_infinite.mp fun hinf ↦ ?_
  rcases exists_forall_card_le χ Λ with ⟨M, hM⟩
  rcases hinf.exists_subset_card_eq (M + 1) with ⟨t, ht, hcard⟩
  let c : t → ℂ := fun x ↦ ((√(∫ z in gammaZeroDomain N, ‖ψ x z‖ ^ 2))⁻¹ : ℂ)
  have h : Fintype.card t ≤ M := hM t (fun x ↦ c x • ψ x) (fun x ↦ e x)
    (fun x ↦ Submodule.smul_mem _ _ (hf x (ht x.2))) (fun x ↦ hl x (ht x.2)) fun x y ↦ ?_
  · rw [Fintype.card_coe, hcard] at h
    omega
  · split_ifs with hxy
    · subst hxy
      exact maassPetersson_inv_sqrt_smul_self (mem_maassCuspSpace_iff.mp (hf x (ht x.2))).1
        (hf0 x (ht x.2))
    · rw [maassPetersson_smul_smul, horth x (ht x.2) y (ht y.2) (fun he ↦ hxy (Subtype.ext he)),
        mul_zero]

variable (Λ) in
/-- **Discreteness of the spectrum of Maass cusp forms** (Selberg; LMFDB `mf.maass.spectral_index`):
for `N ≠ 0`, the Maass cusp forms on `Γ₀(N)` with character `χ` have finitely many eigenvalues below
every bound, eigenforms of different eigenvalues being orthogonal
(`maassPetersson_eq_zero_of_ne`). -/
lemma finite_maassCuspSpectrum_inter_Iic : (maassCuspSpectrum N χ ∩ Iic Λ).Finite := by
  have hch :
      ∀ x ∈ maassCuspSpectrum N χ ∩ Iic Λ, ∃ F : ℍ → ℂ, F ≠ 0 ∧ F ∈ maassCuspSpace N χ (x : ℂ) :=
    fun x hx ↦ hx.1
  choose! F hF using hch
  refine finite_of_forall_maassPetersson_eq_zero (χ := χ) (Λ := Λ) (e := id)
    (fun x hx ↦ (hF x hx).1) (fun x hx ↦ (hF x hx).2) (fun x hx ↦ hx.2) fun x hx y hy hxy ↦ ?_
  refine maassPetersson_eq_zero_of_ne (mem_maassCuspSpace_iff.mp (hF x hx).2).1
    (mem_maassCuspSpace_iff.mp (hF y hy).2).1 ?_
  rw [Complex.conj_ofReal]
  exact fun he ↦ hxy (Complex.ofReal_injective he)

variable (a) in
/-- **The eigenspaces of Maass cusp forms are finite-dimensional** (LMFDB
`mf.maass.spectral_index`, `mf.maass.mwf.dimension`): for `N ≠ 0`, the space of Maass cusp forms on
`Γ₀(N)` with character `χ` and eigenvalue `λ` has finite dimension, an orthonormal family in it
having a bounded number of elements (`exists_forall_card_le`). -/
lemma finite_maassCuspSpace : Module.Finite ℂ (maassCuspSpace N χ a) := by
  classical
  by_cases ha : conj a = a
  · rcases Complex.conj_eq_iff_real.mp ha with ⟨l, rfl⟩
    rcases exists_forall_card_le χ l with ⟨M, hM⟩
    have hmem (F : maassCuspSpace N χ (l : ℂ)) :
        MemLp (F : ℍ → ℂ) 2 (volume.restrict (gammaZeroDomain N)) :=
      memLp_of_mem_maassCuspidalSpace (mem_maassCuspSpace_iff.mp F.2).2
    let Φ : maassCuspSpace N χ (l : ℂ) →ₗ[ℂ] Lp ℂ 2 (volume.restrict (gammaZeroDomain N)) :=
      { toFun := fun F ↦ (hmem F).toLp F
        map_add' := fun F G ↦ MemLp.toLp_add (hmem F) (hmem G)
        map_smul' := fun c F ↦ MemLp.toLp_const_smul c (hmem F) }
    have hin (F G : maassCuspSpace N χ (l : ℂ)) : maassPetersson N (F : ℍ → ℂ) G = ⟪Φ G, Φ F⟫_ℂ :=
      maassPetersson_eq_inner (hmem F) (hmem G)
    have hΦ : Function.Injective Φ := by
      refine (injective_iff_map_eq_zero Φ).mpr fun F hF ↦ Subtype.ext ?_
      refine eq_zero_of_maassPetersson_self_eq_zero (mem_maassCuspSpace_iff.mp F.2).1 ?_
      rw [hin, hF, inner_zero_left]
    refine Module.rank_lt_aleph0_iff.mp <| (rank_le (n := M) fun s hs ↦ ?_).trans_lt
      (Cardinal.natCast_lt_aleph0 (n := M))
    let b : s → Lp ℂ 2 (volume.restrict (gammaZeroDomain N)) := fun F ↦ Φ F
    have hb : LinearIndependent ℂ b := hs.map' Φ (LinearMap.ker_eq_bot.mpr hΦ)
    let W : Submodule ℂ (Lp ℂ 2 (volume.restrict (gammaZeroDomain N))) := Submodule.span ℂ (range b)
    have hW : ∀ x ∈ W, ∃ F, Φ F = x := by
      have hle : W ≤ LinearMap.range Φ :=
        Submodule.span_le.mpr (by rintro _ ⟨F, rfl⟩; exact ⟨F, rfl⟩)
      exact fun x hx ↦ hle hx
    have hfd : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (finite_range b)
    have hcard : Module.finrank ℂ W = s.card := by
      rw [finrank_span_eq_card hb, Fintype.card_coe]
    let e : OrthonormalBasis (Fin (Module.finrank ℂ W)) ℂ W := stdOrthonormalBasis ℂ W
    choose f hf using fun i ↦ hW (e i : Lp ℂ 2 (volume.restrict (gammaZeroDomain N))) (e i).2
    have h : Fintype.card (Fin (Module.finrank ℂ W)) ≤ M :=
      hM (Fin (Module.finrank ℂ W)) (fun i ↦ (f i : ℍ → ℂ)) (fun _ ↦ l) (fun i ↦ (f i).2)
        (fun _ ↦ le_rfl) fun i j ↦ ?_
    · rwa [Fintype.card_fin, hcard] at h
    · rw [hin, hf, hf, ← Submodule.coe_inner, orthonormal_iff_ite.mp e.orthonormal j i]
      simp only [eq_comm]
  · have hsub : Subsingleton (maassCuspSpace N χ a) := by
      refine ⟨fun F G ↦ ?_⟩
      have h0 (H : maassCuspSpace N χ a) : (H : ℍ → ℂ) = 0 := by
        by_contra hne
        exact ha (conj_eigenvalue_of_mem_maassSpace (mem_maassCuspSpace_iff.mp H.2).1 hne)
      exact Subtype.ext ((h0 F).trans (h0 G).symm)
    infer_instance

/-- **The eigenvalue of a nonzero Maass cusp form is positive**: it is nonnegative
(`zero_le_of_mem_maassSpace`), and a Maass form with eigenvalue `0` is constant
(`apply_eq_of_mem_maassSpace_zero`), with a vanishing constant term only if it is `0`. So the
eigenvalues below `1/4` of Maass cusp forms are exceptional (LMFDB
`mf.maass.exceptional_eigenvalue`). -/
lemma zero_lt_of_mem_maassCuspSpace (hF : F ∈ maassCuspSpace N χ (l : ℂ)) (hF0 : F ≠ 0) :
    0 < l := by
  have hF1 : F ∈ maassSpace N χ (l : ℂ) ∧ F ∈ maassCuspidalSpace N χ :=
    mem_maassCuspSpace_iff.mp hF
  refine (zero_le_of_mem_maassSpace hF1.1 hF0).lt_of_ne fun hl ↦ hF0 ?_
  subst hl
  have hconst (z w : ℍ) : F z = F w := apply_eq_of_mem_maassSpace_zero z (by simpa using hF1.1) w
  have h : ∫ t in (0 : ℝ)..N, F ((1 : SL(2, ℤ)) • ofComplex ((t : ℂ) + (1 : ℝ) * Complex.I)) = 0 :=
    hF1.2.2.2.2 1 1 one_pos
  simp only [one_smul] at h
  have h1 (t : ℝ) : F (ofComplex ((t : ℂ) + (1 : ℝ) * Complex.I)) = F I := hconst _ _
  simp only [h1, intervalIntegral.integral_const, sub_zero] at h
  have hN : ((N : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  have h2 : F I = 0 := (mul_eq_zero.mp h).resolve_left hN
  funext z
  rw [hconst z I, h2]
  rfl

end UpperHalfPlane
