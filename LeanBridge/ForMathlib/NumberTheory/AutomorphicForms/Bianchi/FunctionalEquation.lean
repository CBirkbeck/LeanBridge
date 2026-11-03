import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.NewformBasis
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The functional equation of the L-function of a Bianchi newform

Let `K` be an imaginary quadratic field of class number `1`, embedded in `ℂ` by `σ`, and `F` a
Bianchi newform of even weight `k = 2m ≥ 1` and level `(n)`, with `F ∣ W_n = λ F`, `λ = ±1`, for the
Fricke involution `W_n`. The **central function** `ψ(y) = y^m F_m(0, y)`
(`HyperbolicThreeSpace.bianchiCentralFunction`) satisfies `ψ(1 / (|n| y)) = (-1)^m λ ψ(y)`, since
`W_n (0, y) = (0, 1 / (|n| y))` with an antidiagonal automorphy factor, and it decays rapidly at
`∞`, hence at `0`. So its Mellin transform `M` is entire and `|n|^{-w} M(-w) = (-1)^m λ M(w)`. On
the other hand, the Fourier–Bessel expansion `ψ(y) = ∑_{α ≠ 0} c(α) y^{m+1} K₀(4π|α|y / √|Δ|)`, with
`c(α) = O(|α|^{m+1})` and `∫₀^∞ t^{u-1} K₀(t) dt = 2^{u-2} Γ(u/2)²`, shows for `Re(2s) > m + 3` that
`M(2s - m - 1)` is `(4π / √|Δ|)^{-2s} 2^{2s-2} Γ(s)² ∑_{α ≠ 0} c(α) |α|^{-2s}`. Here
`∑_{α ≠ 0} c(α) |α|^{-2s}` is `w` times the Dirichlet series `L(F, s) = ∑_𝔞 c(𝔞) N(𝔞)^{-s}`, `w` the
number of units, as `c(uα) = c(α)`.

So the completed L-function `Λ(F, s) = |n|^s M(2s - m - 1)` satisfies
`Λ(F, m + 1 - s) = (-1)^m λ Λ(F, s)`. If `F` has sign `ε`, that is `λ = -ε`, **the sign of the
functional equation is `(-1)^{m+1} ε`**, and the order of vanishing `r` of `Λ(F, s)` at the centre
satisfies `(-1)^{m+1} ε = (-1)^r`.

The knowl says that the sign of `F`, minus the eigenvalue of `W_n`, "is equal to the sign of the
functional equation": this holds for `k ≡ 2` modulo `4`, in particular for `k = 2`, while for
`k ≡ 0` modulo `4` the sign of the functional equation is the eigenvalue of `W_n` itself, for the
action of `W_n` by the slash operator `bianchiSlash` of a representative in `SL(2, ℂ)`.

The coefficient bound `c(α) = O(|α|^{k/2+1})` of this file gives the convergence of the Dirichlet
series for `Re s > k/4 + 3/2` only. Its absolute convergence for `Re s > k/4 + 1`, and the
`AnalyticLFunction` of `F`, which gives the analytic rank of the LMFDB, are in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.NewformLFunction`.

## Main definitions

* `HyperbolicThreeSpace.bianchiCentralFunction`: the central function of `F`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.completedL`: the completed L-function `Λ(F, s)`.

## Main results

* `HyperbolicThreeSpace.mellin_besselK_zero`: the Mellin transform of `K₀`.
* `HyperbolicThreeSpace.exists_height_pow_mul_norm_le_exp`: the exponential decay of a cusp form.
* `HyperbolicThreeSpace.bianchiCentralFunction_mul_inv`: the central function under `W_n`.
* `HyperbolicThreeSpace.mellin_bianchiCentralFunction_neg`: the functional equation of its Mellin
  transform.
* `HyperbolicThreeSpace.differentiable_mellin_bianchiCentralFunction`: its Mellin transform is
  entire.
* `HyperbolicThreeSpace.hasSum_mellin_bianchiCentralFunction`: its Mellin transform as a Dirichlet
  series.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.completedL_add_one_sub`: the functional equation of
  the L-function of a newform, with its sign.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.differentiable_completedL`: `Λ(F, s)` is entire.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.summable_coeff_mul_norm_cpow`: the Dirichlet series
  converges for `Re(2s) > k/2 + 3`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.completedL_eq_tsum`: `Λ(F, s)` in terms of the
  Dirichlet series.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.tsum_coeff_mul_norm_cpow_eq`: the Dirichlet series
  over the ideals.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.exists_completedL_ne_zero`: `Λ(F, s)` is not
  identically `0`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.neg_one_pow_mul_eq_neg_one_pow_analyticOrderNatAt`:
  the parity of the order of vanishing at the centre.
-/

open Complex Filter Matrix MeasureTheory Module NumberField Set Asymptotics Topology
  HilbertModularGroup

open Submodule (IsPrincipal)

open scoped ComplexConjugate MatrixGroups nonZeroDivisors Real

namespace HyperbolicThreeSpace

lemma besselK_zero_eq_mellin {x : ℝ} (hx : 0 < x) :
    besselK 0 x = 2⁻¹ * mellin (fun w : ℝ ↦ (rexp (-w - x ^ 2 / (4 * w)) : ℂ)) 0 := by
  have h₁ : besselK 0 x = 2⁻¹ * mellin (fun t : ℝ ↦ (rexp (-(x / 2) * (t + t⁻¹)) : ℂ)) 0 :=
    rfl
  have h₂ : (fun w : ℝ ↦ (rexp (-w - x ^ 2 / (4 * w)) : ℂ)) = fun w : ℝ ↦
      (fun t : ℝ ↦ (fun s : ℝ ↦ (rexp (-(x / 2) * (s + s⁻¹)) : ℂ)) t⁻¹) (2 / x * w) := by
    funext w
    congr 2
    by_cases hw : w = 0
    · simp [hw]
    · have hx₀ : x ≠ 0 := hx.ne'
      simp only [mul_inv]
      field_simp
      ring1
  rw [h₁, h₂, mellin_comp_mul_left (fun t : ℝ ↦ (fun s : ℝ ↦ (rexp (-(x / 2) * (s + s⁻¹)) : ℂ)) t⁻¹)
    0 (by positivity : 0 < 2 / x), mellin_comp_inv (fun s : ℝ ↦ (rexp (-(x / 2) * (s + s⁻¹)) : ℂ))]
  simp

lemma mellin_exp_neg_mul_sq {u : ℂ} (hu : 0 < u.re) {b : ℝ} (hb : 0 < b) :
    mellin (fun x : ℝ ↦ (rexp (-(b * x ^ 2)) : ℂ)) u =
      2⁻¹ * (1 / (b : ℂ)) ^ (u / 2) * Gamma (u / 2) := by
  have h₁ :
      (fun x : ℝ ↦ (rexp (-(b * x ^ 2)) : ℂ)) = fun x : ℝ ↦ (rexp (-(b * x ^ (2 : ℝ))) : ℂ) := by
    funext x
    rw [Real.rpow_two]
  have hu₂ : 0 < (u / 2).re := by
    simpa using hu
  have h₂ : mellin (fun t : ℝ ↦ (rexp (-(b * t)) : ℂ)) (u / 2) =
      (1 / (b : ℂ)) ^ (u / 2) * Gamma (u / 2) := by
    rw [← integral_cpow_mul_exp_neg_mul_Ioi hu₂ hb, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    simp
  have h₃ : mellin (fun x : ℝ ↦ (rexp (-(b * x ^ (2 : ℝ))) : ℂ)) u =
      (|(2 : ℝ)|)⁻¹ • mellin (fun t : ℝ ↦ (rexp (-(b * t)) : ℂ)) (u / ((2 : ℝ) : ℂ)) :=
    mellin_comp_rpow (fun t : ℝ ↦ (rexp (-(b * t)) : ℂ)) u 2
  have h₄ : ((2⁻¹ : ℝ) : ℂ) = 2⁻¹ := by
    norm_num
  rw [ofReal_ofNat, h₂, abs_of_pos (two_pos : (0 : ℝ) < 2), real_smul, h₄] at h₃
  rw [h₁, h₃, mul_assoc]

/-- The integrand `x^(u-1) w⁻¹ e^{-w - x² / (4w)}` of the double integral computing the Mellin
transform of `K₀`. -/
noncomputable def besselKZeroKernel (u : ℂ) (x w : ℝ) : ℂ :=
  (x : ℂ) ^ (u - 1) * ((w : ℂ) ^ ((0 : ℂ) - 1) * (rexp (-w - x ^ 2 / (4 * w)) : ℂ))

lemma measurable_besselKZeroKernel (u : ℂ) :
    Measurable (Function.uncurry (besselKZeroKernel u)) := by
  unfold besselKZeroKernel Function.uncurry
  fun_prop

lemma norm_besselKZeroKernel (u : ℂ) {x w : ℝ} (hx : 0 < x) (hw : 0 < w) :
    ‖besselKZeroKernel u x w‖ =
      (w⁻¹ * rexp (-w)) * (x ^ (u.re - 1) * rexp (-(1 / (4 * w)) * x ^ (2 : ℝ))) := by
  have h₁ : rexp (-w - x ^ 2 / (4 * w)) = rexp (-w) * rexp (-(1 / (4 * w)) * x ^ (2 : ℝ)) := by
    rw [← Real.exp_add, Real.rpow_two]
    congr 1
    field_simp
    ring1
  have e : ((0 : ℂ) - 1).re = -1 := by
    simp
  rw [besselKZeroKernel, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx,
    norm_cpow_eq_rpow_re_of_pos hw, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, h₁, e,
    Real.rpow_neg_one, sub_re, one_re]
  ring1

lemma integrable_besselKZeroKernel {u : ℂ} (hu : 0 < u.re) :
    Integrable (Function.uncurry (besselKZeroKernel u))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry (besselKZeroKernel u))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) :=
    (measurable_besselKZeroKernel u).aestronglyMeasurable
  refine (integrable_prod_iff' hmeas).mpr ⟨?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun w (hw : 0 < w) ↦ ?_)
    have hb : 0 < 1 / (4 * w) := by
      positivity
    have h₁ : IntegrableOn (fun x : ℝ ↦ (w⁻¹ * rexp (-w)) *
        (x ^ (u.re - 1) * rexp (-(1 / (4 * w)) * x ^ (2 : ℝ)))) (Ioi 0) :=
      (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) two_pos hb).const_mul _
    refine (integrable_norm_iff (measurable_besselKZeroKernel u |>.comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mp ?_
    refine h₁.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (norm_besselKZeroKernel u hx hw).symm
  · have hσ : 0 < u.re / 2 := half_pos hu
    have h₁ : Integrable (fun x : ℝ ↦ 2⁻¹ * (4 : ℝ) ^ (u.re / 2) * Real.Gamma (u.re / 2) *
        (rexp (-x) * x ^ (u.re / 2 - 1))) (volume.restrict (Ioi 0)) :=
      (Real.GammaIntegral_convergent hσ).const_mul _
    refine h₁.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w (hw : 0 < w)
    have hb : 0 < 1 / (4 * w) := by
      positivity
    have h₂ : ∫ x, ‖Function.uncurry (besselKZeroKernel u) (x, w)‖ ∂volume.restrict (Ioi 0) =
        ∫ x in Ioi 0, (w⁻¹ * rexp (-w)) * (x ^ (u.re - 1) * rexp (-(1 / (4 * w)) * x ^ (2 : ℝ))) :=
      setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ norm_besselKZeroKernel u hx hw
    rw [h₂, integral_const_mul, integral_rpow_mul_exp_neg_mul_rpow two_pos
      (by linarith : -1 < u.re - 1) hb]
    have e₁ : (u.re - 1 + 1) / 2 = u.re / 2 := by
      ring1
    have e₂ : -(u.re - 1 + 1) / 2 = -(u.re / 2) := by
      ring1
    have e₃ : (1 / (4 * w))⁻¹ = 4 * w := by
      rw [one_div, inv_inv]
    rw [e₁, e₂, Real.rpow_neg hb.le, ← Real.inv_rpow hb.le, e₃, Real.mul_rpow (by norm_num) hw.le,
      Real.rpow_sub hw, Real.rpow_one]
    field_simp

/-- **The Mellin transform of `K₀`**: `∫₀^∞ t^(u-1) K₀(t) dt = 2^(u-2) Γ(u/2)²` for `Re u > 0`. -/
lemma mellin_besselK_zero {u : ℂ} (hu : 0 < u.re) :
    mellin (fun t : ℝ ↦ besselK 0 t) u = 2 ^ (u - 2) * Gamma (u / 2) ^ 2 := by
  have hu₂ : 0 < (u / 2).re := by
    simpa using hu
  have h₁ : mellin (fun t : ℝ ↦ besselK 0 t) u =
      2⁻¹ * ∫ x in Ioi (0 : ℝ), ∫ w in Ioi (0 : ℝ), besselKZeroKernel u x w := by
    rw [mellin, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) ↦ ?_
    simp only [besselK_zero_eq_mellin hx, mellin, besselKZeroKernel, smul_eq_mul]
    rw [integral_const_mul]
    ring1
  have h₂ (w : ℝ) (hw : w ∈ Ioi (0 : ℝ)) : ∫ x in Ioi (0 : ℝ), besselKZeroKernel u x w =
      2⁻¹ * 2 ^ u * Gamma (u / 2) * ((rexp (-w) : ℂ) * (w : ℂ) ^ (u / 2 - 1)) := by
    have hw₀ : 0 < w := hw
    have hb : 0 < 1 / (4 * w) := by
      positivity
    have hw' : (w : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw₀.ne'
    have e₁ : ∫ x in Ioi (0 : ℝ), besselKZeroKernel u x w =
        (w : ℂ) ^ ((0 : ℂ) - 1) * (rexp (-w) : ℂ) *
          mellin (fun x : ℝ ↦ (rexp (-((1 / (4 * w)) * x ^ 2)) : ℂ)) u := by
      rw [mellin, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
      have e₂ : rexp (-w - x ^ 2 / (4 * w)) = rexp (-w) * rexp (-((1 / (4 * w)) * x ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
        field_simp
        ring1
      simp only [besselKZeroKernel, e₂]
      push_cast
      ring1
    have e₃ : (1 / ((1 / (4 * w) : ℝ) : ℂ)) ^ (u / 2) = 2 ^ u * (w : ℂ) ^ (u / 2) := by
      have e₄ : (1 / ((1 / (4 * w) : ℝ) : ℂ)) = ((4 : ℝ) : ℂ) * (w : ℂ) := by
        push_cast
        field_simp
      have e₅ : ((4 : ℝ) : ℂ) ^ (u / 2) = 2 ^ u := by
        have e₆ : ((4 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) * ((2 : ℝ) : ℂ) := by
          norm_num
        rw [e₆, mul_cpow_ofReal_nonneg (by norm_num) (by norm_num), ofReal_ofNat,
          ← cpow_add _ _ two_ne_zero, add_halves]
      rw [e₄, mul_cpow_ofReal_nonneg (by norm_num) hw₀.le, e₅]
    rw [e₁, mellin_exp_neg_mul_sq hu hb, e₃, sub_eq_add_neg (u / 2), cpow_add _ _ hw', zero_sub,
      cpow_neg_one]
    field_simp
  have h₃ : ∫ x in Ioi (0 : ℝ), ∫ w in Ioi (0 : ℝ), besselKZeroKernel u x w =
      ∫ w in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), besselKZeroKernel u x w :=
    integral_integral_swap (integrable_besselKZeroKernel hu)
  have h₄ : ∫ w in Ioi (0 : ℝ), (rexp (-w) : ℂ) * (w : ℂ) ^ (u / 2 - 1) = Gamma (u / 2) :=
    (Gamma_eq_integral hu₂).symm
  have h₅ : (2 : ℂ) ^ (u - 2) = 2 ^ u / 4 := by
    rw [cpow_sub _ _ two_ne_zero, cpow_ofNat]
    norm_num
  rw [h₁, h₃, setIntegral_congr_fun measurableSet_Ioi h₂, integral_const_mul, h₄, h₅]
  ring1

lemma mellinConvergent_besselK_zero {u : ℂ} (hu : 0 < u.re) :
    MellinConvergent (fun t : ℝ ↦ besselK 0 t) u := by
  have h₁ : Integrable
      (fun x : ℝ ↦ ∫ w in Ioi (0 : ℝ), Function.uncurry (besselKZeroKernel u) (x, w))
      (volume.restrict (Ioi 0)) := (integrable_besselKZeroKernel hu).integral_prod_left
  refine (h₁.const_mul 2⁻¹).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
  rw [besselK_zero_eq_mellin hx, mellin, smul_eq_mul]
  simp only [Function.uncurry, besselKZeroKernel, smul_eq_mul]
  rw [integral_const_mul]
  ring1

lemma integral_norm_cpow_smul_besselK (u : ℂ) {b : ℝ} (hb : 0 < b) :
    ∫ y in Ioi (0 : ℝ), ‖(y : ℂ) ^ (u - 1) • besselK 0 (b * y)‖ =
      b ^ (-u.re) * ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (u - 1) • besselK 0 t‖ := by
  have h₁ : ∫ x in Ioi (0 : ℝ), ‖((b * x : ℝ) : ℂ) ^ (u - 1) • besselK 0 (b * x)‖ =
      b⁻¹ • ∫ x in Ioi (b * 0), ‖(x : ℂ) ^ (u - 1) • besselK 0 x‖ :=
    integral_comp_mul_left_Ioi (fun t : ℝ ↦ ‖(t : ℂ) ^ (u - 1) • besselK 0 t‖) 0 hb
  rw [mul_zero, smul_eq_mul] at h₁
  have h₂ : ∀ y ∈ Ioi (0 : ℝ), ‖(y : ℂ) ^ (u - 1) • besselK 0 (b * y)‖ =
      b ^ (-(u.re - 1)) * ‖((b * y : ℝ) : ℂ) ^ (u - 1) • besselK 0 (b * y)‖ := by
    intro y (hy : 0 < y)
    rw [norm_smul, norm_smul, norm_cpow_eq_rpow_re_of_pos hy,
      norm_cpow_eq_rpow_re_of_pos (mul_pos hb hy), sub_re, one_re, Real.mul_rpow hb.le hy.le,
      ← mul_assoc, ← mul_assoc, ← Real.rpow_add hb, neg_add_cancel, Real.rpow_zero, one_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi h₂, integral_const_mul, h₁, ← mul_assoc]
  congr 1
  rw [← Real.rpow_neg_one, ← Real.rpow_add hb]
  congr 1
  ring1

variable {K : Type*} [Field K] {σ : K →+* ℂ} {δ : ℂ} {x : K} {k : ℕ} {𝔑 : Ideal (𝓞 K)}
  {F : HyperbolicThreeSpace → Fin (k + 1) → ℂ} {c : 𝓞 K → ℂ}

lemma symPowMatrix_antidiag_apply (a b : ℂ) (i j : Fin (k + 1)) :
    symPowMatrix k !![0, a; b, 0] i j =
      if (j : ℕ) + i = k then a ^ (j : ℕ) * b ^ (i : ℕ) else 0 := by
  have hi : (i : ℕ) ≤ k := Nat.lt_succ_iff.mp i.2
  rw [symPowMatrix, Matrix.of_apply, Finset.sum_eq_single 0]
  · simp only [Nat.sub_zero]
    simp only [Matrix.of_apply, Matrix.cons_val_zero]
    split_ifs with h
    · have e₁ : k - (i : ℕ) = j := by
        omega
      have e₂ : k - (i : ℕ) - (j : ℕ) = 0 := by
        omega
      rw [e₂, e₁, Nat.choose_self]
      simp
    · by_cases h' : (j : ℕ) ≤ k - i
      · have e : k - (i : ℕ) - (j : ℕ) ≠ 0 := by
          omega
        rw [zero_pow e]
        simp
      · rw [Nat.choose_eq_zero_of_lt (not_le.mp h')]
        simp
  · intro q _ hq
    simp [hq]
  · simp

lemma symPowMatrix_antidiag_mulVec_apply (hk : Even k) (a b : ℂ) (v : Fin (k + 1) → ℂ) :
    (symPowMatrix k !![0, a; b, 0] *ᵥ v) ⟨k / 2, by omega⟩ =
      (a * b) ^ (k / 2) * v ⟨k / 2, by omega⟩ := by
  rcases hk with ⟨m, rfl⟩
  have e : (m + m) / 2 = m := by
    omega
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (⟨(m + m) / 2, by omega⟩ : Fin (m + m + 1))]
  · rw [symPowMatrix_antidiag_apply, ite_eq_left (by simp; omega), mul_pow]
  · intro j _ hj
    rw [symPowMatrix_antidiag_apply, ite_eq_right, zero_mul]
    intro h
    exact hj (Fin.ext (by simp at h ⊢; omega))
  · simp

variable (k F) in
/-- The **central function** `y ↦ y^{k/2} F_{k/2}(0, y)` of `F : ℋ₃ → ℂ^{k+1}`: for a Bianchi cusp
form, its Mellin transform is the completed L-function of `F`. -/
noncomputable def bianchiCentralFunction (y : ℝ) : ℂ :=
  (y : ℂ) ^ (k / 2) * extend F (0, y) ⟨k / 2, by omega⟩

lemma norm_extend_apply_le (i : Fin (k + 1)) {y : ℝ} (hy : 0 < y) :
    ‖extend F (0, y) i‖ ≤ ‖F (.mk (WithLp.toLp 2 (0, y)) hy)‖ := by
  rw [extend, dite_eq_left hy]
  exact norm_le_pi_norm _ i

lemma continuousOn_bianchiCentralFunction
    (hF : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords) :
    ContinuousOn (bianchiCentralFunction k F) (Ioi 0) := by
  intro y (hy : 0 < y)
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.mul (by fun_prop) ?_
  have h₁ : ContinuousAt (extend F) (0, y) := (hF (.mk (WithLp.toLp 2 (0, y)) hy)).continuousAt
  have h₂ : ContinuousAt (fun t : ℝ ↦ extend F ((0 : ℂ), t)) y :=
    ContinuousAt.comp (f := fun t : ℝ ↦ ((0 : ℂ), t)) h₁ (by fun_prop)
  exact (continuous_apply _).continuousAt.comp h₂

variable {n : 𝓞 K} [NeZero n]

variable (σ n) in
lemma apply_coe_ne_zero : σ (n : K) ≠ 0 :=
  (map_ne_zero σ).mpr (RingOfIntegers.coe_ne_zero_iff.mpr (NeZero.ne n))

variable (σ n) in
lemma norm_apply_pos : 0 < ‖σ (n : K)‖ :=
  norm_pos_iff.mpr (apply_coe_ne_zero σ n)

variable (σ n) in
lemma ofReal_norm_apply_ne_zero : ((‖σ (n : K)‖ : ℝ) : ℂ) ≠ 0 :=
  ofReal_ne_zero.mpr (norm_apply_pos σ n).ne'

lemma slRepresentative_frickeMatrix_apply_zero_zero :
    (slRepresentative σ (frickeMatrix n) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 := by
  rw [coe_slRepresentative_frickeMatrix]
  simp

lemma slRepresentative_frickeMatrix_apply_one_one :
    (slRepresentative σ (frickeMatrix n) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0 := by
  rw [coe_slRepresentative_frickeMatrix]
  simp

lemma slRepresentative_frickeMatrix_apply_one_zero :
    (slRepresentative σ (frickeMatrix n) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = σ n ^ (2⁻¹ : ℂ) := by
  have hs : (σ (n : K) ^ (2⁻¹ : ℂ)) ^ 2 = σ n := cpow_ofNat_inv_pow _ 2
  have hs₀ : σ (n : K) ^ (2⁻¹ : ℂ) ≠ 0 :=
    fun h ↦ apply_coe_ne_zero σ n (by rw [← hs, h, zero_pow two_ne_zero])
  rw [coe_slRepresentative_frickeMatrix]
  simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    smul_eq_mul]
  rw [inv_mul_eq_div, div_eq_iff hs₀, ← sq, hs]

/-- **The central function under the Fricke involution**: if `F ∣ W_n = a F`, `k` even, then
`ψ(1 / (|n| y)) = (-1)^{k/2} a ψ(y)` for the central function `ψ` of `F`. -/
lemma bianchiCentralFunction_mul_inv (hk : Even k) {a : ℂ}
    (h : bianchiSlash k (slRepresentative σ (frickeMatrix n)) F = a • F) {y : ℝ} (hy : 0 < y) :
    bianchiCentralFunction k F (‖σ n‖ * y)⁻¹ =
      (-1) ^ (k / 2) * a * bianchiCentralFunction k F y := by
  have hs : (σ (n : K) ^ (2⁻¹ : ℂ)) ^ 2 = σ n := cpow_ofNat_inv_pow _ 2
  have h₀₀ : (slRepresentative σ (frickeMatrix n) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 :=
    slRepresentative_frickeMatrix_apply_zero_zero
  have h₁₁ : (slRepresentative σ (frickeMatrix n) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0 :=
    slRepresentative_frickeMatrix_apply_one_one
  have h₁₀ : (slRepresentative σ (frickeMatrix n) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
      σ n ^ (2⁻¹ : ℂ) := slRepresentative_frickeMatrix_apply_one_zero
  have hnorm : normSq (σ (n : K) ^ (2⁻¹ : ℂ)) = ‖σ (n : K)‖ := by
    rw [normSq_eq_norm_sq, ← norm_pow, hs]
  have hmul : (σ (n : K) ^ (2⁻¹ : ℂ)) * conj (σ (n : K) ^ (2⁻¹ : ℂ)) = (‖σ (n : K)‖ : ℂ) := by
    rw [mul_conj, hnorm]
  generalize σ (n : K) ^ (2⁻¹ : ℂ) = s at hs hnorm hmul h₁₀
  let z : HyperbolicThreeSpace := .mk (WithLp.toLp 2 (0, y)) hy
  have hz : z.coords = (0, y) := rfl
  have hD : moebiusDenom (slRepresentative σ (frickeMatrix n)) (0, y) = ‖σ (n : K)‖ * y ^ 2 := by
    simp only [moebiusDenom, h₁₁, h₁₀, mul_zero, map_zero, zero_add, hnorm]
  have hgz : (slRepresentative σ (frickeMatrix n) • z).coords = (0, (‖σ (n : K)‖ * y)⁻¹) := by
    rw [coords_smul, hz, moebius, hD]
    refine Prod.ext ?_ ?_
    · simp [h₀₀, h₁₁]
    · field_simp
  have hJ : (automorphyFactor (slRepresentative σ (frickeMatrix n)) (0, y))⁻¹ =
      !![0, s * y / (‖σ (n : K)‖ * y ^ 2 : ℝ); -(conj s * y) / (‖σ (n : K)‖ * y ^ 2 : ℝ), 0] := by
    rw [inv_automorphyFactor, hD]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h₁₁, h₁₀, div_eq_inv_mul]
  have h₁ : bianchiSlash k (slRepresentative σ (frickeMatrix n)) F z ⟨k / 2, by omega⟩ =
      (a • F) z ⟨k / 2, by omega⟩ := congrFun (congrFun h z) ⟨k / 2, by omega⟩
  rw [bianchiSlash, hz, hJ, symPowMatrix_antidiag_mulVec_apply hk, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul] at h₁
  have hF₁ : F (slRepresentative σ (frickeMatrix n) • z) = extend F (0, (‖σ (n : K)‖ * y)⁻¹) := by
    rw [← hgz, extend_coords]
  have hF₂ : F z = extend F (0, y) := by
    rw [← hz, extend_coords]
  rw [hF₁, hF₂] at h₁
  have hy₀ : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have hn₀ : ((‖σ (n : K)‖ : ℝ) : ℂ) ≠ 0 := ofReal_norm_apply_ne_zero σ n
  have hAB : s * y / (‖σ (n : K)‖ * y ^ 2 : ℝ) * (-(conj s * y) / (‖σ (n : K)‖ * y ^ 2 : ℝ)) =
      -((‖σ (n : K)‖ * y ^ 2 : ℝ) : ℂ)⁻¹ := by
    have e : s * y / (‖σ (n : K)‖ * y ^ 2 : ℝ) * (-(conj s * y) / (‖σ (n : K)‖ * y ^ 2 : ℝ)) =
        -((s * conj s) * y ^ 2) / ((‖σ (n : K)‖ * y ^ 2 : ℝ) : ℂ) ^ 2 := by
      ring1
    rw [e, hmul]
    push_cast
    field_simp
  rw [hAB] at h₁
  rw [bianchiCentralFunction, bianchiCentralFunction]
  generalize extend F (0, (‖σ (n : K)‖ * y)⁻¹) ⟨k / 2, by omega⟩ = P at h₁ ⊢
  generalize extend F (0, y) ⟨k / 2, by omega⟩ = Q at h₁ ⊢
  have hP : P = (-((‖σ (n : K)‖ * y ^ 2 : ℝ) : ℂ)) ^ (k / 2) * (a * Q) := by
    rw [← h₁, ← mul_assoc, ← mul_pow]
    have e : -((‖σ (n : K)‖ * y ^ 2 : ℝ) : ℂ) * -((‖σ (n : K)‖ * y ^ 2 : ℝ) : ℂ)⁻¹ = 1 := by
      rw [neg_mul_neg, mul_inv_cancel₀]
      push_cast
      exact mul_ne_zero hn₀ (pow_ne_zero 2 hy₀)
    rw [e, one_pow, one_mul]
  have e : (((‖σ (n : K)‖ * y)⁻¹ : ℝ) : ℂ) * -((‖σ (n : K)‖ * y ^ 2 : ℝ) : ℂ) = -1 * (y : ℂ) := by
    push_cast
    field_simp
  rw [hP, ← mul_assoc, ← mul_pow, e, mul_pow]
  ring1

/-- **The functional equation of the Mellin transform of the central function**: if `F ∣ W_n = a F`,
`k` even, then `|n|^{-w} M(-w) = (-1)^{k/2} a M(w)`, for `M` the Mellin transform of the central
function of `F`. -/
lemma mellin_bianchiCentralFunction_neg (hk : Even k) {a : ℂ}
    (h : bianchiSlash k (slRepresentative σ (frickeMatrix n)) F = a • F) (w : ℂ) :
    ((‖σ (n : K)‖ : ℝ) : ℂ) ^ (-w) * mellin (bianchiCentralFunction k F) (-w) =
      (-1) ^ (k / 2) * a * mellin (bianchiCentralFunction k F) w := by
  have h₁ : mellin (fun y : ℝ ↦ bianchiCentralFunction k F (‖σ (n : K)‖ * y)⁻¹) w =
      ((‖σ (n : K)‖ : ℝ) : ℂ) ^ (-w) • mellin (fun t : ℝ ↦ bianchiCentralFunction k F t⁻¹) w :=
    mellin_comp_mul_left (fun t : ℝ ↦ bianchiCentralFunction k F t⁻¹) w (norm_apply_pos σ n)
  rw [mellin_comp_inv (bianchiCentralFunction k F), smul_eq_mul] at h₁
  rw [← h₁, ← smul_eq_mul, ← mellin_const_smul]
  exact setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) ↦ by
    simp only [smul_eq_mul, bianchiCentralFunction_mul_inv hk h hy]

variable [NumberField K]

variable (K) in
lemma abs_discr_pos : 0 < |(discr K : ℝ)| :=
  abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))

lemma bianchiWhittakerTerm_zero_apply (hk : Even k) (hδ : ‖δ‖ = √|(discr K : ℝ)|) (α : 𝓞 K)
    (y : ℝ) : bianchiWhittakerTerm σ δ k c (0, y) α ⟨k / 2, by omega⟩ =
      c α * y * besselK 0 (4 * π * ‖σ α / δ‖ * y) := by
  have e₁ : ((k / 2 : ℕ) : ℂ) - (k : ℂ) / 2 = 0 := by
    rcases hk with ⟨m, rfl⟩
    rw [(by omega : (m + m) / 2 = m)]
    push_cast
    ring1
  have e₂ : 4 * π * ‖(σ α : ℂ)‖ * y / √|(discr K : ℝ)| = 4 * π * ‖σ α / δ‖ * y := by
    rw [norm_div, hδ]
    ring1
  simp only [bianchiWhittakerTerm, bianchiWhittakerVector, Pi.smul_apply]
  rw [e₁, e₂]
  simp

/-- **The Mellin transform of the central function as a Dirichlet series**: if `F` has the
Fourier–Bessel coefficients `c(α) = O(|α|^{k/2+1})`, then for `Re u > k/2 + 3`,
`M(u - k/2 - 1) = ∑_{α ≠ 0} c(α) (4π|α/δ|)^{-u} 2^{u-2} Γ(u/2)²`. -/
lemma hasSum_mellin_bianchiCentralFunction (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) (hk : Even k)
    (hδ : δ ^ 2 = discr K) (hc : HasBianchiWhittakerExpansion σ δ k (extend F) c) {E : ℝ}
    (hcE : ∀ α : 𝓞 K, α ≠ 0 → ‖c α‖ ≤ E * ‖σ α / δ‖ ^ (k / 2 + 1)) {u : ℂ}
    (hu : (k / 2 : ℕ) + 3 < u.re) : HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦
      c α * (((4 * π * ‖σ α.1 / δ‖ : ℝ) : ℂ) ^ (-u) * (2 ^ (u - 2) * Gamma (u / 2) ^ 2)))
        (mellin (bianchiCentralFunction k F) (u - (k / 2 : ℕ) - 1)) := by
  have hδ₀ : δ ≠ 0 := ne_zero_of_sq_eq_discr K hδ
  have hδ' : 0 < ‖δ‖ := norm_pos_iff.mpr hδ₀
  have hδn : ‖δ‖ = √|(discr K : ℝ)| := norm_eq_sqrt_of_sq_eq_discr hδ
  have hu₀ : 0 < u.re := by
    have hm : (0 : ℝ) ≤ (k / 2 : ℕ) := Nat.cast_nonneg _
    linarith
  have hb (α : {α : 𝓞 K // α ≠ 0}) : 0 < 4 * π * ‖σ (α.1 : K) / δ‖ := by
    have hμ : 0 < ‖σ (α.1 : K) / δ‖ := norm_pos_iff.mpr (div_ne_zero ((map_ne_zero σ).mpr
      (RingOfIntegers.coe_ne_zero_iff.mpr α.2)) hδ₀)
    positivity
  let G : {α : 𝓞 K // α ≠ 0} → ℝ → ℂ := fun α y ↦
    (y : ℂ) ^ (u - 1) * (c α * besselK 0 (4 * π * ‖σ α.1 / δ‖ * y))
  have hpt (y : ℝ) (hy : 0 < y) : HasSum (fun α ↦ G α y)
      ((y : ℂ) ^ (u - (k / 2 : ℕ) - 1 - 1) • bianchiCentralFunction k F y) := by
    have hy₀ : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
    have h₁ : HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦
        bianchiWhittakerTerm σ δ k c (0, y) α ⟨k / 2, by omega⟩)
        (extend F (0, y) ⟨k / 2, by omega⟩) := (Pi.hasSum.mp (hc (0, y) hy)) ⟨k / 2, by omega⟩
    simp only [bianchiWhittakerTerm_zero_apply hk hδn] at h₁
    have e : (y : ℂ) ^ (u - (k / 2 : ℕ) - 1 - 1) • bianchiCentralFunction k F y =
        (y : ℂ) ^ (u - (k / 2 : ℕ) - 1 - 1) * (y : ℂ) ^ (k / 2) *
          extend F (0, y) ⟨k / 2, by omega⟩ := by
      rw [bianchiCentralFunction, smul_eq_mul, mul_assoc]
    rw [e]
    refine (h₁.mul_left _).congr_fun fun α ↦ ?_
    have e₂ : (y : ℂ) ^ (u - 1) = (y : ℂ) ^ (u - (k / 2 : ℕ) - 1 - 1 + (k / 2 : ℕ) + 1) := by
      congr 1
      ring1
    simp only [G]
    rw [e₂, cpow_add _ _ hy₀, cpow_add _ _ hy₀, cpow_natCast, cpow_one]
    ring1
  have hconv (α : {α : 𝓞 K // α ≠ 0}) : IntegrableOn (G α) (Ioi 0) := by
    have h₁ : MellinConvergent (fun y : ℝ ↦ besselK 0 (4 * π * ‖σ α.1 / δ‖ * y)) u :=
      (MellinConvergent.comp_mul_left (hb α)).mpr (mellinConvergent_besselK_zero hu₀)
    have h₂ : IntegrableOn (fun y : ℝ ↦ c α * ((y : ℂ) ^ (u - 1) •
        besselK 0 (4 * π * ‖σ α.1 / δ‖ * y))) (Ioi 0) := h₁.const_mul (c α)
    refine h₂.congr_fun (fun y _ ↦ ?_) measurableSet_Ioi
    beta_reduce
    ring1
  have hM₀ : 0 ≤ ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (u - 1) • besselK 0 t‖ :=
    integral_nonneg fun _ ↦ norm_nonneg _
  have hnorm (α : {α : 𝓞 K // α ≠ 0}) : ∫ y in Ioi (0 : ℝ), ‖G α y‖ =
      ‖c α‖ * ((4 * π * ‖σ α.1 / δ‖) ^ (-u.re) *
        ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (u - 1) • besselK 0 t‖) := by
    rw [← integral_norm_cpow_smul_besselK u (hb α), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
    simp only [G, smul_eq_mul, norm_mul]
    ring1
  have hsum : Summable fun α ↦ ∫ y in Ioi (0 : ℝ), ‖G α y‖ := by
    simp only [hnorm]
    have hr : (k / 2 : ℕ) + 1 - u.re < -2 := by
      linarith
    refine Summable.of_nonneg_of_le (fun α ↦ ?_) (fun α ↦ ?_)
      ((summable_norm_rpow_apply hK hx hr).mul_left
        (E * (∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (u - 1) • besselK 0 t‖) * (4 * π) ^ (-u.re) *
          ‖δ‖ ^ (-((k / 2 : ℕ) + 1 - u.re))))
    · exact mul_nonneg (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg (hb α).le _) hM₀)
    · have hμ : 0 < ‖σ (α.1 : K) / δ‖ := norm_pos_iff.mpr (div_ne_zero ((map_ne_zero σ).mpr
        (RingOfIntegers.coe_ne_zero_iff.mpr α.2)) hδ₀)
      have hα : 0 < ‖σ (α.1 : K)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr
        (RingOfIntegers.coe_ne_zero_iff.mpr α.2))
      refine (mul_le_mul_of_nonneg_right (hcE α.1 α.2)
        (mul_nonneg (Real.rpow_nonneg (hb α).le _) hM₀)).trans_eq ?_
      have e₁ : ‖σ (α.1 : K) / δ‖ ^ (k / 2 + 1) * ‖σ (α.1 : K) / δ‖ ^ (-u.re) =
          ‖σ (α.1 : K) / δ‖ ^ ((k / 2 : ℕ) + 1 - u.re) := by
        rw [sub_eq_add_neg, Real.rpow_add hμ, ← Nat.cast_succ, Real.rpow_natCast]
      have e₂ : ‖σ (α.1 : K) / δ‖ ^ ((k / 2 : ℕ) + 1 - u.re) =
          ‖σ (α.1 : K)‖ ^ ((k / 2 : ℕ) + 1 - u.re) * ‖δ‖ ^ (-((k / 2 : ℕ) + 1 - u.re)) := by
        rw [norm_div, Real.div_rpow hα.le hδ'.le, Real.rpow_neg hδ'.le, div_eq_mul_inv]
      rw [Real.mul_rpow (by positivity) hμ.le]
      have e₃ : E * ‖σ (α.1 : K) / δ‖ ^ (k / 2 + 1) *
          ((4 * π) ^ (-u.re) * ‖σ (α.1 : K) / δ‖ ^ (-u.re) *
            ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (u - 1) • besselK 0 t‖) =
          E * (∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (u - 1) • besselK 0 t‖) * (4 * π) ^ (-u.re) *
            (‖σ (α.1 : K) / δ‖ ^ (k / 2 + 1) * ‖σ (α.1 : K) / δ‖ ^ (-u.re)) := by
        ring1
      rw [e₃, e₁, e₂]
      ring1
  have h : HasSum (fun α ↦ ∫ y in Ioi (0 : ℝ), G α y) (∫ y in Ioi (0 : ℝ), ∑' α, G α y) :=
    hasSum_integral_of_summable_integral_norm hconv hsum
  have e₁ :
      ∫ y in Ioi (0 : ℝ), ∑' α, G α y = mellin (bianchiCentralFunction k F) (u - (k / 2 : ℕ) - 1) :=
    setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ (hpt y hy).tsum_eq
  rw [e₁] at h
  refine h.congr_fun fun α ↦ ?_
  have h₃ : mellin (fun y : ℝ ↦ besselK 0 (4 * π * ‖σ α.1 / δ‖ * y)) u =
      ((4 * π * ‖σ α.1 / δ‖ : ℝ) : ℂ) ^ (-u) • mellin (fun t : ℝ ↦ besselK 0 t) u :=
    mellin_comp_mul_left (fun t : ℝ ↦ besselK 0 t) u (hb α)
  rw [mellin_besselK_zero hu₀, smul_eq_mul] at h₃
  rw [← h₃, mellin, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
  simp only [smul_eq_mul]
  ring1

lemma mul_ne_zero_of_two_mul_re_pos {s : ℂ} (hs : 0 < (2 * s).re) :
    ((4 * π / √|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(2 * s)) * (2 ^ (2 * s - 2) * Gamma s ^ 2) ≠ 0 := by
  have hd : 0 < √|(discr K : ℝ)| := Real.sqrt_pos.mpr (abs_discr_pos K)
  have hre : 0 < s.re := by
    simp only [mul_re, re_ofNat, im_ofNat] at hs
    linarith
  refine mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr (by positivity))))
    (mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl two_ne_zero))
      (pow_ne_zero 2 (Gamma_ne_zero_of_re_pos hre)))

variable [IsTotallyComplex K]

lemma norm_coeff_le_of_bianchiNormSq_le (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) (hk' : Even k)
    (hk : k ≠ 0) (hδ : δ ^ 2 = discr K) (hH : IsBianchiCuspFunction σ k F)
    (hper : ∀ a : 𝓞 K, glSlash σ k (glUpper a) F = F)
    (hc : HasBianchiWhittakerExpansion σ δ k (extend F) c) {M : ℝ} (hM : ∀ z, bianchiNormSq F z ≤ M)
    {α : 𝓞 K} (hα : α ≠ 0) : ‖c α‖ ≤ 2 * rexp (5 * π) * √M * ‖σ α / δ‖ ^ (k / 2 + 1) := by
  have hδ₀ : δ ≠ 0 := ne_zero_of_sq_eq_discr K hδ
  have hμ : 0 < ‖σ (α : K) / δ‖ := norm_pos_iff.mpr (div_ne_zero ((map_ne_zero σ).mpr
    (RingOfIntegers.coe_ne_zero_iff.mpr hα)) hδ₀)
  have hy : 0 < ‖σ (α : K) / δ‖⁻¹ := inv_pos.mpr hμ
  have h₁ : ‖c α‖ * ‖σ (α : K) / δ‖⁻¹ *
      ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π * ‖σ (α : K) / δ‖ * ‖σ (α : K) / δ‖⁻¹)‖ ≤
        (‖σ (α : K) / δ‖⁻¹ ^ (k / 2))⁻¹ * √M :=
    hH.norm_coeff_mul_norm_besselK_le hK hx hk' hk hδ hper hc hα hy
      (norm_extend_le_of_bianchiNormSq_le hM hk' hy)
  have hr : 1 ≤ (k / 2 : ℝ) := one_le_div_two hk' hk
  have ht : 0 < 4 * π * ‖σ (α : K) / δ‖ * ‖σ (α : K) / δ‖⁻¹ := by
    positivity
  have h₂ : 2⁻¹ * rexp (-(5 / 4 * (4 * π * ‖σ (α : K) / δ‖ * ‖σ (α : K) / δ‖⁻¹))) ≤
      ‖besselK ((k / 2 : ℝ) : ℂ) (4 * π * ‖σ (α : K) / δ‖ * ‖σ (α : K) / δ‖⁻¹)‖ :=
    Complex.exp_le_norm_besselK hr ht
  have e₁ : 4 * π * ‖σ (α : K) / δ‖ * ‖σ (α : K) / δ‖⁻¹ = 4 * π := by
    field_simp
  have e₂ : 5 / 4 * (4 * π) = 5 * π := by
    ring1
  rw [e₁] at h₁ h₂
  rw [e₂, Real.exp_neg] at h₂
  have hc₀ : 0 ≤ ‖c α‖ * ‖σ (α : K) / δ‖⁻¹ := by
    positivity
  have h₃ :
      ‖c α‖ * ‖σ (α : K) / δ‖⁻¹ * (2⁻¹ * (rexp (5 * π))⁻¹) ≤ (‖σ (α : K) / δ‖⁻¹ ^ (k / 2))⁻¹ * √M :=
    (mul_le_mul_of_nonneg_left h₂ hc₀).trans h₁
  have he : 0 < rexp (5 * π) := Real.exp_pos _
  rw [inv_pow, inv_inv] at h₃
  have h₄ : ‖c α‖ * ‖σ (α : K) / δ‖⁻¹ * (2⁻¹ * (rexp (5 * π))⁻¹) *
      (2 * rexp (5 * π) * ‖σ (α : K) / δ‖) ≤
        ‖σ (α : K) / δ‖ ^ (k / 2) * √M * (2 * rexp (5 * π) * ‖σ (α : K) / δ‖) :=
    mul_le_mul_of_nonneg_right h₃ (by positivity)
  have e₃ : ‖c α‖ * ‖σ (α : K) / δ‖⁻¹ * (2⁻¹ * (rexp (5 * π))⁻¹) *
      (2 * rexp (5 * π) * ‖σ (α : K) / δ‖) = ‖c α‖ := by
    field_simp
  rw [e₃] at h₄
  refine h₄.trans_eq ?_
  rw [pow_succ]
  ring1

variable [IsPrincipalIdealRing (𝓞 K)]

/-- **Exponential decay of a cusp form**: for `K` imaginary quadratic of class number `1`, `k ≥ 1`
even and `F` in `S_k(𝔑)`, `𝔑 ≠ 0`, there are `C` and `a > 0` with `y^{k/2} |F(x, y)| ≤ C e^{-ay}`
for `y ≥ 1`. -/
lemma exists_height_pow_mul_norm_le_exp (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hk' : Even k)
    (h𝔑 : 𝔑 ≠ ⊥) (hF : F ∈ bianchiCuspForms σ 𝔑.gamma0GL k) : ∃ C a : ℝ, 0 < a ∧
    ∀ z : HyperbolicThreeSpace, 1 ≤ z.height → z.height ^ (k / 2) * ‖F z‖ ≤
    C * rexp (-a * z.height) := by
  rcases exists_span_eq h𝔑 with ⟨N, rfl⟩
  rcases (mem_bianchiCuspForms_iff hK h𝔑).mp hF with ⟨hH, -⟩
  have hper : ∀ a : 𝓞 K, glSlash σ k (glUpper a) F = F := fun a ↦
    hF.1.invariant.glSlash_eq (glUpper_mem_gamma0GL a N)
  rcases exists_bianchiNormSq_le hK hk h𝔑 hF with ⟨M, hM⟩
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  have hδ : ((discr K : ℂ) ^ (2⁻¹ : ℂ)) ^ 2 = discr K := cpow_ofNat_inv_pow _ 2
  have hδ₀ : (discr K : ℂ) ^ (2⁻¹ : ℂ) ≠ 0 := ne_zero_of_sq_eq_discr K hδ
  generalize (discr K : ℂ) ^ (2⁻¹ : ℂ) = δ at hδ hδ₀
  have hδ' : 0 < ‖δ‖ := norm_pos_iff.mpr hδ₀
  rcases (⟨_, hH.hasBianchiWhittakerExpansion hK hx hk' hk hδ hper⟩ :
    ∃ e : 𝓞 K → ℂ, HasBianchiWhittakerExpansion σ δ k (extend F) e) with ⟨e, hc⟩
  have hE : 0 ≤ 2 * rexp (5 * π) * √M := by
    positivity
  have ht₁ : 0 < 4 * π / ‖δ‖ := by
    positivity
  have ha : 0 < 3 / 4 * π / ‖δ‖ := by
    positivity
  refine ⟨2 * rexp (5 * π) * √M * bianchiTailConstant k (4 * π / ‖δ‖) *
    ((∑' α : {α : 𝓞 K // α ≠ 0}, rexp (-(3 / 4 * π * ‖σ α.1 / δ‖ * 1))) * rexp (3 / 4 * π / ‖δ‖)),
    3 / 4 * π / ‖δ‖, ha, fun z hz ↦ ?_⟩
  have hy₁ : 0 < z.height := z.height_pos
  have hs : Summable fun α : {α : 𝓞 K // α ≠ 0} ↦
      rexp (-(3 / 4 * π * ‖σ α.1 / δ‖ * z.height)) := summable_exp_neg_norm_div hK hx hδ₀ hy₁
  have hs₁ : Summable fun α : {α : 𝓞 K // α ≠ 0} ↦ rexp (-(3 / 4 * π * ‖σ α.1 / δ‖ * 1)) :=
    summable_exp_neg_norm_div hK hx hδ₀ one_pos
  have h₁ : z.height ^ (k / 2) * ‖F z‖ ≤
      2 * rexp (5 * π) * √M * bianchiTailConstant k (4 * π / ‖δ‖) *
        ∑' α : {α : 𝓞 K // α ≠ 0}, rexp (-(3 / 4 * π * ‖σ α.1 / δ‖ * z.height)) :=
    height_pow_mul_norm_le_of_hasSum (norm_eq_sqrt_of_sq_eq_discr hδ) hc ht₁
    (fun α hα ↦ div_ne_zero ((map_ne_zero σ).mpr (RingOfIntegers.coe_ne_zero_iff.mpr hα)) hδ₀)
    (fun α hα ↦ ?_) hE (fun α hα ↦ ?_) hs.hasSum (fun _ ↦ (Real.exp_pos _).le)
    (fun _ ↦ Or.inr le_rfl) le_rfl
  · have h₂ : ∑' α : {α : 𝓞 K // α ≠ 0}, rexp (-(3 / 4 * π * ‖σ α.1 / δ‖ * z.height)) ≤
        (∑' α : {α : 𝓞 K // α ≠ 0}, rexp (-(3 / 4 * π * ‖σ α.1 / δ‖ * 1))) *
          (rexp (3 / 4 * π / ‖δ‖) * rexp (-(3 / 4 * π / ‖δ‖) * z.height)) := by
      rw [← tsum_mul_right]
      refine hs.tsum_le_tsum (fun α ↦ ?_) (hs₁.mul_right _)
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h₃ : 1 / ‖δ‖ ≤ ‖σ (α.1 : K) / δ‖ := by
        rw [norm_div]
        exact div_le_div_of_nonneg_right (one_le_norm_apply hK α.2) hδ'.le
      have h₄ :
          3 / 4 * π * (1 / ‖δ‖) * (z.height - 1) ≤ 3 / 4 * π * ‖σ (α.1 : K) / δ‖ * (z.height - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₃ (by positivity)) (by linarith)
      have e : 3 / 4 * π * (1 / ‖δ‖) = 3 / 4 * π / ‖δ‖ := by
        ring1
      rw [e] at h₄
      nlinarith [h₄]
    have hT : 0 ≤ 2 * rexp (5 * π) * √M * bianchiTailConstant k (4 * π / ‖δ‖) :=
      mul_nonneg hE (bianchiTailConstant_nonneg _)
    refine h₁.trans ((mul_le_mul_of_nonneg_left h₂ hT).trans_eq ?_)
    ring1
  · refine le_trans ?_ (le_mul_norm_div_mul (σ := σ) hK hδ₀ hy₁ hα)
    refine div_le_div_of_nonneg_right ?_ hδ'.le
    nlinarith [Real.pi_pos]
  · refine (norm_coeff_le_of_bianchiNormSq_le hK hx hk' hk hδ hH hper hc hM hα).trans ?_
    refine le_mul_of_one_le_right (by positivity) ?_
    exact Real.one_le_exp (by positivity)

lemma bianchiCentralFunction_isBigO_atTop (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hk' : Even k)
    (h𝔑 : 𝔑 ≠ ⊥) (hF : F ∈ bianchiCuspForms σ 𝔑.gamma0GL k) (r : ℝ) :
    bianchiCentralFunction k F =O[atTop] (· ^ r) := by
  rcases exists_height_pow_mul_norm_le_exp hK hk hk' h𝔑 hF with ⟨C, a, ha, h⟩
  have h₁ : bianchiCentralFunction k F =O[atTop] fun y : ℝ ↦ rexp (-a * y) := by
    refine IsBigO.of_bound C ((eventually_ge_atTop 1).mono fun y hy ↦ ?_)
    have hy₀ : 0 < y := one_pos.trans_le hy
    let z : HyperbolicThreeSpace := .mk (WithLp.toLp 2 (0, y)) hy₀
    have e : z.height = y := rfl
    have h₂ : z.height ^ (k / 2) * ‖F z‖ ≤ C * rexp (-a * z.height) := h z (by rwa [e])
    rw [e] at h₂
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine le_trans ?_ h₂
    rw [bianchiCentralFunction, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hy₀.le]
    exact mul_le_mul_of_nonneg_left (norm_extend_apply_le _ hy₀) (pow_nonneg hy₀.le _)
  exact h₁.trans (isLittleO_exp_neg_mul_rpow_atTop ha r).isBigO

lemma bianchiCentralFunction_isBigO_nhdsGT (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hk' : Even k)
    (hF : F ∈ bianchiCuspForms σ (Ideal.span {n}).gamma0GL k) {a : ℂ} (ha : ‖a‖ = 1)
    (h : bianchiSlash k (slRepresentative σ (frickeMatrix n)) F = a • F) (r : ℝ) :
    bianchiCentralFunction k F =O[𝓝[>] 0] (· ^ (-r)) := by
  have hσ' : 0 < ‖σ (n : K)‖ := norm_apply_pos σ n
  have h₁ : bianchiCentralFunction k F =O[atTop] (· ^ r) :=
    bianchiCentralFunction_isBigO_atTop hK hk hk' (NeZero.ne (Ideal.span {n})) hF r
  have ht : Tendsto (fun y : ℝ ↦ (‖σ (n : K)‖ * y)⁻¹) (𝓝[>] 0) atTop := by
    refine tendsto_inv_nhdsGT_zero.comp ?_
    have h₂ : Tendsto (fun y : ℝ ↦ ‖σ (n : K)‖ * y) (𝓝 0) (𝓝 (‖σ (n : K)‖ * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at h₂
    refine tendsto_nhdsWithin_iff.mpr ⟨h₂.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    exact mul_pos hσ' hy
  refine IsBigO.trans ?_ ((h₁.comp_tendsto ht).trans ?_)
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    rw [one_mul, Function.comp_apply, bianchiCentralFunction_mul_inv hk' h hy, norm_mul, norm_mul,
      ha, norm_pow, norm_neg, norm_one, one_pow, one_mul, one_mul]
  · refine IsBigO.of_bound (‖σ (n : K)‖ ^ (-r)) ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    have e : ((‖σ (n : K)‖ * y)⁻¹) ^ r = ‖σ (n : K)‖ ^ (-r) * y ^ (-r) := by
      rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
        Real.mul_rpow hσ'.le hy.le]
    simp only [Function.comp_apply]
    rw [e, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]

/-- **The Mellin transform of the central function of a cusp form is entire**, for a form with
`F ∣ W_n = a F`, `|a| = 1`, as the central function decays rapidly at `∞` and, by the Fricke
involution, at `0`. -/
lemma differentiable_mellin_bianchiCentralFunction (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (hk' : Even k) (hF : F ∈ bianchiCuspForms σ (Ideal.span {n}).gamma0GL k) {a : ℂ} (ha : ‖a‖ = 1)
    (h : bianchiSlash k (slRepresentative σ (frickeMatrix n)) F = a • F) :
    Differentiable ℂ (mellin (bianchiCentralFunction k F)) :=
  fun s ↦ mellin_differentiableAt_of_isBigO_rpow
    ((continuousOn_bianchiCentralFunction hF.1.analyticAt).locallyIntegrableOn measurableSet_Ioi)
    (bianchiCentralFunction_isBigO_atTop hK hk hk' (NeZero.ne (Ideal.span {n})) hF (-(s.re + 1)))
    (lt_add_one _) (bianchiCentralFunction_isBigO_nhdsGT hK hk hk' hF ha h (s.re - 1))
    (sub_one_lt _)

namespace BianchiNewformOfWeight

variable (N : BianchiNewformOfWeight σ k (Ideal.span {n})) {ε : ℂ}

/-- The **completed L-function** `Λ(F, s) = |n|^s ∫₀^∞ ψ(y) y^{2s - k/2 - 1} dy / y` of a Bianchi
newform `F` of level `(n)`, for the central function `ψ` of `F`. It is entire
(`differentiable_completedL`), it satisfies the functional equation
(`completedL_add_one_sub`), and for `Re s` large, it is
`|n|^s (4π / √|Δ|)^{-2s} 2^{2s-2} Γ(s)² ∑_{α ≠ 0} c(α) |α|^{-2s}`, where `|α|² = N(α)`
(`completedL_eq_tsum`), that is `w` times the sum `∑_𝔞 c(𝔞) N(𝔞)^{-s}` over the nonzero ideals `𝔞`,
for `w` the number of units of `𝒪_K`. -/
noncomputable def completedL (s : ℂ) : ℂ :=
  ((‖σ (n : K)‖ : ℝ) : ℂ) ^ s * mellin (bianchiCentralFunction k N.toFun) (2 * s - (k / 2 : ℕ) - 1)

variable {N}

lemma bianchiSlash_toFun (hs : N.HasSign ε) :
    bianchiSlash k (slRepresentative σ (frickeMatrix n)) N.toFun = (-ε) • N.toFun :=
  congrArg Subtype.val hs

/-- **The functional equation of the L-function of a Bianchi newform** (LMFDB `mf.bianchi.sign`):
for `K` imaginary quadratic of class number `1` and a newform `F` of weight `k` and level `(n)`, of
sign `ε`, `Λ(F, k/2 + 1 - s) = (-1)^{k/2+1} ε Λ(F, s)`. So the sign of the functional equation is
`(-1)^{k/2+1} ε`, which is `ε` for `k ≡ 2` modulo `4`, as for `k = 2`, the weight of the LMFDB, and
`-ε` for `k ≡ 0` modulo `4`. -/
lemma completedL_add_one_sub (hK : finrank ℚ K = 2) (hs : N.HasSign ε) (s : ℂ) :
    N.completedL ((k / 2 : ℕ) + 1 - s) = (-1) ^ (k / 2 + 1) * ε * N.completedL s := by
  have h₁ : ((‖σ (n : K)‖ : ℝ) : ℂ) ^ (-(2 * s - (k / 2 : ℕ) - 1)) *
      mellin (bianchiCentralFunction k N.toFun) (-(2 * s - (k / 2 : ℕ) - 1)) =
        (-1) ^ (k / 2) * -ε * mellin (bianchiCentralFunction k N.toFun) (2 * s - (k / 2 : ℕ) - 1) :=
    mellin_bianchiCentralFunction_neg (N.even hK) (bianchiSlash_toFun hs) _
  have e₁ : 2 * ((k / 2 : ℕ) + 1 - s) - (k / 2 : ℕ) - 1 = -(2 * s - (k / 2 : ℕ) - 1) := by
    ring1
  have e₂ : ((‖σ (n : K)‖ : ℝ) : ℂ) ^ ((k / 2 : ℕ) + 1 - s) =
      ((‖σ (n : K)‖ : ℝ) : ℂ) ^ s * ((‖σ (n : K)‖ : ℝ) : ℂ) ^ (-(2 * s - (k / 2 : ℕ) - 1)) := by
    rw [← cpow_add _ _ (ofReal_norm_apply_ne_zero σ n)]
    congr 1
    ring1
  rw [completedL, completedL, e₁, e₂, mul_assoc, h₁, pow_succ]
  ring1

/-- **The completed L-function of a Bianchi newform is entire** (LMFDB `mf.bianchi.sign`). -/
lemma differentiable_completedL (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hs : N.HasSign ε) :
    Differentiable ℂ N.completedL := by
  have ha : ‖-ε‖ = 1 := by
    rcases hs.eq_one_or_eq_neg_one (N.toFun_ne_zero hK) with rfl | rfl <;> simp
  have h₁ : Differentiable ℂ (mellin (bianchiCentralFunction k N.toFun)) :=
    differentiable_mellin_bianchiCentralFunction hK hk (N.even hK)
      (bianchiNewSubspace_le σ k _ N.mem_bianchiNewSubspace) ha (bianchiSlash_toFun hs)
  refine Differentiable.mul (fun s ↦ ?_) (h₁.comp (by fun_prop))
  exact differentiableAt_id.const_cpow (Or.inl (ofReal_norm_apply_ne_zero σ n))

lemma hasSum_mul_coeff_mul_norm_cpow (hK : finrank ℚ K = 2) (hk : k ≠ 0) {s : ℂ}
    (hs : (k / 2 : ℕ) + 3 < (2 * s).re) : HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦
      ((4 * π / √|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(2 * s)) * (2 ^ (2 * s - 2) * Gamma s ^ 2) *
        (N.coeff α * ((‖σ α.1‖ : ℝ) : ℂ) ^ (-(2 * s))))
          (mellin (bianchiCentralFunction k N.toFun) (2 * s - (k / 2 : ℕ) - 1)) := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  have hδ : ((discr K : ℂ) ^ (2⁻¹ : ℂ)) ^ 2 = discr K := cpow_ofNat_inv_pow _ 2
  have hδ₀ : (discr K : ℂ) ^ (2⁻¹ : ℂ) ≠ 0 := ne_zero_of_sq_eq_discr K hδ
  have hδn : ‖(discr K : ℂ) ^ (2⁻¹ : ℂ)‖ = √|(discr K : ℝ)| := norm_eq_sqrt_of_sq_eq_discr hδ
  have hF : N.toFun ∈ bianchiCuspForms σ (Ideal.span {n}).gamma0GL k :=
    bianchiNewSubspace_le σ k _ N.mem_bianchiNewSubspace
  have h𝔑 : Ideal.span {n} ≠ ⊥ := NeZero.ne (Ideal.span {n})
  rcases (mem_bianchiCuspForms_iff hK h𝔑).mp hF with ⟨hH, -⟩
  have hper : ∀ a : 𝓞 K, glSlash σ k (glUpper a) N.toFun = N.toFun :=
    hF.1.invariant.glSlash_glUpper h𝔑
  rcases exists_bianchiNormSq_le hK hk h𝔑 hF with ⟨M, hM⟩
  refine (hasSum_mellin_bianchiCentralFunction hK hx (N.even hK) hδ N.hasWhittakerExpansion
    (fun α hα ↦ norm_coeff_le_of_bianchiNormSq_le hK hx (N.even hK) hk hδ hH hper
      N.hasWhittakerExpansion hM hα) hs).congr_fun fun α ↦ ?_
  have hd : 0 < √|(discr K : ℝ)| := Real.sqrt_pos.mpr (abs_discr_pos K)
  have e₁ : 4 * π * ‖σ (α.1 : K) / (discr K : ℂ) ^ (2⁻¹ : ℂ)‖ =
      (4 * π / √|(discr K : ℝ)|) * ‖σ (α.1 : K)‖ := by
    rw [norm_div, hδn]
    ring1
  rw [e₁, ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) (norm_nonneg _),
    mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℂ) ≠ 0)]
  ring1

/-- **The Dirichlet series of a Bianchi newform converges** for `Re(2s) > k/2 + 3`. -/
lemma summable_coeff_mul_norm_cpow (hK : finrank ℚ K = 2) (hk : k ≠ 0) {s : ℂ}
    (hs : (k / 2 : ℕ) + 3 < (2 * s).re) :
    Summable fun α : {α : 𝓞 K // α ≠ 0} ↦ N.coeff α * ((‖σ α.1‖ : ℝ) : ℂ) ^ (-(2 * s)) :=
  (summable_mul_left_iff (mul_ne_zero_of_two_mul_re_pos
    (lt_of_le_of_lt (by positivity) hs))).mp (hasSum_mul_coeff_mul_norm_cpow hK hk hs).summable

/-- **The completed L-function of a Bianchi newform in terms of its Dirichlet series** (LMFDB
`mf.bianchi.sign`): for `Re(2s) > k/2 + 3`,
`Λ(F, s) = |n|^s (4π / √|Δ|)^{-2s} 2^{2s-2} Γ(s)² ∑_{α ≠ 0} c(α) |α|^{-2s}`. -/
lemma completedL_eq_tsum (hK : finrank ℚ K = 2) (hk : k ≠ 0) {s : ℂ}
    (hs : (k / 2 : ℕ) + 3 < (2 * s).re) : N.completedL s = ((‖σ (n : K)‖ : ℝ) : ℂ) ^ s *
    (((4 * π / √|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(2 * s)) * (2 ^ (2 * s - 2) * Gamma s ^ 2) *
      ∑' α : {α : 𝓞 K // α ≠ 0}, N.coeff α * ((‖σ α.1‖ : ℝ) : ℂ) ^ (-(2 * s))) := by
  rw [completedL, ← (hasSum_mul_coeff_mul_norm_cpow hK hk hs).tsum_eq, tsum_mul_left]

variable (σ) in
lemma sq_norm_generator (hK : finrank ℚ K = 2) (𝔞 : Ideal (𝓞 K)) :
    ‖σ ((IsPrincipal.generator 𝔞 : 𝓞 K) : K)‖ ^ 2 = Ideal.absNorm 𝔞 := by
  rw [sq_norm_apply_eq_absNorm σ hK, Ideal.span_singleton_generator]

lemma cpow_neg_two_mul_eq {r : ℝ} (hr : 0 < r) (s : ℂ) :
    (r : ℂ) ^ (-(2 * s)) = ((r ^ 2 : ℝ) : ℂ) ^ (-s) := by
  have e : -(2 * s) = -s + -s := by
    ring1
  rw [e, cpow_add _ _ (ofReal_ne_zero.mpr hr.ne'), sq, ofReal_mul,
    mul_cpow_ofReal_nonneg hr.le hr.le]

/-- **The Dirichlet series of a Bianchi newform over the ideals**: for `Re(2s) > k/2 + 3`,
`∑_{α ≠ 0} c(α) |α|^{-2s}` is `w` times `L(F, s) = ∑_𝔞 c(𝔞) N(𝔞)^{-s}`, where `𝔞` runs over the
nonzero ideals of `𝒪_K` and `w` is the number of units of `𝒪_K`, as `c(uα) = c(α)` for the units
`u`. -/
lemma tsum_coeff_mul_norm_cpow_eq (hK : finrank ℚ K = 2) (hk : k ≠ 0) {s : ℂ}
    (hs : (k / 2 : ℕ) + 3 < (2 * s).re) : ∑' α : {α : 𝓞 K // α ≠ 0}, N.coeff α *
      ((‖σ α.1‖ : ℝ) : ℂ) ^ (-(2 * s)) = Nat.card (𝓞 K)ˣ * ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
        N.idealCoeff 𝔞 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) := by
  let e : (𝓞 K)ˣ × {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥} → {α : 𝓞 K // α ≠ 0} := fun p ↦
    ⟨(p.1 : 𝓞 K) * IsPrincipal.generator p.2.1, mul_ne_zero p.1.ne_zero (generator_ne_zero p.2.2)⟩
  have he : Function.Bijective e := by
    refine ⟨?_, ?_⟩
    · rintro ⟨u, 𝔞⟩ ⟨v, 𝔟⟩ h
      have h₁ : (u : 𝓞 K) * IsPrincipal.generator 𝔞.1 = v * IsPrincipal.generator 𝔟.1 :=
        congrArg Subtype.val h
      have h₂ : 𝔞 = 𝔟 := Subtype.ext <| by
        rw [← Ideal.span_singleton_generator 𝔞.1, ← Ideal.span_singleton_generator 𝔟.1,
          ← Ideal.span_singleton_mul_left_unit u.isUnit, h₁,
          Ideal.span_singleton_mul_left_unit v.isUnit]
      subst h₂
      rw [Units.ext (mul_right_cancel₀ (generator_ne_zero 𝔞.2) h₁)]
    · rintro ⟨α, hα⟩
      have h𝔞 : Ideal.span {α} ≠ ⊥ := fun h ↦ hα (Ideal.span_singleton_eq_bot.mp h)
      have h₁ : Associated (IsPrincipal.generator (Ideal.span {α})) α := by
        rw [← Ideal.span_singleton_eq_span_singleton, Ideal.span_singleton_generator]
      rcases h₁ with ⟨u, hu⟩
      exact ⟨(u, ⟨_, h𝔞⟩), Subtype.ext ((mul_comm _ _).trans hu)⟩
  have hterm (p : (𝓞 K)ˣ × {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥}) : N.coeff (e p) *
      ((‖σ ((e p).1 : K)‖ : ℝ) : ℂ) ^ (-(2 * s)) = N.idealCoeff p.2 *
        (Ideal.absNorm p.2.1 : ℂ) ^ (-s) := by
    have hg : IsPrincipal.generator p.2.1 ≠ 0 := generator_ne_zero p.2.2
    have hr : 0 < ‖σ ((IsPrincipal.generator p.2.1 : 𝓞 K) : K)‖ :=
      one_pos.trans_le (one_le_norm_apply hK hg)
    have h₁ : ‖σ ((e p).1 : K)‖ = ‖σ ((IsPrincipal.generator p.2.1 : 𝓞 K) : K)‖ := by
      have e₁ : ((e p).1 : K) = ((p.1 : 𝓞 K) : K) * ((IsPrincipal.generator p.2.1 : 𝓞 K) : K) :=
        rfl
      rw [e₁, map_mul, norm_mul, norm_unit_eq_one hK p.1, one_mul]
    have h₂ : (Ideal.absNorm p.2.1 : ℂ) =
        ((‖σ ((IsPrincipal.generator p.2.1 : 𝓞 K) : K)‖ ^ 2 : ℝ) : ℂ) := by
      rw [sq_norm_generator σ hK]
      push_cast
      rfl
    rw [h₁, cpow_neg_two_mul_eq hr, h₂]
    exact congrArg (· * _) (N.coeff_unit_mul hK p.1 hg)
  have hfin : Finite (𝓞 K)ˣ := finite_units σ hK
  let _ : Fintype (𝓞 K)ˣ := Fintype.ofFinite _
  have hsum : Summable fun p : (𝓞 K)ˣ × {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥} ↦
      N.idealCoeff p.2 * (Ideal.absNorm p.2.1 : ℂ) ^ (-s) := by
    simpa only [Function.comp_def, Equiv.ofBijective_apply, hterm] using
      (Equiv.ofBijective e he).summable_iff.mpr (summable_coeff_mul_norm_cpow (N := N) hK hk hs)
  rw [← (Equiv.ofBijective e he).tsum_eq]
  simp only [Equiv.ofBijective_apply, hterm]
  rw [hsum.tsum_prod, tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

lemma coeff_eq_one_of_norm_eq_one (hK : finrank ℚ K = 2) {α : 𝓞 K} (hα : ‖σ (α : K)‖ = 1) :
    N.coeff α = 1 := by
  have h₁ : ‖σ (α : K)‖ ^ 2 = ((|Algebra.norm ℚ (α : K)| : ℚ) : ℝ) :=
    norm_sq_apply_eq_abs_norm hK _
  rw [hα, one_pow] at h₁
  have h₂ : |Algebra.norm ℚ (α : K)| = 1 := by
    exact_mod_cast h₁.symm
  have hu : IsUnit α := isUnit_iff_norm.mpr h₂
  rcases hu with ⟨u, rfl⟩
  have h₃ : N.coeff ((u : 𝓞 K) * 1) = N.coeff 1 := N.coeff_unit_mul hK u one_ne_zero
  rw [mul_one, N.coeff_one] at h₃
  exact h₃

/-- **The completed L-function of a Bianchi newform is not identically `0`**, as its Dirichlet
series tends to the number of units of `𝒪_K` at `+∞`, since `c(u) = c(1) = 1` for the units `u`. -/
lemma exists_completedL_ne_zero (hK : finrank ℚ K = 2) (hk : k ≠ 0) : ∃ s, N.completedL s ≠ 0 := by
  classical
  have hre (t : ℝ) : (2 * (t : ℂ)).re = 2 * t := by
    simp
  have hm : (0 : ℝ) ≤ (k / 2 : ℕ) := Nat.cast_nonneg _
  have hs₀ : (k / 2 : ℕ) + 3 < (2 * (((k / 2 : ℕ) + 4 : ℝ) : ℂ)).re := by
    rw [hre]
    linarith
  have hb : Summable fun α : {α : 𝓞 K // α ≠ 0} ↦
      ‖N.coeff α * ((‖σ (α.1 : K)‖ : ℝ) : ℂ) ^ (-(2 * ((((k / 2 : ℕ) + 4 : ℝ) : ℂ))))‖ :=
    (summable_coeff_mul_norm_cpow (N := N) hK hk hs₀).norm
  have hnormx (α : {α : 𝓞 K // α ≠ 0}) (t : ℝ) :
      ‖((‖σ (α.1 : K)‖ : ℝ) : ℂ) ^ (-(2 * (t : ℂ)))‖ = ‖σ (α.1 : K)‖ ^ (-(2 * t)) := by
    have hα : 0 < ‖σ (α.1 : K)‖ := one_pos.trans_le (one_le_norm_apply hK α.2)
    rw [norm_cpow_eq_rpow_re_of_pos hα, neg_re, hre]
  let g : {α : 𝓞 K // α ≠ 0} → ℝ := fun α ↦ if ‖σ (α.1 : K)‖ = 1 then 1 else 0
  have hg₀ (α : {α : 𝓞 K // α ≠ 0}) : 0 ≤ g α := by
    simp only [g]
    split_ifs <;> norm_num
  have hlim (α : {α : 𝓞 K // α ≠ 0}) : Tendsto (fun t : ℝ ↦
      N.coeff α * ((‖σ (α.1 : K)‖ : ℝ) : ℂ) ^ (-(2 * (t : ℂ)))) atTop (𝓝 (g α : ℂ)) := by
    by_cases h₁ : ‖σ (α.1 : K)‖ = 1
    · simp only [g, h₁, ofReal_one, one_cpow, mul_one, coeff_eq_one_of_norm_eq_one hK h₁]
      exact tendsto_const_nhds
    · have hgt : 1 < ‖σ (α.1 : K)‖ := lt_of_le_of_ne (one_le_norm_apply hK α.2) (Ne.symm h₁)
      simp only [g, h₁, ite_false, ofReal_zero]
      rw [← mul_zero (N.coeff α)]
      refine Tendsto.const_mul _ (tendsto_zero_iff_norm_tendsto_zero.mpr ?_)
      simp only [hnormx]
      refine (tendsto_rpow_atBot_of_base_gt_one _ hgt).comp ?_
      exact tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop two_pos)
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ α : {α : 𝓞 K // α ≠ 0},
      ‖N.coeff α * ((‖σ (α.1 : K)‖ : ℝ) : ℂ) ^ (-(2 * (t : ℂ)))‖ ≤
        ‖N.coeff α * ((‖σ (α.1 : K)‖ : ℝ) : ℂ) ^ (-(2 * ((((k / 2 : ℕ) + 4 : ℝ) : ℂ))))‖ := by
    filter_upwards [eventually_ge_atTop (((k / 2 : ℕ) : ℝ) + 4)] with t ht α
    rw [norm_mul, norm_mul, hnormx, hnormx]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le (one_le_norm_apply hK α.2) (by linarith)
  have hT : Tendsto (fun t : ℝ ↦ ∑' α : {α : 𝓞 K // α ≠ 0},
      N.coeff α * ((‖σ (α.1 : K)‖ : ℝ) : ℂ) ^ (-(2 * (t : ℂ)))) atTop (𝓝 (∑' α, (g α : ℂ))) :=
    tendsto_tsum_of_dominated_convergence hb hlim hbound
  have hgs : Summable g := by
    refine Summable.of_nonneg_of_le hg₀ (fun α ↦ ?_) hb
    by_cases h₁ : ‖σ (α.1 : K)‖ = 1
    · simp [g, h₁, coeff_eq_one_of_norm_eq_one hK h₁]
    · simp only [g, h₁]
      exact norm_nonneg _
  have hL : (∑' α, (g α : ℂ)) ≠ 0 := by
    rw [← ofReal_tsum]
    refine ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le one_pos ?_))
    have h₁ : g ⟨1, one_ne_zero⟩ = 1 := by
      simp [g]
    exact h₁ ▸ hgs.le_tsum ⟨1, one_ne_zero⟩ fun α _ ↦ hg₀ α
  rcases ((hT.eventually_ne hL).and (eventually_ge_atTop (((k / 2 : ℕ) : ℝ) + 4))).exists with
    ⟨t, ht₁, ht₂⟩
  have hst : (k / 2 : ℕ) + 3 < (2 * (t : ℂ)).re := by
    rw [hre]
    linarith
  refine ⟨t, ?_⟩
  rw [completedL_eq_tsum hK hk hst]
  exact mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl (ofReal_norm_apply_ne_zero σ n)))
    (mul_ne_zero (mul_ne_zero_of_two_mul_re_pos (lt_of_le_of_lt (by positivity) hst)) ht₁)

end BianchiNewformOfWeight

lemma eq_neg_one_pow_analyticOrderNatAt {f : ℂ → ℂ} (hf : Differentiable ℂ f) {s₀ : ℂ}
    (hs₀ : f s₀ ≠ 0) {a ρ : ℂ} (h : ∀ s, f (2 * a - s) = ρ * f s) :
    ρ = (-1) ^ analyticOrderNatAt f a := by
  have han : AnalyticAt ℂ f a := hf.analyticAt a
  have htop : analyticOrderAt f a ≠ ⊤ := fun h₀ ↦ hs₀ <|
    (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ a) (analyticOrderAt_eq_top.mp h₀) (mem_univ s₀)
  rcases (han.analyticOrderNatAt_eq_iff htop).mp rfl with ⟨g, hg, hg₀, hev⟩
  have hcont : Tendsto (fun s : ℂ ↦ 2 * a - s) (𝓝 a) (𝓝 a) := by
    have h₁ : Tendsto (fun s : ℂ ↦ 2 * a - s) (𝓝 a) (𝓝 (2 * a - a)) :=
      tendsto_const_nhds.sub tendsto_id
    have e : 2 * a - a = a := by
      ring1
    rwa [e] at h₁
  have hkey : ∀ᶠ s in 𝓝[≠] a, (-1) ^ analyticOrderNatAt f a * g (2 * a - s) = ρ * g s := by
    filter_upwards [nhdsWithin_le_nhds (hev.and (hcont.eventually hev)), self_mem_nhdsWithin] with
      s hs hsa
    rcases hs with ⟨h₁, h₂⟩
    have h₃ : f (2 * a - s) = ρ * f s := h s
    rw [h₂, h₁, smul_eq_mul, smul_eq_mul] at h₃
    have e : 2 * a - s - a = -1 * (s - a) := by
      ring1
    rw [e, mul_pow] at h₃
    refine mul_left_cancel₀ (pow_ne_zero (analyticOrderNatAt f a) (sub_ne_zero.mpr hsa)) ?_
    linear_combination h₃
  have hlim₁ : Tendsto (fun s ↦ (-1) ^ analyticOrderNatAt f a * g (2 * a - s)) (𝓝[≠] a)
      (𝓝 ((-1) ^ analyticOrderNatAt f a * g a)) :=
    (((hg.continuousAt.tendsto).comp hcont).mono_left nhdsWithin_le_nhds).const_mul _
  have hlim₂ : Tendsto (fun s ↦ ρ * g s) (𝓝[≠] a) (𝓝 (ρ * g a)) :=
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).const_mul _
  exact (mul_right_cancel₀ hg₀ (tendsto_nhds_unique (hlim₁.congr' hkey) hlim₂)).symm

/-- **The parity of the order of vanishing at the centre** (LMFDB `mf.bianchi.sign`): for `K`
imaginary quadratic of class number `1` and a newform `F` of weight `k ≥ 1` and level `(n)`, of sign
`ε`, the order of vanishing `r` of `Λ(F, s)` at the centre `s = (k/2 + 1) / 2` of the functional
equation satisfies `(-1)^{k/2+1} ε = (-1)^r`. So for `k = 2`, it is even when `F` has sign `+1` and
odd otherwise. -/
lemma BianchiNewformOfWeight.neg_one_pow_mul_eq_neg_one_pow_analyticOrderNatAt
    {N : BianchiNewformOfWeight σ k (Ideal.span {n})} {ε : ℂ} (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (hs : N.HasSign ε) : (-1) ^ (k / 2 + 1) * ε =
      (-1) ^ analyticOrderNatAt N.completedL ((((k / 2 : ℕ) : ℂ) + 1) / 2) := by
  rcases exists_completedL_ne_zero (N := N) hK hk with ⟨s₀, hs₀⟩
  refine eq_neg_one_pow_analyticOrderNatAt (differentiable_completedL hK hk hs) hs₀ fun s ↦ ?_
  rw [mul_div_cancel₀ _ (two_ne_zero : (2 : ℂ) ≠ 0)]
  exact completedL_add_one_sub hK hs s

end HyperbolicThreeSpace
