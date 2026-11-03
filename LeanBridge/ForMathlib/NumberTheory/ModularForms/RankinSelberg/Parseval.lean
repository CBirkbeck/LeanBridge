import LeanBridge.ForMathlib.NumberTheory.ModularForms.RankinSelberg.Strip
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import TauCeti.NumberTheory.ModularForms.Petersson.Basic

/-!
# The Mellin transform of the mean square of a cusp form

Parseval's identity writes the mean square `J(y) = ∫_0^1 |W(x + i y)| ^ 2 dx` of a cusp form on a
horizontal line as `∑ |a_n| ^ 2 exp (-4 π n y)`. Its Mellin transform is therefore the Dirichlet
series `∑ |a_n| ^ 2 Γ(s) (4 π n) ^ (-s)`, which is the right-hand side of the Rankin–Selberg
identity.

## Main definitions

* `RankinSelberg.mellinKernel`: the kernel `Γ(s) (4 π n) ^ (-s)`.

## Main results

* `RankinSelberg.hasSum_norm_sq_mul_mellinKernel`: the Mellin transform of the mean square of a cusp
  form on horizontal lines is a Dirichlet series.
-/

open MeasureTheory UpperHalfPlane Set

open scoped Real

namespace RankinSelberg

variable {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (W : CuspForm Γ k) {s y : ℝ}

lemma hasSum_norm_sq_mul_exp (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (hy : 0 < y) : HasSum
    (fun n : ℕ ↦ ‖(qExpansion 1 W).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y)))
    (∫ x in Ico (0 : ℝ) 1, ‖W (coordPoint (x, y))‖ ^ 2) := by
  have h : HasSum (fun n : ℕ ↦ ‖(qExpansion 1 W).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y)))
      (∫ x in (0 : ℝ)..1, ‖W ⟨x + y * UpperHalfPlane.I, by simpa using hy⟩‖ ^ 2) := by
    simpa only [inv_one, one_mul, div_one] using hasSum_norm_sq_qExpansion_coeff_mul_exp one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex W hΓ) (ModularFormClass.holo W)
      (ModularFormClass.bdd_at_infty W) hy
  have hval : ∀ x : ℝ, (⟨x + y * UpperHalfPlane.I, by simpa using hy⟩ : ℍ) = coordPoint (x, y) :=
    fun x ↦ by
      rw [coordPoint, ofComplex_apply_of_im_pos (by simpa using hy)]
      exact UpperHalfPlane.ext <| by simp
  simp_rw [hval] at h
  rwa [intervalIntegral.integral_of_le zero_le_one, ← integral_Ico_eq_integral_Ioc] at h

variable (s) in
/-- The kernel `Γ(s) (4 π n) ^ (-s)` of the Mellin transform of `exp (-4 π n y)`. -/
noncomputable def mellinKernel (n : ℕ) : ℝ :=
  (1 / (4 * π * n)) ^ s * Real.Gamma s

lemma mellinKernel_nonneg (hs : 0 < s) (n : ℕ) : 0 ≤ mellinKernel s n :=
  mul_nonneg (by positivity) (Real.Gamma_pos_of_pos hs).le

/-- **The Mellin transform of the mean square of a cusp form on horizontal lines.** With
`J(y) = ∫_0^1 |W(x + i y)| ^ 2 dx`, one has
`∫_0^∞ y ^ (s - 1) J(y) dy = ∑ |a_n| ^ 2 Γ(s) (4 π n) ^ (-s)`, provided the left side converges. -/
lemma hasSum_norm_sq_mul_mellinKernel (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (hs : 0 < s)
    (hint : IntegrableOn
      (fun y : ℝ ↦ y ^ (s - 1) * ∫ x in Ico (0 : ℝ) 1, ‖W (coordPoint (x, y))‖ ^ 2) (Ioi 0)) :
    HasSum (fun n : ℕ ↦ ‖(qExpansion 1 W).coeff n‖ ^ 2 * mellinKernel s n)
      (∫ y in Ioi (0 : ℝ), y ^ (s - 1) * ∫ x in Ico (0 : ℝ) 1, ‖W (coordPoint (x, y))‖ ^ 2) := by
  have ha0 : (qExpansion 1 W).coeff 0 = 0 := CuspFormClass.qExpansion_coeff_zero W one_pos hΓ
  let G : ℕ → ℝ → ℝ := fun n y ↦
    ‖(qExpansion 1 W).coeff n‖ ^ 2 * (y ^ (s - 1) * Real.exp (-(4 * π * n * y)))
  have hG_nonneg : ∀ n, ∀ y ∈ Ioi (0 : ℝ), 0 ≤ G n y := fun n y hy ↦ by
    have hy' : 0 < y := hy
    positivity
  have hb : ∀ {n : ℕ}, n ≠ 0 → 0 < 4 * π * (n : ℝ) := fun hn ↦
    mul_pos (by positivity) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  have hG_int : ∀ n, IntegrableOn (G n) (Ioi 0) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [G, ha0]
    · refine Integrable.const_mul ?_ _
      have h :
          IntegrableOn (fun y : ℝ ↦ y ^ (s - 1) * Real.exp (-(4 * π * n) * y ^ (1 : ℝ))) (Ioi 0) :=
        integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos (hb hn)
      refine h.congr_fun (fun y _ ↦ ?_) measurableSet_Ioi
      simp only [Real.rpow_one, neg_mul]
  have hG_val :
      ∀ n, ∫ y in Ioi (0 : ℝ), G n y = ‖(qExpansion 1 W).coeff n‖ ^ 2 * mellinKernel s n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [G, ha0]
    · simp only [G]
      rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hs (hb hn), mellinKernel]
  have hpt : ∀ y ∈ Ioi (0 : ℝ), HasSum (fun n ↦ G n y)
      (y ^ (s - 1) * ∫ x in Ico (0 : ℝ) 1, ‖W (coordPoint (x, y))‖ ^ 2) := fun y hy ↦ by
    refine ((hasSum_norm_sq_mul_exp W hΓ hy).mul_left (y ^ (s - 1))).congr_fun fun n ↦ ?_
    simp only [G]
    ring1
  have hsum : Summable fun n ↦ ∫ y in Ioi (0 : ℝ), ‖G n y‖ := by
    have hnorm : ∀ n, ∫ y in Ioi (0 : ℝ), ‖G n y‖ = ∫ y in Ioi (0 : ℝ), G n y := fun n ↦
      setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ Real.norm_of_nonneg (hG_nonneg n y hy)
    simp_rw [hnorm]
    refine summable_of_sum_range_le (c := ∫ y in Ioi (0 : ℝ), y ^ (s - 1) *
      ∫ x in Ico (0 : ℝ) 1, ‖W (coordPoint (x, y))‖ ^ 2)
      (fun n ↦ setIntegral_nonneg measurableSet_Ioi (hG_nonneg n)) fun N ↦ ?_
    rw [← integral_finsetSum _ fun n _ ↦ hG_int n]
    refine setIntegral_mono_on (integrable_finsetSum _ fun n _ ↦ hG_int n) hint measurableSet_Ioi
      fun y hy ↦ ?_
    exact sum_le_hasSum _ (fun n _ ↦ hG_nonneg n y hy) (hpt y hy)
  have hmain : HasSum (fun n ↦ ∫ y in Ioi (0 : ℝ), G n y) (∫ y in Ioi (0 : ℝ), ∑' n, G n y) :=
    hasSum_integral_of_summable_integral_norm hG_int hsum
  simp_rw [hG_val] at hmain
  rwa [setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ (hpt y hy).tsum_eq] at hmain

end RankinSelberg
