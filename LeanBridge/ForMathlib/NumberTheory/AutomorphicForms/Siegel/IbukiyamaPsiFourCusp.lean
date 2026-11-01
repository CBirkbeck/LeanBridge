import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.IbukiyamaPsiFour

/-!
# The Siegel operator of `f₁₁(2Ω)` at the standard cusp

The form `f₁₁(2Ω) = f₆(2Ω) χ₅(2Ω)` of weight 11 on `Γ₀(4)` (LMFDB
`mf.siegel.family.gamma0_4_psi_4`; the generator `χ₁₁ = f₁₁(2Ω)/4096` of Aoki and Ibukiyama, §5)
is a cusp form. This file proves the cusp condition at the standard cusp: `Φ(f₁₁(2Ω)) = 0`, that is
`f₁₁(2 diag(τ', it)) → 0` as `t → ∞`. At `W = 2 diag(τ', it)` the term `n` of the theta series of
characteristic `(μ, ν)` has absolute value `e^{-π(2 Im(τ') x₁² + 2t x₂²)}`, `x = n + μ/2`, so every
theta constant is bounded for `t ≥ 1` by the sum of these terms at `t = 1`, and when `μ₂` is odd,
`x₂² ≥ 1/4` and the theta constant is at most `e^{-π(t - 1)/2}` times that sum. The factor
`θ₀₁₀₀` of `χ₅` therefore tends to 0, and the other factors of `f₁₁` stay bounded.

The cusp condition at the other cusps, `Φ(f₁₁(2Ω) ∣ γ) = 0` for every `γ ∈ Sp(4, ℚ)`, is not proved
here: it needs the transformation of `f₁₁(2Ω)` under all of `Sp(4, ℤ)`, that is of `f₁₁` under the
conjugates of `Sp(4, ℤ)` by `diag(2, 2, 1, 1)`.

## Main results

* `SiegelUpperHalfSpace.Ibukiyama.tendsto_f11_double_diagPoint`: `f₁₁(2 diag(τ', it)) → 0` as
  `t → ∞`.
* `SiegelUpperHalfSpace.Ibukiyama.siegelOperatorVanishes_f11_comp_double`: `Φ(f₁₁(2Ω)) = 0`.
-/

open Asymptotics Complex Filter Matrix Real Topology

open scoped UpperHalfPlane

namespace SiegelUpperHalfSpace.Ibukiyama

variable (τ' : ℍ) (μ ν : Fin 2 → ℤ) (t : Set.Ioi (0 : ℝ)) (a b c d : ℤ)

private lemma norm_term_double_diagPoint (n : Fin 2 → ℤ) :
    ‖cexp (π * I * ((fun i ↦ (n i : ℂ) + μ i / 2) ⬝ᵥ (double (diagPoint τ' t)).val *ᵥ
      (fun i ↦ (n i : ℂ) + μ i / 2) + (fun i ↦ (n i : ℂ) + μ i / 2) ⬝ᵥ fun i ↦ (ν i : ℂ)))‖ =
      rexp (-(π * (2 * τ'.im * (n 0 + μ 0 / 2 : ℝ) ^ 2 + 2 * t * (n 1 + μ 1 / 2 : ℝ) ^ 2))) := by
  rw [Complex.norm_exp]
  congr 1
  simp [double, diagPoint, dotProduct]
  ring1

private lemma summable_rexp_double_diagPoint :
    Summable fun n : Fin 2 → ℤ ↦
      rexp (-(π * (2 * τ'.im * (n 0 + μ 0 / 2 : ℝ) ^ 2 + 2 * t * (n 1 + μ 1 / 2 : ℝ) ^ 2))) := by
  simpa only [norm_term_double_diagPoint τ' μ 0] using
    summable_norm_iff.mpr (summable_thetaConstant_term (double (diagPoint τ' t)) μ 0)

lemma norm_thetaConstant_double_diagPoint_le {r : ℝ} (hr : ∀ n : ℤ, r ≤ (n + μ 1 / 2 : ℝ) ^ 2)
    (ht : 1 ≤ (t : ℝ)) : ‖thetaConstant μ ν (double (diagPoint τ' t))‖ ≤
      rexp (-(2 * π * r * ((t : ℝ) - 1))) * ∑' n : Fin 2 → ℤ,
        rexp (-(π * (2 * τ'.im * (n 0 + μ 0 / 2 : ℝ) ^ 2 + 2 * (n 1 + μ 1 / 2 : ℝ) ^ 2))) := by
  have h1 : Summable fun n : Fin 2 → ℤ ↦
      rexp (-(π * (2 * τ'.im * (n 0 + μ 0 / 2 : ℝ) ^ 2 + 2 * (n 1 + μ 1 / 2 : ℝ) ^ 2))) := by
    simpa only [mul_one] using summable_rexp_double_diagPoint τ' μ ⟨1, Set.mem_Ioi.mpr one_pos⟩
  rw [thetaConstant, ← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm (summable_norm_iff.mpr
    (summable_thetaConstant_term (double (diagPoint τ' t)) μ ν))).trans ?_
  simp only [norm_term_double_diagPoint]
  refine Summable.tsum_le_tsum (fun n ↦ ?_) (summable_rexp_double_diagPoint τ' μ t)
    (h1.mul_left _)
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith [hr (n 1), Real.pi_pos, mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr (hr (n 1)))]

lemma isBigO_theta_double_diagPoint :
    (fun s : Set.Ioi (0 : ℝ) ↦ theta a b c d (double (diagPoint τ' s))) =O[atTop]
      fun _ ↦ (1 : ℂ) := by
  refine IsBigO.of_bound (∑' n : Fin 2 → ℤ, rexp (-(π * (2 * τ'.im *
    (n 0 + (![a, b] 0 : ℤ) / 2 : ℝ) ^ 2 + 2 * (n 1 + (![a, b] 1 : ℤ) / 2 : ℝ) ^ 2)))) ?_
  filter_upwards [eventually_ge_atTop ⟨1, Set.mem_Ioi.mpr one_pos⟩] with s hs
  simpa using norm_thetaConstant_double_diagPoint_le τ' ![a, b] ![c, d] s (fun n ↦ sq_nonneg _) hs

lemma tendsto_theta_double_diagPoint :
    Tendsto (fun s : Set.Ioi (0 : ℝ) ↦ theta a 1 c d (double (diagPoint τ' s))) atTop (𝓝 0) := by
  have hc (n : ℤ) : (1 / 4 : ℝ) ≤ (n + (![a, 1] 1 : ℤ) / 2 : ℝ) ^ 2 := by
    have h : (0 : ℤ) ≤ n * (n + 1) := by
      rcases le_or_gt 0 n with h | h
      · exact mul_nonneg h (by omega)
      · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    have h' : (0 : ℝ) ≤ n * (n + 1) := mod_cast h
    simp only [cons_val_one, cons_val_fin_one]
    nlinarith
  have hv : Tendsto (fun s : Set.Ioi (0 : ℝ) ↦ (s : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have hl : Tendsto (fun s : Set.Ioi (0 : ℝ) ↦ -(2 * π * (1 / 4) * ((s : ℝ) - 1))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp <| Tendsto.const_mul_atTop (by positivity) <| by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-1) hv
  have he : Tendsto (fun s : Set.Ioi (0 : ℝ) ↦ rexp (-(2 * π * (1 / 4) * ((s : ℝ) - 1))) *
      ∑' n : Fin 2 → ℤ, rexp (-(π * (2 * τ'.im * (n 0 + (![a, 1] 0 : ℤ) / 2 : ℝ) ^ 2 +
        2 * (n 1 + (![a, 1] 1 : ℤ) / 2 : ℝ) ^ 2)))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hl).mul_const _
  refine squeeze_zero_norm' ?_ he
  filter_upwards [eventually_ge_atTop ⟨1, Set.mem_Ioi.mpr one_pos⟩] with s hs
  exact norm_thetaConstant_double_diagPoint_le τ' ![a, 1] ![c, d] s hc hs

/-- **`f₁₁(2Ω)` vanishes at the standard cusp**: `f₁₁(2 diag(τ', it)) → 0` as `t → ∞`. The factor
`θ₀₁₀₀(2 diag(τ', it))` of `χ₅(2 diag(τ', it))` tends to 0, as `e^{-π(t - 1)/2}`, and the other
theta constants of `f₁₁ = f₆ χ₅` are bounded for `t ≥ 1`. -/
lemma tendsto_f11_double_diagPoint :
    Tendsto (fun s : Set.Ioi (0 : ℝ) ↦ f11 (double (diagPoint τ' s))) atTop (𝓝 0) := by
  have h6 : (fun s : Set.Ioi (0 : ℝ) ↦ f6 (double (diagPoint τ' s))) =O[atTop]
      fun _ ↦ (1 : ℂ) := by
    simpa [f6] using ((((isBigO_theta_double_diagPoint τ' 0 0 0 1).pow 4).sub
      ((isBigO_theta_double_diagPoint τ' 0 0 1 0).pow 4)).mul
        (((isBigO_theta_double_diagPoint τ' 0 0 0 1).pow 4).sub
          ((isBigO_theta_double_diagPoint τ' 0 0 1 1).pow 4))).mul
            (((isBigO_theta_double_diagPoint τ' 0 0 1 0).pow 4).sub
              ((isBigO_theta_double_diagPoint τ' 0 0 1 1).pow 4))
  have h5 : (fun s : Set.Ioi (0 : ℝ) ↦ chi5 (double (diagPoint τ' s))) =o[atTop]
      fun _ ↦ (1 : ℂ) := by
    simpa [chi5] using ((((((((((isBigO_theta_double_diagPoint τ' 0 0 0 0).mul
      (isBigO_theta_double_diagPoint τ' 0 0 0 1)).mul
        (isBigO_theta_double_diagPoint τ' 0 0 1 0)).mul
          (isBigO_theta_double_diagPoint τ' 0 0 1 1)).mul_isLittleO
            ((isLittleO_one_iff ℂ).mpr (tendsto_theta_double_diagPoint τ' 0 0 0))).mul_isBigO
              (isBigO_theta_double_diagPoint τ' 0 1 1 0)).mul_isBigO
                (isBigO_theta_double_diagPoint τ' 1 0 0 0)).mul_isBigO
                  (isBigO_theta_double_diagPoint τ' 1 0 0 1)).mul_isBigO
                    (isBigO_theta_double_diagPoint τ' 1 1 0 0)).mul_isBigO
                      (isBigO_theta_double_diagPoint τ' 1 1 1 1))
  rw [← isLittleO_one_iff ℂ]
  simpa [f11] using h6.mul_isLittleO h5

/-- **The Siegel operator kills `f₁₁(2Ω)`** (LMFDB `mf.siegel.family.gamma0_4_psi_4`):
`Φ(f₁₁(2Ω)) = 0`, the cusp condition for `f₁₁(2Ω)` at the standard cusp, `γ = 1`. -/
lemma siegelOperatorVanishes_f11_comp_double : SiegelOperatorVanishes (f11 ∘ double) :=
  fun x φ ↦ by
    have hφ (z : ℂ) : φ z = z * φ 1 := by
      rw [← smul_eq_mul, ← φ.map_smul, smul_eq_mul, mul_one]
    have h :
        Tendsto (fun s : Set.Ioi (0 : ℝ) ↦ f11 (double (diagPoint x s)) * φ 1) atTop (𝓝 0) := by
      simpa using (tendsto_f11_double_diagPoint x).mul_const (φ 1)
    exact h.congr fun s ↦ (hφ _).symm

end SiegelUpperHalfSpace.Ibukiyama
