import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.UpperHalfSpace
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Theta constants of the Siegel upper half-space

The theta constant of characteristic `m = (μ, ν) ∈ ℤ^g × ℤ^g` is the function
`θ_m(Ω) = ∑_{n ∈ ℤ^g} e^{2πi (½ (n + μ/2)ᵀ Ω (n + μ/2) + (n + μ/2)ᵀ ν/2)}` on the Siegel upper
half-space `ℋ_g`. In degree `2`, with `μ, ν ∈ {0, 1}²`, the ten even characteristics (those with
`μ·ν` even) give the ten theta constants `θ_{μ₁μ₂ν₁ν₂}` from which the LMFDB builds generators of
rings of Siegel modular forms (LMFDB `mf.siegel.family.gamma0_2`, `mf.siegel.family.gamma0_4`).

## Main definitions

* `SiegelUpperHalfSpace.thetaConstant`: the theta constant `θ_m`.
* `SiegelUpperHalfSpace.double`: the map `Ω ↦ 2Ω` of `ℋ_g`.

## Main results

* `SiegelUpperHalfSpace.thetaConstant_zero_zero`: in degree `1`, the theta constant of
  characteristic `0` is Jacobi's theta function `θ(τ) = ∑ e^{πin²τ}`.
-/

open Complex Matrix Real

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] (μ ν : l → ℤ) (Ω : SiegelUpperHalfSpace l)

/-- The **theta constant** `θ_m` of characteristic `m = (μ, ν) ∈ ℤ^g × ℤ^g` (LMFDB
`mf.siegel.theta_constant`) on the Siegel upper half-space:
`θ_m(Ω) = ∑_{n ∈ ℤ^g} e^{πi ((n + μ/2)ᵀ Ω (n + μ/2) + (n + μ/2)ᵀ ν)}`, that is
`e^{2πi (½ (n + μ/2)ᵀ Ω (n + μ/2) + (n + μ/2)ᵀ ν/2)}`. The knowl's formula omits the factor `2πi`
in the exponent, without which the series diverges; this is the standard theta constant, as in
the knowl `mf.siegel.family.gamma_2`. The series converges absolutely, which is not proved
here. -/
noncomputable def thetaConstant : ℂ :=
  ∑' n : l → ℤ, letI x : l → ℂ := fun i ↦ n i + μ i / 2
    cexp (π * I * (x ⬝ᵥ Ω.val *ᵥ x + x ⬝ᵥ fun i ↦ (ν i : ℂ)))

/-- **In degree `1` the theta constant of characteristic `0` is Jacobi's theta function**
`θ(τ) = ∑_{n ∈ ℤ} e^{πin²τ}`. -/
lemma thetaConstant_zero_zero [Unique l] :
    thetaConstant 0 0 Ω = jacobiTheta (Ω.val default default) := by
  rw [thetaConstant, jacobiTheta, ← (Equiv.funUnique l ℤ).symm.tsum_eq]
  refine tsum_congr fun n ↦ congrArg cexp ?_
  simp [dotProduct, mulVec]
  ring1

variable [DecidableEq l] in
/-- The map `Ω ↦ 2Ω` of the Siegel upper half-space; the LMFDB writes `F(2Ω)` for `F ∘ double`. -/
def double : SiegelUpperHalfSpace l where
  val := (2 : ℂ) • Ω.val
  transpose_val := by rw [transpose_smul, Ω.transpose_val]
  posDef_im := by
    have h : ((2 : ℂ) • Ω.val).map im = (2 : ℝ) • Ω.val.map im := by
      ext i j
      simp
    rw [h]
    exact Ω.posDef_im.smul two_pos

end SiegelUpperHalfSpace
