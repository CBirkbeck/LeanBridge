import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.UpperHalfPlane
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Maass forms of real weight with a multiplier system

A Maass form of weight `k ∈ ℝ` and multiplier system `v` on a subgroup `Γ` of `GL(2, ℝ)` is a
smooth function `f` on `ℍ` with `exp(-ik Arg(cz + d)) f(γz) = v(γ) f(z)` for every `γ ∈ Γ`, which
is square-integrable on `Γ \ ℍ` and an eigenfunction of the weight `k` Laplacian
`Δ_k = y² (∂²/∂x² + ∂²/∂y²) - iky ∂/∂x`.

## Main definitions

* `UpperHalfPlane.maassLaplacian` (LMFDB `mf.maass.mwf.weight`): the weight `k` Laplacian.
* `UpperHalfPlane.maassSlash` (LMFDB `mf.maass.mwf`): the unitary weight `k` slash action.
* `UpperHalfPlane.IsMaassFormOfWeight` (LMFDB `mf.maass.mwf`, `mf.maass.mwf.weight`): Maass forms
  of weight `k` and multiplier system `v`.

## Main results

* `UpperHalfPlane.isMaassFormOfWeight_zero_iff`: the Maass forms of weight `0` with trivial
  multiplier are the Maass forms of weight `0` of `UpperHalfPlane.IsMaassForm`.
-/

open MeasureTheory Matrix

open scoped ContDiff

namespace UpperHalfPlane

variable {Γ : Subgroup (GL (Fin 2) ℝ)} (k : ℝ) (f : ℂ → ℂ) {eigenvalue : ℂ}

variable (z : ℂ) in
/-- The **weight `k` Laplacian** (LMFDB `mf.maass.mwf.weight`)
`Δ_k = y² (∂²/∂x² + ∂²/∂y²) - iky ∂/∂x` at `z = x + iy`, for the unitary slash action
`maassSlash`. Its first part is `hyperbolicLaplacian`, with the sign convention of
`mf.maass.mwf.laplacian` explained there. -/
noncomputable def maassLaplacian : ℂ :=
  hyperbolicLaplacian f z - Complex.I * k * z.im * fderiv ℝ f z 1

variable (γ : GL (Fin 2) ℝ) (z : ℍ) in
/-- The **unitary weight `k` slash action** (LMFDB `mf.maass.mwf`)
`f|[γ, k](z) = exp(-ik Arg(cz + d)) f(γz)`, with `Arg` the principal argument in `(-π, π]`. -/
noncomputable def maassSlash : ℂ :=
  Complex.exp (-(Complex.I * k * (denom γ z).arg)) * f ↑(γ • z)

variable (Γ) in
/-- A function `f` on the upper half-plane, given on `ℂ`, is a **Maass form of weight `k`** (LMFDB
`mf.maass.mwf`, `mf.maass.mwf.weight`) with **multiplier system** `v` on a subgroup `Γ` of
`GL(2, ℝ)` and eigenvalue `λ` if it is smooth on `ℍ`, square-integrable on `Γ \ ℍ`, satisfies
`f|[γ, k] = v(γ) f` for every `γ ∈ Γ`, and `(Δ_k + λ) f = 0`.

The multiplier `v : Γ → S¹` is any unitary function: for non-integral weight, such as the eta
multipliers `v_η^{2k}` that the knowl mentions (not formalised here), it is not a homomorphism.
Square-integrability is taken as in `IsMaassForm` (on a fundamental domain of the image of `Γ` in
`PGL(2, ℝ)`); the knowl lists it only for weight `0`, but `|f|` is `Γ`-invariant since `v` is
unitary, and it is part of the notion of a Maass form. The condition at `γ` determines `v(γ)` where
`f ≠ 0`; for instance `-1 ∈ Γ` acts trivially with `Arg(-1) = π`, forcing `v(-1) = exp(-ikπ)` for
`f ≠ 0`. For `k ≠ 0` the knowl's groups lie in `SL(2, ℝ)`: an element of negative determinant
exchanges `Δ_k` and `Δ_{-k}`, so it leaves only degenerate forms. -/
def IsMaassFormOfWeight (v : Γ → Circle) (eigenvalue : ℂ) : Prop :=
  ContDiffOn ℝ ∞ f {z | 0 < z.im} ∧
    (∃ D : Set ℍ, IsFundamentalDomain (Γ.map ProjGenLinGroup.mk) D ∧
      IntegrableOn (fun z : ℍ ↦ ‖f z‖ ^ 2) D) ∧
    (∀ (γ : Γ) (z : ℍ), maassSlash k f γ z = v γ * f z) ∧
    ∀ z : ℂ, 0 < z.im → maassLaplacian k f z + eigenvalue * f z = 0

/-- **Weight `0` with trivial multiplier**: these Maass forms are those of `IsMaassForm`. -/
lemma isMaassFormOfWeight_zero_iff :
    IsMaassFormOfWeight Γ 0 f 1 eigenvalue ↔ IsMaassForm Γ f eigenvalue := by
  simp [IsMaassFormOfWeight, IsMaassForm, maassSlash, maassLaplacian]

end UpperHalfPlane
