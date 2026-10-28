import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.UpperHalfSpace
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Maass forms on the Picard group

The Picard group `PSL(2, ℤ[i])` acts on hyperbolic 3-space `ℋ₃` through `PSL(2, ℂ)`. A Maass
form on it is a smooth function on `ℋ₃` that is invariant under the Picard group, square-integrable
on the quotient, and an eigenfunction `(Δ + λ) f = 0` of the hyperbolic Laplacian.

## Main definitions

* `HyperbolicThreeSpace.PicardGroup` (LMFDB `mf.maass.picard`): the Picard group.
* `HyperbolicThreeSpace.IsPicardMaassForm` (LMFDB `mf.maass.picard`): Maass forms on it.
-/

open MeasureTheory
open scoped ContDiff

namespace HyperbolicThreeSpace

/-- The **Picard group** `Γ = PSL(2, ℤ[i])` (LMFDB `mf.maass.picard`), acting on hyperbolic 3-space
by `z ↦ (az + b)(cz + d)⁻¹` through `PSL(2, ℂ)`. -/
abbrev PicardGroup : Type :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) GaussianInt

/-- A function `f` on hyperbolic 3-space, given on `ℂ × ℝ`, is a **Maass form** (LMFDB
`mf.maass.picard`) on the Picard group `Γ = PSL(2, ℤ[i])` with eigenvalue `λ` if it is smooth on
`ℋ₃ = {(x, y) | y > 0}`, square-integrable on `Γ \ ℋ₃`, invariant under `Γ`, and an eigenfunction
`(Δ + λ) f = 0` of the hyperbolic Laplacian.

Square-integrability on `Γ \ ℋ₃` is stated as the integrability of `|f|²` on a fundamental domain
of `Γ` for the hyperbolic volume `dx₁ dx₂ dy / y³`. Fundamental domains exist, such as Picard's
`{|x₁| ≤ 1/2, 0 ≤ x₂ ≤ 1/2, |x|² + y² ≥ 1}`, since `Γ` is discrete, and the integral of the
`Γ`-invariant function `|f|²` does not depend on the choice, since the hyperbolic volume is
invariant under `PSL(2, ℂ)`; neither fact, nor the action axioms for the action of `PSL(2, ℂ)` by
the LMFDB's formula, is proved here. -/
def IsPicardMaassForm (f : ℂ × ℝ → ℂ) (eigenvalue : ℂ) : Prop :=
  ContDiffOn ℝ ∞ f {p | 0 < p.2} ∧
    (∃ D : Set HyperbolicThreeSpace, IsFundamentalDomain PicardGroup D hyperbolicVolume ∧
      IntegrableOn (fun p ↦ ‖f p.coords‖ ^ 2) D hyperbolicVolume) ∧
    (∀ (γ : PicardGroup) (p : HyperbolicThreeSpace), f (γ • p).coords = f p.coords) ∧
    ∀ p : ℂ × ℝ, 0 < p.2 → laplacian f p + eigenvalue * f p = 0

end HyperbolicThreeSpace
