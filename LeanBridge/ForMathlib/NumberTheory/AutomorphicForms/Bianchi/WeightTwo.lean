import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.UpperHalfSpace
import Mathlib.GroupTheory.Index
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Cuspidality of weight 2 Bianchi modular forms

A weight 2 Bianchi modular form is a function `F : ℋ₃ → ℂ³`, transforming under the weight 2 slash
operator `(F ∣ γ)(x, y) = (|r|² + |s|²)⁻¹ M(r, s) F(γ(x, y))`, where `r = cx + d`, `s = cy` and
`M(r, s)` is the explicit matrix below, and such that `F₁ β₁ + F₂ β₂ + F₃ β₃` is a harmonic
`Γ`-invariant differential 1-form on `ℋ₃`. It is cuspidal if the constant term of `F ∣ γ` vanishes
for every `γ ∈ PSL(2, 𝓞_K)`: `∫_{ℂ / Λ} (F ∣ γ)(x, y) dx = 0` for the lattices `Λ` of periods of
`F ∣ γ`.

## Main definitions

* `HyperbolicThreeSpace.slashTwo`: the weight 2 slash operator.
* `HyperbolicThreeSpace.integerLattice`: the ring of integers `𝓞_K`, embedded in `ℂ`.
* `HyperbolicThreeSpace.IsCuspidalWeightTwo` (LMFDB `mf.bianchi.weight2`): cuspidality.
-/

open Complex Matrix MeasureTheory NumberField
open scoped ComplexConjugate MatrixGroups

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] [NumberField K] (σ : K →+* ℂ) (F : ℂ × ℝ → Fin 3 → ℂ)

/-- The **weight 2 slash operator** `F ∣ γ` of `γ = (a, b; c, d) ∈ SL(2, ℂ)` on `F : ℋ₃ → ℂ³`,
given on `ℂ × ℝ` (LMFDB `mf.bianchi.weight2`): `(F ∣ γ)(x, y) = (|r|² + |s|²)⁻¹ M F(γ(x, y))` with
`M = (r̄², 2r̄s, s²; -r̄s̄, |r|² - |s|², rs; s̄², -2rs̄, r²)`, where `r = cx + d` and `s = cy`. -/
noncomputable def slashTwo (γ : SL(2, ℂ)) (p : ℂ × ℝ) : Fin 3 → ℂ :=
  letI r : ℂ := γ 1 0 * p.1 + γ 1 1
  letI s : ℂ := γ 1 0 * p.2
  ((normSq r + normSq s : ℝ) : ℂ)⁻¹ • !![conj r ^ 2, 2 * conj r * s, s ^ 2;
    -(conj r * conj s), ((normSq r - normSq s : ℝ) : ℂ), r * s;
    conj s ^ 2, -2 * r * conj s, r ^ 2] *ᵥ F (moebius γ p)

/-- The ring of integers `𝓞_K` of `K`, embedded in `ℂ` by `σ`, as an additive subgroup. -/
def integerLattice : AddSubgroup ℂ :=
  (σ.comp (algebraMap (𝓞 K) K)).range.toAddSubgroup

/-- A function `F : ℋ₃ → ℂ³`, given on `ℂ × ℝ`, is **cuspidal** (LMFDB `mf.bianchi.weight2`) for
the imaginary quadratic field `K` embedded in `ℂ` by `σ` if the constant term of `F ∣ γ` vanishes
for every `γ ∈ SL(2, 𝓞_K)`: for every `y > 0` and every subgroup `Λ` of finite index of `𝓞_K`
such that `x ↦ (F ∣ γ)(x, y)` is `Λ`-periodic, `∫_{ℂ / Λ} (F ∣ γ)(x, y) dx = 0`, the integral
being over any fundamental domain of `Λ` in `ℂ`. Here `∣` is the weight 2 slash operator, and the
sign of `γ` does not matter.

The LMFDB writes `∫_{ℂ / 𝓞_K} (F ∣ γ)(x, y) dx = 0`, which only makes sense when `F ∣ γ` is
periodic under all of `𝓞_K`, as for `Γ = PSL(2, 𝓞_K)`. For a congruence subgroup `Γ`, `F ∣ γ` is
only periodic under a sublattice (the level `𝔑` when `Γ(𝔑) ⊆ Γ`), and the condition is the
vanishing of the constant term of the Fourier–Bessel expansion of `F ∣ γ`, as the knowl also says;
when `F ∣ γ` is `𝓞_K`-periodic, the two agree.

This is the cuspidality condition only: the harmonicity of the 1-form `F₁ β₁ + F₂ β₂ + F₃ β₃`,
which makes `F` a weight 2 Bianchi modular form, needs the Hodge Laplacian on differential forms
on `ℋ₃` and is not formalised. -/
def IsCuspidalWeightTwo : Prop :=
  ∀ γ : SL(2, 𝓞 K),
    letI G : ℂ × ℝ → Fin 3 → ℂ := slashTwo F (SpecialLinearGroup.map (σ.comp (algebraMap _ K)) γ)
    ∀ (y : ℝ) (Λ : AddSubgroup ℂ), 0 < y → Λ ≤ integerLattice σ →
      Λ.relIndex (integerLattice σ) ≠ 0 → (∀ x, ∀ a ∈ Λ, G (x + a, y) = G (x, y)) →
      ∀ P : Set ℂ, IsAddFundamentalDomain Λ P → ∫ x in P, G (x, y) = 0

end HyperbolicThreeSpace
