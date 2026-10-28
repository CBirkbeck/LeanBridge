import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ModularForm
import TauCeti.RepresentationTheory.ClassicalGroups.Determinant

/-!
# Scalar-valued Siegel modular forms

A Siegel modular form of weight `ρ = det^k`, the representation of `GL(g, ℂ)` of highest weight
`(k, …, k)`, is a holomorphic `f : ℋ_g → ℂ` with `f((aτ + b)(cτ + d)⁻¹) = det(cτ + d)^k f(τ)`.

## Main definitions

* `SiegelUpperHalfSpace.scalarModularForms` (LMFDB `mf.siegel`): the space `M_k(Γ)` of
  scalar-valued Siegel modular forms.

## Main results

* `SiegelUpperHalfSpace.mem_scalarModularForms_iff`: the transformation law of `M_k(Γ)`.
-/

open Matrix

namespace SiegelUpperHalfSpace

variable {n : ℕ} (k : ℤ) (Γ : Subgroup (symplecticGroup (Fin n) ℚ))
    (f : SiegelUpperHalfSpace (Fin n) → ℂ)

/-- The space `M_k(Γ)` of **scalar-valued Siegel modular forms** (LMFDB `mf.siegel`) of weight `k`
and degree `n` on a subgroup `Γ` of `Sp(2n, ℚ)`: the Siegel modular forms of weight
`ρ = det^k` (Tau Ceti's `TauCeti.detPowerRep`), whose highest weight is `(k, …, k)`. -/
noncomputable abbrev scalarModularForms : Submodule ℂ (SiegelUpperHalfSpace (Fin n) → ℂ) :=
  modularForms (TauCeti.detPowerRep ℂ n k) Γ 1

/-- **The transformation law of scalar-valued Siegel modular forms**: `f ∈ M_k(Γ)` exactly when
`f` is holomorphic and `f((aτ + b)(cτ + d)⁻¹) = det(cτ + d)^k f(τ)` for all `γ ∈ Γ` and `τ`. -/
lemma mem_scalarModularForms_iff : f ∈ scalarModularForms k Γ ↔ IsHolomorphic f ∧ ∀ γ : Γ, ∀ τ,
    f (SymplecticGroup.map (algebraMap ℚ ℝ) (γ : symplecticGroup (Fin n) ℚ) • τ) =
      (denom (SymplecticGroup.map (algebraMap ℚ ℝ) (γ : symplecticGroup (Fin n) ℚ)) τ.val).det ^ k *
        f τ := by
  simp [modularForms]

end SiegelUpperHalfSpace
