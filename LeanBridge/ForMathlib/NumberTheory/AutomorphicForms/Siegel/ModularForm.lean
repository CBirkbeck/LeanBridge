import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.CongruenceSubgroups
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.UpperHalfSpace
import Mathlib.RepresentationTheory.Basic

/-!
# Siegel modular forms with character

For a representation `ρ` of `GL(g, ℂ)` on a complex vector space `V`, a subgroup `Γ` of
`Sp(2g, ℚ)` and a character `ψ` of `Γ`, a Siegel modular form of weight `ρ` and character `ψ` on
`Γ` is a holomorphic `f : ℋ_g → V` with `f((aτ + b)(cτ + d)⁻¹) = ψ(γ) ρ(cτ + d) f(τ)` for all
`γ = (a, b; c, d) ∈ Γ`. Equivalently `f ∣ γ = ψ(γ) f` for the slash operator
`(f ∣ γ)(τ) = ρ(cτ + d)⁻¹ f(γτ)`, a right action of `Sp(2g, ℝ)` by the cocycle relation of
`cτ + d`.

## Main definitions

* `SiegelUpperHalfSpace.slash`: the slash operator of weight `ρ`.
* `SiegelUpperHalfSpace.modularForms` (LMFDB `mf.siegel.character`): the space `M_ρ(Γ, ψ)`.

## Main results

* `SiegelUpperHalfSpace.slash_mul`: the slash operator is a right action.
* `SiegelUpperHalfSpace.mem_modularForms_iff_slash`: `f ∈ M_ρ(Γ, ψ)` exactly when `f` is
  holomorphic and `f ∣ γ = ψ(γ) f` for every `γ ∈ Γ`.
-/

open Module

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] [DecidableEq l] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL l ℂ) V) (γ γ' : Matrix.symplecticGroup l ℝ)
    (f : SiegelUpperHalfSpace l → V) (τ : SiegelUpperHalfSpace l)

lemma denomGL_one : denomGL 1 τ = 1 := by
  have h : denomGL (1 * 1) τ = denomGL 1 ((1 : Matrix.symplecticGroup l ℝ) • τ) * denomGL 1 τ :=
    denomGL_mul 1 1 τ
  rw [one_mul, one_smul] at h
  exact left_eq_mul.mp h

/-- The **slash operator** `(f ∣ γ)(τ) = ρ(cτ + d)⁻¹ f(γτ)` of weight `ρ` by
`γ = (a, b; c, d) ∈ Sp(2g, ℝ)` on functions `f : ℋ_g → V`. -/
noncomputable def slash : SiegelUpperHalfSpace l → V :=
  fun τ ↦ ρ (denomGL γ τ)⁻¹ (f (γ • τ))

lemma slash_apply : slash ρ γ f τ = ρ (denomGL γ τ)⁻¹ (f (γ • τ)) :=
  rfl

/-- **The slash operator is a right action**: `f ∣ γγ' = (f ∣ γ) ∣ γ'`, by the cocycle relation
`denom_mul` of the automorphy factor. -/
lemma slash_mul : slash ρ (γ * γ') f = slash ρ γ' (slash ρ γ f) := by
  ext τ
  rw [slash_apply, slash_apply, slash_apply, denomGL_mul, mul_inv_rev, map_mul, mul_smul,
    End.mul_apply]

lemma slash_one : slash ρ 1 f = f := by
  ext τ
  rw [slash_apply, denomGL_one, inv_one, map_one, one_smul, End.one_apply]

lemma slash_zero : slash ρ γ (0 : SiegelUpperHalfSpace l → V) = 0 := by
  ext τ
  simp [slash_apply]

lemma slash_add (g : SiegelUpperHalfSpace l → V) :
    slash ρ γ (f + g) = slash ρ γ f + slash ρ γ g := by
  ext τ
  simp [slash_apply]

lemma slash_smul (c : ℂ) : slash ρ γ (c • f) = c • slash ρ γ f := by
  ext τ
  simp [slash_apply]

variable (Γ : Subgroup (Matrix.symplecticGroup l ℚ)) (ψ : Γ →* ℂˣ)

/-- The space `M_ρ(Γ, ψ)` of **Siegel modular forms with character `ψ`** (LMFDB
`mf.siegel.character`) and weight `ρ` on a subgroup `Γ` of `Sp(2g, ℚ)`: the holomorphic
`f : ℋ_g → V` with `f((aτ + b)(cτ + d)⁻¹) = ψ(γ) ρ(cτ + d) f(τ)` for every
`γ = (a, b; c, d) ∈ Γ` and `τ ∈ ℋ_g`. With the trivial character it is the space `M_ρ(Γ)` of
Siegel modular forms of weight `ρ` (LMFDB `mf.siegel`).

The LMFDB takes `Γ` to be an arithmetic subgroup of `GSp(2g, ℚ)`, `ρ` finite-dimensional and
`g ≥ 2`. Its transformation law has no similitude factor, and the elements of an arithmetic
subgroup of `GSp(2g, ℚ)` have similitude `±1`, those with `-1` mapping `ℋ_g` to its complex
conjugate; so `Γ` is taken in `Sp(2g, ℚ)`, where the LMFDB's groups (`Γ(N)`, `Γ₀(N)`, the
paramodular groups) lie. Arithmeticity, finite dimension and `g ≥ 2` are not imposed: for `g ≥ 2`
and arithmetic `Γ`, Koecher's principle makes a condition at the cusps superfluous, but for `g = 1`
the space is larger than that of modular forms, as it has no condition at the cusps. -/
def modularForms : Submodule ℂ (SiegelUpperHalfSpace l → V) where
  carrier := {f | IsHolomorphic f ∧ ∀ γ : Γ, ∀ τ,
    f (SymplecticGroup.map (algebraMap ℚ ℝ) (γ : Matrix.symplecticGroup l ℚ) • τ) = (ψ γ : ℂ) •
      ρ (denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (γ : Matrix.symplecticGroup l ℚ)) τ) (f τ)}
  add_mem' {f g} hf hg := ⟨hf.1.add hg.1, fun γ τ ↦ by
    simp [hf.2 γ τ, hg.2 γ τ]⟩
  zero_mem' := ⟨isHolomorphic_zero, fun γ τ ↦ by simp⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, fun γ τ ↦ by
    simp [hf.2 γ τ, smul_comm c]⟩

/-- **The transformation law in slash form**: `f ∈ M_ρ(Γ, ψ)` exactly when `f` is holomorphic
and `f ∣ γ = ψ(γ) f` for every `γ ∈ Γ`. -/
lemma mem_modularForms_iff_slash : f ∈ modularForms ρ Γ ψ ↔ IsHolomorphic f ∧ ∀ γ : Γ,
    slash ρ (SymplecticGroup.map (algebraMap ℚ ℝ) (γ : Matrix.symplecticGroup l ℚ)) f =
      (ψ γ : ℂ) • f := by
  refine and_congr_right fun _ ↦ forall_congr' fun γ ↦ ?_
  rw [funext_iff]
  refine forall_congr' fun τ ↦ ?_
  rw [slash_apply, Pi.smul_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, map_smul, ← End.mul_apply, ← map_mul, inv_mul_cancel, map_one, End.one_apply]
  · rw [← map_smul, ← h, ← End.mul_apply, ← map_mul, mul_inv_cancel, map_one, End.one_apply]

lemma const_mem_modularForms (v : V) :
    Function.const _ v ∈ modularForms (Representation.trivial ℂ (GL l ℂ) V) Γ 1 := by
  refine ⟨fun φ ↦ (differentiableOn_const (φ v)).congr fun Z hZ ↦ ?_, fun γ τ ↦ by simp⟩
  have hZ' : ((symmetrize Z).map Complex.im).PosDef := hZ
  simp [extend, hZ']

end SiegelUpperHalfSpace
