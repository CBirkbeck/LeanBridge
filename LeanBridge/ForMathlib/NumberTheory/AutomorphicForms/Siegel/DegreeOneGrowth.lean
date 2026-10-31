import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ModularForm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The growth condition on Siegel modular forms of degree `1`

In degree `g ≥ 2` a Siegel modular form is a holomorphic `F : ℋ_g → V` with
`F((AZ + B)(CZ + D)⁻¹) = ρ(CZ + D) F(Z)` (`SiegelUpperHalfSpace.modularForms`); by Koecher's
principle no condition at the cusps is needed. In degree `1` the LMFDB also imposes a growth
condition: there is `ε > 0` with `|F(x + iy)| ≪ y^ε` for `y ≥ 1`. Here `ℋ_1` is the Siegel upper
half-space of `1 × 1` matrices, indexed by `Fin 1`, and `x + iy` is the entry of `τ ∈ ℋ_1`.

## Main definitions

* `SiegelUpperHalfSpace.HasModerateGrowth` (LMFDB `mf.siegel.vector_valued`): the growth condition
  `|F(x + iy)| ≪ y^ε` for `y ≥ 1`.
* `SiegelUpperHalfSpace.modularFormsDegreeOne` (LMFDB `mf.siegel.vector_valued`): the space of
  Siegel modular forms of degree `1`, with the growth condition at every cusp.

## Main results

* `SiegelUpperHalfSpace.HasModerateGrowth.add` and
  `SiegelUpperHalfSpace.HasModerateGrowth.const_smul`: the growth condition is linear.
-/

open Module

namespace SiegelUpperHalfSpace

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {F G : SiegelUpperHalfSpace (Fin 1) → V}
    (ρ : Representation ℂ (GL (Fin 1) ℂ) V) (Γ : Subgroup (Matrix.symplecticGroup (Fin 1) ℚ))
    (ψ : Γ →* ℂˣ)

variable (F) in
/-- A function `F : ℋ_1 → V` satisfies the **growth condition** of Siegel modular forms of degree
`1` (LMFDB `mf.siegel.vector_valued`): there is `ε > 0` with `|F(x + iy)| ≪ y^ε` for `y ≥ 1`,
uniformly in `x`, where `x + iy` is the entry of `τ ∈ ℋ_1`. The absolute value is taken
coordinatewise, through every linear form `φ` on `V` with a constant depending on `φ`, which for
finite-dimensional `V` is the condition for any norm on `V`. -/
def HasModerateGrowth : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ φ : Dual ℂ V, ∃ C : ℝ, ∀ τ : SiegelUpperHalfSpace (Fin 1),
    1 ≤ (τ.val 0 0).im → ‖φ (F τ)‖ ≤ C * (τ.val 0 0).im ^ ε

lemma hasModerateGrowth_zero : HasModerateGrowth (0 : SiegelUpperHalfSpace (Fin 1) → V) :=
  ⟨1, one_pos, fun _ ↦ ⟨0, fun _ _ ↦ by simp⟩⟩

/-- **The growth condition is additive**, with the larger of the two exponents. -/
lemma HasModerateGrowth.add (hF : HasModerateGrowth F) (hG : HasModerateGrowth G) :
    HasModerateGrowth (F + G) := by
  rcases hF with ⟨ε, hε, hF⟩
  rcases hG with ⟨δ, -, hG⟩
  refine ⟨max ε δ, lt_max_of_lt_left hε, fun φ ↦ ?_⟩
  rcases hF φ with ⟨C, hC⟩
  rcases hG φ with ⟨D, hD⟩
  refine ⟨|C| + |D|, fun τ hτ ↦ ?_⟩
  have hε' : (τ.val 0 0).im ^ ε ≤ (τ.val 0 0).im ^ max ε δ :=
    Real.rpow_le_rpow_of_exponent_le hτ (le_max_left ε δ)
  have hδ' : (τ.val 0 0).im ^ δ ≤ (τ.val 0 0).im ^ max ε δ :=
    Real.rpow_le_rpow_of_exponent_le hτ (le_max_right ε δ)
  have hy (s : ℝ) : 0 ≤ (τ.val 0 0).im ^ s := Real.rpow_nonneg (zero_le_one.trans hτ) s
  rw [Pi.add_apply, map_add]
  refine (norm_add_le _ _).trans <| (add_le_add (hC τ hτ) (hD τ hτ)).trans ?_
  nlinarith [le_abs_self C, le_abs_self D, abs_nonneg C, abs_nonneg D, hy ε, hy δ]

/-- **The growth condition is preserved by scalars.** -/
lemma HasModerateGrowth.const_smul (hF : HasModerateGrowth F) (c : ℂ) :
    HasModerateGrowth (c • F) := by
  rcases hF with ⟨ε, hε, hF⟩
  refine ⟨ε, hε, fun φ ↦ ?_⟩
  rcases hF φ with ⟨C, hC⟩
  refine ⟨‖c‖ * C, fun τ hτ ↦ ?_⟩
  rw [Pi.smul_apply, map_smul, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC τ hτ) (norm_nonneg c)

/-- The space of **Siegel modular forms of degree `1`** (LMFDB `mf.siegel.vector_valued`), weight
`ρ` and character `ψ` on a subgroup `Γ` of `Sp(2, ℚ)`: the `F ∈ M_ρ(Γ, ψ)`
(`SiegelUpperHalfSpace.modularForms`) such that `F ∣_ρ γ` satisfies the growth condition
`|(F ∣_ρ γ)(x + iy)| ≪ y^ε` for `y ≥ 1` (`SiegelUpperHalfSpace.HasModerateGrowth`) for every
`γ ∈ Sp(2, ℚ)`. The knowl states the condition for `F` itself (`γ = 1`), which suffices when `Γ`
has a single cusp, as `Sp(2, ℤ) ≅ SL(2, ℤ)` does; for a general `Γ` it is needed at every cusp,
as in the classical definition of modular forms. -/
def modularFormsDegreeOne : Submodule ℂ (SiegelUpperHalfSpace (Fin 1) → V) where
  carrier := {F | F ∈ modularForms ρ Γ ψ ∧
    ∀ γ : Matrix.symplecticGroup (Fin 1) ℚ,
      HasModerateGrowth (slash ρ (SymplecticGroup.map (algebraMap ℚ ℝ) γ) F)}
  add_mem' hF hG := ⟨add_mem hF.1 hG.1, fun γ ↦ by
    rw [slash_add]
    exact (hF.2 γ).add (hG.2 γ)⟩
  zero_mem' := ⟨zero_mem _, fun γ ↦ by
    rw [slash_zero]
    exact hasModerateGrowth_zero⟩
  smul_mem' c _ hF := ⟨Submodule.smul_mem _ c hF.1, fun γ ↦ by
    rw [slash_smul]
    exact (hF.2 γ).const_smul c⟩

lemma modularFormsDegreeOne_le_modularForms :
    modularFormsDegreeOne ρ Γ ψ ≤ modularForms ρ Γ ψ :=
  fun _ hF ↦ hF.1

lemma HasModerateGrowth.of_mem_modularFormsDegreeOne (hF : F ∈ modularFormsDegreeOne ρ Γ ψ) :
    HasModerateGrowth F := by
  simpa [slash_one] using hF.2 1

end SiegelUpperHalfSpace
