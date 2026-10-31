import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ModularForm
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PhiOperator

/-!
# Siegel cusp forms of every degree

A Siegel modular form `f` of degree `g ≥ 1`, weight `ρ` and character `ψ` on `Γ ≤ Sp(2g, ℚ)` is a
cusp form if `Φ(f ∣_ρ γ) = 0` for every `γ ∈ Sp(2g, ℚ)`, where `∣_ρ` is the slash operator and
`Φ(F)(τ) = lim_{t → ∞} F(diag(τ, it))` is the Siegel `Φ` operator. As for
`SiegelUpperHalfSpace.siegelPhi`, the Siegel upper half-space `ℋ_g` is indexed by `l ⊕ Unit`, so
`g = |l| + 1`, and `Φ(f ∣_ρ γ) = 0` means that the limit exists and is `0`. The degree `2` case, on
`ℋ_2` indexed by `Fin 2`, is `SiegelUpperHalfSpace.IsCuspForm`.

## Main definitions

* `SiegelUpperHalfSpace.IsSiegelCuspForm` (LMFDB `mf.siegel.cusp_form`): cusp forms of every
  degree.
* `SiegelUpperHalfSpace.siegelCuspForms` (LMFDB `mf.siegel.cusp_form`): the space `S_ρ(Γ, ψ)` of
  Siegel cusp forms.

## Main results

* `SiegelUpperHalfSpace.IsSiegelCuspForm.siegelPhi_slash`: for a cusp form `f`, the Siegel `Φ`
  operator `SiegelUpperHalfSpace.siegelPhi` vanishes on every `f ∣_ρ γ`, `γ ∈ Sp(2g, ℚ)`.
-/

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] [DecidableEq l] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (l ⊕ Unit) ℂ) V) {f g : SiegelUpperHalfSpace (l ⊕ Unit) → V}
    (Γ : Subgroup (Matrix.symplecticGroup (l ⊕ Unit) ℚ)) (ψ : Γ →* ℂˣ)

variable (f) in
/-- A function `f : ℋ_g → V`, `g = |l| + 1`, is a **cusp form** (LMFDB `mf.siegel.cusp_form`) of
weight `ρ` if `Φ(f ∣_ρ γ) = 0` for every `γ ∈ Sp(2g, ℚ)`, where `∣_ρ` is the slash operator
`(f ∣_ρ γ)(τ) = ρ(cτ + d)⁻¹ f(γτ)` and `Φ` the Siegel `Φ` operator: `(f ∣_ρ γ)(diag(τ, it))`
tends to `0` as `t → ∞`, for every `τ ∈ ℋ_{g-1}`. The limit is taken coordinatewise, through every
linear form on `V`, as in `SiegelUpperHalfSpace.HasSiegelPhi`. -/
def IsSiegelCuspForm : Prop :=
  ∀ γ : Matrix.symplecticGroup (l ⊕ Unit) ℚ,
    HasSiegelPhi (slash ρ (SymplecticGroup.map (algebraMap ℚ ℝ) γ) f) 0

lemma isSiegelCuspForm_zero : IsSiegelCuspForm ρ (0 : SiegelUpperHalfSpace (l ⊕ Unit) → V) :=
  fun γ τ φ ↦ by simp [slash_zero]

lemma IsSiegelCuspForm.add (hf : IsSiegelCuspForm ρ f) (hg : IsSiegelCuspForm ρ g) :
    IsSiegelCuspForm ρ (f + g) := fun γ ↦ by
  simpa [slash_add] using (hf γ).add (hg γ)

lemma IsSiegelCuspForm.const_smul (hf : IsSiegelCuspForm ρ f) (c : ℂ) :
    IsSiegelCuspForm ρ (c • f) := fun γ ↦ by
  simpa [slash_smul] using (hf γ).const_smul c

/-- **The Siegel `Φ` operator vanishes on the slashes of a cusp form**: if `f` is a cusp form, then
`Φ(f ∣_ρ γ) = 0` for every `γ ∈ Sp(2g, ℚ)`, for the Siegel `Φ` operator
`SiegelUpperHalfSpace.siegelPhi`. -/
lemma IsSiegelCuspForm.siegelPhi_slash (hf : IsSiegelCuspForm ρ f)
    (γ : Matrix.symplecticGroup (l ⊕ Unit) ℚ) :
    siegelPhi (slash ρ (SymplecticGroup.map (algebraMap ℚ ℝ) γ) f) = 0 :=
  siegelPhi_eq (hf γ)

lemma IsSiegelCuspForm.siegelPhi_eq_zero (hf : IsSiegelCuspForm ρ f) : siegelPhi f = 0 := by
  simpa [slash_one] using hf.siegelPhi_slash ρ 1

/-- The space `S_ρ(Γ, ψ)` of **Siegel cusp forms** (LMFDB `mf.siegel.cusp_form`) of degree
`g = |l| + 1`, weight `ρ` and character `ψ` on a subgroup `Γ` of `Sp(2g, ℚ)`: the Siegel modular
forms `f ∈ M_ρ(Γ, ψ)` with `Φ(f ∣_ρ γ) = 0` for every `γ ∈ Sp(2g, ℚ)`. The LMFDB allows arithmetic
subgroups of `GSp(2g, ℚ)`; see `SiegelUpperHalfSpace.modularForms`. Its Siegel modular forms have
degree `g ≥ 2` (LMFDB `mf.siegel`), that is `l` nonempty: for `g = 1`, `M_ρ(Γ, ψ)` lacks the growth
condition at the cusps of `SiegelUpperHalfSpace.modularFormsDegreeOne`. -/
def siegelCuspForms : Submodule ℂ (SiegelUpperHalfSpace (l ⊕ Unit) → V) where
  carrier := {f | f ∈ modularForms ρ Γ ψ ∧ IsSiegelCuspForm ρ f}
  add_mem' hf hg := ⟨add_mem hf.1 hg.1, hf.2.add ρ hg.2⟩
  zero_mem' := ⟨zero_mem _, isSiegelCuspForm_zero ρ⟩
  smul_mem' c _ hf := ⟨Submodule.smul_mem _ c hf.1, hf.2.const_smul ρ c⟩

lemma siegelCuspForms_le_modularForms : siegelCuspForms ρ Γ ψ ≤ modularForms ρ Γ ψ :=
  fun _ hf ↦ hf.1

end SiegelUpperHalfSpace
