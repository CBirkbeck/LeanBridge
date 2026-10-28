import Mathlib.Analysis.Complex.Circle
import Mathlib.NumberTheory.ModularForms.Basic

/-!
# Modular forms with a multiplier system

A modular form of weight `k ∈ ℤ` and multiplier system `v : Γ → S¹` on a subgroup `Γ` of
`SL(2, ℝ)` (inside `GL(2, ℝ)`) is a holomorphic function `f : ℍ → ℂ` satisfying the functional
equation `f ∣[k] γ = v(γ) f` for `γ ∈ Γ` and the growth condition of being bounded at every cusp of
`Γ`. These form a complex vector space. For `v = 1` they are Mathlib's modular forms.

## Main definitions

* `ModularForm.multiplierSpace` (LMFDB `mf`): the space of modular forms of weight `k` and
  multiplier `v` on `Γ`.

## Main results

* `ModularForm.mem_multiplierSpace_one_iff`: for the trivial multiplier, these are Mathlib's
  modular forms.
-/

open UpperHalfPlane OnePoint Subgroup

open scoped ModularForm Manifold

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ} {f : ℍ → ℂ}

variable (k) in
/-- The space of **modular forms** (LMFDB `mf`) of weight `k ∈ ℤ` and multiplier system `v` on a
subgroup `Γ` of `SL(2, ℝ)`: the holomorphic functions `f : ℍ → ℂ` with `f ∣[k] γ = v(γ) f` for every
`γ ∈ Γ` (the functional equation, LMFDB `mf.transformation_property`) that are bounded at every cusp
of `Γ` (the growth condition, LMFDB `mf.growth_condition`), as a complex vector space. The LMFDB's
`mf` is an umbrella term also covering Maass, Hilbert, Bianchi and Siegel modular forms; this is its
elliptic, holomorphic, integral-weight instance, which Mathlib's `ModularForm Γ k` is for `v = 1`
(`mem_multiplierSpace_one_iff`). The multiplier only gives nonzero forms if it is a multiplier
system of weight `k` (`MonoidHom.isMultiplierSystem_of_slash_eq_smul`). -/
def multiplierSpace (v : Γ →* Circle) : Submodule ℂ (ℍ → ℂ) where
  carrier := {f | MDiff f ∧ (∀ γ : Γ, f ∣[k] (γ : GL (Fin 2) ℝ) = (v γ : ℂ) • f) ∧
    ∀ {c : OnePoint ℝ}, IsCusp c Γ → c.IsBoundedAt f k}
  add_mem' hf hg := ⟨hf.1.add hg.1, fun γ ↦ by rw [SlashAction.add_slash, hf.2.1, hg.2.1, smul_add],
    fun hc ↦ (hf.2.2 hc).add (hg.2.2 hc)⟩
  zero_mem' := ⟨mdifferentiable_const, fun γ ↦ by simp, fun _ g _ ↦ by
    simpa using zero_form_isBoundedAtImInfty⟩
  smul_mem' a f hf := by
    refine ⟨hf.1.const_smul a, fun γ ↦ ?_, fun hc g hg ↦ ?_⟩
    · rw [smul_slash, hf.2.1, smul_comm]
      simp [σ, HasDetOne.det_eq γ.2]
    · simp_rw [IsBoundedAtImInfty, Filter.BoundedAtFilter, smul_slash]
      exact (hf.2.2 hc g hg).const_smul_left (σ g a)

/-- **For the trivial multiplier these are Mathlib's modular forms**: a function lies in the space
of modular forms of weight `k` and multiplier `1` on `Γ` exactly when it is a modular form of weight
`k` on `Γ`. -/
lemma mem_multiplierSpace_one_iff : f ∈ multiplierSpace k (1 : Γ →* Circle) ↔
    ∃ g : ModularForm Γ k, ⇑g = f := by
  refine ⟨fun hf ↦ ⟨⟨⟨f, fun γ hγ ↦ by simpa using hf.2.1 ⟨γ, hγ⟩⟩, hf.1, hf.2.2⟩, rfl⟩, ?_⟩
  rintro ⟨g, rfl⟩
  exact ⟨g.holo', fun γ ↦ by simpa using g.slash_action_eq' γ γ.2, g.bdd_at_cusps'⟩

end ModularForm
