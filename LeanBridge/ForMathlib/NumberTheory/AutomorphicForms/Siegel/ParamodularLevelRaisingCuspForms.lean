import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularLevelRaisingEta
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularNewform

/-!
# The level raising operators `θ` and `η` preserve cusp forms

The level raising operators `θ = [K(M) K(Mp)]` and `η = [K(M) diag(1, p, 1, p⁻¹) K(Mp²)]` of
Roberts and Schmidt are sums of slash operators of elements of `Sp(4, ℚ)`: the representatives of
the right cosets of `K(M) K(Mp)` are products of elements of the paramodular groups, and
`η = diag(1, p, 1, p⁻¹)` has multiplier `1` (`SiegelUpperHalfSpace.coe_levelRaisingEta`). The cusp
condition `Φ(F ∣_ρ γ) = 0` for all `γ ∈ Sp(4, ℚ)` is preserved by such slash operators, so `θ` and
`η` map the cusp forms `S_ρ(K(M))` to `S_ρ(K(Mp))` and `S_ρ(K(Mp²))`, as soon as the slash
operator preserves holomorphy, as it does for the holomorphic representations `ρ` of the LMFDB
(taken as a hypothesis, as for the Hecke operators in
`SiegelUpperHalfSpace.heckeOperator_mem_modularForms`). The operator `θ'` involves similitudes of
multiplier `p`, and is not treated here.

## Main definitions

* `SiegelUpperHalfSpace.etaSp`: `η = diag(1, p, 1, p⁻¹)` as an element of `Sp(4, ℚ)`.

## Main results

* `SiegelUpperHalfSpace.levelRaisingTheta_mem_paramodularCuspForms`: `θ` maps `S_ρ(K(M))` to
  `S_ρ(K(Mp))` when the slash operator preserves holomorphy.
* `SiegelUpperHalfSpace.levelRaisingEta_mem_paramodularCuspForms`: `η` maps `S_ρ(K(M))` to
  `S_ρ(K(Mp²))` when the slash operator preserves holomorphy.
-/

open Matrix

namespace SiegelUpperHalfSpace

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) ℂ) V)
    (M p : ℕ+) {F : slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel M))}
    {f g : SiegelUpperHalfSpace (Fin 2) → V}

private lemma IsCuspForm.add (hf : IsCuspForm ρ f) (hg : IsCuspForm ρ g) : IsCuspForm ρ (f + g) :=
  fun γ ↦ by
    rw [slash_add]
    exact (hf γ).add (hg γ)

private lemma isCuspForm_zero : IsCuspForm ρ (0 : SiegelUpperHalfSpace (Fin 2) → V) := fun γ ↦ by
  rw [slash_zero]
  exact siegelOperatorVanishes_zero

lemma IsCuspForm.slash (hf : IsCuspForm ρ f) (γ : symplecticGroup (Fin 2) ℚ) :
    IsCuspForm ρ (slash ρ (SymplecticGroup.map (algebraMap ℚ ℝ) γ) f) := fun δ ↦ by
  rw [← slash_mul, ← map_mul]
  exact hf (γ * δ)

variable (f) in
lemma heckeMonoidSlash_eq_slash {Δ : Submonoid (GL (Fin 2 ⊕ Fin 2) ℚ)}
    [Fact (Δ ≤ gspPlusGL (Fin 2))] {x : Δ} {γ : symplecticGroup (Fin 2) ℚ}
    (h : (x : GL (Fin 2 ⊕ Fin 2) ℚ) = spRatToGL (Fin 2) γ) :
    heckeMonoidSlash ρ x f = slash ρ (SymplecticGroup.map (algebraMap ℚ ℝ) γ) f := by
  rw [← gspSlash_ofSp]
  exact congrArg (gspSlash ρ · f) (Subtype.ext (congrArg Units.val h))

/-- **The level raising operator `θ` maps `S_ρ(K(M))` to `S_ρ(K(Mp))`** when the slash operator of
`GSp(4, ℚ)⁺` preserves holomorphy, as it does for the holomorphic representations `ρ` of the
LMFDB: `θF = ∑ᵢ F ∣_ρ γᵢ` is `K(Mp)`-invariant, holomorphic, and a cusp form, the representatives
`γᵢ` of the right cosets of `K(M) K(Mp)` lying in `Sp(4, ℚ)`. -/
lemma levelRaisingTheta_mem_paramodularCuspForms
    (hρ : ∀ α f, IsHolomorphic f → IsHolomorphic (gspSlash ρ α f))
    (hF : (F : SiegelUpperHalfSpace (Fin 2) → V) ∈ paramodularCuspForms ρ M) :
    (levelRaisingTheta ρ M p F : SiegelUpperHalfSpace (Fin 2) → V) ∈
      paramodularCuspForms ρ (M * p) := by
  refine ⟨(mem_modularForms_iff_slashInvariantsOf ρ _ _).mpr
    ⟨?_, fun γ hγ ↦ (levelRaisingTheta ρ M p F).2 γ hγ⟩, ?_⟩ <;>
  rw [levelRaisingTheta, coe_doubleCosetOperator]
  · exact Finset.sum_induction _ IsHolomorphic (fun _ _ ↦ IsHolomorphic.add) isHolomorphic_zero
      fun _ _ ↦ hρ _ _ hF.1.1
  · refine Finset.sum_induction _ (IsCuspForm ρ) (fun _ _ ↦ IsCuspForm.add ρ) (isCuspForm_zero ρ)
      fun v _ ↦ ?_
    have hle (Γ : Subgroup (symplecticGroup (Fin 2) ℚ)) :
        heckeGammaOf Γ ≤ (⊤ : Subgroup (symplecticGroup (Fin 2) ℚ)).map (spRatToGL (Fin 2)) :=
      Subgroup.map_mono le_top
    have hD : (((HeckeCoset.mk (heckeGammaOf (paramodularLevel M))
        (heckeGammaOf (paramodularLevel (M * p))) (1 : gspPlusGL (Fin 2))).rep :
          gspPlusGL (Fin 2)) : GL (Fin 2 ⊕ Fin 2) ℚ) ∈
        (⊤ : Subgroup (symplecticGroup (Fin 2) ℚ)).map (spRatToGL (Fin 2)) := by
      rcases DoubleCoset.mem_doubleCoset.mp (HeckeCoset.rep_mk_mem_doubleCoset
        (H₁ := heckeGammaOf (paramodularLevel M)) (H₂ := heckeGammaOf (paramodularLevel (M * p)))
        (1 : gspPlusGL (Fin 2))) with ⟨h₁, hh₁, h₂, hh₂, h⟩
      rw [h]
      exact mul_mem (mul_mem (hle _ hh₁) (one_mem _)) (hle _ hh₂)
    rcases DoubleCoset.rightCosetRep_mem _ hD (fun _ hx ↦ hle _ hx) v with ⟨γ, -, hγ⟩
    rw [heckeMonoidSlash_eq_slash ρ _ hγ.symm]
    exact hF.2.slash ρ γ

/-- The matrix `η = diag(1, p, 1, p⁻¹)` of the level raising operator `η`, as an element of
`Sp(4, ℚ)`: its multiplier is `1`. -/
def etaSp : symplecticGroup (Fin 2) ℚ :=
  ⟨(etaDiag p : GL (Fin 2 ⊕ Fin 2) ℚ), by
    rw [SymplecticGroup.mem_iff']
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [etaDiag, diagSimilitude, J]⟩

/-- **The level raising operator `η` maps `S_ρ(K(M))` to `S_ρ(K(Mp²))`** when the slash operator
of `GSp(4, ℚ)⁺` preserves holomorphy, as it does for the holomorphic representations `ρ` of the
LMFDB: `ηF = F ∣_ρ η` (`SiegelUpperHalfSpace.coe_levelRaisingEta`) is `K(Mp²)`-invariant,
holomorphic, and a cusp form since `η ∈ Sp(4, ℚ)`. -/
lemma levelRaisingEta_mem_paramodularCuspForms
    (hρ : ∀ α f, IsHolomorphic f → IsHolomorphic (gspSlash ρ α f))
    (hF : (F : SiegelUpperHalfSpace (Fin 2) → V) ∈ paramodularCuspForms ρ M) :
    (levelRaisingEta ρ M p F : SiegelUpperHalfSpace (Fin 2) → V) ∈
      paramodularCuspForms ρ (M * p * p) := by
  refine ⟨(mem_modularForms_iff_slashInvariantsOf ρ _ _).mpr
    ⟨?_, fun γ hγ ↦ (levelRaisingEta ρ M p F).2 γ hγ⟩, ?_⟩ <;>
  rw [coe_levelRaisingEta]
  · exact hρ _ _ hF.1.1
  · have h : ((etaDiag p : gspPlusGL (Fin 2)) : GL (Fin 2 ⊕ Fin 2) ℚ) =
        spRatToGL (Fin 2) (etaSp p) :=
      Units.ext rfl
    rw [heckeMonoidSlash_eq_slash ρ _ h]
    exact hF.2.slash ρ (etaSp p)

end SiegelUpperHalfSpace
