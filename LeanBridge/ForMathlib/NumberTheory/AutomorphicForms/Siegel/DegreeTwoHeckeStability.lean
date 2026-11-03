import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoOrthogonalDecomposition
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SiegelEisensteinHecke

/-!
# The Hecke stability of `E_{j,k}(Γ₂)` and `KE_{j,k}(Γ₂)`

For `k > 4`, the decomposition `N_{j,k}(Γ₂) = E_{j,k}(Γ₂) ⊕ KE_{j,k}(Γ₂)` of the knowl
`mf.siegel.subspace.degree.two` is stable under the Hecke operators. For `j = 0` and even `k`, the
Siegel Eisenstein series `ψ_k` is an eigenform, and the Klingen–Eisenstein series are the elements
of `N_{0,k}(Γ₂)` with vanishing constant Fourier coefficient, a condition which is preserved by the
Hecke operators. In the other weights, `E_{j,k}(Γ₂) = 0`, so that `KE_{j,k}(Γ₂) = N_{j,k}(Γ₂)`.

## Main results

* `SiegelUpperHalfSpace.heckeOperator_mem_siegelEisensteinSubspaceKJ` (LMFDB
  `mf.siegel.subspace.degree.two`): the Hecke operators preserve `E_{j,k}(Γ₂)` for `k > 4`.
* `SiegelUpperHalfSpace.heckeOperator_mem_klingenEisensteinSubspaceKJ` (LMFDB
  `mf.siegel.subspace.degree.two`): the Hecke operators preserve `KE_{j,k}(Γ₂)` for `k > 4`.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open Complex Filter Module SymplecticGroup Topology

open scoped MatrixGroups TensorProduct

namespace SiegelUpperHalfSpace

attribute [local instance] Fintype.ofFinite

variable {k : ℤ} {j : ℕ}
    (D : HeckeCoset (heckeMonoid (Fin 2)) (heckeGamma (Fin 2)) (heckeGamma (Fin 2)))
    {F : slashInvariants (rhoKJ k j)}

private lemma eq_zero_of_mem_siegelEisensteinSubspaceKJ_of_odd (hk : 4 < k) (hk' : Odd k)
    {H : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)}
    (hH : H ∈ siegelEisensteinSubspaceKJ k j) : H = 0 := by
  have h₁ : H ∈ cuspFormsKJ k j (integral (Fin 2)) := by
    rw [← modularFormsKJ_eq_cuspFormsKJ_of_odd hk']
    exact siegelEisensteinSubspaceKJ_le_modularFormsKJ k j hk hH
  exact Submodule.disjoint_def.mp (disjoint_sup_siegelEisensteinSubspaceKJ k j hk) H
    (Submodule.mem_sup_left h₁) hH

/-- **The Hecke operators preserve `E_{j,k}(Γ₂)`** (LMFDB `mf.siegel.subspace.degree.two`), for
`k > 4`: `ψ_k` is an eigenform, and `E_{j,k}(Γ₂) = 0` for `j > 0` or `k` odd. -/
lemma heckeOperator_mem_siegelEisensteinSubspaceKJ (hk : 4 < k)
    (hF : (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      siegelEisensteinSubspaceKJ k j) :
    (heckeOperator (rhoKJ k j) D F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      siegelEisensteinSubspaceKJ k j := by
  have hzero (hF₀ : (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) = 0) :
      (heckeOperator (rhoKJ k j) D F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
        siegelEisensteinSubspaceKJ k j := by
    have e : F = 0 := Subtype.ext hF₀
    rw [e, map_zero]
    exact zero_mem _
  rcases eq_or_ne j 0 with rfl | hj
  · rcases Int.even_or_odd k with hk' | hk'
    · have hk₅ : 5 < k := by
        rcases hk' with ⟨m, rfl⟩
        omega
      rw [siegelEisensteinSubspaceKJ_eq_span_singleton hk₅ hk'] at hF ⊢
      rcases Submodule.mem_span_singleton.mp hF with ⟨c, hc⟩
      have hψ : siegelEisensteinKJ k ∈ slashInvariants (rhoKJ k 0) :=
        ((mem_modularForms_iff_slashInvariants _ _).mp
          (siegelEisensteinKJ_mem_modularFormsKJ hk₅ hk')).2
      rcases exists_heckeOperator_siegelEisensteinKJ hk₅ hk' D with ⟨C, hC⟩
      have e : F = c • ⟨_, hψ⟩ := Subtype.ext hc.symm
      rw [e, map_smul, Submodule.coe_smul, hC _ rfl]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    · exact hzero (eq_zero_of_mem_siegelEisensteinSubspaceKJ_of_odd hk hk' hF)
  · rw [siegelEisensteinSubspaceKJ_eq_bot k hj, Submodule.mem_bot] at hF
    exact hzero hF

private lemma tendsto_dual_heckeOperator_scalarPoint
    (hF : (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      modularFormsKJ k j (integral (Fin 2)))
    {a : dualLattice (integral (Fin 2)) → Sym[ℂ]^j (Fin 2 → ℂ)}
    (ha : HasSiegelFourierExpansion (integral (Fin 2))
      (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) a) (h₀ : a 0 = 0)
    (ψ : Dual ℂ (Sym[ℂ]^j (Fin 2 → ℂ))) :
    Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ ψ ((heckeOperator (rhoKJ k j) D F :
      SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) (scalarPoint t))) atTop (𝓝 0) := by
  have h : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦
      ∑ v, ψ (heckeMonoidSlash (rhoKJ k j) (heckeRep D v) F (scalarPoint t))) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ fun v _ ↦
      tendsto_dual_heckeMonoidSlash_scalarPoint hF ha h₀ (heckeRep D v) ψ
  refine h.congr fun t ↦ ?_
  rw [coe_heckeOperator, Finset.sum_apply, map_sum]

/-- **The Hecke operators preserve `KE_{j,k}(Γ₂)`** (LMFDB `mf.siegel.subspace.degree.two`), for
`k > 4`: they preserve `N_{j,k}(Γ₂) = E_{j,k}(Γ₂) ⊕ KE_{j,k}(Γ₂)`, and, for `j = 0` and `k` even,
the elements of `KE_{0,k}(Γ₂)` are those of `N_{0,k}(Γ₂)` with vanishing constant Fourier
coefficient. -/
lemma heckeOperator_mem_klingenEisensteinSubspaceKJ (hk : 4 < k)
    (hF : (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      klingenEisensteinSubspaceKJ k j) :
    (heckeOperator (rhoKJ k j) D F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      klingenEisensteinSubspaceKJ k j := by
  have hadm : IsAdmissibleForm (rhoKJ k j) (symHermitianForm j) :=
    isAdmissibleForm_symHermitianForm k
  have hN : (heckeOperator (rhoKJ k j) D F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      cuspFormsOrthogonalKJ (integral (Fin 2)) k j (symHermitianForm j) :=
    heckeOperator_mem_cuspFormsOrthogonalKJ hadm D
      (klingenEisensteinSubspaceKJ_le_cuspFormsOrthogonalKJ hadm hk hF)
  rw [cuspFormsOrthogonalKJ_eq_sup hadm (fun v hv ↦ symHermitianForm_pos hv) hk] at hN
  rcases Submodule.mem_sup.mp hN with ⟨e, he, κ, hκ, hsum⟩
  suffices h : e = 0 by
    rw [← hsum, h, zero_add]
    exact hκ
  rcases eq_or_ne j 0 with rfl | hj
  · rcases Int.even_or_odd k with hk' | hk'
    · have hk₅ : 5 < k := by
        rcases hk' with ⟨m, rfl⟩
        omega
      rw [siegelEisensteinSubspaceKJ_eq_span_singleton hk₅ hk'] at he
      rcases Submodule.mem_span_singleton.mp he with ⟨c, rfl⟩
      have hF₁ : (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^0 (Fin 2 → ℂ)) ∈
          modularFormsKJ k 0 (integral (Fin 2)) :=
        klingenEisensteinSubspaceKJ_le_modularFormsKJ k 0 hF
      rcases exists_hasSiegelFourierExpansion (rhoKJ k 0) (isArithmetic_integral (Fin 2)) hF₁ with
        ⟨a, ha⟩
      have ha₀ : a 0 = 0 := by
        have h₁ : symConstCoeff 0 (a 0) = 0 := by
          rw [klingenEisensteinSubspaceKJ_eq_range hk Even.zero] at hF
          rcases hF with ⟨f, hf⟩
          rw [← hf] at ha
          exact symConstCoeff_apply_zero_vectorKlingenEisenstein hk hk' f ha
        rw [eq_smul_tprod_of_symPowerRep_eq (symPowerRep_zero _ (a 0)), h₁, zero_smul]
      have hψ : siegelEisensteinKJ k ∈ modularFormsKJ k 0 (integral (Fin 2)) :=
        siegelEisensteinKJ_mem_modularFormsKJ hk₅ hk'
      rcases exists_hasSiegelFourierExpansion (rhoKJ k 0) (isArithmetic_integral (Fin 2)) hψ with
        ⟨bψ, hbψ⟩
      have hκ₁ : κ ∈ modularFormsKJ k 0 (integral (Fin 2)) :=
        klingenEisensteinSubspaceKJ_le_modularFormsKJ k 0 hκ
      rcases exists_hasSiegelFourierExpansion (rhoKJ k 0) (isArithmetic_integral (Fin 2)) hκ₁ with
        ⟨bκ, hbκ⟩
      have h₂ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦
          symConstCoeff 0 (siegelEisensteinKJ k (scalarPoint t))) atTop
            (𝓝 (symConstCoeff 0 (bψ 0))) :=
        tendsto_dual_scalarPoint (symConstCoeff 0) hbψ (posSemidef_of_apply_ne_zero hψ hbψ)
      have h₃ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ symConstCoeff 0 (κ (scalarPoint t))) atTop
          (𝓝 (symConstCoeff 0 (bκ 0))) :=
        tendsto_dual_scalarPoint (symConstCoeff 0) hbκ (posSemidef_of_apply_ne_zero hκ₁ hbκ)
      have hκ₀ : symConstCoeff 0 (bκ 0) = 0 := by
        rw [klingenEisensteinSubspaceKJ_eq_range hk Even.zero] at hκ
        rcases hκ with ⟨f, rfl⟩
        exact symConstCoeff_apply_zero_vectorKlingenEisenstein hk hk' f hbκ
      rw [symConstCoeff_apply_zero_siegelEisensteinKJ hk₅ hk' hbψ] at h₂
      rw [hκ₀] at h₃
      have h₅ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦
          c * symConstCoeff 0 (siegelEisensteinKJ k (scalarPoint t)) +
            symConstCoeff 0 (κ (scalarPoint t))) atTop (𝓝 0) := by
        refine (tendsto_dual_heckeOperator_scalarPoint D hF₁ ha ha₀ (symConstCoeff 0)).congr
          fun t ↦ ?_
        rw [← hsum]
        simp
      have h₆ : c = 0 := by
        simpa using tendsto_nhds_unique ((h₂.const_mul c).add h₃) h₅
      rw [h₆, zero_smul]
    · exact eq_zero_of_mem_siegelEisensteinSubspaceKJ_of_odd hk hk' he
  · rw [siegelEisensteinSubspaceKJ_eq_bot k hj, Submodule.mem_bot] at he
    exact he

end SiegelUpperHalfSpace
