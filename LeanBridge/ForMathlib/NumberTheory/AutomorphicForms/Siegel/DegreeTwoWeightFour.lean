import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoHeckeStability

/-!
# The decomposition `N_{j,k}(Γ₂) = E_{j,k}(Γ₂) ⊕ KE_{j,k}(Γ₂)` at `(j, k) = (0, 4)`

The decomposition of the knowl `mf.siegel.subspace.degree.two` holds for `k > 4`
(`SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_eq_sup`) and at `(j, k) = (0, 4)`, where
`N_{0,4}(Γ₂) = E_{0,4}(Γ₂) = ℂ ψ₄` and `KE_{0,4}(Γ₂) = 0`, as `S₄(SL(2, ℤ)) = 0`. For
`F ∈ M_{0,4}(Γ₂)`, the Siegel operator of `F - c ψ₄` vanishes, for `c` the constant Fourier
coefficient of `F`: it is a cusp form on `SL(2, ℤ)` of weight `4`. So `F - c ψ₄` is a cusp form, and
`M_{0,4}(Γ₂) = S_{0,4}(Γ₂) + ℂ ψ₄`. Since `ψ₄` is orthogonal to the cusp forms, this gives
`N_{0,4}(Γ₂) = ℂ ψ₄`.

At `(8, 4)` the decomposition fails, since `E_{8,4}(Γ₂) = 0` and the Klingen–Eisenstein series do
not converge, while `N_{8,4}(Γ₂) ≠ 0` by the table of the LMFDB (Ibukiyama and Wakatsuki). At
`(0, 0)` it fails as well, as the constants lie in `N_{0,0}(Γ₂)`. So the correct range of the
knowl's claim is `k > 4` together with `(j, k) = (0, 4)`, which is what is stated here.

## Main results

* `SiegelUpperHalfSpace.siegelEisensteinKJ_ne_zero`: `ψ_k ≠ 0` for even `k > 3`.
* `SiegelUpperHalfSpace.klingenEisensteinSubspaceKJ_four_eq_bot`: `KE_{0,4}(Γ₂) = 0`.
* `SiegelUpperHalfSpace.modularFormsKJ_four_eq_sup`: `M_{0,4}(Γ₂) = S_{0,4}(Γ₂) + E_{0,4}(Γ₂)`.
* `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_four_eq_span_singleton`: `N_{0,4}(Γ₂) = ℂ ψ₄`.
* `SiegelUpperHalfSpace.disjoint_cuspFormsKJ_siegelEisensteinSubspaceKJ_four`: the sum
  `S_{0,4}(Γ₂) + E_{0,4}(Γ₂)` is direct.
* `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_eq_sup_of_range`,
  `SiegelUpperHalfSpace.disjoint_siegelEisensteinSubspaceKJ_klingenEisensteinSubspaceKJ_of_range`,
  `SiegelUpperHalfSpace.heckeOperator_mem_siegelEisensteinSubspaceKJ_of_range`,
  `SiegelUpperHalfSpace.heckeOperator_mem_klingenEisensteinSubspaceKJ_of_range` (LMFDB
  `mf.siegel.subspace.degree.two`): `N_{j,k}(Γ₂) = E_{j,k}(Γ₂) ⊕ KE_{j,k}(Γ₂)`, stable under the
  Hecke operators, for `k > 4` and for `(j, k) = (0, 4)`.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open Complex Filter Module SymplecticGroup Topology

open scoped ComplexOrder MatrixGroups TensorProduct

namespace SiegelUpperHalfSpace

variable {k : ℤ} {j : ℕ}

/-- **The Siegel Eisenstein series `ψ_k` is nonzero** for even `k > 3`: its constant term is `1`. -/
lemma siegelEisensteinKJ_ne_zero (hk : 3 < k) (hk' : Even k) : siegelEisensteinKJ k ≠ 0 := by
  intro h
  have h₁ :
      Tendsto (fun s : Set.Ioi (0 : ℝ) ↦ siegelEisensteinSeries k (scalarPoint s)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr fun s ↦ ?_
    rw [← symConstCoeff_siegelEisensteinKJ, h]
    simp
  exact zero_ne_one (tendsto_nhds_unique h₁ (tendsto_siegelEisensteinSeries_scalarPoint hk hk'))

private lemma subsingleton_cuspForm_four : Subsingleton (CuspForm 𝒮ℒ ((4 : ℤ) + (0 : ℕ))) :=
  rank_zero_iff.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))

/-- **The space `KE_{0,4}(Γ₂)` vanishes**, as there are no nonzero cusp forms of weight `4` on
`SL(2, ℤ)`. -/
lemma klingenEisensteinSubspaceKJ_four_eq_bot : klingenEisensteinSubspaceKJ 4 0 = ⊥ := by
  have h : Submodule.span ℂ (Set.range fun f : CuspForm 𝒮ℒ ((4 : ℤ) + (0 : ℕ)) ↦
      vectorKlingenEisenstein 4 0 f) = ⊥ := by
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨f, rfl⟩
    have : Subsingleton (CuspForm 𝒮ℒ ((4 : ℤ) + (0 : ℕ))) := subsingleton_cuspForm_four
    rw [Subsingleton.elim f 0]
    funext Z
    simp [vectorKlingenEisenstein, vectorKlingenTerm, dualTsum]
  rw [klingenEisensteinSubspaceKJ, h, bot_inf_eq]

variable {F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^0 (Fin 2 → ℂ)}

private lemma siegelEisensteinKJ_four_mem :
    siegelEisensteinKJ 4 ∈ modularFormsKJ 4 0 (integral (Fin 2)) :=
  siegelEisensteinKJ_mem_modularFormsKJ (by norm_num) (by decide)

private lemma exists_sub_smul_mem_cuspFormsKJ_four
    (hF : F ∈ modularFormsKJ 4 0 (integral (Fin 2))) :
    ∃ c : ℂ, F - c • siegelEisensteinKJ 4 ∈ cuspFormsKJ 4 0 (integral (Fin 2)) := by
  rcases exists_hasSiegelFourierExpansion (rhoKJ 4 0) (isArithmetic_integral (Fin 2)) hF with
    ⟨b, hb⟩
  rcases exists_hasSiegelFourierExpansion (rhoKJ 4 0) (isArithmetic_integral (Fin 2))
    siegelEisensteinKJ_four_mem with ⟨c, hc⟩
  generalize hc₀ : symConstCoeff 0 (b 0) = c₀
  have hG : F - c₀ • siegelEisensteinKJ 4 ∈ modularFormsKJ 4 0 (integral (Fin 2)) :=
    sub_mem hF (Submodule.smul_mem _ _ siegelEisensteinKJ_four_mem)
  have hbG : HasSiegelFourierExpansion (integral (Fin 2)) (F - c₀ • siegelEisensteinKJ 4)
      (b - c₀ • c) := by
    intro τ φ
    have e : φ ((F - c₀ • siegelEisensteinKJ 4) τ) = φ (F τ) - c₀ * φ (siegelEisensteinKJ 4 τ) := by
      simp
    rw [e]
    refine ((hb τ φ).sub ((hc τ φ).mul_left c₀)).congr_fun fun n ↦ ?_
    simp
    ring1
  have h₀ : symConstCoeff 0 ((b - c₀ • c) 0) = 0 := by
    simp [symConstCoeff_apply_zero_siegelEisensteinKJ (by norm_num) (by decide) hc, hc₀]
  refine ⟨c₀, hG, isCuspForm_of_siegelOperatorVanishes hG fun τ' φ ↦ ?_⟩
  have : Subsingleton (CuspForm 𝒮ℒ ((4 : ℤ) + (0 : ℕ))) := subsingleton_cuspForm_four
  have hu : siegelOperatorSeries (b - c₀ • c) τ' = 0 :=
    DFunLike.congr_fun (Subsingleton.elim (siegelOperatorCuspKJ hG hbG h₀) 0) τ'
  simpa [hu] using tendsto_dual_diagPoint_siegelOperatorSeries τ' hG hbG φ

/-- **`M_{0,4}(Γ₂) = S_{0,4}(Γ₂) + E_{0,4}(Γ₂)`**: for `F ∈ M_{0,4}(Γ₂)`, the Siegel operator of
`F - c ψ₄` is a cusp form of weight `4` on `SL(2, ℤ)`, hence `0`, for `c` the constant Fourier
coefficient of `F`. The sum is direct
(`SiegelUpperHalfSpace.disjoint_cuspFormsKJ_siegelEisensteinSubspaceKJ_four`). -/
lemma modularFormsKJ_four_eq_sup : modularFormsKJ 4 0 (integral (Fin 2)) =
    cuspFormsKJ 4 0 (integral (Fin 2)) ⊔ siegelEisensteinSubspaceKJ 4 0 := by
  rw [siegelEisensteinSubspaceKJ_eq_span_singleton (by norm_num) (by decide)]
  refine le_antisymm (fun F hF ↦ ?_) (sup_le (cuspForms_le_modularForms _ _ _)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr siegelEisensteinKJ_four_mem))
  rcases exists_sub_smul_mem_cuspFormsKJ_four hF with ⟨c, hc⟩
  refine Submodule.mem_sup.mpr ⟨_, hc, _, Submodule.smul_mem _ c
    (Submodule.mem_span_singleton_self _), sub_add_cancel _ _⟩

variable {c : Sym[ℂ]^0 (Fin 2 → ℂ) →ₗ[ℂ] Sym[ℂ]^0 (Fin 2 → ℂ) →ₗ⋆[ℂ] ℂ}

/-- **`N_{0,4}(Γ₂)` is the line of `ψ₄`**, for an admissible positive definite form `c`. -/
lemma cuspFormsOrthogonalKJ_four_eq_span_singleton (hadm : IsAdmissibleForm (rhoKJ 4 0) c)
    (hpos : ∀ v, v ≠ 0 → 0 < c v v) :
    cuspFormsOrthogonalKJ (integral (Fin 2)) 4 0 c = Submodule.span ℂ {siegelEisensteinKJ 4} := by
  have hψ : siegelEisensteinKJ 4 ∈ cuspFormsOrthogonalKJ (integral (Fin 2)) 4 0 c :=
    ⟨siegelEisensteinKJ_four_mem, fun G hG ↦
      isPeterssonOrthogonal_siegelEisensteinKJ hadm (by norm_num) (by decide) hG⟩
  refine le_antisymm (fun F hF ↦ ?_) ((Submodule.span_singleton_le_iff_mem _ _).mpr hψ)
  rcases exists_sub_smul_mem_cuspFormsKJ_four hF.1 with ⟨a, ha⟩
  have h₀ : F - a • siegelEisensteinKJ 4 = 0 :=
    Submodule.disjoint_def.mp (disjoint_cuspFormsKJ_cuspFormsOrthogonalKJ hadm hpos) _ ha
      (sub_mem hF (Submodule.smul_mem _ a hψ))
  rw [sub_eq_zero.mp h₀]
  exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)

/-- **The sum `S_{0,4}(Γ₂) + E_{0,4}(Γ₂)` is direct**, as `E_{0,4}(Γ₂)` is orthogonal to the cusp
forms. -/
lemma disjoint_cuspFormsKJ_siegelEisensteinSubspaceKJ_four :
    Disjoint (cuspFormsKJ 4 0 (integral (Fin 2))) (siegelEisensteinSubspaceKJ 4 0) := by
  have hadm : IsAdmissibleForm (rhoKJ 4 0) (symHermitianForm 0) :=
    isAdmissibleForm_symHermitianForm 4
  have hpos : ∀ v, v ≠ 0 → 0 < symHermitianForm 0 v v := fun v hv ↦ symHermitianForm_pos hv
  rw [siegelEisensteinSubspaceKJ_eq_span_singleton (by norm_num) (by decide),
    ← cuspFormsOrthogonalKJ_four_eq_span_singleton hadm hpos]
  exact disjoint_cuspFormsKJ_cuspFormsOrthogonalKJ hadm hpos

/-! ### The range of the decomposition -/

variable {c' : Sym[ℂ]^j (Fin 2 → ℂ) →ₗ[ℂ] Sym[ℂ]^j (Fin 2 → ℂ) →ₗ⋆[ℂ] ℂ}

/-- **`N_{j,k}(Γ₂) = E_{j,k}(Γ₂) ⊕ KE_{j,k}(Γ₂)`** (LMFDB `mf.siegel.subspace.degree.two`), for
`k > 4` and for `(j, k) = (0, 4)`, and an admissible positive definite form `c'`. The sum is direct:
`SiegelUpperHalfSpace.disjoint_siegelEisensteinSubspaceKJ_klingenEisensteinSubspaceKJ_of_range`. -/
lemma cuspFormsOrthogonalKJ_eq_sup_of_range (hadm : IsAdmissibleForm (rhoKJ k j) c')
    (hpos : ∀ v, v ≠ 0 → 0 < c' v v) (hkj : 4 < k ∨ k = 4 ∧ j = 0) :
    cuspFormsOrthogonalKJ (integral (Fin 2)) k j c' =
      siegelEisensteinSubspaceKJ k j ⊔ klingenEisensteinSubspaceKJ k j := by
  rcases hkj with hk | ⟨rfl, rfl⟩
  · exact cuspFormsOrthogonalKJ_eq_sup hadm hpos hk
  · rw [cuspFormsOrthogonalKJ_four_eq_span_singleton hadm hpos,
      klingenEisensteinSubspaceKJ_four_eq_bot, sup_bot_eq,
      siegelEisensteinSubspaceKJ_eq_span_singleton (by norm_num) (by decide)]

/-- **The sum `E_{j,k}(Γ₂) + KE_{j,k}(Γ₂)` is direct**, for `k > 4` and for `(j, k) = (0, 4)`. -/
lemma disjoint_siegelEisensteinSubspaceKJ_klingenEisensteinSubspaceKJ_of_range
    (hkj : 4 < k ∨ k = 4 ∧ j = 0) :
    Disjoint (siegelEisensteinSubspaceKJ k j) (klingenEisensteinSubspaceKJ k j) := by
  rcases hkj with hk | ⟨rfl, rfl⟩
  · exact disjoint_siegelEisensteinSubspaceKJ_klingenEisensteinSubspaceKJ hk
  · rw [klingenEisensteinSubspaceKJ_four_eq_bot]
    exact disjoint_bot_right

variable (D : HeckeCoset (heckeMonoid (Fin 2)) (heckeGamma (Fin 2)) (heckeGamma (Fin 2)))

private lemma heckeOperator_mem_siegelEisensteinSubspaceKJ_zero (hk : 3 < k) (hk' : Even k)
    {G : slashInvariants (rhoKJ k 0)}
    (hG : (G : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^0 (Fin 2 → ℂ)) ∈
      siegelEisensteinSubspaceKJ k 0) :
    (heckeOperator (rhoKJ k 0) D G : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^0 (Fin 2 → ℂ)) ∈
      siegelEisensteinSubspaceKJ k 0 := by
  rw [siegelEisensteinSubspaceKJ_eq_span_singleton hk hk'] at hG ⊢
  rcases Submodule.mem_span_singleton.mp hG with ⟨a, ha⟩
  have hψ : siegelEisensteinKJ k ∈ slashInvariants (rhoKJ k 0) :=
    ((mem_modularForms_iff_slashInvariants _ _).mp
      (siegelEisensteinKJ_mem_modularFormsKJ hk hk')).2
  rcases exists_heckeOperator_siegelEisensteinKJ hk hk' D with ⟨C, hC⟩
  have e : G = a • ⟨_, hψ⟩ := Subtype.ext ha.symm
  rw [e, map_smul, Submodule.coe_smul, hC _ rfl]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

variable {G : slashInvariants (rhoKJ k j)}

/-- **The Hecke operators preserve `E_{j,k}(Γ₂)`** (LMFDB `mf.siegel.subspace.degree.two`), for
`k > 4` and for `(j, k) = (0, 4)`, where `ψ₄` is an eigenform. -/
lemma heckeOperator_mem_siegelEisensteinSubspaceKJ_of_range (hkj : 4 < k ∨ k = 4 ∧ j = 0)
    (hG : (G : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      siegelEisensteinSubspaceKJ k j) :
    (heckeOperator (rhoKJ k j) D G : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      siegelEisensteinSubspaceKJ k j := by
  rcases hkj with hk | ⟨rfl, rfl⟩
  · exact heckeOperator_mem_siegelEisensteinSubspaceKJ D hk hG
  · exact heckeOperator_mem_siegelEisensteinSubspaceKJ_zero D (by norm_num) (by decide) hG

/-- **The Hecke operators preserve `KE_{j,k}(Γ₂)`** (LMFDB `mf.siegel.subspace.degree.two`), for
`k > 4` and for `(j, k) = (0, 4)`, where this space vanishes. -/
lemma heckeOperator_mem_klingenEisensteinSubspaceKJ_of_range (hkj : 4 < k ∨ k = 4 ∧ j = 0)
    (hG : (G : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      klingenEisensteinSubspaceKJ k j) :
    (heckeOperator (rhoKJ k j) D G : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      klingenEisensteinSubspaceKJ k j := by
  rcases hkj with hk | ⟨rfl, rfl⟩
  · exact heckeOperator_mem_klingenEisensteinSubspaceKJ D hk hG
  · rw [klingenEisensteinSubspaceKJ_four_eq_bot, Submodule.mem_bot] at hG
    have e : G = 0 := Subtype.ext hG
    rw [e, map_zero]
    exact zero_mem _

end SiegelUpperHalfSpace
