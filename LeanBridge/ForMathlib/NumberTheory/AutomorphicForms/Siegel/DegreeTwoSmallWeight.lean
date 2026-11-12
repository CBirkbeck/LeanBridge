import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoWeightFour

/-!
# The vanishing of `N_{j,k}(Γ₂)` in small weights

Let `N_{j,k}(Γ₂)` be the Petersson orthogonal complement of the cusp forms in `M_{j,k}(Γ₂)`. The
Siegel operator is injective on `N_{j,k}(Γ₂)` and sends `F` to `u e₁^j`, with `u` a modular form of
weight `k + j` on `SL(2, ℤ)`, a cusp form for `j > 0`. So `N_{j,k}(Γ₂) = 0` as soon as there are no
nonzero such forms `u`. This gives `N_{j,k}(Γ₂) = 0` in the following weights:

* `j > 0` and `k + j < 12` or `k + j = 14`, among them `(j, 4)` for `j = 2, 4, 6, 10`;
* `j = 0` and `k < 0` or `k = 2`.

Together with the known vanishing for odd `k` and odd `j`, this proves part of the claim that
`N_{j,k}(Γ₂) = 0` for `k < 4` apart from `(j, k) = (0, 0)`, which lies behind the corrected range of
the decomposition `N_{j,k}(Γ₂) = E_{j,k}(Γ₂) ⊕ KE_{j,k}(Γ₂)` of the knowl
`mf.siegel.subspace.degree.two`. The weights with even `k ≤ 2`, even `j` and `k + j ≥ 12`,
`k + j ≠ 14` need Witt's restriction to the diagonal; the whole claim is
`SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_eq_bot_of_lt_four`, in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoWeightZero`. Below weight `4`,
`E_{j,k}(Γ₂)` vanishes for `j > 0` (`SiegelUpperHalfSpace.siegelEisensteinSubspaceKJ_eq_bot`), but
`E_{0,k}(Γ₂)` and `KE_{j,k}(Γ₂)` are not shown to vanish.

## Main results

* `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_eq_bot_of_subsingleton_cuspForm`: `N_{j,k}(Γ₂) = 0`
  for `j > 0` when `S_{k+j}(SL(2, ℤ)) = 0`.
* `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_eq_bot_of_subsingleton_modularForm`:
  `N_{j,k}(Γ₂) = 0` when `M_{k+j}(SL(2, ℤ)) = 0`.
* `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_eq_bot_of_lt_twelve` (LMFDB
  `mf.siegel.subspace.degree.two`): `N_{j,k}(Γ₂) = 0` for `j > 0` and `k + j < 12`.
* `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_eq_bot_of_eq_fourteen` (LMFDB
  `mf.siegel.subspace.degree.two`): `N_{j,k}(Γ₂) = 0` for `j > 0` and `k + j = 14`.
* `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_zero_eq_bot_of_neg` (LMFDB
  `mf.siegel.subspace.degree.two`): `N_{0,k}(Γ₂) = 0` for `k < 0`.
* `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_zero_two_eq_bot` (LMFDB
  `mf.siegel.subspace.degree.two`): `N_{0,2}(Γ₂) = 0`.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open Complex Filter Module SymplecticGroup Topology

open scoped ComplexOrder MatrixGroups TensorProduct

namespace SiegelUpperHalfSpace

variable {k : ℤ} {j : ℕ} {c : Sym[ℂ]^j (Fin 2 → ℂ) →ₗ[ℂ] Sym[ℂ]^j (Fin 2 → ℂ) →ₗ⋆[ℂ] ℂ}

/-- **`N_{j,k}(Γ₂) = 0` for `j > 0` when there are no nonzero cusp forms of weight `k + j` on
`SL(2, ℤ)`**, for an admissible positive definite form `c`. -/
lemma cuspFormsOrthogonalKJ_eq_bot_of_subsingleton_cuspForm (hadm : IsAdmissibleForm (rhoKJ k j) c)
    (hpos : ∀ v, v ≠ 0 → 0 < c v v) (hj : j ≠ 0) (hS : Subsingleton (CuspForm 𝒮ℒ (k + j))) :
    cuspFormsOrthogonalKJ (integral (Fin 2)) k j c = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun F hF ↦ ?_
  rcases exists_hasSiegelFourierExpansion (rhoKJ k j) (isArithmetic_integral (Fin 2)) hF.1 with
    ⟨b, hb⟩
  have h₀ : symConstCoeff j (b 0) = 0 := by
    rw [apply_zero_eq_zero hj hF.1 hb, map_zero]
  refine eq_zero_of_mem_cuspFormsOrthogonalKJ_of_siegelOperatorVanishes hadm hpos hF
    fun τ' φ ↦ ?_
  have hu : siegelOperatorSeries b τ' = 0 :=
    DFunLike.congr_fun (Subsingleton.elim (siegelOperatorCuspKJ hF.1 hb h₀) 0) τ'
  simpa [hu] using tendsto_dual_diagPoint_siegelOperatorSeries τ' hF.1 hb φ

/-- **`N_{j,k}(Γ₂) = 0` when there are no nonzero modular forms of weight `k + j` on
`SL(2, ℤ)`**, for an admissible positive definite form `c`. -/
lemma cuspFormsOrthogonalKJ_eq_bot_of_subsingleton_modularForm
    (hadm : IsAdmissibleForm (rhoKJ k j) c) (hpos : ∀ v, v ≠ 0 → 0 < c v v)
    (hM : Subsingleton (ModularForm 𝒮ℒ (k + j))) :
    cuspFormsOrthogonalKJ (integral (Fin 2)) k j c = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun F hF ↦ ?_
  rcases exists_hasSiegelFourierExpansion (rhoKJ k j) (isArithmetic_integral (Fin 2)) hF.1 with
    ⟨b, hb⟩
  refine eq_zero_of_mem_cuspFormsOrthogonalKJ_of_siegelOperatorVanishes hadm hpos hF
    fun τ' φ ↦ ?_
  have hu : siegelOperatorKJ k j F b hF.1 hb τ' = 0 :=
    DFunLike.congr_fun (Subsingleton.elim (siegelOperatorKJ k j F b hF.1 hb) 0) τ'
  simpa [hu] using tendsto_dual_diagPoint_siegelOperatorKJ τ' hF.1 hb φ

/-- **`N_{j,k}(Γ₂) = 0` for `j > 0` and `k + j < 12`** (LMFDB `mf.siegel.subspace.degree.two`),
for an admissible positive definite form `c`. -/
lemma cuspFormsOrthogonalKJ_eq_bot_of_lt_twelve (hadm : IsAdmissibleForm (rhoKJ k j) c)
    (hpos : ∀ v, v ≠ 0 → 0 < c v v) (hj : j ≠ 0) (hk : k + j < 12) :
    cuspFormsOrthogonalKJ (integral (Fin 2)) k j c = ⊥ :=
  cuspFormsOrthogonalKJ_eq_bot_of_subsingleton_cuspForm hadm hpos hj
    (rank_zero_iff.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve hk))

/-- **`N_{j,k}(Γ₂) = 0` for `j > 0` and `k + j = 14`** (LMFDB `mf.siegel.subspace.degree.two`),
for an admissible positive definite form `c`, as `S₁₄(SL(2, ℤ)) ≅ M₂(SL(2, ℤ)) = 0`. -/
lemma cuspFormsOrthogonalKJ_eq_bot_of_eq_fourteen (hadm : IsAdmissibleForm (rhoKJ k j) c)
    (hpos : ∀ v, v ≠ 0 → 0 < c v v) (hj : j ≠ 0) (hk : k + j = 14) :
    cuspFormsOrthogonalKJ (integral (Fin 2)) k j c = ⊥ := by
  refine cuspFormsOrthogonalKJ_eq_bot_of_subsingleton_cuspForm hadm hpos hj ?_
  rw [hk]
  have h : Module.rank ℂ (ModularForm 𝒮ℒ ((14 : ℤ) - 12)) = 0 :=
    ModularForm.levelOne_weight_two_rank_zero
  exact rank_zero_iff.mp (CuspForm.discriminantEquiv.rank_eq.trans h)

variable {c₀ : Sym[ℂ]^0 (Fin 2 → ℂ) →ₗ[ℂ] Sym[ℂ]^0 (Fin 2 → ℂ) →ₗ⋆[ℂ] ℂ}

/-- **`N_{0,k}(Γ₂) = 0` for `k < 0`** (LMFDB `mf.siegel.subspace.degree.two`), for an admissible
positive definite form `c₀`. -/
lemma cuspFormsOrthogonalKJ_zero_eq_bot_of_neg (hadm : IsAdmissibleForm (rhoKJ k 0) c₀)
    (hpos : ∀ v, v ≠ 0 → 0 < c₀ v v) (hk : k < 0) :
    cuspFormsOrthogonalKJ (integral (Fin 2)) k 0 c₀ = ⊥ :=
  cuspFormsOrthogonalKJ_eq_bot_of_subsingleton_modularForm hadm hpos
    (rank_zero_iff.mp (ModularForm.levelOne_neg_weight_rank_zero (by simpa using hk)))

/-- **`N_{0,2}(Γ₂) = 0`** (LMFDB `mf.siegel.subspace.degree.two`), for an admissible positive
definite form `c₀`. -/
lemma cuspFormsOrthogonalKJ_zero_two_eq_bot (hadm : IsAdmissibleForm (rhoKJ 2 0) c₀)
    (hpos : ∀ v, v ≠ 0 → 0 < c₀ v v) : cuspFormsOrthogonalKJ (integral (Fin 2)) 2 0 c₀ = ⊥ :=
  cuspFormsOrthogonalKJ_eq_bot_of_subsingleton_modularForm hadm hpos
    (rank_zero_iff.mp ModularForm.levelOne_weight_two_rank_zero)

end SiegelUpperHalfSpace
