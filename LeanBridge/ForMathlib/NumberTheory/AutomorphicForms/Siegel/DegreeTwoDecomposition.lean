import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PeterssonConvergence
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SiegelOperatorKJ

/-!
# The decomposition `M_{j,k}(Γ₂) = S_{j,k}(Γ₂) ⊕ E_{j,k}(Γ₂) ⊕ KE_{j,k}(Γ₂)`

The space `M_{j,k}(Γ₂)` of Siegel modular forms of degree `2` and weight `ρ_{k,j} = det^k ⊗ Sym^j`
on `Γ₂ = Sp(4, ℤ)` is the direct sum of the cusp forms, the Siegel Eisenstein series and the
Klingen–Eisenstein series, for `k > 4` (LMFDB `mf.siegel.subspace.degree.two`).

For `k` odd, `M_{j,k}(Γ₂) = S_{j,k}(Γ₂)`: the Siegel operator takes values in the modular forms of
odd weight `k + j` on `SL(2, ℤ)` for `j` even, and `M_{j,k}(Γ₂) = 0` for `j` odd. For `k` even and
`j > 0`, `Φ(F) = u e₁^j` with `u` a cusp form, and `F - E(u)` has a vanishing Siegel operator, so
it is a cusp form. For `k` even and `j = 0`, one first subtracts from `F` a multiple of `ψ_k`, whose
constant term is `1`. The sum is direct since `Φ` determines `u`, and since the constant Fourier
coefficients of cusp forms and of Klingen–Eisenstein series vanish.

The knowl's definition of `N_{j,k}(Γ₂)` as the Petersson orthogonal complement of the cusp forms,
the decomposition `M_{j,k}(Γ₂) = S_{j,k}(Γ₂) ⊕ N_{j,k}(Γ₂)`,
`N_{j,k}(Γ₂) = E_{j,k}(Γ₂) ⊕ KE_{j,k}(Γ₂)` and the Hecke stability of `N_{j,k}(Γ₂)`, `E_{j,k}(Γ₂)`
and `KE_{j,k}(Γ₂)` are `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ`,
`SiegelUpperHalfSpace.modularFormsKJ_eq_cuspFormsKJ_sup_cuspFormsOrthogonalKJ`,
`SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_eq_sup`,
`SiegelUpperHalfSpace.heckeOperator_mem_cuspFormsOrthogonalKJ`,
`SiegelUpperHalfSpace.heckeOperator_mem_siegelEisensteinSubspaceKJ` and
`SiegelUpperHalfSpace.heckeOperator_mem_klingenEisensteinSubspaceKJ`, the second decomposition and
the stability of `E_{j,k}(Γ₂)` and `KE_{j,k}(Γ₂)` for `k > 4`.

## Main results

* `SiegelUpperHalfSpace.tendsto_dual_scalarPoint`: the constant Fourier coefficient is the limit
  along `diag(is, is)`.
* `SiegelUpperHalfSpace.sub_vectorKlingenEisenstein_mem_cuspFormsKJ`: `F - E(Φ(F))` is a cusp form.
* `SiegelUpperHalfSpace.modularFormsKJ_eq_cuspFormsKJ_of_odd`: `M_{j,k}(Γ₂) = S_{j,k}(Γ₂)` for `k`
  odd.
* `SiegelUpperHalfSpace.symConstCoeff_apply_zero_siegelEisensteinKJ`: the constant Fourier
  coefficient of `ψ_k` is `1`.
* `SiegelUpperHalfSpace.modularFormsKJ_le_sup`, `SiegelUpperHalfSpace.modularFormsKJ_eq_sup` (LMFDB
  `mf.siegel.subspace.degree.two`): `M_{j,k}(Γ₂) = S_{j,k}(Γ₂) + E_{j,k}(Γ₂) + KE_{j,k}(Γ₂)`.
* `SiegelUpperHalfSpace.siegelEisensteinSubspaceKJ_le_modularFormsKJ`: the Siegel Eisenstein series
  are modular forms.
* `SiegelUpperHalfSpace.siegelEisensteinSubspaceKJ_eq_span_singleton`: `E_{0,k}(Γ₂) = ℂ ψ_k`.
* `SiegelUpperHalfSpace.disjoint_sup_siegelEisensteinSubspaceKJ`: the sum is direct, with
  `SiegelUpperHalfSpace.disjoint_klingenEisensteinSubspaceKJ_cuspFormsKJ`.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open Complex Filter Module Real SymplecticGroup TauCeti Topology

open scoped MatrixGroups TensorProduct UpperHalfPlane

namespace SiegelUpperHalfSpace

variable {k : ℤ} {j : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    {G : SiegelUpperHalfSpace (Fin 2) → V} {a : dualLattice (integral (Fin 2)) → V}

/-- **The constant term of a form with a positive semidefinite Fourier expansion**:
`φ(G(diag(is, is))) → φ(a(0))` as `s → ∞`, the case `T = id` of
`SiegelUpperHalfSpace.tendsto_dual_comp_scalarPoint`. -/
lemma tendsto_dual_scalarPoint (φ : Dual ℂ V)
    (ha : HasSiegelFourierExpansion (integral (Fin 2)) G a)
    (hpsd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) :
    Tendsto (fun s : Set.Ioi (0 : ℝ) ↦ φ (G (scalarPoint s))) atTop (𝓝 (φ (a 0))) :=
  tendsto_dual_comp_scalarPoint ha hpsd (A := 1) (by simp) one_pos (T := id)
    (fun Z i j ↦ by fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]) φ

variable {F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)}
    {b : dualLattice (integral (Fin 2)) → Sym[ℂ]^j (Fin 2 → ℂ)}

/-- **`F - E(Φ(F))` is a cusp form**: for `F ∈ M_{k,j}(Sp(4, ℤ))`, `k > 4` even, with
`Φ(F) = u e₁^j` for a cusp form `u` of weight `k + j`, the Siegel operator of `F - E(u)`
vanishes. -/
lemma sub_vectorKlingenEisenstein_mem_cuspFormsKJ (hk : 4 < k) (hk' : Even k)
    (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) (h₀ : symConstCoeff j (b 0) = 0) : F -
    vectorKlingenEisenstein k j (siegelOperatorCuspKJ hF hb h₀) ∈
      cuspFormsKJ k j (integral (Fin 2)) := by
  have hE : vectorKlingenEisenstein k j (siegelOperatorCuspKJ hF hb h₀) ∈
      modularFormsKJ k j (integral (Fin 2)) :=
    vectorKlingenEisenstein_mem_modularFormsKJ _ hk hk'
  refine ⟨sub_mem hF hE, isCuspForm_of_siegelOperatorVanishes (sub_mem hF hE) fun τ' φ ↦ ?_⟩
  have h₁ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ φ (F (diagPoint τ' t))) atTop
      (𝓝 (siegelOperatorSeries b τ' * φ (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1))) :=
    tendsto_dual_diagPoint_siegelOperatorSeries τ' hF hb φ
  have h₂ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ φ (vectorKlingenEisenstein k j
      (siegelOperatorCuspKJ hF hb h₀) (diagPoint τ' t))) atTop
      (𝓝 (siegelOperatorSeries b τ' * φ (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1))) :=
    tendsto_dual_vectorKlingenEisenstein_diagPoint (siegelOperatorCuspKJ hF hb h₀) φ τ' hk hk'
  simpa using h₁.sub h₂

private lemma vectorKlingenEisenstein_mem_klingenEisensteinSubspaceKJ (hk : 4 < k) (hk' : Even k)
    (f : CuspForm 𝒮ℒ (k + j)) : vectorKlingenEisenstein k j f ∈ klingenEisensteinSubspaceKJ k j :=
  ⟨Submodule.subset_span ⟨f, rfl⟩, vectorKlingenEisenstein_mem_modularFormsKJ f hk hk'⟩

/-- **For `k` odd every form is a cusp form**: `Φ(F)` is a modular form of odd weight `k + j` on
`SL(2, ℤ)` for `j` even, and there are no nonzero forms for `j` odd. -/
lemma modularFormsKJ_eq_cuspFormsKJ_of_odd (hk : Odd k) :
    modularFormsKJ k j (integral (Fin 2)) = cuspFormsKJ k j (integral (Fin 2)) := by
  refine le_antisymm (fun F hF ↦ ?_) (cuspForms_le_modularForms _ _ _)
  rcases Nat.even_or_odd j with hj | hj
  · rcases exists_hasSiegelFourierExpansion (rhoKJ k j) (isArithmetic_integral (Fin 2)) hF with
      ⟨b, hb⟩
    have hodd : Odd (k + j) := hk.add_even (by exact_mod_cast hj)
    refine ⟨hF, isCuspForm_of_siegelOperatorVanishes hF fun τ' φ ↦ ?_⟩
    have h₁ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ φ (F (diagPoint τ' t))) atTop
        (𝓝 (siegelOperatorKJ k j F b hF hb τ' * φ (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1))) :=
      tendsto_dual_diagPoint_siegelOperatorKJ τ' hF hb φ
    rw [ModularForm.levelOne_odd_weight_eq_zero hodd (siegelOperatorKJ k j F b hF hb)] at h₁
    simpa using h₁
  · rw [modularFormsKJ_eq_bot_of_odd hj, Submodule.mem_bot] at hF
    rw [hF]
    exact zero_mem _

/-! ### The Siegel Eisenstein series in the decomposition -/

private lemma eq_smul_tprod_zero (v : Sym[ℂ]^0 (Fin 2 → ℂ)) :
    v = symConstCoeff 0 v • ⨂ₛ[ℂ] _ : Fin 0, (Pi.single 0 1 : Fin 2 → ℂ) :=
  eq_smul_tprod_of_symPowerRep_eq (symPowerRep_zero _ v)

private lemma symConstCoeff_siegelEisensteinKJ (Z : SiegelUpperHalfSpace (Fin 2)) :
    symConstCoeff 0 (siegelEisensteinKJ k Z) = siegelEisensteinSeries k Z := by
  rw [siegelEisensteinKJ, map_smul, symConstCoeff_tprod_single, smul_eq_mul, mul_one]

/-- **The constant Fourier coefficient of `ψ_k` is `1`**, for even `k > 5`. -/
lemma symConstCoeff_apply_zero_siegelEisensteinKJ (hk : 5 < k) (hk' : Even k)
    {c : dualLattice (integral (Fin 2)) → Sym[ℂ]^0 (Fin 2 → ℂ)}
    (hc : HasSiegelFourierExpansion (integral (Fin 2)) (siegelEisensteinKJ k) c) :
    symConstCoeff 0 (c 0) = 1 := by
  refine tendsto_nhds_unique (tendsto_dual_scalarPoint (symConstCoeff 0) hc
    (posSemidef_of_apply_ne_zero (siegelEisensteinKJ_mem_modularFormsKJ hk hk') hc)) ?_
  simp only [symConstCoeff_siegelEisensteinKJ]
  exact tendsto_siegelEisensteinSeries_scalarPoint hk hk'

private lemma mem_sup_of_zero (hk : 5 < k) (hk' : Even k)
    {H : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^0 (Fin 2 → ℂ)}
    (hH : H ∈ modularFormsKJ k 0 (integral (Fin 2))) : H ∈ cuspFormsKJ k 0 (integral (Fin 2)) ⊔
    siegelEisensteinSubspaceKJ k 0 ⊔ klingenEisensteinSubspaceKJ k 0 := by
  have hψ : siegelEisensteinKJ k ∈ modularFormsKJ k 0 (integral (Fin 2)) :=
    siegelEisensteinKJ_mem_modularFormsKJ hk hk'
  rcases exists_hasSiegelFourierExpansion (rhoKJ k 0) (isArithmetic_integral (Fin 2)) hH with
    ⟨b, hb⟩
  rcases exists_hasSiegelFourierExpansion (rhoKJ k 0) (isArithmetic_integral (Fin 2)) hψ with
    ⟨c, hc⟩
  generalize hc₀ : symConstCoeff 0 (b 0) = c₀
  have hG : H - c₀ • siegelEisensteinKJ k ∈ modularFormsKJ k 0 (integral (Fin 2)) :=
    sub_mem hH (Submodule.smul_mem _ _ hψ)
  have hbG : HasSiegelFourierExpansion (integral (Fin 2)) (H - c₀ • siegelEisensteinKJ k)
      (b - c₀ • c) := by
    intro τ φ
    have e : φ ((H - c₀ • siegelEisensteinKJ k) τ) = φ (H τ) - c₀ * φ (siegelEisensteinKJ k τ) := by
      simp
    rw [e]
    refine ((hb τ φ).sub ((hc τ φ).mul_left c₀)).congr_fun fun n ↦ ?_
    simp
    ring1
  have h₀ : symConstCoeff 0 ((b - c₀ • c) 0) = 0 := by
    simp [symConstCoeff_apply_zero_siegelEisensteinKJ hk hk' hc, hc₀]
  have hk₄ : 4 < k := by
    linarith
  have hS : (H - c₀ • siegelEisensteinKJ k) -
      vectorKlingenEisenstein k 0 (siegelOperatorCuspKJ hG hbG h₀) ∈
        cuspFormsKJ k 0 (integral (Fin 2)) :=
    sub_vectorKlingenEisenstein_mem_cuspFormsKJ hk₄ hk' hG hbG h₀
  have hKE : vectorKlingenEisenstein k 0 (siegelOperatorCuspKJ hG hbG h₀) ∈
      klingenEisensteinSubspaceKJ k 0 :=
    vectorKlingenEisenstein_mem_klingenEisensteinSubspaceKJ hk₄ hk' _
  have hE : c₀ • siegelEisensteinKJ k ∈ siegelEisensteinSubspaceKJ k 0 :=
    Submodule.smul_mem _ _ (siegelEisensteinKJ_mem_siegelEisensteinSubspaceKJ hk hk')
  refine Submodule.mem_sup.mpr ⟨_, Submodule.mem_sup.mpr ⟨_, hS, _, hE, rfl⟩, _, hKE, ?_⟩
  abel

variable (k j) in
/-- **`M_{j,k}(Γ₂)` is the sum of the cusp forms, the Siegel Eisenstein series and the
Klingen–Eisenstein series** (LMFDB `mf.siegel.subspace.degree.two`), for `k > 4`. -/
lemma modularFormsKJ_le_sup (hk : 4 < k) : modularFormsKJ k j (integral (Fin 2)) ≤
    cuspFormsKJ k j (integral (Fin 2)) ⊔ siegelEisensteinSubspaceKJ k j ⊔
      klingenEisensteinSubspaceKJ k j := by
  intro F hF
  rcases Int.even_or_odd k with hk' | hk'
  · rcases eq_or_ne j 0 with rfl | hj
    · refine mem_sup_of_zero ?_ hk' hF
      rcases hk' with ⟨m, rfl⟩
      omega
    · rcases exists_hasSiegelFourierExpansion (rhoKJ k j) (isArithmetic_integral (Fin 2)) hF with
        ⟨b, hb⟩
      have h₀ : symConstCoeff j (b 0) = 0 := by
        rw [apply_zero_eq_zero hj hF hb, map_zero]
      have hS : F - vectorKlingenEisenstein k j (siegelOperatorCuspKJ hF hb h₀) ∈
          cuspFormsKJ k j (integral (Fin 2)) :=
        sub_vectorKlingenEisenstein_mem_cuspFormsKJ hk hk' hF hb h₀
      have hKE : vectorKlingenEisenstein k j (siegelOperatorCuspKJ hF hb h₀) ∈
          klingenEisensteinSubspaceKJ k j :=
        vectorKlingenEisenstein_mem_klingenEisensteinSubspaceKJ hk hk' _
      refine Submodule.mem_sup.mpr ⟨_, Submodule.mem_sup_left hS, _, hKE, ?_⟩
      abel
  · refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
    rwa [← modularFormsKJ_eq_cuspFormsKJ_of_odd hk']

private lemma eq_smul_siegelEisensteinKJ (hk : 5 < k) {v : Sym[ℂ]^0 (Fin 2 → ℂ)}
    {H : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^0 (Fin 2 → ℂ)}
    (hH : IsVectorSiegelEisensteinSeries (rhoKJ k 0) v H) :
    H = symConstCoeff 0 v • siegelEisensteinKJ k := by
  refine hH.unique fun Z φ ↦ ?_
  have h : HasSum (fun x : SiegelParabolicCosets (Fin 2) ↦ symConstCoeff 0 v *
      φ (vectorSiegelEisensteinTerm (rhoKJ k 0) (⨂ₛ[ℂ] _ : Fin 0, Pi.single 0 1) Z x.out))
        (symConstCoeff 0 v * φ (siegelEisensteinKJ k Z)) :=
    (isVectorSiegelEisensteinSeries_siegelEisensteinKJ hk Z φ).mul_left _
  have e : φ ((symConstCoeff 0 v • siegelEisensteinKJ k) Z) =
      symConstCoeff 0 v * φ (siegelEisensteinKJ k Z) := by
    simp
  rw [e]
  refine h.congr_fun fun x ↦ ?_
  conv_lhs => rw [eq_smul_tprod_zero v]
  rw [vectorSiegelEisensteinTerm, vectorSiegelEisensteinTerm, map_smul, map_smul, smul_eq_mul]

/-- The element `diag(-1, 1)` of `GL(2, ℤ)`. -/
private def negOneGL : GL (Fin 2) ℤ where
  val := !![-1, 0; 0, 1]
  inv := !![-1, 0; 0, 1]
  val_inv := by
    ext a c
    fin_cases a <;> fin_cases c <;> simp
  inv_val := by
    ext a c
    fin_cases a <;> fin_cases c <;> simp

private lemma eq_zero_of_isGLIntInvariant_of_odd (hk : Odd k) {v : Sym[ℂ]^0 (Fin 2 → ℂ)}
    (hv : IsGLIntInvariant (rhoKJ k 0) v) : v = 0 := by
  have h : rhoKJ k 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) negOneGL) v = v := hv negOneGL
  have e : rhoKJ k 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) negOneGL) v =
      (((GeneralLinearGroup.map (Int.castRingHom ℂ) negOneGL).det ^ k : ℂˣ) : ℂ) •
        symPowerRep ℂ 2 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) negOneGL) v :=
    rfl
  have hd : ((GeneralLinearGroup.map (Int.castRingHom ℂ) negOneGL : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = !![-1, 0; 0, 1] := by
    ext a c
    fin_cases a <;> fin_cases c <;> simp [negOneGL]
  rw [e, symPowerRep_zero, Units.val_zpow_eq_zpow_val, GeneralLinearGroup.val_det_apply, hd,
    det_fin_two_of] at h
  simp only [mul_one, mul_zero, sub_zero, hk.neg_one_zpow, neg_smul, one_smul] at h
  have h₂ : (2 : ℂ) • v = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel v
  simpa using h₂

variable (k j) in
/-- **The Siegel Eisenstein series are modular forms**, for `k > 4`. -/
lemma siegelEisensteinSubspaceKJ_le_modularFormsKJ (hk : 4 < k) :
    siegelEisensteinSubspaceKJ k j ≤ modularFormsKJ k j (integral (Fin 2)) := by
  rcases eq_or_ne j 0 with rfl | hj
  · refine Submodule.span_le.mpr ?_
    rintro G ⟨v, hv, hG⟩
    rcases Int.even_or_odd k with hk' | hk'
    · have hk₅ : 5 < k := by
        rcases hk' with ⟨m, rfl⟩
        omega
      rw [eq_smul_siegelEisensteinKJ hk₅ hG]
      exact Submodule.smul_mem _ _ (siegelEisensteinKJ_mem_modularFormsKJ hk₅ hk')
    · rw [eq_zero_of_isGLIntInvariant_of_odd hk' hv] at hG
      have hG₀ : G = 0 := by
        refine hG.unique fun Z φ ↦ ?_
        simp [vectorSiegelEisensteinTerm]
      rw [hG₀]
      exact zero_mem _
  · rw [siegelEisensteinSubspaceKJ_eq_bot k hj]
    exact bot_le

variable (k j) in
/-- **The decomposition `M_{j,k}(Γ₂) = S_{j,k}(Γ₂) + E_{j,k}(Γ₂) + KE_{j,k}(Γ₂)`** (LMFDB
`mf.siegel.subspace.degree.two`), for `k > 4`. The sum is direct
(`SiegelUpperHalfSpace.disjoint_klingenEisensteinSubspaceKJ_cuspFormsKJ`,
`SiegelUpperHalfSpace.disjoint_sup_siegelEisensteinSubspaceKJ`). -/
lemma modularFormsKJ_eq_sup (hk : 4 < k) : modularFormsKJ k j (integral (Fin 2)) =
    cuspFormsKJ k j (integral (Fin 2)) ⊔ siegelEisensteinSubspaceKJ k j ⊔
      klingenEisensteinSubspaceKJ k j :=
  le_antisymm (modularFormsKJ_le_sup k j hk) (sup_le (sup_le (cuspForms_le_modularForms _ _ _)
    (siegelEisensteinSubspaceKJ_le_modularFormsKJ k j hk))
      (klingenEisensteinSubspaceKJ_le_modularFormsKJ k j))

/-- **The space `E_{0,k}(Γ₂)` is the line of `ψ_k`**, for even `k > 5` (LMFDB
`mf.siegel.subspace.degree.two`). -/
lemma siegelEisensteinSubspaceKJ_eq_span_singleton (hk : 5 < k) (hk' : Even k) :
    siegelEisensteinSubspaceKJ k 0 = Submodule.span ℂ {siegelEisensteinKJ k} := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro G ⟨v, -, hG⟩
    rw [eq_smul_siegelEisensteinKJ hk hG]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rintro _ rfl
    exact siegelEisensteinKJ_mem_siegelEisensteinSubspaceKJ hk hk'

private lemma apply_zero_eq_zero_of_mem_cuspFormsKJ (hF : F ∈ cuspFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) : b 0 = 0 := by
  by_contra h
  have hv : SiegelOperatorVanishes F := by
    have h₁ : SiegelOperatorVanishes (slash (rhoKJ k j) (map (algebraMap ℚ ℝ) 1) F) := hF.2 1
    rwa [map_one, slash_one] at h₁
  have h₂ : ((0 : dualLattice (integral (Fin 2))) : Matrix (Fin 2) (Fin 2) ℚ).PosDef :=
    posDef_of_siegelOperatorVanishes hF.1 hb hv 0 h
  have h₃ : 0 < star ![(1 : ℚ), 0] ⬝ᵥ ((0 : dualLattice (integral (Fin 2))) :
      Matrix (Fin 2) (Fin 2) ℚ) *ᵥ ![(1 : ℚ), 0] :=
    (posDef_iff_dotProduct_mulVec.mp h₂).2 (by simp)
  simp at h₃

lemma symConstCoeff_apply_zero_vectorKlingenEisenstein (hk : 4 < k) (hk' : Even k)
    (f : CuspForm 𝒮ℒ (k + j))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) (vectorKlingenEisenstein k j f) b) :
    symConstCoeff j (b 0) = 0 := by
  have hκ : vectorKlingenEisenstein k j f ∈ modularFormsKJ k j (integral (Fin 2)) :=
    vectorKlingenEisenstein_mem_modularFormsKJ f hk hk'
  refine symConstCoeff_apply_zero_eq_zero hκ hb f fun τ' ↦ ?_
  have h₃ : siegelOperatorSeries b τ' * symConstCoeff j (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1) =
      f τ' * symConstCoeff j (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1) :=
    tendsto_nhds_unique (tendsto_dual_diagPoint_siegelOperatorSeries τ' hκ hb (symConstCoeff j))
      (tendsto_dual_vectorKlingenEisenstein_diagPoint f (symConstCoeff j) τ' hk hk')
  rwa [symConstCoeff_tprod_single, mul_one, mul_one] at h₃

variable (k j) in
/-- **The Siegel Eisenstein series meet the sum of the cusp forms and the Klingen–Eisenstein series
trivially**, for `k > 4`: the constant Fourier coefficient of `ψ_k` is `1`, while those of the cusp
forms and of the Klingen–Eisenstein series vanish. -/
lemma disjoint_sup_siegelEisensteinSubspaceKJ (hk : 4 < k) : Disjoint
    (cuspFormsKJ k j (integral (Fin 2)) ⊔ klingenEisensteinSubspaceKJ k j)
      (siegelEisensteinSubspaceKJ k j) := by
  rcases eq_or_ne j 0 with rfl | hj
  · rcases Int.even_or_odd k with hk' | hk'
    · have hk₅ : 5 < k := by
        rcases hk' with ⟨m, rfl⟩
        omega
      rw [siegelEisensteinSubspaceKJ_eq_span_singleton hk₅ hk',
        klingenEisensteinSubspaceKJ_eq_range hk (by simp), Submodule.disjoint_def]
      intro x hx hx'
      rcases Submodule.mem_span_singleton.mp hx' with ⟨c, rfl⟩
      rcases Submodule.mem_sup.mp hx with ⟨s, hs, _, ⟨f, rfl⟩, hsum⟩
      have hψ : siegelEisensteinKJ k ∈ modularFormsKJ k 0 (integral (Fin 2)) :=
        siegelEisensteinKJ_mem_modularFormsKJ hk₅ hk'
      have hκ : vectorKlingenEisenstein k 0 f ∈ modularFormsKJ k 0 (integral (Fin 2)) :=
        vectorKlingenEisenstein_mem_modularFormsKJ f hk hk'
      rcases exists_hasSiegelFourierExpansion (rhoKJ k 0) (isArithmetic_integral (Fin 2)) hψ with
        ⟨bψ, hbψ⟩
      rcases exists_hasSiegelFourierExpansion (rhoKJ k 0) (isArithmetic_integral (Fin 2)) hs.1 with
        ⟨bs, hbs⟩
      rcases exists_hasSiegelFourierExpansion (rhoKJ k 0) (isArithmetic_integral (Fin 2)) hκ with
        ⟨bκ, hbκ⟩
      have h₁ :
          HasSiegelFourierExpansion (integral (Fin 2)) (c • siegelEisensteinKJ k) (bs + bκ) := by
        rw [← hsum]
        exact hbs.add _ hbκ
      have h₂ : bs + bκ = c • bψ :=
        h₁.unique_of_isArithmetic (isArithmetic_integral (Fin 2)) (hbψ.const_smul _ c)
      have h₃ : symConstCoeff 0 ((bs + bκ) 0) = symConstCoeff 0 ((c • bψ) 0) :=
        congrArg (symConstCoeff 0) (congrFun h₂ 0)
      simp only [Pi.add_apply, Pi.smul_apply, map_smul, smul_eq_mul,
        apply_zero_eq_zero_of_mem_cuspFormsKJ hs hbs, zero_add,
        symConstCoeff_apply_zero_vectorKlingenEisenstein hk hk' f hbκ,
        symConstCoeff_apply_zero_siegelEisensteinKJ hk₅ hk' hbψ, mul_one] at h₃
      rw [← h₃, zero_smul]
    · have hE : siegelEisensteinSubspaceKJ k 0 = ⊥ := by
        rw [siegelEisensteinSubspaceKJ, siegelEisensteinSubspace, Submodule.span_eq_bot]
        rintro G ⟨v, hv, hG⟩
        rw [eq_zero_of_isGLIntInvariant_of_odd hk' hv] at hG
        refine hG.unique fun Z φ ↦ ?_
        simp [vectorSiegelEisensteinTerm]
      rw [hE]
      exact disjoint_bot_right
  · rw [siegelEisensteinSubspaceKJ_eq_bot k hj]
    exact disjoint_bot_right

end SiegelUpperHalfSpace
