import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ArithmeticFiniteDimensional

/-!
# The decomposition of paramodular cusp forms into old and new forms, unconditionally

The paramodular group `K(N)` is arithmetic, so that the space `S_{k,j}(K(N))` is finite-dimensional
and the Petersson product is definite on it. This gives
`S_{k,j}(K(N)) = S_{k,j}^old(K(N)) ⊕ S_{k,j}^new(K(N))` (LMFDB `mf.siegel.newspace`,
`mf.siegel.newform`) for every level `N` and every weight `ρ_{k,j} = det^k ⊗ Sym^j`, with the
trivial character, for every admissible positive definite Hermitian form on `Sym^j(ℂ²)`, such as
`SiegelUpperHalfSpace.symHermitianForm`, and with no other hypothesis. The same holds for the scalar
weight `det^k` on `ℂ`, through the identification of `ℂ` with `Sym⁰(ℂ²)`.

Not proved here: that the newforms form a basis of `S_{k,j}^new(K(N))`. A basis of eigenforms of the
good Hecke operators needs their adjoints on `K(N)`, which are proved here only for `Sp(4, ℤ)`
(`SiegelUpperHalfSpace.peterssonProduct_heckeOperator`). A basis of eigenforms of all Hecke
operators, with multiplicity one, is the theory of Roberts and Schmidt, which is absent from the
pins.

## Main results

* `SiegelUpperHalfSpace.finiteDimensional_paramodularCuspForms_rhoKJ`: `S_{k,j}(K(N))` is
  finite-dimensional.
* `SiegelUpperHalfSpace.isPeterssonDefinite_paramodularCuspForms_rhoKJ`: the Petersson product is
  definite on `S_{k,j}(K(N))`.
* `SiegelUpperHalfSpace.disjoint_paramodularOldSubspace_paramodularNewSubspace_rhoKJ`,
  `SiegelUpperHalfSpace.paramodularOldSubspace_sup_paramodularNewSubspace_rhoKJ` (LMFDB
  `mf.siegel.newspace`, `mf.siegel.newform`):
  `S_{k,j}(K(N)) = S_{k,j}^old(K(N)) ⊕ S_{k,j}^new(K(N))`.
* `SiegelUpperHalfSpace.isModerateForm_detPowerRep`: the form `v w̄` is moderate for `det^k`.
* `SiegelUpperHalfSpace.finiteDimensional_cuspForms_detPowerRep`: `S_k(Γ)` is finite-dimensional,
  for arithmetic `Γ`.
* `SiegelUpperHalfSpace.disjoint_paramodularOldSubspace_paramodularNewSubspace_scalar`,
  `SiegelUpperHalfSpace.paramodularOldSubspace_sup_paramodularNewSubspace_scalar`:
  `S_k(K(N)) = S_k^old(K(N)) ⊕ S_k^new(K(N))` in scalar weight.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open Complex MeasureTheory Module Set SymplecticGroup

open scoped ComplexConjugate ComplexOrder TensorProduct

namespace SiegelUpperHalfSpace

variable {k : ℤ} {j : ℕ} {N : ℕ+} {c : Sym[ℂ]^j (Fin 2 → ℂ) →ₗ[ℂ] Sym[ℂ]^j (Fin 2 → ℂ) →ₗ⋆[ℂ] ℂ}

variable (k j N) in
/-- **The space `S_{k,j}(K(N))` of paramodular cusp forms is finite-dimensional.** -/
lemma finiteDimensional_paramodularCuspForms_rhoKJ :
    FiniteDimensional ℂ (paramodularCuspForms (rhoKJ k j) N) :=
  finiteDimensional_cuspFormsKJ_of_isArithmetic k j (isArithmetic_paramodular _)

/-- **The Petersson product is definite on `S_{k,j}(K(N))`**, for an admissible positive definite
form `c`. -/
lemma isPeterssonDefinite_paramodularCuspForms_rhoKJ (hadm : IsAdmissibleForm (rhoKJ k j) c)
    (hpos : ∀ v, v ≠ 0 → 0 < c v v) :
    IsPeterssonDefinite (paramodularLevel N) (rhoKJ k j) c (paramodularCuspForms (rhoKJ k j) N) :=
  isPeterssonDefinite_cuspForms_of_isArithmetic (isModerateForm_rhoKJ k c) hadm hpos
    (fun g _ hf ↦ hf.slash_rhoKJ k g) (isArithmetic_paramodular _)

/-- **No nonzero paramodular cusp form is both old and new** (LMFDB `mf.siegel.newspace`,
`mf.siegel.newform`), for the Petersson product of an admissible positive definite form `c`. -/
lemma disjoint_paramodularOldSubspace_paramodularNewSubspace_rhoKJ
    (hadm : IsAdmissibleForm (rhoKJ k j) c) (hpos : ∀ v, v ≠ 0 → 0 < c v v) :
    Disjoint (paramodularOldSubspace (rhoKJ k j) N) (paramodularNewSubspace (rhoKJ k j) N c) :=
  disjoint_paramodularOldSubspace_paramodularNewSubspace
    (isPeterssonDefinite_paramodularCuspForms_rhoKJ hadm hpos)

/-- **`S_{k,j}(K(N)) = S_{k,j}^old(K(N)) ⊕ S_{k,j}^new(K(N))`** (LMFDB `mf.siegel.newspace`,
`mf.siegel.newform`), for every level `N` and weight `ρ_{k,j}`, with the Petersson product of an
admissible positive definite form `c`; the sum is direct
(`SiegelUpperHalfSpace.disjoint_paramodularOldSubspace_paramodularNewSubspace_rhoKJ`). -/
lemma paramodularOldSubspace_sup_paramodularNewSubspace_rhoKJ
    (hadm : IsAdmissibleForm (rhoKJ k j) c) (hpos : ∀ v, v ≠ 0 → 0 < c v v) :
    paramodularOldSubspace (rhoKJ k j) N ⊔ paramodularNewSubspace (rhoKJ k j) N c =
      paramodularCuspForms (rhoKJ k j) N :=
  have : FiniteDimensional ℂ (paramodularCuspForms (rhoKJ k j) N) :=
    finiteDimensional_paramodularCuspForms_rhoKJ k j N
  paramodularOldSubspace_sup_paramodularNewSubspace
    (isPeterssonDefinite_paramodularCuspForms_rhoKJ hadm hpos)

/-! ### The scalar weight -/

/-- **The form `v w̄` is moderate for the weight `det^k`.** -/
lemma isModerateForm_detPowerRep : IsModerateForm (TauCeti.detPowerRep ℂ 2 k) (innerₛₗ ℂ).flip where
  continuous v w := by
    have e : (fun τ : SiegelUpperHalfSpace (Fin 2) ↦
        (innerₛₗ ℂ).flip (TauCeti.detPowerRep ℂ 2 k (imGL τ) v) w) =
          fun τ ↦ (((τ.val.map im).det ^ k : ℝ) : ℂ) * v * conj w := by
      funext τ
      rw [ofReal_zpow]
      exact peterssonIntegrand_detPowerRep k τ (fun _ ↦ v) (fun _ ↦ w)
    rw [e]
    exact ((continuous_ofReal.comp (continuous_det_im_zpow k)).mul continuous_const).mul
      continuous_const
  exists_bound := by
    refine ⟨2 * k.natAbs, fun v w ↦ ⟨((25 : ℝ) / 12) ^ k.natAbs * (‖v‖ * ‖w‖), fun τ hτ ↦ ?_⟩⟩
    have h : (innerₛₗ ℂ).flip (TauCeti.detPowerRep ℂ 2 k (imGL τ) v) w =
        (((τ.val.map im).det ^ k : ℝ) : ℂ) * v * conj w := by
      rw [ofReal_zpow]
      exact peterssonIntegrand_detPowerRep k τ (fun _ ↦ v) (fun _ ↦ w)
    have hD : 0 ≤ (τ.val.map im).det ^ k := (zpow_pos τ.posDef_im.det_pos k).le
    rw [h, norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hD, RCLike.norm_conj]
    refine (mul_le_mul_of_nonneg_right (det_im_zpow_le k hτ)
      (mul_nonneg (norm_nonneg v) (norm_nonneg w))).trans_eq' (by ring1) |>.trans_eq (by ring1)

variable {f : SiegelUpperHalfSpace (Fin 2) → ℂ}

/-- The identification of functions with values in `ℂ` with functions with values in `Sym⁰(ℂ²)`. -/
private noncomputable def scalarToSym : (SiegelUpperHalfSpace (Fin 2) → ℂ) →ₗ[ℂ]
    (SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^0 (Fin 2 → ℂ)) where
  toFun f τ := f τ • ⨂ₛ[ℂ] _ : Fin 0, (Pi.single 0 1 : Fin 2 → ℂ)
  map_add' f g := by
    funext τ
    exact add_smul _ _ _
  map_smul' c f := by
    funext τ
    exact mul_smul _ _ _

private lemma scalarToSym_apply (τ : SiegelUpperHalfSpace (Fin 2)) :
    scalarToSym f τ = f τ • ⨂ₛ[ℂ] _ : Fin 0, (Pi.single 0 1 : Fin 2 → ℂ) :=
  rfl

private lemma slash_scalarToSym (g : symplecticGroup (Fin 2) ℝ) :
    slash (rhoKJ k 0) g (scalarToSym f) = scalarToSym (slash (TauCeti.detPowerRep ℂ 2 k) g f) := by
  funext τ
  rw [scalarToSym_apply, slash_apply, slash_apply, scalarToSym_apply, map_smul, rhoKJ_apply,
    symPowerRep_zero, smul_smul, TauCeti.detPowerRep_apply, mul_comm]

private lemma isHolomorphic_scalarToSym (hf : IsHolomorphic f) : IsHolomorphic (scalarToSym f) := by
  intro φ
  refine ((hf LinearMap.id).mul_const (φ (⨂ₛ[ℂ] _ : Fin 0, Pi.single 0 1))).congr fun Z hZ ↦ ?_
  rw [extend_of_mem _ hZ, extend_of_mem _ hZ]
  simp [scalarToSym_apply]

variable {Γ : Subgroup (symplecticGroup (Fin 2) ℚ)}

private lemma scalarToSym_mem_cuspFormsKJ (hf : f ∈ cuspForms (TauCeti.detPowerRep ℂ 2 k) Γ 1) :
    scalarToSym f ∈ cuspFormsKJ k 0 Γ := by
  refine ⟨(mem_modularForms_iff_slash _ _ _ _).mpr ⟨isHolomorphic_scalarToSym hf.1.1, fun γ ↦ ?_⟩,
    fun γ τ' φ ↦ ?_⟩
  · rw [slash_scalarToSym, ((mem_modularForms_iff_slash _ _ _ _).mp hf.1).2 γ, MonoidHom.one_apply,
      Units.val_one, one_smul, one_smul]
  · rw [slash_scalarToSym]
    simpa [scalarToSym_apply] using (hf.2 γ τ' LinearMap.id).mul_const
      (φ (⨂ₛ[ℂ] _ : Fin 0, (Pi.single 0 1 : Fin 2 → ℂ)))

/-- **The space `S_k(Γ)` of cusp forms of scalar weight `k` is finite-dimensional**, for every
arithmetic subgroup `Γ`. -/
lemma finiteDimensional_cuspForms_detPowerRep (hΓ : IsArithmetic Γ) :
    FiniteDimensional ℂ (cuspForms (TauCeti.detPowerRep ℂ 2 k) Γ 1) := by
  have : FiniteDimensional ℂ (cuspFormsKJ k 0 Γ) :=
    finiteDimensional_cuspFormsKJ_of_isArithmetic k 0 hΓ
  let L : cuspForms (TauCeti.detPowerRep ℂ 2 k) Γ 1 →ₗ[ℂ] cuspFormsKJ k 0 Γ :=
    (scalarToSym.domRestrict (cuspForms (TauCeti.detPowerRep ℂ 2 k) Γ 1)).codRestrict
      (cuspFormsKJ k 0 Γ) fun f ↦ scalarToSym_mem_cuspFormsKJ f.2
  refine FiniteDimensional.of_injective (V₂ := cuspFormsKJ k 0 Γ) L fun f g h ↦ Subtype.ext ?_
  funext τ
  have h₁ : scalarToSym (f : SiegelUpperHalfSpace (Fin 2) → ℂ) τ = scalarToSym g τ :=
    congrFun (congrArg Subtype.val h) τ
  simpa [scalarToSym_apply, symConstCoeff_tprod_single] using congrArg (symConstCoeff 0) h₁

/-- **No nonzero paramodular cusp form of scalar weight is both old and new**, for the Petersson
inner product. -/
lemma disjoint_paramodularOldSubspace_paramodularNewSubspace_scalar :
    Disjoint (paramodularOldSubspace (TauCeti.detPowerRep ℂ 2 k) N)
      (paramodularNewSubspace (TauCeti.detPowerRep ℂ 2 k) N (innerₛₗ ℂ).flip) :=
  disjoint_paramodularOldSubspace_paramodularNewSubspace_detPowerRep fun _ _ hf hg ↦
    integrableOn_peterssonIntegrand_of_isArithmetic isModerateForm_detPowerRep
      (isAdmissibleForm_detPowerRep k) (fun g _ hf ↦ hf.slash_detPowerRep g k)
      (isArithmetic_paramodular _) (cuspForms_le_modularForms _ _ _ hf) hg
      (isFundamentalDomain_fundamentalDomain (isArithmetic_paramodular _))

/-- **`S_k(K(N)) = S_k^old(K(N)) ⊕ S_k^new(K(N))` in scalar weight** (LMFDB `mf.siegel.newspace`,
`mf.siegel.newform`), for the Petersson inner product; the sum is direct
(`SiegelUpperHalfSpace.disjoint_paramodularOldSubspace_paramodularNewSubspace_scalar`). -/
lemma paramodularOldSubspace_sup_paramodularNewSubspace_scalar :
    paramodularOldSubspace (TauCeti.detPowerRep ℂ 2 k) N ⊔
      paramodularNewSubspace (TauCeti.detPowerRep ℂ 2 k) N (innerₛₗ ℂ).flip =
        paramodularCuspForms (TauCeti.detPowerRep ℂ 2 k) N :=
  have : FiniteDimensional ℂ (paramodularCuspForms (TauCeti.detPowerRep ℂ 2 k) N) :=
    finiteDimensional_cuspForms_detPowerRep (isArithmetic_paramodular _)
  paramodularOldSubspace_sup_paramodularNewSubspace_detPowerRep fun _ _ hf hg ↦
    integrableOn_peterssonIntegrand_of_isArithmetic isModerateForm_detPowerRep
      (isAdmissibleForm_detPowerRep k) (fun g _ hf ↦ hf.slash_detPowerRep g k)
      (isArithmetic_paramodular _) (cuspForms_le_modularForms _ _ _ hf) hg
      (isFundamentalDomain_fundamentalDomain (isArithmetic_paramodular _))

end SiegelUpperHalfSpace
