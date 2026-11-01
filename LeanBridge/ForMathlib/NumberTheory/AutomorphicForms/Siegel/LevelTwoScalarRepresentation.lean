import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.IgusaLevelTwoModularity

/-!
# The action of `Sp(4, ℤ)/Γ[2]` on the scalar-valued forms on `Γ[2]`

The slash operator `f ↦ f ∣_k g`, `(f ∣_k g)(Ω) = det(CΩ + D)^{-k} f(gΩ)`, of weight `k` by an
element `g` of `Sp(4, ℝ)` preserves holomorphy on the Siegel upper half-space of degree 2: the
entries of `gΩ = (AΩ + B)(CΩ + D)⁻¹` are rational functions of the entries of `Ω` whose
denominator `det(CΩ + D)` does not vanish on `ℋ₂`, and `gΩ` lies in `ℋ₂`. Hence the slash operator
of `g ∈ Sp(4, ℤ)` maps `M_k(Γ[2])` to itself, since `Γ[2]` is normal in `Sp(4, ℤ)`, and
`g ↦ (f ↦ f ∣_k g⁻¹)` is a representation of `Sp(4, ℤ)/Γ[2]` on `M_k(Γ[2])`: the action of the
knowl `mf.siegel.family.gamma_2` on the scalar-valued forms, the case `j = 0` of `M_{k,j}(Γ[2])`.
It is a subrepresentation of `SiegelUpperHalfSpace.quotientSlashRep` for the weight `det^k`. In
weight 2 the fourth powers `θ_m⁴` of the theta constants, among them Igusa's generators `xᵢ`, span
a subrepresentation, since `Sp(4, ℤ)` permutes them up to constants. The knowl identifies
`Sp(4, ℤ)/Γ[2]` with the symmetric group `S₆`, which is not formalised here, nor is the holomorphy
of the slash operator for the vector-valued weights `ρ_{k,j}`, `j > 0`.

## Main definitions

* `SiegelUpperHalfSpace.levelTwoScalarRep` (LMFDB `mf.siegel.family.gamma_2`): the representation
  `g ↦ (f ↦ f ∣_k g⁻¹)` of `Sp(4, ℤ)/Γ[2]` on `M_k(Γ[2])`.
* `SiegelUpperHalfSpace.thetaFourthSpan`: the subspace of `M₂(Γ[2])` spanned by the `θ_m⁴`.

## Main results

* `SiegelUpperHalfSpace.IsHolomorphic.comp_smul`: `Ω ↦ f(gΩ)` is holomorphic for holomorphic
  `f : ℋ₂ → ℂ` and `g ∈ Sp(4, ℝ)`.
* `SiegelUpperHalfSpace.IsHolomorphic.slash_detPowerRep`: the slash operator of weight `k` by
  `g ∈ Sp(4, ℝ)` preserves holomorphy.
* `SiegelUpperHalfSpace.slash_mem_scalarModularForms_principal`: the slash operator of
  `g ∈ Sp(4, ℤ)` maps `M_k(Γ[2])` to itself.
* `SiegelUpperHalfSpace.coe_levelTwoScalarRep_apply`: the action on `M_k(Γ[2])` is the restriction
  of `SiegelUpperHalfSpace.quotientSlashRep`.
* `SiegelUpperHalfSpace.levelTwoScalarRep_mem_thetaFourthSpan`: the span of the `θ_m⁴` is a
  subrepresentation of `M₂(Γ[2])`.
-/

open Complex Matrix

namespace SiegelUpperHalfSpace

open IgusaLevelTwo

variable {s : Set (Fin 2 → Fin 2 → ℂ)} {P Q : (Fin 2 → Fin 2 → ℂ) → Matrix (Fin 2) (Fin 2) ℂ}
    {f : SiegelUpperHalfSpace (Fin 2) → ℂ} (g : symplecticGroup (Fin 2) ℝ) {k : ℤ}
    (γ : symplecticGroup (Fin 2) ℤ) (i j : Fin 2)
    (q : symplecticGroup (Fin 2) ℤ ⧸ SymplecticGroup.Gamma (Fin 2) 2)
    (F : scalarModularForms k principal)

lemma differentiableOn_mul_apply (hP : ∀ i j, DifferentiableOn ℂ (fun Z ↦ P Z i j) s)
    (hQ : ∀ i j, DifferentiableOn ℂ (fun Z ↦ Q Z i j) s) :
    DifferentiableOn ℂ (fun Z ↦ (P Z * Q Z) i j) s := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hP i 0).mul (hQ 0 j)).add ((hP i 1).mul (hQ 1 j))

lemma differentiableOn_det (hQ : ∀ i j, DifferentiableOn ℂ (fun Z ↦ Q Z i j) s) :
    DifferentiableOn ℂ (fun Z ↦ (Q Z).det) s := by
  simp only [det_fin_two]
  exact ((hQ 0 0).mul (hQ 1 1)).sub ((hQ 0 1).mul (hQ 1 0))

lemma differentiableOn_inv_apply (hQ : ∀ i j, DifferentiableOn ℂ (fun Z ↦ Q Z i j) s)
    (hdet : ∀ Z ∈ s, (Q Z).det ≠ 0) : DifferentiableOn ℂ (fun Z ↦ (Q Z)⁻¹ i j) s := by
  have e (Z : Fin 2 → Fin 2 → ℂ) :
      (Q Z)⁻¹ i j = ((Q Z).det)⁻¹ * !![Q Z 1 1, -Q Z 0 1; -Q Z 1 0, Q Z 0 0] i j := by
    rw [Matrix.inv_def, adjugate_fin_two, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  refine DifferentiableOn.congr (((differentiableOn_det hQ).inv hdet).mul ?_) fun Z _ ↦ e Z
  fin_cases i <;> fin_cases j <;> simp [hQ]

lemma differentiableOn_symmetrize_apply :
    DifferentiableOn ℂ (fun Z : Fin 2 → Fin 2 → ℂ ↦ symmetrize Z i j) s := by
  have h : Differentiable ℂ fun Z : Fin 2 → Fin 2 → ℂ ↦ (2⁻¹ : ℂ) * (Z i j + Z j i) := by
    fun_prop
  refine h.differentiableOn.congr fun Z _ ↦ ?_
  rw [symmetrize, Matrix.smul_apply, Matrix.add_apply, transpose_apply, of_apply, of_apply,
    smul_eq_mul]

lemma differentiableOn_num_apply :
    DifferentiableOn ℂ (fun Z : Fin 2 → Fin 2 → ℂ ↦ num g (symmetrize Z) i j) s :=
  (differentiableOn_mul_apply i j
    (P := fun _ ↦ (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ).toBlocks₁₁.map ofReal)
    (Q := symmetrize) (fun _ _ ↦ differentiableOn_const _)
      differentiableOn_symmetrize_apply).add (differentiableOn_const _)

lemma differentiableOn_denom_apply :
    DifferentiableOn ℂ (fun Z : Fin 2 → Fin 2 → ℂ ↦ denom g (symmetrize Z) i j) s :=
  (differentiableOn_mul_apply i j
    (P := fun _ ↦ (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ).toBlocks₂₁.map ofReal)
    (Q := symmetrize) (fun _ _ ↦ differentiableOn_const _)
      differentiableOn_symmetrize_apply).add (differentiableOn_const _)

lemma symmetrize_of_transpose_eq {M : Matrix (Fin 2) (Fin 2) ℂ} (h : Mᵀ = M) :
    symmetrize M = M := by
  have e : symmetrize M = (2⁻¹ : ℂ) • (M + Mᵀ) := rfl
  rw [e, h, ← two_smul ℂ M, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- **Composition with the action of `Sp(4, ℝ)` preserves holomorphy**: if `f : ℋ₂ → ℂ` is
holomorphic, so is `Ω ↦ f(gΩ)` for `g ∈ Sp(4, ℝ)`. The entries of `gΩ = (AΩ + B)(CΩ + D)⁻¹` are
complex differentiable in the entries of `Ω` where `det(CΩ + D) ≠ 0`, which holds on `ℋ₂`. -/
lemma IsHolomorphic.comp_smul (hf : IsHolomorphic f) : IsHolomorphic fun τ ↦ f (g • τ) := by
  rw [isHolomorphic_iff_differentiableOn] at hf ⊢
  have hmem (Z : Fin 2 → Fin 2 → ℂ) (hZ : Z ∈ symmetrizePreimage (Fin 2)) :
      symmetrize (num g (symmetrize Z) * (denom g (symmetrize Z))⁻¹) =
        (g • (⟨symmetrize Z, transpose_symmetrize Z, hZ⟩ : SiegelUpperHalfSpace (Fin 2))).val :=
    symmetrize_of_transpose_eq (g • (⟨symmetrize Z, transpose_symmetrize Z, hZ⟩ :
      SiegelUpperHalfSpace (Fin 2))).transpose_val
  have hmaps : Set.MapsTo (fun Z : Fin 2 → Fin 2 → ℂ ↦
      ((num g (symmetrize Z) * (denom g (symmetrize Z))⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) :
        Fin 2 → Fin 2 → ℂ)) (symmetrizePreimage (Fin 2)) (symmetrizePreimage (Fin 2)) :=
    fun Z hZ ↦ (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ (M.map im).PosDef) (hmem Z hZ)).mpr
      (g • (⟨symmetrize Z, transpose_symmetrize Z, hZ⟩ : SiegelUpperHalfSpace (Fin 2))).posDef_im
  refine (hf.comp (differentiableOn_pi.mpr fun i ↦ differentiableOn_pi.mpr fun j ↦
    differentiableOn_mul_apply i j (differentiableOn_num_apply g) fun i j ↦
      differentiableOn_inv_apply i j (differentiableOn_denom_apply g) fun Z hZ ↦
        (isUnit_det_denom g ⟨symmetrize Z, transpose_symmetrize Z, hZ⟩).ne_zero)
          hmaps).congr fun Z hZ ↦ ?_
  exact (extend_of_mem _ hZ).trans ((congrArg f (SiegelUpperHalfSpace.ext (hmem Z hZ).symm)).trans
    (extend_of_mem _ (hmaps hZ)).symm)

lemma isHolomorphic_det_denom_zpow (m : ℤ) : IsHolomorphic fun τ ↦ (denom g τ.val).det ^ m := by
  rw [isHolomorphic_iff_differentiableOn]
  exact ((differentiableOn_det (differentiableOn_denom_apply g)).zpow (m := m) (Or.inl fun Z hZ ↦
    (isUnit_det_denom g ⟨symmetrize Z, transpose_symmetrize Z, hZ⟩).ne_zero)).congr fun Z hZ ↦
      extend_of_mem _ hZ

variable (k) in
lemma slash_detPowerRep_apply (τ : SiegelUpperHalfSpace (Fin 2)) :
    slash (TauCeti.detPowerRep ℂ 2 k) g f τ = (denom g τ.val).det ^ (-k) * f (g • τ) := by
  rw [slash_apply, TauCeti.detPowerRep_apply, map_inv, Units.val_zpow_eq_zpow_val,
    Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply, coe_denomGL,
    inv_zpow' (denom g τ.val).det]

variable (k) in
/-- **The slash operator of weight `k` preserves holomorphy**: if `f : ℋ₂ → ℂ` is holomorphic, so
is `f ∣_k g = det(CΩ + D)^{-k} f(gΩ)` for `g ∈ Sp(4, ℝ)`. -/
lemma IsHolomorphic.slash_detPowerRep (hf : IsHolomorphic f) :
    IsHolomorphic (slash (TauCeti.detPowerRep ℂ 2 k) g f) := by
  rw [show slash (TauCeti.detPowerRep ℂ 2 k) g f =
    (fun τ ↦ (denom g τ.val).det ^ (-k)) * fun τ ↦ f (g • τ) from
      funext (slash_detPowerRep_apply g k)]
  exact (isHolomorphic_det_denom_zpow g (-k)).mul (hf.comp_smul g)

/-- **The slash operator of `Sp(4, ℤ)` preserves `M_k(Γ[2])`** (LMFDB `mf.siegel.family.gamma_2`):
`f ∣_k γ ∈ M_k(Γ[2])` for `f ∈ M_k(Γ[2])` and `γ ∈ Sp(4, ℤ)`, since the slash operator preserves
holomorphy and `Γ[2]` is normal in `Sp(4, ℤ)`. -/
lemma slash_mem_scalarModularForms_principal (hf : f ∈ scalarModularForms k principal) :
    slash (TauCeti.detPowerRep ℂ 2 k) (SymplecticGroup.map (Int.castRingHom ℝ) γ) f ∈
      scalarModularForms k principal :=
  mem_scalarModularForms_of_slash_eq (hf.1.slash_detPowerRep _ k) fun δ hδ ↦
    slash_mem_intSlashInvariants (mem_intSlashInvariants_of_mem_modularForms _ _ hf) γ δ hδ

variable (k) in
/-- The **representation of `Sp(4, ℤ)/Γ[2]` on `M_k(Γ[2])`** (LMFDB `mf.siegel.family.gamma_2`),
by `g ↦ (f ↦ f ∣_k g⁻¹)`, on the scalar-valued Siegel modular forms of weight `k` on the principal
congruence subgroup `Γ[2]`, on which `Γ[2]` acts trivially. The knowl identifies `Sp(4, ℤ)/Γ[2]`
with the symmetric group `S₆`, which is not formalised. -/
noncomputable def levelTwoScalarRep : Representation ℂ
    (symplecticGroup (Fin 2) ℤ ⧸ SymplecticGroup.Gamma (Fin 2) 2)
      (scalarModularForms k principal) :=
  QuotientGroup.lift (SymplecticGroup.Gamma (Fin 2) 2)
    { toFun δ :=
        { toFun F := ⟨slash (TauCeti.detPowerRep ℂ 2 k) (SymplecticGroup.map (Int.castRingHom ℝ)
            δ⁻¹) F, slash_mem_scalarModularForms_principal δ⁻¹ F.2⟩
          map_add' F F' := Subtype.ext <| slash_add (TauCeti.detPowerRep ℂ 2 k) _ F F'
          map_smul' c F := Subtype.ext <| slash_smul (TauCeti.detPowerRep ℂ 2 k) _ F c }
      map_one' := LinearMap.ext fun F ↦ Subtype.ext <| by
        simp only [inv_one, map_one]
        exact slash_one (TauCeti.detPowerRep ℂ 2 k) F
      map_mul' δ ε := LinearMap.ext fun F ↦ Subtype.ext <| by
        simp only [mul_inv_rev δ ε, map_mul]
        exact slash_mul (TauCeti.detPowerRep ℂ 2 k) _ _ F }
    fun δ hδ ↦ LinearMap.ext fun F ↦ Subtype.ext <|
      mem_intSlashInvariants_of_mem_modularForms _ _ F.2 δ⁻¹ (inv_mem hδ)

lemma levelTwoScalarRep_mk_apply :
    (levelTwoScalarRep k γ F : SiegelUpperHalfSpace (Fin 2) → ℂ) =
      slash (TauCeti.detPowerRep ℂ 2 k) (SymplecticGroup.map (Int.castRingHom ℝ) γ⁻¹) F :=
  rfl

/-- **`M_k(Γ[2])` is a subrepresentation of the `Γ[2]`-invariant functions**: the action of
`Sp(4, ℤ)/Γ[2]` on `M_k(Γ[2])` is the restriction of its action `quotientSlashRep` on the functions
invariant under the slash operator of weight `k` of `Γ[2]`, which contain `M_k(Γ[2])`. -/
lemma coe_levelTwoScalarRep_apply :
    (levelTwoScalarRep k q F : SiegelUpperHalfSpace (Fin 2) → ℂ) =
      quotientSlashRep (TauCeti.detPowerRep ℂ 2 k) (SymplecticGroup.Gamma (Fin 2) 2) q
        ⟨F, mem_intSlashInvariants_of_mem_modularForms _ _ F.2⟩ :=
  QuotientGroup.induction_on q fun _ ↦ rfl

/-- The subspace of `M₂(Γ[2])` **spanned by the fourth powers of the theta constants** (LMFDB
`mf.siegel.family.gamma_2`), which contains Igusa's generators `xᵢ = ϑᵢ⁴`. -/
noncomputable def thetaFourthSpan : Submodule ℂ (scalarModularForms 2 principal) :=
  Submodule.span ℂ (Set.range fun m : (Fin 2 → ℤ) × (Fin 2 → ℤ) ↦
    ⟨thetaConstant m.1 m.2 ^ 4, thetaConstant_pow_four_mem_scalarModularForms m.1 m.2⟩)

/-- **The span of the fourth powers of the theta constants is a subrepresentation** of the
representation of `Sp(4, ℤ)/Γ[2]` on `M₂(Γ[2])` (LMFDB `mf.siegel.family.gamma_2`): `Sp(4, ℤ)`
permutes the `θ_m⁴` up to constants. -/
lemma levelTwoScalarRep_mem_thetaFourthSpan {G : scalarModularForms 2 principal}
    (hG : G ∈ thetaFourthSpan) : levelTwoScalarRep 2 q G ∈ thetaFourthSpan := by
  induction q using QuotientGroup.induction_on with
  | H δ =>
    induction hG using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨m, rfl⟩
      rcases exists_slash_thetaConstant_pow_four_eq_smul m.1 m.2 δ⁻¹ with ⟨c, μ, ν, e⟩
      have h : levelTwoScalarRep 2 δ ⟨thetaConstant m.1 m.2 ^ 4,
          thetaConstant_pow_four_mem_scalarModularForms m.1 m.2⟩ =
            c • ⟨thetaConstant μ ν ^ 4, thetaConstant_pow_four_mem_scalarModularForms μ ν⟩ :=
        Subtype.ext e
      rw [h]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨(μ, ν), rfl⟩)
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ a hx

end SiegelUpperHalfSpace
