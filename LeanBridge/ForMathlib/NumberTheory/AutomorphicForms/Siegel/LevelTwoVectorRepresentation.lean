import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.LevelTwoSymmetricRepresentation

/-!
# The actions of `S₆` and `S₃` on the vector-valued Siegel modular forms of level 2

The slash operator `(f ∣_{k,j} g)(Ω) = ρ_{k,j}(CΩ + D)⁻¹ f(gΩ)` of weight
`ρ_{k,j} = det^k ⊗ Sym^j` by an element `g` of `Sp(4, ℝ)` preserves holomorphy on the Siegel upper
half-space of degree 2. For a linear form `φ` on `Sym^j(ℂ²)` and a pure tensor `v₁ ⋯ v_j`,
`φ(Sym^j(M)(v₁ ⋯ v_j)) = φ(Mv₁ ⋯ Mv_j)` is a polynomial in the entries of `M` (expand every `Mvᵢ`
in the standard basis), so `M ↦ φ(Sym^j(M) v)` is holomorphic for every `v`, since the pure
tensors span `Sym^j(ℂ²)`. The entries of `(CΩ + D)⁻¹` and `det(CΩ + D)^{-k}` are holomorphic in
`Ω`, and the coordinates of `f(gΩ)` in a basis of `Sym^j(ℂ²)` are holomorphic too. Hence the slash
operator of an element of `Sp(4, ℤ)` normalising a subgroup `H` maps `M_{k,j}(H)` and `S_{k,j}(H)`
to themselves.

This gives the actions of the knowl `mf.siegel.family.gamma_2` on the vector-valued forms. The
principal congruence subgroup `Γ[2]` is normal in `Sp(4, ℤ)`, so `Sp(4, ℤ)/Γ[2] ≅ S₆` acts on
`M_{k,j}(Γ[2])` by `f ↦ f ∣_{k,j} g⁻¹`, with `S_{k,j}(Γ[2])` a subrepresentation; and `Γ₁[2]` is
normal in `Γ₀[2]`, so `Γ₀[2]/Γ₁[2] ≅ S₃` acts on `M_{k,j}(Γ₁[2])`. The isotypic multiplicities
are defined in `LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.LevelTwoIsotypic`; the
Eisenstein subspaces `E_{k,j}(Γ[2])` are not formalised.

## Main definitions

* `SiegelUpperHalfSpace.normalizerSlashRep`: the representation `g ↦ (f ↦ f ∣_{k,j} ι(g)⁻¹)` on
  `M_{k,j}(H)` of a group mapped by `ι` into the normaliser of `H` in `Sp(4, ℤ)`.
* `SiegelUpperHalfSpace.levelTwoVectorRep`: the representation of `Sp(4, ℤ)/Γ[2]` on
  `M_{k,j}(Γ[2])`.
* `SiegelUpperHalfSpace.levelTwoVectorSymmetricRep`: the representation of `S₆` on
  `M_{k,j}(Γ[2])`.
* `SiegelUpperHalfSpace.gammaOneVectorRep`: the representation of `Γ₀[2]/Γ₁[2]` on
  `M_{k,j}(Γ₁[2])`.
* `SiegelUpperHalfSpace.gammaOneVectorSymmetricRep`: the representation of `S₃` on
  `M_{k,j}(Γ₁[2])`.

## Main results

* `SiegelUpperHalfSpace.IsHolomorphic.slash_rhoKJ`: the slash operator of weight `ρ_{k,j}` by an
  element of `Sp(4, ℝ)` preserves holomorphy.
* `SiegelUpperHalfSpace.slash_mem_modularFormsKJ`: the slash operator of an element of `Sp(4, ℤ)`
  normalising `H` maps `M_{k,j}(H)` to itself.
* `SiegelUpperHalfSpace.slash_mem_cuspFormsKJ`: the same for `S_{k,j}(H)`.
* `SiegelUpperHalfSpace.levelTwoVectorSymmetricRep_mem_cuspFormsKJ`: `S_{k,j}(Γ[2])` is a
  subrepresentation of `M_{k,j}(Γ[2])` under `S₆`.
-/

open SymplecticGroup

open Matrix hiding mul_inv_rev

open scoped TensorProduct

namespace SiegelUpperHalfSpace

variable (k : ℤ) {j : ℕ} (φ : Module.Dual ℂ (Sym[ℂ]^j (Fin 2 → ℂ))) (v : Sym[ℂ]^j (Fin 2 → ℂ))
    (g : symplecticGroup (Fin 2) ℝ) {f : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)}
    {H : Subgroup (symplecticGroup (Fin 2) ℤ)} {γ : symplecticGroup (Fin 2) ℤ}

lemma dual_tprod_mulVec (M : Matrix (Fin 2) (Fin 2) ℂ) (m : Fin j → Fin 2 → ℂ) :
    φ (⨂ₛ[ℂ] i, M *ᵥ m i) =
      ∑ r : Fin j → Fin 2, (∏ i, (M *ᵥ m i) (r i)) * φ (⨂ₛ[ℂ] i, Pi.single (r i) 1) := by
  rw [funext fun i ↦ pi_eq_sum_univ' (M *ᵥ m i), MultilinearMap.map_sum, map_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [MultilinearMap.map_smul_univ, map_smul, smul_eq_mul]

lemma differentiable_symmetricPower_map :
    Differentiable ℂ fun M : Fin 2 → Fin 2 → ℂ ↦ φ (SymmetricPower.map (mulVecLin (of M)) v) := by
  have hv : v ∈ Submodule.span ℂ (Set.range (SymmetricPower.tprod ℂ)) := by
    rw [SymmetricPower.span_tprod_eq_top]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨m, rfl⟩
    have e : (fun M : Fin 2 → Fin 2 → ℂ ↦ φ (SymmetricPower.map (mulVecLin (of M))
        (SymmetricPower.tprod ℂ m))) = fun M ↦ ∑ r : Fin j → Fin 2,
          (∏ i, ∑ a, M (r i) a * m i a) * φ (⨂ₛ[ℂ] i, Pi.single (r i) 1) := funext fun M ↦ by
      rw [SymmetricPower.map_tprod]
      simp only [mulVecLin_apply]
      rw [dual_tprod_mulVec]
      rfl
    rw [e]
    fun_prop
  | zero => simp
  | add x y _ _ hx hy =>
    simpa only [map_add] using hx.fun_add hy
  | smul a x _ hx =>
    simpa only [map_smul, smul_eq_mul] using hx.const_mul a

lemma isHolomorphic_symPowerRep_denomGL_inv :
    IsHolomorphic fun τ ↦ φ (TauCeti.symPowerRep ℂ 2 j (denomGL g τ)⁻¹ v) := by
  rw [isHolomorphic_iff_differentiableOn]
  refine ((differentiable_symmetricPower_map φ v).comp_differentiableOn
    (differentiableOn_pi.mpr fun a ↦ differentiableOn_pi.mpr fun b ↦ differentiableOn_inv_apply a b
      (differentiableOn_denom_apply g) fun Z hZ ↦
        (isUnit_det_denom g ⟨symmetrize Z, transpose_symmetrize Z, hZ⟩).ne_zero)).congr
          fun Z hZ ↦ ?_
  rw [extend_of_mem _ hZ, Function.comp_apply, Representation.symmetricPower_apply,
    TauCeti.stdRep_apply, coe_units_inv, coe_denomGL]
  rfl

lemma isHolomorphic_iff_comp {V : Type*} [AddCommGroup V] [Module ℂ V]
    {F : SiegelUpperHalfSpace (Fin 2) → V} :
    IsHolomorphic F ↔ ∀ φ : Module.Dual ℂ V, IsHolomorphic (φ ∘ F) :=
  ⟨fun hF φ ψ ↦ hF (ψ ∘ₗ φ), fun hF φ ↦ hF φ LinearMap.id⟩

/-- **The slash operator of weight `ρ_{k,j}` preserves holomorphy**: if `f : ℋ₂ → Sym^j(ℂ²)` is
holomorphic, so is `f ∣_{k,j} g = ρ_{k,j}(CΩ + D)⁻¹ f(gΩ)` for `g ∈ Sp(4, ℝ)`. In a basis `(bᵢ)` of
`Sym^j(ℂ²)`, `φ(f ∣_{k,j} g)` is `det(CΩ + D)^{-k} Σᵢ fᵢ(gΩ) φ(Sym^j((CΩ + D)⁻¹) bᵢ)`, where the
coordinates `fᵢ` of `f` are holomorphic and the matrix coefficients of `Sym^j` are polynomials. -/
lemma IsHolomorphic.slash_rhoKJ (hf : IsHolomorphic f) : IsHolomorphic (slash (rhoKJ k j) g f) := by
  refine isHolomorphic_iff_comp.mpr fun φ ↦ ?_
  let b : Module.Basis (Fin (Module.finrank ℂ (Sym[ℂ]^j (Fin 2 → ℂ)))) ℂ (Sym[ℂ]^j (Fin 2 → ℂ)) :=
    Module.finBasis ℂ _
  have e : φ ∘ slash (rhoKJ k j) g f = (fun τ ↦ (denom g τ.val).det ^ (-k)) *
      ∑ i, (fun τ ↦ b.coord i (f (g • τ))) *
        fun τ ↦ φ (TauCeti.symPowerRep ℂ 2 j (denomGL g τ)⁻¹ (b i)) := by
    ext τ
    rw [Function.comp_apply, slash_apply, Pi.mul_apply, Finset.sum_apply, Finset.mul_sum]
    conv_lhs => rw [← b.sum_repr (f (g • τ))]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [rhoKJ, mul_left_comm]
  rw [e]
  exact (isHolomorphic_det_denom_zpow g (-k)).mul <| Finset.sum_induction _ IsHolomorphic
    (fun _ _ ↦ IsHolomorphic.add) isHolomorphic_zero fun i _ ↦
      ((isHolomorphic_iff_comp.mp hf (b.coord i)).comp_smul g).mul
        (isHolomorphic_symPowerRep_denomGL_inv φ (b i) g)

lemma mem_modularFormsKJ_of_slash_eq (hf : IsHolomorphic f)
    (h : ∀ δ ∈ H, slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) δ) f = f) :
    f ∈ modularFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) := by
  have hle : H ≤ slashCharStabilizer (rhoKJ k j) f H 1 := fun δ hδ ↦ ⟨hδ, by
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact h δ hδ⟩
  simpa using mem_modularForms_map_of_le_slashCharStabilizer _ _ _ 1 hf hle

/-- **The slash operator of an element normalising `H` preserves `M_{k,j}(H)`**: if `γ ∈ Sp(4, ℤ)`
normalises a subgroup `H`, then `f ∣_{k,j} γ ∈ M_{k,j}(H)` for every `f ∈ M_{k,j}(H)`, since the
slash operator preserves holomorphy and `f ∣ γδ = f ∣ (γδγ⁻¹)γ = f ∣ γ` for `δ ∈ H`. -/
lemma slash_mem_modularFormsKJ
    (hf : f ∈ modularFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ))))
    (hγ : γ ∈ Subgroup.normalizer (H : Set (symplecticGroup (Fin 2) ℤ))) :
    slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) γ) f ∈
      modularFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) :=
  mem_modularFormsKJ_of_slash_eq k (hf.1.slash_rhoKJ k _) fun δ hδ ↦ by
    rw [← slash_mul, ← map_mul, ← inv_mul_cancel_right (γ * δ) γ, map_mul _ (γ * δ * γ⁻¹) γ,
      slash_mul, mem_intSlashInvariants_of_mem_modularForms _ _ hf _
        ((Subgroup.mem_normalizer_iff.mp hγ δ).mp hδ)]

/-- **The slash operator of an element normalising `H` preserves `S_{k,j}(H)`** (LMFDB
`mf.siegel.family.gamma_2`): the Siegel operator vanishes on `(f ∣ γ) ∣ δ = f ∣ γδ` for every
`δ ∈ Sp(4, ℚ)` when `f` is a cusp form. -/
lemma slash_mem_cuspFormsKJ
    (hf : f ∈ cuspFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ))))
    (hγ : γ ∈ Subgroup.normalizer (H : Set (symplecticGroup (Fin 2) ℤ))) :
    slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) γ) f ∈
      cuspFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) :=
  ⟨slash_mem_modularFormsKJ k hf.1 hγ, fun δ ↦ by
    rw [← slash_mul, ← map_algebraMap_map_intCast γ, ← map_mul]
    exact hf.2 _⟩

variable (j) {G : Type*} [Group G] (ι : G →* symplecticGroup (Fin 2) ℤ) in
/-- The **representation `g ↦ (f ↦ f ∣_{k,j} ι(g)⁻¹)`** on `M_{k,j}(H)` of a group `G` mapped by
`ι` into the normaliser of `H` in `Sp(4, ℤ)` (LMFDB `mf.siegel.family.gamma_2`), a representation
since the slash operator is a right action. -/
noncomputable def normalizerSlashRep
    (hι : ∀ x, ι x ∈ Subgroup.normalizer (H : Set (symplecticGroup (Fin 2) ℤ))) :
    Representation ℂ G (modularFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))) where
  toFun δ :=
    { toFun F := ⟨slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) (ι δ⁻¹)) F,
        slash_mem_modularFormsKJ k F.2 (hι δ⁻¹)⟩
      map_add' F F' := Subtype.ext <| slash_add (rhoKJ k j) _ F F'
      map_smul' c F := Subtype.ext <| slash_smul (rhoKJ k j) _ F c }
  map_one' := LinearMap.ext fun F ↦ Subtype.ext <| by
    simp only [inv_one, map_one]
    exact slash_one (rhoKJ k j) F
  map_mul' δ ε := LinearMap.ext fun F ↦ Subtype.ext <| by
    simp only [mul_inv_rev, map_mul]
    exact slash_mul (rhoKJ k j) _ _ F

lemma mem_normalizer_Gamma_two :
    γ ∈ Subgroup.normalizer (Gamma (Fin 2) 2 : Set (symplecticGroup (Fin 2) ℤ)) :=
  (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge (Subgroup.mem_top γ)

variable (j) in
/-- The **representation of `Sp(4, ℤ)/Γ[2]` on `M_{k,j}(Γ[2])`** (LMFDB `mf.siegel.family.gamma_2`)
by `g ↦ (f ↦ f ∣_{k,j} g⁻¹)`, on the vector-valued Siegel modular forms of weight `ρ_{k,j}` on the
principal congruence subgroup `Γ[2]`, which is normal in `Sp(4, ℤ)` and acts trivially. -/
noncomputable def levelTwoVectorRep : Representation ℂ (symplecticGroup (Fin 2) ℤ ⧸ Gamma (Fin 2) 2)
    (modularFormsKJ k j IgusaLevelTwo.principal) :=
  QuotientGroup.lift (Gamma (Fin 2) 2) (normalizerSlashRep k j (MonoidHom.id _) fun _ ↦
    mem_normalizer_Gamma_two) fun δ hδ ↦ LinearMap.ext fun F ↦ Subtype.ext <|
      mem_intSlashInvariants_of_mem_modularForms _ _ F.2 δ⁻¹ (inv_mem hδ)

lemma levelTwoVectorRep_mk_apply (F : modularFormsKJ k j IgusaLevelTwo.principal) :
    (levelTwoVectorRep k j γ F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) =
      slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) γ⁻¹) F :=
  rfl

variable (j) in
/-- The **representation of `S₆` on `M_{k,j}(Γ[2])`** (LMFDB `mf.siegel.family.gamma_2`): the
action `f ↦ f ∣_{k,j} γ⁻¹` of `Sp(4, ℤ)/Γ[2]` on the vector-valued Siegel modular forms of weight
`ρ_{k,j}` on `Γ[2]`, transported through `Sp(4, ℤ)/Γ[2] ≅ S₆`, the action on the six odd theta
characteristics numbered by `Fin 6`. For `j = 0` it is `levelTwoSymmetricRep` up to the
identification of `ρ_{k,0}` with `det^k`. -/
noncomputable def levelTwoVectorSymmetricRep :
    Representation ℂ (Equiv.Perm (Fin 6)) (modularFormsKJ k j IgusaLevelTwo.principal) :=
  (levelTwoVectorRep k j).comp quotientGammaTwoEquivPerm.symm.toMonoidHom

/-- **`S_{k,j}(Γ[2])` is a subrepresentation of `M_{k,j}(Γ[2])` under `S₆`** (LMFDB
`mf.siegel.family.gamma_2`): the action of `S₆ ≅ Sp(4, ℤ)/Γ[2]` maps cusp forms to cusp forms. -/
lemma levelTwoVectorSymmetricRep_mem_cuspFormsKJ (σ : Equiv.Perm (Fin 6))
    {F : modularFormsKJ k j IgusaLevelTwo.principal}
    (hF : (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      cuspFormsKJ k j IgusaLevelTwo.principal) :
    (levelTwoVectorSymmetricRep k j σ F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      cuspFormsKJ k j IgusaLevelTwo.principal := by
  rcases QuotientGroup.mk_surjective (quotientGammaTwoEquivPerm.symm σ) with ⟨δ, hδ⟩
  rw [levelTwoVectorSymmetricRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hδ]
  exact slash_mem_cuspFormsKJ k hF mem_normalizer_Gamma_two

variable (j) in
/-- The **representation of `Γ₀[2]/Γ₁[2]` on `M_{k,j}(Γ₁[2])`** (LMFDB `mf.siegel.family.gamma_2`)
by `g ↦ (f ↦ f ∣_{k,j} g⁻¹)`, on the vector-valued Siegel modular forms of weight `ρ_{k,j}` on
`Γ₁[2]`, which is normal in `Γ₀[2]` and acts trivially. -/
noncomputable def gammaOneVectorRep :
    Representation ℂ (Gamma0 (Fin 2) 2 ⧸ (Gamma1 (Fin 2) 2).subgroupOf (Gamma0 (Fin 2) 2))
      (modularFormsKJ k j ((Gamma1 (Fin 2) 2).map (SymplecticGroup.map (Int.castRingHom ℚ)))) :=
  QuotientGroup.lift _ (normalizerSlashRep k j (Gamma0 (Fin 2) 2).subtype fun x ↦
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Gamma1_le_Gamma0 2)).mp inferInstance x.2)
      fun _ hδ ↦ LinearMap.ext fun F ↦ Subtype.ext <| mem_intSlashInvariants_of_mem_modularForms _ _
        F.2 _ (inv_mem (Subgroup.mem_subgroupOf.mp hδ))

variable (j) in
/-- The **representation of `S₃` on `M_{k,j}(Γ₁[2])`** (LMFDB `mf.siegel.family.gamma_2`): the
action of `Γ₀[2]/Γ₁[2]` on the vector-valued Siegel modular forms of weight `ρ_{k,j}` on `Γ₁[2]`,
transported through `Γ₀[2]/Γ₁[2] ≅ GL(2, ℤ/2ℤ) ≅ S₃`, the action on the three nonzero vectors of
`(ℤ/2ℤ)²` numbered by `Fin 3`. -/
noncomputable def gammaOneVectorSymmetricRep : Representation ℂ (Equiv.Perm (Fin 3))
    (modularFormsKJ k j ((Gamma1 (Fin 2) 2).map (SymplecticGroup.map (Int.castRingHom ℚ)))) :=
  (gammaOneVectorRep k j).comp quotientGammaOneGamma0EquivPerm.symm.toMonoidHom

end SiegelUpperHalfSpace
