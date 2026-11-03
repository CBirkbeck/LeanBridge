import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ArithmeticFiniteDimensional
import TauCeti.NumberTheory.ModularForms.SturmBound

/-!
# Modular forms of degree 2 and weight `ρ_{k,j}` on an arithmetic subgroup are finite-dimensional

Let `H` be a normal subgroup of finite index of `Sp(4, ℤ)` and `F ∈ M_{k,j}(H)`. The coordinates
`T_r` of `Sym^j(ℂ²)`, for `r : Fin j → Fin 2`, diagonalise `ρ_{k,j}(diag(w, 1))`, with eigenvalue
`w^{k + w(r)}`, for `w(r)` the number of `i` with `r i = 0`. So the limit
`u_r(τ') = lim_{t → ∞} T_r(F(diag(τ', it)))` is a modular form of weight `k + w(r)` on the preimage
of `H` in `SL(2, ℤ)`: the embedding of `SL(2, ℤ)` in `Sp(4, ℤ)` acts on `diag(τ', it)` through `τ'`,
its automorphy factor is `diag(cτ' + d, 1)`, and `u_r ∣ g` is the limit attached to `F ∣ g`, which
lies in `M_{k,j}(H)`, so that `u_r` is bounded at every cusp. By the cusp criterion, the forms with
`u_r(F ∣ g) = 0` for all `r` and `g ∈ Sp(4, ℤ)` are the cusp forms, and these are
finite-dimensional. Hence so is `M_{k,j}(H)`, and so is `M_{k,j}(Γ)` for every arithmetic subgroup
`Γ`.

## Main definitions

* `SiegelUpperHalfSpace.siegelCoord`: the limit `u_r`.

## Main results

* `SiegelUpperHalfSpace.isCuspForm_of_forall_siegelOperatorVanishes_slash`: a form on the image of a
  normal subgroup of finite index of `Sp(4, ℤ)`, whose Siegel operator vanishes after every element
  of `Sp(4, ℤ)`, is a cusp form.
* `SiegelUpperHalfSpace.finiteDimensional_modularFormsKJ_map`: `M_{k,j}(H)` is finite-dimensional.
* `SiegelUpperHalfSpace.finiteDimensional_modularFormsKJ_of_isArithmetic`: `M_{k,j}(Γ)` is
  finite-dimensional, for every arithmetic subgroup `Γ`.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_mul zpow_neg one_zpow

open Filter Module SymplecticGroup Topology UpperHalfPlane

open scoped ComplexOrder Manifold MatrixGroups ModularForm TensorProduct

namespace SiegelUpperHalfSpace

variable {H : Subgroup (symplecticGroup (Fin 2) ℤ)} [H.Normal] [H.FiniteIndex]

/-- **The cusp criterion on an arithmetic subgroup**: a modular form on the image of a normal
subgroup `H` of finite index of `Sp(4, ℤ)`, with `Φ(F ∣ g) = 0` for every `g ∈ Sp(4, ℤ)`, is a cusp
form, if the slash operators preserve holomorphy. Writing `γ ∈ Sp(4, ℚ)` as `g p`, with
`g ∈ Sp(4, ℤ)` and `p` in the Siegel parabolic subgroup, `F ∣ γ = (F ∣ g) ∣ p`, where `F ∣ g` has
positive definite support. -/
lemma isCuspForm_of_forall_siegelOperatorVanishes_slash {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {ρ : Representation ℂ (GL (Fin 2) ℂ) V}
    {F : SiegelUpperHalfSpace (Fin 2) → V}
    (hρ : ∀ (g : symplecticGroup (Fin 2) ℝ) (f : SiegelUpperHalfSpace (Fin 2) → V),
      IsHolomorphic f → IsHolomorphic (slash ρ g f))
    (hF : F ∈ modularForms ρ (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) 1)
    (hv : ∀ g : symplecticGroup (Fin 2) ℤ,
      SiegelOperatorVanishes (slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) g) F)) :
    IsCuspForm ρ F := by
  intro γ
  rcases exists_mem_integral_inv_mul_mem_siegelParabolic γ with ⟨_, ⟨g, -, rfl⟩, hp⟩
  have hG : slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) g) F ∈
      modularForms ρ (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) 1 :=
    slash_mem_modularForms_map hρ hF g
  rcases exists_hasSiegelFourierExpansion ρ (isArithmetic_map H) hG with ⟨a, ha⟩
  have hpd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosDef :=
    posDef_of_forall_siegelOperatorVanishes_slash_levi (isArithmetic_map H) hG ha fun U ↦ by
      rw [← slash_mul, ← map_mul]
      exact hv _
  rw [← mul_inv_cancel_left (SymplecticGroup.map (Int.castRingHom ℚ) g) γ, map_mul, slash_mul,
    map_algebraMap_map_intCast]
  exact siegelOperatorVanishes_slash_of_posDef ρ (map_mem_siegelParabolic hp) ha hpd

/-! ### The coordinates of the Siegel operator -/

variable {k : ℤ} {j : ℕ} (r : Fin j → Fin 2)

/-- The limit `u_r(τ') = lim_{t → ∞} T_r(F(diag(τ', it)))` of a coordinate of `F`, for
`F : ℋ₂ → Sym^j(ℂ²)`. -/
noncomputable def siegelCoord (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) (τ' : ℍ) :
    ℂ :=
  limUnder atTop fun t : Set.Ioi (0 : ℝ) ↦ symCoord r (F (diagPoint τ' t))

variable (k) in
/-- The weight `k + w(r)` of the coordinate `r`, for `w(r)` the number of `i` with `r i = 0`. -/
private def coordWeight : ℤ :=
  k + (Finset.univ.filter fun i ↦ r i = 0).card

private lemma symCoord_rhoKJ_of_diag {A : GL (Fin 2) ℂ} {w : ℂ}
    (hA : (A : Matrix (Fin 2) (Fin 2) ℂ) = !![w, 0; 0, 1]) (hw : w ≠ 0) (v : Sym[ℂ]^j (Fin 2 → ℂ)) :
    symCoord r (rhoKJ k j A v) = w ^ coordWeight k r * symCoord r v := by
  have hdiag (a c : Fin 2) :
      (A : Matrix (Fin 2) (Fin 2) ℂ) a c = if a = c then (if a = 0 then w else 1) else 0 := by
    rw [hA]
    fin_cases a <;> fin_cases c <;> simp
  rw [rhoKJ_apply, map_smul, symCoord_symPowerRep, Finset.sum_eq_single r]
  · simp only [hdiag, Units.val_zpow_eq_zpow_val, GeneralLinearGroup.val_det_apply, hA, ite_true,
      coordWeight, zpow_add₀ hw]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one]
    simp [mul_assoc]
  · intro s _ hs
    rcases Function.ne_iff.mp hs with ⟨i, hi⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hdiag, ite_eq_right (Ne.symm hi)]),
      zero_mul]
  · simp

variable {K : Subgroup (symplecticGroup (Fin 2) ℚ)}
    {F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)} (τ' : ℍ)

private lemma tendsto_siegelCoord (hK : IsArithmetic K) (hF : F ∈ modularFormsKJ k j K) :
    Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ symCoord r (F (diagPoint τ' t))) atTop
      (𝓝 (siegelCoord r F τ')) := by
  rcases exists_hasSiegelFourierExpansion (rhoKJ k j) hK hF with ⟨a, ha⟩
  have h : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ symCoord r (F (diagPoint τ' t))) atTop _ :=
    tendsto_dual_diagPoint τ' (symCoord r) ha (koecherPrinciple (rhoKJ k j) hK (by simp) F hF a ha)
  rwa [siegelCoord, h.limUnder_eq]

private lemma siegelCoord_add (hK : IsArithmetic K)
    {G : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)} (hF : F ∈ modularFormsKJ k j K)
    (hG : G ∈ modularFormsKJ k j K) :
    siegelCoord r (F + G) τ' = siegelCoord r F τ' + siegelCoord r G τ' :=
  tendsto_nhds_unique (tendsto_siegelCoord r τ' hK (add_mem hF hG)) <| by
    simpa using (tendsto_siegelCoord r τ' hK hF).add (tendsto_siegelCoord r τ' hK hG)

private lemma siegelCoord_smul (hK : IsArithmetic K) (hF : F ∈ modularFormsKJ k j K) (c : ℂ) :
    siegelCoord r (c • F) τ' = c * siegelCoord r F τ' :=
  tendsto_nhds_unique (tendsto_siegelCoord r τ' hK (Submodule.smul_mem _ c hF)) <| by
    simpa using (tendsto_siegelCoord r τ' hK hF).const_mul c

private lemma mdifferentiable_siegelCoord (hK : IsArithmetic K) (hF : F ∈ modularFormsKJ k j K) :
    MDiff (siegelCoord r F) := by
  rcases exists_hasSiegelFourierExpansion (rhoKJ k j) hK hF with ⟨a, ha⟩
  have hpsd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef :=
    koecherPrinciple (rhoKJ k j) hK (by simp) F hF a ha
  have e (τ' : ℍ) : siegelCoord r F τ' = ∑' n, phiTerm (fun n ↦ symCoord r (a n)) τ' n :=
    (tendsto_dual_diagPoint τ' (symCoord r) ha hpsd).limUnder_eq
  refine UpperHalfPlane.mdifferentiable_iff.mpr fun z hz ↦ ?_
  refine ((differentiableAt_tsum_phiTerm (d := fun n ↦ symCoord r (a n))
    (fun τ ↦ (ha τ (symCoord r)).summable)
    (fun n hn ↦ hpsd n fun h ↦ hn (by rw [h, map_zero])) hz).differentiableWithinAt).congr
      (fun w hw ↦ ?_) ?_
  · simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    exact e _
  · simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    exact e _

private lemma isBoundedAtImInfty_siegelCoord (hK : IsArithmetic K) (hF : F ∈ modularFormsKJ k j K) :
    IsBoundedAtImInfty (siegelCoord r F) := by
  rcases exists_hasSiegelFourierExpansion (rhoKJ k j) hK hF with ⟨a, ha⟩
  have hpsd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef :=
    koecherPrinciple (rhoKJ k j) hK (by simp) F hF a ha
  have e : siegelCoord r F = fun τ' : ℍ ↦ ∑' n, phiTerm (fun n ↦ symCoord r (a n)) τ' n :=
    funext fun τ' ↦ (tendsto_dual_diagPoint τ' (symCoord r) ha hpsd).limUnder_eq
  rw [e]
  exact isBoundedAtImInfty_tsum_phiTerm (fun τ ↦ (ha τ (symCoord r)).summable)
    fun n hn ↦ hpsd n fun h ↦ hn (by rw [h, map_zero])

private lemma slash_siegelCoord
    (hF : F ∈ modularFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))) (g : SL(2, ℤ)) :
    siegelCoord r F ∣[coordWeight k r] g = siegelCoord r
      (slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) (embedFirst g)) F) := by
  ext τ'
  have hw : (g 1 0 : ℂ) * τ' + (g 1 1 : ℂ) ≠ 0 := by
    have h : UpperHalfPlane.denom (g : GL (Fin 2) ℝ) τ' ≠ 0 :=
      UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) τ'
    simpa [UpperHalfPlane.denom] using h
  have e : UpperHalfPlane.denom g τ' = (g 1 0 : ℂ) * τ' + (g 1 1 : ℂ) := by
    simp [UpperHalfPlane.denom]
  generalize hx : (g 1 0 : ℂ) * τ' + (g 1 1 : ℂ) = x at hw e
  have hA (t : Set.Ioi (0 : ℝ)) : (((denomGL (SymplecticGroup.map (Int.castRingHom ℝ)
      (embedFirst g)) (diagPoint τ' t))⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        !![x⁻¹, 0; 0, 1] := by
    rw [coe_units_inv, coe_denomGL_embedFirst, hx]
    refine inv_eq_right_inv ?_
    ext a c
    fin_cases a <;> fin_cases c <;> simp [hw]
  have h₁ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ x⁻¹ ^ coordWeight k r *
      symCoord r (F (diagPoint (g • τ') t))) atTop
        (𝓝 (x⁻¹ ^ coordWeight k r * siegelCoord r F (g • τ'))) :=
    (tendsto_siegelCoord r (g • τ') (isArithmetic_map H) hF).const_mul _
  have h₂ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ x⁻¹ ^ coordWeight k r *
      symCoord r (F (diagPoint (g • τ') t))) atTop (𝓝 (siegelCoord r
        (slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) (embedFirst g)) F) τ')) := by
    refine (tendsto_siegelCoord r τ' (isArithmetic_map H) (slash_mem_modularForms_map
      (fun g _ hf ↦ hf.slash_rhoKJ k g) hF _)).congr fun t ↦ ?_
    rw [slash_apply, symCoord_rhoKJ_of_diag r (hA t) (inv_ne_zero hw), smul_diagPoint_embedFirst]
  rw [ModularForm.SL_slash_apply, e, ← tendsto_nhds_unique h₁ h₂, inv_zpow', mul_comm]

/-- The limit `u_r`, as a modular form of weight `k + w(r)` on the preimage of `H` in `SL(2, ℤ)`. -/
private noncomputable def siegelCoordForm
    (hF : F ∈ modularFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))) :
    ModularForm ((H.comap (embedFirst (R := ℤ)) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
      (coordWeight k r) where
  toFun := siegelCoord r F
  slash_action_eq' := by
    rintro _ ⟨g, hg, rfl⟩
    have h : slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) (embedFirst g)) F = F :=
      mem_intSlashInvariants_of_mem_modularForms _ _ hF _ hg
    exact (slash_siegelCoord r hF g).trans (by rw [h])
  holo' := mdifferentiable_siegelCoord r (isArithmetic_map H) hF
  bdd_at_cusps' hc := (OnePoint.isBoundedAt_iff_forall_SL2Z (hc.mono
    (Subgroup.map_le_range _ _))).mpr fun g _ ↦ by
      rw [slash_siegelCoord r hF g]
      exact isBoundedAtImInfty_siegelCoord r (isArithmetic_map H) (slash_mem_modularForms_map
        (fun g _ hf ↦ hf.slash_rhoKJ k g) hF _)

variable (k j H) in
/-- The limits `u_r(F ∣ g)`, for the representatives `g` of `Sp(4, ℤ) / H`, as a linear map. -/
private noncomputable def siegelCoordMap :
    modularFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) →ₗ[ℂ]
      ((_ : symplecticGroup (Fin 2) ℤ ⧸ H) → (r : Fin j → Fin 2) →
        ModularForm ((H.comap (embedFirst (R := ℤ)) : Subgroup SL(2, ℤ)) :
          Subgroup (GL (Fin 2) ℝ)) (coordWeight k r)) where
  toFun F q r := siegelCoordForm r (slash_mem_modularForms_map
    (fun g _ hf ↦ hf.slash_rhoKJ k g) F.2 q.out)
  map_add' F G := by
    funext q r
    refine DFunLike.ext _ _ fun τ' ↦ ?_
    have e : slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) q.out)
        ((F + G : modularFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))) :
          SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) =
        slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) q.out) F +
          slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) q.out) G :=
      slash_add _ _ _ _
    exact (congrArg (siegelCoord r · τ') e).trans (siegelCoord_add r τ' (isArithmetic_map H)
      (slash_mem_modularForms_map (fun g _ hf ↦ hf.slash_rhoKJ k g) F.2 q.out)
      (slash_mem_modularForms_map (fun g _ hf ↦ hf.slash_rhoKJ k g) G.2 q.out))
  map_smul' c F := by
    funext q r
    refine DFunLike.ext _ _ fun τ' ↦ ?_
    have e : slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) q.out)
        ((c • F : modularFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))) :
          SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) =
        c • slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) q.out) F :=
      slash_smul _ _ _ _
    exact (congrArg (siegelCoord r · τ') e).trans (siegelCoord_smul r τ' (isArithmetic_map H)
      (slash_mem_modularForms_map (fun g _ hf ↦ hf.slash_rhoKJ k g) F.2 q.out) c)

private lemma tendsto_dual_of_forall_tendsto_symCoord {α : Type*} {l : Filter α}
    {v : α → Sym[ℂ]^j (Fin 2 → ℂ)} (h : ∀ r, Tendsto (fun x ↦ symCoord r (v x)) l (𝓝 0))
    (φ : Dual ℂ (Sym[ℂ]^j (Fin 2 → ℂ))) : Tendsto (fun x ↦ φ (v x)) l (𝓝 0) := by
  let ι : Sym[ℂ]^j (Fin 2 → ℂ) →ₗ[ℂ] (Fin j → Fin 2) → ℂ := LinearMap.pi symCoord
  have hι : LinearMap.ker ι = ⊥ := LinearMap.ker_eq_bot'.mpr fun u hu ↦ by
    by_contra hu₀
    rcases exists_symCoord_ne_zero hu₀ with ⟨r, hr⟩
    exact hr (congrFun hu r)
  rcases ι.exists_leftInverse_of_injective hι with ⟨π, hπ⟩
  have h₁ : Tendsto (fun x ↦ ι (v x)) l (𝓝 0) := tendsto_pi_nhds.mpr h
  have h₂ : Tendsto (fun x ↦ (φ ∘ₗ π) (ι (v x))) l (𝓝 ((φ ∘ₗ π) 0)) :=
    ((φ ∘ₗ π).continuous_of_finiteDimensional.tendsto 0).comp h₁
  rw [map_zero] at h₂
  refine h₂.congr fun x ↦ ?_
  have e : π (ι (v x)) = v x := LinearMap.congr_fun hπ (v x)
  rw [LinearMap.comp_apply, e]

private lemma mem_cuspFormsKJ_of_siegelCoordMap_eq_zero
    {G : modularFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))}
    (hG : siegelCoordMap H k j G = 0) : (G : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) ∈
      cuspFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) := by
  refine ⟨G.2, isCuspForm_of_forall_siegelOperatorVanishes_slash
    (fun g _ hf ↦ hf.slash_rhoKJ k g) G.2 fun g τ' φ ↦ ?_⟩
  have hq : ((QuotientGroup.mk g : symplecticGroup (Fin 2) ℤ ⧸ H).out)⁻¹ * g ∈ H :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
  generalize (QuotientGroup.mk g : symplecticGroup (Fin 2) ℤ ⧸ H) = q at hq
  have e : slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) g) G =
      slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) q.out) G := by
    have h₁ : g = q.out * (q.out⁻¹ * g) := (mul_inv_cancel_left _ _).symm
    rw [h₁, map_mul, slash_mul]
    exact mem_intSlashInvariants_of_mem_modularForms _ _ (slash_mem_modularForms_map
      (fun g _ hf ↦ hf.slash_rhoKJ k g) G.2 q.out) _ hq
  rw [e]
  refine tendsto_dual_of_forall_tendsto_symCoord (fun r ↦ ?_) φ
  have h₂ :
      siegelCoord r (slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) q.out) G) τ' = 0 :=
    DFunLike.congr_fun (congrFun (congrFun hG q) r) τ'
  rw [← h₂]
  exact tendsto_siegelCoord r τ' (isArithmetic_map H) (slash_mem_modularForms_map
    (fun g _ hf ↦ hf.slash_rhoKJ k g) G.2 q.out)

variable (k j H) in
/-- **The space `M_{k,j}(H)` is finite-dimensional**, for the image in `Sp(4, ℚ)` of a normal
subgroup `H` of finite index of `Sp(4, ℤ)`: `M_{k,j}(H)` is the sum of `S_{k,j}(H)`, which is
finite-dimensional, and its orthogonal complement, on which the linear map `F ↦ (u_r(F ∣ g))_{r, g}`
to a product of spaces of modular forms of degree one is injective, as its kernel consists of cusp
forms. -/
lemma finiteDimensional_modularFormsKJ_map :
    FiniteDimensional ℂ (modularFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))) := by
  have hS :
      FiniteDimensional ℂ (cuspFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))) :=
    finiteDimensional_cuspFormsKJ_map k j H
  have hadm : IsAdmissibleForm (rhoKJ k j) (symHermitianForm j) :=
    isAdmissibleForm_symHermitianForm k
  have hpos : ∀ v, v ≠ 0 → 0 < symHermitianForm j v v := fun _ hv ↦ symHermitianForm_pos hv
  have hN : FiniteDimensional ℂ (cuspFormsOrthogonalKJ
      (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) k j (symHermitianForm j)) := by
    let L : cuspFormsOrthogonalKJ (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) k j
        (symHermitianForm j) →ₗ[ℂ] _ :=
      (siegelCoordMap H k j).comp (Submodule.inclusion (cuspFormsOrthogonal_le _ _ _))
    refine FiniteDimensional.of_injective L ((injective_iff_map_eq_zero _).mpr fun F hF ↦
      Subtype.ext ?_)
    exact Submodule.disjoint_def.mp (disjoint_cuspForms_cuspFormsOrthogonal
      (isModerateForm_rhoKJ k _) hadm hpos (fun g _ hf ↦ hf.slash_rhoKJ k g) (isArithmetic_map H)) _
        (mem_cuspFormsKJ_of_siegelCoordMap_eq_zero hF) F.2
  exact Submodule.finiteDimensional_of_le (modularForms_eq_cuspForms_sup_cuspFormsOrthogonal
    (isModerateForm_rhoKJ k _) hadm hpos (fun g _ hf ↦ hf.slash_rhoKJ k g) (isArithmetic_map H)).le

variable (k j) in
/-- **The space `M_{k,j}(Γ)` is finite-dimensional, for every arithmetic subgroup `Γ` of
`Sp(4, ℚ)`**: it is contained in `M_{k,j}(H)`, for the image of a normal subgroup `H` of finite
index of `Sp(4, ℤ)`. -/
lemma finiteDimensional_modularFormsKJ_of_isArithmetic (hK : IsArithmetic K) :
    FiniteDimensional ℂ (modularFormsKJ k j K) := by
  rcases exists_normal_map_le hK with ⟨H, hN, hH, hle⟩
  have :
      FiniteDimensional ℂ (modularFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))) :=
    finiteDimensional_modularFormsKJ_map H k j
  exact Submodule.finiteDimensional_of_le (modularForms_le_of_le hle)

end SiegelUpperHalfSpace
