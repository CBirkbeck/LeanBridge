import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ArithmeticCuspDecay
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoOrthogonalDecomposition

/-!
# The Petersson product of degree 2 on arithmetic subgroups

An arithmetic subgroup `Γ` of `Sp(4, ℚ)` contains the image of a normal subgroup `H` of finite index
of `Sp(4, ℤ)`. So `M_ρ(Γ) ⊆ M_ρ(H)` and `S_ρ(Γ) ⊆ S_ρ(H)`, and `M_ρ(H)`, `S_ρ(H)` are stable under
the slash operators of `Sp(4, ℤ)`, when these preserve holomorphy. The translates of the Siegel set
by representatives `g` of `Sp(4, ℤ) / H` cover `ℋ₂` up to `H`, and the Petersson integrand of `F`,
`G` at `g Z` is the integrand of `F ∣ g`, `G ∣ g` at `Z`. For `F` modular and `G` cuspidal, `F ∣ g`
is bounded and `G ∣ g` decays exponentially on the Siegel set. So the Petersson integrand is
integrable on every fundamental domain of `Γ`, the Petersson product is definite on `S_ρ(Γ)`, and
if `S_ρ(Γ)` is finite-dimensional, `M_ρ(Γ)` is the direct sum of `S_ρ(Γ)` and its orthogonal
complement.

## Main results

* `SiegelUpperHalfSpace.exists_normal_map_le`: an arithmetic subgroup contains the image of a normal
  subgroup of finite index of `Sp(4, ℤ)`.
* `SiegelUpperHalfSpace.isArithmetic_map`: the image of a subgroup of finite index of `Sp(4, ℤ)` is
  arithmetic.
* `SiegelUpperHalfSpace.slash_mem_modularForms_map`, `SiegelUpperHalfSpace.slash_mem_cuspForms_map`:
  the slash operators of `Sp(4, ℤ)` preserve the modular forms and the cusp forms on the image of a
  normal subgroup.
* `SiegelUpperHalfSpace.exists_smul_eq_out_smul_of_normal`: the translates of the Siegel set by
  representatives of `Sp(4, ℤ) / H` cover `ℋ₂` up to `H`.
* `SiegelUpperHalfSpace.integrableOn_peterssonIntegrand_of_isArithmetic`: the Petersson integrand of
  a modular form and a cusp form on an arithmetic subgroup is integrable on every fundamental
  domain.
* `SiegelUpperHalfSpace.isPeterssonDefinite_cuspForms_of_isArithmetic`: the Petersson product is
  definite on the cusp forms on an arithmetic subgroup.
* `SiegelUpperHalfSpace.disjoint_cuspForms_cuspFormsOrthogonal`,
  `SiegelUpperHalfSpace.modularForms_eq_cuspForms_sup_cuspFormsOrthogonal`: `M_ρ(Γ)` is the direct
  sum of `S_ρ(Γ)` and its orthogonal complement, if `S_ρ(Γ)` is finite-dimensional.
-/

open Complex Matrix MeasureTheory Module Real Set SymplecticGroup Subgroup

open scoped ComplexOrder ENNReal Pointwise

namespace SiegelUpperHalfSpace

variable {Γ : Subgroup (symplecticGroup (Fin 2) ℚ)}

/-- **An arithmetic subgroup contains the image of a normal subgroup of finite index of
`Sp(4, ℤ)`**: the normal core of its preimage in `Sp(4, ℤ)`. -/
lemma exists_normal_map_le (hΓ : IsArithmetic Γ) : ∃ H : Subgroup (symplecticGroup (Fin 2) ℤ),
    H.Normal ∧ H.FiniteIndex ∧ H.map (SymplecticGroup.map (Int.castRingHom ℚ)) ≤ Γ := by
  have hfin : (Γ.comap (SymplecticGroup.map (Int.castRingHom ℚ))).FiniteIndex := ⟨by
    rw [index_comap, MonoidHom.range_eq_map]
    exact hΓ.1.relIndex_ne_zero⟩
  exact ⟨_, normalCore_normal _, inferInstance, map_le_iff_le_comap.mpr (normalCore_le _)⟩

/-- **The image of a subgroup of finite index of `Sp(4, ℤ)` is arithmetic.** -/
lemma isArithmetic_map (H : Subgroup (symplecticGroup (Fin 2) ℤ)) [H.FiniteIndex] :
    IsArithmetic (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) := by
  have e : integral (Fin 2) = (⊤ : Subgroup (symplecticGroup (Fin 2) ℤ)).map
      (SymplecticGroup.map (Int.castRingHom ℚ)) :=
    rfl
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · rw [e, relIndex_map_map_of_injective _ _ map_intCast_injective, relIndex_top_right]
    exact index_ne_zero_of_finite
  · rw [e, relIndex_eq_one.mpr (map_mono le_top)]
    exact one_ne_zero

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin 2) ℂ) V}
    {b : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {F G : SiegelUpperHalfSpace (Fin 2) → V}
    {Γ' : Subgroup (symplecticGroup (Fin 2) ℚ)} {H : Subgroup (symplecticGroup (Fin 2) ℤ)}

lemma modularForms_le_of_le (h : Γ' ≤ Γ) : modularForms ρ Γ 1 ≤ modularForms ρ Γ' 1 :=
  fun _ hf ↦ ⟨hf.1, fun γ τ ↦ by simpa using hf.2 ⟨γ, h γ.2⟩ τ⟩

lemma cuspForms_le_of_le (h : Γ' ≤ Γ) : cuspForms ρ Γ 1 ≤ cuspForms ρ Γ' 1 :=
  fun _ hf ↦ ⟨modularForms_le_of_le h hf.1, hf.2⟩

variable [H.Normal]

/-- **The slash operators of `Sp(4, ℤ)` preserve the modular forms on the image of a normal
subgroup**, if they preserve holomorphy. -/
lemma slash_mem_modularForms_map
    (hρ : ∀ (g : symplecticGroup (Fin 2) ℝ) (f : SiegelUpperHalfSpace (Fin 2) → V),
      IsHolomorphic f → IsHolomorphic (slash ρ g f))
    (hF : F ∈ modularForms ρ (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) 1)
    (γ : symplecticGroup (Fin 2) ℤ) : slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) γ) F ∈
      modularForms ρ (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) 1 := by
  refine (mem_modularForms_iff_slash ρ _ _ 1).mpr ⟨hρ _ _ hF.1, ?_⟩
  rintro ⟨_, δ, hδ, rfl⟩
  have h₁ : slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) (γ * δ * γ⁻¹)) F = F :=
    mem_intSlashInvariants_of_mem_modularForms _ _ hF _ (Normal.conj_mem ‹_› δ hδ γ)
  rw [map_algebraMap_map_intCast, ← slash_mul, ← map_mul,
    ← inv_mul_cancel_right (γ * δ) γ, map_mul _ (γ * δ * γ⁻¹) γ, slash_mul, h₁]
  simp

/-- **The slash operators of `Sp(4, ℤ)` preserve the cusp forms on the image of a normal
subgroup**, if they preserve holomorphy. -/
lemma slash_mem_cuspForms_map
    (hρ : ∀ (g : symplecticGroup (Fin 2) ℝ) (f : SiegelUpperHalfSpace (Fin 2) → V),
      IsHolomorphic f → IsHolomorphic (slash ρ g f))
    (hF : F ∈ cuspForms ρ (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) 1)
    (γ : symplecticGroup (Fin 2) ℤ) : slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) γ) F ∈
      cuspForms ρ (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) 1 :=
  ⟨slash_mem_modularForms_map hρ hF.1 γ, fun δ ↦ by
    rw [← slash_mul, ← map_algebraMap_map_intCast γ, ← map_mul]
    exact hF.2 _⟩

/-- **The translates of the Siegel set by representatives of `Sp(4, ℤ) / H` cover `ℋ₂` up to `H`**,
for a normal subgroup `H` of `Sp(4, ℤ)`. -/
lemma exists_smul_eq_out_smul_of_normal (τ : SiegelUpperHalfSpace (Fin 2)) : ∃ δ ∈ H,
    ∃ (q : symplecticGroup (Fin 2) ℤ ⧸ H), ∃ σ ∈ siegelSet,
      SymplecticGroup.map (Int.castRingHom ℝ) δ • τ =
        SymplecticGroup.map (Int.castRingHom ℝ) q.out • σ := by
  rcases exists_smul_mem_siegelSet τ with ⟨γ, hγ⟩
  have hq : ((QuotientGroup.mk γ⁻¹ : symplecticGroup (Fin 2) ℤ ⧸ H).out)⁻¹ * γ⁻¹ ∈ H :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
  generalize hg : (QuotientGroup.mk γ⁻¹ : symplecticGroup (Fin 2) ℤ ⧸ H).out = g at hq
  have hh : g * γ ∈ H := by
    have h₁ : g * (g⁻¹ * γ⁻¹) * g⁻¹ ∈ H := Normal.conj_mem ‹_› _ hq g
    have h₂ : g * (g⁻¹ * γ⁻¹) * g⁻¹ = (g * γ)⁻¹ := by
      group
    rw [h₂] at h₁
    exact inv_mem_iff.mp h₁
  refine ⟨g * γ, hh, QuotientGroup.mk γ⁻¹, _, hγ, ?_⟩
  rw [hg, map_mul, mul_smul]

variable [FiniteDimensional ℂ V]

lemma exists_norm_peterssonIntegrand_smul_le [H.FiniteIndex] (hb : IsModerateForm ρ b)
    (hadm : IsAdmissibleForm ρ b)
    (hρ : ∀ (g : symplecticGroup (Fin 2) ℝ) (f : SiegelUpperHalfSpace (Fin 2) → V),
      IsHolomorphic f → IsHolomorphic (slash ρ g f))
    (hF : F ∈ modularForms ρ (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) 1)
    (hG : G ∈ cuspForms ρ (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) 1)
    (γ : symplecticGroup (Fin 2) ℤ) : ∃ (c C : ℝ) (N : ℕ), 0 < c ∧ ∀ τ ∈ siegelSet,
      ‖peterssonIntegrand ρ b F G (SymplecticGroup.map (Int.castRingHom ℝ) γ • τ)‖ ≤
        C * rexp (-c * ((τ.val 0 0).im + (τ.val 1 1).im)) *
          (1 + (τ.val 0 0).im + (τ.val 1 1).im) ^ N := by
  rcases exists_norm_dual_le_of_mem_cuspForms_of_isArithmetic (isArithmetic_map H)
    (slash_mem_cuspForms_map hρ hG γ) with ⟨c, hc, hdecay⟩
  rcases exists_norm_peterssonIntegrand_le
    (f := slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) γ) F)
    (g := slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) γ) G)
    (A := fun τ ↦ rexp (-c * ((τ.val 0 0).im + (τ.val 1 1).im))) hb (fun φ ψ ↦ by
      rcases exists_norm_dual_le_of_mem_modularForms_of_isArithmetic (isArithmetic_map H)
        (slash_mem_modularForms_map hρ hF γ) φ with ⟨C₁, hC₁, h₁⟩
      rcases hdecay ψ with ⟨C₂, -, h₂⟩
      refine ⟨C₁ * C₂, fun τ hτ ↦ ?_⟩
      rw [mul_assoc]
      exact mul_le_mul (h₁ τ hτ) (h₂ τ hτ) (norm_nonneg _) hC₁) with ⟨C, N, hC⟩
  refine ⟨c, C, N, hc, fun τ hτ ↦ ?_⟩
  rw [← peterssonIntegrand_slash hadm]
  exact hC τ hτ

/-- **Convergence of the Petersson product on an arithmetic subgroup**: for a moderate admissible
form, the Petersson integrand of a modular form `F` and a cusp form `G` on an arithmetic `Γ` is
integrable on every fundamental domain, if the slash operators preserve holomorphy. -/
lemma integrableOn_peterssonIntegrand_of_isArithmetic (hb : IsModerateForm ρ b)
    (hadm : IsAdmissibleForm ρ b)
    (hρ : ∀ (g : symplecticGroup (Fin 2) ℝ) (f : SiegelUpperHalfSpace (Fin 2) → V),
      IsHolomorphic f → IsHolomorphic (slash ρ g f)) (hΓ : IsArithmetic Γ)
    (hF : F ∈ modularForms ρ Γ 1) (hG : G ∈ cuspForms ρ Γ 1)
    {s : Set (SiegelUpperHalfSpace (Fin 2))}
    (hs : IsFundamentalDomain (transformationGroup Γ) s (invariantMeasure (Fin 2))) :
    IntegrableOn (peterssonIntegrand ρ b F G) s (invariantMeasure (Fin 2)) := by
  classical
  rcases exists_normal_map_le hΓ with ⟨H, hN, hH, hle⟩
  have : Fintype (symplecticGroup (Fin 2) ℤ ⧸ H) := Fintype.ofFinite _
  refine hs.integrableOn_of_setLIntegral_lt_top
    (t := ⋃ q : symplecticGroup (Fin 2) ℤ ⧸ H, integralTransformation q.out • siegelSet)
    (continuous_peterssonIntegrand hb hF.1 hG.1.1).aestronglyMeasurable
    (fun γ τ ↦ by rw [peterssonIntegrand_map_smul hadm hF hG.1]) (.of_forall fun τ ↦ ?_) ?_
  · rcases exists_smul_eq_out_smul_of_normal (H := H) τ with ⟨δ, hδ, q, σ, hσ, h⟩
    refine ⟨⟨_, SymplecticGroup.map (Int.castRingHom ℚ) δ, hle ⟨_, hδ, rfl⟩, rfl⟩,
      mem_iUnion.mpr ⟨q, σ, hσ, ?_⟩⟩
    have e : SymplecticGroup.map (Int.castRingHom ℝ) q.out • σ =
        SymplecticGroup.map (algebraMap ℚ ℝ) (SymplecticGroup.map (Int.castRingHom ℚ) δ) • τ := by
      rw [map_algebraMap_map_intCast, h]
    exact e
  · refine (lintegral_iUnion_le _ _).trans_lt ?_
    rw [tsum_fintype]
    refine ENNReal.sum_lt_top.mpr fun q _ ↦ ?_
    rw [← image_smul, ← (measurePreserving_smul (integralTransformation q.out)
      (invariantMeasure (Fin 2))).setLIntegral_comp_emb
        (measurableEmbedding_const_smul (integralTransformation q.out))]
    rcases exists_norm_peterssonIntegrand_smul_le hb hadm hρ (modularForms_le_of_le hle hF)
      (cuspForms_le_of_le hle hG) q.out with ⟨c, C, N, hc, h⟩
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_siegelSet fun τ hτ ↦ ?_)
      (lintegral_siegelSet_mul_pow_lt_top C N hc)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (h τ hτ)

/-- **The Petersson product is definite on the cusp forms on an arithmetic subgroup**, for a
moderate admissible positive definite form `b`, if the slash operators preserve holomorphy. -/
lemma isPeterssonDefinite_cuspForms_of_isArithmetic (hb : IsModerateForm ρ b)
    (hadm : IsAdmissibleForm ρ b) (hpos : ∀ v, v ≠ 0 → 0 < b v v)
    (hρ : ∀ (g : symplecticGroup (Fin 2) ℝ) (f : SiegelUpperHalfSpace (Fin 2) → V),
      IsHolomorphic f → IsHolomorphic (slash ρ g f)) (hΓ : IsArithmetic Γ) :
    IsPeterssonDefinite Γ ρ b (cuspForms ρ Γ 1) :=
  IsPeterssonDefinite.of_integrableOn (fun τ _ hv ↦ peterssonForm_pos b hadm hpos τ hv)
    (exists_isFundamentalDomain hΓ) (cuspForms_le_modularForms _ _ _) fun _ _ hf hg ↦
      integrableOn_peterssonIntegrand_of_isArithmetic hb hadm hρ hΓ
        (cuspForms_le_modularForms _ _ _ hf) hg (isFundamentalDomain_fundamentalDomain hΓ)

/-- **A form both cuspidal and orthogonal to the cusp forms vanishes**, on an arithmetic
subgroup. -/
lemma disjoint_cuspForms_cuspFormsOrthogonal (hb : IsModerateForm ρ b) (hadm : IsAdmissibleForm ρ b)
    (hpos : ∀ v, v ≠ 0 → 0 < b v v)
    (hρ : ∀ (g : symplecticGroup (Fin 2) ℝ) (f : SiegelUpperHalfSpace (Fin 2) → V),
      IsHolomorphic f → IsHolomorphic (slash ρ g f)) (hΓ : IsArithmetic Γ) :
    Disjoint (cuspForms ρ Γ 1) (cuspFormsOrthogonal ρ Γ b) :=
  Submodule.disjoint_def.mpr fun f hf hf' ↦
    (isPeterssonDefinite_cuspForms_of_isArithmetic hb hadm hpos hρ hΓ).eq_zero f hf (hf'.2 f hf).2

/-- **`M_ρ(Γ) = S_ρ(Γ) ⊕ N_ρ(Γ)` on an arithmetic subgroup**, for a moderate admissible positive
definite form, if `S_ρ(Γ)` is finite-dimensional and the slash operators preserve holomorphy; the
sum is direct (`SiegelUpperHalfSpace.disjoint_cuspForms_cuspFormsOrthogonal`). -/
lemma modularForms_eq_cuspForms_sup_cuspFormsOrthogonal [FiniteDimensional ℂ (cuspForms ρ Γ 1)]
    (hb : IsModerateForm ρ b) (hadm : IsAdmissibleForm ρ b) (hpos : ∀ v, v ≠ 0 → 0 < b v v)
    (hρ : ∀ (g : symplecticGroup (Fin 2) ℝ) (f : SiegelUpperHalfSpace (Fin 2) → V),
      IsHolomorphic f → IsHolomorphic (slash ρ g f)) (hΓ : IsArithmetic Γ) :
    modularForms ρ Γ 1 = cuspForms ρ Γ 1 ⊔ cuspFormsOrthogonal ρ Γ b := by
  have hs : IsFundamentalDomain (transformationGroup Γ) (fundamentalDomain Γ)
      (invariantMeasure (Fin 2)) :=
    isFundamentalDomain_fundamentalDomain hΓ
  refine le_antisymm (fun F hF ↦ ?_)
    (sup_le (cuspForms_le_modularForms _ _ _) (cuspFormsOrthogonal_le _ _ _))
  rcases exists_mem_forall_peterssonProduct_eq
    (isPeterssonDefinite_cuspForms_of_isArithmetic hb hadm hpos hρ hΓ)
    (fun g hg ↦ integrableOn_peterssonIntegrand_of_isArithmetic hb hadm hρ hΓ hF hg hs) with
      ⟨g, hg, hgF⟩
  have hsub : F - g ∈ modularForms ρ Γ 1 := sub_mem hF (cuspForms_le_modularForms _ _ _ hg)
  refine Submodule.mem_sup.mpr ⟨g, hg, F - g, ⟨hsub, fun G hG ↦
    ⟨integrableOn_peterssonIntegrand_of_isArithmetic hb hadm hρ hΓ hsub hG hs, ?_⟩⟩,
      add_sub_cancel _ _⟩
  have e : peterssonIntegrand ρ b (F - g) G = peterssonIntegrand ρ b F G -
      peterssonIntegrand ρ b g G := by
    ext τ
    simp [peterssonIntegrand_apply]
  rw [peterssonProduct, e]
  simp only [Pi.sub_apply]
  rw [integral_sub (integrableOn_peterssonIntegrand_of_isArithmetic hb hadm hρ hΓ hF hG hs)
    (integrableOn_peterssonIntegrand_of_isArithmetic hb hadm hρ hΓ
      (cuspForms_le_modularForms _ _ _ hg) hG hs), ← peterssonProduct, ← peterssonProduct, hgF G hG,
    sub_self]

end SiegelUpperHalfSpace
