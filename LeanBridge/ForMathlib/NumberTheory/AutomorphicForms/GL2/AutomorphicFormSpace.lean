import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.AutomorphicForm
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The spaces of automorphic forms and of cusp forms on `GL₂(𝔸_F)`

The automorphic forms with a given central character form a complex vector space, stable under the
right translations by `GL₂(𝔸_F^f)` (which give the action of the Hecke operators), and an
automorphic form is continuous, so that its constant term is an integral of a continuous function
on a compact group. The cusp forms form a subspace.

## Main definitions

* `AdelicGL2.rightTranslateₗ`: right translation, as a linear map.
* `AdelicGL2.automorphicForms`: the space of automorphic forms with central character `ω`.
* `AdelicGL2.cuspForms`: the space of cusp forms with central character `ω`.

## Main results

* `AdelicGL2.IsAutomorphicForm.continuous`: an automorphic form is continuous on `GL₂(𝔸_F)`.
* `AdelicGL2.IsAutomorphicForm.rightTranslate`: right translates by `GL₂(𝔸_F^f)` of automorphic
  forms are automorphic forms.
* `AdelicGL2.unipotent_out_mul`: for a function left invariant under `GL₂(F)`, the integrand of the
  constant term does not depend on the representatives in `𝔸_F` of the points of `𝔸_F / F`.
* `AdelicGL2.IsAutomorphicForm.integrable_constantTerm`: the integrand of the constant term of an
  automorphic form is integrable, so that the constant term is not a junk value.
* `AdelicGL2.IsCuspidal.rightTranslate`: right translates of cusp forms are cusp forms.
-/

open IsDedekindDomain Matrix NumberField MeasureTheory TauCeti GlobalNumberFields

open mixedEmbedding (mixedSpace)

open scoped AdeleRing MatrixGroups Classical

namespace AdelicGL2

variable {F : Type*} [Field F] [NumberField F] {ω : HeckeCharacter F} {φ φ₁ φ₂ : AdelicGL2 F → ℂ}

lemma one_le_infHeight (x : GL (Fin 2) (mixedSpace F)) : 1 ≤ infHeight x :=
  le_add_of_nonneg_right <| Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
    add_nonneg (norm_nonneg _) (norm_nonneg _)

lemma IsSmoothOperator.map_zero {D : (AdelicGL2 F → ℂ) → AdelicGL2 F → ℂ}
    (hD : IsSmoothOperator D) : D 0 = 0 := by
  simpa using hD.smul 0 0 (isSmoothAtInfinity_const 0)

variable (F) in
/-- Right translation by an element of `GL₂(𝔸_F)`, as a linear map on functions. -/
noncomputable def rightTranslateₗ (h : AdelicGL2 F) :
    (AdelicGL2 F → ℂ) →ₗ[ℂ] AdelicGL2 F → ℂ where
  toFun := rightTranslate h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma casimirOf_map {D : Fin 3 → (AdelicGL2 F → ℂ) → AdelicGL2 F → ℂ}
    (T : (AdelicGL2 F → ℂ) →ₗ[ℂ] AdelicGL2 F → ℂ) (hT : ∀ b ψ, D b (T ψ) = T (D b ψ))
    (ψ : AdelicGL2 F → ℂ) : casimirOf D (T ψ) = T (casimirOf D ψ) := by
  simp only [casimirOf, hT, map_add, map_smul]

private lemma lieDerivHolo_map (T : (AdelicGL2 F → ℂ) →ₗ[ℂ] AdelicGL2 F → ℂ)
    (hT : ∀ b y ψ, lieDeriv b y (T ψ) = T (lieDeriv b y ψ))
    (v : {v : InfinitePlace F // v.IsComplex}) (b : Fin 3) (ψ : AdelicGL2 F → ℂ) :
    lieDerivHolo v b (T ψ) = T (lieDerivHolo v b ψ) := by
  simp only [lieDerivHolo, hT, map_sub, map_smul]

private lemma lieDerivAntiholo_map (T : (AdelicGL2 F → ℂ) →ₗ[ℂ] AdelicGL2 F → ℂ)
    (hT : ∀ b y ψ, lieDeriv b y (T ψ) = T (lieDeriv b y ψ))
    (v : {v : InfinitePlace F // v.IsComplex}) (b : Fin 3) (ψ : AdelicGL2 F → ℂ) :
    lieDerivAntiholo v b (T ψ) = T (lieDerivAntiholo v b ψ) := by
  simp only [lieDerivAntiholo, hT, map_add, map_smul]

lemma IsCasimirFinite.map (T : (AdelicGL2 F → ℂ) →ₗ[ℂ] AdelicGL2 F → ℂ)
    (hs : ∀ ψ, IsSmoothAtInfinity ψ → IsSmoothAtInfinity (T ψ))
    (hT : ∀ b y ψ, lieDeriv b y (T ψ) = T (lieDeriv b y ψ)) (h : IsCasimirFinite φ) :
    IsCasimirFinite (T φ) := by
  rcases h with ⟨W, hf, hφ, hsm, hr, hh, ha⟩
  refine ⟨W.map T, inferInstance, Submodule.mem_map_of_mem hφ, ?_, fun v ↦ ?_, fun v ↦ ?_,
    fun v ↦ ?_⟩
  · rintro _ ⟨ψ, hψ, rfl⟩
    exact hs ψ (hsm ψ hψ)
  · rintro _ ⟨ψ, hψ, rfl⟩
    exact ⟨_, hr v ψ hψ, (casimirOf_map T (fun b ψ ↦ hT b _ ψ) ψ).symm⟩
  · rintro _ ⟨ψ, hψ, rfl⟩
    exact ⟨_, hh v ψ hψ, (casimirOf_map T (lieDerivHolo_map T hT v) ψ).symm⟩
  · rintro _ ⟨ψ, hψ, rfl⟩
    exact ⟨_, ha v ψ hψ, (casimirOf_map T (lieDerivAntiholo_map T hT v) ψ).symm⟩

lemma IsKFinite.map (T : (AdelicGL2 F → ℂ) →ₗ[ℂ] AdelicGL2 F → ℂ)
    (hT : ∀ k : unitaryGroup (Fin 2) (mixedSpace F), ∃ c : ℂ,
      rightTranslate (ofInf F (Unitary.toUnits k)) (T φ) =
        c • T (rightTranslate (ofInf F (Unitary.toUnits k)) φ))
    (h : IsKFinite φ) : IsKFinite (T φ) := by
  have hle : kInfSpan (T φ) ≤ (kInfSpan φ).map T := by
    refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun k ↦ ?_)
    rcases hT k with ⟨c, hc⟩
    rw [hc]
    exact Submodule.smul_mem _ c
      (Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_range_self k)))
  have hfd : FiniteDimensional ℂ (kInfSpan φ) := h
  exact Submodule.finiteDimensional_of_le hle

private lemma stable_sup {W₁ W₂ : Submodule ℂ (AdelicGL2 F → ℂ)}
    {D : (AdelicGL2 F → ℂ) → AdelicGL2 F → ℂ} (hD : IsSmoothOperator D)
    (hs₁ : ∀ ψ ∈ W₁, IsSmoothAtInfinity ψ) (hs₂ : ∀ ψ ∈ W₂, IsSmoothAtInfinity ψ)
    (h₁ : ∀ ψ ∈ W₁, D ψ ∈ W₁) (h₂ : ∀ ψ ∈ W₂, D ψ ∈ W₂) (ψ : AdelicGL2 F → ℂ)
    (hψ : ψ ∈ W₁ ⊔ W₂) : D ψ ∈ W₁ ⊔ W₂ := by
  rcases Submodule.mem_sup.mp hψ with ⟨ψ₁, hψ₁, ψ₂, hψ₂, rfl⟩
  rw [hD.add ψ₁ ψ₂ (hs₁ ψ₁ hψ₁) (hs₂ ψ₂ hψ₂)]
  exact Submodule.add_mem_sup (h₁ ψ₁ hψ₁) (h₂ ψ₂ hψ₂)

lemma IsCasimirFinite.add (h₁ : IsCasimirFinite φ₁) (h₂ : IsCasimirFinite φ₂) :
    IsCasimirFinite (φ₁ + φ₂) := by
  rcases h₁ with ⟨W₁, hf₁, hφ₁, hs₁, hr₁, hh₁, ha₁⟩
  rcases h₂ with ⟨W₂, hf₂, hφ₂, hs₂, hr₂, hh₂, ha₂⟩
  refine ⟨W₁ ⊔ W₂, inferInstance, Submodule.add_mem_sup hφ₁ hφ₂, fun ψ hψ ↦ ?_, fun v ↦ ?_,
    fun v ↦ ?_, fun v ↦ ?_⟩
  · rcases Submodule.mem_sup.mp hψ with ⟨ψ₁, hψ₁, ψ₂, hψ₂, rfl⟩
    exact (hs₁ ψ₁ hψ₁).add (hs₂ ψ₂ hψ₂)
  · exact stable_sup (isSmoothOperator_casimirReal v) hs₁ hs₂ (hr₁ v) (hr₂ v)
  · exact stable_sup (isSmoothOperator_casimirHolo v) hs₁ hs₂ (hh₁ v) (hh₂ v)
  · exact stable_sup (isSmoothOperator_casimirAntiholo v) hs₁ hs₂ (ha₁ v) (ha₂ v)

lemma IsCasimirFinite.const_smul (c : ℂ) (h : IsCasimirFinite φ) : IsCasimirFinite (c • φ) := by
  rcases h with ⟨W, hf, hφ, h⟩
  exact ⟨W, hf, Submodule.smul_mem _ c hφ, h⟩

variable (F) in
lemma isCasimirFinite_zero : IsCasimirFinite (0 : AdelicGL2 F → ℂ) := by
  refine ⟨⊥, inferInstance, zero_mem _, ?_, fun v ↦ ?_, fun v ↦ ?_, fun v ↦ ?_⟩
  · rintro ψ hψ
    rw [(Submodule.mem_bot ℂ).mp hψ]
    exact isSmoothAtInfinity_const 0
  · rintro ψ hψ
    rw [(Submodule.mem_bot ℂ).mp hψ, (isSmoothOperator_casimirReal v).map_zero]
    exact zero_mem _
  · rintro ψ hψ
    rw [(Submodule.mem_bot ℂ).mp hψ, (isSmoothOperator_casimirHolo v).map_zero]
    exact zero_mem _
  · rintro ψ hψ
    rw [(Submodule.mem_bot ℂ).mp hψ, (isSmoothOperator_casimirAntiholo v).map_zero]
    exact zero_mem _

lemma IsKFinite.add (h₁ : IsKFinite φ₁) (h₂ : IsKFinite φ₂) : IsKFinite (φ₁ + φ₂) := by
  have hf₁ : FiniteDimensional ℂ (kInfSpan φ₁) := h₁
  have hf₂ : FiniteDimensional ℂ (kInfSpan φ₂) := h₂
  have hle : kInfSpan (φ₁ + φ₂) ≤ kInfSpan φ₁ ⊔ kInfSpan φ₂ :=
    Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun k ↦ Submodule.add_mem_sup
      (Submodule.subset_span (Set.mem_range_self k)) (Submodule.subset_span (Set.mem_range_self k))
  exact Submodule.finiteDimensional_of_le hle

lemma IsKFinite.const_smul (c : ℂ) (h : IsKFinite φ) : IsKFinite (c • φ) := by
  have hf : FiniteDimensional ℂ (kInfSpan φ) := h
  have hle : kInfSpan (c • φ) ≤ kInfSpan φ :=
    Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun k ↦
      Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_range_self k))
  exact Submodule.finiteDimensional_of_le hle

variable (F) in
lemma isKFinite_zero : IsKFinite (0 : AdelicGL2 F → ℂ) := by
  have h : kInfSpan (0 : AdelicGL2 F → ℂ) ≤ ⊥ :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun _ ↦ zero_mem _)
  exact Submodule.finiteDimensional_of_le h

lemma HasModerateGrowth.add (h₁ : HasModerateGrowth φ₁) (h₂ : HasModerateGrowth φ₂) :
    HasModerateGrowth (φ₁ + φ₂) := fun y ↦ by
  rcases h₁ y with ⟨C₁, n₁, hC₁⟩
  rcases h₂ y with ⟨C₂, n₂, hC₂⟩
  refine ⟨|C₁| + |C₂|, n₁ + n₂, fun x ↦ ?_⟩
  have hx : 1 ≤ infHeight x := one_le_infHeight x
  have hp₁ : infHeight x ^ n₁ ≤ infHeight x ^ (n₁ + n₂) := pow_le_pow_right₀ hx (by omega)
  have hp₂ : infHeight x ^ n₂ ≤ infHeight x ^ (n₁ + n₂) := pow_le_pow_right₀ hx (by omega)
  have hq₁ : 0 ≤ infHeight x ^ n₁ := by positivity
  have hq₂ : 0 ≤ infHeight x ^ n₂ := by positivity
  refine (norm_add_le _ _).trans ?_
  nlinarith [hC₁ x, hC₂ x, le_abs_self C₁, le_abs_self C₂, abs_nonneg C₁, abs_nonneg C₂]

lemma HasModerateGrowth.const_smul (c : ℂ) (h : HasModerateGrowth φ) :
    HasModerateGrowth (c • φ) := fun y ↦ by
  rcases h y with ⟨C, n, hC⟩
  refine ⟨‖c‖ * C, n, fun x ↦ ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)

lemma IsAutomorphicForm.add (h₁ : IsAutomorphicForm ω φ₁) (h₂ : IsAutomorphicForm ω φ₂) :
    IsAutomorphicForm ω (φ₁ + φ₂) where
  left_invariant γ g := by
    rw [Pi.add_apply, h₁.left_invariant, h₂.left_invariant, Pi.add_apply]
  central z g := by
    rw [Pi.add_apply, h₁.central, h₂.central, Pi.add_apply, mul_add]
  smooth := h₁.smooth.add h₂.smooth
  exists_openSubgroup := by
    rcases h₁.exists_openSubgroup with ⟨U₁, hU₁⟩
    rcases h₂.exists_openSubgroup with ⟨U₂, hU₂⟩
    refine ⟨U₁ ⊓ U₂, fun u hu g ↦ ?_⟩
    rw [Pi.add_apply, hU₁ u hu.1, hU₂ u hu.2, Pi.add_apply]
  kFinite := h₁.kFinite.add h₂.kFinite
  casimirFinite := h₁.casimirFinite.add h₂.casimirFinite
  moderateGrowth := h₁.moderateGrowth.add h₂.moderateGrowth

lemma IsAutomorphicForm.const_smul (c : ℂ) (h : IsAutomorphicForm ω φ) :
    IsAutomorphicForm ω (c • φ) where
  left_invariant γ g := by
    rw [Pi.smul_apply, h.left_invariant, Pi.smul_apply]
  central z g := by
    rw [Pi.smul_apply, h.central, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]
  smooth := h.smooth.const_smul c
  exists_openSubgroup := by
    rcases h.exists_openSubgroup with ⟨U, hU⟩
    exact ⟨U, fun u hu g ↦ by rw [Pi.smul_apply, hU u hu, Pi.smul_apply]⟩
  kFinite := h.kFinite.const_smul c
  casimirFinite := h.casimirFinite.const_smul c
  moderateGrowth := h.moderateGrowth.const_smul c

variable (F ω) in
lemma isAutomorphicForm_zero : IsAutomorphicForm ω (0 : AdelicGL2 F → ℂ) where
  left_invariant _ _ := rfl
  central _ _ := by
    simp
  smooth := isSmoothAtInfinity_const 0
  exists_openSubgroup := ⟨⊤, fun _ _ _ ↦ rfl⟩
  kFinite := isKFinite_zero F
  casimirFinite := isCasimirFinite_zero F
  moderateGrowth _ := ⟨0, 0, fun _ ↦ by simp⟩

variable (ω) in
/-- The complex vector space of **automorphic forms** on `GL(2)` over `F` with central character
`ω`. -/
def automorphicForms : Submodule ℂ (AdelicGL2 F → ℂ) where
  carrier := {φ | IsAutomorphicForm ω φ}
  add_mem' := IsAutomorphicForm.add
  zero_mem' := isAutomorphicForm_zero F ω
  smul_mem' c _ h := h.const_smul c

lemma rightTranslate_comm {h h' : AdelicGL2 F} (hc : h * h' = h' * h) (ψ : AdelicGL2 F → ℂ) :
    rightTranslate h (rightTranslate h' ψ) = rightTranslate h' (rightTranslate h ψ) :=
  funext fun g ↦ by
    simp only [rightTranslate, mul_assoc, hc]

lemma lieDeriv_rightTranslate_ofFin (b : Fin 3) (w : mixedSpace F) (y : GL (Fin 2) 𝔸ᶠ[F])
    (ψ : AdelicGL2 F → ℂ) : lieDeriv b w (rightTranslate (ofFin F y) ψ) =
      rightTranslate (ofFin F y) (lieDeriv b w ψ) :=
  funext fun g ↦ by
    simp only [lieDeriv, rightTranslate, mul_assoc, ofFin_mul_ofInf]

lemma IsSmoothAtInfinity.rightTranslate_ofFin (y : GL (Fin 2) 𝔸ᶠ[F]) (h : IsSmoothAtInfinity φ) :
    IsSmoothAtInfinity (rightTranslate (ofFin F y) φ) := fun g ↦ by
  have he : (fun x ↦ rightTranslate (ofFin F y) φ (g * ofInf F x)) =
      fun x ↦ φ (g * ofFin F y * ofInf F x) :=
    funext fun x ↦ by
      rw [rightTranslate, mul_assoc, mul_assoc, ofFin_mul_ofInf]
  rw [he]
  exact h _

/-- **The right translates by `GL₂(𝔸_F^f)` of an automorphic form are automorphic forms.** -/
lemma IsAutomorphicForm.rightTranslate (y : GL (Fin 2) 𝔸ᶠ[F]) (h : IsAutomorphicForm ω φ) :
    IsAutomorphicForm ω (rightTranslate (ofFin F y) φ) where
  left_invariant γ g := by
    simp only [AdelicGL2.rightTranslate, mul_assoc, h.left_invariant]
  central z g := by
    simp only [AdelicGL2.rightTranslate, mul_assoc, h.central]
  smooth := h.smooth.rightTranslate_ofFin y
  exists_openSubgroup := by
    rcases h.exists_openSubgroup with ⟨U, hU⟩
    let c : GL (Fin 2) 𝔸ᶠ[F] →* GL (Fin 2) 𝔸ᶠ[F] := (MulAut.conj y⁻¹).toMonoidHom
    have hc : Continuous c := (continuous_const.mul continuous_id).mul continuous_const
    refine ⟨U.comap c hc, fun u hu g ↦ ?_⟩
    have hu' : y⁻¹ * u * y⁻¹⁻¹ ∈ U := hu
    rw [inv_inv] at hu'
    have he : g * ofFin F u * ofFin F y = g * ofFin F y * ofFin F (y⁻¹ * u * y) := by
      simp only [map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
    rw [AdelicGL2.rightTranslate, he, hU _ hu']
    rfl
  kFinite := IsKFinite.map (rightTranslateₗ F (ofFin F y)) (fun _ ↦ ⟨1,
    (rightTranslate_comm (ofFin_mul_ofInf _ y).symm φ).trans (one_smul ℂ _).symm⟩) h.kFinite
  casimirFinite := IsCasimirFinite.map (rightTranslateₗ F (ofFin F y))
    (fun _ hψ ↦ hψ.rightTranslate_ofFin y) (fun b w ψ ↦ lieDeriv_rightTranslate_ofFin b w y ψ)
      h.casimirFinite
  moderateGrowth y' := by
    rcases h.moderateGrowth (y' * y) with ⟨C, n, hC⟩
    refine ⟨C, n, fun x ↦ ?_⟩
    have he : ofInf F x * ofFin F y' * ofFin F y = ofInf F x * ofFin F (y' * y) := by
      rw [map_mul, mul_assoc]
    rw [AdelicGL2.rightTranslate, he]
    exact hC x

variable (F) in
lemma continuous_toFin : Continuous (toFin F) :=
  Continuous.generalLinearGroup_map
    (f := (RingHom.snd _ _).comp (adeleEquiv F : 𝔸[F] →+* mixedSpace F × 𝔸ᶠ[F])) continuous_snd

variable (F) in
lemma continuous_toInf : Continuous (toInf F) :=
  Continuous.generalLinearGroup_map
    (f := (RingHom.fst _ _).comp (adeleEquiv F : 𝔸[F] →+* mixedSpace F × 𝔸ᶠ[F]))
    ((InfiniteAdeleRing.continuous_ringEquiv_mixedSpace F).comp continuous_fst)

/-- **An automorphic form is continuous on `GL₂(𝔸_F)`**: it is smooth in the archimedean variable,
and locally constant in the finite variable, uniformly. -/
lemma IsAutomorphicForm.continuous (h : IsAutomorphicForm ω φ) : Continuous φ := by
  rcases h.exists_openSubgroup with ⟨U, hU⟩
  refine continuous_iff_continuousAt.mpr fun g₀ ↦ ?_
  have hV : {g | (toFin F g₀)⁻¹ * toFin F g ∈ U} ∈ nhds g₀ :=
    (U.isOpen.preimage (continuous_const.mul (continuous_toFin F))).mem_nhds (by simp)
  have heq : φ =ᶠ[nhds g₀] fun g ↦ φ (ofFin F (toFin F g₀) * ofInf F (toInf F g)) := by
    filter_upwards [hV] with g hg
    rw [← hU _ hg (ofFin F (toFin F g₀) * ofInf F (toInf F g))]
    refine congrArg φ (ext_toInf_toFin ?_ ?_) <;> simp
  refine ContinuousAt.congr ?_ heq.symm
  exact ((h.smooth _).continuous.comp (continuous_toInf F)).continuousAt

variable (F) in
lemma continuous_unipotent : Continuous (unipotent : 𝔸[F] → AdelicGL2 F) :=
  GeneralLinearGroup.continuous_upperRightHom

lemma unipotent_add (a b : 𝔸[F]) : unipotent (a + b) = unipotent a * unipotent b :=
  GeneralLinearGroup.upperRightHom.map_add_eq_mul a b

lemma ofGlobal_upperRightHom (ξ : F) :
    ofGlobal F (GeneralLinearGroup.upperRightHom ξ) = unipotent (algebraMap F 𝔸[F] ξ) := by
  refine GeneralLinearGroup.ext fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;> simp [ofGlobal, unipotent]

/-- **A function left invariant under `GL₂(F)` does not see the representative chosen in the
constant term**: `φ(n(x') g) = φ(n(x) g)` when `x' ∈ 𝔸_F` represents the class of `x` in
`𝔸_F / F`. -/
lemma unipotent_out_mul
    (hφ : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 F), φ (ofGlobal F γ * g) = φ g) (a : 𝔸[F])
    (g : AdelicGL2 F) :
    φ (unipotent (Quotient.out (a : AdeleQuotient F)) * g) = φ (unipotent a * g) := by
  have h : Quotient.out (a : AdeleQuotient F) - a ∈ AdeleRing.principalSubgroup (𝓞 F) F := by
    refine neg_add_eq_sub a _ ▸ QuotientAddGroup.eq.mp ?_
    exact (Quotient.out_eq _).symm
  rcases h with ⟨ξ, hξ⟩
  have he : Quotient.out (a : AdeleQuotient F) = algebraMap F 𝔸[F] ξ + a := by
    rw [← sub_eq_iff_eq_add]
    exact hξ.symm
  rw [he, unipotent_add, ← ofGlobal_upperRightHom, mul_assoc, hφ]

variable (F) in
private lemma continuous_constantTerm_integrand (h : IsAutomorphicForm ω φ) (g : AdelicGL2 F) :
    Continuous fun x : AdeleQuotient F ↦ φ (unipotent (Quotient.out x) * g) := by
  refine (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr ?_
  have he : (fun x : AdeleQuotient F ↦ φ (unipotent (Quotient.out x) * g)) ∘ QuotientAddGroup.mk =
      fun a ↦ φ (unipotent a * g) :=
    funext fun a ↦ unipotent_out_mul h.left_invariant a g
  rw [he]
  exact h.continuous.comp ((continuous_unipotent F).mul continuous_const)

/-- **The integrand of the constant term of an automorphic form is integrable**: it is a
continuous function on the compact group `𝔸_F / F`, so the constant term is a genuine integral. -/
lemma IsAutomorphicForm.integrable_constantTerm (h : IsAutomorphicForm ω φ) (g : AdelicGL2 F) :
    Integrable (fun x : AdeleQuotient F ↦ φ (unipotent (Quotient.out x) * g)) Measure.addHaar :=
  (continuous_constantTerm_integrand F h g).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma constantTerm_add (h₁ : IsAutomorphicForm ω φ₁) (h₂ : IsAutomorphicForm ω φ₂)
    (g : AdelicGL2 F) : constantTerm (φ₁ + φ₂) g = constantTerm φ₁ g + constantTerm φ₂ g :=
  integral_add (h₁.integrable_constantTerm g) (h₂.integrable_constantTerm g)

variable (φ) in
lemma constantTerm_const_smul (c : ℂ) (g : AdelicGL2 F) :
    constantTerm (c • φ) g = c * constantTerm φ g :=
  integral_const_mul c _

lemma IsCuspidal.add (h₁ : IsAutomorphicForm ω φ₁) (h₂ : IsAutomorphicForm ω φ₂)
    (hc₁ : IsCuspidal φ₁) (hc₂ : IsCuspidal φ₂) : IsCuspidal (φ₁ + φ₂) := fun g ↦ by
  rw [constantTerm_add h₁ h₂, hc₁ g, hc₂ g, add_zero]

lemma IsCuspidal.const_smul (c : ℂ) (h : IsCuspidal φ) : IsCuspidal (c • φ) := fun g ↦ by
  rw [constantTerm_const_smul, h g, mul_zero]

/-- **The right translates of a cusp form are cusp forms.** -/
lemma IsCuspidal.rightTranslate (k : AdelicGL2 F) (h : IsCuspidal φ) :
    IsCuspidal (rightTranslate k φ) := fun g ↦ by
  have he : constantTerm (AdelicGL2.rightTranslate k φ) g = constantTerm φ (g * k) := by
    simp only [constantTerm, AdelicGL2.rightTranslate, mul_assoc]
  rw [he, h]

variable (ω) in
/-- The complex vector space of **cusp forms** on `GL(2)` over `F` with central character `ω`. -/
def cuspForms : Submodule ℂ (AdelicGL2 F → ℂ) where
  carrier := {φ | IsAutomorphicForm ω φ ∧ IsCuspidal φ}
  add_mem' := fun ha hb ↦ ⟨ha.1.add hb.1, IsCuspidal.add ha.1 hb.1 ha.2 hb.2⟩
  zero_mem' := ⟨isAutomorphicForm_zero F ω, fun _ ↦ by simp [constantTerm]⟩
  smul_mem' c _ h := ⟨h.1.const_smul c, h.2.const_smul c⟩

variable (ω) in
lemma cuspForms_le : cuspForms ω ≤ automorphicForms ω :=
  fun _ h ↦ h.1

end AdelicGL2
