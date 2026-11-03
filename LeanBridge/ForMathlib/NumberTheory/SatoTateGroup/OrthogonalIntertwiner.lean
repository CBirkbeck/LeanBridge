import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.IrrepOfRepresentation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.Integral
import TauCeti.RepresentationTheory.Compact.Character.IsotypicProjection
import TauCeti.RepresentationTheory.Compact.Intertwiner.Basic

/-!
# Intertwiners between isotypic vectors of two unitary representations

Two nonzero isotypic vectors of the same type in two unitary representations of a compact group are
related by an intertwiner, which is nonzero on the span of the orbit of the first and takes a value
in the span of the orbit of the second. The intertwiner is the composite of the two nonzero maps
from the model of the type given by averaging rank one operators, one of them adjoint. Moreover a
nonzero vector of a unitary representation has a nonzero isotypic component.

## Main results

* `SatoTateGroup.exists_intertwiner_of_isotypic`: two isotypic vectors of the same type are related
  by an intertwiner.
* `SatoTateGroup.exists_isotypicProjector_ne_zero`: a nonzero vector has a nonzero isotypic
  component.
-/

open Filter MeasureTheory Representation TauCeti

open scoped InnerProductSpace

namespace SatoTateGroup

variable {G V V' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
  {ρ : ContRepresentation ℂ G V} {ρ' : ContRepresentation ℂ G V'} (χ : IrrepClass ℂ G)

local instance : CompleteSpace V := FiniteDimensional.complete ℂ V

local instance : CompleteSpace V' := FiniteDimensional.complete ℂ V'

lemma exists_averageOperator_ne_zero (hρ : Continuous ρ) (hu : ρ.IsUnitary) {x : V}
    (hx : ContRepresentation.isotypicProjector ρ hρ χ.model.rep χ.model.continuous_rep x = x)
    (hx₀ : x ≠ 0) : ∃ ξ : EuclideanSpace ℂ (Fin χ.model.dim),
      ContRepresentation.averageOperator χ.model.rep χ.model.continuous_rep ρ hρ
        (InnerProductSpace.rankOne ℂ x ξ) ≠ 0 := by
  by_contra h
  push Not at h
  refine hx₀ (ext_inner_left ℂ fun w ↦ ?_)
  rw [inner_zero_right]
  have h₁ (i : Fin χ.model.dim) :
      ∫ g, ⟪χ.model.rep g (χ.model.basis i), χ.model.basis i⟫_ℂ * ⟪w, ρ g x⟫_ℂ ∂haarProb G = 0 := by
    have h₂ : 0 = ∫ g, ⟪ρ g w, InnerProductSpace.rankOne ℂ x (χ.model.basis i)
        (χ.model.rep g (χ.model.basis i))⟫_ℂ ∂haarProb G := by
      rw [← ContRepresentation.inner_averageOperator_of_isUnitary χ.model.rep
        χ.model.continuous_rep ρ hρ hu, h, zero_apply, inner_zero_right]
    rw [← integral_inv_eq_self]
    refine Eq.trans (integral_congr_ae (Eventually.of_forall fun g ↦ ?_)) h₂.symm
    beta_reduce
    rw [InnerProductSpace.rankOne_apply, inner_smul_right,
      χ.model.isUnitary.inner_map_right g (χ.model.basis i) (χ.model.basis i),
      hu.inner_map_right g⁻¹ w x, inv_inv]
  have hcont (i : Fin χ.model.dim) :
      Continuous fun g ↦ ⟪χ.model.rep g (χ.model.basis i), χ.model.basis i⟫_ℂ * ⟪w, ρ g x⟫_ℂ :=
    ((χ.model.continuous_rep.clm_apply continuous_const).inner continuous_const).mul
      (continuous_const.inner (hρ.clm_apply continuous_const))
  have h₂ (g : G) : star (ContRepresentation.character χ.model.rep χ.model.continuous_rep g) =
      ∑ i, ⟪χ.model.rep g (χ.model.basis i), χ.model.basis i⟫_ℂ := by
    rw [← ContinuousMap.star_apply, ContRepresentation.star_character _ _ χ.model.basis,
      ContinuousMap.sum_apply]
    rfl
  have hint : Integrable (fun g ↦ ContRepresentation.isotypicKernel χ.model.rep
      χ.model.continuous_rep g • ρ g x) (haarProb G) :=
    Continuous.integrable_of_hasCompactSupport
      ((ContRepresentation.isotypicKernel χ.model.rep χ.model.continuous_rep).continuous.smul
        (hρ.clm_apply continuous_const)) (HasCompactSupport.of_compactSpace _)
  rw [← hx, ContRepresentation.isotypicProjector_apply, ← integral_inner hint]
  have h₃ (g : G) : ⟪w, ContRepresentation.isotypicKernel χ.model.rep χ.model.continuous_rep g •
      ρ g x⟫_ℂ = (Module.finrank ℂ (EuclideanSpace ℂ (Fin χ.model.dim)) : ℂ) *
        ∑ i, ⟪χ.model.rep g (χ.model.basis i), χ.model.basis i⟫_ℂ * ⟪w, ρ g x⟫_ℂ := by
    rw [inner_smul_right, ContRepresentation.isotypicKernel_apply, h₂, mul_assoc, Finset.sum_mul]
  simp only [h₃]
  rw [integral_const_mul, integral_finsetSum _ fun i _ ↦
    (hcont i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)]
  simp only [h₁, Finset.sum_const_zero, mul_zero]

lemma averageOperator_rankOne_mem_span (hρ : Continuous ρ) (x : V)
    (ξ v : EuclideanSpace ℂ (Fin χ.model.dim)) : ContRepresentation.averageOperator χ.model.rep
      χ.model.continuous_rep ρ hρ (InnerProductSpace.rankOne ℂ x ξ) v ∈
        Submodule.span ℂ (Set.range fun g ↦ ρ g x) := by
  rw [ContRepresentation.averageOperator_apply]
  let U : Submodule ℂ V := Submodule.span ℂ (Set.range fun g ↦ ρ g x)
  have hclosed : IsClosed (U : Set V) := Submodule.closed_of_finiteDimensional U
  have hconvex : Convex ℝ (U : Set V) := (U.restrictScalars ℝ).convex
  refine hconvex.integral_mem hclosed (Eventually.of_forall fun g ↦ ?_) ?_
  · rw [InnerProductSpace.rankOne_apply, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g⁻¹, rfl⟩)
  · refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    exact (hρ.comp continuous_inv).clm_apply
      ((InnerProductSpace.rankOne ℂ x ξ).continuous.comp
        (χ.model.continuous_rep.clm_apply continuous_const))

/-- **Two isotypic vectors of the same type are related by an intertwiner**, between the spans of
their orbits. -/
lemma exists_intertwiner_of_isotypic (hρ : Continuous ρ) (hu : ρ.IsUnitary) (hρ' : Continuous ρ')
    (hu' : ρ'.IsUnitary) {x : V} {y : V'}
    (hx : ContRepresentation.isotypicProjector ρ hρ χ.model.rep χ.model.continuous_rep x = x)
    (hx₀ : x ≠ 0)
    (hy : ContRepresentation.isotypicProjector ρ' hρ' χ.model.rep χ.model.continuous_rep y = y)
    (hy₀ : y ≠ 0) : ∃ F : V →L[ℂ] V', (∀ g v, F (ρ g v) = ρ' g (F v)) ∧
      ∃ v ∈ Submodule.span ℂ (Set.range fun g ↦ ρ g x), F v ≠ 0 ∧
        F v ∈ Submodule.span ℂ (Set.range fun g ↦ ρ' g y) := by
  rcases exists_averageOperator_ne_zero χ hρ hu hx hx₀ with ⟨ξ₁, hξ₁⟩
  rcases exists_averageOperator_ne_zero χ hρ' hu' hy hy₀ with ⟨ξ₂, hξ₂⟩
  let S₁ : EuclideanSpace ℂ (Fin χ.model.dim) →L[ℂ] V :=
    ContRepresentation.averageOperator χ.model.rep χ.model.continuous_rep ρ hρ
      (InnerProductSpace.rankOne ℂ x ξ₁)
  let S₂ : EuclideanSpace ℂ (Fin χ.model.dim) →L[ℂ] V' :=
    ContRepresentation.averageOperator χ.model.rep χ.model.continuous_rep ρ' hρ'
      (InnerProductSpace.rankOne ℂ y ξ₂)
  have hS₁ (g : G) (v : EuclideanSpace ℂ (Fin χ.model.dim)) : S₁ (χ.model.rep g v) = ρ g (S₁ v) :=
    ContRepresentation.averageOperator_isIntertwining _ _ _ _ _ g v
  have hS₂ (g : G) (v : EuclideanSpace ℂ (Fin χ.model.dim)) : S₂ (χ.model.rep g v) = ρ' g (S₂ v) :=
    ContRepresentation.averageOperator_isIntertwining _ _ _ _ _ g v
  have hS₂inj : Function.Injective S₂ := by
    let f : IntertwiningMap χ.model.rep.toRepresentation ρ'.toRepresentation :=
      (ContRepresentation.averageIntertwiner χ.model.rep χ.model.continuous_rep ρ' hρ'
        (InnerProductSpace.rankOne ℂ y ξ₂)).toIntertwiningMap
    have hf : f ≠ 0 := fun h₀ ↦ hξ₂ (ContinuousLinearMap.ext fun v ↦
      congrArg (fun φ : IntertwiningMap _ _ ↦ φ v) h₀)
    have : χ.model.rep.toRepresentation.IsIrreducible := χ.model.isIrreducible
    exact (IsIrreducible.injective_or_eq_zero f).resolve_right hf
  have hadj (g : G) (v : V) : S₁.adjoint (ρ g v) = χ.model.rep g (S₁.adjoint v) := by
    refine ext_inner_right ℂ fun e ↦ ?_
    rw [ContinuousLinearMap.adjoint_inner_left, ← inv_inv g, ← hu.inner_map_right g⁻¹,
      ← χ.model.isUnitary.inner_map_right g⁻¹, ContinuousLinearMap.adjoint_inner_left, hS₁]
  rcases DFunLike.ne_iff.mp hξ₁ with ⟨v₀, hv₀⟩
  have hv₁ : S₁ v₀ ≠ 0 := hv₀
  refine ⟨S₂.comp S₁.adjoint, fun g v ↦ ?_, S₁ v₀, averageOperator_rankOne_mem_span χ hρ x ξ₁ v₀,
    ?_, averageOperator_rankOne_mem_span χ hρ' y ξ₂ _⟩
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hadj, hS₂]
  · rw [ContinuousLinearMap.comp_apply]
    refine fun h₀ ↦ hv₁ ?_
    have h₁ : S₁.adjoint (S₁ v₀) = 0 := hS₂inj (h₀.trans (map_zero S₂).symm)
    have h₂ : ⟪S₁ v₀, S₁ v₀⟫_ℂ = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_left, h₁, inner_zero_left]
    exact inner_self_eq_zero.mp h₂

variable (ρ) in
/-- **A nonzero vector of a unitary representation has a nonzero isotypic component.** -/
lemma exists_isotypicProjector_ne_zero (hρ : Continuous ρ) (hu : ρ.IsUnitary) {x : V} (hx : x ≠ 0) :
    ∃ χ : IrrepClass ℂ G,
      ContRepresentation.isotypicProjector ρ hρ χ.model.rep χ.model.continuous_rep x ≠ 0 := by
  by_contra h
  push Not at h
  let σ : Subrepresentation ρ.toRepresentation :=
    { toSubmodule := Submodule.span ℂ (Set.range fun g ↦ ρ g x)
      apply_mem_toSubmodule := fun g v hv ↦ by
        induction hv using Submodule.span_induction with
        | mem y hy =>
          rcases hy with ⟨g', rfl⟩
          exact Submodule.subset_span ⟨g * g', congrArg (fun R ↦ R x) (map_mul ρ g g')⟩
        | zero =>
          rw [map_zero]
          exact Submodule.zero_mem _
        | add y z _ _ hy hz =>
          rw [map_add]
          exact Submodule.add_mem _ hy hz
        | smul c y _ hy =>
          rw [map_smul]
          exact Submodule.smul_mem _ c hy }
  have hσ : σ ≠ ⊥ := fun h₀ ↦ by
    have h₁ : x ∈ σ.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
    rw [h₀, Subrepresentation.toSubmodule_bot, Submodule.mem_bot] at h₁
    exact hx h₁
  rcases Representation.exists_isAtom_le hσ with ⟨τ, hτσ, hτ⟩
  have hc (v : τ.toSubmodule) (φ : Module.Dual ℂ τ.toSubmodule) :
      Continuous fun g ↦ φ (τ.toRepresentation g v) := by
    have h₁ : Continuous fun g ↦ (⟨ρ g v, τ.apply_mem_toSubmodule g v.2⟩ : τ.toSubmodule) :=
      (hρ.clm_apply continuous_const).subtype_mk _
    exact (LinearMap.continuous_of_finiteDimensional φ).comp h₁
  rcases exists_irrepClass_equiv τ.toRepresentation
    (Representation.isIrreducible_toRepresentation_of_isAtom hτ) hc with ⟨χ, e, he⟩
  let φ : τ.toRepresentation.Equiv χ.model.rep.toRepresentation :=
    .mk e fun g ↦ LinearMap.ext (he g)
  have he' : Nonempty (τ.asSubmodule ≃ₗ[MonoidAlgebra ℂ G] χ.model.rep.toRepresentation.asModule) :=
    ⟨τ.asModuleEquivAsSubmodule.symm.trans (Representation.asModuleLinearEquivOfEquiv φ)⟩
  let P : ContIntertwiningMap ρ ρ :=
    ContRepresentation.isotypicProjector ρ hρ χ.model.rep χ.model.continuous_rep
  have h₁ (v : τ.toSubmodule) : P (v : V) = v :=
    ContRepresentation.isotypicProjector_apply_subtype_of_equiv ρ hρ hu _ _ hτ he' v
  have h₂ : ∀ v ∈ σ.toSubmodule, P v = 0 := fun v hv ↦ by
    induction hv using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨g, rfl⟩
      have h₃ : P (ρ g x) = ρ g (P x) := congrArg (fun R ↦ R x) (P.isIntertwining' g)
      rw [h₃, h χ, map_zero]
    | zero => exact map_zero P
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul c y _ hy => rw [map_smul, hy, smul_zero]
  refine hτ.1 (Subrepresentation.toSubmodule_injective (eq_bot_iff.mpr fun v hv ↦ ?_))
  have h₃ : P v = v := h₁ ⟨v, hv⟩
  rw [h₂ v (hτσ hv)] at h₃
  exact h₃.symm

end SatoTateGroup
