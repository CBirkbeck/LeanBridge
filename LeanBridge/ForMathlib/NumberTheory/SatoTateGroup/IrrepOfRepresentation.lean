import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.RepresentationTheory.Compact.Character.Basis
import TauCeti.RepresentationTheory.Compact.UnitaryModel
import TauCeti.RepresentationTheory.Continuous.Transport
import TauCeti.RepresentationTheory.Irreducible

/-!
# The class of an irreducible representation of a compact group

An irreducible finite-dimensional representation of a compact group with continuous matrix
coefficients, on a vector space without any topology, is equivalent to the chosen model of a class
of the unitary dual.

## Main results

* `SatoTateGroup.exists_irrepClass_equiv`: the class of an irreducible representation.
* `SatoTateGroup.character_model_eq_trace`: the character of the class is the trace on the
  representation.
-/

open TauCeti

namespace SatoTateGroup

variable {G V : Type*} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]

/-- **The character of the model of a class is the trace on an equivalent representation.** -/
lemma character_model_eq_trace {π : Representation ℂ G V} {χ : IrrepClass ℂ G}
    (e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin χ.model.dim)) (he : ∀ g v, e (π g v) = χ.model.rep g (e v))
    (g : G) : ContRepresentation.character χ.model.rep χ.model.continuous_rep g =
      LinearMap.trace ℂ V (π g) := by
  have h₁ : (χ.model.rep g : _ →L[ℂ] _).toLinearMap = e.conj (π g) := by
    refine LinearMap.ext fun x ↦ ?_
    have h₂ : e (π g (e.symm x)) = χ.model.rep g (e (e.symm x)) := he g (e.symm x)
    rw [LinearEquiv.apply_symm_apply] at h₂
    exact h₂.symm
  rw [ContRepresentation.character_apply, h₁, LinearMap.trace_conj']

variable [FiniteDimensional ℂ V]

lemma continuous_trace (π : Representation ℂ G V)
    (hc : ∀ (v : V) (φ : Module.Dual ℂ V), Continuous fun g ↦ φ (π g v)) :
    Continuous fun g ↦ LinearMap.trace ℂ V (π g) := by
  have h₁ (g : G) : LinearMap.trace ℂ V (π g) = ∑ i, (Module.finBasis ℂ V).coord i
      (π g (Module.finBasis ℂ V i)) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V), Matrix.trace]
    exact Finset.sum_congr rfl fun i _ ↦ LinearMap.toMatrix_apply _ _ _ _ _
  simp only [h₁]
  exact continuous_finsetSum _ fun i _ ↦ hc _ _

variable [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- **An irreducible representation of a compact group with continuous matrix coefficients is
equivalent to the chosen model of a class of the unitary dual.** -/
lemma exists_irrepClass_equiv (π : Representation ℂ G V) (hirr : π.IsIrreducible)
    (hc : ∀ (v : V) (φ : Module.Dual ℂ V), Continuous fun g ↦ φ (π g v)) :
    ∃ (χ : IrrepClass ℂ G) (e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin χ.model.dim)),
      ∀ g v, e (π g v) = χ.model.rep g (e v) := by
  let e₀ : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    (Module.finBasis ℂ V).equivFun.trans (WithLp.linearEquiv 2 ℂ _).symm
  let ρ : ContRepresentation ℂ G (EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) := .ofMonoidHom
    { toFun := fun g ↦ LinearMap.toContinuousLinearMap (e₀.conj (π g))
      map_one' := by
        refine ContinuousLinearMap.ext fun x ↦ ?_
        simp
      map_mul' := fun g h ↦ by
        refine ContinuousLinearMap.ext fun x ↦ ?_
        simp }
  have hρ₁ (g : G) (x : EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) :
      ρ g x = e₀ (π g (e₀.symm x)) :=
    rfl
  have hρ : Continuous ρ := by
    refine continuous_clm_apply.mpr fun y ↦ ?_
    simp only [hρ₁]
    refine (EuclideanSpace.equiv (Fin (Module.finrank ℂ V)) ℂ).symm.continuous.comp
      (continuous_pi fun i ↦ ?_)
    exact hc (e₀.symm y) ((Module.finBasis ℂ V).coord i)
  rcases ContRepresentation.exists_isUnitary_congr ρ hρ with ⟨e₁, he₁⟩
  have hirr₁ : ρ.toRepresentation.IsIrreducible :=
    Representation.isIrreducible_of_linearEquiv e₀ (fun g v ↦ by
      have h₁ : ρ g (e₀ v) = e₀ (π g (e₀.symm (e₀ v))) := hρ₁ g (e₀ v)
      rw [LinearEquiv.symm_apply_apply] at h₁
      exact h₁.symm) hirr
  let m : IrrepModel ℂ G :=
    ⟨_, ContinuousLinearEquiv.congr e₁ ρ, ContinuousLinearEquiv.continuous_congr e₁ hρ, he₁,
      ContinuousLinearEquiv.isIrreducible_congr e₁ hirr₁⟩
  rcases Quotient.mk_out (s := IrrepModel.instSetoid ℂ G) m with ⟨e₂, he₂⟩
  refine ⟨Quotient.mk _ m, (e₀.trans (e₁ : _ ≃ₗ[ℂ] _)).trans e₂.symm.toLinearEquiv, fun g v ↦ ?_⟩
  have h₂ : e₂ ((IrrepClass.model (Quotient.mk _ m : IrrepClass ℂ G)).rep g
      (e₂.symm (e₁ (e₀ v)))) = m.rep g (e₁ (e₀ v)) :=
    congrArg (fun r : ContRepresentation ℂ G _ ↦ r g (e₁ (e₀ v))) he₂
  have h₃ : ρ g (e₀ v) = e₀ (π g v) := by
    rw [hρ₁, LinearEquiv.symm_apply_apply]
  have h₄ : m.rep g (e₁ (e₀ v)) = e₁ (e₀ (π g v)) := by
    rw [← h₃]
    refine (ContinuousLinearEquiv.congr_apply e₁ ρ g (e₁ (e₀ v))).trans ?_
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [h₄] at h₂
  exact (e₂.symm_apply_eq.mpr h₂.symm)

end SatoTateGroup
