import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Basic
import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricBaseChange

/-!
# The projective line is an algebraic curve

The projective line `ℙ¹_K = Proj K[X₀, X₁]` over a field `K`, Tau Ceti's
`TauCeti.AlgebraicGeometry.projectiveLine K`, is geometrically integral over `K`: its base change
to a field `L` over `K` is the projective spectrum of the symmetric algebra of `L ⊗[K] K²` (Tau
Ceti's `AlgebraicGeometry.Proj.symmetricAlgebraBaseChangeIso`), which is integral since that
symmetric algebra, a polynomial ring in two variables over `L`, is a domain. Being a curve over `K`
in Tau Ceti's sense (integral, proper and of dimension one over `K`), `ℙ¹_K` is therefore an
algebraic curve over `K` (LMFDB `ag.curve`).

## Main results

* The instance `GeometricallyIntegral (projectiveLine K ↘ Spec K)`: `ℙ¹_K` is geometrically
  integral over `K`.
* The instance `(projectiveLine K).IsAlgebraicCurveOver K`: `ℙ¹_K` is an algebraic curve over `K`.
-/

open CategoryTheory AlgebraicGeometry

open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry.projectiveLine

universe u

variable (K : Type u) [Field K]

lemma isIntegral_proj_symmetricAlgebra_baseChange (L : Type u) [Field L] [Algebra K L] :
    IsIntegral (Proj (SymmetricAlgebra.homogeneousSubmodule L (L ⊗[K] (Fin 2 → K)))) := by
  refine Proj.isIntegral_of_isDomain _ fun h ↦ ?_
  have hmem : SymmetricAlgebra.ι L (L ⊗[K] (Fin 2 → K)) (1 ⊗ₜ Pi.single 0 1) ∈
      HomogeneousIdeal.irrelevant (SymmetricAlgebra.homogeneousSubmodule L _) := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_ne _ (SymmetricAlgebra.ι_mem_homogeneousSubmodule L _ _)
        one_ne_zero]
  rw [h, ← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at hmem
  have h₀ : (1 : L) ⊗ₜ[K] (Pi.single 0 1 : Fin 2 → K) = 0 :=
    SymmetricAlgebra.ι_injective L _ (hmem.trans (map_zero _).symm)
  have h₁ : TensorProduct.rid K L
      ((LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K).lTensor L ((1 : L) ⊗ₜ[K] Pi.single 0 1)) = 0 := by
    rw [h₀, map_zero, map_zero]
  simp at h₁

instance : GeometricallyIntegral (projectiveLine K ↘ Spec (.of K)) := by
  have : ObjectProperty.IsClosedUnderIsomorphisms IsIntegral :=
    ⟨fun {X Y} e _ ↦
      have : Nonempty Y := ⟨e.hom (Classical.arbitrary X)⟩
      isIntegral_of_isOpenImmersion e.inv⟩
  rw [geometricallyIntegral_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro L _ _
  have : IsIntegral (Proj (SymmetricAlgebra.homogeneousSubmodule L (L ⊗[K] (Fin 2 → K)))) :=
    isIntegral_proj_symmetricAlgebra_baseChange K L
  exact ObjectProperty.prop_of_iso _ (Proj.symmetricAlgebraBaseChangeIso K L (Fin 2 → K)) this

end TauCeti.AlgebraicGeometry.projectiveLine

namespace AlgebraicGeometry.Scheme

open TauCeti AlgebraicGeometry in
instance (K : Type*) [Field K] : (projectiveLine K).IsAlgebraicCurveOver K :=
  IsCurveOver.isAlgebraicCurveOver

end AlgebraicGeometry.Scheme
