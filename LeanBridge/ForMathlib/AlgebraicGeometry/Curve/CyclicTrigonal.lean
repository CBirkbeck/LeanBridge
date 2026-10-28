import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Basic
import Mathlib.FieldTheory.Galois.Basic

/-!
# Cyclic trigonal curves

An algebraic curve `X` over a field `k` is cyclic trigonal if some subgroup `H` of order three of
its automorphism group has quotient curve `X / H` isomorphic to `ℙ¹`; a generator of such an `H` is
a trigonal automorphism.

Automorphisms of `X` over `k` are taken as `k`-automorphisms of the function field `k(X)` (the two
groups are anti-isomorphic for smooth proper curves, which is not formalised), and the quotient
curve `X / H` (`AlgebraicGeometry.Scheme.IsQuotientCurve`) is described by its function field, the
fixed field `k(X)ᴴ`. The quotient is isomorphic to `ℙ¹_k` exactly when this fixed field is a
rational function field `k(t)` with `t` transcendental over `k`.

## Main definitions

* `TauCeti.IsCyclicTrigonalFunctionField` (LMFDB `ag.cyclic_trigonal`).
* `TauCeti.IsTrigonalAutomorphism` (LMFDB `ag.cyclic_trigonal`).
* `AlgebraicGeometry.Scheme.IsCyclicTrigonalCurveOver` (LMFDB `ag.cyclic_trigonal`).

## Main results

* `TauCeti.isCyclicTrigonalFunctionField_iff_exists_isTrigonalAutomorphism`: a function field is
  cyclic trigonal if and only if it has a trigonal automorphism.
-/

open scoped IntermediateField

namespace TauCeti

variable (k : Type*) {F : Type*} [Field k] [Field F] [Algebra k F]

variable (F) in
/-- A field extension `F / k`, such as the function field `k(X)` of a curve `X` over `k`, is
**cyclic trigonal** (LMFDB `ag.cyclic_trigonal`) if some subgroup `H` of order three of its
automorphism group has a rational function field `k(t)`, with `t` transcendental over `k`, as fixed
field, that is the quotient curve `X / H` is isomorphic to `ℙ¹_k`. -/
def IsCyclicTrigonalFunctionField : Prop :=
  ∃ H : Subgroup (F ≃ₐ[k] F), Nat.card H = 3 ∧
    ∃ t : F, Transcendental k t ∧ IntermediateField.fixedField H = k⟮t⟯

/-- A **trigonal automorphism** (LMFDB `ag.cyclic_trigonal`) of a field extension `F / k`, such as
the function field of a curve over `k`: an automorphism `σ` of order three that generates a
subgroup `H` exhibiting `F` as cyclic trigonal, whose fixed field is a rational function field
`k(t)`. -/
def IsTrigonalAutomorphism (σ : F ≃ₐ[k] F) : Prop :=
  orderOf σ = 3 ∧ ∃ t : F, Transcendental k t ∧ IntermediateField.fixedField (.zpowers σ) = k⟮t⟯

/-- **A field extension is cyclic trigonal if and only if it has a trigonal automorphism.** -/
lemma isCyclicTrigonalFunctionField_iff_exists_isTrigonalAutomorphism :
    IsCyclicTrigonalFunctionField k F ↔ ∃ σ : F ≃ₐ[k] F, IsTrigonalAutomorphism k σ := by
  refine ⟨fun ⟨H, hH, ht⟩ ↦ ?_, fun ⟨σ, hσ, ht⟩ ↦ ⟨_, Nat.card_zpowers σ ▸ hσ, ht⟩⟩
  have : Fact (Nat.Prime (Nat.card H)) := ⟨hH ▸ Nat.prime_three⟩
  rcases (isCyclic_of_prime_card rfl).exists_generator (α := H) with ⟨σ, hσ⟩
  have ho : orderOf (σ : F ≃ₐ[k] F) = 3 :=
    (Subgroup.orderOf_coe σ).trans <| (orderOf_eq_card_of_forall_mem_zpowers hσ).trans hH
  have : Finite H := Nat.finite_of_card_ne_zero <| by omega
  have he : Subgroup.zpowers (σ : F ≃ₐ[k] F) = H :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr σ.2) <| by
      rw [hH, Nat.card_zpowers, ho]
  exact ⟨σ, ho, by rwa [he]⟩

end TauCeti

namespace AlgebraicGeometry.Scheme

universe u

variable (K : Type u) [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

/-- An algebraic curve `X` over `K` is a **cyclic trigonal curve** (LMFDB `ag.cyclic_trigonal`) if
some subgroup `H` of order three of its automorphism group has quotient curve `X / H` isomorphic to
`ℙ¹_K`: automorphisms are taken as `K`-automorphisms of the function field `K(X)`, and the
condition is that the fixed field `K(X)ᴴ`, the function field of `X / H`, is a rational function
field `K(t)`. -/
class IsCyclicTrigonalCurveOver : Prop extends X.IsAlgebraicCurveOver K where
  /-- The function field is cyclic trigonal. -/
  isCyclicTrigonalFunctionField :
    haveI : IsIntegral X := IsVarietyOver.isIntegral K
    TauCeti.IsCyclicTrigonalFunctionField K X.functionField

end AlgebraicGeometry.Scheme
