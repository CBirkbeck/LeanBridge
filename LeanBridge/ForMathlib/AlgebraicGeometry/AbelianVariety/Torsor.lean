import LeanBridge.ForMathlib.AlgebraicGeometry.Variety.Basic
import Mathlib.CategoryTheory.Monoidal.Mod
import TauCeti.AlgebraicGeometry.AbelianVariety.Basic

/-!
# Principal homogeneous spaces of an abelian variety

A principal homogeneous space, or torsor, of an abelian variety `A` over a field `k` is a variety
`X` over `k` with an action of `A` such that `X_{k̄}`, with the induced action of `A_{k̄}`, is
isomorphic to `A_{k̄}` acting on itself by translation, where `k̄` is a separable closure of `k`.

An action of `A` on `X` is Mathlib's `ModObj A X` in the cartesian monoidal category of schemes
over `Spec k`. An `A_{k̄}`-equivariant isomorphism `A_{k̄} → X_{k̄}` is the orbit map `a ↦ a • x`
of the image `x ∈ X(k̄)` of the identity, and conversely; so the condition says that for some
point `x : Spec k̄ → X` over `k`, the morphism `A ×_k Spec k̄ → X ×_k Spec k̄`,
`(a, t) ↦ (a • x(t), t)`, is an isomorphism. This is how we state it, without base-changing the
action. The bijection with `H¹(k, A)` and the equivalent triviality conditions are not formalised.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.sepClosureOver`: `Spec k̄` as a scheme over `k`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.orbitMap`: the morphism
  `A ×_k Spec k̄ → X ×_k Spec k̄`, `(a, t) ↦ (a • x(t), t)`, of a point `x ∈ X(k̄)`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.IsPrincipalHomogeneousSpace` (LMFDB `ag.torsor`):
  principal homogeneous spaces of `A`.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.AbelianVariety

variable {k : Type*} [Field k] (A : AbelianVariety k) (X : Over (Spec (.of k)))
  [ModObj A.toOver X]

variable (k) in
/-- The spectrum of a separable closure `k̄` of a field `k`, as a scheme over `k`. -/
noncomputable def sepClosureOver : Over (Spec (.of k)) :=
  Over.mk <| Spec.map <| CommRingCat.ofHom <| algebraMap k (SeparableClosure k)

/-- The morphism `A ×_k Spec k̄ → X ×_k Spec k̄`, `(a, t) ↦ (a • x(t), t)`, of a point
`x : Spec k̄ → X` over `k` of a scheme `X` with an action of an abelian variety `A`: the base change
to `k̄` of the orbit map of `x`. -/
noncomputable def orbitMap (x : sepClosureOver k ⟶ X) :
    A.toOver ⊗ sepClosureOver k ⟶ X ⊗ sepClosureOver k :=
  lift (lift (fst _ _) (snd _ _ ≫ x) ≫ ModObj.smul (M := A.toOver)) (snd _ _)

/-- A **principal homogeneous space** or **torsor** (LMFDB `ag.torsor`) of an abelian variety `A`
over a field `k`: a variety `X` over `k` with an action of `A` such that `X_{k̄}` with the induced
action of `A_{k̄}` is isomorphic to `A_{k̄}` acting by translation, for a separable closure `k̄` of
`k`; equivalently, the base change to `k̄` of the orbit map of some point `x ∈ X(k̄)` is an
isomorphism. -/
structure IsPrincipalHomogeneousSpace : Prop where
  /-- `X` is a variety over `k`. -/
  isVarietyOver : X.left.IsVarietyOver k
  /-- The base change to `k̄` of the orbit map of some point of `X(k̄)` is an isomorphism. -/
  exists_isIso_orbitMap : ∃ x : sepClosureOver k ⟶ X, IsIso (A.orbitMap X x)

end TauCeti.AlgebraicGeometry.AbelianVariety
