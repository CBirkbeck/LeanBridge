import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Basic
import TauCeti.AlgebraicGeometry.PicardFunctor.PicZero
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# The Jacobian of a curve

The Jacobian of a smooth projective geometrically integral curve `X` over a field `K` is the
abelian variety `J` that represents the degree-zero Picard functor `Pic⁰_{X/K}`. Following Milne
(*Jacobian varieties*, Section 1), with Tau Ceti's degree-zero relative Picard presheaf
`T ↦ Pic⁰(X_T) / Pic(T)`, `TauCeti.AlgebraicGeometry.relativePicardDegreeZeroFunctor`, this means
that there is a morphism of presheaves of groups from it to the functor of points of `J` which is
bijective at every scheme `T` over `K` over which `X` has a point.

When `X` has a `K`-rational point, this morphism is an isomorphism of presheaves of groups, whose
component at `Spec K` identifies `J(K)` with `Pic⁰_{X/K}(K)`, and the Jacobian is unique up to
isomorphism. With a rational point `x₀`, the Jacobian with its Abel–Jacobi map `X ⟶ J` is also
characterized by the Albanese property, Tau Ceti's
`TauCeti.AlgebraicGeometry.AbelianVariety.IsAlbanese`, which is not proved here.

The LMFDB's Jacobian comes with its canonical principal polarization, which needs the dual abelian
variety; neither it, nor the existence of the Jacobian, nor the fact that its dimension is the
genus of `X` is formalised here.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.IsJacobian` (LMFDB `ag.jacobian`).

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.IsJacobian.nonempty_relativePicardDegreeZeroFunctor_iso`
  and `TauCeti.AlgebraicGeometry.AbelianVariety.IsJacobian.nonempty_iso`: for a curve with a
  rational point, the degree-zero Picard functor is isomorphic to the functor of points of its
  Jacobian, and the Jacobian is unique up to isomorphism.
-/

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  [IsProper (X ↘ Spec (.of K))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of K))]
  [GeometricallyConnected (X ↘ Spec (.of K))] {J J' : AbelianVariety K}
  (x₀ : 𝟙_ (Over (Spec (.of K))) ⟶ X.asOver (Spec (.of K)))

variable (X J) in
/-- An abelian variety `J` over `K` is the **Jacobian** (LMFDB `ag.jacobian`) of a smooth proper
geometrically connected curve `X` over `K` if there is a morphism of presheaves of groups
`Pic⁰_{X/K} ⟶ J` on schemes over `K`, from the degree-zero relative Picard functor
`T ↦ Pic⁰(X_T) / Pic(T)` to the functor of points `T ↦ J(T)` of `J`, that is bijective at every
`T` over which `X` has a point.

The canonical principal polarization of the Jacobian is not part of this definition. -/
def IsJacobian : Prop :=
  ∃ ι : relativePicardDegreeZeroFunctor (X ↘ Spec (.of K)) ⋙ forget₂ CommGrpCat GrpCat ⟶
    yonedaGrpObj J.toOver ⋙ GrpCat.uliftFunctor.{u + 1}, ∀ T : Over (Spec (.of K)), Nonempty (T ⟶
    X.asOver (Spec (.of K))) → Function.Bijective (ι.app (op T))

variable (hJ : J.IsJacobian X)

include x₀ hJ in
/-- When `X` has a rational point `x₀`, the degree-zero Picard functor `T ↦ Pic⁰(X_T) / Pic(T)` of
`X` is isomorphic, as a presheaf of groups on schemes over `K`, to the functor of points of a
Jacobian `J` of `X`; at `T = Spec K`, this identifies `J(K)` with `Pic⁰_{X/K}(K) = Pic⁰(X)`. -/
lemma IsJacobian.nonempty_relativePicardDegreeZeroFunctor_iso : Nonempty
    (relativePicardDegreeZeroFunctor (X ↘ Spec (.of K)) ⋙ forget₂ CommGrpCat GrpCat ≅ yonedaGrpObj
    J.toOver ⋙ GrpCat.uliftFunctor.{u + 1}) := by
  rcases hJ with ⟨ι, hι⟩
  have : ∀ T, IsIso (ι.app T) := fun T ↦
    (ConcreteCategory.isIso_iff_bijective _).mpr (hι T.unop ⟨toUnit T.unop ≫ x₀⟩)
  have : IsIso ι := NatIso.isIso_of_isIso_app ι
  exact ⟨asIso ι⟩

include x₀ hJ in
/-- The Jacobian of a curve `X` with a rational point `x₀` is unique up to isomorphism. -/
lemma IsJacobian.nonempty_iso (hJ' : J'.IsJacobian X) : Nonempty (J ≅ J') := by
  rcases hJ.nonempty_relativePicardDegreeZeroFunctor_iso x₀ with ⟨e⟩
  rcases hJ'.nonempty_relativePicardDegreeZeroFunctor_iso x₀ with ⟨e'⟩
  let f : yonedaGrpObj J.toOver ≅ yonedaGrpObj J'.toOver :=
    (GrpCat.uliftFunctorFullyFaithful.whiskeringRight _).preimageIso (e.symm ≪≫ e')
  let g : Grp.mk J.toOver ≅ Grp.mk J'.toOver := yonedaGrpFullyFaithful.preimageIso f
  exact ⟨InducedCategory.isoMk ((CommGrp.fullyFaithfulForget₂Grp _).preimageIso g)⟩

end TauCeti.AlgebraicGeometry.AbelianVariety
