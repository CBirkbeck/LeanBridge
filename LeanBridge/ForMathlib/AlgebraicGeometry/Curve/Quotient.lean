import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Basic
import Mathlib.CategoryTheory.Endomorphism

/-!
# Quotient curves

The quotient curve `X / H` of an algebraic curve `X` over a field `K` by a finite group `H` of
automorphisms of `X` is the algebraic curve obtained by identifying the points of each `H`-orbit,
together with the projection `X ⟶ X / H`. As for every quotient of a quasi-projective variety by a
finite group, it is a categorical quotient: the projection is invariant under `H`, and every
morphism from `X` invariant under `H` factors uniquely through it. This universal property
characterizes the quotient curve up to unique isomorphism, and it is how the quotient curve is
defined here.

The existence of `X / H`, by gluing the invariant quotients `Spec Aᴴ` of an `H`-stable affine cover
of `X` (Tau Ceti's `TauCeti.AffineInvariantQuotient.quotient` for one affine chart), and the
surjectivity of the projection are not formalised.

## Main definitions

* `AlgebraicGeometry.Scheme.IsQuotientCurve` (LMFDB `ag.quotient_curve`).
* `AlgebraicGeometry.Scheme.IsQuotientCurve.desc`: the factorisation through the quotient curve of
  a morphism invariant under `H`.
* `AlgebraicGeometry.Scheme.IsQuotientCurve.uniqueUpToIso`: the isomorphism between two quotient
  curves of `X` by `H`.

## Main results

* `AlgebraicGeometry.Scheme.isQuotientCurve_bot`: the quotient of a curve by the trivial group is
  the curve itself.
-/

namespace AlgebraicGeometry.Scheme

open CategoryTheory

universe u

variable {K : Type u} [Field K] {X Y Y' : Over (Spec (.of K))} {H : Subgroup (Aut X)} {π : X ⟶ Y}
  {π' : X ⟶ Y'}

variable (H π) in
/-- A morphism `π : X ⟶ Y` of schemes over `K` exhibits `Y` as the **quotient curve** `X / H`
(LMFDB `ag.quotient_curve`) of an algebraic curve `X` over `K` by a finite subgroup `H` of its
automorphism group if `Y` is an algebraic curve over `K`, `π` is invariant under `H`, and every
morphism over `K` from `X` that is invariant under `H` factors uniquely through `π`. -/
structure IsQuotientCurve : Prop where
  /-- The source `X` is an algebraic curve. -/
  isAlgebraicCurveOver_left : X.left.IsAlgebraicCurveOver K
  /-- The group `H` is finite. -/
  finite : Finite H
  /-- The quotient is an algebraic curve. -/
  isAlgebraicCurveOver_right : Y.left.IsAlgebraicCurveOver K
  /-- The projection is invariant under `H`. -/
  hom_comp : ∀ h ∈ H, h.asIso.hom ≫ π = π
  /-- Every morphism invariant under `H` factors uniquely through the projection. -/
  existsUnique_comp_eq ⦃Z : Over (Spec (.of K))⦄ (f : X ⟶ Z) :
    (∀ h ∈ H, h.asIso.hom ≫ f = f) → ∃! g : Y ⟶ Z, π ≫ g = f

namespace IsQuotientCurve

variable (hπ : IsQuotientCurve H π) (hπ' : IsQuotientCurve H π') {Z : Over (Spec (.of K))}
  {f : X ⟶ Z} (hf : ∀ h ∈ H, h.asIso.hom ≫ f = f)

include hπ in
lemma hom_ext {g g' : Y ⟶ Z} (h : π ≫ g = π ≫ g') : g = g' :=
  (hπ.existsUnique_comp_eq (π ≫ g') fun σ hσ ↦ by rw [← Category.assoc, hπ.hom_comp σ hσ]).unique
    h rfl

/-- The morphism `X / H ⟶ Z` through which a morphism `f : X ⟶ Z` invariant under `H` factors. -/
noncomputable def desc : Y ⟶ Z :=
  (hπ.existsUnique_comp_eq f hf).choose

@[reassoc (attr := simp)]
lemma fac : π ≫ hπ.desc hf = f :=
  (hπ.existsUnique_comp_eq f hf).choose_spec.1

include hπ hπ' in
/-- Two quotient curves of `X` by `H` are isomorphic, compatibly with their projections from `X`. -/
noncomputable def uniqueUpToIso : Y ≅ Y' where
  hom := hπ.desc hπ'.hom_comp
  inv := hπ'.desc hπ.hom_comp
  hom_inv_id := hπ.hom_ext <| by rw [fac_assoc, fac, Category.comp_id]
  inv_hom_id := hπ'.hom_ext <| by rw [fac_assoc, fac, Category.comp_id]

@[reassoc (attr := simp)]
lemma comp_uniqueUpToIso_hom : π ≫ (hπ.uniqueUpToIso hπ').hom = π' :=
  hπ.fac hπ'.hom_comp

end IsQuotientCurve

/-- The quotient of an algebraic curve `X` by the trivial group is `X`, with the identity as
projection. -/
lemma isQuotientCurve_bot [X.left.IsAlgebraicCurveOver K] :
    IsQuotientCurve (⊥ : Subgroup (Aut X)) (𝟙 X) where
  isAlgebraicCurveOver_left := inferInstance
  finite := inferInstance
  isAlgebraicCurveOver_right := inferInstance
  hom_comp h hh := by
    rw [Subgroup.mem_bot.mp hh, Aut.one_asIso, Iso.refl_hom, Category.comp_id]
  existsUnique_comp_eq _ f _ :=
    ⟨f, Category.id_comp f, fun _ hg ↦ (Category.id_comp _).symm.trans hg⟩

end AlgebraicGeometry.Scheme
