import LeanBridge.ForMathlib.AlgebraicGeometry.LocalObstruction
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Points over extensions and locally solvable curves

For a scheme `X` over a field `K` and a `K`-algebra `L`, the `L`-points of `X` are the morphisms
`Spec L ⟶ X` over `Spec K`; the `K`-points are the rational points `X(K)` (LMFDB
`g2c.all_rational_points`). A curve over a number field `K` is locally solvable if it has a point
over every completion `K_v` of `K` (LeanBridge's `AlgebraicGeometry.Scheme.HasPointIn`): over `ℚ`,
over `ℝ` and over `ℚ_p` for every prime `p`. The finite places of `K` are the height one primes `v`
of `𝓞 K`, with completion `IsDedekindDomain.HeightOneSpectrum.adicCompletion`, and the infinite
places those of `NumberField.InfinitePlace`, with completion `NumberField.InfinitePlace.Completion`
(`ℝ` or `ℂ`). That a smooth geometrically irreducible curve has points over all but finitely many
`K_v` is not proved here.

## Main definitions

* `AlgebraicGeometry.Scheme.PointOver` (LMFDB `g2c.all_rational_points`): the `L`-points of a
  scheme over `K`, the rational points for `L = K`.
* `AlgebraicGeometry.Scheme.PointOver.map`: the map `X(L) → X(L')` induced by a `K`-algebra
  homomorphism `L → L'`.
* `AlgebraicGeometry.Scheme.IsLocallySolvable` (LMFDB `g2c.locally_solvable`): locally solvable
  schemes over a number field.

## Main results

* `AlgebraicGeometry.Scheme.isLocallySolvable_of_nonempty`: a scheme with a rational point is
  locally solvable.
-/

universe u

open CategoryTheory NumberField

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

variable (K) in
/-- The **`L`-points** of a scheme `X` over a field `K`, for a `K`-algebra `L`: the morphisms
`Spec L ⟶ X` over `Spec K`. For `L = K` they are the **rational points** `X(K)` (LMFDB
`g2c.all_rational_points`). -/
def PointOver (L : Type u) [CommRing L] [Algebra K L] : Type u :=
  {f : Spec (.of L) ⟶ X // f ≫ X ↘ Spec (.of K) = Spec.map (CommRingCat.ofHom (algebraMap K L))}

variable {X}

/-- The map `X(L) → X(L')` induced by a homomorphism of `K`-algebras `φ : L → L'`. -/
noncomputable def PointOver.map {L L' : Type u} [CommRing L] [Algebra K L] [CommRing L']
    [Algebra K L'] (φ : L →ₐ[K] L') (P : X.PointOver K L) : X.PointOver K L' :=
  ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P.1, by
    rw [Category.assoc, P.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (Spec.map ∘ CommRingCat.ofHom) φ.comp_algebraMap⟩

lemma hasPointIn_of_nonempty {L : Type u} [Field L] [Algebra K L] (h : Nonempty (X.PointOver K K)) :
    X.HasPointIn K L :=
  h.elim fun P ↦ ⟨_, (P.map (Algebra.ofId K L)).2⟩

variable [NumberField K]

variable (K X) in
/-- A scheme `X` over a number field `K`, typically a curve, is **locally solvable** (LMFDB
`g2c.locally_solvable`) if it has a point over every completion of `K`: over the completion
`K_v` at every finite place `v`, a height one prime of `𝓞 K` (`ℚ_p` for `K = ℚ`), and over the
completion at every infinite place (`ℝ` for `K = ℚ`). -/
def IsLocallySolvable : Prop :=
  (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), X.HasPointIn K (v.adicCompletion K)) ∧
    ∀ w : InfinitePlace K, X.HasPointIn K w.Completion

/-- **A scheme with a rational point is locally solvable.** -/
lemma isLocallySolvable_of_nonempty (h : Nonempty (X.PointOver K K)) : IsLocallySolvable K X :=
  ⟨fun _ ↦ hasPointIn_of_nonempty h, fun _ ↦ hasPointIn_of_nonempty h⟩

end AlgebraicGeometry.Scheme
