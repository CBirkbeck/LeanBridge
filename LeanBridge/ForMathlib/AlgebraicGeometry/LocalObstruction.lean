import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.NumberTheory.Padics.PadicNumbers
import TauCeti.Data.Nat.Prime.Basic

/-!
# Local obstructions to rational points

A scheme `X` over `ℚ`, such as a modular curve, has a local obstruction (to rational points) if it
has no real points, or no `ℚ_p`-points for some prime `p`. For a field extension `L / K`, an
`L`-point of a scheme `X` over `K` is a `K`-morphism `Spec L → X`. A rational point gives points
over every extension of `ℚ`, so a scheme with a local obstruction has no rational point.

That a curve of genus `0` without local obstruction has a rational point (Hasse–Minkowski) is not
formalised.

## Main definitions

* `AlgebraicGeometry.Scheme.HasPointIn`: `X` has an `L`-point.
* `AlgebraicGeometry.Scheme.HasLocalObstruction` (LMFDB `modcurve.local_obstruction`): `X` has a
  local obstruction.

## Main results

* `AlgebraicGeometry.Scheme.not_hasLocalObstruction`: a scheme over `ℚ` with a rational point has
  no local obstruction.
-/

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- A scheme `X` over a field `K` **has an `L`-point**, for a field extension `L / K`, if there is a
`K`-morphism `Spec L → X`. -/
def HasPointIn (X : Scheme.{u}) (K L : Type u) [Field K] [Field L] [Algebra K L]
    [X.Over (Spec (.of K))] : Prop :=
  ∃ f : Spec (.of L) ⟶ X, f ≫ X ↘ Spec (.of K) = Spec.map (CommRingCat.ofHom (algebraMap K L))

variable {X : Scheme.{0}} [X.Over (Spec (.of ℚ))]

variable (X) in
/-- A scheme `X` over `ℚ` **has a local obstruction** (LMFDB `modcurve.local_obstruction`) if it has
no real points, or no `ℚ_p`-points for some prime `p`. -/
def HasLocalObstruction : Prop :=
  ¬X.HasPointIn ℚ ℝ ∨ ∃ p : Nat.Primes, ¬X.HasPointIn ℚ ℚ_[p]

lemma hasPointIn_of_comp_eq_id {L : Type} [Field L] [Algebra ℚ L] {f : Spec (.of ℚ) ⟶ X}
    (hf : f ≫ X ↘ Spec (.of ℚ) = 𝟙 _) : X.HasPointIn ℚ L :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap ℚ L)) ≫ f, by rw [Category.assoc, hf, Category.comp_id]⟩

/-- **A scheme over `ℚ` with a rational point has no local obstruction.** -/
lemma not_hasLocalObstruction {f : Spec (.of ℚ) ⟶ X} (hf : f ≫ X ↘ Spec (.of ℚ) = 𝟙 _) :
    ¬X.HasLocalObstruction := by
  rintro (h | ⟨_, h⟩) <;> exact h (hasPointIn_of_comp_eq_id hf)

end AlgebraicGeometry.Scheme
