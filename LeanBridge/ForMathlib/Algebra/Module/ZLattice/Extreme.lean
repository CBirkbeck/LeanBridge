import LeanBridge.ForMathlib.Algebra.Module.ZLattice.MinimalVectors
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Extreme lattices

The packing density of a lattice `L` of `ℝⁿ` is the proportion of space filled by the balls of
radius `λ₁(L) / 2` centred at its points, where `λ₁(L)` is the length of a shortest nonzero vector:
the volume of such a ball divided by the covolume of `L`. A lattice is extreme if its packing
density is a local maximum among the lattices `g L`, `g ∈ GL_n(ℝ)` near the identity. Voronoi's
theorem, that a lattice is extreme exactly when it is perfect and eutactic, is not formalised.

## Main definitions

* `ZLattice.packingDensity` (LMFDB `lattice.density`): the packing density of a lattice of `ℝⁿ`.
* `ZLattice.IsExtreme` (LMFDB `lattice.extreme`).
-/

open MeasureTheory

namespace ZLattice

variable {ι : Type*} [Fintype ι] (L : Submodule ℤ (EuclideanSpace ℝ ι))

/-- The **packing density** of a lattice `L` of `ℝⁿ` (LMFDB `lattice.density`): the volume of a
ball of radius `λ₁(L) / 2`, half the length `ZLattice.minimum L` of a shortest nonzero vector,
divided by the covolume of `L`, the proportion of space filled by the packing of balls of that
radius centred at the points of `L`. It is meaningful for full lattices (`IsZLattice ℝ L` and
discrete); it is the `TauCeti.IntegralLattice.density` of LMFDB `lattice.density` for a realization
of a positive definite integral lattice, but it is defined for all real lattices, as extremality
requires. -/
noncomputable def packingDensity : ℝ :=
  volume.real (Metric.ball (0 : EuclideanSpace ℝ ι) (minimum L / 2)) / covolume L

lemma packingDensity_nonneg : 0 ≤ packingDensity L :=
  div_nonneg measureReal_nonneg ENNReal.toReal_nonneg

/-- A lattice `L` of `ℝⁿ` is **extreme** (LMFDB `lattice.extreme`) if its packing density is a
local maximum of the packing density: for some `ε > 0`, every lattice `g L`, where `g` is an
invertible linear map of `ℝⁿ` at operator-norm distance less than `ε` from the identity, has packing
density at most that of `L`. Every lattice near `L` is of this form, so this is the local maximality
of the density function on the space of lattices. Voronoi's theorem, that a lattice is extreme
exactly when it is perfect (`ZLattice.IsPerfect`) and eutactic (`ZLattice.IsEutactic`), is not
proved here. -/
def IsExtreme : Prop :=
  ∃ ε > 0, ∀ g : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι,
    ‖(g : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) - .id ℝ _‖ < ε →
      packingDensity (L.map (g.toLinearMap.restrictScalars ℤ)) ≤ packingDensity L

end ZLattice
