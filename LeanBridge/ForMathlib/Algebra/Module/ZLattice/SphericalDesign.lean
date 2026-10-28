import LeanBridge.ForMathlib.Algebra.Module.ZLattice.MinimalVectors
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Spherical designs and strongly perfect lattices

A finite nonempty set of points on the sphere of radius `r > 0` of `ℝⁿ` is a spherical `t`-design
if the average over the points of every real polynomial of degree at most `t` equals its average
over the sphere. A lattice is a spherical `t`-design lattice if its minimal vectors form a
spherical `t`-design, and strongly perfect if they form a spherical `4`-design. That `2`-design
lattices are the strongly eutactic ones, and that strongly perfect lattices are perfect, are not
formalised.

## Main definitions

* `EuclideanSpace.IsSphericalDesign` (LMFDB `lattice.spherical_design`).
* `ZLattice.IsSphericalDesign` (LMFDB `lattice.spherical_design`).
* `ZLattice.IsStronglyPerfect` (LMFDB `lattice.spherical_design`).

## Main results

* `EuclideanSpace.IsSphericalDesign.mono`: a spherical `t`-design is a spherical `s`-design for
  `s ≤ t`.
-/

open MeasureTheory

namespace EuclideanSpace

variable {ι : Type*} [Fintype ι] {s t : ℕ} {r : ℝ} {S : Set (EuclideanSpace ℝ ι)}

variable (t r S) in
/-- A set `S` of points of `ℝⁿ` is a **spherical `t`-design** (LMFDB `lattice.spherical_design`)
on the sphere of radius `r > 0` centred at `0` if it is finite and nonempty, lies on that sphere,
and for every real polynomial `f` in `n` variables of degree at most `t`, the average of `f` over
the sphere, for the rotation-invariant measure normalised to total mass `1`, equals the average
`(1/m) Σᵢ f(vᵢ)` over the `m` points of `S`. The sphere of radius `r` is parametrised by the unit
sphere via `x ↦ r x`, with the normalised surface measure `Measure.toSphere` of the Lebesgue
measure. -/
def IsSphericalDesign : Prop :=
  0 < r ∧ S.Finite ∧ S.Nonempty ∧ (∀ v ∈ S, ‖v‖ = r) ∧
    ∀ f : MvPolynomial ι ℝ, f.totalDegree ≤ t →
      ⨍ x : Metric.sphere (0 : EuclideanSpace ℝ ι) 1,
          f.eval (fun i ↦ r * (x : EuclideanSpace ℝ ι) i) ∂volume.toSphere =
        (Nat.card S : ℝ)⁻¹ * ∑ᶠ v ∈ S, f.eval fun i ↦ v i

/-- **A spherical `t`-design is a spherical `s`-design for every `s ≤ t`.** -/
lemma IsSphericalDesign.mono (h : IsSphericalDesign t r S) (hst : s ≤ t) :
    IsSphericalDesign s r S :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun f hf ↦ h.2.2.2.2 f (hf.trans hst)⟩

end EuclideanSpace

namespace ZLattice

variable {ι : Type*} [Fintype ι] (t : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ ι))

/-- A lattice `L` of `ℝⁿ` is a **spherical `t`-design lattice** (LMFDB `lattice.spherical_design`)
if its minimal vectors form a spherical `t`-design on the sphere of radius the length
`ZLattice.minimum L` of a shortest nonzero vector. -/
def IsSphericalDesign : Prop :=
  EuclideanSpace.IsSphericalDesign t (minimum L) (minimalVectors L)

/-- A lattice `L` of `ℝⁿ` is **strongly perfect** (LMFDB `lattice.spherical_design`) if it is a
spherical `4`-design lattice. That it is then perfect is not proved here. -/
def IsStronglyPerfect : Prop :=
  IsSphericalDesign 4 L

end ZLattice
