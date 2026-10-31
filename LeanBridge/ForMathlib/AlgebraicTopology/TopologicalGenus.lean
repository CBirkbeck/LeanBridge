import Mathlib.LinearAlgebra.Dimension.Finrank
import TauCeti.AlgebraicTopology.Cohomology.Basic

/-!
# The topological genus of a surface

The genus `g` of a compact connected orientable surface `X`, such as a compact Riemann surface, is
half its first Betti number: `H¹(X, ℤ) ≅ ℤ^{2g}`. We define the topological genus of a topological
space as half the rank of its first singular cohomology group with integral coefficients (Tau Ceti's
`TopCat.singularCohomology`), the rank being `0` if it is infinite, as for the Betti numbers of
`LeanBridge.ForMathlib.AlgebraicGeometry.HilbertModularSurface.EulerNumber`. For a space other than
a compact orientable surface it is just half the first Betti number. The classification of
surfaces, which makes `H¹(X, ℤ)` free of even rank `2g` for a compact connected orientable surface
of genus `g`, is not formalised.

## Main definitions

* `TopCat.topologicalGenus`: half the rank of `H¹(X, ℤ)`, the genus of a compact connected
  orientable surface.
-/

namespace TopCat

variable (X : TopCat.{0})

/-- The **topological genus** of a topological space `X`: half its first Betti number, the rank of
the singular cohomology group `H¹(X, ℤ)` (`0` if the rank is infinite). For a compact connected
orientable surface of genus `g`, such as a compact Riemann surface, `H¹(X, ℤ) ≅ ℤ^{2g}`, so this is
its genus. -/
noncomputable def topologicalGenus : ℕ :=
  Module.finrank ℤ (X.singularCohomology (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ ℤ) 1) / 2

end TopCat
