import LeanBridge.ForMathlib.Algebra.Module.ZLattice.PerfectHexagonal
import LeanBridge.ForMathlib.Algebra.Module.ZLattice.Voronoi

/-!
# The hexagonal lattice is extreme

The hexagonal lattice of `ℝ²` (`ZLattice.hexagonalLattice`, spanned by `(1, 0)` and
`(1 / 2, √3 / 2)`) is perfect (`ZLattice.isPerfect_hexagonalLattice`) and strongly eutactic
(`ZLattice.isStronglyEutactic_hexagonalLattice`), so by Voronoi's theorem it is extreme (LMFDB
`lattice.extreme`): extreme lattices, and lattices that are both perfect and eutactic, exist.

## Main results

* `ZLattice.isExtreme_hexagonalLattice` (LMFDB `lattice.extreme`): the hexagonal lattice is
  extreme.
-/

namespace ZLattice

/-- **The hexagonal lattice is extreme** (LMFDB `lattice.extreme`): it is perfect
(`ZLattice.isPerfect_hexagonalLattice`) and eutactic, hence extreme by Voronoi's theorem
(`ZLattice.IsPerfect.isExtreme`). -/
lemma isExtreme_hexagonalLattice : IsExtreme hexagonalLattice := by
  have hd : DiscreteTopology hexagonalLattice := isPerfect_hexagonalLattice.discreteTopology
  have hz : IsZLattice ℝ hexagonalLattice := isPerfect_hexagonalLattice.isZLattice
  exact isPerfect_hexagonalLattice.isExtreme isStronglyEutactic_hexagonalLattice.isEutactic

end ZLattice
