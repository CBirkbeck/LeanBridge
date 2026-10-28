import LeanBridge.ForMathlib.GroupTheory.MinimalNormal
import LeanBridge.ForMathlib.GroupTheory.SubnormalSeries
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Chief series and composition series

A chief series of a group `G` is a normal series `1 = N₀ ⊴ N₁ ⊴ ⋯ ⊴ Nₖ = G` in which each
`Nᵢ₊₁ / Nᵢ` is a minimal normal subgroup of `G / Nᵢ`. Its factors are products of copies of a
simple group; these simple groups, with multiplicities, are the composition factors of `G`, which
are also the factors of a composition series, a subnormal series whose factors are all simple. We
define chief and composition series and the factor groups of a subnormal series. That the
composition factors are well defined (the Jordan–Hölder theorem) and that each chief factor is a
power of a simple group are not proved here.

## Main definitions

* `Subgroup.NormalSeries.IsChief` (LMFDB `group.chief_series`): a chief series.
* `Subgroup.SubnormalSeries.factor` (LMFDB `group.chief_series`): the factor groups
  `Hᵢ₊₁ / Hᵢ` of a subnormal series.
* `Subgroup.SubnormalSeries.IsComposition` (LMFDB `group.chief_series`): a composition series,
  whose factors are the composition factors of `G`.
-/

namespace Subgroup

variable {G : Type*} [Group G]

namespace SubnormalSeries

variable (s : SubnormalSeries G) (i : Fin s.length)

/-- The `i`-th **factor group** `Hᵢ₊₁ / Hᵢ` of a subnormal series `(Hᵢ)` of `G`. -/
abbrev factor : Type _ :=
  s i.succ ⧸ (s i.castSucc).subgroupOf (s i.succ)

/-- A **composition series** of `G` (LMFDB `group.chief_series`): a subnormal series all of whose
factor groups are simple. Its factors are the **composition factors** of `G`. -/
def IsComposition : Prop :=
  ∀ i : Fin s.length, IsSimpleGroup (s.factor i)

end SubnormalSeries

namespace NormalSeries

instance (s : NormalSeries G) (i : Fin (s.length + 1)) : (s i).Normal :=
  s.normal i

/-- A **chief series** of `G` (LMFDB `group.chief_series`): a normal series
`1 = N₀ ⊴ N₁ ⊴ ⋯ ⊴ Nₖ = G` such that each `Nᵢ₊₁ / Nᵢ` is a minimal normal subgroup of
`G / Nᵢ`. -/
def IsChief (s : NormalSeries G) : Prop :=
  ∀ i : Fin s.length, ((s i.succ).map (QuotientGroup.mk' (s i.castSucc))).IsMinimalNormal

end NormalSeries

end Subgroup
