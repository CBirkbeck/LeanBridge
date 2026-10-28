import LeanBridge.ForMathlib.GroupTheory.PolycyclicPresentation

/-!
# Supersolvable groups

## Main definitions

* `Group.IsSupersolvable` (LMFDB `group.supersolvable`): a group with a normal series with cyclic
  factors.
-/

namespace Group

variable (G : Type*) [Group G]

/-- A group `G` is **supersolvable** (LMFDB `group.supersolvable`) if it has a normal series
`⊥ = N₀ ≤ N₁ ≤ ⋯ ≤ Nₖ = ⊤`, all of whose terms are normal in `G`, with cyclic factors `Nᵢ₊₁ / Nᵢ`.

The LMFDB asks for strict inclusions; repeated terms give trivial, hence cyclic, factors and can be
removed, so the two definitions agree. -/
def IsSupersolvable : Prop :=
  ∃ s : Subgroup.NormalSeries G, s.IsPolycyclic

end Group
