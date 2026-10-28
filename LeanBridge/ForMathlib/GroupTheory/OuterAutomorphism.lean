import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The outer automorphism group

The inner automorphisms of a group `G` form the range of `MulAut.conj : G →* MulAut G`; this
subgroup is normal, and the quotient is the outer automorphism group `Out(G)`.

## Main definitions

* `MulAut.Out` (LMFDB `group.outer_aut`): the outer automorphism group `Aut(G) / Inn(G)`.
* `MulAut.IsOuter` (LMFDB `group.outer_aut`): an automorphism that is not inner.

## Main results

* The instance `(MulAut.conj : G →* MulAut G).range.Normal`: the inner automorphisms form a normal
  subgroup of the automorphism group.
* `MulAut.isOuter_iff_ne_one`: an automorphism is outer exactly when its class in `Out(G)` is
  nontrivial.
-/

namespace MulAut

variable {G : Type*} [Group G]

instance : (conj : G →* MulAut G).range.Normal where
  conj_mem := by
    rintro - ⟨g, rfl⟩ σ
    exact ⟨σ g, by ext x; simp⟩

variable (G) in
/-- The **outer automorphism group** `Out(G) = Aut(G) / Inn(G)` (LMFDB `group.outer_aut`): the
automorphism group of `G` modulo the normal subgroup of inner automorphisms. -/
abbrev Out : Type _ :=
  MulAut G ⧸ (conj : G →* MulAut G).range

/-- An automorphism of `G` is an **outer automorphism** (LMFDB `group.outer_aut`) if it is not an
inner automorphism. -/
def IsOuter (σ : MulAut G) : Prop :=
  σ ∉ (conj : G →* MulAut G).range

/-- **An automorphism is outer exactly when its class in `Out(G)` is nontrivial.** -/
lemma isOuter_iff_ne_one (σ : MulAut G) : σ.IsOuter ↔ (σ : Out G) ≠ 1 :=
  (QuotientGroup.eq_one_iff σ).not.symm

end MulAut
