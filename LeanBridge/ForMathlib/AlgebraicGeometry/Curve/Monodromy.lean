import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.BranchPoints
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting

/-!
# The monodromy group of a group of automorphisms of a Riemann surface

Let `G` be a finite group of automorphisms of a compact Riemann surface `X`, let `φ : X → Y = X/G`
be the natural projection and `B ⊆ Y` its set of branch points. Over `Y - B` the group `G` acts
freely, and the restriction `X - φ⁻¹(B) → Y - B` of `φ` is a covering map, with fibres of `|G|`
points. For a base point `y₀ ∈ Y - B`, lifting loops at `y₀` gives the monodromy action of
`π₁(Y - B, y₀)` on the fibre `φ⁻¹(y₀)`, and the monodromy group (LMFDB
`curve.highergenus.aut.monodromy`) is the image of `π₁(Y - B, y₀)` in the permutations of
`φ⁻¹(y₀)`, a permutation group of degree `d = |G|`.

The definitions only use the topology: `X` is any locally compact Hausdorff space with a continuous
action of a finite group `G`, and `Y` carries the quotient topology. The transitivity of the
monodromy group, which holds when `X - φ⁻¹(B)` is path connected, as for a connected Riemann
surface, and its independence of `y₀` up to conjugation, are not formalised. Note that
`FundamentalGroup` composes loops in the order opposite to path concatenation, so the monodromy is
a left action, while the knowl writes a right action; the image is the same group.

## Main definitions

* `MulAction.unbranchedProjection`: the covering `X - φ⁻¹(B) → Y - B`.
* `MulAction.monodromyGroup` (LMFDB `curve.highergenus.aut.monodromy`).

## Main results

* `MulAction.isCoveringMap_unbranchedProjection`: `X - φ⁻¹(B) → Y - B` is a covering map.
* `MulAction.card_fiber_unbranchedProjection`: its fibres have `|G|` points.
-/

open Set

namespace MulAction

variable (G X : Type*) [Group G] [MulAction G X]

/-- The restriction `X - φ⁻¹(B) → Y - B` of the natural projection `φ : X → Y = X/G` of a space
with an action of a group `G` to the complement of the set `B` of its branch points. -/
def unbranchedProjection :
    (Quotient.mk'' ⁻¹' (branchPoints G X)ᶜ : Set X) → ↥(branchPoints G X)ᶜ :=
  (branchPoints G X)ᶜ.restrictPreimage Quotient.mk''

variable [Finite G]

/-- **The fibres of `X - φ⁻¹(B) → Y - B` have `|G|` points.** -/
lemma card_fiber_unbranchedProjection (y₀ : ↥(branchPoints G X)ᶜ) :
    Nat.card (unbranchedProjection G X ⁻¹' {y₀}) = Nat.card G := by
  rcases y₀ with ⟨P, hP⟩
  induction P using Quotient.inductionOn' with | h x => ?_
  have hx (y : X) : (Quotient.mk'' y : orbitRel.Quotient G X) = Quotient.mk'' x ↔ y ∈ orbit G x :=
    Quotient.eq''
  let e : unbranchedProjection G X ⁻¹' {⟨Quotient.mk'' x, hP⟩} ≃ orbit G x :=
    { toFun z := ⟨z.1.1, (hx _).mp (congrArg Subtype.val z.2)⟩
      invFun w := ⟨⟨w.1, by rw [mem_preimage, (hx _).mpr w.2]; exact hP⟩,
        Subtype.ext ((hx _).mpr w.2)⟩
      left_inv z := rfl
      right_inv w := rfl }
  rw [Nat.card_congr e, Nat.card_congr (orbitEquivQuotientStabilizer G x), ← Subgroup.index,
    not_not.mp fun h ↦ hP ((mk_mem_branchPoints_iff x).mpr h), Subgroup.index_bot]

variable [TopologicalSpace X] [ContinuousConstSMul G X] [T2Space X] [LocallyCompactSpace X]

/-- **The restriction `X - φ⁻¹(B) → Y - B` of the projection to the quotient of a locally compact
Hausdorff space by a continuous action of a finite group is a covering map.** -/
lemma isCoveringMap_unbranchedProjection : IsCoveringMap (unbranchedProjection G X) := by
  have : ProperlyDiscontinuousSMul G X := ⟨fun _ _ ↦ toFinite _⟩
  refine (isCoveringMapOn_quotientMk_of_properlyDiscontinuousSMul.mono fun P hP ↦ ?_)
    |>.isCoveringMap_restrictPreimage
  induction P using Quotient.inductionOn' with | h x => ?_
  exact ⟨x, not_not.mp fun h ↦ hP ((mk_mem_branchPoints_iff x).mpr h), rfl⟩

/-- The **(geometric) monodromy group** (LMFDB `curve.highergenus.aut.monodromy`) of a finite group
`G` acting on a space `X`, such as a group of automorphisms of a compact Riemann surface, at a base
point `y₀` of `Y - B`, where `Y = X/G` and `B` is the set of branch points of `φ : X → Y`: the
image of the monodromy action of `π₁(Y - B, y₀)` on the fibre `φ⁻¹(y₀)`, a group of permutations
of a set of `|G|` points (`MulAction.card_fiber_unbranchedProjection`), obtained by lifting loops
to `X - φ⁻¹(B)`. -/
noncomputable def monodromyGroup (y₀ : ↥(branchPoints G X)ᶜ) :
    Subgroup (Equiv.Perm (unbranchedProjection G X ⁻¹' {y₀})) :=
  ((isCoveringMap_unbranchedProjection G X).monodromyPerm y₀).range

end MulAction
