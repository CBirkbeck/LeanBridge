import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Monodromy

/-!
# Transitivity of the monodromy group

Let a finite group `G` act continuously on a locally compact Hausdorff space `X`, with quotient
`φ : X → Y = X/G` and branch points `B ⊆ Y`. If `X - φ⁻¹(B)` is path-connected, the monodromy group
(LMFDB `curve.highergenus.aut.monodromy`, `MulAction.monodromyGroup`) at a base point `y₀ ∈ Y - B`
acts transitively on the fibre `φ⁻¹(y₀)`: for points `e`, `e'` of the fibre, a path from `e` to `e'`
in `X - φ⁻¹(B)` projects to a loop at `y₀` whose monodromy sends `e` to `e'` (Mathlib's
`IsCoveringMap.monodromy_eq_of_map_eq`).

LeanBridge's monodromy group is defined for any continuous action on a locally compact Hausdorff
space, where the path-connectedness can fail, so transitivity is proved here under that hypothesis.
For a compact connected Riemann surface `X` and a finite group of holomorphic automorphisms, `B` is
finite and `X - φ⁻¹(B)` is path-connected, a connected surface minus finitely many points, and the
monodromy group is moreover independent of the base point up to conjugation:
`LeanBridge.ForMathlib.AlgebraicGeometry.Curve.MonodromyRiemannSurface`.

## Main results

* `MulAction.isPretransitive_monodromyGroup` (LMFDB `curve.highergenus.aut.monodromy`): if
  `X - φ⁻¹(B)` is path-connected, the monodromy group acts transitively on the fibre.
-/

open Path Set

namespace MulAction

variable (G X : Type*) [Group G] [MulAction G X] [Finite G] [TopologicalSpace X]
  [ContinuousConstSMul G X] [T2Space X] [LocallyCompactSpace X]

/-- **If `X - φ⁻¹(B)` is path-connected, the monodromy group acts transitively on the fibre**
(LMFDB `curve.highergenus.aut.monodromy`): a path between two points of the fibre over `y₀`
projects to a loop at `y₀` whose monodromy sends the first point to the second. -/
lemma isPretransitive_monodromyGroup
    [PathConnectedSpace (Quotient.mk'' ⁻¹' (branchPoints G X)ᶜ : Set X)]
    (y₀ : ↥(branchPoints G X)ᶜ) :
    IsPretransitive (monodromyGroup G X y₀) (unbranchedProjection G X ⁻¹' {y₀}) := by
  refine ⟨fun e e' ↦ ?_⟩
  have cov : IsCoveringMap (unbranchedProjection G X) := isCoveringMap_unbranchedProjection G X
  let Γ : Homotopic.Quotient e.1 e'.1 := .mk (PathConnectedSpace.somePath e.1 e'.1)
  let δ : Homotopic.Quotient (unbranchedProjection G X e.1) (unbranchedProjection G X e'.1) :=
    Γ.map ⟨_, cov.continuous⟩
  let γ : Homotopic.Quotient y₀ y₀ := δ.cast e.2.symm e'.2.symm
  have h : cov.monodromy γ e = e' :=
    cov.monodromy_eq_of_map_eq Γ ((δ.cast_cast _ _ _ _).trans δ.cast_rfl_rfl).symm
  exact ⟨⟨cov.monodromyPerm y₀ (.of γ), _, rfl⟩, h⟩

end MulAction
