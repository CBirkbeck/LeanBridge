import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.MonodromyTransitive
import TauCeti.Geometry.Manifold.Connected

/-!
# The monodromy group of a group of automorphisms of a compact Riemann surface

Let a finite group `G` act faithfully by holomorphic maps on a compact connected Riemann surface
`X`, with natural projection `φ : X → Y = X/G` and branch points `B ⊆ Y`. This file completes the
description of the monodromy group (LMFDB `curve.highergenus.aut.monodromy`,
`MulAction.monodromyGroup`) at a base point `y₀ ∈ Y - B`: it is a transitive permutation group of
the fibre `φ⁻¹(y₀)`, which has `|G|` points (`MulAction.card_fiber_unbranchedProjection`), and it
does not depend on the base point, up to the relabelling of the fibre by the monodromy along a path.

The set `B` is finite (`MulAction.finite_branchPoints`), hence so is `φ⁻¹(B)`, a finite union of
orbits, and a connected surface minus finitely many points is connected (Tau Ceti's
`TauCeti.isConnected_compl_of_finite_of_one_lt_rank`), hence path-connected, being an open subset of
a locally path-connected space. So `X - φ⁻¹(B)` is path-connected, and so is its image `Y - B`.
Transitivity follows by `MulAction.isPretransitive_monodromyGroup`. For two base points `y₀` and
`y₁` of `Y - B` and a path `δ` from `y₀` to `y₁` in `Y - B`, the monodromy along `δ` is a bijection
`φ⁻¹(y₀) ≃ φ⁻¹(y₁)`, and it conjugates the monodromy group at `y₀` to the one at `y₁`: the
monodromy of a loop `γ` at `y₀` corresponds to that of the loop `δ⁻¹ γ δ` at `y₁` (Mathlib's
`FundamentalGroup.fundamentalGroupMulEquivOfPath`). Since `Y - B` is path-connected, the monodromy
groups at any two base points are conjugate.

The knowl takes `X` of genus `g ≥ 2`, where every group of automorphisms of `X` is finite. Here the
genus is not modelled and `G` is assumed finite: Tau Ceti proves the finiteness for the automorphism
group of a function field of genus at least two (`TauCeti.finite_algEquiv_of_two_le_genus`), but
nothing relates a compact Riemann surface to its function field.

## Main definitions

* `IsCoveringMap.monodromyEquiv`: the monodromy along a path, a bijection between two fibres of a
  covering map.

## Main results

* `IsCoveringMap.range_monodromyPerm_eq_map`: the monodromy along a path from `x` to `y` conjugates
  the image of `π₁(X, x)` in the permutations of the fibre over `x` to the image of `π₁(X, y)`.
* `MulAction.monodromyGroup_eq_map_permCongrHom` (LMFDB `curve.highergenus.aut.monodromy`): the
  monodromy groups at two base points are conjugate by the monodromy along a path between them.
* `MulAction.pathConnectedSpace_preimage_compl_branchPoints`: `X - φ⁻¹(B)` is path-connected.
* `MulAction.pathConnectedSpace_compl_branchPoints`: `Y - B` is path-connected, so any two base
  points are joined by a path.
* `MulAction.isPretransitive_monodromyGroup_of_mdifferentiable` (LMFDB
  `curve.highergenus.aut.monodromy`): the monodromy group acts transitively on the fibre.
* `MulAction.exists_monodromyGroup_eq_map_permCongrHom` (LMFDB `curve.highergenus.aut.monodromy`):
  the monodromy groups at any two base points are conjugate.
* `MulAction.pathConnectedSpace_compl_branchPoints_of_subgroup` and
  `MulAction.isPretransitive_monodromyGroup_of_subgroup`: the same for a finite group of
  automorphisms of `X`, a finite subgroup of its group `TauCeti.Diff` of biholomorphisms.
-/

open Path Set

open scoped ContDiff Manifold

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p)
  {x y : X}

/-- The **monodromy along a path** `γ` from `x` to `y` of a covering map `p : E → X`, as a bijection
from the fibre over `x` onto the fibre over `y`: a point of the fibre over `x` goes to the endpoint
of the lift of `γ` starting at it. -/
noncomputable def monodromyEquiv (γ : Homotopic.Quotient x y) : p ⁻¹' {x} ≃ p ⁻¹' {y} :=
  .ofBijective (cov.monodromy γ) (cov.monodromy_bijective γ)

lemma monodromyEquiv_symm_apply (γ : Homotopic.Quotient x y) (e : p ⁻¹' {y}) :
    (cov.monodromyEquiv γ).symm e = cov.monodromy γ.symm e := by
  rw [Equiv.symm_apply_eq, monodromyEquiv, Equiv.ofBijective_apply, ← cov.monodromy_trans_apply,
    γ.symm_trans, cov.monodromy_refl, id]

lemma monodromyPerm_fundamentalGroupMulEquivOfPath (γ : Path x y) (g : FundamentalGroup X x) :
    cov.monodromyPerm y (FundamentalGroup.fundamentalGroupMulEquivOfPath γ g) =
      (cov.monodromyEquiv (.mk γ)).permCongr (cov.monodromyPerm x g) := by
  have h : (FundamentalGroup.fundamentalGroupMulEquivOfPath γ g).asHom =
      (.mk γ : Homotopic.Quotient x y).symm.trans (g.asHom.trans (.mk γ)) :=
    rfl
  ext e
  rw [coe_monodromyPerm, h, cov.monodromy_trans_apply, cov.monodromy_trans_apply,
    Equiv.permCongr_apply, monodromyEquiv_symm_apply]
  rfl

/-- **The monodromy along a path conjugates the monodromy groups at its endpoints**: for a path `γ`
from `x` to `y`, the image of `π₁(X, y)` in the permutations of the fibre over `y` is the image of
`π₁(X, x)` in the permutations of the fibre over `x`, transported by the monodromy along `γ`. -/
lemma range_monodromyPerm_eq_map (γ : Path x y) : (cov.monodromyPerm y).range =
    (cov.monodromyPerm x).range.map (cov.monodromyEquiv (.mk γ)).permCongrHom.toMonoidHom := by
  let φ : FundamentalGroup X x ≃* FundamentalGroup X y :=
    FundamentalGroup.fundamentalGroupMulEquivOfPath γ
  have h : (cov.monodromyEquiv (.mk γ)).permCongrHom.toMonoidHom.comp (cov.monodromyPerm x) =
      (cov.monodromyPerm y).comp φ.toMonoidHom :=
    MonoidHom.ext fun g ↦ (cov.monodromyPerm_fundamentalGroupMulEquivOfPath γ g).symm
  rw [← MonoidHom.range_comp, h, MonoidHom.range_comp,
    φ.toMonoidHom.range_eq_top_of_surjective φ.surjective, ← MonoidHom.range_eq_map]

end IsCoveringMap

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X]

lemma surjective_unbranchedProjection : Function.Surjective (unbranchedProjection G X) :=
  (branchPoints G X)ᶜ.restrictPreimage_surjective Quotient.mk''_surjective

variable [Finite G]

lemma finite_preimage_branchPoints (hB : (branchPoints G X).Finite) :
    (Quotient.mk'' ⁻¹' branchPoints G X : Set X).Finite :=
  hB.preimage' fun P _ ↦ by
    induction P using Quotient.inductionOn' with | h x => ?_
    exact (finite_range fun g : G ↦ g • x).subset fun y hy ↦ Quotient.eq''.mp hy

variable [TopologicalSpace X]

variable [ContinuousConstSMul G X] [T2Space X] [LocallyCompactSpace X] in
/-- **The monodromy group does not depend on the base point** (LMFDB
`curve.highergenus.aut.monodromy`): for a path `δ` from `y₀` to `y₁` in `Y - B`, the monodromy along
`δ`, a bijection from the fibre over `y₀` onto the fibre over `y₁`, conjugates the monodromy group
at `y₀` to the monodromy group at `y₁`. For a group of automorphisms of a compact connected Riemann
surface, any two base points are joined by such a path
(`MulAction.pathConnectedSpace_compl_branchPoints`). -/
lemma monodromyGroup_eq_map_permCongrHom {y₀ y₁ : ↥(branchPoints G X)ᶜ} (δ : Path y₀ y₁) :
    monodromyGroup G X y₁ = (monodromyGroup G X y₀).map
      ((isCoveringMap_unbranchedProjection G X).monodromyEquiv (.mk δ)).permCongrHom.toMonoidHom :=
  (isCoveringMap_unbranchedProjection G X).range_monodromyPerm_eq_map δ

variable [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X] [ConnectedSpace X]
  [FaithfulSMul G X]

/-- **The complement `X - φ⁻¹(B)` of the fibres over the branch points is path-connected**, for a
finite group acting faithfully by holomorphic maps on a compact connected Riemann surface `X`: it is
a connected surface minus finitely many points. -/
lemma pathConnectedSpace_preimage_compl_branchPoints
    (hG : ∀ g : G, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g • · : X → X)) :
    PathConnectedSpace (Quotient.mk'' ⁻¹' (branchPoints G X)ᶜ : Set X) := by
  have hfin : (Quotient.mk'' ⁻¹' branchPoints G X : Set X).Finite :=
    finite_preimage_branchPoints (finite_branchPoints hG)
  have : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  rw [preimage_compl, ← isPathConnected_iff_pathConnectedSpace,
    ← hfin.isClosed.isOpen_compl.isConnected_iff_isPathConnected]
  exact TauCeti.isConnected_compl_of_finite_of_one_lt_rank (E := ℂ) (by simp) hfin

/-- **The complement `Y - B` of the branch points in the quotient is path-connected**, for a finite
group acting faithfully by holomorphic maps on a compact connected Riemann surface `X`: it is the
image of the path-connected `X - φ⁻¹(B)`. -/
lemma pathConnectedSpace_compl_branchPoints
    (hG : ∀ g : G, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g • · : X → X)) :
    PathConnectedSpace ↥(branchPoints G X)ᶜ :=
  have : PathConnectedSpace (Quotient.mk'' ⁻¹' (branchPoints G X)ᶜ : Set X) :=
    pathConnectedSpace_preimage_compl_branchPoints hG
  surjective_unbranchedProjection.pathConnectedSpace continuous_quotient_mk'.restrictPreimage

variable [ContinuousConstSMul G X] in
/-- **The monodromy group of a finite group of automorphisms of a compact connected Riemann surface
is transitive** (LMFDB `curve.highergenus.aut.monodromy`): for a finite group acting faithfully by
holomorphic maps on a compact connected Riemann surface `X`, the monodromy group at every base point
`y₀ ∈ Y - B` acts transitively on the fibre over `y₀`. -/
lemma isPretransitive_monodromyGroup_of_mdifferentiable
    (hG : ∀ g : G, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g • · : X → X)) (y₀ : ↥(branchPoints G X)ᶜ) :
    IsPretransitive (monodromyGroup G X y₀) (unbranchedProjection G X ⁻¹' {y₀}) :=
  have : PathConnectedSpace (Quotient.mk'' ⁻¹' (branchPoints G X)ᶜ : Set X) :=
    pathConnectedSpace_preimage_compl_branchPoints hG
  isPretransitive_monodromyGroup G X y₀

variable [ContinuousConstSMul G X] in
/-- **The monodromy group does not depend on the base point** (LMFDB
`curve.highergenus.aut.monodromy`): for a finite group acting faithfully by holomorphic maps on a
compact connected Riemann surface `X`, the monodromy groups at any two base points `y₀` and `y₁` of
`Y - B` are conjugate by a bijection between the fibres over `y₀` and `y₁`, the monodromy along a
path from `y₀` to `y₁` in `Y - B`. -/
lemma exists_monodromyGroup_eq_map_permCongrHom
    (hG : ∀ g : G, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g • · : X → X)) (y₀ y₁ : ↥(branchPoints G X)ᶜ) :
    ∃ e : unbranchedProjection G X ⁻¹' {y₀} ≃ unbranchedProjection G X ⁻¹' {y₁},
      monodromyGroup G X y₁ = (monodromyGroup G X y₀).map e.permCongrHom.toMonoidHom :=
  have : PathConnectedSpace ↥(branchPoints G X)ᶜ := pathConnectedSpace_compl_branchPoints hG
  ⟨_, monodromyGroup_eq_map_permCongrHom (PathConnectedSpace.somePath y₀ y₁)⟩

variable {n : ℕ∞ω} (H : Subgroup (TauCeti.Diff 𝓘(ℂ) X n)) [Finite H]

/-- **For a finite group of automorphisms of a compact connected Riemann surface `X`, a finite
subgroup of its group `TauCeti.Diff` of biholomorphisms, `Y - B` is path-connected.** -/
lemma pathConnectedSpace_compl_branchPoints_of_subgroup (hn : n ≠ 0) :
    PathConnectedSpace ↥(branchPoints H X)ᶜ :=
  pathConnectedSpace_compl_branchPoints fun g : H ↦ (g : X ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X).mdifferentiable hn

/-- **The monodromy group of a finite group of automorphisms of a compact connected Riemann surface
`X`, a finite subgroup of its group `TauCeti.Diff` of biholomorphisms, is transitive** (LMFDB
`curve.highergenus.aut.monodromy`). -/
lemma isPretransitive_monodromyGroup_of_subgroup (hn : n ≠ 0) (y₀ : ↥(branchPoints H X)ᶜ) :
    IsPretransitive (monodromyGroup H X y₀) (unbranchedProjection H X ⁻¹' {y₀}) :=
  isPretransitive_monodromyGroup_of_mdifferentiable
    (fun g : H ↦ (g : X ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X).mdifferentiable hn) y₀

end MulAction
