import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Standard generators of the fundamental group of a punctured Riemann surface

For a Riemann surface `Y`, a set `B` of points of `Y` and a base point `y₀` of `Y - B`, a standard
generator of `π₁(Y - B, y₀)` at `b ∈ B` is the homotopy class of a loop that starts at `y₀` and
makes a counterclockwise loop about `b` containing no other point of `B`: it runs along a path to
the boundary of a disc about `b` in a chart of `Y` whose only point of `B` is `b`, goes once
counterclockwise around the boundary circle, and returns along the same path. Its class depends on
the path, so standard generators for `π₁(Y - B, y₀)` are such classes chosen coherently, one at
each point of `B`: they generate `π₁(Y - B, y₀)`, and their product is `1` when `B` is listed in a
suitable order, as for the classes of loops around the points of `B` that meet only at `y₀`. The
LMFDB takes `Y` compact of genus `0`, that is the Riemann sphere, and `B` finite, the branch points
of a quotient map; the definitions make sense on any Riemann surface.

## Main definitions

* `TauCeti.RiemannSurface.IsolatingDisc`: a closed disc in a chart about `b` whose only point of `B`
  is `b`.
* `TauCeti.RiemannSurface.IsolatingDisc.basePoint`: the point of its boundary circle where the
  circle starts.
* `TauCeti.RiemannSurface.IsolatingDisc.loop`: its boundary circle, traversed counterclockwise.
* `TauCeti.RiemannSurface.IsStandardGenerator` (LMFDB `curve.highergenus.aut.generators`): the
  standard generators of `π₁(Y - B, y₀)` at a point of `B`.
* `TauCeti.RiemannSurface.IsStandardGeneratingSystem` (LMFDB `curve.highergenus.aut.generators`):
  standard generators for `π₁(Y - B, y₀)`, one at each point of `B`.

## Main results

* `TauCeti.RiemannSurface.exists_isStandardGenerator`: when `B` is finite and `Y - B` is path
  connected, there is a standard generator at every point of `B`.
-/

open Metric Real Set Topology

namespace TauCeti.RiemannSurface

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] {B : Set Y} {b : Y}

variable (B b) in
/-- A **disc isolating `b` in `B`**: a closed disc `|z - e b| ≤ r` of positive radius in a chart `e`
of `Y` at `b`, contained in the target of the chart, whose only point of `B` is `b`. -/
structure IsolatingDisc where
  /-- The chart. -/
  chart : OpenPartialHomeomorph Y ℂ
  /-- The chart belongs to the atlas of `Y`. -/
  chart_mem_atlas : chart ∈ atlas ℂ Y
  /-- The chart is defined at `b`. -/
  mem_source : b ∈ chart.source
  /-- The radius of the disc. -/
  radius : ℝ
  /-- The radius of the disc is positive. -/
  radius_pos : 0 < radius
  /-- The disc lies in the target of the chart. -/
  closedBall_subset_target : closedBall (chart b) radius ⊆ chart.target
  /-- The only point of `B` in the disc is `b`. -/
  eq_of_symm_mem : ∀ z ∈ closedBall (chart b) radius, chart.symm z ∈ B → z = chart b

namespace IsolatingDisc

variable (D : IsolatingDisc B b)

lemma symm_circleMap_notMem (θ : ℝ) : D.chart.symm (circleMap (D.chart b) D.radius θ) ∉ B :=
  fun h ↦ D.radius_pos.ne' <| circleMap_eq_center_iff.mp <|
    D.eq_of_symm_mem _ (circleMap_mem_closedBall _ D.radius_pos.le θ) h

/-- The point `e⁻¹(e b + r)` of the boundary circle of a disc isolating `b` in `B`, as a point of
`Y - B`. -/
noncomputable def basePoint : ↥Bᶜ :=
  ⟨D.chart.symm (circleMap (D.chart b) D.radius 0), D.symm_circleMap_notMem 0⟩

/-- The **boundary circle** of a disc isolating `b` in `B`, traversed once counterclockwise in the
chart: the loop `t ↦ e⁻¹(e b + r exp(2πit))` in `Y - B`. -/
noncomputable def loop : Path D.basePoint D.basePoint where
  toFun t := ⟨D.chart.symm (circleMap (D.chart b) D.radius (2 * π * t)), D.symm_circleMap_notMem _⟩
  continuous_toFun := by
    refine (D.chart.continuousOn_symm.comp_continuous ?_ fun t ↦
      D.closedBall_subset_target (circleMap_mem_closedBall _ D.radius_pos.le _)).subtype_mk _
    unfold circleMap
    fun_prop
  source' := by
    simp [basePoint]
  target' := by
    simp [basePoint, (periodic_circleMap _ _).eq]

end IsolatingDisc

lemma nonempty_isolatingDisc (hB : B.Finite) : Nonempty (IsolatingDisc B b) := by
  let e : OpenPartialHomeomorph Y ℂ := chartAt ℂ b
  have hb : b ∈ e.source := mem_chart_source ℂ b
  rcases isOpen_iff.mp e.open_target (e b) (e.map_source hb) with ⟨ε₁, hε₁, h₁⟩
  have hF : (e '' (e.source ∩ (B \ {b})))ᶜ ∈ 𝓝 (e b) := by
    refine ((hB.sdiff.inter_of_right _).image e).isClosed.isOpen_compl.mem_nhds ?_
    rintro ⟨y, ⟨hy, -, hyb⟩, h⟩
    exact hyb (e.injOn hy hb h)
  rcases Metric.mem_nhds_iff.mp hF with ⟨ε₂, hε₂, h₂⟩
  have hr₁ : min ε₁ ε₂ / 2 < ε₁ := by linarith [min_le_left ε₁ ε₂, lt_min hε₁ hε₂]
  have hr₂ : min ε₁ ε₂ / 2 < ε₂ := by linarith [min_le_right ε₁ ε₂, lt_min hε₁ hε₂]
  have hsub : closedBall (e b) (min ε₁ ε₂ / 2) ⊆ e.target := (closedBall_subset_ball hr₁).trans h₁
  refine ⟨⟨e, chart_mem_atlas ℂ b, hb, min ε₁ ε₂ / 2, by positivity, hsub, fun z hz hzB ↦ ?_⟩⟩
  by_contra hzb
  have hzt : z ∈ e.target := hsub hz
  have hez : e (e.symm z) = z := e.right_inv hzt
  refine h₂ (closedBall_subset_ball hr₂ hz) ⟨e.symm z, ⟨e.map_target hzt, hzB, fun h ↦ hzb ?_⟩, hez⟩
  rw [← hez, mem_singleton_iff.mp h]

variable (b) in
/-- A **standard generator** (LMFDB `curve.highergenus.aut.generators`) of the fundamental group
`π₁(Y - B, y₀)` at a point `b` of `B`: the homotopy class of a loop that starts at `y₀` and makes a
counterclockwise loop about `b` containing no other point of `B`. It runs along a path `δ` in
`Y - B` to the boundary of a closed disc about `b` in a chart of `Y` whose only point of `B` is `b`
(`TauCeti.RiemannSurface.IsolatingDisc`), goes once counterclockwise around the boundary circle
(`TauCeti.RiemannSurface.IsolatingDisc.loop`) and returns along `δ`. The LMFDB takes `Y` compact
of genus `0` and `B` finite; on a Riemann surface the transition maps of the atlas preserve the
orientation, so that counterclockwise does not depend on the chart. The class depends on the path
`δ`, and changing `δ` conjugates it: standard generators at all the points of `B` chosen coherently
are `TauCeti.RiemannSurface.IsStandardGeneratingSystem`. -/
def IsStandardGenerator (y₀ : ↥Bᶜ) (γ : FundamentalGroup ↥Bᶜ y₀) : Prop :=
  b ∈ B ∧ ∃ (D : IsolatingDisc B b) (δ : Path y₀ D.basePoint),
    γ = FundamentalGroup.fromPath ⟦δ.trans (D.loop.trans δ.symm)⟧

/-- **Standard generators** (LMFDB `curve.highergenus.aut.generators`) for the fundamental group
`π₁(Y - B, y₀)`: a family `(γ_b)_{b ∈ B}` in which `γ_b` is a standard generator at `b`
(`TauCeti.RiemannSurface.IsStandardGenerator`), the class of a loop that starts at `y₀` and makes a
counterclockwise loop about `b` containing no other point of `B`, such that the `γ_b` generate
`π₁(Y - B, y₀)` and have product `1` when `B` is listed in a suitable order. For `Y` compact of
genus `0` and `B` finite, as in the LMFDB, the classes of loops around the points of `B` that meet
only at `y₀`, listed in counterclockwise order around `y₀`, generate `π₁(Y - B, y₀)` subject to
this single relation, a classical fact not proved here; the knowl leaves the paths joining the loops
to `y₀` free, but generation and the relation, which the generating vectors of a group action rest
on, need such a coherent choice. Since any order of `B` is allowed, the relation does not depend on
the convention of `FundamentalGroup`, whose product `γ * δ` runs through `δ` first. -/
structure IsStandardGeneratingSystem (y₀ : ↥Bᶜ) (γ : B → FundamentalGroup ↥Bᶜ y₀) : Prop where
  /-- Each `γ_b` is a standard generator at `b`. -/
  isStandardGenerator (c : B) : IsStandardGenerator (c : Y) y₀ (γ c)
  /-- The `γ_b` generate the fundamental group. -/
  closure_range : Subgroup.closure (range γ) = ⊤
  /-- With `B` listed in a suitable order, the product of the `γ_b` is `1`. -/
  exists_prod_eq_one : ∃ l : List B, l.Nodup ∧ (∀ c, c ∈ l) ∧ (l.map γ).prod = 1

/-- **There is a standard generator at every point of a finite set `B`** of points of `Y` such that
`Y - B` is path connected, as for a finite set of points of a connected Riemann surface. -/
lemma exists_isStandardGenerator [PathConnectedSpace ↥Bᶜ] (hB : B.Finite) (y₀ : ↥Bᶜ) (hb : b ∈ B) :
    ∃ γ : FundamentalGroup ↥Bᶜ y₀, IsStandardGenerator b y₀ γ :=
  (nonempty_isolatingDisc hB).elim fun D ↦
    ⟨_, hb, D, PathConnectedSpace.somePath y₀ D.basePoint, rfl⟩

end TauCeti.RiemannSurface
