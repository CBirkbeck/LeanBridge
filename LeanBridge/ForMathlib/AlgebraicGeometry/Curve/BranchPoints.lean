import Mathlib.GroupTheory.Index
import TauCeti.Geometry.Diffeomorphism.Action
import TauCeti.Geometry.Manifold.Complex.Chart

/-!
# Branch points of the quotient of a Riemann surface by a finite group

A finite group `G` of automorphisms of a compact Riemann surface `X` has a quotient `X/G`, the
compact Riemann surface whose points are the `G`-orbits of `X`, and the fibre of the natural
projection `φ : X → X/G` over an orbit is the orbit itself. By the orbit–stabiliser theorem it has
`|G|` points unless the points of the orbit have a nontrivial stabiliser. A holomorphic
automorphism other than the identity of a compact connected Riemann surface has finitely many fixed
points, by the identity theorem in a chart at an accumulation point of its fixed points, so all
but finitely many fibres of `φ` have `|G|` points. The others lie over the branch points.

The complex structure of `X/G` is not needed to define the branch points, and is not constructed.

## Main definitions

* `MulAction.branchPoints` (LMFDB `curve.highergenus.aut.branchpoints`): the branch points of the
  projection `X → X/G`.

## Main results

* `MDifferentiable.finite_fixedPoints`: a holomorphic self-map of a compact connected Riemann
  surface other than the identity has finitely many fixed points.
* `MulAction.mk_mem_branchPoints_iff`: the orbit of a point is a branch point if and only if the
  point has a nontrivial stabiliser.
* `MulAction.finite_branchPoints`: a finite group acting faithfully by holomorphic maps on a
  compact connected Riemann surface has finitely many branch points.
* `MulAction.finite_branchPoints_of_subgroup`: so does a finite group of automorphisms of a compact
  connected Riemann surface, a finite subgroup of its group `TauCeti.Diff` of biholomorphisms.
-/

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace MDifferentiable

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] {f : X → X}
  (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)

include hf

lemma eventually_apply_eq_self {x : X} (hx : f x = x) (h : ∃ᶠ y in 𝓝[≠] x, f y = y) :
    ∀ᶠ y in 𝓝 x, f y = y := by
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have hcx : x ∈ c.source := mem_chart_source ℂ x
  have hcs : c.source ∈ 𝓝 x := c.open_source.mem_nhds hcx
  have hF : AnalyticAt ℂ (fun z ↦ c (f (c.symm z))) (c x) := by
    have h₀ : AnalyticAt ℂ (fun z ↦ chartAt ℂ (f x) (f (c.symm z))) (c x) :=
      TauCeti.analyticAt_chartAt_comp_comp_chartAt_symm (.of_forall hf)
    rwa [hx] at h₀
  have hfreq : ∃ᶠ z in 𝓝[≠] (c x), c (f (c.symm z)) = z := by
    have h₁ : ∃ᶠ z in map c (𝓝[≠] x), c (f (c.symm z)) = z := by
      rw [frequently_map]
      exact (h.and_eventually (eventually_nhdsWithin_of_eventually_nhds hcs)).mono
        fun y ⟨hy, hys⟩ ↦ by rw [c.left_inv hys, hy]
    refine h₁.filter_mono ?_
    rw [c.map_nhdsWithin_eq hcx]
    refine nhdsWithin_mono _ ?_
    rintro _ ⟨y, ⟨hys, hyx⟩, rfl⟩ h
    exact hyx (c.injOn hys hcx h)
  have hev : ∀ᶠ z in 𝓝 (c x), c (f (c.symm z)) = z :=
    (hF.frequently_eq_iff_eventually_eq analyticAt_id).mp hfreq
  filter_upwards [(c.continuousAt hcx).eventually hev, hcs,
    hf.continuous.continuousAt.eventually (c.open_source.mem_nhds (hx.symm ▸ hcx))] with y hy hys
    hfys
  rw [c.left_inv hys] at hy
  exact c.injOn hfys hys hy

variable [T2Space X] [CompactSpace X] [PreconnectedSpace X]

/-- **A holomorphic self-map of a compact connected Riemann surface other than the identity has
finitely many fixed points**: near an accumulation point of its fixed points it is the identity by
the identity theorem in a chart, and the set of points near which it is the identity is clopen. -/
lemma finite_fixedPoints (hne : f ≠ id) : (fixedPoints f).Finite := by
  by_contra hinf
  apply hne
  rcases Infinite.exists_accPt_of_subset_isCompact hinf isCompact_univ (subset_univ _) with
    ⟨x₀, -, hx₀⟩
  have hclosed : IsClosed (fixedPoints f) := isClosed_eq hf.continuous continuous_id
  have hsub : {x | ∀ᶠ y in 𝓝 x, f y = y} ⊆ fixedPoints f := fun _ hy ↦ Eventually.self_of_nhds hy
  have hS : IsClopen {x | ∀ᶠ y in 𝓝 x, f y = y} := by
    refine ⟨isClosed_of_closure_subset fun x hx ↦ ?_, isOpen_setOfPred_eventually_nhds⟩
    by_contra hxS
    refine hxS (hf.eventually_apply_eq_self ?_ ?_)
    · exact hclosed.closure_subset (closure_mono hsub hx)
    · exact frequently_nhdsWithin_iff.mpr ((mem_closure_iff_frequently.mp hx).mono fun y hy ↦
        ⟨hsub hy, fun hyx ↦ hxS (hyx ▸ hy)⟩)
  have huniv : {x | ∀ᶠ y in 𝓝 x, f y = y} = univ := hS.eq_univ ⟨x₀,
    hf.eventually_apply_eq_self (hclosed.closure_subset (mem_closure_iff_clusterPt.mpr
      hx₀.clusterPt)) (accPt_iff_frequently_nhdsNE.mp hx₀)⟩
  exact funext fun x ↦ hsub (huniv.symm ▸ mem_univ x)

end MDifferentiable

namespace MulAction

variable (G X : Type*) [Group G] [MulAction G X]

/-- The **branch points** (LMFDB `curve.highergenus.aut.branchpoints`) of the natural projection
`φ : X → X/G` of a set `X` with an action of a group `G` onto its set `X/G` of orbits: the points
`P` of `X/G` whose fibre `φ⁻¹(P)`, the orbit `P` itself, has fewer than `|G|` points. For a finite
group `G` of automorphisms of a compact Riemann surface `X`, the quotient `X/G` is the compact
Riemann surface whose points are the `G`-orbits; its complex structure is not needed here. The
branch points are then the orbits of the points with a nontrivial stabiliser
(`MulAction.mk_mem_branchPoints_iff`), and there are finitely many of them
(`MulAction.finite_branchPoints`). A group of automorphisms acts faithfully; for an action that is
not faithful every orbit would be a branch point. -/
def branchPoints : Set (orbitRel.Quotient G X) :=
  {P | (Quotient.mk'' ⁻¹' {P} : Set X).ncard < Nat.card G}

variable {G X} [Finite G]

/-- **The orbit of a point is a branch point if and only if the point has a nontrivial
stabiliser**, by the orbit–stabiliser theorem. -/
lemma mk_mem_branchPoints_iff (x : X) :
    (Quotient.mk'' x : orbitRel.Quotient G X) ∈ branchPoints G X ↔ stabilizer G x ≠ ⊥ := by
  have hfib :
      (Quotient.mk'' ⁻¹' {(Quotient.mk'' x : orbitRel.Quotient G X)} : Set X) = orbit G x := by
    ext y
    exact Quotient.eq''
  rw [branchPoints, mem_ofPred_eq, hfib, ← index_stabilizer]
  refine ⟨fun h hbot ↦ (Subgroup.index_bot (G := G) ▸ hbot ▸ h).false, fun h ↦ ?_⟩
  exact (lt_mul_left (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    ((stabilizer G x).one_lt_card_iff_ne_bot.mpr h)).trans_eq (stabilizer G x).card_mul_index

variable [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [PreconnectedSpace X]

/-- **A finite group acting faithfully by holomorphic maps on a compact connected Riemann surface
has finitely many branch points**: all but finitely many fibres of the projection `X → X/G` have
`|G|` points, since the elements of `G` other than the identity have finitely many fixed points. -/
lemma finite_branchPoints [FaithfulSMul G X]
    (hG : ∀ g : G, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g • · : X → X)) : (branchPoints G X).Finite := by
  have hfin : {x : X | stabilizer G x ≠ ⊥}.Finite := by
    refine ((toFinite ({1}ᶜ : Set G)).biUnion fun g hg ↦ (hG g).finite_fixedPoints fun h ↦
      hg ?_).subset fun x hx ↦ ?_
    · exact eq_of_smul_eq_smul fun y ↦ (congrFun h y).trans (one_smul G y).symm
    · rcases (stabilizer G x).ne_bot_iff_exists_ne_one.mp hx with ⟨⟨g, hg⟩, hg1⟩
      exact mem_biUnion (fun h ↦ hg1 (Subtype.ext h)) hg
  refine (hfin.image Quotient.mk'').subset fun P hP ↦ ?_
  induction P using Quotient.inductionOn' with | h x => ?_
  exact ⟨x, (mk_mem_branchPoints_iff x).mp hP, rfl⟩

/-- **A finite group of automorphisms of a compact connected Riemann surface has finitely many
branch points**, for a finite subgroup of the group `TauCeti.Diff` of biholomorphisms. -/
lemma finite_branchPoints_of_subgroup {n : ℕ∞ω} (hn : n ≠ 0) (H : Subgroup (TauCeti.Diff 𝓘(ℂ) X n))
    [Finite H] : (branchPoints H X).Finite :=
  finite_branchPoints fun g ↦ (g : X ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X).mdifferentiable hn

end MulAction
