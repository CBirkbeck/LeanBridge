import LeanBridge.ForMathlib.NumberTheory.Padics.ClusterPicture
import Mathlib.Data.EReal.Operations

/-!
# The tree of clusters and the depths of a cluster picture

The `p`-adic norm is nonarchimedean, so two closed discs are nested or disjoint, and so are two
clusters of roots of a polynomial `f`. Hence the clusters strictly containing a cluster `s` other
than the top cluster form a nonempty finite chain, whose least element is their intersection
`Polynomial.padicClusterParent`: the smallest other cluster containing `s` is a cluster.

In an ultrametric space every point of a disc is a centre, so the minimal radius of a closed disc
containing a nonempty bounded set is its diameter. The depth of a cluster, the valuation of the
radius of a minimal disc containing it, is therefore `-log_p` of its diameter for a cluster of at
least two roots, and `∞` for a single root, which lies in a disc of radius `0`. The depth and the
relative depth are given here as extended reals, with these values.

## Main definitions

* `Polynomial.padicClusterValDepth` (LMFDB `ag.cluster_picture`): the depth of a cluster, `∞` for
  a single root.
* `Polynomial.padicClusterRelValDepth` (LMFDB `ag.cluster_picture`): the relative depth of a
  cluster, its depth for the top cluster.

## Main results

* `IsUltrametricDist.isLeast_diam`: in an ultrametric space, the diameter of a nonempty bounded set
  is the least radius of a closed disc containing it.
* `Polynomial.IsPadicCluster.subset_or_subset_or_disjoint` (LMFDB `ag.cluster_picture`): two
  clusters are nested or disjoint.
* `Polynomial.IsPadicCluster.isPadicCluster_padicClusterParent` and
  `Polynomial.IsPadicCluster.ssubset_padicClusterParent` (LMFDB `ag.cluster_picture`): the smallest
  cluster strictly containing a cluster other than the top cluster is a cluster.
-/

open Metric Set

/-- **In an ultrametric space, the diameter of a nonempty bounded set is the least radius of a
closed disc containing it**: every point of the set is the centre of such a disc. -/
lemma IsUltrametricDist.isLeast_diam {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X]
    {s : Set X} (hs : s.Nonempty) (hb : Bornology.IsBounded s) :
    IsLeast {r | ∃ z, s ⊆ closedBall z r} (diam s) := by
  rcases hs with ⟨a, ha⟩
  refine ⟨⟨a, fun x hx ↦ dist_le_diam_of_mem hb hx ha⟩, fun r ⟨z, hz⟩ ↦ ?_⟩
  exact diam_le_of_forall_dist_le (dist_nonneg.trans (hz ha)) fun x hx y hy ↦
    (dist_triangle_max x z y).trans <| max_le (hz hx) <| dist_comm z y ▸ hz hy

namespace Polynomial

variable {p : ℕ} [Fact p.Prime] {f : ℚ[X]} {s t : Set (PadicAlgCl p)}

lemma IsPadicCluster.subset_rootSet (hs : f.IsPadicCluster p s) : s ⊆ f.rootSet (PadicAlgCl p) := by
  rcases hs with ⟨-, z, r, rfl⟩
  exact inter_subset_left

/-- **Two clusters are nested or disjoint** (LMFDB `ag.cluster_picture`), as two closed `p`-adic
discs are: the clusters form a tree under inclusion. -/
lemma IsPadicCluster.subset_or_subset_or_disjoint (hs : f.IsPadicCluster p s)
    (ht : f.IsPadicCluster p t) : s ⊆ t ∨ t ⊆ s ∨ Disjoint s t := by
  rcases hs with ⟨-, z, r, rfl⟩
  rcases ht with ⟨-, w, q, rfl⟩
  rcases IsUltrametricDist.closedBall_subset_trichotomy z w r q with h | h | h
  · exact .inl (inter_subset_inter_right _ h)
  · exact .inr (.inl (inter_subset_inter_right _ h))
  · exact .inr (.inr (h.mono inter_subset_right inter_subset_right))

lemma IsPadicCluster.padicClusterParent_mem (hs : f.IsPadicCluster p s)
    (hsR : s ≠ f.rootSet (PadicAlgCl p)) :
    f.padicClusterParent p s ∈ {t | f.IsPadicCluster p t ∧ s ⊂ t} := by
  have hR : f.rootSet (PadicAlgCl p) ∈ {t | f.IsPadicCluster p t ∧ s ⊂ t} :=
    ⟨f.isPadicCluster_rootSet p (hs.1.mono hs.subset_rootSet),
      hs.subset_rootSet.ssubset_of_ne hsR⟩
  have hfin : {t | f.IsPadicCluster p t ∧ s ⊂ t}.Finite :=
    (f.rootSet_finite (PadicAlgCl p)).finite_subsets.subset fun t ht ↦ ht.1.subset_rootSet
  rcases hfin.exists_minimal ⟨_, hR⟩ with ⟨t₀, ht₀, hmin⟩
  have hle (t : Set (PadicAlgCl p)) (ht : t ∈ {t | f.IsPadicCluster p t ∧ s ⊂ t}) : t₀ ⊆ t := by
    rcases ht₀.1.subset_or_subset_or_disjoint ht.1 with h | h | h
    · exact h
    · exact hmin ht h
    · exact absurd (disjoint_self.mp (h.mono ht₀.2.subset ht.2.subset)) hs.1.ne_empty
  rwa [padicClusterParent, (sInter_subset_of_mem ht₀).antisymm (subset_sInter hle)]

/-- **The smallest cluster strictly containing a cluster is a cluster** (LMFDB
`ag.cluster_picture`), for a cluster `s` other than the top cluster: the clusters strictly
containing `s` form a nonempty finite chain, and `padicClusterParent` is its least element. -/
lemma IsPadicCluster.isPadicCluster_padicClusterParent (hs : f.IsPadicCluster p s)
    (hsR : s ≠ f.rootSet (PadicAlgCl p)) : f.IsPadicCluster p (f.padicClusterParent p s) :=
  (hs.padicClusterParent_mem hsR).1

/-- **A cluster other than the top cluster is strictly contained in its parent** (LMFDB
`ag.cluster_picture`), the smallest cluster strictly containing it. -/
lemma IsPadicCluster.ssubset_padicClusterParent (hs : f.IsPadicCluster p s)
    (hsR : s ≠ f.rootSet (PadicAlgCl p)) : s ⊂ f.padicClusterParent p s :=
  (hs.padicClusterParent_mem hsR).2

lemma padicClusterParent_subset (ht : f.IsPadicCluster p t) (hst : s ⊂ t) :
    f.padicClusterParent p s ⊆ t :=
  sInter_subset_of_mem ⟨ht, hst⟩

variable (p s) in
open scoped Classical in
/-- The **depth** (LMFDB `ag.cluster_picture`) of a cluster `s`, as an extended real: the
valuation `-log_p r` of the radius `r` of a minimal disc containing it, which is its diameter
(`IsUltrametricDist.isLeast_diam`), and `∞` for a single root, which lies in a disc of radius
`0`. -/
noncomputable def padicClusterValDepth : EReal :=
  if s.Subsingleton then ⊤ else (padicClusterDepth p s : EReal)

variable (p f s) in
open scoped Classical in
/-- The **relative depth** (LMFDB `ag.cluster_picture`) of a cluster `s`, as an extended real: its
depth minus the depth of the smallest cluster strictly containing it (`padicClusterParent`, a
cluster by `IsPadicCluster.isPadicCluster_padicClusterParent`), so `∞` for a single root; for the
top cluster of all the roots, which the cluster picture labels with its depth, its depth. -/
noncomputable def padicClusterRelValDepth : EReal :=
  if s = f.rootSet (PadicAlgCl p) then padicClusterValDepth p s
  else padicClusterValDepth p s - padicClusterValDepth p (f.padicClusterParent p s)

end Polynomial
