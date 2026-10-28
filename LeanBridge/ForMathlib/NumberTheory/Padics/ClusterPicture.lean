import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.NumberTheory.Padics.Complex

/-!
# Cluster pictures

Let `H : y² = f(x)` be an elliptic or hyperelliptic curve over `ℚ` and `p` an odd prime. A cluster
of `f` at `p` is a nonempty set of roots of `f` in the algebraic closure `ℚ̄_p` of the form
`R ∩ D` for the set `R` of roots of `f` and a closed `p`-adic disc `D`. Its size is its number of
roots, and its depth is the `p`-adic valuation `-log_p r` of the radius `r` of a minimal disc
containing it; since the norm is nonarchimedean, `r` is the diameter of the cluster, the largest
`|α - β|` for roots `α, β` in it. The relative depth of a cluster is its depth minus that of the
smallest cluster strictly containing it. The cluster picture of `H` at `p` is the set of clusters,
drawn with their relative depths, and with the depth of the top cluster of all the roots.

The cluster picture depends on the model `y² = f(x)`, so it is attached here to the polynomial
`f ∈ ℚ[X]`. The definitions make sense for any prime `p`; the LMFDB takes `p` odd. The depth is
meaningful for clusters of at least two roots: a single root has infinite depth, and is drawn
without one, whereas the formula below gives it depth `0`. The relative depth of the top cluster is
its depth, as the intersection of the empty family of larger clusters is everything. That the
clusters form a tree under inclusion (two clusters are disjoint or nested) is not formalised.

## Main definitions

* `Polynomial.IsPadicCluster` (LMFDB `ag.cluster_picture`): the clusters of `f` at `p`, which
  form the cluster picture.
* `Polynomial.padicClusterSize` (LMFDB `ag.cluster_picture`): the size of a cluster.
* `Polynomial.padicClusterDepth` (LMFDB `ag.cluster_picture`): the depth of a cluster.
* `Polynomial.padicClusterParent`: the smallest cluster strictly containing a cluster.
* `Polynomial.padicClusterRelDepth` (LMFDB `ag.cluster_picture`): the relative depth of a cluster.

## Main results

* `Polynomial.isPadicCluster_rootSet`: the set of all roots of a polynomial with a root is a
  cluster, the top cluster.
-/

namespace Polynomial

variable (p : ℕ) [Fact p.Prime] (f : ℚ[X]) (s : Set (PadicAlgCl p))

/-- A **cluster** (LMFDB `ag.cluster_picture`) of a polynomial `f ∈ ℚ[X]` at a prime `p`: a
nonempty set of roots of `f` in `ℚ̄_p` cut out by a closed `p`-adic disc. The **cluster picture**
of `y² = f(x)` at `p` is the set of these clusters, with their depths. -/
def IsPadicCluster : Prop :=
  s.Nonempty ∧ ∃ z r, s = f.rootSet (PadicAlgCl p) ∩ Metric.closedBall z r

/-- The **size** (LMFDB `ag.cluster_picture`) of a cluster: the number of roots it contains. -/
noncomputable def padicClusterSize : ℕ :=
  s.ncard

/-- The **depth** (LMFDB `ag.cluster_picture`) of a cluster: the `p`-adic valuation `-log_p r` of
the radius `r` of a minimal disc containing it, which is its diameter `max |α - β|` since the norm
is nonarchimedean. It is meaningful for clusters of at least two roots. -/
noncomputable def padicClusterDepth : ℝ :=
  -Real.logb p (Metric.diam s)

/-- The smallest cluster of `f` strictly containing a set `s` of roots: the intersection of the
clusters strictly containing `s`, which form a chain. -/
def padicClusterParent : Set (PadicAlgCl p) :=
  ⋂₀ {t | f.IsPadicCluster p t ∧ s ⊂ t}

/-- The **relative depth** (LMFDB `ag.cluster_picture`) of a cluster: its depth minus the depth of
the smallest cluster strictly containing it. For the top cluster, which contains all the roots, it
is its depth. -/
noncomputable def padicClusterRelDepth : ℝ :=
  padicClusterDepth p s - padicClusterDepth p (f.padicClusterParent p s)

/-- **The set of all the roots of `f` is a cluster**, the top cluster, when `f` has a root. -/
lemma isPadicCluster_rootSet (hf : (f.rootSet (PadicAlgCl p)).Nonempty) :
    f.IsPadicCluster p (f.rootSet (PadicAlgCl p)) := by
  rcases hf with ⟨z, hz⟩
  exact ⟨⟨z, hz⟩, z, Metric.diam (f.rootSet (PadicAlgCl p)), Set.left_eq_inter.mpr fun _ hx ↦
    Metric.dist_le_diam_of_mem (f.rootSet_finite (PadicAlgCl p)).isBounded hx hz⟩

end Polynomial
