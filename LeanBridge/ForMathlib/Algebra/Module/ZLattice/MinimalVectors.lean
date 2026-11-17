import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Minimal vectors and eutactic lattices in a real inner product space

The minimal vectors of a lattice `L` in a real inner product space `E` are its nonzero vectors of
least norm. The lattice is eutactic if `⟪v, v⟫ = ∑ₓ cₓ ⟪v, x⟫²` for all `v ∈ E` and positive
coefficients `cₓ` indexed by its minimal vectors `x`, and strongly eutactic if the coefficients can
be taken equal. The finiteness of the similarity classes of eutactic lattices and the arithmeticity
of strongly eutactic lattices are not formalised. Unlike `TauCeti.IntegralLattice.minimalVectors`,
for integral lattices in rational spaces, these lattices need not be integral, as eutaxy and
perfection require.

The minimum bounds the norms of the nonzero vectors of `L` from below, and that of the image of `L`
under an invertible map is bounded by the norms of the images; a positive minimum makes `L`
discrete, and the minimum of a nonzero discrete `L` is positive and isolated: the other nonzero
vectors of `L` are longer than some `m > min L`.

## Main definitions

* `ZLattice.minimum` and `ZLattice.minimalVectors` (LMFDB `lattice.minimal_vector`).
* `ZLattice.IsEutactic` and `ZLattice.IsStronglyEutactic` (LMFDB `lattice.eutactic`).

## Main results

* `ZLattice.finite_minimalVectors`: a discrete subgroup has finitely many minimal vectors.
* `ZLattice.nonempty_minimalVectors`: a nonzero discrete subgroup has a minimal vector.
* `ZLattice.IsStronglyEutactic.isEutactic`: a strongly eutactic lattice is eutactic.
* `ZLattice.IsEutactic.span_minimalVectors`: a eutactic lattice is well-rounded: its minimal
  vectors span `E`.
-/

open Module Set

open scoped InnerProductSpace

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E) {x : E}

/-- The **minimum length** of a lattice `L` in a real inner product space: the infimum of the norms
of the nonzero vectors of `L`, and `0` for `L = ⊥`. For a discrete nonzero `L` it is attained
(`ZLattice.nonempty_minimalVectors`). The LMFDB's minimum `m(L)` (LMFDB `lattice.minimum`) is its
square, as for integral lattices in Tau Ceti's `TauCeti.IntegralLattice.minimum`. -/
noncomputable def minimum : ℝ :=
  sInf (norm '' ((L : Set E) \ {0}))

/-- The **minimal vectors** (LMFDB `lattice.minimal_vector`) of a lattice `L` in a real inner
product space: the nonzero vectors of `L` of least norm `ZLattice.minimum L`. -/
def minimalVectors : Set E :=
  {x | x ∈ L ∧ x ≠ 0 ∧ ‖x‖ = minimum L}

variable {L}

lemma minimum_nonneg : 0 ≤ minimum L :=
  Real.sInf_nonneg fun _ ⟨x, _, hx⟩ ↦ hx ▸ norm_nonneg x

lemma minimum_le_norm (hx : x ∈ L) (hx₀ : x ≠ 0) : minimum L ≤ ‖x‖ :=
  csInf_le ⟨0, by rintro _ ⟨y, -, rfl⟩; exact norm_nonneg y⟩ ⟨x, ⟨hx, hx₀⟩, rfl⟩

lemma minimum_pos_of_mem_minimalVectors (hx : x ∈ minimalVectors L) : 0 < minimum L :=
  hx.2.2 ▸ norm_pos_iff.mpr hx.2.1

lemma discreteTopology_of_minimum_pos (h : 0 < minimum L) : DiscreteTopology L :=
  .of_forall_le_norm h fun x hx ↦ minimum_le_norm x.2 fun h0 ↦ hx (Subtype.ext h0)

variable [InnerProductSpace ℝ E] (g : E ≃L[ℝ] E)

lemma minimum_map_le_norm (hx : x ∈ L) (hx0 : x ≠ 0) :
    minimum (L.map (g.toLinearMap.restrictScalars ℤ)) ≤ ‖g x‖ :=
  minimum_le_norm (Submodule.mem_map_of_mem hx) (g.toLinearEquiv.map_ne_zero_iff.mpr hx0)

lemma le_minimum_map {m : ℝ} (hL : L ≠ ⊥) (h : ∀ x ∈ L, x ≠ 0 → m ≤ ‖g x‖) :
    m ≤ minimum (L.map (g.toLinearMap.restrictScalars ℤ)) := by
  rcases L.ne_bot_iff.mp hL with ⟨x, hx, hx0⟩
  refine le_csInf
    ⟨‖g x‖, g x, ⟨Submodule.mem_map_of_mem hx, g.toLinearEquiv.map_ne_zero_iff.mpr hx0⟩, rfl⟩ ?_
  rintro _ ⟨_, ⟨⟨y, hy, rfl⟩, hy0⟩, rfl⟩
  exact h y hy fun h0 ↦ hy0 (by simp [h0])

variable (L) in
/-- A lattice `L` in a real inner product space `E` is **eutactic** (LMFDB `lattice.eutactic`) if
there are positive real numbers `cₓ`, indexed by the minimal vectors `x` of `L`, such that
`⟪v, v⟫ = ∑ₓ cₓ ⟪v, x⟫²` for every `v ∈ E`. The sum is finite for a discrete `L`
(`ZLattice.finite_minimalVectors`). -/
def IsEutactic : Prop :=
  ∃ c : E → ℝ, (∀ x ∈ minimalVectors L, 0 < c x) ∧
    ∀ v : E, ⟪v, v⟫_ℝ = ∑ᶠ x ∈ minimalVectors L, c x * ⟪v, x⟫_ℝ ^ 2

variable (L) in
/-- A lattice `L` in a real inner product space `E` is **strongly eutactic** (LMFDB
`lattice.eutactic`) if it is eutactic with equal coefficients: `⟪v, v⟫ = c ∑ₓ ⟪v, x⟫²` for every
`v ∈ E`, for a positive real number `c`, the sum ranging over the minimal vectors `x` of `L`. -/
def IsStronglyEutactic : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ v : E, ⟪v, v⟫_ℝ = c * ∑ᶠ x ∈ minimalVectors L, ⟪v, x⟫_ℝ ^ 2

/-- **A strongly eutactic lattice is eutactic.** -/
lemma IsStronglyEutactic.isEutactic (h : IsStronglyEutactic L) : IsEutactic L := by
  rcases h with ⟨c, hc, h⟩
  exact ⟨fun _ ↦ c, fun _ _ ↦ hc, fun v ↦ (h v).trans (mul_finsum_mem _ c)⟩

variable [FiniteDimensional ℝ E]

/-- **A eutactic lattice is well-rounded** (LMFDB `lattice.well_rounded`): its minimal vectors span
`E`. -/
lemma IsEutactic.span_minimalVectors (h : IsEutactic L) :
    Submodule.span ℝ (minimalVectors L) = ⊤ := by
  rcases h with ⟨c, -, h⟩
  refine Submodule.orthogonal_eq_bot_iff.mp <| (Submodule.eq_bot_iff _).mpr fun v hv ↦ ?_
  have hzero : ∀ x ∈ minimalVectors L, c x * ⟪v, x⟫_ℝ ^ 2 = 0 := fun x hx ↦ by
    rw [Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span hx) hv]
    ring1
  rw [← inner_self_eq_zero (𝕜 := ℝ), h, finsum_mem_congr rfl hzero, finsum_mem_zero]

variable [DiscreteTopology L]

lemma finite_inter_closedBall (r : ℝ) : (Metric.closedBall 0 r ∩ (L : Set E)).Finite :=
  have : DiscreteTopology L.toAddSubgroup := ‹DiscreteTopology L›
  Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete Metric.isBounded_closedBall
    L.toAddSubgroup.isClosed_of_discreteTopology

/-- **A discrete subgroup has finitely many minimal vectors.** -/
lemma finite_minimalVectors : (minimalVectors L).Finite :=
  (finite_inter_closedBall (minimum L)).subset fun _ hx ↦
    ⟨mem_closedBall_zero_iff.mpr hx.2.2.le, hx.1⟩

/-- **A nonzero discrete subgroup has a minimal vector**: its minimum is attained. -/
lemma nonempty_minimalVectors (hL : L ≠ ⊥) : (minimalVectors L).Nonempty := by
  rcases L.ne_bot_iff.mp hL with ⟨x, hx, hx₀⟩
  rcases exists_min_image ((Metric.closedBall 0 ‖x‖ ∩ (L : Set E)) \ {0}) (‖·‖)
    (finite_inter_closedBall ‖x‖).sdiff ⟨x, ⟨mem_closedBall_zero_iff.mpr le_rfl, hx⟩, hx₀⟩ with
    ⟨y, ⟨⟨hyx, hy⟩, hy₀⟩, hmin⟩
  refine ⟨y, hy, hy₀, (IsLeast.csInf_eq ?_).symm⟩
  refine ⟨⟨y, ⟨hy, hy₀⟩, rfl⟩, ?_⟩
  rintro _ ⟨z, ⟨hz, hz₀⟩, rfl⟩
  exact (le_or_gt ‖z‖ ‖x‖).elim (fun h ↦ hmin z ⟨⟨mem_closedBall_zero_iff.mpr h, hz⟩, hz₀⟩)
    fun h ↦ (mem_closedBall_zero_iff.mp hyx).trans h.le

lemma minimum_pos (hL : L ≠ ⊥) : 0 < minimum L :=
  minimum_pos_of_mem_minimalVectors (nonempty_minimalVectors hL).some_mem

lemma exists_lt_forall_le_norm (hS : (minimalVectors L).Nonempty) :
    ∃ m, minimum L < m ∧ ∀ x ∈ L, x ≠ 0 → x ∉ minimalVectors L → m ≤ ‖x‖ := by
  have hm : 0 < minimum L := minimum_pos_of_mem_minimalVectors hS.some_mem
  have hlt (x : E) (hx : x ∈ L) (hx0 : x ≠ 0) (hxS : x ∉ minimalVectors L) : minimum L < ‖x‖ :=
    (minimum_le_norm hx hx0).lt_of_ne fun h ↦ hxS ⟨hx, hx0, h.symm⟩
  rcases (((Metric.closedBall 0 (2 * minimum L) ∩ (L : Set E)) \ {0}) \
    minimalVectors L).eq_empty_or_nonempty with hF | hF
  · refine ⟨2 * minimum L, by linarith, fun x hx hx0 hxS ↦ le_of_not_gt fun h ↦ ?_⟩
    exact hF.subset ⟨⟨⟨mem_closedBall_zero_iff.mpr h.le, hx⟩, hx0⟩, hxS⟩
  rcases exists_min_image _ (‖·‖) (finite_inter_closedBall _).sdiff.sdiff hF with ⟨y, hy, hmin⟩
  refine ⟨min (2 * minimum L) ‖y‖, lt_min (by linarith) (hlt y hy.1.1.2 hy.1.2 hy.2),
    fun x hx hx0 hxS ↦ ?_⟩
  rcases le_or_gt ‖x‖ (2 * minimum L) with h | h
  · exact (min_le_right _ _).trans (hmin x ⟨⟨⟨mem_closedBall_zero_iff.mpr h, hx⟩, hx0⟩, hxS⟩)
  · exact (min_le_left _ _).trans h.le

end ZLattice
