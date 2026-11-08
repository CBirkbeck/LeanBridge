import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.EnhancedGroup
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.QuaternionOrder

/-!
# The profinite group `Ô^×` of a quaternion order

For an order `O` in a quaternion algebra over `ℚ`, the unit group `Ô^×` of `Ô = O ⊗ ℤ̂` is the
inverse limit `lim_N (O/NO)^×` over the positive integers `N` ordered by divisibility
(`Subalgebra.completedUnits`, LMFDB `shimcurve.enhanced_group`). Its topology is the inverse limit
topology: the subspace topology of the product `∏_N (O/NO)^×` of the finite discrete groups
`(O/NO)^×` (`Subalgebra.completedUnitsTopology`), the coarsest one making the reductions
`Ô^× → (O/NO)^×` continuous. With it `Ô^×` is a profinite group: a topological group, compact
because it is closed in a product of finite spaces, and totally disconnected and Hausdorff as a
subspace of a product of discrete spaces (LMFDB `shimcurve.enhanced_group`, `gl2.profinite`).

The topology is a definition rather than an instance: `(O/NO)^×` is not given a topology elsewhere,
and the topology of `Ô^×` is not the one a topology on the quaternion algebra would induce.

## Main definitions

* `Subalgebra.completedUnitsTopology` (LMFDB `shimcurve.enhanced_group`): the inverse limit
  topology on `Ô^×`.
* `Subalgebra.completedUnitsProfinite` (LMFDB `shimcurve.enhanced_group`, `gl2.profinite`): `Ô^×` as
  a profinite group, for an order `O`.

## Main results

* `Subalgebra.continuous_completedUnitsReduction`: the reductions `Ô^× → (O/NO)^×` are continuous.
* `Subalgebra.isTopologicalGroup_completedUnits`: `Ô^×` is a topological group.
* `Subalgebra.compactSpace_completedUnits`: `Ô^×` is compact when `O` is a finitely generated
  `ℤ`-module, for instance an order.
* `Subalgebra.totallyDisconnectedSpace_completedUnits`: `Ô^×` is totally disconnected.
* `Subalgebra.t2Space_completedUnits`: `Ô^×` is Hausdorff.
* `Subalgebra.isQuaternionOrder_range_mapMatrix`: the integral matrices are an order of `M₂(ℚ)`, a
  concrete order to which the construction applies.
-/

namespace Subalgebra

variable {B : Type*} [Ring B] (O : Subalgebra ℤ B)

/-- The **inverse limit topology** on `Ô^× = lim_N (O/NO)^×` (LMFDB `shimcurve.enhanced_group`):
the subspace topology of the product `∏_N (O/NO)^×` of the groups `(O/NO)^×` with the discrete
topology. -/
@[instance_reducible]
def completedUnitsTopology : TopologicalSpace O.completedUnits :=
  letI _ : ∀ N : ℕ+, TopologicalSpace (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⊥
  inferInstance

open Ideal in
lemma finite_quotient_span_natCast [Module.Finite ℤ O] (N : ℕ+) :
    Finite (O ⧸ Ideal.span {((N : ℕ) : O)}) := by
  refine Module.finite_of_fg_torsion _ fun x ↦ ⟨⟨((N : ℕ) : ℤ),
    mem_nonZeroDivisors_of_ne_zero (by simp)⟩, ?_⟩
  rcases Quotient.mkₐ_surjective ℤ _ x with ⟨y, rfl⟩
  rw [Submonoid.mk_smul, ← map_zsmul, Quotient.mkₐ_eq_mk, Quotient.eq_zero_iff_mem, natCast_zsmul,
    nsmul_eq_mul, (Nat.cast_commute _ y).eq]
  exact Ideal.mul_mem_left _ y (Ideal.mem_span_singleton_self _)

/-- **The reductions `Ô^× → (O/NO)^×` are continuous** for the inverse limit topology and the
discrete topology on `(O/NO)^×`. -/
lemma continuous_completedUnitsReduction (N : ℕ+) :
    letI _ : TopologicalSpace O.completedUnits := O.completedUnitsTopology
    letI _ : TopologicalSpace (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := ⊥
    Continuous (O.completedUnitsReduction N) := by
  let _ : ∀ N : ℕ+, TopologicalSpace (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⊥
  exact (continuous_apply N).comp continuous_subtype_val

/-- **`Ô^×` is a topological group** for the inverse limit topology. -/
lemma isTopologicalGroup_completedUnits :
    letI _ : TopologicalSpace O.completedUnits := O.completedUnitsTopology
    IsTopologicalGroup O.completedUnits := by
  let _ : ∀ N : ℕ+, TopologicalSpace (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⊥
  have _ : ∀ N : ℕ+, DiscreteTopology (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⟨rfl⟩
  exact inferInstance

/-- **`Ô^×` is compact** for the inverse limit topology when `O` is a finitely generated `ℤ`-module,
for instance an order: it is closed in the product of the finite spaces `(O/NO)^×`. -/
lemma compactSpace_completedUnits [Module.Finite ℤ O] :
    letI _ : TopologicalSpace O.completedUnits := O.completedUnitsTopology
    CompactSpace O.completedUnits := by
  let _ : ∀ N : ℕ+, TopologicalSpace (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⊥
  have _ : ∀ N : ℕ+, DiscreteTopology (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⟨rfl⟩
  have _ : ∀ N : ℕ+, Finite (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun N ↦
    have : Finite (O ⧸ Ideal.span {((N : ℕ) : O)}) := O.finite_quotient_span_natCast N
    inferInstance
  have hc : (O.completedUnits : Set (∀ N : ℕ+, (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ)) =
      ⋂ (M : ℕ+) (N : ℕ+) (h : (M : ℕ) ∣ N), {x | O.quotientUnitsReduction h (x N) = x M} := by
    ext x
    simp [completedUnits]
  refine isCompact_iff_compactSpace.mp (IsClosed.isCompact ?_)
  rw [hc]
  exact isClosed_iInter fun M ↦ isClosed_iInter fun N ↦ isClosed_iInter fun h ↦
    isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply N)) (continuous_apply M)

/-- **`Ô^×` is totally disconnected** for the inverse limit topology. -/
lemma totallyDisconnectedSpace_completedUnits :
    letI _ : TopologicalSpace O.completedUnits := O.completedUnitsTopology
    TotallyDisconnectedSpace O.completedUnits := by
  let _ : ∀ N : ℕ+, TopologicalSpace (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⊥
  have _ : ∀ N : ℕ+, DiscreteTopology (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⟨rfl⟩
  exact inferInstance

/-- **`Ô^×` is Hausdorff** for the inverse limit topology. -/
lemma t2Space_completedUnits :
    letI _ : TopologicalSpace O.completedUnits := O.completedUnitsTopology
    T2Space O.completedUnits := by
  let _ : ∀ N : ℕ+, TopologicalSpace (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⊥
  have _ : ∀ N : ℕ+, DiscreteTopology (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⟨rfl⟩
  exact inferInstance

variable [Algebra ℚ B] in
lemma module_finite_of_isQuaternionOrder (hO : O.IsQuaternionOrder) : Module.Finite ℤ O :=
  .of_fg hO.fg

variable [Algebra ℚ B] in
/-- **`Ô^×` as a profinite group** (LMFDB `shimcurve.enhanced_group`, `gl2.profinite`), for an order
`O` of a quaternion algebra over `ℚ`: the group `lim_N (O/NO)^×` with the inverse limit topology, a
compact, totally disconnected (and Hausdorff) topological group. -/
noncomputable def completedUnitsProfinite (hO : O.IsQuaternionOrder) : ProfiniteGrp :=
  letI _ : TopologicalSpace O.completedUnits := O.completedUnitsTopology
  haveI : IsTopologicalGroup O.completedUnits := O.isTopologicalGroup_completedUnits
  haveI : Module.Finite ℤ O := O.module_finite_of_isQuaternionOrder hO
  haveI : CompactSpace O.completedUnits := O.compactSpace_completedUnits
  haveI : TotallyDisconnectedSpace O.completedUnits := O.totallyDisconnectedSpace_completedUnits
  ProfiniteGrp.of O.completedUnits

open Module in
/-- **The integral matrices form an order of `M₂(ℚ)`**, the split quaternion algebra over `ℚ`, so
that `Subalgebra.completedUnitsProfinite` applies to a concrete order. -/
lemma isQuaternionOrder_range_mapMatrix :
    ((Int.castRingHom ℚ).mapMatrix.toIntAlgHom.range :
      Subalgebra ℤ (Matrix (Fin 2) (Fin 2) ℚ)).IsQuaternionOrder := by
  let f : Matrix (Fin 2) (Fin 2) ℤ →ₐ[ℤ] Matrix (Fin 2) (Fin 2) ℚ :=
    (Int.castRingHom ℚ).mapMatrix.toIntAlgHom
  have h : toSubmodule f.range = Submodule.map f.toLinearMap ⊤ := by
    ext
    simp
  refine ⟨h ▸ Finite.fg_top.map _, Submodule.eq_top_iff'.mpr fun M ↦ ?_⟩
  rw [M.matrix_eq_sum_single]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦ ?_
  have hs : f (Matrix.single i j 1) = Matrix.single i j 1 :=
    (Matrix.map_single i j (1 : ℤ) (Int.castRingHom ℚ)).trans (congrArg _ (map_one _))
  rw [← mul_one (M i j), ← smul_eq_mul, ← Matrix.smul_single]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hs ▸ f.mem_range_self _))

end Subalgebra
