import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.GroupTheory.Coxeter.Basic

/-!
# Coxeter graphs and irreducible Coxeter groups

Coxeter groups (LMFDB `group.coxeter`) are Mathlib's `IsCoxeterGroup`, presented through a
`CoxeterSystem` for a `CoxeterMatrix`, in which the entry `0` stands for `m = ∞`; finite Coxeter
groups are those with `Finite W`.

## Main definitions

* `CoxeterMatrix.coxeterGraph` (LMFDB `group.coxeter`).
* `CoxeterMatrix.IsIrreducible` and `IsIrreducibleCoxeterGroup` (LMFDB `group.coxeter`).

## Main results

* `CoxeterMatrix.coxeterGraph_adj_iff`: two distinct generators are adjacent exactly when
  `m ≥ 3`, or `m = ∞`.
-/

universe u

variable {B : Type*} (M : CoxeterMatrix B)

/-- The **Coxeter graph** (LMFDB `group.coxeter`) of a Coxeter matrix `M`, with an edge between
distinct `i` and `j` when `m_ij ≠ 2`, that is when `m_ij ≥ 3` or `m_ij = ∞`. An edge with
`m_ij ≥ 4` carries the label `M i j`, read off from `M`. -/
def CoxeterMatrix.coxeterGraph : SimpleGraph B where
  Adj i j := i ≠ j ∧ M i j ≠ 2
  symm := ⟨fun i j h ↦ ⟨h.1.symm, M.symmetric j i ▸ h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- Two distinct generators are adjacent in the Coxeter graph exactly when `m_ij ≥ 3` or
`m_ij = ∞`. -/
lemma CoxeterMatrix.coxeterGraph_adj_iff (i j : B) :
    M.coxeterGraph.Adj i j ↔ i ≠ j ∧ (M i j = 0 ∨ 3 ≤ M i j) := by
  refine and_congr_right fun h ↦ ?_
  have h1 : M i j ≠ 1 := M.off_diagonal i j h
  omega

/-- A Coxeter matrix `M`, or a Coxeter system for it, is **irreducible** (LMFDB `group.coxeter`) if
its Coxeter graph is connected. -/
def CoxeterMatrix.IsIrreducible : Prop :=
  M.coxeterGraph.Connected

/-- A group `W` is an **irreducible Coxeter group** (LMFDB `group.coxeter`) if it has a Coxeter
system whose Coxeter matrix is irreducible. The LMFDB's finite irreducible Coxeter groups also
satisfy `Finite W`. -/
class IsIrreducibleCoxeterGroup (W : Type u) [Group W] : Prop where
  exists_coxeterSystem :
    ∃ (B : Type u) (M : CoxeterMatrix B), Nonempty (CoxeterSystem M W) ∧ M.IsIrreducible

instance {W : Type u} [Group W] [IsIrreducibleCoxeterGroup W] : IsCoxeterGroup W := by
  rcases IsIrreducibleCoxeterGroup.exists_coxeterSystem (W := W) with ⟨B, M, h, -⟩
  exact ⟨B, M, h⟩
