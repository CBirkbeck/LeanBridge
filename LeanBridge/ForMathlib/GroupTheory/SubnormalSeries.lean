import Mathlib.GroupTheory.IsSubnormal
import Mathlib.Order.RelSeries

/-!
# Subnormal and normal series of a group

A subnormal series of a group `G` is a chain of subgroups `⊥ = H₀ ⊴ H₁ ⊴ ⋯ ⊴ Hₖ = ⊤` in which each
term is normal in the next, and a normal series is a subnormal series whose terms are all normal
in `G`. Both are relation series (`RelSeries`) from `⊥` to `⊤`, for the relation `H ≤ K` with `H`
normal in `K`; the inclusions need not be strict.

## Main definitions

* `Subgroup.SubnormalSeries` (LMFDB `group.normal_series`): subnormal series.
* `Subgroup.NormalSeries` (LMFDB `group.normal_series`): normal series.
* `Subgroup.NormalSeries.ofLE`: a chain of normal subgroups of `G` from `⊥` to `⊤` is a normal
  series.

## Main results

* `Subgroup.SubnormalSeries.isSubnormal`: every term of a subnormal series is subnormal.
* `Subgroup.isSubnormal_iff_exists_subnormalSeries`: a subgroup is subnormal in Mathlib's sense
  (`Subgroup.IsSubnormal`) if and only if it is a term of a subnormal series.
-/

namespace Subgroup

variable (G : Type*) [Group G]

/-- A **subnormal series** of `G` (LMFDB `group.normal_series`): a chain of subgroups
`⊥ = H₀ ⊴ H₁ ⊴ ⋯ ⊴ Hₖ = ⊤` in which each `Hᵢ` is contained and normal in `Hᵢ₊₁`. -/
structure SubnormalSeries extends RelSeries {p : Subgroup G × Subgroup G | p.1 ≤ p.2 ∧
    (p.1.subgroupOf p.2).Normal} where
  /-- A subnormal series starts at the trivial subgroup. -/
  head_eq_bot : toRelSeries.head = ⊥
  /-- A subnormal series ends at the whole group. -/
  last_eq_top : toRelSeries.last = ⊤

/-- A **normal series** of `G` (LMFDB `group.normal_series`): a subnormal series all of whose
terms are normal in `G`. -/
structure NormalSeries extends SubnormalSeries G where
  /-- Every term of a normal series is normal in the whole group. -/
  normal (i : Fin (length + 1)) : (toFun i).Normal

variable {G}

namespace SubnormalSeries

instance : CoeFun (SubnormalSeries G) fun s ↦ Fin (s.length + 1) → Subgroup G :=
  ⟨fun s ↦ s.toFun⟩

variable (s : SubnormalSeries G) (i : Fin s.length)

lemma le_succ : s i.castSucc ≤ s i.succ :=
  (s.step i).1

lemma normal_subgroupOf : ((s i.castSucc).subgroupOf (s i.succ)).Normal :=
  (s.step i).2

instance : ((s i.castSucc).subgroupOf (s i.succ)).Normal :=
  s.normal_subgroupOf i

lemma apply_zero : s 0 = ⊥ :=
  s.head_eq_bot

lemma apply_last : s (Fin.last s.length) = ⊤ :=
  s.last_eq_top

lemma monotone : Monotone s :=
  Fin.monotone_iff_le_succ.mpr s.le_succ

/-- **Every term of a subnormal series is subnormal** in the sense of `Subgroup.IsSubnormal`. -/
lemma isSubnormal (j : Fin (s.length + 1)) : (s j).IsSubnormal := by
  induction j using Fin.reverseInduction with
  | last => exact s.apply_last ▸ IsSubnormal.top
  | cast j ih => exact IsSubnormal.step _ _ (s.le_succ j) ih (s.normal_subgroupOf j)

end SubnormalSeries

/-- **A subgroup is subnormal if and only if it is a term of a subnormal series**: Mathlib's
inductive predicate `Subgroup.IsSubnormal` agrees with the LMFDB's chains. -/
lemma isSubnormal_iff_exists_subnormalSeries {H : Subgroup G} :
    H.IsSubnormal ↔ ∃ (s : SubnormalSeries G) (i : Fin (s.length + 1)), s i = H := by
  refine ⟨fun h ↦ ?_, fun ⟨s, i, hi⟩ ↦ hi ▸ s.isSubnormal i⟩
  rcases IsSubnormal.isSubnormal_iff.mp h with ⟨n, f, hf, hn, h0, hN⟩
  refine ⟨⟨⟨n + 1, Fin.cons ⊥ fun j ↦ f j, fun j ↦ ?_⟩, ?_, ?_⟩, 1, ?_⟩
  · induction j using Fin.cases with
    | zero => simp
    | succ j =>
      rw [← Fin.succ_castSucc]
      simpa using ⟨hf (Nat.le_succ j), hn j⟩
  · simp [RelSeries.head]
  · simp [RelSeries.last, hN]
  · simpa using h0

namespace NormalSeries

instance : CoeFun (NormalSeries G) fun s ↦ Fin (s.length + 1) → Subgroup G :=
  ⟨fun s ↦ s.toFun⟩

/-- A chain `⊥ = H₀ ≤ H₁ ≤ ⋯ ≤ Hₖ = ⊤` of normal subgroups of `G` is a normal series: a normal
subgroup of `G` is normal in every subgroup containing it. -/
def ofLE (s : RelSeries {p : Subgroup G × Subgroup G | p.1 ≤ p.2}) (hs : ∀ i, (s i).Normal)
    (head : s.head = ⊥) (last : s.last = ⊤) : NormalSeries G where
  length := s.length
  toFun := s
  step i := ⟨s.step i, (hs i.castSucc).subgroupOf _⟩
  head_eq_bot := head
  last_eq_top := last
  normal := hs

end NormalSeries

end Subgroup
