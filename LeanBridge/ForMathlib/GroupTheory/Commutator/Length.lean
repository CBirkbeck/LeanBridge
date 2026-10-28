import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Order.Lattice.Nat

/-!
# Commutator length

## Main definitions

* `commutatorLength` (LMFDB `group.commutator_length`).

## Main results

* `exists_list_commutatorSet_of_mem_commutator`: every element of the commutator subgroup is a
  product of commutators.
* `exists_list_length_le_commutatorLength`: every element of the commutator subgroup of a finite
  group is a product of at most `commutatorLength G` commutators.
-/

variable (G : Type*) [Group G]

/-- The **commutator length** (LMFDB `group.commutator_length`) of `G`, the least `k` such that
every element of the commutator subgroup `G'` is a product of `k` commutators. Products of at most
`k` commutators are products of exactly `k` commutators, padding with `⁅1, 1⁆ = 1`. Such a `k`
exists for finite `G`; otherwise this is `0` by convention. -/
noncomputable def commutatorLength : ℕ :=
  sInf {k | ∀ g ∈ commutator G,
    ∃ l : List G, l.length ≤ k ∧ (∀ x ∈ l, x ∈ commutatorSet G) ∧ l.prod = g}

variable {G}

/-- Every element of the commutator subgroup is a product of commutators. -/
lemma exists_list_commutatorSet_of_mem_commutator {g : G} (hg : g ∈ commutator G) :
    ∃ l : List G, (∀ x ∈ l, x ∈ commutatorSet G) ∧ l.prod = g := by
  rw [commutator_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨[x], by simpa using hx, by simp⟩
  | one => exact ⟨[], by simp, by simp⟩
  | mul x y _ _ hx hy =>
    rcases hx with ⟨l, hl, rfl⟩
    rcases hy with ⟨m, hm, rfl⟩
    exact ⟨l ++ m, by grind, List.prod_append⟩
  | inv x _ hx =>
    rcases hx with ⟨l, hl, rfl⟩
    refine ⟨(l.map (·⁻¹)).reverse, fun y hy ↦ ?_, l.prod_inv_reverse.symm⟩
    rcases List.mem_map.mp (List.mem_reverse.mp hy) with ⟨a, ha, rfl⟩
    rcases mem_commutatorSet_iff.mp (hl a ha) with ⟨b, c, rfl⟩
    rw [commutatorElement_inv]
    exact commutator_mem_commutatorSet c b

/-- Every element of the commutator subgroup of a finite group is a product of at most
`commutatorLength G` commutators. -/
lemma exists_list_length_le_commutatorLength [Finite G] {g : G} (hg : g ∈ commutator G) :
    ∃ l : List G, l.length ≤ commutatorLength G ∧ (∀ x ∈ l, x ∈ commutatorSet G) ∧ l.prod = g := by
  classical
  let hG : Fintype G := Fintype.ofFinite G
  let f : G → ℕ := fun x ↦
    if hx : x ∈ commutator G then (exists_list_commutatorSet_of_mem_commutator hx).choose.length
    else 0
  refine Nat.sInf_mem (s := {k | ∀ g ∈ commutator G,
    ∃ l : List G, l.length ≤ k ∧ (∀ x ∈ l, x ∈ commutatorSet G) ∧ l.prod = g})
    ⟨Finset.univ.sup f, fun x hx ↦ ?_⟩ g hg
  let l : List G := (exists_list_commutatorSet_of_mem_commutator hx).choose
  have hl : (∀ y ∈ l, y ∈ commutatorSet G) ∧ l.prod = x :=
    (exists_list_commutatorSet_of_mem_commutator hx).choose_spec
  exact ⟨l, (dite_eq_left hx).symm.trans_le <| Finset.le_sup (f := f) (Finset.mem_univ x), hl.1,
    hl.2⟩
