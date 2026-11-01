import TauCeti.RepresentationTheory.Symmetric.Specht.Complex
import TauCeti.RepresentationTheory.Symmetric.Specht.HookLength

/-!
# The degrees of the irreducible complex representations of `S₆`

The knowl `mf.siegel.family.gamma_2` lists the irreducible representations `s[λ]` of `S₆` with
their dimensions. Here `s[λ]` is the complex Specht module `TauCeti.spechtModuleℂ λ`, whose
dimension is given by the hook length formula; the eleven partitions of 6 are enumerated, and the
dimensions are those of the knowl's table: `1, 5, 9, 10, 5, 16, 10, 5, 9, 5, 1` for
`[6], [5,1], [4,2], [4,1²], [3²], [3,2,1], [3,1³], [2³], [2²,1²], [2,1⁴], [1⁶]`.

## Main results

* `Nat.Partition.finrank_spechtModuleℂ_six`: the dimensions of the irreducible complex
  representations of `S₆`.
-/

namespace Nat.Partition

open TauCeti

private lemma sort_parts_six_cases (μ : Nat.Partition 6) :
    μ.parts.sort (· ≥ ·) = [6] ∨ μ.parts.sort (· ≥ ·) = [5, 1] ∨
      μ.parts.sort (· ≥ ·) = [4, 2] ∨ μ.parts.sort (· ≥ ·) = [4, 1, 1] ∨
      μ.parts.sort (· ≥ ·) = [3, 3] ∨ μ.parts.sort (· ≥ ·) = [3, 2, 1] ∨
      μ.parts.sort (· ≥ ·) = [3, 1, 1, 1] ∨ μ.parts.sort (· ≥ ·) = [2, 2, 2] ∨
      μ.parts.sort (· ≥ ·) = [2, 2, 1, 1] ∨ μ.parts.sort (· ≥ ·) = [2, 1, 1, 1, 1] ∨
      μ.parts.sort (· ≥ ·) = [1, 1, 1, 1, 1, 1] := by
  have hs : (μ.parts.sort (· ≥ ·)).Pairwise (· ≥ ·) := Multiset.pairwise_sort μ.parts (· ≥ ·)
  have hp : ∀ x ∈ μ.parts.sort (· ≥ ·), 0 < x := fun x hx ↦
    μ.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hx)
  have hsum : (μ.parts.sort (· ≥ ·)).sum = 6 := by
    rw [← Multiset.sum_coe, Multiset.sort_eq, μ.parts_sum]
  generalize μ.parts.sort (· ≥ ·) = w at hs hp hsum ⊢
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, t⟩⟩⟩⟩⟩⟩⟩
  all_goals simp_all
  all_goals omega

/-- **The dimensions of the irreducible complex representations of `S₆`** (LMFDB
`mf.siegel.family.gamma_2`), indexed by their decreasing row lengths, as in the knowl's table. -/
lemma finrank_spechtModuleℂ_six (μ : Nat.Partition 6) :
    Module.finrank ℂ (spechtModuleℂ μ) =
      match μ.parts.sort (· ≥ ·) with
      | [6] => 1
      | [5, 1] => 5
      | [4, 2] => 9
      | [4, 1, 1] => 10
      | [3, 3] => 5
      | [3, 2, 1] => 16
      | [3, 1, 1, 1] => 10
      | [2, 2, 2] => 5
      | [2, 2, 1, 1] => 9
      | [2, 1, 1, 1, 1] => 5
      | [1, 1, 1, 1, 1, 1] => 1
      | _ => 0 := by
  rw [finrank_spechtModuleℂ, finrank_spechtModule_eq_factorial_div_prod_hookLength]
  rcases sort_parts_six_cases μ with h | h | h | h | h | h | h | h | h | h | h
  all_goals
    simp only [YoungDiagram.hookLength_def, YoungDiagram.armLength_def, YoungDiagram.legLength_def]
    rw [← YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := YoungDiagram.ofPartition μ)]
    simp only [YoungDiagram.rowLens_ofPartition_eq_sort_parts, h, YoungDiagram.rowLen_eq_card,
      YoungDiagram.colLen_eq_card, YoungDiagram.row, YoungDiagram.col, YoungDiagram.ofRowLens]
    norm_num [YoungDiagram.cellsOfRowLens, Finset.range_add_one, Finset.filter_insert,
      Finset.filter_singleton]

end Nat.Partition
