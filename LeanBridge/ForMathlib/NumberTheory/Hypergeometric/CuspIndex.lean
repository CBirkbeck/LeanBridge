import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Totient

/-!
# Cusp-indices and the defining parameters of hypergeometric families

The hypergeometric families `H(A, B)` over `ℚ` are indexed by pairs `(A, B)` of cusp-indices of a
common degree with no common entries. This file formalises that indexing datum, which is purely
combinatorial: no hypergeometric motive is involved.

## Main definitions

* `Hypergeometric.CuspIndex` (LMFDB `hgm.cusp_index`): a cusp-index of degree `d`, a weakly
  increasing list `[u₁, …, u_k]` of positive integers with `φ(u₁) + ⋯ + φ(u_k) = d`.
* `Hypergeometric.Parameters` (LMFDB `hgm.cusp_index`): a pair `(A, B)` of cusp-indices of a common
  degree with no common entries, the defining parameters of a hypergeometric family `H(A, B)`.
-/

namespace Hypergeometric

variable (d : ℕ)

/-- A **cusp-index** of degree `d` (LMFDB `hgm.cusp_index`): a weakly increasing list
`[u₁, …, u_k]` of positive integers with `φ(u₁) + ⋯ + φ(u_k) = d`, where `φ` is Euler's totient
function. Being weakly increasing, the list is the sorted presentation of a multiset of positive
integers, which is how the LMFDB knowl `hgm.familes` describes it. -/
@[ext]
structure CuspIndex where
  /-- The entries `u₁ ≤ ⋯ ≤ u_k`. -/
  toList : List ℕ
  /-- The entries are weakly increasing. -/
  sortedLE : toList.SortedLE
  /-- The entries are positive. -/
  pos (u : ℕ) : u ∈ toList → 0 < u
  /-- The totients of the entries add up to the degree. -/
  sum_totient : (toList.map Nat.totient).sum = d

variable {d} in
lemma CuspIndex.ext_iff_perm {c c' : CuspIndex d} : c = c' ↔ c.toList.Perm c'.toList :=
  ⟨fun h ↦ h ▸ .rfl, fun h ↦ CuspIndex.ext <| h.eq_of_sortedLE c.sortedLE c'.sortedLE⟩

/-- The **defining parameters** `(A, B)` of a hypergeometric family `H(A, B)` of degree `d` (LMFDB
`hgm.cusp_index`): two cusp-indices of degree `d` with no common entries. They are only the
combinatorial index of the family; the family itself, a motive over `ℚ(t)`, is not formalised. -/
@[ext]
structure Parameters where
  /-- The cusp-index `A`. -/
  A : CuspIndex d
  /-- The cusp-index `B`. -/
  B : CuspIndex d
  /-- The cusp-indices `A` and `B` have no common entries. -/
  disjoint : A.toList.Disjoint B.toList

end Hypergeometric
