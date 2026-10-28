import LeanBridge.ForMathlib.NumberTheory.Hypergeometric.CuspIndex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Rat.Lemmas

/-!
# The weight of a hypergeometric family

The defining parameters `(A, B)` of a hypergeometric family `H(A, B)` give two lists `α` and `β` of
rational numbers in `(0, 1]`: each entry `a` of `A` (or of `B`) is replaced by the fractions in
`(0, 1]` with denominator `a`, and the result is sorted. The zigzag procedure orders the entries of
`α` (red) and `β` (blue) together and draws them from left to right, moving up after a red point
and down after a blue one; the numbers of red points on the horizontal lines form the Hodge vector
`(h^{0,w}, …, h^{w,0})` of the family, and its number of commas is the weight `w`.

Everything here is the combinatorial recipe by which the LMFDB computes these invariants from
`(A, B)`. Hypergeometric motives are not formalised: the weight as the degree `w` of the cohomology
`H^w(X)` in which the motive occurs, and the Hodge vector as the dimensions of its Hodge pieces, are
not available.

## Main definitions

* `Hypergeometric.fractionsWithDen n`: the elements of `ℚ ∩ (0, 1]` with denominator `n`.
* `Hypergeometric.CuspIndex.fractions` (LMFDB `hgm.defining_parameters`): the list `α` of a
  cusp-index.
* `Hypergeometric.Parameters.zigzagHeights` (LMFDB `hgm.zigzagplot`): the heights of the red points
  of the zigzag plot.
* `Hypergeometric.Parameters.hodgeVector` (LMFDB `hgm.hodge_vector`): the Hodge vector of `H(A, B)`.
* `Hypergeometric.Parameters.weight` (LMFDB `hgm.weight`): the weight of `H(A, B)`.

## Main results

* `Hypergeometric.mem_fractionsWithDen`, `Hypergeometric.card_fractionsWithDen`: the fractions
  with denominator `n` are the elements of `ℚ ∩ (0, 1]` with denominator `n`, and there are `φ(n)`
  of them.
* `Hypergeometric.CuspIndex.length_fractions`: the list `α` of a cusp-index of degree `d` has
  length `d`.
* `Hypergeometric.Parameters.sum_hodgeVector`: the Hodge numbers add up to the degree.
-/

open Finset

namespace Hypergeometric

variable (n : ℕ)

/-- The elements of `ℚ ∩ (0, 1]` with denominator `n`: the fractions `k / n` with `1 ≤ k ≤ n` and
`k` prime to `n` (`Hypergeometric.mem_fractionsWithDen`). -/
def fractionsWithDen : Finset ℚ :=
  {k ∈ Icc 1 n | k.Coprime n}.image fun k : ℕ ↦ (k / n : ℚ)

variable {n} in
/-- **The fractions with denominator `n`** are the elements of `ℚ ∩ (0, 1]` with denominator `n`. -/
lemma mem_fractionsWithDen {q : ℚ} : q ∈ fractionsWithDen n ↔ 0 < q ∧ q ≤ 1 ∧ q.den = n := by
  simp only [fractionsWithDen, mem_image, mem_filter, mem_Icc]
  constructor
  · rintro ⟨k, ⟨⟨hk1, hkn⟩, hk⟩, rfl⟩
    refine ⟨div_pos (by exact_mod_cast hk1) (by exact_mod_cast hk1.trans hkn),
      div_le_one_of_le₀ (by exact_mod_cast hkn) n.cast_nonneg, ?_⟩
    simpa using Rat.den_div_eq_of_coprime (a := k) (b := n) (by omega) hk
  · rintro ⟨hq0, hq1, rfl⟩
    have hnum : 0 < q.num := Rat.num_pos.mpr hq0
    refine ⟨q.num.natAbs, ⟨⟨by omega, ?_⟩, q.reduced⟩, ?_⟩
    · have hle : q.num ≤ q.den := Rat.num_le_denom_iff.mpr hq1
      omega
    · rw [Nat.cast_natAbs, abs_of_pos hnum]
      exact_mod_cast q.num_div_den

/-- **There are `φ(n)` fractions with denominator `n`** in `(0, 1]`. -/
lemma card_fractionsWithDen : #(fractionsWithDen n) = n.totient := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rfl
  rw [fractionsWithDen, card_image_of_injOn, ← Nat.filter_coprime_Ico_eq_totient n 1]
  · congr 1
    ext k
    simp only [mem_filter, mem_Icc, mem_Ico, Nat.coprime_comm]
    omega
  · intro a _ b _ h
    exact_mod_cast (div_left_inj' (Nat.cast_ne_zero.mpr hn.ne')).mp h

variable {d : ℕ} (c : CuspIndex d) (P : Parameters d)

/-- The list `α` of a cusp-index `A` (LMFDB `hgm.defining_parameters`): every entry `a` of `A` is
replaced by the elements of `ℚ ∩ (0, 1]` with denominator `a`, and the result is sorted in
ascending order. For the defining parameters `(A, B)` of a hypergeometric family these are the
lists `α` and `β`. -/
def CuspIndex.fractions : List ℚ :=
  ((c.toList : Multiset ℕ).bind fun a ↦ (fractionsWithDen a).val).sort (· ≤ ·)

/-- **The list `α` of a cusp-index of degree `d` has length `d`.** -/
lemma CuspIndex.length_fractions : c.fractions.length = d := by
  rw [CuspIndex.fractions, Multiset.length_sort, Multiset.card_bind]
  simpa [Function.comp_def, card_fractionsWithDen] using c.sum_totient

/-- The heights of the red points in the **zigzag plot** of a hypergeometric family `H(A, B)` (LMFDB
`hgm.zigzagplot`). The entries of `α` (red) and `β` (blue) are ordered increasingly, which is
unambiguous as `A` and `B` have no common entries, so that no entry of `α` is one of `β`; the
lowest is drawn at height `0`, and one moves up after each red point and down after each blue
one. The `j`-th entry `α_j` of `α`, counting from `0`, is preceded by `j` entries of `α` and by the
entries of `β` below it, so it is drawn at height `j - #{b ∈ β | b < α_j}`. -/
def Parameters.zigzagHeights : List ℤ :=
  P.A.fractions.zipIdx.map fun x ↦ (x.2 : ℤ) - ((P.B.fractions.filter (· < x.1)).length : ℤ)

/-- The **Hodge vector** `(h^{0,w}, …, h^{w,0})` of a hypergeometric family `H(A, B)` (LMFDB
`hgm.hodge_vector`), read from the zigzag plot (LMFDB `hgm.zigzagplot`): the numbers of red points
on its horizontal lines, from bottom to top. Only the lines carrying red points are counted; they
form an interval, as the plot climbs one step at a time (cyclically, from the last point back to
the first), so no line in between is skipped, though this is not proved here. This is the LMFDB's
combinatorial recipe from `α` and `β`; the Hodge numbers of the motive itself are not available,
as hypergeometric motives are not formalised. -/
def Parameters.hodgeVector : List ℕ :=
  (P.zigzagHeights.toFinset.sort (· ≤ ·)).map P.zigzagHeights.count

/-- The **(motivic) weight** `w` of a hypergeometric family `H(A, B)` (LMFDB `hgm.weight`): the
number of commas in its Hodge vector `(h^{0,w}, …, h^{w,0})`, that is its length minus one. For a
motive the weight is the degree `w` of the cohomology `H^w(X)` in which it occurs; hypergeometric
motives are not formalised, and this is the combinatorial recipe by which the LMFDB computes the
weight from the defining parameters. -/
def Parameters.weight : ℕ :=
  P.hodgeVector.length - 1

/-- **The Hodge numbers of a hypergeometric family of degree `d` add up to `d`.** -/
lemma Parameters.sum_hodgeVector : P.hodgeVector.sum = d := by
  rw [Parameters.hodgeVector, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq,
    ← Finset.sum_eq_multiset_sum, List.sum_toFinset_count_eq_length, Parameters.zigzagHeights,
    List.length_map, List.length_zipIdx, CuspIndex.length_fractions]

end Hypergeometric
