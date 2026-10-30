import LeanBridge.ForMathlib.NumberTheory.Hypergeometric.HodgeType
import LeanBridge.ForMathlib.NumberTheory.Hypergeometric.HodgeWidth
import Mathlib.Data.List.Indexes

/-!
# The Hodge vector and the degree of a hypergeometric motive

The hypergeometric motives `H(A, B, t)` of a family `H(A, B)` of degree `d` (LMFDB `hgm.motive`)
are indexed by the rational numbers `t ∉ {0, 1}`, the case `t = 1` being allowed with special
attention. For `t ≠ 0, 1` the motive `H(A, B, t)` has the Hodge vector of the family, and the
special motive `H(A, B, 1)` has the Hodge vector `Hypergeometric.Parameters.hodgeVectorAtOne`, in
which the middle Hodge number drops by `1` if the weight `w` is even and the two middle ones drop
by `1` if `w` is odd (LMFDB `hgm.hodge_vector`). Its degree, the sum of its Hodge numbers, is
therefore `1` or `2` less than the degree `d` of the other motives `H(A, B, t)`, as the knowls
state: the middle Hodge numbers are positive, as all the entries of the Hodge vector of the family
are.

As in `Hypergeometric.Weight`, these are the LMFDB's combinatorial recipes from the defining
parameters `(A, B)` and `t`. The motives `H(A, B, t)` themselves, through Katz's hypergeometric
sheaves or explicit varieties and their cohomology, are not formalised, nor is the knowl's example
`H([3], [1, 1], t) = H¹(E_{1728t}, ℚ)`, which needs the cohomology of elliptic curves. As written,
with `E_j` of `j`-invariant `1728j`, that example cannot hold: the projective monodromy of this
family, the triangle group `(∞, 3, ∞)` of index `4` in `PSL(2, ℤ)`, makes the `j`-invariant of its
elliptic curves a rational function of degree `4` in `t`, while `E_{1728t}` has `j`-invariant
`1728² t`.

## Main definitions

* `Hypergeometric.Parameters.motiveHodgeVector` (LMFDB `hgm.motive`, `hgm.hodge_vector`): the
  Hodge vector of `H(A, B, t)`.
* `Hypergeometric.Parameters.motiveDegree` (LMFDB `hgm.motive`, `hgm.degree`): the degree of
  `H(A, B, t)`.

## Main results

* `Hypergeometric.Parameters.motiveDegree_of_ne_one`: for `t ≠ 1` the degree of `H(A, B, t)` is the
  degree `d` of the family.
* `Hypergeometric.Parameters.motiveDegree_one_add_one`: for even weight and `d ≠ 0`, the degree of
  `H(A, B, 1)` is `d - 1`.
* `Hypergeometric.Parameters.motiveDegree_one_add_two`: for odd weight, the degree of `H(A, B, 1)`
  is `d - 2`.
-/

open Finset

namespace Hypergeometric

lemma sum_mapIdx_add_card {l : List ℕ} (c : ℕ → Prop) [DecidablePred c]
    (h : ∀ (i : ℕ) (hi : i < l.length), c i → 1 ≤ l[i]) :
    (l.mapIdx fun i x ↦ if c i then x - 1 else x).sum + #{i ∈ range l.length | c i} = l.sum := by
  rw [List.mapIdx_eq_ofFn, List.sum_ofFn, card_filter, ← Fin.sum_univ_eq_sum_range,
    ← sum_add_distrib, ← Fin.sum_univ_getElem]
  refine sum_congr rfl fun i _ ↦ ?_
  have hi : c i → 1 ≤ l[(i : ℕ)] := h i i.isLt
  split_ifs <;> simp_all

lemma card_filter_range_middle (w : ℕ) :
    #{i ∈ range (w + 1) | 2 * i = w ∨ 2 * i + 1 = w ∨ 2 * i = w + 1} = if Even w then 1 else 2 := by
  split_ifs with hw
  · rcases hw with ⟨m, rfl⟩
    refine card_eq_one.mpr ⟨m, ext fun i ↦ ?_⟩
    simp only [mem_filter, mem_range, mem_singleton]
    omega
  · rcases Nat.not_even_iff_odd.mp hw with ⟨m, rfl⟩
    refine card_eq_two.mpr ⟨m, m + 1, by omega, ext fun i ↦ ?_⟩
    simp only [mem_filter, mem_range, mem_insert, mem_singleton]
    omega

namespace Parameters

variable {d : ℕ} (P : Parameters d) (t : ℚ)

/-- The **Hodge vector** `(h^{0,w}, …, h^{w,0})` (LMFDB `hgm.motive`, `hgm.hodge_vector`) of the
hypergeometric motive `H(A, B, t)`: that of the family, `Hypergeometric.Parameters.hodgeVector`,
for `t ≠ 1`, and `Hypergeometric.Parameters.hodgeVectorAtOne`, with smaller middle Hodge numbers,
for the special motive `H(A, B, 1)`. The knowl's motives have `t ≠ 0`; `t = 0` is a junk value. -/
def motiveHodgeVector : List ℕ :=
  if t = 1 then P.hodgeVectorAtOne else P.hodgeVector

/-- The **degree** (LMFDB `hgm.motive`, `hgm.degree`) of the hypergeometric motive `H(A, B, t)`:
the dimension of its realisations, the sum of its Hodge numbers. It is the degree `d` of the family
for `t ≠ 1` (`motiveDegree_of_ne_one`), and `d - 1` or `d - 2` for the special motive `H(A, B, 1)`,
according as the weight is even or odd (`motiveDegree_one_add_one`, `motiveDegree_one_add_two`). -/
def motiveDegree : ℕ :=
  (P.motiveHodgeVector t).sum

/-- **For `t ≠ 1` the degree of `H(A, B, t)` is the degree of the family.** -/
lemma motiveDegree_of_ne_one (ht : t ≠ 1) : P.motiveDegree t = d := by
  rw [motiveDegree, motiveHodgeVector, ite_eq_right ht, P.sum_hodgeVector]

lemma motiveDegree_one_add_card : P.motiveDegree 1 + #{i ∈ range P.hodgeVector.length |
    2 * i = P.weight ∨ 2 * i + 1 = P.weight ∨ 2 * i = P.weight + 1} = d := by
  rw [motiveDegree, motiveHodgeVector, ite_eq_left rfl, hodgeVectorAtOne, sum_mapIdx_add_card _
    fun i hi _ ↦ Nat.one_le_iff_ne_zero.mpr <| P.ne_zero_of_mem_hodgeVector <| List.getElem_mem hi,
    P.sum_hodgeVector]

lemma length_hodgeVector (h : P.hodgeVector ≠ []) : P.hodgeVector.length = P.weight + 1 :=
  (Nat.sub_add_cancel (List.length_pos_iff.mpr h)).symm

lemma motiveDegree_one_add (h : P.hodgeVector ≠ []) :
    P.motiveDegree 1 + (if Even P.weight then 1 else 2) = d := by
  refine Eq.trans ?_ P.motiveDegree_one_add_card
  rw [P.length_hodgeVector h, card_filter_range_middle]

/-- **The special motive `H(A, B, 1)` has degree `d - 1` for even weight**, the middle Hodge number
dropping by `1`, if the family has positive degree `d`. -/
lemma motiveDegree_one_add_one (hw : Even P.weight) (hd : d ≠ 0) : P.motiveDegree 1 + 1 = d := by
  refine Eq.trans ?_ <| P.motiveDegree_one_add fun h ↦ hd ?_
  · rw [ite_eq_left hw]
  · rw [← P.sum_hodgeVector, h, List.sum_nil]

/-- **The special motive `H(A, B, 1)` has degree `d - 2` for odd weight**, the two middle Hodge
numbers dropping by `1`. -/
lemma motiveDegree_one_add_two (hw : Odd P.weight) : P.motiveDegree 1 + 2 = d := by
  refine Eq.trans ?_ <| P.motiveDegree_one_add fun h ↦ ?_
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr hw)]
  · simp [weight, h] at hw

end Parameters

end Hypergeometric
