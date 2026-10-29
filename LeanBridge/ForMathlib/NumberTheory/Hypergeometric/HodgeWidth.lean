import LeanBridge.ForMathlib.NumberTheory.Hypergeometric.Weight
import Mathlib.Data.List.GetD
import Mathlib.Order.Int.ConditionallyCompleteOrder
import TauCeti.Geometry.Hodge.Dimension

/-!
# The width of a motive

The **width** of a motive `M` of weight `w` (LMFDB `mot.width`) is the number of steps from the
first nonzero entry of its Hodge vector `(h^{0,w}, …, h^{w,0})` to the last nonzero entry, that is
`p_max - p_min` for the largest and the smallest `p` with `h^{p,w-p} ≠ 0`. It depends on `M` only
through its Hodge numbers. Motives are not formalised, so the width is defined on Hodge vectors,
given as lists `(h^{0,w}, …, h^{w,0})` like those of hypergeometric motives (LMFDB
`mot.hodgevector`), and on Tau Ceti's Hodge types `TauCeti.Hodge.HodgeType`, the numerical types
`(w, p ↦ h^{p,w-p})` of pure Hodge structures, such as the Hodge realisation of a motive. The two
agree on the Hodge vector of an effective Hodge type.

The knowl's example is the Hodge vector `(0, 2, 3, 1, 3, 2, 0)`, of width `4`. Having seven
entries, it is a Hodge vector of weight `6`, not of the weight `7` that the knowl states.

## Main definitions

* `Hypergeometric.hodgeVectorWidth` (LMFDB `mot.width`): the width of a Hodge vector.
* `TauCeti.Hodge.HodgeType.width` (LMFDB `mot.width`): the width of a Hodge type.
* `TauCeti.Hodge.HodgeType.hodgeVector` (LMFDB `mot.hodgevector`): the Hodge vector
  `(h^{0,w}, …, h^{w,0})` of a Hodge type.

## Main results

* `Hypergeometric.hodgeVectorWidth_zero_two_three_one_three_two_zero`: the knowl's example, the
  Hodge vector `(0, 2, 3, 1, 3, 2, 0)` has width `4`.
* `TauCeti.Hodge.HodgeType.hodgeVectorWidth_hodgeVector`: the width of the Hodge vector of an
  effective Hodge type is the width of the Hodge type.
* `TauCeti.Hodge.HodgeType.width_eq_two_mul_sub_weight`: by Hodge symmetry, the width is
  `2 p_max - w`.
* `TauCeti.Hodge.HodgeType.width_le_toNat_weight`: an effective Hodge type of weight `w` has width
  at most `w`.
* `Hypergeometric.Parameters.hodgeVectorWidth_hodgeVector`: the Hodge vector of a hypergeometric
  family has no zero entry, so its width is the weight of the family.
-/

open Hypergeometric

namespace Hypergeometric

variable {v : List ℕ} {a b : ℕ}

variable (v) in
/-- The **width** (LMFDB `mot.width`) of a Hodge vector `(h^{0,w}, …, h^{w,0})`, given as a list:
the number of steps from its first nonzero entry, of index `v.findIdx (· ≠ 0)`, to its last
nonzero entry, of index `v.length - 1 - v.reverse.findIdx (· ≠ 0)`. It is `0` when all entries
vanish. -/
def hodgeVectorWidth : ℕ :=
  v.length - 1 - v.reverse.findIdx (· ≠ 0) - v.findIdx (· ≠ 0)

/-- **The knowl's example**: the Hodge vector `(0, 2, 3, 1, 3, 2, 0)` has width `4`. -/
lemma hodgeVectorWidth_zero_two_three_one_three_two_zero :
    hodgeVectorWidth [0, 2, 3, 1, 3, 2, 0] = 4 := by
  decide

lemma hodgeVectorWidth_eq (ha : v.getD a 0 ≠ 0) (hb : v.getD b 0 ≠ 0)
    (h : ∀ i, v.getD i 0 ≠ 0 → a ≤ i ∧ i ≤ b) : hodgeVectorWidth v = b - a := by
  have hbv : b < v.length :=
    not_le.mp fun hbv ↦ hb (List.getD_eq_default _ _ hbv)
  have hav : a < v.length :=
    (h a ha).2.trans_lt hbv
  have h₁ : v.findIdx (· ≠ 0) = a := by
    rw [List.findIdx_eq hav]
    refine ⟨by rwa [← List.getD_eq_getElem _ 0 hav, decide_eq_true_iff], fun j hj ↦ ?_⟩
    rw [← List.getD_eq_getElem _ 0 (hj.trans hav), decide_eq_false_iff_not, not_not]
    exact by_contra fun hj' ↦ (h j hj').1.not_gt hj
  have h₂ : v.reverse.findIdx (· ≠ 0) = v.length - 1 - b := by
    rw [List.findIdx_eq (by rw [List.length_reverse]; omega)]
    refine ⟨?_, fun j hj ↦ ?_⟩
    · rw [List.getElem_reverse, ← List.getD_eq_getElem _ 0,
        Nat.sub_sub_self (Nat.le_sub_one_of_lt hbv), decide_eq_true_iff]
      exact hb
    · rw [List.getElem_reverse, ← List.getD_eq_getElem _ 0, decide_eq_false_iff_not, not_not]
      exact by_contra fun hj' ↦ (h _ hj').2.not_gt (by omega)
  rw [hodgeVectorWidth, h₁, h₂]
  omega

lemma hodgeVectorWidth_eq_zero (h : ∀ i, v.getD i 0 = 0) : hodgeVectorWidth v = 0 := by
  have hv (l : List ℕ) (hl : ∀ x ∈ l, x = 0) : l.findIdx (· ≠ 0) = l.length :=
    List.findIdx_eq_length.mpr fun x hx ↦ by simpa using hl x hx
  have hv₀ (x : ℕ) (hx : x ∈ v) : x = 0 := by
    rcases List.getElem_of_mem hx with ⟨i, hi, rfl⟩
    rw [← List.getD_eq_getElem _ 0 hi]
    exact h i
  rw [hodgeVectorWidth, hv v hv₀, hv v.reverse fun x hx ↦ hv₀ x (List.mem_reverse.mp hx),
    List.length_reverse]
  omega

namespace Parameters

variable {d : ℕ} (P : Parameters d)

lemma ne_zero_of_mem_hodgeVector {x : ℕ} (hx : x ∈ P.hodgeVector) : x ≠ 0 := by
  rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact (List.count_pos_iff.mpr (List.mem_toFinset.mp ((Finset.mem_sort _).mp hy))).ne'

/-- **The Hodge vector of a hypergeometric family has width its weight**: all its entries are
nonzero, being numbers of points on the lines of the zigzag plot that carry points. -/
lemma hodgeVectorWidth_hodgeVector : hodgeVectorWidth P.hodgeVector = P.weight := by
  rcases eq_or_ne P.hodgeVector [] with h | h
  · simp [hodgeVectorWidth, weight, h]
  have hl : 0 < P.hodgeVector.length :=
    List.length_pos_iff.mpr h
  have hne (i : ℕ) (hi : i < P.hodgeVector.length) : P.hodgeVector.getD i 0 ≠ 0 := by
    rw [List.getD_eq_getElem _ 0 hi]
    exact P.ne_zero_of_mem_hodgeVector (List.getElem_mem hi)
  have hle (i : ℕ) (hi : P.hodgeVector.getD i 0 ≠ 0) : 0 ≤ i ∧ i ≤ P.hodgeVector.length - 1 :=
    ⟨i.zero_le, Nat.le_sub_one_of_lt (not_le.mp fun h' ↦ hi (List.getD_eq_default _ _ h'))⟩
  rw [hodgeVectorWidth_eq (hne 0 hl) (hne _ (Nat.sub_lt hl one_pos)) hle, weight, Nat.sub_zero]

end Parameters

end Hypergeometric

namespace TauCeti.Hodge.HodgeType

variable (t : HodgeType) {a b : ℤ}

/-- The **Hodge vector** `(h^{0,w}, …, h^{w,0})` (LMFDB `mot.hodgevector`) of a Hodge type of
weight `w`: its Hodge numbers `h^{p,w-p}` for `0 ≤ p ≤ w`, empty if `w < 0`. They are all the
nonzero Hodge numbers when the type is effective. -/
def hodgeVector : List ℕ :=
  (List.range (t.weight + 1).toNat).map fun p : ℕ ↦ t.h p

/-- The **width** (LMFDB `mot.width`) of a Hodge type: the number of steps `p_max - p_min` from
the first nonzero Hodge number `h^{p_min,w-p_min}` to the last one `h^{p_max,w-p_max}`, and `0`
when all Hodge numbers vanish. For the Hodge type of a pure Hodge structure, such as the Hodge
realisation of a motive, this is the width of the motive. -/
noncomputable def width : ℕ :=
  (sSup {p | t.h p ≠ 0} - sInf {p | t.h p ≠ 0}).toNat

lemma width_eq (ha : t.h a ≠ 0) (hb : t.h b ≠ 0) (h : ∀ p, t.h p ≠ 0 → a ≤ p ∧ p ≤ b) :
    t.width = (b - a).toNat := by
  rw [width, IsGreatest.csSup_eq ⟨hb, fun p hp ↦ (h p hp).2⟩,
    IsLeast.csInf_eq ⟨ha, fun p hp ↦ (h p hp).1⟩]

/-- **The width is `2 p_max - w`**: by Hodge symmetry, the smallest `p` with `h^{p,w-p} ≠ 0` is
`w - p_max` for the largest one `p_max`. -/
lemma width_eq_two_mul_sub_weight (hb : t.h b ≠ 0) (h : ∀ p, t.h p ≠ 0 → p ≤ b) :
    (t.width : ℤ) = 2 * b - t.weight := by
  have hb' : t.h (t.weight - b) ≠ 0 := by
    rwa [← t.symm]
  have hle (p : ℤ) (hp : t.h p ≠ 0) : t.weight - b ≤ p ∧ p ≤ b := by
    have hp' : t.h (t.weight - p) ≠ 0 := by
      rwa [← t.symm]
    have hp'' : t.weight - p ≤ b :=
      h _ hp'
    exact ⟨by omega, h p hp⟩
  rw [t.width_eq hb' hb hle, Int.toNat_of_nonneg (by linarith [h _ hb'])]
  ring1

/-- **An effective Hodge type of weight `w` has width at most `w`.** -/
lemma width_le_toNat_weight (ht : t.IsEffective) : t.width ≤ t.weight.toNat := by
  rcases Set.eq_empty_or_nonempty {p | t.h p ≠ 0} with hS | hS
  · simp [width, hS]
  have h₁ : sSup {p | t.h p ≠ 0} ≤ t.weight :=
    (ht _ (Int.csSup_mem hS t.finite_support.bddAbove)).2
  have h₂ : 0 ≤ sInf {p | t.h p ≠ 0} :=
    (ht _ (Int.csInf_mem hS t.finite_support.bddBelow)).1
  exact Int.toNat_le_toNat (by omega)

lemma getD_hodgeVector (ht : t.IsEffective) (i : ℕ) : t.hodgeVector.getD i 0 = t.h i := by
  rcases lt_or_ge i t.hodgeVector.length with hi | hi
  · rw [List.getD_eq_getElem _ 0 hi]
    simp only [hodgeVector, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_default _ _ hi, eq_comm]
  by_contra h
  have hi' : (i : ℤ) ≤ t.weight :=
    (ht _ h).2
  rw [hodgeVector, List.length_map, List.length_range] at hi
  omega

/-- **The Hodge vector of an effective Hodge type has the width of the Hodge type.** -/
lemma hodgeVectorWidth_hodgeVector (ht : t.IsEffective) :
    hodgeVectorWidth t.hodgeVector = t.width := by
  rcases Set.eq_empty_or_nonempty {p | t.h p ≠ 0} with hS | hS
  · rw [hodgeVectorWidth_eq_zero fun i ↦ ?_]
    · simp [width, hS]
    rw [t.getD_hodgeVector ht]
    by_contra h
    exact hS.subset h
  have ha : t.h (sInf {p | t.h p ≠ 0}) ≠ 0 :=
    Int.csInf_mem hS t.finite_support.bddBelow
  have hb : t.h (sSup {p | t.h p ≠ 0}) ≠ 0 :=
    Int.csSup_mem hS t.finite_support.bddAbove
  have ha₀ : 0 ≤ sInf {p | t.h p ≠ 0} :=
    (ht _ ha).1
  have hab : sInf {p | t.h p ≠ 0} ≤ sSup {p | t.h p ≠ 0} :=
    csInf_le_csSup hS t.finite_support.bddBelow t.finite_support.bddAbove
  have hle (i : ℕ) (hi : t.hodgeVector.getD i 0 ≠ 0) :
      (sInf {p | t.h p ≠ 0}).toNat ≤ i ∧ i ≤ (sSup {p | t.h p ≠ 0}).toNat := by
    rw [t.getD_hodgeVector ht] at hi
    have h₁ : sInf {p | t.h p ≠ 0} ≤ i :=
      csInf_le t.finite_support.bddBelow hi
    have h₂ : (i : ℤ) ≤ sSup {p | t.h p ≠ 0} :=
      le_csSup t.finite_support.bddAbove hi
    omega
  rw [hodgeVectorWidth_eq (by rwa [t.getD_hodgeVector ht, Int.toNat_of_nonneg ha₀])
    (by rwa [t.getD_hodgeVector ht, Int.toNat_of_nonneg (ha₀.trans hab)]) hle, width]
  omega

end TauCeti.Hodge.HodgeType
