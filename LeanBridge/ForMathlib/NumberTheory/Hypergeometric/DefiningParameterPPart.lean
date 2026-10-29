import LeanBridge.ForMathlib.NumberTheory.Hypergeometric.CuspIndex
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The `p`-part and the prime-to-`p` part of the defining parameters of a hypergeometric family

Let `(A, B)` be the defining parameters of a hypergeometric family and `p` a prime. Every entry `u`
of `A` or `B` is `p^s v` with `p ∤ v`, that is `p^s = ordProj[p] u` and `v = ordCompl[p] u`.
Replacing every `u` by `φ(v)` copies of `p^s` gives two multisets `A'` and `B'`; removing equal
numbers of the elements common to `A'` and `B'`, that is taking `A' - B'` and `B' - A'`, gives the
`p`-part `[A_p, B_p]`, and the removed elements form the multiset `C_p = A' ∩ B'`. Replacing every
`u` by `φ(p^s)` copies of `v` instead, and removing the common elements, gives the prime-to-`p` part
`[A^p, B^p]`.

As `φ(p^s) φ(v) = φ(u)`, the totients of the entries of `A'` add up to the degree `d`, and so do
those of `B'`; the removal subtracts the same amount from both. Hence `[A_p, B_p]` and `[A^p, B^p]`
are again defining parameters, two cusp-indices of a common degree with no common entries, and we
construct them as such: the degree of the `p`-part is `d` minus the totient sum of `C_p`.

## Main definitions

* `Hypergeometric.Parameters.ofMultisets`: the defining parameters `[A' - B', B' - A']` of two
  multisets `A'` and `B'` of positive integers with the same totient sum.
* `Hypergeometric.Parameters.pPart` (LMFDB `hgm.defining_parameter_ppart`): the `p`-part
  `[A_p, B_p]`.
* `Hypergeometric.Parameters.pPartCommon` (LMFDB `hgm.defining_parameter_ppart`): the removed
  common elements `C_p`.
* `Hypergeometric.Parameters.primeToPPart` (LMFDB `hgm.defining_parameter_primetoppart`): the
  prime-to-`p` part `[A^p, B^p]`.

## Main results

* `Hypergeometric.Parameters.pPart_A_add_pPartCommon`,
  `Hypergeometric.Parameters.pPart_B_add_pPartCommon`: `A' = A_p + C_p` and `B' = B_p + C_p`.
* `Hypergeometric.Parameters.pPartDegree_add_sum_totient_pPartCommon`: the degree of the `p`-part
  plus the totient sum of `C_p` is the degree of the family.
-/

open Nat

namespace Hypergeometric

variable {d : ℕ} (m : Multiset ℕ) (pos : ∀ u ∈ m, 0 < u) (sum_totient : (m.map φ).sum = d)
  (A' B' : Multiset ℕ)

/-- The cusp-index of degree `d` with the entries of a multiset `m` of positive integers whose
totients add up to `d`, sorted in increasing order. -/
def CuspIndex.ofMultiset : CuspIndex d where
  toList := m.sort
  sortedLE := (m.pairwise_sort _).sortedLE
  pos u hu := pos u <| (Multiset.mem_sort _).mp hu
  sum_totient := by
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.sort_eq, sum_totient]

lemma CuspIndex.coe_ofMultiset :
    ((CuspIndex.ofMultiset m pos sum_totient).toList : Multiset ℕ) = m :=
  m.sort_eq _

variable {A' B'} in
lemma sum_map_totient_sub_eq_sum_map_totient_sub (h : (A'.map φ).sum = (B'.map φ).sum) :
    ((A' - B').map φ).sum = ((B' - A').map φ).sum := by
  have hA : ((A' - B').map φ).sum + ((A' ∩ B').map φ).sum = (A'.map φ).sum := by
    rw [← Multiset.sum_add, ← Multiset.map_add, Multiset.sub_add_inter]
  have hB : ((B' - A').map φ).sum + ((A' ∩ B').map φ).sum = (B'.map φ).sum := by
    rw [← Multiset.sum_add, ← Multiset.map_add, Multiset.inter_comm, Multiset.sub_add_inter]
  omega

/-- The defining parameters obtained from two multisets `A'` and `B'` of positive integers with the
same totient sum by removing equal numbers of their common elements: the cusp-indices with the
entries of `A' - B'` and of `B' - A'`, which have no common entries, of degree the totient sum of
`A' - B'`. -/
def Parameters.ofMultisets (hA : ∀ u ∈ A', 0 < u) (hB : ∀ u ∈ B', 0 < u)
    (h : (A'.map φ).sum = (B'.map φ).sum) : Parameters ((A' - B').map φ).sum where
  A := .ofMultiset (A' - B') (fun u hu ↦ hA u <| Multiset.mem_of_le (A'.sub_le_self B') hu) rfl
  B := .ofMultiset (B' - A') (fun u hu ↦ hB u <| Multiset.mem_of_le (B'.sub_le_self A') hu)
    (sum_map_totient_sub_eq_sum_map_totient_sub h).symm
  disjoint u hu hu' := by
    rw [CuspIndex.ofMultiset, Multiset.mem_sort, Multiset.mem_sub] at hu hu'
    exact lt_asymm hu hu'

variable (c : CuspIndex d) (P : Parameters d) (p : ℕ) {u : ℕ}

variable (u) in
lemma coprime_ordProj_ordCompl : (ordProj[p] u).Coprime (ordCompl[p] u) := by
  by_cases hp : p.Prime
  · rcases eq_or_ne u 0 with rfl | hu
    · simp
    · exact (coprime_ordCompl hp hu).pow_left _
  · rw [ordProj_of_not_prime u p hp]
    exact coprime_one_left _

/-- The multiset `A'` of the `p`-part (LMFDB `hgm.defining_parameter_ppart`) of a cusp-index `A`:
every entry `u = p^s v` of `A`, with `p ∤ v`, replaced by `φ(v)` copies of `p^s`. For `p` not a
prime, Mathlib's `u.factorization p` is `0`, and every `u` is replaced by `φ(u)` copies of `1`. -/
def CuspIndex.pPartMultiset : Multiset ℕ :=
  (c.toList : Multiset ℕ).bind fun u ↦ .replicate (φ (ordCompl[p] u)) (ordProj[p] u)

/-- The multiset `A'` of the prime-to-`p` part (LMFDB `hgm.defining_parameter_primetoppart`) of a
cusp-index `A`: every entry `u = p^s v` of `A`, with `p ∤ v`, replaced by `φ(p^s)` copies of `v`.
-/
def CuspIndex.primeToPPartMultiset : Multiset ℕ :=
  (c.toList : Multiset ℕ).bind fun u ↦ .replicate (φ (ordProj[p] u)) (ordCompl[p] u)

lemma CuspIndex.pos_of_mem_pPartMultiset (hu : u ∈ c.pPartMultiset p) : 0 < u := by
  rcases Multiset.mem_bind.mp hu with ⟨a, -, ha⟩
  rw [(Multiset.mem_replicate.mp ha).2]
  exact ordProj_pos a p

lemma CuspIndex.pos_of_mem_primeToPPartMultiset (hu : u ∈ c.primeToPPartMultiset p) : 0 < u := by
  rcases Multiset.mem_bind.mp hu with ⟨a, ha, ha'⟩
  rw [(Multiset.mem_replicate.mp ha').2]
  exact ordCompl_pos p (c.pos a ha).ne'

lemma CuspIndex.sum_totient_bind_replicate {f g : ℕ → ℕ} (h : ∀ u, φ (f u) * φ (g u) = φ u) :
    (((c.toList : Multiset ℕ).bind fun u ↦ .replicate (φ (f u)) (g u)).map φ).sum = d := by
  rw [Multiset.map_bind, Multiset.sum_bind]
  refine Eq.trans ?_ c.sum_totient
  rw [← Multiset.sum_coe, ← Multiset.map_coe]
  refine congrArg Multiset.sum <| Multiset.map_congr rfl fun u _ ↦ ?_
  rw [Multiset.map_replicate, Multiset.sum_replicate, smul_eq_mul, h]

lemma CuspIndex.sum_totient_pPartMultiset : ((c.pPartMultiset p).map φ).sum = d :=
  c.sum_totient_bind_replicate fun u ↦ by
    rw [mul_comm, ← totient_mul (coprime_ordProj_ordCompl p u), ordProj_mul_ordCompl_eq_self]

lemma CuspIndex.sum_totient_primeToPPartMultiset : ((c.primeToPPartMultiset p).map φ).sum = d :=
  c.sum_totient_bind_replicate fun u ↦ by
    rw [← totient_mul (coprime_ordProj_ordCompl p u), ordProj_mul_ordCompl_eq_self]

/-- The degree of the `p`-part `[A_p, B_p]` of defining parameters `(A, B)`: the totient sum of
`A_p = A' - B'`. -/
def Parameters.pPartDegree : ℕ :=
  ((P.A.pPartMultiset p - P.B.pPartMultiset p).map φ).sum

/-- The **`p`-part** `[A_p, B_p]` (LMFDB `hgm.defining_parameter_ppart`) of the defining parameters
`(A, B)` of a hypergeometric family, for a prime `p`: every entry `u = p^s v` of `A` and of `B`,
with `p ∤ v`, is replaced by `φ(v)` copies of `p^s`, giving multisets `A'` and `B'`, and equal
numbers of the elements common to `A'` and `B'` are removed, giving `A_p = A' - B'` and
`B_p = B' - A'`. These are again defining parameters, of degree the totient sum of `A_p`, which is
the degree of the family minus the totient sum of the removed elements `C_p`
(`Hypergeometric.Parameters.pPartDegree_add_sum_totient_pPartCommon`). -/
def Parameters.pPart : Parameters (P.pPartDegree p) :=
  .ofMultisets (P.A.pPartMultiset p) (P.B.pPartMultiset p)
    (fun _ ↦ P.A.pos_of_mem_pPartMultiset p) (fun _ ↦ P.B.pos_of_mem_pPartMultiset p)
    ((P.A.sum_totient_pPartMultiset p).trans (P.B.sum_totient_pPartMultiset p).symm)

/-- The **multiset `C_p`** (LMFDB `hgm.defining_parameter_ppart`) of the elements removed from the
multisets `A'` and `B'` to form the `p`-part `[A_p, B_p]` of defining parameters `(A, B)`: the
elements common to `A'` and `B'`, with the smaller of their two multiplicities. -/
def Parameters.pPartCommon : Multiset ℕ :=
  P.A.pPartMultiset p ∩ P.B.pPartMultiset p

/-- **`A' = A_p + C_p`**: the multiset `A'` is the `p`-part `A_p` together with the removed common
elements `C_p`. -/
lemma Parameters.pPart_A_add_pPartCommon :
    ((P.pPart p).A.toList : Multiset ℕ) + P.pPartCommon p = P.A.pPartMultiset p := by
  rw [Parameters.pPart, Parameters.ofMultisets, CuspIndex.coe_ofMultiset, Parameters.pPartCommon,
    Multiset.sub_add_inter]

/-- **`B' = B_p + C_p`**: the multiset `B'` is the `p`-part `B_p` together with the removed common
elements `C_p`. -/
lemma Parameters.pPart_B_add_pPartCommon :
    ((P.pPart p).B.toList : Multiset ℕ) + P.pPartCommon p = P.B.pPartMultiset p := by
  rw [Parameters.pPart, Parameters.ofMultisets, CuspIndex.coe_ofMultiset, Parameters.pPartCommon,
    Multiset.inter_comm, Multiset.sub_add_inter]

/-- **The degree of the `p`-part** plus the totient sum of the removed common elements `C_p` is the
degree of the family. -/
lemma Parameters.pPartDegree_add_sum_totient_pPartCommon :
    P.pPartDegree p + ((P.pPartCommon p).map φ).sum = d := by
  rw [Parameters.pPartDegree, Parameters.pPartCommon, ← Multiset.sum_add, ← Multiset.map_add,
    Multiset.sub_add_inter, P.A.sum_totient_pPartMultiset]

/-- The degree of the prime-to-`p` part `[A^p, B^p]` of defining parameters `(A, B)`: the totient
sum of `A^p`. -/
def Parameters.primeToPPartDegree : ℕ :=
  ((P.A.primeToPPartMultiset p - P.B.primeToPPartMultiset p).map φ).sum

/-- The **prime-to-`p` part** `[A^p, B^p]` (LMFDB `hgm.defining_parameter_primetoppart`) of the
defining parameters `(A, B)` of a hypergeometric family, for a prime `p`: every entry `u = p^s v`
of `A` and of `B`, with `p ∤ v`, is replaced by `φ(p^s)` copies of `v`, giving multisets `A'` and
`B'`, and equal numbers of the elements common to `A'` and `B'` are removed, giving
`A^p = A' - B'` and `B^p = B' - A'`. These are again defining parameters, of degree the totient sum
of `A^p`. -/
def Parameters.primeToPPart : Parameters (P.primeToPPartDegree p) :=
  .ofMultisets (P.A.primeToPPartMultiset p) (P.B.primeToPPartMultiset p)
    (fun _ ↦ P.A.pos_of_mem_primeToPPartMultiset p) (fun _ ↦ P.B.pos_of_mem_primeToPPartMultiset p)
    ((P.A.sum_totient_primeToPPartMultiset p).trans (P.B.sum_totient_primeToPPartMultiset p).symm)

lemma Parameters.coe_primeToPPart_A : ((P.primeToPPart p).A.toList : Multiset ℕ) =
    P.A.primeToPPartMultiset p - P.B.primeToPPartMultiset p :=
  Multiset.sort_eq _ _

lemma Parameters.coe_primeToPPart_B : ((P.primeToPPart p).B.toList : Multiset ℕ) =
    P.B.primeToPPartMultiset p - P.A.primeToPPartMultiset p :=
  Multiset.sort_eq _ _

end Hypergeometric
