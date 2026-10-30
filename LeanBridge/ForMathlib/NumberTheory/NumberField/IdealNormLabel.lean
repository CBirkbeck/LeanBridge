import Mathlib.Order.Interval.Set.Nat
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Labels `N.i` of ideals of rings of integers

The LMFDB labels a nonzero ideal `I` of the ring of integers `𝒪_K` of a number field `K` (LMFDB
`nf.ideal_labels`) by `N.i`, where `N = [𝒪_K : I]` is its absolute norm and `i` is the position of
`I` in a sorted list of the finitely many ideals of norm `N`. The ordering of the ideals of a given
norm is that of Cremona, Page and Sutherland, which depends only on the integral primitive element
`α` of `K`, for the LMFDB the root of the polredabs polynomial of `K`
(`NumberField.polredabs`): it orders the primes above `p` through the factors of the minimal
polynomial of `α` over `ℤ_p` and extends this to all ideals. The knowl does not state that
ordering, and it is not formalised: the label is defined here relative to any strict total order
`r` on the ideals, only its restriction to the ideals of each norm mattering. For every such order
the labels identify the ideals (`Ideal.normLabel_injective`) and take exactly the values `N.i`,
`1 ≤ i ≤ #{J | N(J) = N}` (`Ideal.exists_normLabel_eq`).

## Main definitions

* `Ideal.normLabelIndex` (LMFDB `nf.ideal_labels`): the index `i` of an ideal among the ideals of
  its norm, for an ordering `r`.
* `Ideal.normLabel` (LMFDB `nf.ideal_labels`): the ideal label `N.i`, as the pair `(N, i)`.

## Main results

* `Ideal.normLabel_injective`: an ideal is determined by its label.
* `Ideal.normLabelIndex_le`: the index of an ideal of norm `N` is at most the number of ideals of
  norm `N`.
* `Ideal.exists_normLabel_eq`: every `N.i` with `1 ≤ i ≤ #{J | N(J) = N}` is the label of an
  ideal.
-/

namespace Ideal

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Infinite S] [Module.Free ℤ S]
  [Module.Finite ℤ S] (r : Ideal S → Ideal S → Prop) [IsStrictTotalOrder (Ideal S) r]
  (I : Ideal S) {J : Ideal S}

/-- The **index** `i` (LMFDB `nf.ideal_labels`) of an ideal `I` of a ring of integers `S` among the
ideals of its norm `N`, for an ordering `r` of the ideals: `1` plus the number of ideals of norm `N`
before `I`, so that `I` is the `i`-th ideal of norm `N`. The LMFDB uses the ordering of Cremona,
Page and Sutherland, which is not formalised. -/
noncomputable def normLabelIndex : ℕ :=
  {J : Ideal S | absNorm J = absNorm I ∧ r J I}.ncard + 1

/-- The **ideal label** `N.i` (LMFDB `nf.ideal_labels`) of an ideal `I` of a ring of integers `S`,
as the pair `(N, i)`: its absolute norm `N = [S : I]` and its index `i` among the ideals of norm `N`
for an ordering `r` of the ideals (`normLabelIndex`). The LMFDB labels the nonzero ideals; the
zero ideal, the only one of norm `0`, has the label `(0, 1)`. -/
noncomputable def normLabel : ℕ × ℕ :=
  (absNorm I, normLabelIndex r I)

lemma ncard_lt_ncard_setOf_absNorm_eq {s : Set (Ideal S)}
    (hs : s ⊆ {J : Ideal S | absNorm J = absNorm I}) (hI : I ∉ s) :
    s.ncard < {J : Ideal S | absNorm J = absNorm I}.ncard :=
  Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hs).mpr ⟨I, rfl, hI⟩)
    (finite_setOfPred_absNorm_eq (absNorm I))

variable {I} in
lemma normLabelIndex_lt_normLabelIndex (hN : absNorm I = absNorm J) (hIJ : r I J) :
    normLabelIndex r I < normLabelIndex r J := by
  have hsub : {K : Ideal S | absNorm K = absNorm I ∧ r K I} ⊆
      {K : Ideal S | absNorm K = absNorm J ∧ r K J} :=
    fun K hK ↦ ⟨hK.1.trans hN, IsTrans.trans _ _ _ hK.2 hIJ⟩
  have hfin : {K : Ideal S | absNorm K = absNorm J ∧ r K J}.Finite :=
    (finite_setOfPred_absNorm_eq (absNorm J)).subset fun K hK ↦ hK.1
  exact Nat.add_lt_add_right (Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).mpr
    ⟨I, ⟨hN, hIJ⟩, fun h ↦ irrefl I h.2⟩) hfin) 1

/-- **An ideal is determined by its label**: two ideals of the same norm `N` and the same index are
equal. -/
lemma normLabel_injective : Function.Injective (normLabel r) := by
  intro I J h
  rcases Prod.ext_iff.mp h with ⟨hN, hi⟩
  rcases trichotomous_of r I J with hIJ | hIJ | hJI
  · exact absurd hi (normLabelIndex_lt_normLabelIndex r hN hIJ).ne
  · exact hIJ
  · exact absurd hi (normLabelIndex_lt_normLabelIndex r hN.symm hJI).ne'

/-- **The index of an ideal of norm `N` is at most the number of ideals of norm `N`.** -/
lemma normLabelIndex_le : normLabelIndex r I ≤ {J : Ideal S | absNorm J = absNorm I}.ncard :=
  ncard_lt_ncard_setOf_absNorm_eq I (fun _ hJ ↦ hJ.1) fun h ↦ irrefl I h.2

/-- **Every `N.i` with `1 ≤ i ≤ #{J | N(J) = N}` is the label of an ideal**: the labels of the
ideals of norm `N` are exactly `N.1, …, N.m`, `m` the number of ideals of norm `N`. -/
lemma exists_normLabel_eq {N i : ℕ} (hi : 1 ≤ i) (hiN : i ≤ {J : Ideal S | absNorm J = N}.ncard) :
    ∃ I : Ideal S, normLabel r I = (N, i) := by
  rcases Set.surj_on_of_inj_on_of_ncard_le (s := {J : Ideal S | absNorm J = N})
    (t := Set.Icc 1 {J : Ideal S | absNorm J = N}.ncard) (fun I _ ↦ normLabelIndex r I)
    (fun I hI ↦ ⟨Nat.le_add_left 1 _, hI ▸ normLabelIndex_le r I⟩)
    (fun I J hI hJ hIJ ↦ normLabel_injective r <| Prod.ext (hI.trans hJ.symm) hIJ)
    (by rw [Set.ncard_Icc_nat, Nat.add_sub_cancel]) (Set.finite_Icc _ _) i ⟨hi, hiN⟩ with
    ⟨I, hI, hIi⟩
  exact ⟨I, Prod.ext hI hIi.symm⟩

end Ideal
