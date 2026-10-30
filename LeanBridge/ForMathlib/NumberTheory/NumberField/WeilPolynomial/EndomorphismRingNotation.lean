import Mathlib.RingTheory.PicardGroup
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.FrobeniusOrder
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.WeakEquivalence

/-!
# The LMFDB notation for the endomorphism rings of an isogeny class over a finite field

When the Weil polynomial `h` of an isogeny class of abelian varieties over `𝔽_q` is squarefree,
the endomorphism rings of its abelian varieties are overorders `S` of the Frobenius order `ℤ[F, V]`
in the étale algebra `K = ℚ[F]` (`Polynomial.frobeniusOrder`), and for an ordinary class every
overorder occurs (Deligne). The LMFDB draws them as a graph, ordered by inclusion, and writes each
as `[index]^{#weak · #Pic}_i`:

* `index` is the index `[𝒪_K : S]` of `S` in the maximal order `𝒪_K` of `K`, as additive groups;
* `#weak` is the number of weak equivalence classes of fractional `ℤ[F, V]`-ideals `I` whose
  multiplier ring `(I : I) = {x ∈ K | xI ⊆ I}` is `S`, omitted when it is `1`, which happens
  exactly when `S` is Gorenstein;
* `#Pic` is the order of the Picard group `Pic(S)` (LMFDB `av.fq.picard_group`);
* `i` is a counter that distinguishes `S` among the overorders of `ℤ[F, V]` of the same index.

The first three are defined here for subrings `S` and `R` of any commutative ring `K`, with the
fractional ideals of `R` in place of those of `ℤ[F, V]`. The counter `i` is an enumeration of the
LMFDB's database that the knowl does not define: this database numbering is not formalised. Neither
are the characterisation of Gorenstein orders by `#weak = 1` nor the finiteness of the two counts
for orders of étale `ℚ`-algebras. The knowl describes `#Pic` as the number of invertible fractional
`S`-ideals; it is the number of their isomorphism classes, the order of `Pic(S)`.

The index is also the component `N` of the label `g.q.isog.N.i` of an endomorphism ring
(LMFDB `av.fq.lmfdb_label`).

## Main definitions

* `Subalgebra.maximalOrderIndex` (LMFDB `av.fq.endomorphism_ring_notation`, `av.fq.lmfdb_label`):
  the index `[𝒪_K : S]`.
* `Subalgebra.weakClassCount` (LMFDB `av.fq.endomorphism_ring_notation`): the number `#weak` of weak
  equivalence classes of fractional `R`-ideals with multiplier ring `S`.
* `Subalgebra.picardCard` (LMFDB `av.fq.endomorphism_ring_notation`): the order `#Pic` of the
  Picard group of `S`.

## Main results

* `Subalgebra.maximalOrderIndex_eq_one_iff`: a subring of the maximal order has index `1` if and
  only if it is the maximal order.
-/

open scoped nonZeroDivisors

namespace Subalgebra

variable {K : Type*} [CommRing K] (S R : Subalgebra ℤ K)

/-- The **index** (LMFDB `av.fq.endomorphism_ring_notation`, `av.fq.lmfdb_label`) of a subring `S`
of a commutative ring `K`: the index `[𝒪_K : S]` of the additive group of `S` in that of the
maximal order `𝒪_K`, the integral closure of `ℤ` in `K`. The LMFDB's `S` is an endomorphism ring
of an abelian variety over `𝔽_q`, an overorder of the Frobenius order `ℤ[F, V]` in the étale
algebra `K = ℚ[F]`, contained in `𝒪_K`; for `S = ℤ[F, V]` this is `Polynomial.frobeniusOrderIndex`.
It is `0` when the index is infinite. -/
noncomputable def maximalOrderIndex : ℕ :=
  S.toSubmodule.toAddSubgroup.relIndex (integralClosure ℤ K).toSubmodule.toAddSubgroup

/-- The **number of weak equivalence classes** `#weak` (LMFDB `av.fq.endomorphism_ring_notation`)
of a subring `S` of a commutative ring `K`, relative to a subring `R`: the number of weak
equivalence classes (`FractionalIdeal.WeakEquivalenceClass`) of fractional `R`-ideals `I` of `K`
whose multiplier ring `(I : I) = {x ∈ K | xI ⊆ I}` is `S`. The LMFDB's `R` is the Frobenius order
`ℤ[F, V]` of an isogeny class over `𝔽_q` and `S` one of its overorders in `K = ℚ[F]`; weakly
equivalent fractional ideals have the same multiplier ring (not formalised here), so these classes
are those of the ideals with multiplier ring `S`. For two such ideals `I` and `J`, weak equivalence
as fractional `R`-ideals and as fractional `S`-ideals (LMFDB `av.fq.weak_equivalence_class`) are
the same condition, `1 ∈ (I : J)(J : I)` (Dade, Taussky and Zassenhaus; not formalised here). The
fractional ideals of Mathlib that the LMFDB excludes, such as `0`, have multiplier rings that are
not orders, so the condition `(I : I) = S` leaves them out when `S` is an order. It is `0` when
there are infinitely many classes. -/
noncomputable def weakClassCount : ℕ :=
  (Quotient.mk (FractionalIdeal.weakEquivalenceSetoid R⁰ K) ''
    {I | (((I : Submodule R K) / I : Submodule R K) : Set K) = S}).ncard

/-- The **order of the Picard group** `#Pic` (LMFDB `av.fq.endomorphism_ring_notation`) of a
commutative ring `S`, here a subring of a commutative ring `K`: the number of isomorphism classes
of invertible `S`-modules, which for an order `S` of an étale `ℚ`-algebra are the classes of its
invertible fractional ideals (LMFDB `av.fq.picard_group`). It is `0` when the Picard group is
infinite. -/
noncomputable def picardCard : ℕ :=
  Nat.card (CommRing.Pic S)

variable {S} in
/-- **A subring of the maximal order has index `1` if and only if it is the maximal order.** -/
lemma maximalOrderIndex_eq_one_iff (hS : S ≤ integralClosure ℤ K) :
    S.maximalOrderIndex = 1 ↔ S = integralClosure ℤ K := by
  rw [maximalOrderIndex, AddSubgroup.relIndex_eq_one, Submodule.toAddSubgroup_le,
    toSubmodule.le_iff_le]
  exact ⟨hS.antisymm, fun h ↦ h.ge⟩

end Subalgebra

namespace Polynomial

lemma maximalOrderIndex_frobeniusOrder (q : ℕ) (h : ℤ[X]) :
    (h.frobeniusOrder q).maximalOrderIndex = h.frobeniusOrderIndex q :=
  rfl

end Polynomial
