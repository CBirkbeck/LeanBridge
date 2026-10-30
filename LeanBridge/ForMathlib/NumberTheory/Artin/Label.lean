import LeanBridge.ForMathlib.NumberTheory.Artin.Conductor
import LeanBridge.ForMathlib.RepresentationTheory.PermutationContainer
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Simproc.Factors

/-!
# The label of an Artin representation

The LMFDB label of an Artin representation `ρ` has the form `A.B.C.DcE` (LMFDB `artin.label`),
where `A` is the dimension of `ρ`, `B` its conductor in factored form, `C` the smallest
permutation representation containing `ρ`, written `dtj` for its degree `d` and its T-number `j`
when the degree is small enough (below `48` and not `32`, LMFDB `artin.permutation_container`),
and `d` otherwise, `D` an index that tells apart the representations that are not Galois conjugate
and share `A`, `B` and `C`, and `E` the index of `ρ` in its Galois orbit. The factored form of a
positive integer `N = p₁ ^ a₁ ⋯ pₖ ^ aₖ` lists the factors `pᵢ ^ aᵢ`, written `pᵢeaᵢ`, separated
by underscores: `2e3_59` is `2 ^ 3 · 59`.

We formalise the prefix `A.B.d`, for a representation of the Galois group of a finite Galois
extension `K / ℚ` through which an Artin representation factors: its dimension, its conductor
(LeanBridge's `Representation.artinConductor`) and the degree `d` of a smallest permutation
representation containing it (LeanBridge's `Representation.minPermutationDegree`). LeanBridge's
conductor is the real number `∏_p p ^ f(ρ, p)`, as Artin's theorem that the exponents `f(ρ, p)`
are integers is not proved, so the prefix is a relation: `s` is the prefix of `ρ` when it is
`A.B.d` for a natural number whose cast is the conductor, which then determines it
(`Representation.IsArtinLabelPrefix.eq`). The factored form of the conductor lists the primes in
increasing order and omits the exponents `1`, as in the knowl's example, and writes `1` for the
conductor `1`.

The rest of the label is not formalised: the T-number `j` of the permutation representation, and
the indices `D` and `E`, follow orderings of the database (GAP's numbering of transitive groups and
LMFDB orderings of representations and of Galois orbits) that the knowl does not specify.

## Main definitions

* `Nat.lmfdbFactoredForm` (LMFDB `artin.label`): the factored form of a positive integer.
* `Representation.IsArtinLabelPrefix` (LMFDB `artin.label`): the prefix `A.B.d` of the label of an
  Artin representation.

## Main results

* `Nat.lmfdbFactoredForm_four_hundred_seventy_two`: the knowl's example, `472` is written
  `2e3_59`.
* `Representation.IsArtinLabelPrefix.eq`: a representation has at most one label prefix.
-/

namespace Nat

/-- The **factored form** (LMFDB `artin.label`) of a positive integer `N`: writing
`N = p₁ ^ a₁ ⋯ pₖ ^ aₖ` for primes `p₁ < ⋯ < pₖ` and exponents `aᵢ ≥ 1`, the factors `pᵢ`,
followed by `e aᵢ` when `aᵢ > 1`, joined by underscores, so that `472 = 2 ^ 3 · 59` is written
`2e3_59` (`lmfdbFactoredForm_four_hundred_seventy_two`). The empty product `1` is written `1`. -/
def lmfdbFactoredForm (N : ℕ) : String :=
  if N = 1 then "1" else "_".intercalate <| N.primeFactorsList.dedup.map fun p ↦
    toString p ++ if N.factorization p = 1 then "" else "e" ++ toString (N.factorization p)

/-- **The knowl's example**: `472 = 2 ^ 3 · 59` has the factored form `2e3_59`. -/
lemma lmfdbFactoredForm_four_hundred_seventy_two : lmfdbFactoredForm 472 = "2e3_59" := by
  have h : primeFactorsList 472 = [2, 2, 2, 59] := by
    simp
  simp only [lmfdbFactoredForm, ← primeFactorsList_count_eq, h]
  decide

end Nat

namespace Representation

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ Gal(K/ℚ) V) {s t : String}

variable (s) in
/-- `s` is the **label prefix** `A.B.d` (LMFDB `artin.label`) of a representation `ρ` of the Galois
group of a finite Galois extension `K / ℚ`, through which an Artin representation factors: `A` is
the dimension of `ρ`, `B` the factored form (`Nat.lmfdbFactoredForm`) of its conductor `N`, and
`d` the smallest degree of a permutation representation containing `ρ`
(`Representation.minPermutationDegree`), separated by dots. The conductor `N` is a positive
integer by Artin's theorem, which is not proved here, where it is the real number
`Representation.artinConductor`: `s` is the prefix when it is `A.B.d` for a natural number `N`
whose cast is the conductor. The prefix is then unique (`IsArtinLabelPrefix.eq`). The LMFDB label
continues with the T-number of the permutation representation, when its degree is small enough,
and with two indices, which are database orderings that the knowl does not specify and are not
formalised. -/
def IsArtinLabelPrefix : Prop :=
  ∃ N : ℕ, (N : ℝ) = ρ.artinConductor ∧ s = toString (Module.finrank ℂ V) ++ "." ++
    N.lmfdbFactoredForm ++ "." ++ toString ρ.minPermutationDegree

variable {ρ} in
/-- **A representation has at most one label prefix**, since a real number is the cast of at most
one natural number. -/
lemma IsArtinLabelPrefix.eq (hs : ρ.IsArtinLabelPrefix s) (ht : ρ.IsArtinLabelPrefix t) :
    s = t := by
  rcases hs with ⟨N, hN, rfl⟩
  rcases ht with ⟨M, hM, rfl⟩
  rw [Nat.cast_injective (hN.trans hM.symm)]

end Representation
