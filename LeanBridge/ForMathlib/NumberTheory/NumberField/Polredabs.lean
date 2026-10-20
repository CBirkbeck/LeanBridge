import LeanBridge.ForMathlib.NumberTheory.NumberField.FieldIndex
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial
import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Reduced defining polynomials of number fields

A defining polynomial of a number field `K` is a monic integer polynomial `P` with
`K ≅ ℚ[X] / (P)`. Among the defining polynomials of `K`, the reduced one (the output of PARI's
`polredabs`) has minimal `T₂` norm `∑ |α|²`, then minimal absolute discriminant, and is then the
least for the lexicographic order on `S(P) = (|a₁|, a₁, …, |aₙ|, aₙ)`. It exists because there are
only finitely many defining polynomials of bounded `T₂` norm, and it is unique because `S(P)`
determines `P`.

## Main definitions

* `Polynomial.t2Norm`: the `T₂` norm of an integer polynomial.
* `Polynomial.polredabsKey`: the vector `S(P)`.
* `NumberField.IsDefiningPolynomial` (LMFDB `nf.polredabs`): defining polynomials.
* `NumberField.IsPolredabs` (LMFDB `nf.polredabs`): the reduced defining polynomial.
* `NumberField.polredabs`: the reduced defining polynomial of `K`.

## Main results

* `Polynomial.eq_of_polredabsKey_eq`: a monic polynomial is determined by its vector `S(P)`.
* `NumberField.finite_setOf_isDefiningPolynomial_t2Norm_le`: there are finitely many defining
  polynomials of bounded `T₂` norm.
* `NumberField.exists_isPolredabs`: every number field has a reduced defining polynomial.
* `NumberField.IsPolredabs.eq`: the reduced defining polynomial is unique.
* `NumberField.isPolredabs_polredabs`: `NumberField.polredabs K` is the reduced defining polynomial
  of `K`.
-/

open Polynomial Prod.Lex

namespace Polynomial

variable (P : ℤ[X]) {Q : ℤ[X]}

/-- The **`T₂` norm** of an integer polynomial `P` (LMFDB `nf.polredabs`): the sum of the squared
absolute values of the complex roots of `P`, counted with multiplicity. -/
noncomputable def t2Norm : ℝ :=
  ((P.map (Int.castRingHom ℂ)).roots.map fun z ↦ ‖z‖ ^ 2).sum

/-- The vector `S(P) = (|a₁|, a₁, …, |aₙ|, aₙ)` of a polynomial `P = a₀ Xⁿ + a₁ Xⁿ⁻¹ + ⋯ + aₙ` with
`a₀ ≠ 0` (LMFDB `nf.polredabs`, where `P` is monic), made of the coefficients after the leading
one. -/
def polredabsKey : List ℤ :=
  P.coeffList.tail.flatMap fun a ↦ [|a|, a]

private lemma eq_of_flatMap_eq {l m : List ℤ}
    (h : (l.flatMap fun a ↦ [|a|, a]) = m.flatMap fun a ↦ [|a|, a]) : l = m := by
  induction l generalizing m with
  | nil => cases m <;> simp_all
  | cons a l ih =>
    cases m with
    | nil => simp at h
    | cons b m =>
      simp only [List.flatMap_cons, List.cons_append, List.cons.injEq] at h
      rw [h.2.1, ih h.2.2]

variable {P}

/-- A monic polynomial is determined by its vector `S(P)`. -/
lemma eq_of_polredabsKey_eq (hP : P.Monic) (hQ : Q.Monic) (h : P.polredabsKey = Q.polredabsKey) :
    P = Q := by
  rcases coeffList_eq_cons_leadingCoeff hP.ne_zero with ⟨l, hl⟩
  rcases coeffList_eq_cons_leadingCoeff hQ.ne_zero with ⟨m, hm⟩
  rw [polredabsKey, polredabsKey, hl, hm, List.tail_cons, List.tail_cons] at h
  rw [← ofCoeffList_reverse_coeffList P, ← ofCoeffList_reverse_coeffList Q, hl, hm,
    hP.leadingCoeff, hQ.leadingCoeff, eq_of_flatMap_eq h]

lemma sq_norm_le_t2Norm {z : ℂ} (hz : z ∈ (P.map (Int.castRingHom ℂ)).roots) : ‖z‖ ^ 2 ≤ P.t2Norm :=
  Multiset.single_le_sum (Multiset.forall_mem_map_iff.mpr fun _ _ ↦ sq_nonneg _) _ <|
    Multiset.mem_map_of_mem _ hz

lemma mahlerMeasure_le_of_t2Norm_le (hP : P.Monic) {B : ℝ} (h : P.t2Norm ≤ B) :
    (P.map (Int.castRingHom ℂ)).mahlerMeasure ≤ max 1 √B ^ P.natDegree :=
  hP.mahlerMeasure_map_le fun _ hz ↦ Real.le_sqrt_of_sq_le <| (sq_norm_le_t2Norm hz).trans h

end Polynomial

namespace NumberField

variable (K : Type*) [Field K] [NumberField K] {P Q : ℤ[X]}

variable (P) in
/-- A **defining polynomial** of a number field `K` (LMFDB `nf.polredabs`): a monic polynomial
`P ∈ ℤ[X]` such that `K ≅ ℚ[X] / (P)`. -/
def IsDefiningPolynomial : Prop :=
  P.Monic ∧ Nonempty (AdjoinRoot (P.map (Int.castRingHom ℚ)) ≃ₐ[ℚ] K)

variable (P) in
/-- `P` is the **reduced defining polynomial** of a number field `K` (LMFDB `nf.polredabs`), the
output of PARI's `polredabs`: a defining polynomial of `K` that is least among the defining
polynomials of `K` for the lexicographic order on `(T₂(P), |disc P|, S(P))`. That is, `P` has
minimal `T₂` norm, then minimal absolute discriminant among those, and comes first among those for
the lexicographic order on `S(P)`. It exists (`exists_isPolredabs`) and is unique
(`IsPolredabs.eq`). -/
def IsPolredabs : Prop :=
  IsDefiningPolynomial K P ∧ ∀ Q : ℤ[X], IsDefiningPolynomial K Q →
    toLex (P.t2Norm, toLex (|P.discr|, P.polredabsKey)) ≤
      toLex (Q.t2Norm, toLex (|Q.discr|, Q.polredabsKey))

variable {K} in
lemma IsDefiningPolynomial.natDegree_eq (h : IsDefiningPolynomial K P) :
    P.natDegree = Module.finrank ℚ K := by
  rcases h with ⟨hP, ⟨e⟩⟩
  rw [← e.toLinearEquiv.finrank_eq, ← hP.natDegree_map (Int.castRingHom ℚ)]
  exact finrank_quotient_span_eq_natDegree.symm

lemma exists_isDefiningPolynomial : ∃ P, IsDefiningPolynomial K P := by
  rcases nonempty_integralPrimitiveElement K with ⟨θ, hθ⟩
  refine ⟨minpoly ℤ θ, minpoly.monic θ.isIntegral, ⟨?_⟩⟩
  have hint : IsIntegral ℚ (θ : K) := IsIntegral.of_finite ℚ _
  have htop : IntermediateField.adjoin ℚ {(θ : K)} = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic fun x _ ↦ IsAlgebraic.of_finite ℚ x).mpr hθ
  rw [← RingOfIntegers.minpoly_coe, ← algebraMap_int_eq,
    ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ θ.isIntegral_coe]
  exact ((IntermediateField.adjoinRootEquivAdjoin ℚ hint).trans
    (IntermediateField.equivOfEq htop)).trans IntermediateField.topEquiv

/-- A number field has finitely many defining polynomials of bounded `T₂` norm: their roots are
bounded, so their Mahler measures are, and Northcott's theorem applies. -/
lemma finite_setOf_isDefiningPolynomial_t2Norm_le (B : ℝ) :
    {P : ℤ[X] | IsDefiningPolynomial K P ∧ P.t2Norm ≤ B}.Finite :=
  finite_mahlerMeasure_le (Module.finrank ℚ K) ⟨max 1 √B ^ Module.finrank ℚ K, by positivity⟩
    |>.subset fun _ ⟨hP, hB⟩ ↦
      ⟨hP.natDegree_eq.le, hP.natDegree_eq ▸ mahlerMeasure_le_of_t2Norm_le hP.1 hB⟩

/-- Every number field has a reduced defining polynomial. -/
lemma exists_isPolredabs : ∃ P, IsPolredabs K P := by
  rcases exists_isDefiningPolynomial K with ⟨P₀, hP₀⟩
  rcases Set.exists_min_image {P | IsDefiningPolynomial K P ∧ P.t2Norm ≤ P₀.t2Norm}
    (fun P ↦ toLex (P.t2Norm, toLex (|P.discr|, P.polredabsKey)))
    (finite_setOf_isDefiningPolynomial_t2Norm_le K _) ⟨P₀, hP₀, le_rfl⟩ with ⟨P, ⟨hP, hPB⟩, hmin⟩
  refine ⟨P, hP, fun Q hQ ↦ ?_⟩
  rcases le_or_gt Q.t2Norm P₀.t2Norm with h | h
  · exact hmin Q ⟨hQ, h⟩
  · exact (toLex_lt_toLex.mpr (.inl (hPB.trans_lt h))).le

variable {K} in
/-- The reduced defining polynomial of a number field is unique. -/
lemma IsPolredabs.eq (hP : IsPolredabs K P) (hQ : IsPolredabs K Q) : P = Q :=
  eq_of_polredabsKey_eq hP.1.1 hQ.1.1 <| congrArg (fun x ↦ (ofLex (ofLex x).2).2) <|
    (hP.2 Q hQ.1).antisymm (hQ.2 P hP.1)

/-- The **reduced defining polynomial** of a number field `K` (LMFDB `nf.polredabs`), the
polynomial `P` with `IsPolredabs K P`. -/
noncomputable def polredabs : ℤ[X] :=
  (exists_isPolredabs K).choose

/-- `polredabs K` is the reduced defining polynomial of `K`. -/
lemma isPolredabs_polredabs : IsPolredabs K (polredabs K) :=
  (exists_isPolredabs K).choose_spec

end NumberField
