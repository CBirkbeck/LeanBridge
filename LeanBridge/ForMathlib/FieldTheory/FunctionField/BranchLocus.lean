import TauCeti.FieldTheory.FunctionField.Different.Hurwitz

/-!
# The branch locus of a cover of the projective line from its genus

Let `F / k(t)` be a finite extension of the rational function field over a field `k` of
characteristic zero, with exact constant field `k`, and let `S` be a set of places of `k(t)`. In
characteristic zero every place is tame, so the Riemann–Hurwitz formula reads
`2g - 2 = -2 [F : k(t)] + ∑_P (e_P - 1) deg P`, the sum running over the places `P` of `F`
(Tau Ceti's `TauCeti.hurwitz_genus_formula_ratFunc` and
`TauCeti.Divisor.tameDifferent_eq_different_iff`). Keeping only the places over `S` gives the genus
that the ramification over `S` predicts, and the other terms of the sum are nonnegative. So `F` has
the predicted genus exactly when `F / k(t)` is unramified outside `S`.

This is how the LMFDB certifies its Belyi maps (LMFDB `rcs.rigor.belyi`): having checked the
ramification of a map `X → ℙ¹` over `0`, `1` and `∞`, it checks that `X` has the genus this
ramification predicts, and concludes by the Riemann–Hurwitz formula that there is no other
ramification, so that the map is a Belyi map. Tau Ceti's `IsAlgebraicBelyiPair` (on its main
branch) asks exactly that every place of `F` over a place of `k(t)` other than `t = 0`, `t = 1`
and `t = ∞` have ramification index `1`.

## Main results

* `TauCeti.two_mul_genus_sub_two_eq_iff_forall_ramificationIdx_eq_one`: the genus is the one that
  the ramification over `S` predicts if and only if `F / k(t)` is unramified outside `S`.
* `TauCeti.ramificationIdx_eq_one_of_two_mul_genus_sub_two_eq` (LMFDB `rcs.rigor.belyi`): the case
  of the places `t = 0`, `t = 1` and `t = ∞`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.4.13 and Corollary 3.5.6.
-/

open Polynomial TauCeti AlgebraicGeometry

namespace TauCeti

private lemma degree_filter_eq_degree_iff {K E : Type*} [Field K] [Field E] [Algebra K E]
    (hE : IsFunctionField K E) {D : Divisor K E} (hD : 0 ≤ D) (p : Place K E → Prop)
    [DecidablePred p] : Divisor.degree (D.filter p) = Divisor.degree D ↔ ∀ P, D P ≠ 0 → p P := by
  have hle : D.filter p ≤ D := WeilDivisor.le_iff.mpr fun P ↦ by
    rw [WeilDivisor.coeff, WeilDivisor.coeff, Finsupp.filter_apply]
    split_ifs
    exacts [le_rfl, WeilDivisor.le_iff.mp hD P]
  rw [← Finsupp.filter_eq_self_iff]
  exact ⟨Divisor.eq_of_le_of_degree_eq hE hle, congrArg _⟩

variable {k F : Type*} [Field k] [CharZero k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- **The Riemann–Hurwitz formula detects the branch locus** (LMFDB `rcs.rigor.belyi`): for a
finite extension `F` of `k(t)` in characteristic zero with exact constant field `k` and a set `S` of
places of `k(t)`, the genus `g` of `F` satisfies
`2g - 2 = -2 [F : k(t)] + ∑_{P ∣ S} (e_P - 1) deg P`, the sum running over the places of `F` above
`S`, if and only if every place of `F` that does not lie above `S` is unramified. -/
lemma two_mul_genus_sub_two_eq_iff_forall_ramificationIdx_eq_one (hex : IsIntegrallyClosedIn k F)
    (S : Set (Place k (RatFunc k)))
    [DecidablePred fun P : Place k F ↦ P.restrict k (RatFunc k) ∈ S] : 2 * (genus k F : ℤ) - 2 =
        -2 * Module.finrank (RatFunc k) F +
          Divisor.degree ((Divisor.tameDifferent k F (IsFunctionField.ratFunc k)).filter
            fun P ↦ P.restrict k (RatFunc k) ∈ S) ↔
      ∀ P : Place k F, P.restrict k (RatFunc k) ∉ S → Place.ramificationIdx (RatFunc k) P = 1 := by
  have hT : Divisor.tameDifferent k F (IsFunctionField.ratFunc k) =
      Divisor.different k F (IsFunctionField.ratFunc k) :=
    (Divisor.tameDifferent_eq_different_iff k F _).mpr fun P ↦ Place.isTame_of_charZero k _ P
  rw [hurwitz_genus_formula_ratFunc hex, ← hT, add_right_inj, eq_comm,
    degree_filter_eq_degree_iff (isFunctionField_iff_functionField.mpr inferInstance)
      (Divisor.zero_le_tameDifferent k F _)]
  refine forall_congr' fun P ↦ ?_
  have h₁ : Divisor.tameDifferent k F (IsFunctionField.ratFunc k) P =
      (Place.ramificationIdx (RatFunc k) P : ℤ) - 1 :=
    Divisor.coeff_tameDifferent k F _ P
  have h₂ : 0 < Place.ramificationIdx (RatFunc k) P := Place.ramificationIdx_pos (RatFunc k) P
  rw [not_imp_comm]
  exact imp_congr_right fun _ ↦ by omega

open scoped Classical in
/-- **A cover of the projective line with the predicted genus is a Belyi map** (LMFDB
`rcs.rigor.belyi`): if the genus of `F` is the one that its ramification over `t = 0`, `t = 1` and
`t = ∞` predicts by the Riemann–Hurwitz formula, then every place of `F` over another place of
`k(t)` is unramified. -/
lemma ramificationIdx_eq_one_of_two_mul_genus_sub_two_eq (hex : IsIntegrallyClosedIn k F) :
    letI S : Set (Place k (RatFunc k)) := {Place.adicOfIrreducible irreducible_X,
      Place.adicOfIrreducible (irreducible_X_sub_C 1), Place.infty k}
    2 * (genus k F : ℤ) - 2 = -2 * Module.finrank (RatFunc k) F +
        Divisor.degree ((Divisor.tameDifferent k F (IsFunctionField.ratFunc k)).filter
          fun P ↦ P.restrict k (RatFunc k) ∈ S) →
      ∀ P : Place k F, P.restrict k (RatFunc k) ∉ S → Place.ramificationIdx (RatFunc k) P = 1 :=
  (two_mul_genus_sub_two_eq_iff_forall_ramificationIdx_eq_one hex _).mp

end TauCeti
