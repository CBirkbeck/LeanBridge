import TauCeti.FieldTheory.FunctionField.Automorphism.FixedField
import TauCeti.FieldTheory.FunctionField.Different.Divisor
import TauCeti.FieldTheory.FunctionField.Different.Galois
import TauCeti.FieldTheory.FunctionField.Different.Hurwitz
import TauCeti.FieldTheory.FunctionField.Different.Tame
import TauCeti.FieldTheory.FunctionField.Place.Extension.Galois
import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The signature of a finite group of automorphisms of a function field

Let `G` be a finite group of automorphisms of a curve `X` over a field `k`, a compact Riemann
surface when `k = ℂ`, and let `F = k(X)`, on which `G` acts. The quotient curve `Y = X / G` has
function field the fixed field `F^G`, of genus `g₀` (LMFDB `curve.highergenus.aut.quotientgenus`),
and `F / F^G` is a Galois extension with group `G`. The closed points of `Y` are the places of
`F^G`, and all the places of `F` over a place `P` of `F^G` share one ramification index `e_P`. The
branch points of `X → Y` are the places `P` with `e_P > 1`, finitely many, and over `ℂ` the
monodromy of a standard generator of `π₁(Y - B, y₀)` around a branch point `P` has order `e_P`, the
order of the stabiliser of a point over `P`. So the signature `[g₀; m₁, …, m_r]` of the action
(LMFDB `curve.highergenus.aut.signature`) is the genus of `F^G` together with the multiset of the
`e_P` over the branch places. This is how it is defined here, intrinsically, for any finite group
`G` of `k`-automorphisms of a function field `F / k`: `MulAction.signature` instead takes the genus
`g₀` as an argument and computes the periods from the monodromy of given loops.

The comparison of the ramification indices with the orders of the monodromy permutations of a
compact Riemann surface, through the Riemann existence theorem, is not formalised.

## Main definitions

* `Subgroup.branchPlaces`: the branch places of `F / F^G`, the places of `F^G` that ramify in `F`.
* `Subgroup.signaturePeriods` (LMFDB `curve.highergenus.aut.signature`): the periods
  `m₁ ≤ ⋯ ≤ m_r`, the ramification indices of the branch places.
* `Subgroup.signature` (LMFDB `curve.highergenus.aut.signature`): the signature
  `[g₀; m₁, …, m_r]`.

## Main results

* `Subgroup.finite_branchPlaces`: there are finitely many branch places.
* `Subgroup.mem_signaturePeriods_iff`: the periods are the ramification indices of the branch
  places.
* `Subgroup.card_signaturePeriods`: there is one period for each branch place.
* `Subgroup.two_le_of_mem_signaturePeriods`: every period is at least two.
* `Subgroup.natCard_stabilizer_eq_ramificationIdxIn`: over an algebraically closed field, the
  ramification index of a place of `F^G`, the period at a branch place, is the order of the
  stabiliser of any place above it.
* `Subgroup.mem_branchPlaces_iff`: over an algebraically closed field, the branch places are the
  places with fewer than `|G|` places above them, the branch points of `X → X / G`.
* `Subgroup.two_mul_genus_sub_two_eq`: the Riemann–Hurwitz formula
  `2g - 2 = |G| (2g₀ - 2 + ∑ (1 - 1/m_i))` over an algebraically closed field of characteristic
  zero.
-/

open TauCeti IntermediateField

namespace Subgroup

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (G : Subgroup (F ≃ₐ[k] F)) [Finite G]
  {m : ℕ} (P' : Place k F)

/-- The **branch places** of a finite group `G` of automorphisms of a function field `F / k`: the
places `P` of the fixed field `F^G`, the function field of the quotient curve `X / G`, that ramify
in `F`, that is whose ramification index `e_P` in the Galois extension `F / F^G` is greater than
one. Over an algebraically closed field, such as `ℂ`, they are the branch points of the projection
`X → X / G` (LMFDB `curve.highergenus.aut.branchpoints`). -/
def branchPlaces : Set (Place k (fixedField G)) :=
  {P | 1 < P.ramificationIdxIn F}

open scoped Classical in
/-- The **periods** `m₁ ≤ ⋯ ≤ m_r` of the signature (LMFDB `curve.highergenus.aut.signature`) of a
finite group `G` of automorphisms of a function field `F / k`: the multiset of the ramification
indices `e_P` of the branch places `P` of `F^G` in `F`, one for each branch place. For a curve over
`ℂ`, `e_P` is the order of the monodromy permutation of a standard generator of `π₁(Y - B, y₀)`
around `P`, as in the knowl (a comparison that is not formalised). The junk value `0` for
infinitely many branch places does not occur (`Subgroup.finite_branchPlaces`). -/
noncomputable def signaturePeriods : Multiset ℕ :=
  if h : G.branchPlaces.Finite then h.toFinset.val.map (·.ramificationIdxIn F) else 0

/-- The **signature** `[g₀; m₁, …, m_r]` (LMFDB `curve.highergenus.aut.signature`) of a finite
group `G` of automorphisms of a function field `F / k`, such as the function field of a curve `X`
over `ℂ` on which `G` acts: the genus `g₀` of the fixed field `F^G`, the function field of the
quotient curve `X / G` (LMFDB `curve.highergenus.aut.quotientgenus`), and the periods
`m₁ ≤ ⋯ ≤ m_r` (`Subgroup.signaturePeriods`), the ramification indices of the branch places. -/
noncomputable def signature : ℕ × Multiset ℕ :=
  (genus k (fixedField G), G.signaturePeriods)

/-- **There are finitely many branch places**: a place of `F^G` that ramifies in `F` has a place
above it with nonzero different exponent, by Dedekind's different theorem, and there are finitely
many such places. -/
lemma finite_branchPlaces (hF : IsFunctionField k F) : G.branchPlaces.Finite := by
  refine (Place.finite_setOf_exists_differentExponent_ne_zero (k' := k) (F' := F) k _
    (hF.fixedField G)).subset fun P hP ↦ ?_
  rcases Place.restrict_surjective_of_finiteDimensional (hF.fixedField G) hF P with ⟨P', hP'⟩
  have hle : P'.ramificationIdx (fixedField G) ≤ P'.differentExponent k (fixedField G) + 1 :=
    P'.ramificationIdx_le_differentExponent_add_one k (fixedField G)
  refine ⟨P', hP', fun h ↦ ?_⟩
  rw [h, ← Place.ramificationIdxIn_eq_ramificationIdx hP'] at hle
  exact (hle.trans_lt hP).false

lemma signaturePeriods_eq (hF : IsFunctionField k F) :
    G.signaturePeriods = (G.finite_branchPlaces hF).toFinset.val.map (·.ramificationIdxIn F) :=
  dite_eq_left (G.finite_branchPlaces hF)

variable {G}

/-- **The periods are the ramification indices of the branch places.** -/
lemma mem_signaturePeriods_iff (hF : IsFunctionField k F) :
    m ∈ G.signaturePeriods ↔ ∃ P ∈ G.branchPlaces, P.ramificationIdxIn F = m := by
  simp [G.signaturePeriods_eq hF]

/-- **There is one period for each branch place.** -/
lemma card_signaturePeriods (hF : IsFunctionField k F) :
    G.signaturePeriods.card = G.branchPlaces.ncard := by
  rw [G.signaturePeriods_eq hF, Multiset.card_map]
  exact (Set.ncard_eq_toFinset_card _ _).symm

/-- **Every period is at least two.** -/
lemma two_le_of_mem_signaturePeriods (hm : m ∈ G.signaturePeriods) : 2 ≤ m := by
  unfold signaturePeriods at hm
  split_ifs at hm with h
  · rcases Multiset.mem_map.mp hm with ⟨P, hP, rfl⟩
    exact (h.mem_toFinset.mp hP : 1 < P.ramificationIdxIn F)
  · exact absurd hm (Multiset.notMem_zero m)

variable (G) in
lemma ncard_setOf_restrict_eq_pos :
    0 < {Q : Place k F | Q.restrict k (fixedField G) = P'.restrict k (fixedField G)}.ncard :=
  (Set.ncard_pos (Place.finite_setOf_restrict_eq k _ _)).mpr ⟨P', rfl⟩

variable [IsAlgClosed k]

variable (G) in
lemma relativeDegree_fixedField_eq_one (hF : IsFunctionField k F) :
    P'.relativeDegree k (fixedField G) = 1 := by
  have hdeg :
      P'.degree = (P'.restrict k (fixedField G)).degree * P'.relativeDegree k (fixedField G) :=
    P'.degree_eq_degree_restrict_mul_relativeDegree k (fixedField G)
  rwa [P'.degree_eq_one_of_isAlgClosed_of_isFunctionField hF,
    (P'.restrict k _).degree_eq_one_of_isAlgClosed_of_isFunctionField (hF.fixedField G), one_mul,
    eq_comm] at hdeg

/-- **Over an algebraically closed field, the ramification index of the place `P` of `F^G` below a
place `P'` of `F` is the order of the stabiliser of `P'`**, in the Galois group `Gal(F / F^G)`,
which is `G` by Artin's theorem: the period at a branch place is the order of the stabiliser of
any place above it. For a curve over `ℂ`, this stabiliser is generated by the monodromy of a
standard generator around the branch point, as in the knowl (which is not formalised). The places
over `P` all have relative degree one, so their number `r` satisfies `r e_P = |G|` by the
fundamental identity, and `r |Stab| = |G|` by the orbit–stabiliser theorem. -/
lemma natCard_stabilizer_eq_ramificationIdxIn (hF : IsFunctionField k F) :
    Nat.card (MulAction.stabilizer (F ≃ₐ[fixedField G] F) P') =
      (P'.restrict k (fixedField G)).ramificationIdxIn F := by
  rw [Place.ramificationIdxIn_eq_ramificationIdx rfl]
  refine Nat.eq_of_mul_eq_mul_left (G.ncard_setOf_restrict_eq_pos P') ?_
  rw [Place.ncard_mul_card_stabilizer_eq_finrank,
    ← Place.ncard_mul_ramificationIdx_mul_relativeDegree_eq_finrank P',
    G.relativeDegree_fixedField_eq_one P' hF, mul_one]

/-- **A place of `F^G` is a branch place exactly when fewer than `|G|` places of `F` lie over it**,
over an algebraically closed field: the places over `P` all have relative degree one, so there are
`|G| / e_P` of them. So the branch places are the branch points of the projection `X → X / G`, the
points whose fibre has fewer than `|G|` points (LMFDB `curve.highergenus.aut.branchpoints`). -/
lemma mem_branchPlaces_iff (hF : IsFunctionField k F) {P : Place k (fixedField G)} :
    P ∈ G.branchPlaces ↔ {Q : Place k F | Q.restrict k (fixedField G) = P}.ncard < Nat.card G := by
  rcases Place.restrict_surjective_of_finiteDimensional (hF.fixedField G) hF P with ⟨P', rfl⟩
  rw [branchPlaces, Set.mem_ofPred_eq, Place.ramificationIdxIn_eq_ramificationIdx rfl,
    ← finrank_fixedField_eq_natCard G,
    ← Place.ncard_mul_ramificationIdx_mul_relativeDegree_eq_finrank P',
    G.relativeDegree_fixedField_eq_one P' hF, mul_one]
  exact (lt_mul_iff_one_lt_right (G.ncard_setOf_restrict_eq_pos P')).symm

variable [CharZero k] in
/-- **The Riemann–Hurwitz formula in terms of the signature**: over an algebraically closed field of
characteristic zero, such as `ℂ`, if `F` has genus `g` and `G` has signature `[g₀; m₁, …, m_r]`,
then `2g - 2 = |G| (2g₀ - 2 + ∑ (1 - 1/m_i))`. -/
lemma two_mul_genus_sub_two_eq (hF : IsFunctionField k F) : 2 * (genus k F : ℚ) - 2 = Nat.card G *
    (2 * genus k (fixedField G) - 2 +
      (G.signaturePeriods.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum) := by
  have hFG : IsFunctionField k (fixedField G) := hF.fixedField G
  have hhur : 2 * (genus k F : ℚ) - 2 =
      Module.finrank (fixedField G) F * (2 * genus k (fixedField G) - 2) +
        Divisor.degree (Divisor.tameDifferent k F hFG) := by
    rw [← geometricDegree_eq_finrank (fixedField G) k F]
    exact_mod_cast (two_mul_genus_sub_two_eq_iff_forall_isTame hFG hF
      isIntegrallyClosedIn_of_isAlgClosed isIntegrallyClosedIn_of_isAlgClosed).mpr fun P ↦
        P.isTame_of_charZero k (fixedField G)
  have hbranch : (Divisor.degree (Divisor.tameDifferent k F hFG) : ℚ) =
      Module.finrank (fixedField G) F * ∑ P ∈ (G.finite_branchPlaces hF).toFinset,
        (1 - 1 / (P.ramificationIdxIn F : ℚ)) * P.degree :=
    Divisor.degree_tameDifferent_eq_finrank_mul_sum hFG hF _ fun P' hP' ↦
      (G.finite_branchPlaces hF).mem_toFinset.mpr <| by
        rwa [branchPlaces, Set.mem_ofPred_eq, Place.ramificationIdxIn_eq_ramificationIdx rfl]
  have hsum : ∑ P ∈ (G.finite_branchPlaces hF).toFinset,
      (1 - 1 / (P.ramificationIdxIn F : ℚ)) * P.degree =
        (G.signaturePeriods.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum := by
    rw [G.signaturePeriods_eq hF, Multiset.map_map, Finset.sum]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun P _ ↦ ?_)
    rw [P.degree_eq_one_of_isAlgClosed_of_isFunctionField hFG]
    simp
  rw [hhur, hbranch, hsum, finrank_fixedField_eq_natCard G]
  ring1

end Subgroup
