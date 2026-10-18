/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanBridge.IdealArithmetic.Galois.Parity

/-!
# Degree-3 milestone — the Galois group of an irreducible cubic

The first end-to-end certified Galois group: for an irreducible cubic over `ℚ`, the Galois group is
cyclic of order 3 (`A₃`) exactly when the discriminant is a square, and `S₃` (order 6) otherwise.
Combines Core Theorem 2 (`range_galActionHom_le_alternatingGroup_iff`) with the fact that the image
of `Gal` is a transitive subgroup of `S₃`.

See `.mathlib-quality/tickets.md`, T007.
-/

namespace IdealArithmetic.Galois

open Polynomial Finset Polynomial.Gal

attribute [local instance] factSplitsSplittingField

/-- A subgroup of a symmetric group with exactly three elements lies in the alternating group: each
element has order dividing `3`, hence odd, so its sign (a square root of unity of that odd order) is
`1`. This is general (no cubic-specific data) and could live in `Parity.lean`. -/
private lemma le_alternatingGroup_of_card_eq_three {α : Type*} [DecidableEq α] [Fintype α]
    {G : Subgroup (Equiv.Perm α)} (hG : Nat.card G = 3) : G ≤ alternatingGroup α := by
  intro x hx
  rw [Equiv.Perm.mem_alternatingGroup]
  have hdvd : orderOf (⟨x, hx⟩ : G) ∣ 3 := hG ▸ orderOf_dvd_natCard (⟨x, hx⟩ : G)
  have hpow : x ^ orderOf (⟨x, hx⟩ : G) = 1 := by
    have h := congrArg G.subtype (pow_orderOf_eq_one (⟨x, hx⟩ : G))
    rwa [map_pow, map_one] at h
  have hsign : Equiv.Perm.sign x ^ orderOf (⟨x, hx⟩ : G) = 1 := by
    have h := congrArg Equiv.Perm.sign hpow
    rwa [map_pow, map_one] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign x) with h1 | hm1
  · exact h1
  · exfalso
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h <;>
      rw [h, hm1] at hsign <;> revert hsign <;> decide

/-- A monic irreducible cubic over `ℚ` has exactly three roots in its splitting field. -/
private lemma card_rootSet_cubic (p : ℚ[X]) (hp : Irreducible p) (h3 : p.natDegree = 3) :
    Fintype.card {x // x ∈ p.rootSet p.SplittingField} = 3 := by
  rw [card_rootSet_eq_natDegree hp.separable (IsSplittingField.splits p.SplittingField p), h3]

/-- The Galois group of `p` is isomorphic to the image of `galActionHom`, so they have equal
cardinality. -/
private lemma card_gal_eq_card_range (p : ℚ[X]) :
    Nat.card p.Gal = Nat.card (galActionHom p p.SplittingField).range :=
  Nat.card_congr (MonoidHom.ofInjective (galActionHom_injective p p.SplittingField)).toEquiv

/-- For a monic irreducible cubic the Galois group acts transitively on the three roots, so by
orbit–stabiliser `3` divides its order. -/
private lemma three_dvd_card_gal_of_irreducible_cubic (p : ℚ[X]) (hp : Irreducible p)
    (h3 : p.natDegree = 3) : 3 ∣ Nat.card p.Gal := by
  classical
  have hcardRoot := card_rootSet_cubic p hp h3
  have hcardRootN : Nat.card {x // x ∈ p.rootSet p.SplittingField} = 3 :=
    Nat.card_eq_fintype_card.trans hcardRoot
  have hpt : MulAction.IsPretransitive p.Gal (p.rootSet p.SplittingField) :=
    galAction_isPretransitive p p.SplittingField hp
  obtain ⟨x⟩ : Nonempty (p.rootSet p.SplittingField) := by
    rw [← Fintype.card_pos_iff, hcardRoot]; norm_num
  -- Pin `galAction` explicitly: `galActionAux` also provides `MulAction p.Gal (rootSet p SF)`,
  -- so bare instance synthesis picks the wrong `MulAction` and `hpt` fails to match.
  have hidx := @MulAction.index_stabilizer_of_transitive p.Gal _ _
    (Polynomial.Gal.galAction p p.SplittingField) x hpt
  have hdvd := Subgroup.index_dvd_card
    (@MulAction.stabilizer p.Gal _ _ (Polynomial.Gal.galAction p p.SplittingField) x)
  rwa [hidx, hcardRootN] at hdvd

/-- The Galois group of a cubic embeds in the symmetric group on its three roots, so its order
divides `3! = 6`. -/
private lemma card_gal_cubic_dvd_six (p : ℚ[X]) (hp : Irreducible p) (h3 : p.natDegree = 3) :
    Nat.card p.Gal ∣ 6 := by
  classical
  have hcardRootN : Nat.card {x // x ∈ p.rootSet p.SplittingField} = 3 :=
    Nat.card_eq_fintype_card.trans (card_rootSet_cubic p hp h3)
  rw [card_gal_eq_card_range p]
  have h := Subgroup.card_subgroup_dvd_card (galActionHom p p.SplittingField).range
  rwa [Nat.card_perm, hcardRootN] at h

/-- **First conjunct of T007.** When the discriminant is a square, the image of `Gal` lies in the
alternating group `A₃` (order `3`), and combined with `3 ∣ Nat.card p.Gal` this pins the order to
`3`. -/
private lemma card_gal_cubic_eq_three_of_isSquare_discr (p : ℚ[X]) (hp : Irreducible p)
    (hmonic : p.Monic) (h3 : p.natDegree = 3) (hsq : IsSquare p.discr) :
    Nat.card p.Gal = 3 := by
  classical
  have hcardRoot := card_rootSet_cubic p hp h3
  have : Nontrivial {x // x ∈ p.rootSet p.SplittingField} :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [hcardRoot]; norm_num)
  have hcardA3 : Nat.card (alternatingGroup {x // x ∈ p.rootSet p.SplittingField}) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, hcardRoot]; decide
  refine Nat.dvd_antisymm ?_ (three_dvd_card_gal_of_irreducible_cubic p hp h3)
  rw [card_gal_eq_card_range p, ← hcardA3]
  exact Subgroup.card_dvd_of_le
    ((range_galActionHom_le_alternatingGroup_iff p hmonic hp.separable).mpr hsq)

/-- **Second conjunct of T007.** When the discriminant is not a square, the image of `Gal` is not
contained in `A₃`, so its order (a multiple of `3` dividing `6`) cannot be `3`, forcing it to be
`6`. -/
private lemma card_gal_cubic_eq_six_of_not_isSquare_discr (p : ℚ[X]) (hp : Irreducible p)
    (hmonic : p.Monic) (h3 : p.natDegree = 3) (hnsq : ¬ IsSquare p.discr) :
    Nat.card p.Gal = 6 := by
  classical
  have h3dvd := three_dvd_card_gal_of_irreducible_cubic p hp h3
  have hdvd6 := card_gal_cubic_dvd_six p hp h3
  have hn3 : Nat.card p.Gal ≠ 3 := by
    intro hEq
    refine hnsq ((range_galActionHom_le_alternatingGroup_iff p hmonic hp.separable).mp
      (le_alternatingGroup_of_card_eq_three ?_))
    rw [← card_gal_eq_card_range p]; exact hEq
  have hle6 : Nat.card p.Gal ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
  interval_cases (Nat.card p.Gal) <;> omega

/-- **T007 / Milestone M1.** For a monic irreducible cubic over `ℚ`, the Galois group has order 3
when the discriminant is a square (the group is `A₃`), and order 6 otherwise (the group is `S₃`). -/
theorem galoisGroup_cubic (p : ℚ[X]) (hp : Irreducible p) (hmonic : p.Monic)
    (h3 : p.natDegree = 3) :
    (IsSquare p.discr → Nat.card p.Gal = 3) ∧ (¬ IsSquare p.discr → Nat.card p.Gal = 6) :=
  ⟨card_gal_cubic_eq_three_of_isSquare_discr p hp hmonic h3,
   card_gal_cubic_eq_six_of_not_isSquare_discr p hp hmonic h3⟩

end IdealArithmetic.Galois
