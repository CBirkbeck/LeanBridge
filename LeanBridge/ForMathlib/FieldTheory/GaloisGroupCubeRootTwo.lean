import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.FieldTheory.GaloisGroups.Cubic
import TauCeti.FieldTheory.GaloisGroups.NormalClosure

/-!
# The symmetric group `S₃` as two different Galois groups

The LMFDB identifies the Galois group of a number field `K` of degree `n` by its degree and its
`T`-number: the group `Aut(K^gal/ℚ)` together with its action on the `n` embeddings of `K`, up to
conjugation in `S_n` (LMFDB `nf.galois_group`). It is the Galois group of a defining polynomial of
`K` acting on the roots of that polynomial (`Polynomial.Gal.galActionHom`). An abstract group can
arise in this way from fields of different degrees: "An abstract group may have more than one
representation as a Galois group. Correspondingly, the familiar symbol for a group may represent
several Galois groups." (LMFDB `nf.galois_group.name`). The smallest example is the symmetric group
`S₃`, as no abstract group occurs twice among the transitive groups of degree at most `5`:

* the pure cubic field `ℚ(∛2)` (LMFDB `3.1.108.1`), defined by `X³ - 2`, has Galois group `S₃`
  acting on the three complex roots of `X³ - 2`: the transitive group `3T2` (Tau Ceti's
  `TauCeti.hasGaloisLabel_X_pow_three_sub_two`);
* its Galois closure `L`, the splitting field of `X³ - 2`, is a sextic field, with Galois group `S₃`
  again, now acting on the six complex roots of the minimal polynomial of any primitive element of
  `L`, that is of any defining polynomial of `L`: the transitive group `6T2`.

The Galois group of `X³ - 2` has order `6` (Tau Ceti's `TauCeti.natCard_gal_X_pow_three_sub_two`)
and acts faithfully on the three complex roots, so it is the full symmetric group on them. The
Galois group of the minimal polynomial `g` of a primitive element `y` of `L` is the automorphism
group of the normal closure of `ℚ(y) = L` (Tau Ceti's `TauCeti.galEquivNormalClosure`), which is
the Galois group of `X³ - 2`. A primitive element exists (`Field.exists_primitive_element`), so the
abstract group `S₃` is the Galois group of an irreducible cubic and of an irreducible sextic
polynomial over `ℚ`, with faithful transitive actions on three and on six roots
(`Polynomial.Gal.galActionHom_injective`, `Polynomial.Gal.galAction_isPretransitive`).

## Main definitions

* `Polynomial.galXPowThreeSubTwoMulEquiv`: the Galois group of `X³ - 2` over `ℚ` is `S₃`.
* `Polynomial.galMinpolySplittingFieldXPowThreeSubTwoMulEquiv`: the Galois group of the minimal
  polynomial of a primitive element of the splitting field of `X³ - 2` is `S₃`.

## Main results

* `Polynomial.card_rootSet_X_pow_three_sub_two`: `X³ - 2` has three complex roots.
* `Polynomial.bijective_galActionHom_X_pow_three_sub_two` (LMFDB `nf.galois_group.name`): the
  Galois group of `X³ - 2` acts as the full symmetric group on its three complex roots.
* `Polynomial.finrank_splittingField_X_pow_three_sub_two`: the splitting field of `X³ - 2` is a
  sextic field.
* `Polynomial.card_rootSet_minpoly_splittingField_X_pow_three_sub_two` (LMFDB
  `nf.galois_group.name`): the Galois group of a defining polynomial of the splitting field of
  `X³ - 2` acts on six complex roots.
* `Polynomial.exists_card_rootSet_eq_six_and_nonempty_gal_mulEquiv` (LMFDB
  `nf.galois_group.name`): the group `S₃` is also the Galois group of an irreducible polynomial
  over `ℚ` with six complex roots.
-/

open IntermediateField

namespace Polynomial

attribute [local instance] Gal.splits_ℚ_ℂ

/-- **`X³ - 2` has three complex roots.** -/
lemma card_rootSet_X_pow_three_sub_two : Fintype.card ((X ^ 3 - 2 : ℚ[X]).rootSet ℂ) = 3 := by
  rw [card_rootSet_eq_natDegree TauCeti.irreducible_X_pow_three_sub_two.separable
    (IsAlgClosed.splits _)]
  compute_degree!

/-- **The Galois group of `X³ - 2` over `ℚ` is the full symmetric group on its three complex
roots**, the transitive group `3T2`: its action on the roots is bijective onto the permutations. -/
lemma bijective_galActionHom_X_pow_three_sub_two :
    Function.Bijective (Gal.galActionHom (X ^ 3 - 2 : ℚ[X]) ℂ) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨Gal.galActionHom_injective _ _, ?_⟩
  rw [Fintype.card_perm, card_rootSet_X_pow_three_sub_two, ← Nat.card_eq_fintype_card,
    TauCeti.natCard_gal_X_pow_three_sub_two]
  rfl

/-- The Galois group of `X³ - 2` over `ℚ`, the Galois group of the pure cubic field `ℚ(∛2)`, is the
symmetric group `S₃`. -/
noncomputable def galXPowThreeSubTwoMulEquiv : (X ^ 3 - 2 : ℚ[X]).Gal ≃* Equiv.Perm (Fin 3) :=
  (MulEquiv.ofBijective _ bijective_galActionHom_X_pow_three_sub_two).trans <|
    (Fintype.equivFinOfCardEq card_rootSet_X_pow_three_sub_two).permCongrHom

/-- **The splitting field of `X³ - 2`, the Galois closure of `ℚ(∛2)`, is a sextic field.** -/
lemma finrank_splittingField_X_pow_three_sub_two :
    Module.finrank ℚ (X ^ 3 - 2 : ℚ[X]).SplittingField = 6 := by
  rw [← Gal.card_of_separable TauCeti.irreducible_X_pow_three_sub_two.separable,
    TauCeti.natCard_gal_X_pow_three_sub_two]

variable {y : (X ^ 3 - 2 : ℚ[X]).SplittingField}

lemma natDegree_minpoly_splittingField_X_pow_three_sub_two (hy : ℚ⟮y⟯ = ⊤) :
    (minpoly ℚ y).natDegree = 6 :=
  ((Field.primitive_element_iff_minpoly_natDegree_eq ℚ y).mp hy).trans
    finrank_splittingField_X_pow_three_sub_two

/-- The Galois group of the minimal polynomial of a primitive element `y` of the splitting field
of `X³ - 2`, the Galois group of the sextic Galois closure of `ℚ(∛2)`, is the symmetric group
`S₃`. -/
noncomputable def galMinpolySplittingFieldXPowThreeSubTwoMulEquiv (hy : ℚ⟮y⟯ = ⊤) :
    (minpoly ℚ y).Gal ≃* Equiv.Perm (Fin 3) :=
  (TauCeti.galEquivNormalClosure y).trans <|
    ((equivOfEq <| top_unique <| hy.ge.trans <| le_normalClosure _).trans topEquiv).autCongr.trans
      galXPowThreeSubTwoMulEquiv

/-- **The Galois group of a defining polynomial of the splitting field of `X³ - 2` acts on six
complex roots**: as an abstract group it is `S₃`
(`Polynomial.galMinpolySplittingFieldXPowThreeSubTwoMulEquiv`), and as a permutation group it has
degree `6`, not `3`. It is the transitive group `6T2` of the LMFDB, a label that is not formalised
here: Tau Ceti's labels stop at degree `5`. -/
lemma card_rootSet_minpoly_splittingField_X_pow_three_sub_two (hy : ℚ⟮y⟯ = ⊤) :
    Fintype.card ((minpoly ℚ y).rootSet ℂ) = 6 := by
  rw [card_rootSet_eq_natDegree (minpoly.irreducible <| .of_finite ℚ y).separable
    (IsAlgClosed.splits _), natDegree_minpoly_splittingField_X_pow_three_sub_two hy]

/-- **An abstract group may have more than one representation as a Galois group** (LMFDB
`nf.galois_group.name`): the symmetric group `S₃`, the Galois group of the irreducible cubic
`X³ - 2` acting on its three complex roots, is also the Galois group of an irreducible polynomial
over `ℚ` acting on six complex roots, the minimal polynomial of a primitive element of the
splitting field of `X³ - 2`. -/
lemma exists_card_rootSet_eq_six_and_nonempty_gal_mulEquiv : ∃ g : ℚ[X], Irreducible g ∧
    Fintype.card (g.rootSet ℂ) = 6 ∧ Nonempty (g.Gal ≃* Equiv.Perm (Fin 3)) := by
  rcases Field.exists_primitive_element ℚ (X ^ 3 - 2 : ℚ[X]).SplittingField with ⟨y, hy⟩
  exact ⟨_, minpoly.irreducible <| .of_finite ℚ y,
    card_rootSet_minpoly_splittingField_X_pow_three_sub_two hy,
    ⟨galMinpolySplittingFieldXPowThreeSubTwoMulEquiv hy⟩⟩

end Polynomial
