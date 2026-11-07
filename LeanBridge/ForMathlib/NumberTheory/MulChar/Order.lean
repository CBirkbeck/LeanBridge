import TauCeti.NumberTheory.MulChar.GaloisOrbit

/-!
# The order of a multiplicative character

The order of a multiplicative character `χ`, such as a Dirichlet character, is its order `orderOf χ`
in the group of characters: the least positive integer `n` such that `χ ^ n` is the trivial
character. When the monoid has finitely many units and the values lie in a domain, such as `ℂ`, it
is also the order of the image of `χ` on units, and this image is the group of `n`-th roots of
unity: every value on a unit is an `n`-th root of unity, and one of them is primitive (Tau Ceti's
`MulChar.exists_isPrimitiveRoot_apply`), so that it generates them all.

## Main results

* `MulChar.isLeast_orderOf` (LMFDB `character.dirichlet.order`): the order of `χ` is the least
  positive integer `n` such that `χ ^ n` is the trivial character.
* `MulChar.range_toUnitHom_eq_rootsOfUnity` (LMFDB `character.dirichlet.order`): the image of `χ` on
  units is the group of `n`-th roots of unity, `n` being the order of `χ`.
* `MulChar.card_range_toUnitHom` (LMFDB `character.dirichlet.order`): the image of `χ` on units has
  order `n`.
* `MulChar.isCyclic_range_toUnitHom`: the image of `χ` on units is cyclic.
-/

namespace MulChar

variable {M R : Type*} [CommMonoid M] [CommRing R] (χ : MulChar M R)

lemma toUnitHom_pow_orderOf (u : Mˣ) : χ.toUnitHom u ^ orderOf χ = 1 :=
  Units.ext <| by
    rw [Units.val_pow_eq_pow_val, coe_toUnitHom, ← pow_apply_coe, pow_orderOf_eq_one,
      one_apply_coe, Units.val_one]

variable [Finite Mˣ]

/-- **The order of a character is the least positive integer `n` such that `χ ^ n` is the trivial
character.** -/
lemma isLeast_orderOf : IsLeast {n | 0 < n ∧ χ ^ n = 1} (orderOf χ) :=
  ⟨⟨χ.orderOf_pos, pow_orderOf_eq_one χ⟩, fun _ hn ↦ orderOf_le_of_pow_eq_one hn.1 hn.2⟩

variable [IsDomain R]

/-- **The image of a character on units is the group of `n`-th roots of unity**, `n` being the
order of the character. -/
lemma range_toUnitHom_eq_rootsOfUnity : χ.toUnitHom.range = rootsOfUnity (orderOf χ) R := by
  have : NeZero (orderOf χ) := ⟨χ.orderOf_pos.ne'⟩
  rcases χ.exists_isPrimitiveRoot_apply with ⟨u, hu⟩
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, rfl⟩
    exact (mem_rootsOfUnity _ _).mpr <| χ.toUnitHom_pow_orderOf v
  · rw [← (IsPrimitiveRoot.coe_units_iff.mp <| χ.coe_toUnitHom u ▸ hu).zpowers_eq]
    exact Subgroup.zpowers_le_of_mem ⟨u, rfl⟩

/-- **The image of a character on units has the order of the character.** -/
lemma card_range_toUnitHom : Nat.card χ.toUnitHom.range = orderOf χ := by
  have : NeZero (orderOf χ) := ⟨χ.orderOf_pos.ne'⟩
  rcases χ.exists_isPrimitiveRoot_apply with ⟨u, hu⟩
  rw [χ.range_toUnitHom_eq_rootsOfUnity, hu.card_rootsOfUnity]

/-- **The image of a character on units is cyclic.** -/
lemma isCyclic_range_toUnitHom : IsCyclic χ.toUnitHom.range := by
  have : NeZero (orderOf χ) := ⟨χ.orderOf_pos.ne'⟩
  rw [χ.range_toUnitHom_eq_rootsOfUnity]
  infer_instance

end MulChar
