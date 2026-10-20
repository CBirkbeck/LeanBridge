import TauCeti.NumberTheory.NumberField.Global.RayClass.Narrow.Kernel

/-!
# The unit signature rank of a number field

The signature of a unit `u` of `𝓞 K` records the sign of `σ u` at every real embedding `σ` of `K`.
Tau Ceti's `NumberField.unitSignature` takes values in the sign group `ℝˣ ⧸ ℝˣ₊` at each real
place, a group of order `2` which the LMFDB writes additively as `𝔽₂`, and
`TauCeti.GlobalNumberFields.integerUnitSignatures` is the subgroup of signatures of units. This
file defines the dimension of that subgroup over `𝔽₂`.

## Main definitions

* `NumberField.unitSignatureRank` (LMFDB `nf.unit_signature_rank`).

## Main results

* `NumberField.two_pow_unitSignatureRank`: there are `2 ^ unitSignatureRank K` signatures of
  units.
* `NumberField.unitSignatureRank_le`: the unit signature rank is at most the number `r₁` of real
  places.
* `NumberField.unitSignatureRank_pos`: it is positive when `K` has a real place.
* `NumberField.unitSignatureRank_eq_zero_iff`: it is `0` exactly for totally complex `K`.
-/

open TauCeti.GlobalNumberFields NumberField.InfinitePlace

namespace NumberField

variable (K : Type*) [Field K]

private lemma sq_eq_one (a : ℝˣ ⧸ Units.posSubgroup ℝ) : a ^ 2 = 1 := by
  induction a using QuotientGroup.induction_on with | H u => ?_
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Units.mem_posSubgroup,
    Units.val_pow_eq_pow_val]
  exact sq_pos_of_ne_zero u.ne_zero

@[nolint defsWithUnderscore]
noncomputable instance : Module (ZMod 2) (Additive (integerUnitSignatures (K := K))) :=
  AddCommGroup.zmodModule fun x : Additive (integerUnitSignatures (K := K)) ↦ by
    rw [← ofMul_toMul x, ← ofMul_pow, ofMul_eq_zero]
    exact Subtype.ext <| funext fun _ ↦ sq_eq_one _

/-- The **unit signature rank** of a number field `K` (LMFDB `nf.unit_signature_rank`): the
dimension over `𝔽₂` of the space of signatures of the units of `𝓞 K`, where the signature of a
unit is its vector of signs at the real places of `K`, each sign read in `ℝˣ ⧸ ℝˣ₊ ≅ 𝔽₂`.

A totally complex field has no real places, so its unit signature rank is `0`, as in the LMFDB's
convention (`unitSignatureRank_eq_zero_iff`). -/
noncomputable def unitSignatureRank : ℕ :=
  Module.finrank (ZMod 2) (Additive (integerUnitSignatures (K := K)))

variable [NumberField K]

/-- The units of `𝓞 K` realise `2 ^ unitSignatureRank K` sign patterns at the real places. -/
lemma two_pow_unitSignatureRank :
    2 ^ unitSignatureRank K = Nat.card (integerUnitSignatures (K := K)) := by
  nth_rw 1 [← Nat.card_zmod 2]
  exact Module.natCard_eq_pow_finrank.symm

/-- The unit signature rank is at most the number of real places. -/
lemma unitSignatureRank_le : unitSignatureRank K ≤ nrRealPlaces K := by
  rw [← Nat.pow_le_pow_iff_right one_lt_two, two_pow_unitSignatureRank, nrRealPlaces,
    Fintype.card_eq_nat_card, ← Units.index_posSubgroup ℝ, Subgroup.index, ← Nat.card_fun]
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

/-- The unit signature rank of a number field with a real place is positive, since the unit `-1`
is negative at every real place. -/
lemma unitSignatureRank_pos (h : 0 < nrRealPlaces K) : 0 < unitSignatureRank K := by
  rw [Nat.pos_iff_ne_zero, ← Nat.one_lt_two_pow_iff, two_pow_unitSignatureRank,
    Subgroup.one_lt_card_iff_ne_bot, Subgroup.ne_bot_iff_exists_ne_one]
  rw [nrRealPlaces, Fintype.card_eq_nat_card, Nat.card_pos_iff] at h
  rcases h.1 with ⟨w, hw⟩
  refine ⟨⟨unitSignature (-1), mem_integerUnitSignatures_iff.mpr ⟨-1, rfl⟩⟩, fun h1 ↦ ?_⟩
  exact absurd (unitSignature_eq_one_iff.mp (congrArg Subtype.val h1) w hw) (by norm_num)

/-- The unit signature rank vanishes exactly for totally complex fields. -/
lemma unitSignatureRank_eq_zero_iff : unitSignatureRank K = 0 ↔ IsTotallyComplex K := by
  rw [← nrRealPlaces_eq_zero_iff]
  exact ⟨fun h ↦ Nat.eq_zero_of_not_pos fun hr ↦ (unitSignatureRank_pos K hr).ne' h,
    fun h ↦ Nat.eq_zero_of_le_zero (h ▸ unitSignatureRank_le K)⟩

end NumberField
