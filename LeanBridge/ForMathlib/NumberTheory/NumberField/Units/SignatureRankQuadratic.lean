import LeanBridge.ForMathlib.NumberTheory.NumberField.Units.SignatureRank
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import TauCeti.NumberTheory.NumberField.Quadratic.Basic
import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Signature
import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace
import TauCeti.NumberTheory.NumberField.Units.Torsion

/-!
# The unit signature rank of a real quadratic field

The unit signature rank of a number field `K` (LMFDB `nf.unit_signature_rank`) is the dimension over
`𝔽₂` of the space of sign patterns of the units of `𝓞 K` at the real places. For a real quadratic
field `K`, with fundamental unit `ε`, the LMFDB states that it is `1` if `ε` has norm `1` and `2` if
`ε` has norm `-1`. Here a fundamental unit is any unit generating the units modulo torsion,
`Subgroup.closure {ε} ⊔ torsion K = ⊤`; its norm does not depend on the choice, and Mathlib's
`NumberField.Units.fundSystem` provides one.

The rank is `2 = r₁` exactly when the units realise every sign pattern, which by Tau Ceti's
`TauCeti.NumberField.unitSignature_surjective_iff_exists_norm_eq_neg_one` happens exactly when some
unit has norm `-1`. The units are `±εⁿ`, of norm `N(ε)ⁿ`, so this happens exactly when `N(ε) = -1`.

## Main results

* `NumberField.unitSignatureRank_eq_nrRealPlaces_iff`: the unit signature rank is the number of
  real places exactly when the units realise every sign pattern.
* `NumberField.Units.closure_fundSystem_sup_torsion_eq_top_of_finrank_eq_two`: in a real quadratic
  field, the unit of Mathlib's fundamental system is a fundamental unit.
* `NumberField.unitSignatureRank_eq_two_iff` (LMFDB `nf.unit_signature_rank`): for a real quadratic
  field, the unit signature rank is `2` exactly when the fundamental unit has norm `-1`.
* `NumberField.unitSignatureRank_eq_one_iff` (LMFDB `nf.unit_signature_rank`): for a real quadratic
  field, the unit signature rank is `1` exactly when the fundamental unit has norm `1`.
* `NumberField.unitSignatureRank_eq_ite` (LMFDB `nf.unit_signature_rank`): for a real quadratic
  field, the unit signature rank is `1` if the fundamental unit has norm `1` and `2` otherwise.
-/

open Module Polynomial TauCeti GlobalNumberFields NumberField InfinitePlace Units

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ε : (𝓞 K)ˣ}

/-- The unit signature rank is the number `r₁` of real places exactly when the units of `𝓞 K`
realise all `2 ^ r₁` sign patterns at the real places. -/
lemma unitSignatureRank_eq_nrRealPlaces_iff :
    unitSignatureRank K = nrRealPlaces K ↔ Function.Surjective (unitSignature (K := K)) := by
  rw [← (Nat.pow_right_injective le_rfl).eq_iff, two_pow_unitSignatureRank, nrRealPlaces,
    Fintype.card_eq_nat_card, ← Units.index_posSubgroup ℝ, Subgroup.index, ← Nat.card_fun,
    Subgroup.card_eq_iff_eq_top]
  exact MonoidHom.range_eq_top

variable [IsTotallyReal K]

lemma nrRealPlaces_eq_two_of_finrank_eq_two (hK : finrank ℚ K = 2) : nrRealPlaces K = 2 :=
  IsTotallyReal.finrank (K := K) ▸ hK

lemma Units.rank_eq_one_of_finrank_eq_two (hK : finrank ℚ K = 2) : rank K = 1 := by
  rw [rank, card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_eq_two_of_finrank_eq_two hK,
    IsTotallyReal.nrComplexPlaces_eq_zero]

/-- In a real quadratic field, Mathlib's fundamental system of units is a single fundamental unit,
which generates the units modulo torsion. -/
lemma Units.closure_fundSystem_sup_torsion_eq_top_of_finrank_eq_two (hK : finrank ℚ K = 2)
    (i : Fin (rank K)) : Subgroup.closure {fundSystem K i} ⊔ torsion K = ⊤ := by
  have : Subsingleton (Fin (rank K)) :=
    Fin.subsingleton_iff_le_one.mpr (rank_eq_one_of_finrank_eq_two hK).le
  have : Nonempty (Fin (rank K)) := ⟨i⟩
  rw [← closure_fundSystem_sup_torsion_eq_top K,
    Set.range_eq_singleton fun j ↦ congrArg (fundSystem K) (Subsingleton.elim j i)]

lemma norm_torsion_eq_one_of_finrank_eq_two (hK : finrank ℚ K = 2) (ζ : torsion K) :
    Algebra.norm ℚ ((ζ : (𝓞 K)ˣ) : K) = 1 := by
  rcases torsion_eq_one_or_neg_one_of_isReal
    (IsTotallyReal.isReal (Classical.arbitrary (InfinitePlace K))) ζ with h | h <;> rw [h]
  · rw [coe_one, map_one]
  · rw [coe_neg_one, ← map_one (algebraMap ℚ K), ← map_neg, Algebra.norm_algebraMap, hK]
    norm_num

lemma exists_norm_eq_neg_one_iff_of_finrank_eq_two (hK : finrank ℚ K = 2)
    (hε : Subgroup.closure {ε} ⊔ torsion K = ⊤) :
    (∃ u : (𝓞 K)ˣ, Algebra.norm ℚ (u : K) = -1) ↔ Algebra.norm ℚ (ε : K) = -1 := by
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun h ↦ ⟨ε, h⟩⟩
  rcases Subgroup.mem_sup.mp (hε ▸ Subgroup.mem_top u) with ⟨y, hy, z, hz, rfl⟩
  rcases Subgroup.mem_closure_singleton.mp hy with ⟨n, rfl⟩
  rw [coe_mul, map_mul, coe_zpow, Algebra.norm_zpow,
    norm_torsion_eq_one_of_finrank_eq_two hK ⟨z, hz⟩, mul_one] at hu
  rcases (abs_eq zero_le_one).mp (Units.norm K ε) with h | h
  · rw [h, one_zpow] at hu
    norm_num at hu
  · exact h

/-- **The unit signature rank of a real quadratic field is `2` exactly when its fundamental unit
has norm `-1`** (LMFDB `nf.unit_signature_rank`), for any unit `ε` generating the units modulo
torsion. -/
lemma unitSignatureRank_eq_two_iff (hK : finrank ℚ K = 2)
    (hε : Subgroup.closure {ε} ⊔ torsion K = ⊤) :
    unitSignatureRank K = 2 ↔ Algebra.norm ℚ (ε : K) = -1 := by
  rcases exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top hK with ⟨θ, d, hmin, hgen, hd⟩
  have hd0 : 0 < d := by
    rcases lt_trichotomy d 0 with h | rfl | h
    · have : IsTotallyComplex K := isTotallyComplex_of_minpoly_eq_X_sq_sub_C_of_neg hmin h
      have h2 : nrRealPlaces K = 2 := nrRealPlaces_eq_two_of_finrank_eq_two hK
      rw [IsTotallyComplex.nrRealPlaces_eq_zero] at h2
      exact absurd h2 (by norm_num)
    · exact absurd hd not_squarefree_zero
    · exact h
  rw [← nrRealPlaces_eq_two_of_finrank_eq_two hK, unitSignatureRank_eq_nrRealPlaces_iff,
    unitSignature_surjective_iff_exists_norm_eq_neg_one hmin hgen hd0,
    exists_norm_eq_neg_one_iff_of_finrank_eq_two hK hε]

/-- **The unit signature rank of a real quadratic field is `1` exactly when its fundamental unit
has norm `1`** (LMFDB `nf.unit_signature_rank`), for any unit `ε` generating the units modulo
torsion. -/
lemma unitSignatureRank_eq_one_iff (hK : finrank ℚ K = 2)
    (hε : Subgroup.closure {ε} ⊔ torsion K = ⊤) :
    unitSignatureRank K = 1 ↔ Algebra.norm ℚ (ε : K) = 1 := by
  have hr : nrRealPlaces K = 2 := nrRealPlaces_eq_two_of_finrank_eq_two hK
  have hpos : 0 < unitSignatureRank K := unitSignatureRank_pos K (by rw [hr]; norm_num)
  have hle : unitSignatureRank K ≤ 2 := hr ▸ unitSignatureRank_le K
  rcases (abs_eq zero_le_one).mp (Units.norm K ε) with h | h
  · have h2 : unitSignatureRank K ≠ 2 := fun h2 ↦ by
      have h' : Algebra.norm ℚ (ε : K) = -1 := (unitSignatureRank_eq_two_iff hK hε).mp h2
      rw [h] at h'
      norm_num at h'
    exact iff_of_true (by omega) h
  · have h2 : unitSignatureRank K = 2 := (unitSignatureRank_eq_two_iff hK hε).mpr h
    exact iff_of_false (by omega) (by rw [h]; norm_num)

/-- **The unit signature rank of a real quadratic field** (LMFDB `nf.unit_signature_rank`): it is
`1` if the fundamental unit `ε` has norm `1`, and otherwise, when `ε` has norm `-1`, it is `2`. -/
lemma unitSignatureRank_eq_ite (hK : finrank ℚ K = 2) (hε : Subgroup.closure {ε} ⊔ torsion K = ⊤) :
    unitSignatureRank K = if Algebra.norm ℚ (ε : K) = 1 then 1 else 2 := by
  split_ifs with h
  · exact (unitSignatureRank_eq_one_iff hK hε).mpr h
  · exact (unitSignatureRank_eq_two_iff hK hε).mpr <|
      ((abs_eq zero_le_one).mp (Units.norm K ε)).resolve_left h

end NumberField
