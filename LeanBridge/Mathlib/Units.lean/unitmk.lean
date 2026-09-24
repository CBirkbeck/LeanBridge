import Mathlib
import LeanBridge.LMFDB.Tactic.LMFDB_search
import LeanBridge.LMFDB.NumberFields.LMFDB_Proof_2_2_8_1

noncomputable section

open NumberField



abbrev min_poly_2_2_8_1_int : Polynomial ℤ := (1) * Polynomial.X ^ 2 + (-2)

abbrev min_poly_2_2_8_1 : Polynomial ℚ := ((min_poly_2_2_8_1_int).mapRingHom (Int.castRingHom ℚ))

abbrev K_2_2_8_1 := AdjoinRoot min_poly_2_2_8_1

lemma irreducible_poly : Irreducible min_poly_2_2_8_1 := by
  have := irreducible_T
  rw [Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast] at this
  · convert this
    simp
    ring
  · refine Polynomial.Monic.isPrimitive ?_
    refine Polynomial.Monic.def.mpr ?_
    rw [T_ofList', ofList_leadingCoeff]
    · simp
    · apply List.cons_ne_nil _ _
    · rfl

instance: Fact (Irreducible min_poly_2_2_8_1) := ⟨irreducible_poly⟩

axiom LMFDB_NF_2_2_8_1_discr : NumberField.discr K_2_2_8_1 = 8

axiom LMFDB_NF_2_2_8_1_isGalois : IsGalois ℚ K_2_2_8_1

axiom LMFDB_NF_2_2_8_1_classNumber : NumberField.classNumber K_2_2_8_1 = 1


lemma unit_rank : NumberField.Units.rank K_2_2_8_1 = 1 := by
  simp_rw [Units.rank]

  sorry

abbrev K_gen : K_2_2_8_1 := AdjoinRoot.root min_poly_2_2_8_1

lemma K_int : IsIntegral ℤ K_gen := by
  use min_poly_2_2_8_1_int
  constructor
  · simp [min_poly_2_2_8_1_int]
    monicity
    simp
  · simpa [K_gen, min_poly_2_2_8_1] using AdjoinRoot.eval₂_root min_poly_2_2_8_1


def K_gen_int : 𝓞 K_2_2_8_1 := ⟨K_gen, K_int⟩

lemma K_gen_int_pol : K_gen_int ^ 2 - 2 = 0 := by
  simp [K_gen_int, min_poly_2_2_8_1]
  suffices  K_gen ^ 2 - 2 = 0 by
    exact RingOfIntegers.coe_eq_zero_iff.mp this
  simpa [K_gen, min_poly_2_2_8_1] using AdjoinRoot.eval₂_root min_poly_2_2_8_1

def fundamental_unit_one : (𝓞 K_2_2_8_1)ˣ  where
  val := K_gen_int + 1
  inv := K_gen_int - 1
  val_inv := by
    have := K_gen_int_pol
    grind
  inv_val := by
    have := K_gen_int_pol
    grind

end
