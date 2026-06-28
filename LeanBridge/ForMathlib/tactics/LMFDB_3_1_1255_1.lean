import Mathlib
import LeanBridge.ForMathlib.Irreduciblepolys.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanBridge.ForMathlib.Irreduciblepolys.BrillhartIrreducibilityTest

namespace LMFDB_3_1_1255_1

noncomputable section

open NumberField Polynomial

abbrev min_poly_3_1_1255_1 : Polynomial ℚ := (1) * Polynomial.X ^ 3 + (-1) * Polynomial.X ^ 2 + (4) * Polynomial.X + (5)

abbrev K_3_1_1255_1 := AdjoinRoot min_poly_3_1_1255_1



open Polynomial

local notation "T" => (X^3 - X^2 + 4*X + 5 : ℤ[X])

local notation "l" => [5, 4, -1, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 5
 P := 227
 M := -10
 r := 2
 ρ := 4
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide +kernel
 hrho := by decide +kernel
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 

-- Fundamental Units



abbrev K_gen_3_1_1255_1 : K_3_1_1255_1 := AdjoinRoot.root min_poly_3_1_1255_1

lemma irreducible_poly : Irreducible min_poly_3_1_1255_1 := by
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

instance : Fact (Irreducible min_poly_3_1_1255_1) := ⟨irreducible_poly⟩

lemma K_int_3_1_1255_1 : IsIntegral ℤ K_gen_3_1_1255_1 := by
  sorry

def K_gen_int_3_1_1255_1 : 𝓞 K_3_1_1255_1 := ⟨K_gen_3_1_1255_1, K_int_3_1_1255_1⟩

def fundamental_unit_3_1_1255_1_1 : (𝓞 K_3_1_1255_1)ˣ where
  val := -K_gen_int_3_1_1255_1 - 1
  inv := -K_gen_int_3_1_1255_1^2 + 2 * K_gen_int_3_1_1255_1 - 6
  val_inv := by sorry
  inv_val := by sorry



axiom LMFDB_NF_3_1_1255_1_discr : NumberField.discr K_3_1_1255_1 = -1255

axiom LMFDB_NF_3_1_1255_1_isGalois : ¬ IsGalois ℚ K_3_1_1255_1

axiom LMFDB_NF_3_1_1255_1_classNumber : NumberField.classNumber K_3_1_1255_1 = 2


end
