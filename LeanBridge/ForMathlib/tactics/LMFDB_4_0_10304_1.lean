import Mathlib
import LeanBridge.ForMathlib.Irreduciblepolys.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanBridge.ForMathlib.Irreduciblepolys.BrillhartIrreducibilityTest

namespace LMFDB_4_0_10304_1

noncomputable section

open NumberField Polynomial

abbrev min_poly_4_0_10304_1 : Polynomial ℚ := (1) * Polynomial.X ^ 4 + (-2) * Polynomial.X ^ 3 + (7) * Polynomial.X ^ 2 + (-4) * Polynomial.X + (14)

abbrev K_4_0_10304_1 := AdjoinRoot min_poly_4_0_10304_1



open Polynomial

local notation "T" => (X^4 - 2*X^3 + 7*X^2 - 4*X + 14 : ℤ[X])

local notation "l" => [14, -4, 7, -2, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 2
 P := 4337
 M := 10
 r := 5/2
 ρ := 53/10
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide +kernel
 hrho := by decide +kernel
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 

-- Fundamental Units



abbrev K_gen_4_0_10304_1 : K_4_0_10304_1 := AdjoinRoot.root min_poly_4_0_10304_1

lemma irreducible_poly : Irreducible min_poly_4_0_10304_1 := by
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

instance : Fact (Irreducible min_poly_4_0_10304_1) := ⟨irreducible_poly⟩

lemma K_int_4_0_10304_1 : IsIntegral ℤ K_gen_4_0_10304_1 := by
  sorry

def K_gen_int_4_0_10304_1 : 𝓞 K_4_0_10304_1 := ⟨K_gen_4_0_10304_1, K_int_4_0_10304_1⟩

def fundamental_unit_4_0_10304_1_1 : (𝓞 K_4_0_10304_1)ˣ where
  val := ((1) / (4)) * K_gen_int_4_0_10304_1^3 - ((1) / (4)) * K_gen_int_4_0_10304_1^2 + ((1) / (2)) * K_gen_int_4_0_10304_1 + ((3) / (2))
  inv := ((1) / (4)) * K_gen_int_4_0_10304_1^3 - ((1) / (4)) * K_gen_int_4_0_10304_1^2 + ((1) / (2)) * K_gen_int_4_0_10304_1 - ((1) / (2))
  val_inv := by sorry
  inv_val := by sorry



axiom LMFDB_NF_4_0_10304_1_discr : NumberField.discr K_4_0_10304_1 = 10304

axiom LMFDB_NF_4_0_10304_1_isGalois : ¬ IsGalois ℚ K_4_0_10304_1

axiom LMFDB_NF_4_0_10304_1_classNumber : NumberField.classNumber K_4_0_10304_1 = 4

axiom LMFDB_NF_4_0_10304_1_totallyComplex : IsTotallyComplex K_4_0_10304_1

instance LMFDB_NF_4_0_10304_1_totallyComplexInstance : IsTotallyComplex K_4_0_10304_1 := LMFDB_NF_4_0_10304_1_totallyComplex

axiom LMFDB_NF_4_0_10304_1_isCM : NumberField.IsCMField K_4_0_10304_1

end
