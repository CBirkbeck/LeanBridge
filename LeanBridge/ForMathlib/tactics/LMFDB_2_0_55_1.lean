import Mathlib
import LeanBridge.ForMathlib.Irreduciblepolys.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanBridge.ForMathlib.Irreduciblepolys.BrillhartIrreducibilityTest

namespace LMFDB_2_0_55_1

noncomputable section

open NumberField Polynomial

abbrev min_poly_2_0_55_1 : Polynomial ℚ := (1) * Polynomial.X ^ 2 + (-1) * Polynomial.X + (14)

abbrev K_2_0_55_1 := AdjoinRoot min_poly_2_0_55_1



open Polynomial

local notation "T" => (X^2 - X + 14 : ℤ[X])

local notation "l" => [14, -1, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 14
 P := 59
 M := -28
 r := 7/2
 ρ := 15/2
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide +kernel
 hrho := by decide +kernel
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 



abbrev K_gen_2_0_55_1 : K_2_0_55_1 := AdjoinRoot.root min_poly_2_0_55_1

lemma irreducible_poly : Irreducible min_poly_2_0_55_1 := by
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

instance : Fact (Irreducible min_poly_2_0_55_1) := ⟨irreducible_poly⟩



axiom LMFDB_NF_2_0_55_1_discr : NumberField.discr K_2_0_55_1 = -55

axiom LMFDB_NF_2_0_55_1_isGalois : IsGalois ℚ K_2_0_55_1

axiom LMFDB_NF_2_0_55_1_classNumber : NumberField.classNumber K_2_0_55_1 = 4

axiom LMFDB_NF_2_0_55_1_totallyComplex : IsTotallyComplex K_2_0_55_1

instance LMFDB_NF_2_0_55_1_totallyComplexInstance : IsTotallyComplex K_2_0_55_1 := LMFDB_NF_2_0_55_1_totallyComplex

axiom LMFDB_NF_2_0_55_1_isCM : NumberField.IsCMField K_2_0_55_1

end
