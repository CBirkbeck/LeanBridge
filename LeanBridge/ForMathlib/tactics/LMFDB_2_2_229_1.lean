import Mathlib
import LeanBridge.ForMathlib.Irreduciblepolys.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanBridge.ForMathlib.Irreduciblepolys.BrillhartIrreducibilityTest

namespace LMFDB_2_2_229_1

noncomputable section

open NumberField Polynomial

abbrev min_poly_2_2_229_1 : Polynomial ℚ := (1) * Polynomial.X ^ 2 + (-1) * Polynomial.X + (-57)

abbrev K_2_2_229_1 := AdjoinRoot min_poly_2_2_229_1



open Polynomial

local notation "T" => (X^2 - X - 57 : ℤ[X])

local notation "l" => [-57, -1, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 15
 P := 71
 M := -33
 r := 15/2
 ρ := 151/10
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide +kernel
 hrho := by decide +kernel
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 


lemma irreducible_poly : Irreducible min_poly_2_2_229_1 := by
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

instance : Fact (Irreducible min_poly_2_2_229_1) := ⟨irreducible_poly⟩



axiom LMFDB_NF_2_2_229_1_discr : NumberField.discr K_2_2_229_1 = 229

axiom LMFDB_NF_2_2_229_1_isGalois : IsGalois ℚ K_2_2_229_1

axiom LMFDB_NF_2_2_229_1_classNumber : NumberField.classNumber K_2_2_229_1 = 3


end
