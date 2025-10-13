import LeanBridge.Mathlib.Irreduciblepolys.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanBridge.Mathlib.Irreduciblepolys.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^2 - X + 6 : ℤ[X])

local notation "l" => [6, -1, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 6
 P := 23
 M := -11
 r := 9/4
 ρ := 59/12
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide +kernel
 hrho := by decide +kernel
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 
