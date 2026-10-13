/-
Copyright (c) 2025 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.ForMathlib.FieldTheory.Finite.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanBridge.ForMathlib.RingTheory.Polynomial.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^4 - 2*X^3 + 7*X^2 - 6*X + 78 : ℤ[X])

local notation "l" => [78, -6, 7, -2, 1]

unseal Rat.add Rat.mul Rat.inv

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 6
 P := 3049
 M := 12
 r := 7/2
 ρ := 11/2
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide
 hrho := by decide
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 
