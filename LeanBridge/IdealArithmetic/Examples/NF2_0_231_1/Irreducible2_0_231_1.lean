/-
Copyright (c) 2025 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.ForMathlib.FieldTheory.Finite.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanBridge.ForMathlib.RingTheory.Polynomial.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^2 - X + 58 : ℤ[X])

local notation "l" => [58, -1, 1]

unseal Rat.add Rat.mul Rat.inv

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 10
 P := 139
 M := -36
 r := 15/2
 ρ := 457/30
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide
 hrho := by decide
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 
