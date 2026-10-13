/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF2_0_231_1.ClassGroupData2_0_231_1
import LeanBridge.IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import LeanBridge.IdealArithmetic.Saturation.PrincipalityCertificate
import LeanBridge.IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import LeanBridge.IdealArithmetic.Examples.NF2_0_231_1.RI2_0_231_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section 

namespace Sat3 
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}

def R13 : IsOrderOf (2 : ZMod 13) 12 where
 m := 2
 P := ![2, 3]
 e := ![2, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0], ![4, 1]] i)))

def A0: IdealEqSpanCertificate' Table ![![13, 0], ![4, 1]] 
 ![![13, 0], ![4, 1]] where
  M :=![![![13, 0], ![0, 13]], ![![4, 1], ![-58, 5]]]
  hmulB := by decide  
  f := ![![![-3, -1], ![13, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-4, 13]], ![![0, 1], ![-6, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 13 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def Log00Mem : IdealMemCertificate B I0
  ![![13, 0], ![4, 1]] ![-4, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, -1]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![3, -1]
 hxeq :=  rfl
 m:= 7
 C := ![-4, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k :=  11
 hpow := by zmod_pow
 heql := by decide

end Sat3
