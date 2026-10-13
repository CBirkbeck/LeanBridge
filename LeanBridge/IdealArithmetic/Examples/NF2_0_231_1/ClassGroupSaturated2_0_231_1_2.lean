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

namespace Sat2 
instance hq11 : Fact $ Nat.Prime 11 := {out := by norm_num}
instance hq3 : Fact $ Nat.Prime 3 := {out := by norm_num}
instance hq5 : Fact $ Nat.Prime 5 := {out := by norm_num}

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R3 : IsOrderOf (2 : ZMod 3) 2 where
 m := 1
 P := ![2]
 e := ![1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R5 : IsOrderOf (2 : ZMod 5) 4 where
 m := 1
 P := ![2]
 e := ![2]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0], ![1, 1]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0], ![1, 1]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0], ![5, 1]] i)))

def A0: IdealEqSpanCertificate' Table ![![3, 0], ![1, 1]] 
 ![![3, 0], ![1, 1]] where
  M :=![![![3, 0], ![0, 3]], ![![1, 1], ![-58, 2]]]
  hmulB := by decide  
  f := ![![![0, -1], ![3, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-1, 3]], ![![0, 1], ![-20, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 3 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![5, 0], ![1, 1]] 
 ![![5, 0], ![1, 1]] where
  M :=![![![5, 0], ![0, 5]], ![![1, 1], ![-58, 2]]]
  hmulB := by decide  
  f := ![![![0, -1], ![5, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-1, 5]], ![![0, 1], ![-12, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 5 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![11, 0], ![5, 1]] 
 ![![11, 0], ![5, 1]] where
  M :=![![![11, 0], ![0, 11]], ![![5, 1], ![-58, 6]]]
  hmulB := by decide  
  f := ![![![-4, -1], ![11, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-5, 11]], ![![0, 1], ![-8, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 11 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
  ![![3, 0], ![1, 1]] ![-3, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0]
 hxeq :=  rfl
 m:= 2
 C := ![-3, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k :=  1
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
  ![![3, 0], ![1, 1]] ![2, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![1, -1]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![3, -1]
 hxeq :=  rfl
 m:= 1
 C := ![2, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k :=  0
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
  ![![3, 0], ![1, 1]] ![6, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![2, 0]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 0 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![7, 0]
 hxeq :=  rfl
 m:= 1
 C := ![6, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k :=  0
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
  ![![5, 0], ![1, 1]] ![-5, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0]
 hxeq :=  rfl
 m:= 4
 C := ![-5, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k :=  2
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
  ![![5, 0], ![1, 1]] ![-1, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, -1]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![3, -1]
 hxeq :=  rfl
 m:= 4
 C := ![-1, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k :=  2
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
  ![![5, 0], ![1, 1]] ![5, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![1, 0]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 1 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![7, 0]
 hxeq :=  rfl
 m:= 2
 C := ![5, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k :=  1
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
  ![![11, 0], ![5, 1]] ![-11, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 0]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0]
 hxeq :=  rfl
 m:= 10
 C := ![-11, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k :=  5
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
  ![![11, 0], ![5, 1]] ![-5, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![0, -1]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![3, -1]
 hxeq :=  rfl
 m:= 8
 C := ![-5, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k :=  3
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
  ![![11, 0], ![5, 1]] ![0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![0, 0]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 1 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![7, 0]
 hxeq :=  rfl
 m:= 7
 C := ![0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k :=  7
 hpow := by zmod_pow
 heql := by decide

end Sat2
