/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF3_1_24843_1.ClassGroupData3_1_24843_1
import LeanBridge.IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import LeanBridge.IdealArithmetic.Saturation.PrincipalityCertificate
import LeanBridge.IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import LeanBridge.IdealArithmetic.Examples.NF3_1_24843_1.RI3_1_24843_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section 

namespace Sat3 
instance hq31 : Fact $ Nat.Prime 31 := {out := by norm_num}
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R31 : IsOrderOf (3 : ZMod 31) 30 where
 m := 3
 P := ![2, 3, 5]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R13 : IsOrderOf (2 : ZMod 13) 12 where
 m := 2
 P := ![2, 3]
 e := ![2, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R7 : IsOrderOf (3 : ZMod 7) 6 where
 m := 2
 P := ![2, 3]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![0, 1, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![4, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![-1, -1, 3], ![30, 0, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 3], ![0, -7, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![-2, -2, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![-2, 0, 7]], ![![0, 1, 0], ![-1, -1, 3], ![4, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![0, 1, 0]] 
 ![![13, 0, 0], ![0, 1, 0], ![4, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![0, 1, 0], ![-1, -1, 3], ![30, 0, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 3], ![0, -13, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![-4, -4, 0]]]
  g := ![![![1, 0, 0], ![0, 13, 0], ![-4, 0, 13]], ![![0, 1, 0], ![-1, -1, 3], ![2, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 13 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![31, 0, 0], ![4, 1, 0]] 
 ![![31, 0, 0], ![4, 1, 0], ![6, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![4, 1, 0], ![-1, 3, 3], ![30, 0, 5]]]
  hmulB := by decide  
  f := ![![![-135, 408, 408], ![0, -4216, 0]], ![![-17, 51, 51], ![1, -527, 0]], ![![-30, 78, 79], ![30, -816, 0]]]
  g := ![![![1, 0, 0], ![-4, 31, 0], ![-6, 0, 31]], ![![0, 1, 0], ![-1, 3, 3], ![0, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 31 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
  ![![7, 0, 0], ![0, 1, 0], ![2, 0, 1]] ![-14, 2, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-2, 2, 0]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-9, 2, 0]
 hxeq :=  rfl
 m:= 5
 C := ![-14, 2, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k :=  5
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
  ![![7, 0, 0], ![0, 1, 0], ![2, 0, 1]] ![2, 1, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, 1, 1]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![6, 1, 1]
 hxeq :=  rfl
 m:= 4
 C := ![2, 1, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k :=  4
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
  ![![7, 0, 0], ![0, 1, 0], ![2, 0, 1]] ![2, 1, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, 1, 1]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![5, 1, 1]
 hxeq :=  rfl
 m:= 3
 C := ![2, 1, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k :=  1
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
  ![![13, 0, 0], ![0, 1, 0], ![4, 0, 1]] ![-13, 2, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 2, 0]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-9, 2, 0]
 hxeq :=  rfl
 m:= 4
 C := ![-13, 2, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k :=  2
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
  ![![13, 0, 0], ![0, 1, 0], ![4, 0, 1]] ![4, 1, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, 1, 1]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![6, 1, 1]
 hxeq :=  rfl
 m:= 2
 C := ![4, 1, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k :=  1
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
  ![![13, 0, 0], ![0, 1, 0], ![4, 0, 1]] ![4, 1, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, 1, 1]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![5, 1, 1]
 hxeq :=  rfl
 m:= 1
 C := ![4, 1, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k :=  0
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
  ![![31, 0, 0], ![4, 1, 0], ![6, 0, 1]] ![-23, 2, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 2, 0]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-9, 2, 0]
 hxeq :=  rfl
 m:= 14
 C := ![-23, 2, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k :=  22
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
  ![![31, 0, 0], ![4, 1, 0], ![6, 0, 1]] ![-21, 1, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 1, 1]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![6, 1, 1]
 hxeq :=  rfl
 m:= 27
 C := ![-21, 1, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k :=  3
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
  ![![31, 0, 0], ![4, 1, 0], ![6, 0, 1]] ![-21, 1, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 1, 1]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![5, 1, 1]
 hxeq :=  rfl
 m:= 26
 C := ![-21, 1, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k :=  5
 hpow := by zmod_pow
 heql := by decide

end Sat3
