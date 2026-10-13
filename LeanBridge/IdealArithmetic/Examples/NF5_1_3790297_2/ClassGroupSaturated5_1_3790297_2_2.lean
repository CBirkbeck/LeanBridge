/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.ClassGroupData5_1_3790297_2
import LeanBridge.IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import LeanBridge.IdealArithmetic.Saturation.PrincipalityCertificate
import LeanBridge.IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.RI5_1_3790297_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section 

namespace Sat2 
instance hq17 : Fact $ Nat.Prime 17 := {out := by norm_num}
instance hq11 : Fact $ Nat.Prime 11 := {out := by norm_num}
instance hq37 : Fact $ Nat.Prime 37 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R17 : IsOrderOf (3 : ZMod 17) 16 where
 m := 1
 P := ![2]
 e := ![4]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R37 : IsOrderOf (2 : ZMod 37) 36 where
 m := 2
 P := ![2, 3]
 e := ![2, 2]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))
def I4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 0, -1, 1, 0], ![-4, -5, -6, -3, 16], ![-1, -2, -1, 0, 2]]]
  hmulB := by decide  
  f := ![![![162, -265, 288, 32, -192], ![791, -1484, 28, 84, 0]], ![![162, -264, 287, 32, -192], ![792, -1477, 28, 84, 0]], ![![162, -264, 287, 32, -192], ![792, -1476, 28, 84, 0]], ![![135, -221, 241, 26, -160], ![659, -1238, 29, 70, 0]], ![![117, -190, 206, 22, -137], ![574, -1056, 26, 60, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![-6, 0, 0, 7, 0], ![-5, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 0, -1, 1, 0], ![0, -5, -6, -3, 16], ![1, -2, -1, 0, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-5, 1, 0, 0, 0], ![0, -5, 1, 0, 0], ![0, 0, -5, 1, 0], ![-4, -5, -6, -7, 16], ![-1, -2, -1, 0, -2]]]
  hmulB := by decide  
  f := ![![![27199, -8732, 1454, 448, -1152], ![59202, -8162, 616, 792, 0]], ![![16986, -5446, 907, 280, -720], ![36972, -5082, 385, 495, 0]], ![![20404, -6542, 1089, 336, -864], ![44412, -6104, 462, 594, 0]], ![![16997, -5456, 909, 280, -720], ![36996, -5099, 386, 495, 0]], ![![17303, -5552, 925, 285, -733], ![37662, -5186, 393, 504, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 11, 0, 0, 0], ![-8, 0, 11, 0, 0], ![-7, 0, 0, 11, 0], ![-7, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![2, -5, 1, 0, 0], ![3, 0, -5, 1, 0], ![1, -5, -6, -7, 16], ![3, -2, -1, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 11 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-8, 1, 0, 0, 0], ![0, -8, 1, 0, 0], ![0, 0, -8, 1, 0], ![-4, -5, -6, -10, 16], ![-1, -2, -1, 0, -5]]]
  hmulB := by decide  
  f := ![![![47617, -9672, 1146, 435, -768], ![100776, -8466, 765, 816, 0]], ![![29745, -6009, 711, 272, -480], ![62952, -5219, 476, 510, 0]], ![![11900, -2405, 291, 108, -192], ![25185, -2090, 204, 204, 0]], ![![41679, -8463, 1000, 381, -672], ![88209, -7404, 664, 714, 0]], ![![16806, -3408, 408, 153, -271], ![35568, -2976, 279, 288, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-9, 17, 0, 0, 0], ![-4, 0, 17, 0, 0], ![-15, 0, 0, 17, 0], ![-6, 0, 0, 0, 17]], ![![-1, 1, 0, 0, 0], ![4, -8, 1, 0, 0], ![1, 0, -8, 1, 0], ![7, -5, -6, -10, 16], ![3, -2, -1, 0, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 17 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def A3: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![2, 1, 0, 0, 0], ![0, 2, 1, 0, 0], ![0, 0, 2, 1, 0], ![-4, -5, -6, 0, 16], ![-1, -2, -1, 0, 5]]]
  hmulB := by decide  
  f := ![![![66411, -574209, -303585, -443, -3584], ![-1212009, 11249591, 16391, 8288, 0]], ![![4740, -41004, -21679, -32, -256], ![-86505, 803307, 1184, 592, 0]], ![![61667, -533167, -281886, -411, -3328], ![-1125431, 10445545, 15207, 7696, 0]], ![![14230, -123049, -65056, -95, -768], ![-259699, 2410696, 3516, 1776, 0]], ![![39486, -341424, -180512, -264, -2131], ![-720624, 6688976, 9768, 4928, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 37, 0, 0, 0], ![-33, 0, 37, 0, 0], ![-8, 0, 0, 37, 0], ![-22, 0, 0, 0, 37]], ![![0, 1, 0, 0, 0], ![-1, 2, 1, 0, 0], ![-2, 0, 2, 1, 0], ![-4, -5, -6, 0, 16], ![-2, -2, -1, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N3 : Nat.card (O ⧸ I3) = 37 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3)

def A4: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![-2, 1, 0, 0, 0], ![0, -2, 1, 0, 0], ![0, 0, -2, 1, 0], ![-4, -5, -6, -4, 16], ![-1, -2, -1, 0, 1]]]
  hmulB := by decide  
  f := ![![![256963, -2162736, 1027751, 1732, -12880], ![4694227, -37737965, 55056, 29785, 0]], ![![245789, -2068694, 983061, 1657, -12320], ![4490099, -36097015, 52651, 28490, 0]], ![![234615, -1974654, 938374, 1581, -11760], ![4285971, -34456101, 50283, 27195, 0]], ![![201103, -1692577, 804328, 1355, -10080], ![3673771, -29534064, 43106, 23310, 0]], ![![194458, -1636663, 777756, 1311, -9747], ![3552379, -28558426, 41653, 22540, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-35, 37, 0, 0, 0], ![-33, 0, 37, 0, 0], ![-29, 0, 0, 37, 0], ![-28, 0, 0, 0, 37]], ![![-1, 1, 0, 0, 0], ![1, -2, 1, 0, 0], ![1, 0, -2, 1, 0], ![1, -5, -6, -4, 16], ![2, -2, -1, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N4 : Nat.card (O ⧸ I4) = 37 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4)

def Log00Mem : IdealMemCertificate B I0
  ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-7, 0, 2, 1, -5] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, 0, 2, 1, -5]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-4, 0, 2, 1, -5]
 hxeq :=  rfl
 m:= 3
 C := ![-7, 0, 2, 1, -5]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k :=  1
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
  ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-1, -1, -2, -1, 6] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, -1, -2, -1, 6]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![5, -1, -2, -1, 6]
 hxeq :=  rfl
 m:= 6
 C := ![-1, -1, -2, -1, 6]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k :=  3
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
  ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-7, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 6
 C := ![-7, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k :=  3
 hpow := by zmod_pow
 heql := by decide

def Log03Mem : IdealMemCertificate B I0
  ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-1, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 1, 0, 0, 0]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 1, 0, 0, 0]
 hxeq :=  rfl
 m:= 1
 C := ![-1, 1, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log03Mem
 k :=  0
 hpow := by zmod_pow
 heql := by decide

def Log04Mem : IdealMemCertificate B I0
  ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-6, 0, -1, -1, 4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-2, 0, -1, -1, 4]
 hmem := by decide

def Log04: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 0, -1, -1, 4]
 hxeq :=  rfl
 m:= 6
 C := ![-6, 0, -1, -1, 4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log04Mem
 k :=  3
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
  ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] ![-12, 0, 2, 1, -5] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, 0, 2, 1, -5]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-4, 0, 2, 1, -5]
 hxeq :=  rfl
 m:= 8
 C := ![-12, 0, 2, 1, -5]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k :=  3
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
  ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] ![2, -1, -2, -1, 6] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, -1, -2, -1, 6]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![5, -1, -2, -1, 6]
 hxeq :=  rfl
 m:= 3
 C := ![2, -1, -2, -1, 6]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k :=  8
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
  ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] ![-11, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 10
 C := ![-11, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k :=  5
 hpow := by zmod_pow
 heql := by decide

def Log13Mem : IdealMemCertificate B I1
  ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] ![-5, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 1, 0, 0, 0]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 1, 0, 0, 0]
 hxeq :=  rfl
 m:= 5
 C := ![-5, 1, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log13Mem
 k :=  4
 hpow := by zmod_pow
 heql := by decide

def Log14Mem : IdealMemCertificate B I1
  ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] ![-9, 0, -1, -1, 4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-2, 0, -1, -1, 4]
 hmem := by decide

def Log14: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 0, -1, -1, 4]
 hxeq :=  rfl
 m:= 9
 C := ![-9, 0, -1, -1, 4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log14Mem
 k :=  6
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
  ![![17, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-7, 0, 2, 1, -5] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![0, 0, 2, 1, -5]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R17) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-4, 0, 2, 1, -5]
 hxeq :=  rfl
 m:= 3
 C := ![-7, 0, 2, 1, -5]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k :=  1
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
  ![![17, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![4, -1, -2, -1, 6] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![0, -1, -2, -1, 6]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R17) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![5, -1, -2, -1, 6]
 hxeq :=  rfl
 m:= 1
 C := ![4, -1, -2, -1, 6]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k :=  0
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
  ![![17, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-17, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R17) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 16
 C := ![-17, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k :=  8
 hpow := by zmod_pow
 heql := by decide

def Log23Mem : IdealMemCertificate B I2
  ![![17, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-8, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 1, 0, 0, 0]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R17) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 1, 0, 0, 0]
 hxeq :=  rfl
 m:= 8
 C := ![-8, 1, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log23Mem
 k :=  10
 hpow := by zmod_pow
 heql := by decide

def Log24Mem : IdealMemCertificate B I2
  ![![17, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-12, 0, -1, -1, 4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 0, -1, -1, 4]
 hmem := by decide

def Log24: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R17) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 0, -1, -1, 4]
 hxeq :=  rfl
 m:= 12
 C := ![-12, 0, -1, -1, 4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log24Mem
 k :=  13
 hpow := by zmod_pow
 heql := by decide

def Log30Mem : IdealMemCertificate B I3
  ![![37, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] ![-36, 0, 2, 1, -5] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![0, 0, 2, 1, -5]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-4, 0, 2, 1, -5]
 hxeq :=  rfl
 m:= 32
 C := ![-36, 0, 2, 1, -5]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log30Mem
 k :=  5
 hpow := by zmod_pow
 heql := by decide

def Log31Mem : IdealMemCertificate B I3
  ![![37, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] ![-18, -1, -2, -1, 6] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-2, -1, -2, -1, 6]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![5, -1, -2, -1, 6]
 hxeq :=  rfl
 m:= 23
 C := ![-18, -1, -2, -1, 6]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log31Mem
 k :=  15
 hpow := by zmod_pow
 heql := by decide

def Log32Mem : IdealMemCertificate B I3
  ![![37, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] ![-37, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 36
 C := ![-37, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log32Mem
 k :=  18
 hpow := by zmod_pow
 heql := by decide

def Log33Mem : IdealMemCertificate B I3
  ![![37, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] ![-35, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1, 1, 0, 0, 0]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 1, 0, 0, 0]
 hxeq :=  rfl
 m:= 35
 C := ![-35, 1, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log33Mem
 k :=  19
 hpow := by zmod_pow
 heql := by decide

def Log34Mem : IdealMemCertificate B I3
  ![![37, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] ![-27, 0, -1, -1, 4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-2, 0, -1, -1, 4]
 hmem := by decide

def Log34: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 0, -1, -1, 4]
 hxeq :=  rfl
 m:= 27
 C := ![-27, 0, -1, -1, 4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log34Mem
 k :=  6
 hpow := by zmod_pow
 heql := by decide

def Log40Mem : IdealMemCertificate B I4
  ![![37, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] ![-8, 0, 2, 1, -5] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![1, 0, 2, 1, -5]
 hmem := by decide

def Log40: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-4, 0, 2, 1, -5]
 hxeq :=  rfl
 m:= 4
 C := ![-8, 0, 2, 1, -5]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log40Mem
 k :=  2
 hpow := by zmod_pow
 heql := by decide

def Log41Mem : IdealMemCertificate B I4
  ![![37, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] ![1, -1, -2, -1, 6] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-1, -1, -2, -1, 6]
 hmem := by decide

def Log41: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![5, -1, -2, -1, 6]
 hxeq :=  rfl
 m:= 4
 C := ![1, -1, -2, -1, 6]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log41Mem
 k :=  2
 hpow := by zmod_pow
 heql := by decide

def Log42Mem : IdealMemCertificate B I4
  ![![37, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] ![-37, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log42: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 36
 C := ![-37, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log42Mem
 k :=  18
 hpow := by zmod_pow
 heql := by decide

def Log43Mem : IdealMemCertificate B I4
  ![![37, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] ![-2, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-1, 1, 0, 0, 0]
 hmem := by decide

def Log43: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 1, 0, 0, 0]
 hxeq :=  rfl
 m:= 2
 C := ![-2, 1, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log43Mem
 k :=  1
 hpow := by zmod_pow
 heql := by decide

def Log44Mem : IdealMemCertificate B I4
  ![![37, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] ![-24, 0, -1, -1, 4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-2, 0, -1, -1, 4]
 hmem := by decide

def Log44: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 0, -1, -1, 4]
 hxeq :=  rfl
 m:= 24
 C := ![-24, 0, -1, -1, 4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log44Mem
 k :=  29
 hpow := by zmod_pow
 heql := by decide

end Sat2
