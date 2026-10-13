/-
Copyright (c) 2025 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_0_76176_2.ClassGroupData4_0_76176_2
import LeanBridge.IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import LeanBridge.IdealArithmetic.Saturation.PrincipalityCertificate
import LeanBridge.IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import LeanBridge.IdealArithmetic.Examples.NF4_0_76176_2.RI4_0_76176_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section 

namespace Sat2 
instance hq3 : Fact $ Nat.Prime 3 := {out := by norm_num}
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}
instance hq23 : Fact $ Nat.Prime 23 := {out := by norm_num}

def R3 : IsOrderOf (2 : ZMod 3) 2 where
 m := 1
 P := ![2]
 e := ![1]
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

def R23 : IsOrderOf (5 : ZMod 23) 22 where
 m := 2
 P := ![2, 11]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![0, 1, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![4, 1, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![0, 1, 0, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0], ![4, 1, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0], ![0, 1, 0, 0]] 
 ![![3, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![2, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![0, 0, 0, 3]], ![![0, 1, 0, 0], ![0, 0, 1, 0], ![16, -15, -16, 35], ![6, -8, -8, 18]]]
  hmulB := by decide  
  f := ![![![33, -54, -29, 70], ![72, -9, -6, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 1, 0, 0]], ![![22, -36, -20, 47], ![48, -4, -4, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![-2, 0, 0, 3]], ![![0, 1, 0, 0], ![0, 0, 1, 0], ![-18, -15, -16, 35], ![-10, -8, -8, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 3 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0], ![4, 1, 0, 0]] 
 ![![13, 0, 0, 0], ![4, 1, 0, 0], ![10, 0, 1, 0], ![3, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![4, 1, 0, 0], ![0, 4, 1, 0], ![16, -15, -12, 35], ![6, -8, -8, 22]]]
  hmulB := by decide  
  f := ![![![-14095, -3376, 327, -1400], ![43732, 1989, 520, 0]], ![![-7052, -1691, 163, -700], ![21880, 1001, 260, 0]], ![![-10574, -2534, 245, -1050], ![32808, 1496, 390, 0]], ![![-3257, -782, 75, -323], ![10106, 465, 120, 0]]]
  g := ![![![1, 0, 0, 0], ![-4, 13, 0, 0], ![-10, 0, 13, 0], ![-3, 0, 0, 13]], ![![0, 1, 0, 0], ![-2, 4, 1, 0], ![7, -15, -12, 35], ![4, -8, -8, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 13 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![13, 0, 0, 0], ![0, 1, 0, 0]] 
 ![![13, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![9, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![0, 1, 0, 0], ![0, 0, 1, 0], ![16, -15, -16, 35], ![6, -8, -8, 18]]]
  hmulB := by decide  
  f := ![![![65, -120, -64, 140], ![780, 0, -52, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 1, 0, 0]], ![![45, -84, -45, 97], ![552, 9, -36, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![-9, 0, 0, 13]], ![![0, 1, 0, 0], ![0, 0, 1, 0], ![-23, -15, -16, 35], ![-12, -8, -8, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 13 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def A3: IdealEqSpanCertificate' Table ![![23, 0, 0, 0], ![4, 1, 0, 0]] 
 ![![23, 0, 0, 0], ![4, 1, 0, 0], ![7, 0, 1, 0], ![21, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0], ![0, 23, 0, 0], ![0, 0, 23, 0], ![0, 0, 0, 23]], ![![4, 1, 0, 0], ![0, 4, 1, 0], ![16, -15, -12, 35], ![6, -8, -8, 22]]]
  hmulB := by decide  
  f := ![![![25233, 5210, -782, 2450], ![-138644, -1334, -1610, 0]], ![![5044, 1039, -157, 490], ![-27714, -253, -322, 0]], ![![7569, 1561, -235, 735], ![-41588, -390, -483, 0]], ![![23043, 4758, -714, 2237], ![-126612, -1218, -1470, 0]]]
  g := ![![![1, 0, 0, 0], ![-4, 23, 0, 0], ![-7, 0, 23, 0], ![-21, 0, 0, 23]], ![![0, 1, 0, 0], ![-1, 4, 1, 0], ![-25, -15, -12, 35], ![-16, -8, -8, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N3 : Nat.card (O ⧸ I3) = 23 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3)

def Log00Mem : IdealMemCertificate B I0
  ![![3, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![2, 0, 0, 1]] ![1, -1, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, -1, -1, 2]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![3, -1, -1, 2]
 hxeq :=  rfl
 m:= 2
 C := ![1, -1, -1, 2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k :=  1
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
  ![![3, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![2, 0, 0, 1]] ![-3, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, 0, 0]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0]
 hxeq :=  rfl
 m:= 2
 C := ![-3, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k :=  1
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
  ![![3, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![2, 0, 0, 1]] ![-4, 0, 1, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, 0, 1, -2]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-2, 0, 1, -2]
 hxeq :=  rfl
 m:= 2
 C := ![-4, 0, 1, -2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k :=  1
 hpow := by zmod_pow
 heql := by decide

def Log03Mem : IdealMemCertificate B I0
  ![![3, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![2, 0, 0, 1]] ![-2, 0, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-2, 0, -1, 2]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 0, -1, 2]
 hxeq :=  rfl
 m:= 2
 C := ![-2, 0, -1, 2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log03Mem
 k :=  1
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
  ![![13, 0, 0, 0], ![4, 1, 0, 0], ![10, 0, 1, 0], ![3, 0, 0, 1]] ![-8, -1, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, -1, -1, 2]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![3, -1, -1, 2]
 hxeq :=  rfl
 m:= 11
 C := ![-8, -1, -1, 2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k :=  7
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
  ![![13, 0, 0, 0], ![4, 1, 0, 0], ![10, 0, 1, 0], ![3, 0, 0, 1]] ![-13, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0, 0, 0]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0]
 hxeq :=  rfl
 m:= 12
 C := ![-13, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k :=  6
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
  ![![13, 0, 0, 0], ![4, 1, 0, 0], ![10, 0, 1, 0], ![3, 0, 0, 1]] ![-9, 0, 1, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0, 1, -2]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-2, 0, 1, -2]
 hxeq :=  rfl
 m:= 7
 C := ![-9, 0, 1, -2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k :=  11
 hpow := by zmod_pow
 heql := by decide

def Log13Mem : IdealMemCertificate B I1
  ![![13, 0, 0, 0], ![4, 1, 0, 0], ![10, 0, 1, 0], ![3, 0, 0, 1]] ![-4, 0, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, 0, -1, 2]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 0 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 0, -1, 2]
 hxeq :=  rfl
 m:= 4
 C := ![-4, 0, -1, 2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log13Mem
 k :=  2
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
  ![![13, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![9, 0, 0, 1]] ![-8, -1, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-2, -1, -1, 2]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![3, -1, -1, 2]
 hxeq :=  rfl
 m:= 11
 C := ![-8, -1, -1, 2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k :=  7
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
  ![![13, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![9, 0, 0, 1]] ![-13, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 0, 0, 0]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0]
 hxeq :=  rfl
 m:= 12
 C := ![-13, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k :=  6
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
  ![![13, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![9, 0, 0, 1]] ![-5, 0, 1, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![1, 0, 1, -2]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-2, 0, 1, -2]
 hxeq :=  rfl
 m:= 3
 C := ![-5, 0, 1, -2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k :=  4
 hpow := by zmod_pow
 heql := by decide

def Log23Mem : IdealMemCertificate B I2
  ![![13, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![9, 0, 0, 1]] ![-8, 0, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-2, 0, -1, 2]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 0, -1, 2]
 hxeq :=  rfl
 m:= 8
 C := ![-8, 0, -1, 2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log23Mem
 k :=  3
 hpow := by zmod_pow
 heql := by decide

def Log30Mem : IdealMemCertificate B I3
  ![![23, 0, 0, 0], ![4, 1, 0, 0], ![7, 0, 1, 0], ![21, 0, 0, 1]] ![-15, -1, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-2, -1, -1, 2]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R23) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![3, -1, -1, 2]
 hxeq :=  rfl
 m:= 18
 C := ![-15, -1, -1, 2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log30Mem
 k :=  12
 hpow := by zmod_pow
 heql := by decide

def Log31Mem : IdealMemCertificate B I3
  ![![23, 0, 0, 0], ![4, 1, 0, 0], ![7, 0, 1, 0], ![21, 0, 0, 1]] ![-23, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1, 0, 0, 0]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R23) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0]
 hxeq :=  rfl
 m:= 22
 C := ![-23, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log31Mem
 k :=  11
 hpow := by zmod_pow
 heql := by decide

def Log32Mem : IdealMemCertificate B I3
  ![![23, 0, 0, 0], ![4, 1, 0, 0], ![7, 0, 1, 0], ![21, 0, 0, 1]] ![-12, 0, 1, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![1, 0, 1, -2]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R23) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-2, 0, 1, -2]
 hxeq :=  rfl
 m:= 10
 C := ![-12, 0, 1, -2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log32Mem
 k :=  3
 hpow := by zmod_pow
 heql := by decide

def Log33Mem : IdealMemCertificate B I3
  ![![23, 0, 0, 0], ![4, 1, 0, 0], ![7, 0, 1, 0], ![21, 0, 0, 1]] ![-11, 0, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-2, 0, -1, 2]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R23) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 0, -1, 2]
 hxeq :=  rfl
 m:= 11
 C := ![-11, 0, -1, 2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log33Mem
 k :=  9
 hpow := by zmod_pow
 heql := by decide

end Sat2
