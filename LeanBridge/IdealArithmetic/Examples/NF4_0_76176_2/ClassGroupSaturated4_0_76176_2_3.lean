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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![4, 1, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![0, 1, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0], ![4, 1, 0, 0]] 
 ![![13, 0, 0, 0], ![4, 1, 0, 0], ![10, 0, 1, 0], ![3, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![4, 1, 0, 0], ![0, 4, 1, 0], ![16, -15, -12, 35], ![6, -8, -8, 22]]]
  hmulB := by decide  
  f := ![![![-14095, -3376, 327, -1400], ![43732, 1989, 520, 0]], ![![-7052, -1691, 163, -700], ![21880, 1001, 260, 0]], ![![-10574, -2534, 245, -1050], ![32808, 1496, 390, 0]], ![![-3257, -782, 75, -323], ![10106, 465, 120, 0]]]
  g := ![![![1, 0, 0, 0], ![-4, 13, 0, 0], ![-10, 0, 13, 0], ![-3, 0, 0, 13]], ![![0, 1, 0, 0], ![-2, 4, 1, 0], ![7, -15, -12, 35], ![4, -8, -8, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 13 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0], ![0, 1, 0, 0]] 
 ![![13, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![9, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![0, 1, 0, 0], ![0, 0, 1, 0], ![16, -15, -16, 35], ![6, -8, -8, 18]]]
  hmulB := by decide  
  f := ![![![65, -120, -64, 140], ![780, 0, -52, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 1, 0, 0]], ![![45, -84, -45, 97], ![552, 9, -36, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![-9, 0, 0, 13]], ![![0, 1, 0, 0], ![0, 0, 1, 0], ![-23, -15, -16, 35], ![-12, -8, -8, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 13 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
  ![![13, 0, 0, 0], ![4, 1, 0, 0], ![10, 0, 1, 0], ![3, 0, 0, 1]] ![-8, -1, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, -1, -1, 2]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
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
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k :=  7
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
  ![![13, 0, 0, 0], ![4, 1, 0, 0], ![10, 0, 1, 0], ![3, 0, 0, 1]] ![-9, 0, 1, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, 1, -2]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
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
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k :=  11
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
  ![![13, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![9, 0, 0, 1]] ![-8, -1, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-2, -1, -1, 2]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
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
  ![![13, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![9, 0, 0, 1]] ![-5, 0, 1, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![1, 0, 1, -2]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
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
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k :=  4
 hpow := by zmod_pow
 heql := by decide

end Sat3
