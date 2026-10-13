/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF6_4_19208000_1.ClassGroupData6_4_19208000_1
import LeanBridge.IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import LeanBridge.IdealArithmetic.Saturation.PrincipalityCertificate
import LeanBridge.IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import LeanBridge.IdealArithmetic.Examples.NF6_4_19208000_1.RI6_4_19208000_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat2 
instance hq29 : Fact $ Nat.Prime 29 := {out := by norm_num}
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R29 : IsOrderOf (2 : ZMod 29) 28 where
 m := 2
 P := ![2, 7]
 e := ![2, 1]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0]] i)))
def I4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0, 0], ![-5, 1, 0, 0, 0, 0]] i)))
def I5 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0], ![4, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0, 0], ![0, 7, 0, 0, 0, 0], ![0, 0, 7, 0, 0, 0], ![0, 0, 0, 7, 0, 0], ![0, 0, 0, 0, 7, 0], ![0, 0, 0, 0, 0, 7]], ![![-2, 1, 0, 0, 0, 0], ![0, -2, 5, 0, 0, 0], ![0, 0, -2, 1, 0, 0], ![0, 0, 0, -2, 5, 0], ![0, 0, 0, 0, -2, 1], ![-5, 0, 10, 0, 5, -2]]]
  hmulB := by decide  
  f := ![![![23, -27, 46, 13, 0, -20], ![77, -56, 21, 56, 140, 0]], ![![19, -17, 24, 14, -8, -16], ![64, -28, 14, 56, 112, 0]], ![![6, 0, 1, 4, -4, -8], ![20, 10, 28, 28, 56, 0]], ![![14, -13, 20, 6, 4, -12], ![47, -22, 15, 28, 84, 0]], ![![9, -10, 18, 5, -1, -8], ![30, -20, 13, 24, 56, 0]], ![![18, -20, 34, 11, 0, -17], ![60, -40, 19, 48, 120, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-5, 7, 0, 0, 0, 0], ![-2, 0, 7, 0, 0, 0], ![-4, 0, 0, 7, 0, 0], ![-3, 0, 0, 0, 7, 0], ![-6, 0, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0, 0], ![0, -2, 5, 0, 0, 0], ![0, 0, -2, 1, 0, 0], ![-1, 0, 0, -2, 5, 0], ![0, 0, 0, 0, -2, 1], ![-4, 0, 10, 0, 5, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![7, 0, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0], ![0, 0, 13, 0, 0, 0], ![0, 0, 0, 13, 0, 0], ![0, 0, 0, 0, 13, 0], ![0, 0, 0, 0, 0, 13]], ![![2, 1, 0, 0, 0, 0], ![0, 2, 5, 0, 0, 0], ![0, 0, 2, 1, 0, 0], ![0, 0, 0, 2, 5, 0], ![0, 0, 0, 0, 2, 1], ![-5, 0, 10, 0, 5, 2]]]
  hmulB := by decide  
  f := ![![![11, 3, 23, 182, 546, 63], ![-65, 13, -182, -1092, -819, 0]], ![![-2, -3, 9, 35, 98, 14], ![14, 13, -91, -182, -182, 0]], ![![5, 1, 11, 105, 315, 35], ![-29, 8, -91, -637, -455, 0]], ![![8, 2, 22, 167, 511, 63], ![-46, 10, -168, -1001, -819, 0]], ![![1, -1, 3, 42, 125, 14], ![-5, 9, -42, -252, -182, 0]], ![![5, 1, 12, 98, 294, 34], ![-29, 8, -98, -588, -441, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-2, 13, 0, 0, 0, 0], ![-7, 0, 13, 0, 0, 0], ![-12, 0, 0, 13, 0, 0], ![-3, 0, 0, 0, 13, 0], ![-7, 0, 0, 0, 0, 13]], ![![0, 1, 0, 0, 0, 0], ![-3, 2, 5, 0, 0, 0], ![-2, 0, 2, 1, 0, 0], ![-3, 0, 0, 2, 5, 0], ![-1, 0, 0, 0, 2, 1], ![-8, 0, 10, 0, 5, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 13 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0, 0], ![11, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0], ![0, 0, 13, 0, 0, 0], ![0, 0, 0, 13, 0, 0], ![0, 0, 0, 0, 13, 0], ![0, 0, 0, 0, 0, 13]], ![![-2, 1, 0, 0, 0, 0], ![0, -2, 5, 0, 0, 0], ![0, 0, -2, 1, 0, 0], ![0, 0, 0, -2, 5, 0], ![0, 0, 0, 0, -2, 1], ![-5, 0, 10, 0, 5, -2]]]
  hmulB := by decide  
  f := ![![![19, -7, 23, 0, 91, -63], ![117, 13, 182, 91, 819, 0]], ![![17, -6, 23, 0, 77, -56], ![105, 13, 182, 91, 728, 0]], ![![13, -5, 11, 7, 35, -35], ![81, 8, 91, 91, 455, 0]], ![![3, -1, 1, -1, 14, -7], ![19, 3, 14, 0, 91, 0]], ![![5, -1, 3, 0, 20, -14], ![31, 9, 42, 21, 182, 0]], ![![10, -4, 11, 0, 42, -29], ![62, 5, 84, 42, 378, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-11, 13, 0, 0, 0, 0], ![-7, 0, 13, 0, 0, 0], ![-1, 0, 0, 13, 0, 0], ![-3, 0, 0, 0, 13, 0], ![-6, 0, 0, 0, 0, 13]], ![![-1, 1, 0, 0, 0, 0], ![-1, -2, 5, 0, 0, 0], ![1, 0, -2, 1, 0, 0], ![-1, 0, 0, -2, 5, 0], ![0, 0, 0, 0, -2, 1], ![-6, 0, 10, 0, 5, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 13 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def A3: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![8, 0, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0], ![0, 0, 13, 0, 0, 0], ![0, 0, 0, 13, 0, 0], ![0, 0, 0, 0, 13, 0], ![0, 0, 0, 0, 0, 13]], ![![5, 1, 0, 0, 0, 0], ![0, 5, 5, 0, 0, 0], ![0, 0, 5, 1, 0, 0], ![0, 0, 0, 5, 5, 0], ![0, 0, 0, 0, 5, 1], ![-5, 0, 10, 0, 5, 5]]]
  hmulB := by decide  
  f := ![![![21, -21, 175, 520, 520, 8], ![-52, 65, -520, -1248, -104, 0]], ![![5, -9, 70, 216, 240, 8], ![-12, 26, -208, -520, -104, 0]], ![![6, -17, 102, 344, 360, 8], ![-14, 47, -312, -832, -104, 0]], ![![14, -22, 160, 477, 480, 8], ![-34, 64, -480, -1144, -104, 0]], ![![-3, -6, 10, 40, 37, 0], ![8, 14, -40, -96, 0, 0]], ![![6, -17, 105, 320, 320, 5], ![-14, 47, -320, -768, -64, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-5, 13, 0, 0, 0, 0], ![-8, 0, 13, 0, 0, 0], ![-12, 0, 0, 13, 0, 0], ![-1, 0, 0, 0, 13, 0], ![-8, 0, 0, 0, 0, 13]], ![![0, 1, 0, 0, 0, 0], ![-5, 5, 5, 0, 0, 0], ![-4, 0, 5, 1, 0, 0], ![-5, 0, 0, 5, 5, 0], ![-1, 0, 0, 0, 5, 1], ![-10, 0, 10, 0, 5, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N3 : Nat.card (O ⧸ I3) = 13 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3)

def A4: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0, 0], ![-5, 1, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0, 0], ![8, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![5, 0, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0], ![0, 0, 13, 0, 0, 0], ![0, 0, 0, 13, 0, 0], ![0, 0, 0, 0, 13, 0], ![0, 0, 0, 0, 0, 13]], ![![-5, 1, 0, 0, 0, 0], ![0, -5, 5, 0, 0, 0], ![0, 0, -5, 1, 0, 0], ![0, 0, 0, -5, 5, 0], ![0, 0, 0, 0, -5, 1], ![-5, 0, 10, 0, 5, -5]]]
  hmulB := by decide  
  f := ![![![96, -169, 180, 34, 0, -8], ![247, -390, 78, 104, 104, 0]], ![![66, -93, 100, 36, 0, -8], ![170, -208, 52, 104, 104, 0]], ![![66, -100, 107, 36, 0, -8], ![170, -226, 52, 104, 104, 0]], ![![22, -29, 10, 13, -10, 0], ![57, -64, -38, 26, 0, 0]], ![![12, -7, 10, 2, -3, 0], ![31, -12, 14, 8, 0, 0]], ![![45, -62, 65, 13, 0, -3], ![116, -138, 31, 40, 40, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-8, 13, 0, 0, 0, 0], ![-8, 0, 13, 0, 0, 0], ![-1, 0, 0, 13, 0, 0], ![-1, 0, 0, 0, 13, 0], ![-5, 0, 0, 0, 0, 13]], ![![-1, 1, 0, 0, 0, 0], ![0, -5, 5, 0, 0, 0], ![3, 0, -5, 1, 0, 0], ![0, 0, 0, -5, 5, 0], ![0, 0, 0, 0, -5, 1], ![-5, 0, 10, 0, 5, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N4 : Nat.card (O ⧸ I4) = 13 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4)

def A5: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![24, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] where
  M :=![![![29, 0, 0, 0, 0, 0], ![0, 29, 0, 0, 0, 0], ![0, 0, 29, 0, 0, 0], ![0, 0, 0, 29, 0, 0], ![0, 0, 0, 0, 29, 0], ![0, 0, 0, 0, 0, 29]], ![![9, 1, 0, 0, 0, 0], ![0, 9, 5, 0, 0, 0], ![0, 0, 9, 1, 0, 0], ![0, 0, 0, 9, 5, 0], ![0, 0, 0, 0, 9, 1], ![-5, 0, 10, 0, 5, 9]]]
  hmulB := by decide  
  f := ![![![181, -1789, -1113, 2679, 3016, 169], ![-580, 5829, 348, -8671, -4901, 0]], ![![45, -553, -346, 932, 1105, 65], ![-144, 1798, 116, -3016, -1885, 0]], ![![26, -440, -273, 699, 858, 52], ![-83, 1427, 87, -2262, -1508, 0]], ![![147, -1479, -921, 2213, 2522, 143], ![-471, 4818, 291, -7163, -4147, 0]], ![![45, -567, -355, 831, 932, 52], ![-144, 1843, 120, -2691, -1508, 0]], ![![30, -384, -240, 554, 624, 35], ![-96, 1248, 80, -1794, -1014, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-9, 29, 0, 0, 0, 0], ![-7, 0, 29, 0, 0, 0], ![-24, 0, 0, 29, 0, 0], ![-9, 0, 0, 0, 29, 0], ![-6, 0, 0, 0, 0, 29]], ![![0, 1, 0, 0, 0, 0], ![-4, 9, 5, 0, 0, 0], ![-3, 0, 9, 1, 0, 0], ![-9, 0, 0, 9, 5, 0], ![-3, 0, 0, 0, 9, 1], ![-6, 0, 10, 0, 5, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N5 : Nat.card (O ⧸ I5) = 29 := 
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A5)

def Log00Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0], ![4, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-5, 0, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, 1, 0, 0, 0]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 1, 0, 0, 0]
 hxeq :=  rfl
 m := 4
 C := ![-5, 0, 1, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0], ![4, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-6, 0, -1, 0, 1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, -1, 0, 1, 0]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, -1, 0, 1, 0]
 hxeq :=  rfl
 m := 5
 C := ![-6, 0, -1, 0, 1, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0], ![4, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-2, 2, 0, 0, -2, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, 2, 0, 0, -2, -1]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 1 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![3, 2, 0, 0, -2, -1]
 hxeq :=  rfl
 m := 5
 C := ![-2, 2, 0, 0, -2, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log03Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0], ![4, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-6, -2, -1, 0, 0, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, -2, -1, 0, 0, 1]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta4 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-2, -2, -1, 0, 0, 1]
 hxeq :=  rfl
 m := 4
 C := ![-6, -2, -1, 0, 0, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log03Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log04Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0], ![4, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-7, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, 0, 0, 0, 0]
 hmem := by decide

def Log04: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 6
 C := ![-7, 0, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log04Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log05Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0], ![4, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![2, -2, 1, -1, -2, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![2, -2, 1, -1, -2, 1]
 hmem := by decide

def Log05: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![4, -2, 1, -1, -2, 1]
 hxeq :=  rfl
 m := 2
 C := ![2, -2, 1, -1, -2, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log05Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![7, 0, 0, 0, 0, 1]] ![-6, 0, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0, 1, 0, 0, 0]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 1, 0, 0, 0]
 hxeq :=  rfl
 m := 5
 C := ![-6, 0, 1, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 9
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![7, 0, 0, 0, 0, 1]] ![-4, 0, -1, 0, 1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, 0, -1, 0, 1, 0]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, -1, 0, 1, 0]
 hxeq :=  rfl
 m := 3
 C := ![-4, 0, -1, 0, 1, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![7, 0, 0, 0, 0, 1]] ![-9, 2, 0, 0, -2, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, 2, 0, 0, -2, -1]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![3, 2, 0, 0, -2, -1]
 hxeq :=  rfl
 m := 12
 C := ![-9, 2, 0, 0, -2, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log13Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![7, 0, 0, 0, 0, 1]] ![-4, -2, -1, 0, 0, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, -2, -1, 0, 0, 1]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta4 1 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-2, -2, -1, 0, 0, 1]
 hxeq :=  rfl
 m := 2
 C := ![-4, -2, -1, 0, 0, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log13Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log14Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![7, 0, 0, 0, 0, 1]] ![-13, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0, 0, 0, 0, 0]
 hmem := by decide

def Log14: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 12
 C := ![-13, 0, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log14Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log15Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![7, 0, 0, 0, 0, 1]] ![-8, -2, 1, -1, -2, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, -2, 1, -1, -2, 1]
 hmem := by decide

def Log15: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![4, -2, 1, -1, -2, 1]
 hxeq :=  rfl
 m := 12
 C := ![-8, -2, 1, -1, -2, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log15Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![13, 0, 0, 0, 0, 0], ![11, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-6, 0, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 0, 1, 0, 0, 0]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 1, 0, 0, 0]
 hxeq :=  rfl
 m := 5
 C := ![-6, 0, 1, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 9
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![13, 0, 0, 0, 0, 0], ![11, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-4, 0, -1, 0, 1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![0, 0, -1, 0, 1, 0]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, -1, 0, 1, 0]
 hxeq :=  rfl
 m := 3
 C := ![-4, 0, -1, 0, 1, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![13, 0, 0, 0, 0, 0], ![11, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-3, 2, 0, 0, -2, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 2, 0, 0, -2, -1]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 1 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![3, 2, 0, 0, -2, -1]
 hxeq :=  rfl
 m := 6
 C := ![-3, 2, 0, 0, -2, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log23Mem : IdealMemCertificate B I2
 ![![13, 0, 0, 0, 0, 0], ![11, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-10, -2, -1, 0, 0, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![1, -2, -1, 0, 0, 1]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta4 1 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-2, -2, -1, 0, 0, 1]
 hxeq :=  rfl
 m := 8
 C := ![-10, -2, -1, 0, 0, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log23Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log24Mem : IdealMemCertificate B I2
 ![![13, 0, 0, 0, 0, 0], ![11, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-13, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 0, 0, 0, 0, 0]
 hmem := by decide

def Log24: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 12
 C := ![-13, 0, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log24Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log25Mem : IdealMemCertificate B I2
 ![![13, 0, 0, 0, 0, 0], ![11, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-3, -2, 1, -1, -2, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![1, -2, 1, -1, -2, 1]
 hmem := by decide

def Log25: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![4, -2, 1, -1, -2, 1]
 hxeq :=  rfl
 m := 7
 C := ![-3, -2, 1, -1, -2, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log25Mem
 k := 11
 hpow := by zmod_pow
 heql := by decide

def Log30Mem : IdealMemCertificate B I3
 ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![8, 0, 0, 0, 0, 1]] ![-5, 0, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1, 0, 1, 0, 0, 0]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 1, 0, 0, 0]
 hxeq :=  rfl
 m := 4
 C := ![-5, 0, 1, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log30Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log31Mem : IdealMemCertificate B I3
 ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![8, 0, 0, 0, 0, 1]] ![-7, 0, -1, 0, 1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![0, 0, -1, 0, 1, 0]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, -1, 0, 1, 0]
 hxeq :=  rfl
 m := 6
 C := ![-7, 0, -1, 0, 1, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log31Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log32Mem : IdealMemCertificate B I3
 ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![8, 0, 0, 0, 0, 1]] ![0, 2, 0, 0, -2, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![0, 2, 0, 0, -2, -1]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![3, 2, 0, 0, -2, -1]
 hxeq :=  rfl
 m := 3
 C := ![0, 2, 0, 0, -2, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log32Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log33Mem : IdealMemCertificate B I3
 ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![8, 0, 0, 0, 0, 1]] ![-10, -2, -1, 0, 0, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![0, -2, -1, 0, 0, 1]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta4 1 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-2, -2, -1, 0, 0, 1]
 hxeq :=  rfl
 m := 8
 C := ![-10, -2, -1, 0, 0, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log33Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log34Mem : IdealMemCertificate B I3
 ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![8, 0, 0, 0, 0, 1]] ![-13, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1, 0, 0, 0, 0, 0]
 hmem := by decide

def Log34: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 12
 C := ![-13, 0, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log34Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log35Mem : IdealMemCertificate B I3
 ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![8, 0, 0, 0, 0, 1]] ![-8, -2, 1, -1, -2, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![0, -2, 1, -1, -2, 1]
 hmem := by decide

def Log35: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![4, -2, 1, -1, -2, 1]
 hxeq :=  rfl
 m := 12
 C := ![-8, -2, 1, -1, -2, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log35Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log40Mem : IdealMemCertificate B I4
 ![![13, 0, 0, 0, 0, 0], ![8, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![5, 0, 0, 0, 0, 1]] ![-5, 0, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-1, 0, 1, 0, 0, 0]
 hmem := by decide

def Log40: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 1, 0, 0, 0]
 hxeq :=  rfl
 m := 4
 C := ![-5, 0, 1, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log40Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log41Mem : IdealMemCertificate B I4
 ![![13, 0, 0, 0, 0, 0], ![8, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![5, 0, 0, 0, 0, 1]] ![-7, 0, -1, 0, 1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![0, 0, -1, 0, 1, 0]
 hmem := by decide

def Log41: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, -1, 0, 1, 0]
 hxeq :=  rfl
 m := 6
 C := ![-7, 0, -1, 0, 1, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log41Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log42Mem : IdealMemCertificate B I4
 ![![13, 0, 0, 0, 0, 0], ![8, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![5, 0, 0, 0, 0, 1]] ![-4, 2, 0, 0, -2, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-1, 2, 0, 0, -2, -1]
 hmem := by decide

def Log42: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 1 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![3, 2, 0, 0, -2, -1]
 hxeq :=  rfl
 m := 7
 C := ![-4, 2, 0, 0, -2, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log42Mem
 k := 11
 hpow := by zmod_pow
 heql := by decide

def Log43Mem : IdealMemCertificate B I4
 ![![13, 0, 0, 0, 0, 0], ![8, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![5, 0, 0, 0, 0, 1]] ![-6, -2, -1, 0, 0, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![1, -2, -1, 0, 0, 1]
 hmem := by decide

def Log43: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta4 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-2, -2, -1, 0, 0, 1]
 hxeq :=  rfl
 m := 4
 C := ![-6, -2, -1, 0, 0, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log43Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log44Mem : IdealMemCertificate B I4
 ![![13, 0, 0, 0, 0, 0], ![8, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![5, 0, 0, 0, 0, 1]] ![-13, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-1, 0, 0, 0, 0, 0]
 hmem := by decide

def Log44: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 12
 C := ![-13, 0, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log44Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log45Mem : IdealMemCertificate B I4
 ![![13, 0, 0, 0, 0, 0], ![8, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![5, 0, 0, 0, 0, 1]] ![-6, -2, 1, -1, -2, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![0, -2, 1, -1, -2, 1]
 hmem := by decide

def Log45: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![4, -2, 1, -1, -2, 1]
 hxeq :=  rfl
 m := 10
 C := ![-6, -2, 1, -1, -2, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log45Mem
 k := 10
 hpow := by zmod_pow
 heql := by decide

def Log50Mem : IdealMemCertificate B I5
 ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![24, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-22, 0, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A5
 g := ![-1, 0, 1, 0, 0, 0]
 hmem := by decide

def Log50: DiscreteLogCertificate N5 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 1, 0, 0, 0]
 hxeq :=  rfl
 m := 21
 C := ![-22, 0, 1, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log50Mem
 k := 17
 hpow := by zmod_pow
 heql := by decide

def Log51Mem : IdealMemCertificate B I5
 ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![24, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-27, 0, -1, 0, 1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A5
 g := ![-1, 0, -1, 0, 1, 0]
 hmem := by decide

def Log51: DiscreteLogCertificate N5 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, -1, 0, 1, 0]
 hxeq :=  rfl
 m := 26
 C := ![-27, 0, -1, 0, 1, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log51Mem
 k := 19
 hpow := by zmod_pow
 heql := by decide

def Log52Mem : IdealMemCertificate B I5
 ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![24, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-6, 2, 0, 0, -2, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A5
 g := ![0, 2, 0, 0, -2, -1]
 hmem := by decide

def Log52: DiscreteLogCertificate N5 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![3, 2, 0, 0, -2, -1]
 hxeq :=  rfl
 m := 9
 C := ![-6, 2, 0, 0, -2, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log52Mem
 k := 10
 hpow := by zmod_pow
 heql := by decide

def Log53Mem : IdealMemCertificate B I5
 ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![24, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-19, -2, -1, 0, 0, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A5
 g := ![0, -2, -1, 0, 0, 1]
 hmem := by decide

def Log53: DiscreteLogCertificate N5 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 zeta4 1 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-2, -2, -1, 0, 0, 1]
 hxeq :=  rfl
 m := 17
 C := ![-19, -2, -1, 0, 0, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log53Mem
 k := 21
 hpow := by zmod_pow
 heql := by decide

def Log54Mem : IdealMemCertificate B I5
 ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![24, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-29, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A5
 g := ![-1, 0, 0, 0, 0, 0]
 hmem := by decide

def Log54: DiscreteLogCertificate N5 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 28
 C := ![-29, 0, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log54Mem
 k := 14
 hpow := by zmod_pow
 heql := by decide

def Log55Mem : IdealMemCertificate B I5
 ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![24, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-18, -2, 1, -1, -2, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A5
 g := ![1, -2, 1, -1, -2, 1]
 hmem := by decide

def Log55: DiscreteLogCertificate N5 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 6
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![4, -2, 1, -1, -2, 1]
 hxeq :=  rfl
 m := 22
 C := ![-18, -2, 1, -1, -2, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log55Mem
 k := 26
 hpow := by zmod_pow
 heql := by decide

end Sat2
