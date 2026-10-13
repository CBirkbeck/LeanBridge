/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.RI5_1_3790297_2
import LeanBridge.IdealArithmetic.Generation.ClassGroupGeneration
import LeanBridge.IdealArithmetic.IdealArithmetic
import LeanBridge.IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![9, 6, -2, 1, -1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0], ![9, 6, -2, 1, -1]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![3, 19, 23, 1, 0], ![23, 13, 25, 0, 1]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![9, 6, -2, 1, -1], ![-3, 6, 1, -4, 13], ![3, -9, 17, 9, -25], ![-11, 8, -38, -1, 69], ![-3, -8, -2, 0, 15]]]
  hmulB := by decide  
  f := ![![![1045, -2184, -352, 1436, -4676], ![116, 10440, 0, 0, 0]], ![![-54, 109, 18, -72, 234], ![0, -522, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![69, -157, -23, 101, -330], ![24, 738, 0, 0, 0]], ![![799, -1687, -269, 1106, -3603], ![110, 8046, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-3, -19, -23, 29, 0], ![-23, -13, -25, 0, 29]], ![![1, 0, 0, 1, -1], ![-10, -3, -8, -4, 13], ![19, 5, 15, 9, -25], ![-55, -30, -60, -1, 69], ![-12, -7, -13, 0, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [4, 6, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 18, 16], [7, 10, 13], [0, 1]]
 g := ![![[3, 13, 9], [1, 5], [19, 22, 25], [1]],![[18, 3, 26, 16], [15, 25], [21, 23, 22, 16], [3, 18, 14, 7]],![[22, 21, 15, 5], [2, 24], [12, 10, 18, 4], [24, 4, 1, 22]]]
 h' := ![![[17, 18, 16], [1, 0, 3], [11, 17, 11], [25, 23, 24], [0, 1]],![[7, 10, 13], [7, 10, 1], [3, 14, 5], [0, 1, 28], [17, 18, 16]],![[0, 1], [5, 19, 25], [19, 27, 13], [15, 5, 6], [7, 10, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 26], []]
 b := ![[], [16, 18, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where 
  n := 3
  hpos := by decide  
  P := [4, 6, 5, 1]
  hirr := P29P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![1492, -79488, -56581, -27655, -74604]
  a := ![9, 11, 12, 3, -36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide  
  g := ![62081, 48821, 84296, -27655, -74604]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![-8, 3, -1, 0, 1]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0], ![-8, 3, -1, 0, 1]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![11, 5, 1, 0, 0], ![3, 15, 0, 1, 0], ![3, 8, 0, 0, 1]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![-8, 3, -1, 0, 1], ![-1, -10, 2, -1, 3], ![1, -2, -7, 4, -7], ![-9, -5, -19, -15, 43], ![-2, -5, -2, 0, -3]]]
  hmulB := by decide  
  f := ![![![-21233, -181346, 33614, -16850, 52652], ![-12238, -527626, -9744, 0, 0]], ![![-19654, -167913, 31118, -15598, 48744], ![-11310, -488534, -9048, 0, 0]], ![![-11417, -97514, 18074, -9060, 28311], ![-6579, -283716, -5244, 0, 0]], ![![-12361, -105612, 19573, -9811, 30659], ![-7111, -307272, -5688, 0, 0]], ![![-7615, -65082, 12062, -6046, 18893], ![-4374, -189350, -3504, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-11, -5, 29, 0, 0], ![-3, -15, 0, 29, 0], ![-3, -8, 0, 0, 29]], ![![0, 0, -1, 0, 1], ![-1, -1, 2, -1, 3], ![3, 1, -7, 4, -7], ![4, -1, -19, -15, 43], ![1, 1, -2, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [15, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 28], [0, 1]]
 g := ![![[9, 5], [22], [2, 4], [10, 1]],![[1, 24], [22], [13, 25], [20, 28]]]
 h' := ![![[10, 28], [19, 18], [28, 14], [24, 27], [0, 1]],![[0, 1], [25, 11], [23, 15], [4, 2], [10, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [22, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where 
  n := 2
  hpos := by decide  
  P := [15, 19, 1]
  hirr := P29P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-16057, -99906, -70338, -27393, -4640]
  a := ![51, 47, 47, -6, -201]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide  
  g := ![29440, 24131, -70338, -27393, -4640]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0, 0, 0], ![9, 6, -2, 1, -1]] ![![29, 0, 0, 0, 0], ![-8, 3, -1, 0, 1]]
  ![![29, 0, 0, 0, 0]] where
 M :=  ![![![841, 0, 0, 0, 0], ![-232, 87, -29, 0, 29]], ![![261, 174, -58, 29, -29], ![-87, -29, 0, -29, 87]]]
 hmul := by decide  
 g :=  ![![![![29, 0, 0, 0, 0]], ![![-8, 3, -1, 0, 1]]], ![![![9, 6, -2, 1, -1]], ![![-3, -1, 0, -1, 3]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [20, 12, 5, 14, 20, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 15, 23, 11, 14], [24, 4, 5, 29, 27], [11, 0, 16, 8, 20], [19, 11, 18, 14, 1], [0, 1]]
 g := ![![[13, 28, 19, 7, 2], [5, 9, 12, 22, 25], [14, 11, 1], []],![[2, 25, 30, 8, 12, 23, 8, 9], [29, 24, 30, 7, 1, 12, 23, 4], [20, 23, 30, 15, 15, 0, 10, 4], [25, 14, 19, 27, 18, 16, 10, 16]],![[22, 9, 18, 2, 7, 6, 29, 27], [12, 28, 16, 2, 1, 17, 2, 3], [0, 19, 29, 20, 8, 2, 20, 30], [28, 4, 28, 24, 24, 7, 6, 29]],![[26, 24, 15, 5, 27, 11, 3, 2], [1, 14, 27, 25, 10, 7, 9, 1], [9, 5, 3, 29, 12, 15, 9, 4], [7, 9, 2, 20, 20, 18, 12, 2]],![[5, 17, 27, 9, 14, 16, 22, 14], [6, 19, 12, 22, 22, 5, 14, 16], [23, 29, 19, 8, 25, 24, 17, 10], [25, 17, 27, 7, 30, 2, 22, 1]]]
 h' := ![![[19, 15, 23, 11, 14], [24, 9, 0, 1, 8], [30, 15, 26, 16, 26], [0, 0, 0, 1], [0, 1]],![[24, 4, 5, 29, 27], [25, 18, 12, 19, 26], [28, 6, 26, 25, 24], [4, 10, 16, 17, 24], [19, 15, 23, 11, 14]],![[11, 0, 16, 8, 20], [23, 5, 16, 21, 30], [12, 16, 8, 18, 21], [27, 17, 23, 27, 16], [24, 4, 5, 29, 27]],![[19, 11, 18, 14, 1], [7, 3, 23, 6, 11], [5, 21, 28, 28, 18], [13, 15, 14, 12, 5], [11, 0, 16, 8, 20]],![[0, 1], [23, 27, 11, 15, 18], [30, 4, 5, 6, 4], [4, 20, 9, 5, 17], [19, 11, 18, 14, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 1, 17, 28], [], [], []]
 b := ![[], [18, 2, 30, 29, 29], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where 
  n := 5
  hpos := by decide  
  P := [20, 12, 5, 14, 20, 1]
  hirr := P31P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-98886404, -227630148, -143908758, -25794232, 294703174]
  a := ![4, 4, 5, 0, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide  
  g := ![-3189884, -7342908, -4642218, -832072, 9506554]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 28629151 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀

instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, -2, 0, 0, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![4, -2, 0, 0, 1]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![29, 22, 1, 0, 0], ![28, 26, 0, 1, 0], ![4, 35, 0, 0, 1]] where
  M :=![![![4, -2, 0, 0, 1], ![-1, 2, -3, 0, 3], ![-3, -7, -1, -3, 9], ![3, -6, 2, 5, -21], ![0, -2, -2, -1, 3]]]
  hmulB := by decide  
  f := ![![![6, -4, -4, -1, 7]], ![![-3, -3, -5, -2, 5]], ![![3, -5, -6, -2, 8]], ![![3, -4, -6, -2, 7]], ![![-2, -3, -5, -2, 5]]]
  g := ![![![0, -1, 0, 0, 1], ![2, -1, -3, 0, 3], ![2, -6, -1, -3, 9], ![-3, 15, 2, 5, -21], ![2, -1, -2, -1, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [36, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 36], [0, 1]]
 g := ![![[4, 36], [10], [22, 4], [16], [1]],![[0, 1], [10], [1, 33], [16], [1]]]
 h' := ![![[4, 36], [13, 6], [22, 11], [17, 35], [1, 4], [0, 1]],![[0, 1], [0, 31], [29, 26], [9, 2], [17, 33], [4, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [15, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where 
  n := 2
  hpos := by decide  
  P := [36, 33, 1]
  hirr := P37P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![2320, -8268, -6028, -3929, -18346]
  a := ![-34, -38, -40, -8, 137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide  
  g := ![9744, 23476, -6028, -3929, -18346]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![2, 1, 0, 0, 0], ![0, 2, 1, 0, 0], ![0, 0, 2, 1, 0], ![-4, -5, -6, 0, 16], ![-1, -2, -1, 0, 5]]]
  hmulB := by decide  
  f := ![![![66411, -574209, -303585, -443, -3584], ![-1212009, 11249591, 16391, 8288, 0]], ![![4740, -41004, -21679, -32, -256], ![-86505, 803307, 1184, 592, 0]], ![![61667, -533167, -281886, -411, -3328], ![-1125431, 10445545, 15207, 7696, 0]], ![![14230, -123049, -65056, -95, -768], ![-259699, 2410696, 3516, 1776, 0]], ![![39486, -341424, -180512, -264, -2131], ![-720624, 6688976, 9768, 4928, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 37, 0, 0, 0], ![-33, 0, 37, 0, 0], ![-8, 0, 0, 37, 0], ![-22, 0, 0, 0, 37]], ![![0, 1, 0, 0, 0], ![-1, 2, 1, 0, 0], ![-2, 0, 2, 1, 0], ![-4, -5, -6, 0, 16], ![-2, -2, -1, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, -1, 0, 1]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![2, 1, -1, 0, 1]] 
 ![![37, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![2, 1, -1, 0, 1], ![-1, 0, 0, -1, 3], ![1, -2, 3, 2, -7], ![-1, 5, -7, -1, 11], ![0, -1, 0, 0, 1]]]
  hmulB := by decide  
  f := ![![![18, 1, -1, -3, 5]], ![![7, 1, 0, -1, 1]], ![![13, 2, 0, -2, 3]], ![![3, 1, 1, 0, 1]], ![![7, 1, 0, -1, 2]]]
  g := ![![![0, 1, -1, 0, 1], ![-1, 0, 0, -1, 3], ![1, -2, 3, 2, -7], ![-1, 5, -7, -1, 11], ![0, -1, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2

def I37N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] i)))

def SI37N3: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![-2, 1, 0, 0, 0], ![0, -2, 1, 0, 0], ![0, 0, -2, 1, 0], ![-4, -5, -6, -4, 16], ![-1, -2, -1, 0, 1]]]
  hmulB := by decide  
  f := ![![![256963, -2162736, 1027751, 1732, -12880], ![4694227, -37737965, 55056, 29785, 0]], ![![245789, -2068694, 983061, 1657, -12320], ![4490099, -36097015, 52651, 28490, 0]], ![![234615, -1974654, 938374, 1581, -11760], ![4285971, -34456101, 50283, 27195, 0]], ![![201103, -1692577, 804328, 1355, -10080], ![3673771, -29534064, 43106, 23310, 0]], ![![194458, -1636663, 777756, 1311, -9747], ![3552379, -28558426, 41653, 22540, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-35, 37, 0, 0, 0], ![-33, 0, 37, 0, 0], ![-29, 0, 0, 37, 0], ![-28, 0, 0, 0, 37]], ![![-1, 1, 0, 0, 0], ![1, -2, 1, 0, 0], ![1, 0, -2, 1, 0], ![1, -5, -6, -4, 16], ![2, -2, -1, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N3 : Nat.card (O ⧸ I37N3) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N3)

lemma isPrimeI37N3 : Ideal.IsPrime I37N3 := prime_ideal_of_norm_prime hp37.out _ NI37N3
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![4, -2, 0, 0, 1]] ![![37, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![37, 0, 0, 0, 0], ![-18, -11, 9, 1, -12]] where
 M :=  ![![![148, -74, 0, 0, 37], ![7, -2, -3, 0, 5]]]
 hmul := by decide  
 g :=  ![![![![12006, 1787, -7427, 9949, -28123], ![1221, -52762, 0, 0, 0]], ![![561, 84, -347, 464, -1311], ![59, -2461, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0, 0, 0], ![-18, -11, 9, 1, -12]] ![![2, 1, -1, 0, 1]]
  ![![37, 0, 0, 0, 0], ![-13, -8, 16, 4, -27]] where
 M :=  ![![![74, 37, -37, 0, 37]], ![![-17, -19, 38, 28, -115]]]
 hmul := by decide  
 g :=  ![![![![2, 1, -1, 0, 1], ![0, 0, 0, 0, 0]]], ![![![2, 1, -2, 0, 2], ![7, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N2 : IdealMulLeCertificate' Table 
  ![![37, 0, 0, 0, 0], ![-13, -8, 16, 4, -27]] ![![37, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![37, 0, 0, 0, 0]] where
 M :=  ![![![1369, 0, 0, 0, 0], ![-74, 37, 0, 0, 0]], ![![-481, -296, 592, 148, -999], ![37, 37, -37, 0, 37]]]
 hmul := by decide  
 g :=  ![![![![37, 0, 0, 0, 0]], ![![-2, 1, 0, 0, 0]]], ![![![-13, -8, 16, 4, -27]], ![![1, 1, -1, 0, 1]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2, I37N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
    exact isPrimeI37N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1 ⊙ MulI37N2)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![68, 0, -44, -19, 102]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0], ![68, 0, -44, -19, 102]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![28, 0, 6, 38, 1]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![68, 0, -44, -19, 102], ![-26, -41, 12, -6, 2], ![22, 0, -7, 24, -90], ![-6, 82, -54, -55, 114], ![23, 0, 2, -1, -27]]]
  hmulB := by decide  
  f := ![![![-67, 0, 44, 19, -102], ![41, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![-64, 0, 42, 19, -97], ![39, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-28, 0, -6, -38, 41]], ![![-68, 0, -16, -95, 102], ![-2, -1, 0, -2, 2], ![62, 0, 13, 84, -90], ![-78, 2, -18, -107, 114], ![19, 0, 4, 25, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [28, 13, 29, 18, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 34, 24, 29], [24, 17, 26, 21], [32, 30, 32, 32], [0, 1]]
 g := ![![[29, 38, 23, 37], [5, 23, 37], [21, 22, 23], [23, 1], []],![[34, 40, 40, 7, 32, 26], [0, 26, 10], [34, 18, 32], [13, 21, 19, 0, 9, 34], [5, 30, 21]],![[3, 2, 28, 36, 40, 36], [21, 16, 39], [7, 26, 32], [22, 27, 27, 0, 32, 2], [22, 1, 31]],![[22, 23, 21, 7, 5, 18], [22, 16, 5], [26, 35, 23], [13, 28, 7, 25], [20, 16, 40]]]
 h' := ![![[8, 34, 24, 29], [32, 14, 18, 18], [7, 37, 18, 18], [12, 1, 17, 8], [0, 0, 1], [0, 1]],![[24, 17, 26, 21], [32, 13, 13, 14], [27, 16, 32, 25], [6, 5, 30, 14], [6, 8, 7, 2], [8, 34, 24, 29]],![[32, 30, 32, 32], [11, 1, 31, 20], [5, 23, 14, 11], [23, 29, 40, 27], [1, 10, 18, 39], [24, 17, 26, 21]],![[0, 1], [38, 13, 20, 30], [11, 6, 18, 28], [1, 6, 36, 33], [13, 23, 15], [32, 30, 32, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [35, 8, 13], []]
 b := ![[], [], [19, 12, 7, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where 
  n := 4
  hpos := by decide  
  P := [28, 13, 29, 18, 1]
  hirr := P41P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![119303915, 182719411, 114571313, 5144244, -434296605]
  a := ![23, 29, 35, 13, -93]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide  
  g := ![299502655, 4456571, 66350023, 402644274, -434296605]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![4, 1, 0, 0, 0], ![0, 4, 1, 0, 0], ![0, 0, 4, 1, 0], ![-4, -5, -6, 2, 16], ![-1, -2, -1, 0, 7]]]
  hmulB := by decide  
  f := ![![![133953, -2203964, -563845, -1608, -2400], ![-1366858, 22940033, 53628, 6150, 0]], ![![16068, -264395, -67641, -193, -288], ![-163958, 2751961, 6437, 738, 0]], ![![85725, -1410417, -360830, -1029, -1536], ![-874739, 14680379, 34317, 3936, 0]], ![![75015, -1234226, -315757, -901, -1344], ![-765454, 12846485, 30054, 3444, 0]], ![![91476, -1505146, -385064, -1098, -1639], ![-933422, 15666352, 36618, 4200, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 41, 0, 0, 0], ![-25, 0, 41, 0, 0], ![-23, 0, 0, 41, 0], ![-28, 0, 0, 0, 41]], ![![0, 1, 0, 0, 0], ![-1, 4, 1, 0, 0], ![-3, 0, 4, 1, 0], ![-8, -5, -6, 2, 16], ![-4, -2, -1, 0, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0, 0, 0], ![68, 0, -44, -19, 102]] ![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0]]
  ![![41, 0, 0, 0, 0]] where
 M :=  ![![![1681, 0, 0, 0, 0], ![164, 41, 0, 0, 0]], ![![2788, 0, -1804, -779, 4182], ![246, -41, -164, -82, 410]]]
 hmul := by decide  
 g :=  ![![![![41, 0, 0, 0, 0]], ![![4, 1, 0, 0, 0]]], ![![![68, 0, -44, -19, 102]], ![![6, -1, -4, -2, 10]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![-95, 6, 61, 20, -120]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0], ![-95, 6, 61, 20, -120]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![42, 15, 2, 7, 1]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]], ![![-95, 6, 61, 20, -120], ![40, 45, 6, 21, -40], ![-44, 15, -41, -36, 216], ![-72, -296, 15, 31, 72], ![-49, -39, -31, -1, 92]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![54, -3, -34, -11, 67], ![24, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-42, -15, -2, -7, 43]], ![![115, 42, 7, 20, -120], ![40, 15, 2, 7, -40], ![-212, -75, -11, -36, 216], ![-72, -32, -3, -11, 72], ![-91, -33, -5, -15, 92]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [12, 5, 0, 24, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 32, 0, 5], [5, 24, 11, 37], [41, 29, 32, 1], [0, 1]]
 g := ![![[13, 2, 12, 13], [17, 40, 5, 38], [5, 32, 31], [19, 1], []],![[42, 16, 8, 15, 1, 3], [6, 42, 39, 32, 12, 29], [24, 5, 14], [10, 3, 32, 26], [14, 2, 25]],![[10, 10, 25, 5, 27, 42], [37, 31, 35, 11, 13, 29], [38, 36, 16], [20, 16, 26, 16, 37, 42], [1, 36, 36]],![[34, 19, 40, 13, 18, 9], [27, 3, 30, 21, 31, 31], [7, 0, 15], [25, 10, 6, 35, 38, 36], [36, 40, 1]]]
 h' := ![![[16, 32, 0, 5], [11, 7, 22, 23], [23, 8, 39, 9], [30, 22, 38, 17], [0, 0, 1], [0, 1]],![[5, 24, 11, 37], [23, 2, 12, 11], [10, 25, 19, 25], [30, 7, 2, 10], [2, 27, 26], [16, 32, 0, 5]],![[41, 29, 32, 1], [12, 37, 18, 6], [26, 11, 33, 26], [3, 41, 31, 4], [13, 18, 31, 6], [5, 24, 11, 37]],![[0, 1], [21, 40, 34, 3], [8, 42, 38, 26], [36, 16, 15, 12], [2, 41, 28, 37], [41, 29, 32, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [29, 39, 12], []]
 b := ![[], [], [8, 4, 8, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where 
  n := 4
  hpos := by decide  
  P := [12, 5, 0, 24, 1]
  hirr := P43P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![5511076, 26624638, 4722814, 714922, -2332000]
  a := ![-8, -10, -10, -14, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide  
  g := ![2405932, 1432666, 218298, 396254, -2332000]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![14, 1, 0, 0, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0], ![14, 1, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]], ![![14, 1, 0, 0, 0], ![0, 14, 1, 0, 0], ![0, 0, 14, 1, 0], ![-4, -5, -6, 12, 16], ![-1, -2, -1, 0, 17]]]
  hmulB := by decide  
  f := ![![![1426739, -47068349, -3680334, -28766, -8448], ![-4375637, 144887726, 964490, 22704, 0]], ![![534976, -17649518, -1380042, -10787, -3168], ![-1640707, 54329468, 361673, 8514, 0]], ![![713297, -23532864, -1840073, -14383, -4224], ![-2187596, 72439822, 482245, 11352, 0]], ![![1159201, -38243085, -2990270, -23372, -6864], ![-3555130, 117721430, 783633, 18447, 0]], ![![929012, -30649164, -2396506, -18732, -5501], ![-2849168, 94345510, 628068, 14784, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-14, 43, 0, 0, 0], ![-19, 0, 43, 0, 0], ![-35, 0, 0, 43, 0], ![-28, 0, 0, 0, 43]], ![![0, 1, 0, 0, 0], ![-5, 14, 1, 0, 0], ![-7, 0, 14, 1, 0], ![-16, -5, -6, 12, 16], ![-10, -2, -1, 0, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0, 0, 0], ![-95, 6, 61, 20, -120]] ![![43, 0, 0, 0, 0], ![14, 1, 0, 0, 0]]
  ![![43, 0, 0, 0, 0]] where
 M :=  ![![![1849, 0, 0, 0, 0], ![602, 43, 0, 0, 0]], ![![-4085, 258, 2623, 860, -5160], ![-1290, 129, 860, 301, -1720]]]
 hmul := by decide  
 g :=  ![![![![43, 0, 0, 0, 0]], ![![14, 1, 0, 0, 0]]], ![![![-95, 6, 61, 20, -120]], ![![-30, 3, 20, 7, -40]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![2, 15, -19, 1, 16]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![2, 15, -19, 1, 16]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![3, 32, 1, 1, 0], ![44, 43, 34, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![2, 15, -19, 1, 16], ![-20, -35, -7, -21, 64], ![20, -43, 27, 35, -144], ![4, 133, -109, -43, 128], ![5, -9, 6, 0, -33]]]
  hmulB := by decide  
  f := ![![![24001, 44530, 4066, 24958, -71872], ![-10340, 55366, 0, 0, 0]], ![![-776, -1449, -114, -806, 2304], ![376, -1786, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![1003, 1851, 188, 1044, -3024], ![-389, 2318, 0, 0, 0]], ![![21760, 40369, 3694, 22628, -65169], ![-9358, 50198, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-3, -32, -1, 47, 0], ![-44, -43, -34, 0, 47]], ![![-15, -15, -12, 1, 16], ![-59, -45, -46, -21, 64], ![133, 107, 104, 35, -144], ![-117, -85, -94, -43, 128], ![31, 30, 24, 0, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [28, 11, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 22, 15], [0, 24, 32], [0, 1]]
 g := ![![[36], [4, 43, 28], [1, 24, 34], [7, 26, 1], []],![[5, 46, 11, 5], [5, 13, 42, 40], [43, 4, 34, 38], [6, 4, 19, 39], [24, 37]],![[0, 41, 35, 42], [4, 36, 21, 25], [4, 4, 6, 24], [23, 26, 16, 25], [7, 37]]]
 h' := ![![[26, 22, 15], [29, 6], [19, 39, 34], [39, 41, 9], [0, 0, 1], [0, 1]],![[0, 24, 32], [44, 38, 43], [41, 19, 38], [13, 15, 32], [4, 32, 24], [26, 22, 15]],![[0, 1], [29, 3, 4], [29, 36, 22], [14, 38, 6], [39, 15, 22], [0, 24, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44], []]
 b := ![[], [34, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where 
  n := 3
  hpos := by decide  
  P := [28, 11, 21, 1]
  hirr := P47P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![2856725, 9335397, 6223745, 1729845, -6195724]
  a := ![-22, -31, -26, -4, 101]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide  
  g := ![5750618, 4689287, 4577628, 1729845, -6195724]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![6, 21, -1, 0, 1]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![6, 21, -1, 0, 1]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![17, 45, 1, 0, 0], ![34, 13, 0, 1, 0], ![23, 19, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![6, 21, -1, 0, 1], ![-1, 4, 20, -1, 3], ![1, -2, 7, 22, -7], ![-81, -95, -127, -37, 331], ![-20, -41, -20, 0, 65]]]
  hmulB := by decide  
  f := ![![![-661925, 2053581, 11677295, -573012, 1732717], ![621481, -27403068, -21432, 0, 0]], ![![-302719, 939135, 5340311, -262042, 792409], ![284256, -12532080, -9823, 0, 0]], ![![-528671, 1640141, 9326435, -457644, 1383884], ![496398, -21886304, -17138, 0, 0]], ![![-562569, 1745334, 9924512, -486999, 1472632], ![528197, -23289816, -18221, 0, 0]], ![![-446296, 1384596, 7873270, -386342, 1168261], ![419037, -18476172, -14459, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-17, -45, 47, 0, 0], ![-34, -13, 0, 47, 0], ![-23, -19, 0, 0, 47]], ![![0, 1, -1, 0, 1], ![-8, -20, 20, -1, 3], ![-15, -10, 7, 22, -7], ![-91, -4, -127, -37, 331], ![-25, -8, -20, 0, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [40, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 46], [0, 1]]
 g := ![![[20, 25], [43, 2], [24, 12], [32, 1], [1]],![[42, 22], [41, 45], [12, 35], [31, 46], [1]]]
 h' := ![![[46, 46], [19, 42], [27, 40], [36, 24], [7, 46], [0, 1]],![[0, 1], [24, 5], [34, 7], [12, 23], [8, 1], [46, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [34, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where 
  n := 2
  hpos := by decide  
  P := [40, 1, 1]
  hirr := P47P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-104, -620, -478, -151, 196]
  a := ![2, 2, 2, -2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide  
  g := ![184, 407, -478, -151, 196]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0, 0, 0], ![2, 15, -19, 1, 16]] ![![47, 0, 0, 0, 0], ![6, 21, -1, 0, 1]]
  ![![47, 0, 0, 0, 0]] where
 M :=  ![![![2209, 0, 0, 0, 0], ![282, 987, -47, 0, 47]], ![![94, 705, -893, 47, 752], ![-423, -611, -282, -470, 1551]]]
 hmul := by decide  
 g :=  ![![![![47, 0, 0, 0, 0]], ![![6, 21, -1, 0, 1]]], ![![![2, 15, -19, 1, 16]], ![![-9, -13, -6, -10, 33]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0], ![-77, 12, 39, 17, -89]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0], ![-77, 12, 39, 17, -89]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![36, 35, 21, 1, 1]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]], ![![-77, 12, 39, 17, -89], ![21, 16, -1, 5, 5], ![-25, -14, -19, -11, 95], ![-51, -160, -43, 3, 109], ![-36, -35, -21, -1, 52]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![37, -5, -18, -8, 42], ![25, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-36, -35, -21, -1, 53]], ![![59, 59, 36, 2, -89], ![-3, -3, -2, 0, 5], ![-65, -63, -38, -2, 95], ![-75, -75, -44, -2, 109], ![-36, -35, -21, -1, 52]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [39, 39, 34, 51, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 34, 5, 27], [41, 38, 45, 9], [24, 33, 3, 17], [0, 1]]
 g := ![![[22, 11, 34, 15], [50, 40, 40], [26, 52, 43, 11], [23, 2, 1], []],![[35, 26, 36, 43, 30, 50], [13, 45, 1], [2, 3, 31, 51, 2, 12], [7, 20, 11], [39, 9, 4, 27, 4, 20]],![[42, 25, 47, 31, 48, 46], [10, 28, 17], [5, 26, 39, 46, 1, 10], [0, 12, 42], [45, 12, 31, 44, 44, 40]],![[19, 24, 26, 14, 47, 38], [23, 47, 36], [48, 18, 3, 31, 49, 29], [10, 6, 6], [21, 25, 41, 37, 25, 37]]]
 h' := ![![[43, 34, 5, 27], [7, 5, 5, 11], [46, 48, 13, 27], [4, 32, 2, 45], [0, 0, 0, 1], [0, 1]],![[41, 38, 45, 9], [33, 0, 4, 43], [13, 34, 5, 52], [44, 11, 52, 36], [23, 7, 20, 45], [43, 34, 5, 27]],![[24, 33, 3, 17], [43, 8, 10, 45], [3, 1, 15, 21], [13, 50, 7, 31], [15, 42, 24, 25], [41, 38, 45, 9]],![[0, 1], [8, 40, 34, 7], [51, 23, 20, 6], [10, 13, 45, 47], [20, 4, 9, 35], [24, 33, 3, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [19, 31, 23], []]
 b := ![[], [], [44, 42, 38, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where 
  n := 4
  hpos := by decide  
  P := [39, 39, 34, 51, 1]
  hirr := P53P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-2926483, -5570733, -2614877, -947931, 9532554]
  a := ![-9, -12, -5, -7, 39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide  
  g := ![-6530159, -6400191, -3826387, -197745, 9532554]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0], ![-19, 1, 0, 0, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0], ![-19, 1, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]], ![![-19, 1, 0, 0, 0], ![0, -19, 1, 0, 0], ![0, 0, -19, 1, 0], ![-4, -5, -6, -21, 16], ![-1, -2, -1, 0, -16]]]
  hmulB := by decide  
  f := ![![![788123, -10917390, 640496, 2304, -4416], ![2195366, -30342076, 185076, 14628, 0]], ![![525384, -7278005, 426984, 1536, -2944], ![1463490, -20227344, 123384, 9752, 0]], ![![196990, -2728699, 160090, 576, -1104], ![548728, -7583716, 46269, 3657, 0]], ![![459719, -6368495, 373624, 1344, -2576], ![1280576, -17699596, 107962, 8533, 0]], ![![371740, -5149715, 302117, 1087, -2083], ![1035505, -14312310, 87289, 6900, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-34, 53, 0, 0, 0], ![-10, 0, 53, 0, 0], ![-31, 0, 0, 53, 0], ![-25, 0, 0, 0, 53]], ![![-1, 1, 0, 0, 0], ![12, -19, 1, 0, 0], ![3, 0, -19, 1, 0], ![9, -5, -6, -21, 16], ![9, -2, -1, 0, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0, 0, 0], ![-77, 12, 39, 17, -89]] ![![53, 0, 0, 0, 0], ![-19, 1, 0, 0, 0]]
  ![![53, 0, 0, 0, 0]] where
 M :=  ![![![2809, 0, 0, 0, 0], ![-1007, 53, 0, 0, 0]], ![![-4081, 636, 2067, 901, -4717], ![1484, -212, -742, -318, 1696]]]
 hmul := by decide  
 g :=  ![![![![53, 0, 0, 0, 0]], ![![-19, 1, 0, 0, 0]]], ![![![-77, 12, 39, 17, -89]], ![![28, -4, -14, -6, 32]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![-22, 29, 8, 1, -11]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0], ![-22, 29, 8, 1, -11]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![8, 43, 47, 1, 0], ![51, 12, 25, 0, 1]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]], ![![-22, 29, 8, 1, -11], ![7, -5, 34, 6, -17], ![-7, 11, -24, 22, 45], ![-133, -207, -166, -68, 487], ![-36, -64, -35, 0, 93]]]
  hmulB := by decide  
  f := ![![![7657, -5907, 33396, 5907, -16467], ![1947, -58410, 0, 0, 0]], ![![-126, 91, -612, -108, 306], ![0, 1062, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![952, -742, 4081, 722, -2007], ![279, -7146, 0, 0, 0]], ![![6595, -5090, 28743, 5084, -14171], ![1688, -50274, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-8, -43, -47, 59, 0], ![-51, -12, -25, 0, 59]], ![![9, 2, 4, 1, -11], ![14, -1, 3, 6, -17], ![-42, -25, -37, 22, 45], ![-414, -53, -155, -68, 487], ![-81, -20, -40, 0, 93]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [13, 25, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 43, 35], [16, 15, 24], [0, 1]]
 g := ![![[57, 14, 5], [30, 26, 12], [56, 17], [19, 8, 53], [1]],![[17, 28, 49, 35], [20, 43, 37, 19], [12, 36], [41, 9, 3, 3], [53, 54, 34, 41]],![[54, 40, 5, 56], [46, 39, 58, 34], [0, 12], [37, 22, 51, 58], [17, 15, 8, 18]]]
 h' := ![![[26, 43, 35], [23, 27, 51], [42, 24, 22], [48, 3, 28], [46, 34, 42], [0, 1]],![[16, 15, 24], [54, 58, 58], [48, 9, 49], [26, 7, 53], [13, 40, 50], [26, 43, 35]],![[0, 1], [40, 33, 9], [48, 26, 47], [44, 49, 37], [40, 44, 26], [16, 15, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 6], []]
 b := ![[], [6, 37, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where 
  n := 3
  hpos := by decide  
  P := [13, 25, 17, 1]
  hirr := P59P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-167668, -196388, -123096, 12233, 662456]
  a := ![-16, -20, -24, -8, 65]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide  
  g := ![-577132, -146981, -292533, 12233, 662456]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![5, 1, 0, 0, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0], ![5, 1, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]], ![![5, 1, 0, 0, 0], ![0, 5, 1, 0, 0], ![0, 0, 5, 1, 0], ![-4, -5, -6, 3, 16], ![-1, -2, -1, 0, 8]]]
  hmulB := by decide  
  f := ![![![72463, -385115, -79702, -573, -2448], ![-847830, 4722950, 6726, 9027, 0]], ![![8512, -45292, -9376, -68, -288], ![-99591, 555426, 826, 1062, 0]], ![![42611, -226535, -46887, -338, -1440], ![-498555, 2778134, 4012, 5310, 0]], ![![8525, -45314, -9381, -68, -288], ![-99744, 555716, 827, 1062, 0]], ![![69999, -372065, -77003, -554, -2365], ![-819000, 4562888, 6523, 8721, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-5, 59, 0, 0, 0], ![-34, 0, 59, 0, 0], ![-7, 0, 0, 59, 0], ![-57, 0, 0, 0, 59]], ![![0, 1, 0, 0, 0], ![-1, 5, 1, 0, 0], ![-3, 0, 5, 1, 0], ![-12, -5, -6, 3, 16], ![-7, -2, -1, 0, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 0, 2, 1, -5]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-6, 0, 2, 1, -5]] 
 ![![59, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-6, 0, 2, 1, -5], ![1, -1, -1, 0, 1], ![-1, -1, -2, -1, 3], ![1, -2, 2, 0, -7], ![-1, 0, 0, 0, -2]]]
  hmulB := by decide  
  f := ![![![-8, 4, -8, 2, 3]], ![![-1, 0, -1, 0, 1]], ![![-3, 1, -3, 1, 0]], ![![-5, 4, -6, 1, 2]], ![![-4, 2, -4, 1, 1]]]
  g := ![![![1, 0, 2, 1, -5], ![0, -1, -1, 0, 1], ![0, -1, -2, -1, 3], ![3, -2, 2, 0, -7], ![1, 0, 0, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0, 0, 0], ![-22, 29, 8, 1, -11]] ![![59, 0, 0, 0, 0], ![5, 1, 0, 0, 0]]
  ![![-8, 4, -8, 2, 3]] where
 M :=  ![![![3481, 0, 0, 0, 0], ![295, 59, 0, 0, 0]], ![![-1298, 1711, 472, 59, -649], ![-103, 140, 74, 11, -72]]]
 hmul := by decide  
 g :=  ![![![![-354, 0, 118, 59, -295]], ![![-29, -1, 9, 5, -24]]], ![![![165, -39, -87, -30, 178]], ![![13, -4, -8, -3, 16]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-8, 4, -8, 2, 3]] ![![-6, 0, 2, 1, -5]]
  ![![59, 0, 0, 0, 0]] where
 M :=  ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26, -4, -7, -5, 25]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![26, -4, -7, -5, 25]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![55, 55, 12, 1, 0], ![34, 45, 7, 0, 1]] where
  M :=![![![26, -4, -7, -5, 25], ![-5, 1, 1, 3, -5], ![-7, -10, -12, -5, 33], ![-13, -48, -13, -2, 19], ![0, -13, -11, -3, 21]]]
  hmulB := by decide  
  f := ![![![2, 1, -2, 0, 1]], ![![-1, 0, 0, -2, 3]], ![![5, 3, 9, 4, -23]], ![![2, 2, 0, -1, -1]], ![![1, 1, 0, -1, 0]]]
  g := ![![![-9, -14, -2, -5, 25], ![0, 1, 0, 3, -5], ![-14, -20, -3, -5, 33], ![-9, -13, -2, -2, 19], ![-9, -13, -2, -3, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [41, 20, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 4, 20], [18, 56, 41], [0, 1]]
 g := ![![[0, 36, 58], [50, 25], [8, 15, 34], [36, 49, 19], [1]],![[7, 9], [33, 48], [52, 32, 43, 19], [29, 56, 35, 19], [50, 60, 21, 9]],![[33, 48, 21, 60], [19, 58], [28, 43, 0, 47], [19, 10, 41, 4], [20, 10, 60, 52]]]
 h' := ![![[0, 4, 20], [4, 39, 34], [38, 40, 56], [49, 50, 41], [20, 41, 18], [0, 1]],![[18, 56, 41], [59, 41], [3, 28, 32], [31, 38, 2], [24, 17, 59], [0, 4, 20]],![[0, 1], [59, 42, 27], [44, 54, 34], [45, 34, 18], [10, 3, 45], [18, 56, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3], []]
 b := ![[], [41, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where 
  n := 3
  hpos := by decide  
  P := [41, 20, 43, 1]
  hirr := P61P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![132345, 546132, 378397, 123121, -192048]
  a := ![-12, -16, -17, -3, 52]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide  
  g := ![-1798, 39617, 4021, 123121, -192048]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![53, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![-8, 1, 0, 0, 0], ![0, -8, 1, 0, 0], ![0, 0, -8, 1, 0], ![-4, -5, -6, -10, 16], ![-1, -2, -1, 0, -5]]]
  hmulB := by decide  
  f := ![![![2881533, -47311140, 5980405, 5010, -27984], ![21918337, -358074331, 761280, 106689, 0]], ![![2532261, -41576383, 5255496, 4403, -24592], ![19261605, -314670818, 668987, 93757, 0]], ![![2794218, -45877333, 5799165, 4858, -27136], ![21254177, -347222552, 738222, 103456, 0]], ![![1746393, -28673412, 3624490, 3036, -16960], ![13283912, -217014690, 461405, 64660, 0]], ![![188964, -3102356, 392160, 328, -1835], ![1437352, -23480168, 49952, 6996, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-53, 61, 0, 0, 0], ![-58, 0, 61, 0, 0], ![-37, 0, 0, 61, 0], ![-4, 0, 0, 0, 61]], ![![-1, 1, 0, 0, 0], ![6, -8, 1, 0, 0], ![7, 0, -8, 1, 0], ![15, -5, -6, -10, 16], ![3, -2, -1, 0, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![-5, 1, 0, 0, 0], ![0, -5, 1, 0, 0], ![0, 0, -5, 1, 0], ![-4, -5, -6, -7, 16], ![-1, -2, -1, 0, -2]]]
  hmulB := by decide  
  f := ![![![2167106, -11662447, 2268693, 4529, -17280], ![26385977, -137070538, 184891, 65880, 0]], ![![2058745, -11079233, 2155243, 4302, -16416], ![25066609, -130215907, 175680, 62586, 0]], ![![1300263, -6997439, 1361212, 2717, -10368], ![15831579, -82241968, 110959, 39528, 0]], ![![2058752, -11079334, 2155263, 4302, -16416], ![25066694, -130217122, 175681, 62586, 0]], ![![639483, -3441377, 669452, 1336, -5099], ![7786137, -40447012, 54584, 19440, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-56, 61, 0, 0, 0], ![-36, 0, 61, 0, 0], ![-58, 0, 0, 61, 0], ![-18, 0, 0, 0, 61]], ![![-1, 1, 0, 0, 0], ![4, -5, 1, 0, 0], ![2, 0, -5, 1, 0], ![10, -5, -6, -7, 16], ![3, -2, -1, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![26, -4, -7, -5, 25]] ![![61, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]]
  ![![61, 0, 0, 0, 0], ![-114, -21, 58, 17, -108]] where
 M :=  ![![![1586, -244, -427, -305, 1525], ![-213, 33, 57, 43, -205]]]
 hmul := by decide  
 g :=  ![![![![26, -4, -7, -5, 25], ![0, 0, 0, 0, 0]], ![![75, 15, -39, -11, 71], ![42, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0, 0, 0], ![-114, -21, 58, 17, -108]] ![![61, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]]
  ![![61, 0, 0, 0, 0]] where
 M :=  ![![![3721, 0, 0, 0, 0], ![-305, 61, 0, 0, 0]], ![![-6954, -1281, 3538, 1037, -6588], ![610, 122, -305, -61, 488]]]
 hmul := by decide  
 g :=  ![![![![61, 0, 0, 0, 0]], ![![-5, 1, 0, 0, 0]]], ![![![-114, -21, 58, 17, -108]], ![![10, 2, -5, -1, 8]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)


lemma PB122I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)
  rfl

def PB122I1 : PrimesBelowBoundCertificateInterval' O 23 61 122 where
  m := 9
  g := ![2, 1, 4, 2, 2, 2, 2, 3, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB122I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0]
    · exact ![I37N0, I37N1, I37N2, I37N3]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1, I61N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![24389, 841]
    · exact ![28629151]
    · exact ![1369, 37, 37, 37]
    · exact ![2825761, 41]
    · exact ![3418801, 43]
    · exact ![103823, 2209]
    · exact ![7890481, 53]
    · exact ![205379, 59, 59]
    · exact ![226981, 61, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
      exact NI37N3
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  Il := ![[], [], [I37N1, I37N2, I37N3], [I41N1], [I43N1], [], [I53N1], [I59N1, I59N2], [I61N1, I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
