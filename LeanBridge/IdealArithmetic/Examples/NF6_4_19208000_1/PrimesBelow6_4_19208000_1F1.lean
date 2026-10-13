/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF6_4_19208000_1.RI6_4_19208000_1
import LeanBridge.IdealArithmetic.Generation.ClassGroupGeneration
import LeanBridge.IdealArithmetic.IdealArithmetic
import LeanBridge.IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 1, 0, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![3, 0, 1, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0, 0], ![0, 29, 0, 0, 0, 0], ![3, 0, 1, 0, 0, 0], ![0, 3, 0, 1, 0, 0], ![20, 0, 0, 0, 1, 0], ![0, 20, 0, 0, 0, 1]] where
  M :=![![![3, 0, 1, 0, 0, 0], ![0, 3, 0, 1, 0, 0], ![0, 0, 3, 0, 1, 0], ![0, 0, 0, 3, 0, 1], ![-1, 0, 2, 0, 4, 0], ![0, -1, 0, 2, 0, 4]]]
  hmulB := by decide  
  f := ![![![10, 0, -4, 0, 1, 0]], ![![0, 10, 0, -4, 0, 1]], ![![1, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0]], ![![7, 0, -3, 0, 1, 0]], ![![0, 7, 0, -3, 0, 1]]]
  g := ![![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, 0, 3, 0, 1, 0], ![0, -1, 0, 3, 0, 1], ![-3, 0, 2, 0, 4, 0], ![0, -3, 0, 2, 0, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [27, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 28], [0, 1]]
 g := ![![[], [6], [0, 4], [0, 1]], ![[], [6], [0, 25], [0, 28]]]
 h' := ![![[0, 28], [12], [0, 8], [0, 2], [0, 1]], ![[0, 1], [12], [0, 21], [0, 27], [0, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [0, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [27, 0, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-316, -74, 315, 112, 1081, 110]
  a := ![0, -1, -1, 1, 19, 1]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-789, -90, 315, 112, 1081, 110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -1, 0, 0, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![0, -1, 0, 0, 1, 0]] 
 ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![24, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] where
  M :=![![![0, -1, 0, 0, 1, 0], ![0, 0, -5, 0, 0, 1], ![-1, 0, 2, -1, 1, 0], ![0, -1, 0, 2, -5, 1], ![-1, 0, 1, 0, 3, -1], ![5, -1, -10, 1, -5, 3]]]
  hmulB := by decide  
  f := ![![![-10, -15, 9, -1, 17, 11]], ![![-5, -5, 4, 0, 7, 4]], ![![-3, -4, 3, 0, 5, 3]], ![![-10, -13, 9, 0, 17, 10]], ![![-4, -5, 4, 0, 7, 4]], ![![-5, -4, 6, 1, 8, 4]]]
  g := ![![![0, -1, 0, 0, 1, 0], ![1, 0, -5, 0, 0, 1], ![0, 0, 2, -1, 1, 0], ![0, -1, 0, 2, -5, 1], ![-1, 0, 1, 0, 3, -1], ![3, -1, -10, 1, -5, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -1, 0, 0, -1, 0]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![0, -1, 0, 0, -1, 0]] 
 ![![29, 0, 0, 0, 0, 0], ![20, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![5, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![23, 0, 0, 0, 0, 1]] where
  M :=![![![0, -1, 0, 0, -1, 0], ![0, 0, -5, 0, 0, -1], ![1, 0, -2, -1, -1, 0], ![0, 1, 0, -2, -5, -1], ![1, 0, -1, 0, -3, -1], ![5, 1, -10, -1, -5, -3]]]
  hmulB := by decide  
  f := ![![![10, -15, -9, -1, -17, 11]], ![![5, -10, -5, -1, -10, 7]], ![![3, -4, -3, 0, -5, 3]], ![![0, -2, 0, -1, 0, 1]], ![![4, -5, -4, 0, -7, 4]], ![![5, -11, -3, -2, -9, 7]]]
  g := ![![![1, -1, 0, 0, -1, 0], ![2, 0, -5, 0, 0, -1], ![1, 0, -2, -1, -1, 0], ![2, 1, 0, -2, -5, -1], ![2, 0, -1, 0, -3, -1], ![6, 1, -10, -1, -5, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2

def I29N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 0, 1, 0, -3, 0]] i)))

def SI29N3: IdealEqSpanCertificate' Table ![![4, 0, 1, 0, -3, 0]] 
 ![![29, 0, 0, 0, 0, 0], ![0, 29, 0, 0, 0, 0], ![18, 0, 1, 0, 0, 0], ![0, 18, 0, 1, 0, 0], ![24, 0, 0, 0, 1, 0], ![0, 24, 0, 0, 0, 1]] where
  M :=![![![4, 0, 1, 0, -3, 0], ![0, 4, 0, 1, 0, -3], ![3, 0, -2, 0, -2, 0], ![0, 3, 0, -2, 0, -2], ![2, 0, -1, 0, -4, 0], ![0, 2, 0, -1, 0, -4]]]
  hmulB := by decide  
  f := ![![![6, 0, 7, 0, -8, 0]], ![![0, 6, 0, 7, 0, -8]], ![![4, 0, 4, 0, -5, 0]], ![![0, 4, 0, 4, 0, -5]], ![![5, 0, 6, 0, -7, 0]], ![![0, 5, 0, 6, 0, -7]]]
  g := ![![![2, 0, 1, 0, -3, 0], ![0, 2, 0, 1, 0, -3], ![3, 0, -2, 0, -2, 0], ![0, 3, 0, -2, 0, -2], ![4, 0, -1, 0, -4, 0], ![0, 4, 0, -1, 0, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P3 : CertificateIrreducibleZModOfList' 29 2 2 4 [5, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 28], [0, 1]]
 g := ![![[26, 6], [28], [16, 28], [15, 1]], ![[0, 23], [28], [1, 1], [1, 28]]]
 h' := ![![[15, 28], [25, 8], [7, 12], [12, 17], [0, 1]], ![[0, 1], [0, 21], [13, 17], [6, 12], [15, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [22, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N3 : CertifiedPrimeIdeal' SI29N3 29 where
  n := 2
  hpos := by decide
  P := [5, 14, 1]
  hirr := P29P3
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-127, 36, 250, -10, 154, 38]
  a := ![-1, 3, -1, 0, 1, 2]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-287, -24, 250, -10, 154, 38]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N3 : Ideal.IsPrime I29N3 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N3 B_one_repr
lemma NI29N3 : Nat.card (O ⧸ I29N3) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N3
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 1, 0, 0, 0]] ![![0, -1, 0, 0, 1, 0]]
  ![![-1, -3, 2, -1, 4, 0]] where
 M := ![![![-1, -3, 2, -1, 4, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-1, -3, 2, -1, 4, 0]] ![![0, -1, 0, 0, -1, 0]]
  ![![6, 0, 7, 0, -8, 0]] where
 M := ![![![6, 0, 7, 0, -8, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N2 : IdealMulLeCertificate' Table 
  ![![6, 0, 7, 0, -8, 0]] ![![4, 0, 1, 0, -3, 0]]
  ![![29, 0, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2, I29N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
    exact isPrimeI29N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1 ⊙ MulI29N2)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0, 0], ![0, 31, 0, 0, 0, 0], ![0, 0, 31, 0, 0, 0], ![0, 0, 0, 31, 0, 0], ![0, 0, 0, 0, 31, 0], ![0, 0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0, 0], ![0, 31, 0, 0, 0, 0], ![0, 0, 31, 0, 0, 0], ![0, 0, 0, 31, 0, 0], ![0, 0, 0, 0, 31, 0], ![0, 0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0, 0]], ![![0, 0, 0, 1, 0, 0]], ![![0, 0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 6 2 4 [24, 10, 15, 15, 13, 6, 1] where
 m := 2
 P := ![2, 3]
 exp := ![1, 1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 30, 19, 0, 21, 6], [21, 28, 25, 21, 19, 16], [11, 12, 29, 7, 7, 10], [11, 25, 20, 30, 25, 8], [19, 28, 0, 4, 21, 22], [0, 1]]
 g := ![![[8, 29, 17, 10, 11, 10], [0, 14, 28, 28, 3, 2], [25, 1], []], ![[30, 23, 16, 14, 12, 19, 27, 15], [0, 16, 2, 7, 26, 21, 25, 10, 2, 15], [28, 2, 12, 6, 8, 11, 4, 13, 22, 3], [15, 13, 29, 25, 10, 11, 21, 11, 11, 30]], ![[7, 8, 6, 19, 7, 13, 25, 4, 9, 8], [18, 10, 24, 15, 27, 22, 30, 10, 28, 8], [27, 17, 6, 16, 12, 19, 11, 22, 2, 5], [14, 30, 19, 29, 10, 28, 16, 29, 29, 4]], ![[26, 18, 7, 2, 22, 13, 8, 19, 3, 2], [21, 19, 18, 19, 0, 21, 9, 16, 11, 20], [11, 23, 0, 1, 24, 23, 0, 15, 9, 14], [4, 23, 2, 4, 8, 23, 9, 20, 6, 8]], ![[1, 23, 6, 6, 27, 30, 2, 9, 6, 10], [3, 22, 25, 30, 21, 30, 23, 19, 15, 10], [17, 7, 6, 30, 25, 26, 14, 13, 15, 28], [20, 4, 4, 17, 26, 15, 22, 16, 23, 16]], ![[13, 18, 5, 28, 27, 19, 9, 29, 20, 21], [23, 15, 16, 6, 22, 19, 8, 11, 0, 17], [27, 30, 18, 20, 22, 9, 26, 16, 7, 21], [10, 7, 6, 10, 27, 2, 21, 22, 22, 15]]]
 h' := ![![[25, 30, 19, 0, 21, 6], [0, 2, 8, 17, 28, 14], [20, 5, 18, 13, 1, 23], [0, 0, 0, 1], [0, 1]], ![[21, 28, 25, 21, 19, 16], [4, 2, 8, 2, 24], [19, 11, 18, 2, 13, 24], [13, 19, 22, 24, 30, 4], [25, 30, 19, 0, 21, 6]], ![[11, 12, 29, 7, 7, 10], [14, 6, 20, 1, 8, 4], [6, 25, 6, 22, 5, 4], [28, 7, 2, 20, 2, 14], [21, 28, 25, 21, 19, 16]], ![[11, 25, 20, 30, 25, 8], [21, 6, 25, 1, 14, 26], [11, 6, 26, 5, 11, 8], [26, 13, 30, 25, 29, 19], [11, 12, 29, 7, 7, 10]], ![[19, 28, 0, 4, 21, 22], [24, 16, 23, 15, 18, 3], [12, 24, 21, 16, 7, 28], [14, 6, 14, 24, 4, 9], [11, 25, 20, 30, 25, 8]], ![[0, 1], [6, 30, 9, 26, 1, 15], [0, 22, 4, 4, 25, 6], [16, 17, 25, 30, 28, 16], [19, 28, 0, 4, 21, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [14, 15, 12, 12, 21], [21, 12, 27, 9, 13], [], []]
 b := ![[], [], [18, 18, 22, 25, 18, 20], [5, 23, 26, 7, 26, 8], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 6
  hpos := by decide
  P := [24, 10, 15, 15, 13, 6, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5937741426, 1979151600, 8569857000, -2857912630, 10723471950, -3571290830]
  a := ![-5, 0, 0, 2, -10, 2]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-191540046, 63843600, 276447000, -92190730, 345918450, -115202930]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 887503681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀

instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0, 0], ![0, 37, 0, 0, 0, 0], ![0, 0, 37, 0, 0, 0], ![0, 0, 0, 37, 0, 0], ![0, 0, 0, 0, 37, 0], ![0, 0, 0, 0, 0, 37]] where
  M :=![![![37, 0, 0, 0, 0, 0], ![0, 37, 0, 0, 0, 0], ![0, 0, 37, 0, 0, 0], ![0, 0, 0, 37, 0, 0], ![0, 0, 0, 0, 37, 0], ![0, 0, 0, 0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0, 0]], ![![0, 0, 0, 1, 0, 0]], ![![0, 0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 6 2 5 [23, 2, 14, 28, 12, 34, 1] where
 m := 2
 P := ![2, 3]
 exp := ![1, 1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 16, 36, 12, 36, 10], [29, 23, 20, 12, 13], [24, 16, 25, 27, 14, 31], [14, 31, 31, 36, 29, 30], [29, 24, 36, 24, 19, 3], [0, 1]]
 g := ![![[33, 9, 34, 3, 2, 33], [11, 34, 33, 35, 3], [1, 34, 3, 1], [], []], ![[35, 35, 34, 6, 9, 35, 5, 0, 24, 34], [34, 31, 0, 8, 1], [33, 34, 1, 6, 30, 23, 1, 0, 13, 26], [10, 18, 17, 8, 26], [18, 25, 29, 21, 26]], ![[28, 31, 26, 28, 24, 25, 10, 8, 35], [19, 1, 21, 3, 9], [9, 26, 16, 36, 10, 34, 18, 3, 17], [25, 21, 10, 23, 7], [20, 5, 21]], ![[12, 21, 18, 29, 7, 31, 24, 25, 36, 35], [26, 20, 34, 1, 36], [12, 7, 6, 7, 31, 0, 33, 12, 15, 31], [25, 26, 5, 30, 3], [31, 20, 0, 14, 36]], ![[17, 10, 2, 20, 6, 29, 4, 5, 0, 4], [35, 8, 14, 10, 4], [13, 22, 28, 29, 22, 15, 23, 22, 23, 10], [15, 27, 17, 18, 11], [21, 10, 8, 0, 12]], ![[3, 16, 27, 13, 15, 19, 31, 34], [16, 5, 33, 20, 9], [26, 1, 18, 15, 19, 4, 9, 12, 6, 26], [30, 18, 1, 19, 28], [25, 16, 6, 30, 9]]]
 h' := ![![[18, 16, 36, 12, 36, 10], [17, 36, 20, 2, 21, 25], [14, 30, 34, 22, 28, 15], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[29, 23, 20, 12, 13], [16, 1, 6, 32, 16, 12], [13, 13, 13, 23, 16, 36], [26, 20, 21, 11, 28, 26], [21, 2, 28, 4, 15, 10], [18, 16, 36, 12, 36, 10]], ![[24, 16, 25, 27, 14, 31], [34, 29, 21, 5, 22, 16], [29, 36, 5, 32, 4, 34], [27, 23, 19, 1, 11, 28], [11, 32, 28, 19, 33, 9], [29, 23, 20, 12, 13]], ![[14, 31, 31, 36, 29, 30], [34, 6, 17, 9, 22, 32], [15, 0, 29, 32, 12, 31], [27, 28, 18, 18, 20, 1], [11, 24, 20, 34, 3, 22], [24, 16, 25, 27, 14, 31]], ![[29, 24, 36, 24, 19, 3], [20, 27, 10, 4, 36, 26], [14, 14, 15, 36, 19, 35], [32, 13, 9, 21, 35, 32], [9, 4, 36, 3, 14, 14], [14, 31, 31, 36, 29, 30]], ![[0, 1], [12, 12, 0, 22, 31], [26, 18, 15, 3, 32, 34], [25, 27, 7, 23, 16, 24], [7, 12, 35, 14, 9, 19], [29, 24, 36, 24, 19, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [17, 10, 15, 14], [34, 21, 22, 17, 22], [], []]
 b := ![[], [], [21, 26, 19, 20, 30, 16], [6, 18, 20, 23, 23, 16], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 6
  hpos := by decide
  P := [23, 2, 14, 28, 12, 34, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16991362, -4439408, 2489656, -2152660, -6192764, 2406998]
  a := ![13, -1, 1, 1, -4, -1]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![459226, -119984, 67288, -58180, -167372, 65054]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 2565726409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 0, 2, 0, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-4, 0, 2, 0, 1, 0]] 
 ![![41, 0, 0, 0, 0, 0], ![0, 41, 0, 0, 0, 0], ![14, 0, 1, 0, 0, 0], ![0, 14, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![0, 9, 0, 0, 0, 1]] where
  M :=![![![-4, 0, 2, 0, 1, 0], ![0, -4, 0, 2, 0, 1], ![-1, 0, -2, 0, 3, 0], ![0, -1, 0, -2, 0, 3], ![-3, 0, 5, 0, 1, 0], ![0, -3, 0, 5, 0, 1]]]
  hmulB := by decide  
  f := ![![![-17, 0, 3, 0, 8, 0]], ![![0, -17, 0, 3, 0, 8]], ![![-6, 0, 1, 0, 3, 0]], ![![0, -6, 0, 1, 0, 3]], ![![-4, 0, 1, 0, 2, 0]], ![![0, -4, 0, 1, 0, 2]]]
  g := ![![![-1, 0, 2, 0, 1, 0], ![0, -1, 0, 2, 0, 1], ![0, 0, -2, 0, 3, 0], ![0, 0, 0, -2, 0, 3], ![-2, 0, 5, 0, 1, 0], ![0, -2, 0, 5, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [32, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 40], [0, 1]]
 g := ![![[1, 9], [2], [32], [30, 40], [1]], ![[0, 32], [2], [32], [21, 1], [1]]]
 h' := ![![[9, 40], [27, 38], [3, 17], [24, 14], [9, 9], [0, 1]], ![[0, 1], [0, 3], [33, 24], [27, 27], [8, 32], [9, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [19, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [32, 32, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-63, 20, -14, 36, 115, 10]
  a := ![-3, 1, -1, 1, 3, 0]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-22, -14, -14, 36, 115, 10]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 0, -3, 0, 2, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-4, 0, -3, 0, 2, 0]] 
 ![![41, 0, 0, 0, 0, 0], ![0, 41, 0, 0, 0, 0], ![30, 0, 1, 0, 0, 0], ![0, 30, 0, 1, 0, 0], ![2, 0, 0, 0, 1, 0], ![0, 2, 0, 0, 0, 1]] where
  M :=![![![-4, 0, -3, 0, 2, 0], ![0, -4, 0, -3, 0, 2], ![-2, 0, 0, 0, -1, 0], ![0, -2, 0, 0, 0, -1], ![1, 0, -4, 0, -1, 0], ![0, 1, 0, -4, 0, -1]]]
  hmulB := by decide  
  f := ![![![-4, 0, -11, 0, 3, 0]], ![![0, -4, 0, -11, 0, 3]], ![![-3, 0, -8, 0, 2, 0]], ![![0, -3, 0, -8, 0, 2]], ![![0, 0, -1, 0, 0, 0]], ![![0, 0, 0, -1, 0, 0]]]
  g := ![![![2, 0, -3, 0, 2, 0], ![0, 2, 0, -3, 0, 2], ![0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, -1], ![3, 0, -4, 0, -1, 0], ![0, 3, 0, -4, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [39, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 40], [0, 1]]
 g := ![![[5, 20], [9], [20], [15, 18], [1]], ![[0, 21], [9], [20], [31, 23], [1]]]
 h' := ![![[10, 40], [27, 26], [38, 38], [30, 26], [2, 10], [0, 1]], ![[0, 1], [0, 15], [8, 3], [3, 15], [20, 31], [10, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [13, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [39, 31, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![254, -180, 186, 47, 43, -57]
  a := ![7, -4, 0, 1, 1, -1]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-132, -36, 186, 47, 43, -57]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, -1, 0, 0, -1]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-1, 2, -1, 0, 0, -1]] 
 ![![41, 0, 0, 0, 0, 0], ![15, 1, 0, 0, 0, 0], ![37, 0, 1, 0, 0, 0], ![19, 0, 0, 1, 0, 0], ![25, 0, 0, 0, 1, 0], ![35, 0, 0, 0, 0, 1]] where
  M :=![![![-1, 2, -1, 0, 0, -1], ![5, -1, 0, -1, -5, 0], ![0, 1, -1, 0, -1, -1], ![5, 0, -5, -1, -5, -1], ![1, 1, -2, -1, -2, -1], ![5, 1, -5, -2, -10, -2]]]
  hmulB := by decide  
  f := ![![![10, 13, 3, 8, 1, -11]], ![![5, 5, 0, 3, 0, -4]], ![![9, 12, 3, 7, 1, -10]], ![![5, 6, 2, 4, -1, -5]], ![![6, 8, 2, 5, 1, -7]], ![![10, 11, 0, 7, 0, -9]]]
  g := ![![![1, 2, -1, 0, 0, -1], ![4, -1, 0, -1, -5, 0], ![2, 1, -1, 0, -1, -1], ![9, 0, -5, -1, -5, -1], ![4, 1, -2, -1, -2, -1], ![13, 1, -5, -2, -10, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2

def I41N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 2, 1, 0, 0, -1]] i)))

def SI41N3: IdealEqSpanCertificate' Table ![![1, 2, 1, 0, 0, -1]] 
 ![![41, 0, 0, 0, 0, 0], ![26, 1, 0, 0, 0, 0], ![37, 0, 1, 0, 0, 0], ![22, 0, 0, 1, 0, 0], ![25, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] where
  M :=![![![1, 2, 1, 0, 0, -1], ![5, 1, 0, 1, -5, 0], ![0, 1, 1, 0, 1, -1], ![5, 0, -5, 1, -5, 1], ![-1, 1, 2, -1, 2, -1], ![5, -1, -5, 2, -10, 2]]]
  hmulB := by decide  
  f := ![![![-10, 13, -3, 8, -1, -11]], ![![-5, 8, -3, 5, -1, -7]], ![![-9, 12, -3, 7, -1, -10]], ![![-5, 7, -1, 4, -2, -6]], ![![-6, 8, -2, 5, -1, -7]], ![![0, 2, -3, 1, -1, -2]]]
  g := ![![![-2, 2, 1, 0, 0, -1], ![2, 1, 0, 1, -5, 0], ![-2, 1, 1, 0, 1, -1], ![7, 0, -5, 1, -5, 1], ![-3, 1, 2, -1, 2, -1], ![10, -1, -5, 2, -10, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N3 : Nat.card (O ⧸ I41N3) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N3)

lemma isPrimeI41N3 : Ideal.IsPrime I41N3 := prime_ideal_of_norm_prime hp41.out _ NI41N3
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-4, 0, 2, 0, 1, 0]] ![![-4, 0, -3, 0, 2, 0]]
  ![![13, 0, 8, 0, -11, 0]] where
 M := ![![![13, 0, 8, 0, -11, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 8, 0, -11, 0]] ![![-1, 2, -1, 0, 0, -1]]
  ![![-24, 23, 1, 11, 14, -10]] where
 M := ![![![-24, 23, 1, 11, 14, -10]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N2 : IdealMulLeCertificate' Table 
  ![![-24, 23, 1, 11, 14, -10]] ![![1, 2, 1, 0, 0, -1]]
  ![![41, 0, 0, 0, 0, 0]] where
 M := ![![![82, 0, 0, 0, -41, 0]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, -1, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2, I41N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
    exact isPrimeI41N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1 ⊙ MulI41N2)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 0, -3, 0, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-2, 0, -3, 0, 1, 0]] 
 ![![43, 0, 0, 0, 0, 0], ![0, 43, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![0, 8, 0, 1, 0, 0], ![22, 0, 0, 0, 1, 0], ![0, 22, 0, 0, 0, 1]] where
  M :=![![![-2, 0, -3, 0, 1, 0], ![0, -2, 0, -3, 0, 1], ![-1, 0, 0, 0, -2, 0], ![0, -1, 0, 0, 0, -2], ![2, 0, -5, 0, -2, 0], ![0, 2, 0, -5, 0, -2]]]
  hmulB := by decide  
  f := ![![![-10, 0, -11, 0, 6, 0]], ![![0, -10, 0, -11, 0, 6]], ![![-2, 0, -2, 0, 1, 0]], ![![0, -2, 0, -2, 0, 1]], ![![-5, 0, -6, 0, 3, 0]], ![![0, -5, 0, -6, 0, 3]]]
  g := ![![![0, 0, -3, 0, 1, 0], ![0, 0, 0, -3, 0, 1], ![1, 0, 0, 0, -2, 0], ![0, 1, 0, 0, 0, -2], ![2, 0, -5, 0, -2, 0], ![0, 2, 0, -5, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [27, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 42], [0, 1]]
 g := ![![[4, 35], [0, 4], [4], [0, 11], [1]], ![[8, 8], [41, 39], [4], [16, 32], [1]]]
 h' := ![![[21, 42], [0, 32], [21, 41], [0, 2], [16, 21], [0, 1]], ![[0, 1], [27, 11], [22, 2], [42, 41], [27, 22], [21, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [2, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [27, 22, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-32, 54, 195, 38, 41, 16]
  a := ![-1, 3, 4, 0, -1, 1]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-58, -14, 195, 38, 41, 16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0, 0], ![21, 1, 0, 0, 0, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0, 0], ![21, 1, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0, 0], ![21, 1, 0, 0, 0, 0], ![15, 0, 1, 0, 0, 0], ![29, 0, 0, 1, 0, 0], ![33, 0, 0, 0, 1, 0], ![38, 0, 0, 0, 0, 1]] where
  M :=![![![43, 0, 0, 0, 0, 0], ![0, 43, 0, 0, 0, 0], ![0, 0, 43, 0, 0, 0], ![0, 0, 0, 43, 0, 0], ![0, 0, 0, 0, 43, 0], ![0, 0, 0, 0, 0, 43]], ![![21, 1, 0, 0, 0, 0], ![0, 21, 5, 0, 0, 0], ![0, 0, 21, 1, 0, 0], ![0, 0, 0, 21, 5, 0], ![0, 0, 0, 0, 21, 1], ![-5, 0, 10, 0, 5, 21]]]
  hmulB := by decide  
  f := ![![![190, -894, 19588, 3526, 26445, 1230], ![-387, 1849, -40549, -5289, -52890, 0]], ![![84, -479, 10217, 2214, 13325, 615], ![-171, 989, -21156, -3526, -26445, 0]], ![![36, -326, 6810, 2050, 9881, 451], ![-73, 671, -14104, -3526, -19393, 0]], ![![134, -609, 13209, 2358, 18491, 861], ![-273, 1260, -27347, -3526, -37023, 0]], ![![138, -685, 15033, 2706, 20275, 943], ![-281, 1416, -31119, -4059, -40549, 0]], ![![164, -800, 17308, 3116, 23370, 1087], ![-334, 1654, -35834, -4674, -46740, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-21, 43, 0, 0, 0, 0], ![-15, 0, 43, 0, 0, 0], ![-29, 0, 0, 43, 0, 0], ![-33, 0, 0, 0, 43, 0], ![-38, 0, 0, 0, 0, 43]], ![![0, 1, 0, 0, 0, 0], ![-12, 21, 5, 0, 0, 0], ![-8, 0, 21, 1, 0, 0], ![-18, 0, 0, 21, 5, 0], ![-17, 0, 0, 0, 21, 1], ![-26, 0, 10, 0, 5, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0, 0], ![-21, 1, 0, 0, 0, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0, 0], ![-21, 1, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0, 0], ![22, 1, 0, 0, 0, 0], ![15, 0, 1, 0, 0, 0], ![14, 0, 0, 1, 0, 0], ![33, 0, 0, 0, 1, 0], ![5, 0, 0, 0, 0, 1]] where
  M :=![![![43, 0, 0, 0, 0, 0], ![0, 43, 0, 0, 0, 0], ![0, 0, 43, 0, 0, 0], ![0, 0, 0, 43, 0, 0], ![0, 0, 0, 0, 43, 0], ![0, 0, 0, 0, 0, 43]], ![![-21, 1, 0, 0, 0, 0], ![0, -21, 5, 0, 0, 0], ![0, 0, -21, 1, 0, 0], ![0, 0, 0, -21, 5, 0], ![0, 0, 0, 0, -21, 1], ![-5, 0, 10, 0, 5, -21]]]
  hmulB := by decide  
  f := ![![![2668, -862, -18830, 2270, 25505, -1230], ![5461, -1505, -38915, 2795, 52890, 0]], ![![1408, -340, -9847, 1207, 13601, -656], ![2882, -559, -20296, 1505, 28208, 0]], ![![960, -264, -6542, 818, 9351, -451], ![1965, -447, -13502, 1032, 19393, 0]], ![![896, -238, -6106, 755, 8500, -410], ![1834, -400, -12598, 946, 17630, 0]], ![![2112, -669, -14445, 1736, 19555, -943], ![4323, -1164, -29855, 2133, 40549, 0]], ![![320, -67, -2179, 266, 2965, -143], ![655, -106, -4487, 331, 6150, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-22, 43, 0, 0, 0, 0], ![-15, 0, 43, 0, 0, 0], ![-14, 0, 0, 43, 0, 0], ![-33, 0, 0, 0, 43, 0], ![-5, 0, 0, 0, 0, 43]], ![![-1, 1, 0, 0, 0, 0], ![9, -21, 5, 0, 0, 0], ![7, 0, -21, 1, 0, 0], ![3, 0, 0, -21, 5, 0], ![16, 0, 0, 0, -21, 1], ![-5, 0, 10, 0, 5, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2

def I43N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 2, 0, -3, 0]] i)))

def SI43N3: IdealEqSpanCertificate' Table ![![3, 0, 2, 0, -3, 0]] 
 ![![43, 0, 0, 0, 0, 0], ![0, 43, 0, 0, 0, 0], ![19, 0, 1, 0, 0, 0], ![0, 19, 0, 1, 0, 0], ![26, 0, 0, 0, 1, 0], ![0, 26, 0, 0, 0, 1]] where
  M :=![![![3, 0, 2, 0, -3, 0], ![0, 3, 0, 2, 0, -3], ![3, 0, -3, 0, -1, 0], ![0, 3, 0, -3, 0, -1], ![1, 0, 1, 0, -4, 0], ![0, 1, 0, 1, 0, -4]]]
  hmulB := by decide  
  f := ![![![13, 0, 5, 0, -11, 0]], ![![0, 13, 0, 5, 0, -11]], ![![6, 0, 2, 0, -5, 0]], ![![0, 6, 0, 2, 0, -5]], ![![8, 0, 3, 0, -7, 0]], ![![0, 8, 0, 3, 0, -7]]]
  g := ![![![1, 0, 2, 0, -3, 0], ![0, 1, 0, 2, 0, -3], ![2, 0, -3, 0, -1, 0], ![0, 2, 0, -3, 0, -1], ![2, 0, 1, 0, -4, 0], ![0, 2, 0, 1, 0, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P3 : CertificateIrreducibleZModOfList' 43 2 2 5 [3, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 42], [0, 1]]
 g := ![![[11, 31], [16, 13], [6], [37, 14], [1]], ![[20, 12], [17, 30], [6], [5, 29], [1]]]
 h' := ![![[10, 42], [38, 17], [5, 23], [18, 36], [40, 10], [0, 1]], ![[0, 1], [36, 26], [20, 20], [34, 7], [11, 33], [10, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [5, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N3 : CertifiedPrimeIdeal' SI43N3 43 where
  n := 2
  hpos := by decide
  P := [3, 33, 1]
  hirr := P43P3
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2957, 227, 6476, -789, 719, -63]
  a := ![0, 7, 2, -25, 0, 1]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3365, 392, 6476, -789, 719, -63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N3 : Ideal.IsPrime I43N3 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N3 B_one_repr
lemma NI43N3 : Nat.card (O ⧸ I43N3) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N3
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-2, 0, -3, 0, 1, 0]] ![![43, 0, 0, 0, 0, 0], ![21, 1, 0, 0, 0, 0]]
  ![![43, 0, 0, 0, 0, 0], ![-20, -3, 19, 5, 0, 0]] where
 M := ![![![-86, 0, -129, 0, 43, 0], ![-42, -2, -63, -3, 21, 1]]]
 hmul := by decide  
 g := ![![![![-7442, 224, 1910, -337, 4178, 1540], ![-15996, 2881, -13244, 0, 0, 0]], ![![-3894, 256, 459, -405, 2625, 967], ![-8370, 1806, -8316, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0, 0, 0, 0], ![-20, -3, 19, 5, 0, 0]] ![![43, 0, 0, 0, 0, 0], ![-21, 1, 0, 0, 0, 0]]
  ![![13, 0, 5, 0, -11, 0]] where
 M := ![![![1849, 0, 0, 0, 0, 0], ![-903, 43, 0, 0, 0, 0]], ![![-860, -129, 817, 215, 0, 0], ![420, 43, -414, -86, 25, 0]]]
 hmul := by decide  
 g := ![![![![129, 0, 86, 0, -129, 0]], ![![-63, 3, -42, 2, 63, -3]]], ![![![-3, 6, -97, -21, 41, 4]], ![![1, -3, 49, 8, -22, -1]]]]
 hle2 := by decide  

def MulI43N2 : IdealMulLeCertificate' Table 
  ![![13, 0, 5, 0, -11, 0]] ![![3, 0, 2, 0, -3, 0]]
  ![![43, 0, 0, 0, 0, 0]] where
 M := ![![![43, 0, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2, I43N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
    exact isPrimeI43N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1 ⊙ MulI43N2)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0, 0], ![4, -19, 16, 5, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0, 0], ![4, -19, 16, 5, 0, 0]] 
 ![![47, 0, 0, 0, 0, 0], ![0, 47, 0, 0, 0, 0], ![0, 0, 47, 0, 0, 0], ![29, 15, 22, 1, 0, 0], ![4, 15, 31, 0, 1, 0], ![41, 9, 4, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0, 0], ![0, 47, 0, 0, 0, 0], ![0, 0, 47, 0, 0, 0], ![0, 0, 0, 47, 0, 0], ![0, 0, 0, 0, 47, 0], ![0, 0, 0, 0, 0, 47]], ![![4, -19, 16, 5, 0, 0], ![0, 4, -95, 16, 25, 0], ![0, 0, 4, -19, 16, 5], ![-25, 0, 50, 4, -70, 16], ![-16, -5, 32, 10, 20, -14], ![70, -16, -165, 32, -20, 20]]]
  hmulB := by decide  
  f := ![![![685, -3505, 8848, -321, -1472, 40], ![-8037, 3008, -376, 0, 0, 0]], ![![-24, 235, -2954, 488, 718, -10], ![282, -1410, 94, 0, 0, 0]], ![![-12, 49, 139, -28, -66, -5], ![141, 94, 47, 0, 0, 0]], ![![415, -2088, 4524, -38, -686, 20], ![-4869, 1410, -188, 0, 0, 0]], ![![44, -195, -139, 108, 83, 0], ![-516, -156, 0, 0, 0, 0]], ![![595, -3026, 7250, -199, -1170, 33], ![-6981, 2398, -310, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![-29, -15, -22, 47, 0, 0], ![-4, -15, -31, 0, 47, 0], ![-41, -9, -4, 0, 0, 47]], ![![-3, -2, -2, 5, 0, 0], ![-12, -13, -26, 16, 25, 0], ![6, 0, -2, -19, 16, 5], ![-11, 18, 44, 4, -70, 16], ![4, -7, -16, 10, 20, -14], ![-34, -8, -7, 32, -20, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [21, 25, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 24, 29], [10, 22, 18], [0, 1]]
 g := ![![[29, 8, 14], [8, 37, 6], [28, 14, 18], [25, 12, 1], []], ![[29, 10, 15, 10], [5, 21, 40, 11], [13, 29, 25, 22], [37, 35, 8, 30], [16, 42]], ![[46, 17, 46, 2], [7, 3, 13, 21], [27, 40, 46, 12], [9, 2, 46, 28], [27, 42]]]
 h' := ![![[2, 24, 29], [20, 22, 22], [23, 10, 10], [39, 16, 26], [0, 0, 1], [0, 1]], ![[10, 22, 18], [45, 4, 41], [13, 36, 40], [40, 4, 2], [44, 36, 22], [2, 24, 29]], ![[0, 1], [24, 21, 31], [12, 1, 44], [42, 27, 19], [3, 11, 24], [10, 22, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 22], []]
 b := ![[], [28, 18, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [21, 25, 35, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3085, -1034, 11042, 814, -5506, 2227]
  a := ![1, 3, -6, -1, -1, 3]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2042, 1049, 3296, 814, -5506, 2227]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0, 0], ![-4, -19, -16, 5, 0, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0, 0], ![-4, -19, -16, 5, 0, 0]] 
 ![![47, 0, 0, 0, 0, 0], ![0, 47, 0, 0, 0, 0], ![0, 0, 47, 0, 0, 0], ![18, 15, 25, 1, 0, 0], ![4, 32, 31, 0, 1, 0], ![6, 9, 43, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0, 0], ![0, 47, 0, 0, 0, 0], ![0, 0, 47, 0, 0, 0], ![0, 0, 0, 47, 0, 0], ![0, 0, 0, 0, 47, 0], ![0, 0, 0, 0, 0, 47]], ![![-4, -19, -16, 5, 0, 0], ![0, -4, -95, -16, 25, 0], ![0, 0, -4, -19, -16, 5], ![-25, 0, 50, -4, -70, -16], ![16, -5, -32, 10, -20, -14], ![70, 16, -165, -32, -20, -20]]]
  hmulB := by decide  
  f := ![![![-1935, -9236, -6726, 11608, 8122, -2460], ![-22748, -470, 23124, 0, 0, 0]], ![![96, 481, 962, 14, -118, -10], ![1128, 282, 94, 0, 0, 0]], ![![0, 8, 191, 32, -50, 0], ![0, 94, 0, 0, 0, 0]], ![![-722, -3447, -2357, 5171, 3748, -1140], ![-8488, -188, 10716, 0, 0, 0]], ![![-172, -966, -4245, -439, 885, 15], ![-2022, -1754, -141, 0, 0, 0]], ![![-230, -1097, -699, 1780, 1296, -397], ![-2704, -48, 3732, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![-18, -15, -25, 47, 0, 0], ![-4, -32, -31, 0, 47, 0], ![-6, -9, -43, 0, 0, 47]], ![![-2, -2, -3, 5, 0, 0], ![4, -12, -10, -16, 25, 0], ![8, 16, 16, -19, -16, 5], ![9, 52, 64, -4, -70, -16], ![0, 13, 20, 10, -20, -14], ![18, 28, 45, -32, -20, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 3 2 5 [6, 14, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 31, 35], [38, 15, 12], [0, 1]]
 g := ![![[5, 27, 3], [37, 23, 21], [16], [3, 8, 1], []], ![[42, 24, 16, 45], [30, 18, 6, 10], [9, 28, 44, 35], [25, 23, 0, 26], [32, 3]], ![[20, 34, 13, 28], [38, 25, 15, 12], [16, 5, 0, 12], [44, 43, 32, 17], [8, 3]]]
 h' := ![![[17, 31, 35], [13, 6, 12], [45, 6, 31], [29, 4], [0, 0, 1], [0, 1]], ![[38, 15, 12], [10, 4, 14], [5, 37, 17], [3, 30, 46], [3, 24, 15], [17, 31, 35]], ![[0, 1], [26, 37, 21], [27, 4, 46], [40, 13, 1], [33, 23, 31], [38, 15, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 10], []]
 b := ![[], [12, 5, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 3
  hpos := by decide
  P := [6, 14, 39, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12248, -3717, 19271, 6272, 22253, 7140]
  a := ![0, 1, 5, 1, 3, 2]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5468, -18599, -24136, 6272, 22253, 7140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0, 0, 0, 0], ![4, -19, 16, 5, 0, 0]] ![![47, 0, 0, 0, 0, 0], ![-4, -19, -16, 5, 0, 0]]
  ![![47, 0, 0, 0, 0, 0]] where
 M := ![![![2209, 0, 0, 0, 0, 0], ![-188, -893, -752, 235, 0, 0]], ![![188, -893, 752, 235, 0, 0], ![-141, 0, 1927, 0, -1081, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0, 0, 0, 0]], ![![-4, -19, -16, 5, 0, 0]]], ![![![4, -19, 16, 5, 0, 0]], ![![-3, 0, 41, 0, -23, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0, 0], ![0, 53, 0, 0, 0, 0], ![0, 0, 53, 0, 0, 0], ![0, 0, 0, 53, 0, 0], ![0, 0, 0, 0, 53, 0], ![0, 0, 0, 0, 0, 53]] where
  M :=![![![53, 0, 0, 0, 0, 0], ![0, 53, 0, 0, 0, 0], ![0, 0, 53, 0, 0, 0], ![0, 0, 0, 53, 0, 0], ![0, 0, 0, 0, 53, 0], ![0, 0, 0, 0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0, 0]], ![![0, 0, 0, 1, 0, 0]], ![![0, 0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 6 2 5 [21, 26, 34, 18, 12, 3, 1] where
 m := 2
 P := ![2, 3]
 exp := ![1, 1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 52, 1, 11, 26, 49], [1, 39, 24, 7, 4, 2], [49, 14, 26, 35, 1, 11], [50, 3, 43, 15, 44, 14], [19, 50, 12, 38, 31, 30], [0, 1]]
 g := ![![[26, 3, 26, 1, 39, 11], [30, 25, 8, 19, 17], [5, 33, 13, 9, 45, 9], [1], []], ![[37, 11, 20, 25, 11, 30, 41, 37, 37, 16], [26, 18, 22, 47, 9], [29, 26, 32, 17, 34, 0, 13, 10, 41, 24], [35, 48, 16, 36, 13], [41, 37, 30, 11, 30, 1, 3, 47, 9, 42]], ![[52, 43, 21, 27, 10, 17, 4, 36, 24, 3], [39, 22, 18, 24, 43], [33, 6, 22, 2, 8, 32, 26, 17, 33, 14], [41, 50, 30, 37, 36], [12, 10, 30, 43, 11, 0, 8, 12, 24, 8]], ![[30, 51, 47, 52, 37, 35, 43, 20, 47, 29], [7, 3, 4], [3, 42, 20, 13, 3, 48, 4, 39, 24, 47], [46, 27, 23, 13, 49], [6, 13, 16, 50, 29, 1, 9, 24, 27, 6]], ![[2, 28, 40, 16, 26, 0, 52, 36, 33, 3], [18, 2, 39, 5, 38], [14, 0, 0, 28, 19, 46, 49, 44, 30, 14], [43, 40, 21, 6, 1], [16, 45, 29, 46, 9, 48, 51, 44, 44, 41]], ![[16, 48, 28, 21, 37, 28, 11, 31, 3, 18], [17, 44, 39, 29, 24], [21, 11, 47, 43, 44, 52, 46, 50, 46, 21], [23, 44, 40, 43, 13], [51, 51, 24, 17, 43, 40, 50, 37, 50, 23]]]
 h' := ![![[37, 52, 1, 11, 26, 49], [7, 51, 38, 45, 31, 8], [1, 42, 3, 47, 37, 21], [32, 27, 19, 35, 41, 50], [0, 0, 0, 1], [0, 1]], ![[1, 39, 24, 7, 4, 2], [8, 38, 10, 26, 10, 46], [36, 24, 35, 10, 30, 3], [49, 32, 33, 52, 45, 10], [25, 39, 13, 24, 24, 38], [37, 52, 1, 11, 26, 49]], ![[49, 14, 26, 35, 1, 11], [44, 20, 9, 5, 39, 44], [42, 38, 22, 50, 42, 34], [24, 6, 2, 37, 18, 22], [14, 19, 51, 18, 10, 47], [1, 39, 24, 7, 4, 2]], ![[50, 3, 43, 15, 44, 14], [28, 27, 41, 7, 44, 29], [49, 19, 43, 36, 51], [48, 25, 44, 33, 21, 41], [22, 31, 32, 32, 19, 7], [49, 14, 26, 35, 1, 11]], ![[19, 50, 12, 38, 31, 30], [42, 17, 10, 32, 27, 51], [46, 4, 27, 15, 16, 12], [9, 34, 23, 35, 1, 1], [8, 45, 29, 31, 22, 52], [50, 3, 43, 15, 44, 14]], ![[0, 1], [27, 6, 51, 44, 8, 34], [38, 32, 29, 1, 36, 36], [9, 35, 38, 20, 33, 35], [11, 25, 34, 0, 31, 15], [19, 50, 12, 38, 31, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [36, 22, 10, 3, 27], [0, 50, 51, 21, 28], [], []]
 b := ![[], [], [40, 50, 10, 25, 38, 13], [13, 0, 28, 38, 45, 36], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 6
  hpos := by decide
  P := [21, 26, 34, 18, 12, 3, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14937785, 886054, 27872170, -5506541, 32038712, -5000444]
  a := ![-5, 4, -8, 0, -1, -1]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-281845, 16718, 525890, -103897, 604504, -94348]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 22164361129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0, 0], ![0, 59, 0, 0, 0, 0], ![0, 0, 59, 0, 0, 0], ![0, 0, 0, 59, 0, 0], ![0, 0, 0, 0, 59, 0], ![0, 0, 0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0, 0, 0], ![0, 59, 0, 0, 0, 0], ![0, 0, 59, 0, 0, 0], ![0, 0, 0, 59, 0, 0], ![0, 0, 0, 0, 59, 0], ![0, 0, 0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0, 0]], ![![0, 0, 0, 1, 0, 0]], ![![0, 0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 6 2 5 [7, 41, 43, 4, 30, 5, 1] where
 m := 2
 P := ![2, 3]
 exp := ![1, 1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 22, 38, 43, 25, 35], [9, 22, 36, 53, 11, 7], [14, 27, 28, 44, 5, 6], [48, 19, 10, 56, 22, 33], [44, 27, 6, 40, 55, 37], [0, 1]]
 g := ![![[34, 12, 45, 10, 29, 12], [33, 9, 0, 22, 50, 26], [14, 55, 47, 8, 25], [54, 1], []], ![[11, 26, 5, 17, 19, 18, 32, 7, 51, 3], [44, 47, 55, 47, 17, 24, 2, 3], [44, 52, 32, 56, 15], [2, 55, 38, 46, 23, 1, 55, 23, 45, 9], [0, 10, 15, 55, 57, 3, 28, 11, 43, 41]], ![[33, 10, 51, 38, 50, 16, 10, 41, 51, 21], [43, 55, 18, 35, 34, 16, 49, 45, 9, 20], [39, 43, 45, 17, 26], [19, 20, 20, 55, 30, 46, 14, 21, 11, 46], [24, 32, 26, 21, 55, 56, 45, 1, 20, 48]], ![[52, 45, 48, 16, 21, 26, 13, 2, 8, 11], [56, 37, 26, 32, 53, 10, 43, 53, 24, 10], [39, 26, 14, 55, 12], [39, 50, 22, 16, 38, 46, 6, 21, 51, 23], [5, 1, 41, 42, 36, 23, 2, 6, 50, 39]], ![[36, 15, 52, 57, 49, 14, 39, 0, 33, 38], [12, 22, 13, 18, 5, 16, 50, 13, 8, 32], [8, 42, 0, 39, 51], [34, 13, 12, 6, 52, 51, 18, 23, 27, 32], [7, 17, 57, 28, 20, 45, 0, 29, 41, 6]], ![[40, 29, 40, 38, 9, 5, 19, 46, 7, 33], [26, 15, 28, 34, 39, 39, 24, 57, 38, 56], [58, 55, 48, 10, 17], [0, 16, 11, 53, 17, 44, 53, 5, 29, 34], [37, 1, 12, 17, 40, 45, 3, 5, 55, 31]]]
 h' := ![![[57, 22, 38, 43, 25, 35], [5, 36, 37, 21, 57, 22], [6, 39, 54, 55, 22, 47], [35, 21, 56, 36, 28, 54], [0, 0, 0, 1], [0, 1]], ![[9, 22, 36, 53, 11, 7], [4, 29, 48, 31, 41, 9], [32, 7, 5, 3, 50], [35, 10, 45, 3, 13, 30], [51, 17, 46, 56, 25, 19], [57, 22, 38, 43, 25, 35]], ![[14, 27, 28, 44, 5, 6], [1, 40, 23, 33, 28, 11], [26, 44, 57, 35, 31, 35], [2, 14, 19, 42, 43, 12], [30, 8, 56, 8, 6, 29], [9, 22, 36, 53, 11, 7]], ![[48, 19, 10, 56, 22, 33], [32, 1, 19, 19, 26, 13], [51, 10, 15, 10, 36, 49], [18, 35, 24, 14, 47, 37], [54, 29, 47, 54, 16, 17], [14, 27, 28, 44, 5, 6]], ![[44, 27, 6, 40, 55, 37], [55, 47, 41, 25, 58, 42], [49, 57, 3, 57, 57, 12], [20, 45, 7, 6, 34, 13], [36, 1, 55, 27, 39, 47], [48, 19, 10, 56, 22, 33]], ![[0, 1], [1, 24, 9, 48, 26, 21], [34, 20, 43, 17, 40, 34], [33, 52, 26, 17, 12, 31], [24, 4, 32, 31, 32, 6], [44, 27, 6, 40, 55, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [57, 9, 9, 33, 37], [19, 47, 58, 55, 2], [], []]
 b := ![[], [], [41, 31, 53, 38, 47, 20], [58, 7, 0, 55, 55, 39], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 6
  hpos := by decide
  P := [7, 41, 43, 4, 30, 5, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2379730957, -792766303, 3465746966, 1168730292, 4304863197, 1425042517]
  a := ![-6, -2, -19, -1, 1, -1]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-40334423, -13436717, 58741474, 19808988, 72963783, 24153263]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 42180533641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -6, -6, -1, 0, 3]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![3, -6, -6, -1, 0, 3]] 
 ![![61, 0, 0, 0, 0, 0], ![0, 61, 0, 0, 0, 0], ![0, 0, 61, 0, 0, 0], ![19, 24, 60, 1, 0, 0], ![16, 33, 36, 0, 1, 0], ![48, 6, 18, 0, 0, 1]] where
  M :=![![![3, -6, -6, -1, 0, 3], ![-15, 3, 0, -6, 10, 0], ![0, -3, 3, 0, -6, 2], ![-10, 0, 5, 3, 10, -6], ![6, -2, -12, 1, -3, 2], ![-10, 6, 10, -12, 15, -3]]]
  hmulB := by decide  
  f := ![![![3, -4, -6, -2, -3, 1]], ![![-5, 3, -10, -6, -5, -3]], ![![3, -1, -3, -2, -9, -1]], ![![2, -1, -9, -5, -12, -2]], ![![0, 0, -9, -5, -9, -2]], ![![3, -3, -7, -3, -6, 0]]]
  g := ![![![-2, 0, 0, -1, 0, 3], ![-1, -3, 0, -6, 10, 0], ![0, 3, 3, 0, -6, 2], ![1, -6, -7, 3, 10, -6], ![-1, 1, 0, 1, -3, 2], ![2, -3, 4, -12, 15, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [28, 5, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 44, 24], [29, 16, 37], [0, 1]]
 g := ![![[39, 21, 9], [21, 25], [5, 2, 19], [28, 8, 5], [1]], ![[9, 32, 57, 6], [58, 56], [36, 55, 45, 54], [1, 20, 0, 30], [5, 0, 14, 38]], ![[45, 9, 18, 11], [45, 27], [15, 36, 58, 54], [48, 53, 52, 31], [19, 58, 27, 23]]]
 h' := ![![[6, 44, 24], [41, 49, 58], [43, 0, 56], [9, 54, 43], [33, 56, 35], [0, 1]], ![[29, 16, 37], [22, 17, 30], [50, 34, 42], [41, 34, 32], [15, 30, 13], [6, 44, 24]], ![[0, 1], [21, 56, 34], [0, 27, 24], [5, 34, 47], [6, 36, 13], [29, 16, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 12], []]
 b := ![[], [38, 23, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [28, 5, 26, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26995, 32515, 51454, -53656, 26775, -41696]
  a := ![-3, -4, -1, 1, 1, -8]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![42057, 11260, 50122, -53656, 26775, -41696]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 6, -6, 1, 0, -3]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![3, 6, -6, 1, 0, -3]] 
 ![![61, 0, 0, 0, 0, 0], ![0, 61, 0, 0, 0, 0], ![0, 0, 61, 0, 0, 0], ![42, 24, 1, 1, 0, 0], ![16, 28, 36, 0, 1, 0], ![13, 6, 43, 0, 0, 1]] where
  M :=![![![3, 6, -6, 1, 0, -3], ![15, 3, 0, -6, -10, 0], ![0, 3, 3, 0, -6, -2], ![10, 0, -5, 3, -10, -6], ![6, 2, -12, -1, -3, -2], ![10, 6, -10, -12, -15, -3]]]
  hmulB := by decide  
  f := ![![![3, 4, -6, 2, -3, -1]], ![![5, 3, 10, -6, 5, -3]], ![![3, 1, -3, 2, -9, 1]], ![![4, 4, 0, -1, 0, -2]], ![![5, 3, 1, -1, -4, -1]], ![![3, 2, -2, 1, -6, 0]]]
  g := ![![![0, 0, 2, 1, 0, -3], ![7, 7, 6, -6, -10, 0], ![2, 3, 5, 0, -6, -2], ![2, 4, 10, 3, -10, -6], ![2, 2, 3, -1, -3, -2], ![13, 12, 11, -12, -15, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 3 2 5 [44, 5, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 56, 58], [55, 4, 3], [0, 1]]
 g := ![![[56, 37, 47], [40, 48], [47, 19, 15], [4, 18, 46], [1]], ![[50, 25], [48, 39], [14, 43, 51, 47], [3, 46, 3, 48], [40, 57, 4, 34]], ![[47, 11, 27, 19], [50, 57], [35, 20, 56, 41], [30, 54, 42, 19], [55, 45, 30, 27]]]
 h' := ![![[37, 56, 58], [45, 3, 48], [6, 15, 29], [7, 26, 36], [17, 56, 31], [0, 1]], ![[55, 4, 3], [19, 16], [22, 6, 10], [58, 0, 5], [32, 59, 17], [37, 56, 58]], ![[0, 1], [1, 42, 13], [35, 40, 22], [45, 35, 20], [48, 7, 13], [55, 4, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 42], []]
 b := ![[], [41, 33, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 3
  hpos := by decide
  P := [44, 5, 30, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22507, 7210, 38687, -12627, 46061, -15276]
  a := ![0, -5, 1, -4, 5, -1]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-501, -14554, -15574, -12627, 46061, -15276]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![3, -6, -6, -1, 0, 3]] ![![3, 6, -6, 1, 0, -3]]
  ![![61, 0, 0, 0, 0, 0]] where
 M := ![![![-61, 0, -61, 0, 61, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, -1, 0, 1, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)


lemma PB87I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)
  rfl

def PB87I1 : PrimesBelowBoundCertificateInterval' O 23 61 87 where
  m := 9
  g := ![4, 1, 1, 4, 4, 2, 1, 1, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB87I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2, I29N3]
    · exact ![I31N0]
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2, I41N3]
    · exact ![I43N0, I43N1, I43N2, I43N3]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
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
    · exact ![841, 29, 29, 841]
    · exact ![887503681]
    · exact ![2565726409]
    · exact ![1681, 1681, 41, 41]
    · exact ![1849, 43, 43, 1849]
    · exact ![103823, 103823]
    · exact ![22164361129]
    · exact ![42180533641]
    · exact ![226981, 226981]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
      exact NI29N3
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
      exact NI41N3
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
      exact NI43N3
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  Il := ![[I29N1, I29N2], [], [], [I41N2, I41N3], [I43N1, I43N2], [], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
