/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.RI4_4_54381317_1
import LeanBridge.IdealArithmetic.Generation.ClassGroupGeneration
import LeanBridge.IdealArithmetic.IdealArithmetic
import LeanBridge.IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0], ![-130, -62, -4, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0], ![-130, -62, -4, 1]] 
 ![![31, 0, 0, 0], ![0, 31, 0, 0], ![4, 13, 1, 0], ![10, 21, 0, 1]] where
  M :=![![![31, 0, 0, 0], ![0, 31, 0, 0], ![0, 0, 31, 0], ![0, 0, 0, 31]], ![![-130, -62, -4, 1], ![383, 202, 18, -3], ![-1149, -613, -38, 15], ![5745, 3831, 587, -23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![317, 713, 190, -4], ![-2573, -899, 0, 0]], ![![175, 319, 81, -2], ![-1069, -377, 0, 0]], ![![257, 503, 130, -3], ![-1733, -609, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-4, -13, 31, 0], ![-10, -21, 0, 31]], ![![-4, -1, -4, 1], ![11, 1, 18, -3], ![-37, -14, -38, 15], ![117, -107, 587, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [3, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 30], [0, 1]]
 g := ![![[20, 5], [2, 14], [21, 1], [2, 1]],![[30, 26], [30, 17], [23, 30], [4, 30]]]
 h' := ![![[2, 30], [25, 25], [30, 13], [25, 1], [0, 1]],![[0, 1], [13, 6], [25, 18], [27, 30], [2, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [23, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where 
  n := 2
  hpos := by decide  
  P := [3, 29, 1]
  hirr := P31P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![32941, 29672, 8231, 631]
  a := ![0, -1, -1, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-203, -2922, 8231, 631]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0], ![-136, -73, -4, 1]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0, 0], ![-136, -73, -4, 1]] 
 ![![31, 0, 0, 0], ![0, 31, 0, 0], ![5, 17, 1, 0], ![8, 26, 0, 1]] where
  M :=![![![31, 0, 0, 0], ![0, 31, 0, 0], ![0, 0, 31, 0], ![0, 0, 0, 31]], ![![-136, -73, -4, 1], ![383, 196, 7, -3], ![-1149, -613, -44, 4], ![1532, 179, -293, -40]]]
  hmulB := by decide  
  f := ![![![6888, 238, -1337, -117], ![-29946, -11191, 0, 0]], ![![-341, 0, 71, 6], ![1581, 589, 0, 0]], ![![981, 69, -175, -16], ![-3950, -1482, 0, 0]], ![![1474, 52, -286, -25], ![-6406, -2394, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-5, -17, 31, 0], ![-8, -26, 0, 31]], ![![-4, -1, -4, 1], ![12, 5, 7, -3], ![-31, 1, -44, 4], ![107, 200, -293, -40]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [16, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 30], [0, 1]]
 g := ![![[2, 2], [16, 16], [8, 8], [30, 1]],![[0, 29], [0, 15], [0, 23], [29, 30]]]
 h' := ![![[30, 30], [23, 23], [27, 27], [16, 16], [0, 1]],![[0, 1], [0, 8], [0, 4], [0, 15], [30, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where 
  n := 2
  hpos := by decide  
  P := [16, 1, 1]
  hirr := P31P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![1553083, 1297610, 282820, -6160]
  a := ![-2, 3, -64, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![6073, -108070, 282820, -6160]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0, 0], ![-130, -62, -4, 1]] ![![31, 0, 0, 0], ![-136, -73, -4, 1]]
  ![![31, 0, 0, 0]] where
 M :=  ![![![961, 0, 0, 0], ![-4216, -2263, -124, 31]], ![![-4030, -1922, -124, 31], ![62, -31, -31, 0]]]
 hmul := by decide  
 g :=  ![![![![31, 0, 0, 0]], ![![-136, -73, -4, 1]]], ![![![-130, -62, -4, 1]], ![![2, -1, -1, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-127, -67, -4, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-127, -67, -4, 1]] 
 ![![37, 0, 0, 0], ![0, 37, 0, 0], ![2, 4, 1, 0], ![29, 23, 0, 1]] where
  M :=![![![-127, -67, -4, 1], ![383, 205, 13, -3], ![-1149, -613, -35, 10], ![3830, 2171, 187, -25]]]
  hmulB := by decide  
  f := ![![![-136, -67, -4, 1]], ![![383, 196, 13, -3]], ![![3, 1, 0, 0]], ![![235, 128, 10, -2]]]
  g := ![![![-4, -2, -4, 1], ![12, 6, 13, -3], ![-37, -19, -35, 10], ![113, 54, 187, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [30, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 36], [0, 1]]
 g := ![![[18, 21], [26], [13, 16], [3], [1]],![[0, 16], [26], [31, 21], [3], [1]]]
 h' := ![![[15, 36], [27, 13], [17, 27], [33, 33], [7, 15], [0, 1]],![[0, 1], [0, 24], [15, 10], [10, 4], [10, 22], [15, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [16, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where 
  n := 2
  hpos := by decide  
  P := [30, 22, 1]
  hirr := P37P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![275003, 239545, 61904, 3888]
  a := ![-1, 1, 1, -3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![1039, -2635, 61904, 3888]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-136, -67, -4, 1]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-136, -67, -4, 1]] 
 ![![37, 0, 0, 0], ![0, 37, 0, 0], ![12, 32, 1, 0], ![23, 24, 0, 1]] where
  M :=![![![-136, -67, -4, 1], ![383, 196, 13, -3], ![-1149, -613, -44, 10], ![3830, 2171, 187, -34]]]
  hmulB := by decide  
  f := ![![![-127, -67, -4, 1]], ![![383, 205, 13, -3]], ![![259, 139, 9, -2]], ![![273, 150, 11, -2]]]
  g := ![![![-3, 1, -4, 1], ![8, -4, 13, -3], ![-23, 15, -44, 10], ![64, -81, 187, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [28, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 36], [0, 1]]
 g := ![![[22, 4], [21], [36, 10], [21], [1]],![[0, 33], [21], [18, 27], [21], [1]]]
 h' := ![![[13, 36], [11, 2], [28, 13], [11, 26], [9, 13], [0, 1]],![[0, 1], [0, 35], [12, 24], [16, 11], [30, 24], [13, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [21, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where 
  n := 2
  hpos := by decide  
  P := [28, 24, 1]
  hirr := P37P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![29902, 25489, 6268, 356]
  a := ![0, -1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-1446, -4963, 6268, 356]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-127, -67, -4, 1]] ![![-136, -67, -4, 1]]
  ![![37, 0, 0, 0]] where
 M :=  ![![![37, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![1, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0]] 
 ![![41, 0, 0, 0], ![0, 41, 0, 0], ![0, 0, 41, 0], ![0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0], ![0, 41, 0, 0], ![0, 0, 41, 0], ![0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [26, 32, 21, 22, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 40, 21, 12], [26, 8, 34, 30], [19, 33, 27, 40], [0, 1]]
 g := ![![[1, 25, 30, 33], [40, 6, 36], [9, 18, 21], [19, 1], []],![[7, 20, 31, 38, 38, 35], [23, 33, 2], [12, 26, 9], [39, 21, 36, 32, 6, 27], [36, 1, 21]],![[3, 28, 30, 33, 39, 28], [18], [34, 1, 20], [36, 18, 32, 38, 4, 3], [28, 34, 39]],![[36, 15, 26, 12, 18, 39], [16, 5, 39], [15, 10, 2], [17, 25, 20, 10, 4, 40], [18, 6, 1]]]
 h' := ![![[15, 40, 21, 12], [36, 10, 6, 22], [16, 17, 36, 35], [39, 22, 20, 12], [0, 0, 1], [0, 1]],![[26, 8, 34, 30], [19, 19, 7, 15], [17, 39, 30, 17], [40, 4, 31, 38], [27, 22, 35, 22], [15, 40, 21, 12]],![[19, 33, 27, 40], [32, 7, 40, 21], [34, 14, 31], [37, 23, 27, 15], [30, 30, 3, 18], [26, 8, 34, 30]],![[0, 1], [14, 5, 29, 24], [15, 12, 26, 30], [35, 33, 4, 17], [16, 30, 2, 1], [19, 33, 27, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [29, 11], []]
 b := ![[], [], [1, 24, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where 
  n := 4
  hpos := by decide  
  P := [26, 32, 21, 22, 1]
  hirr := P41P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![3073808142710, 2936740358953, 903274299967, 88867303856]
  a := ![19, 1, -1, 3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![74970930310, 71627813633, 22031080487, 2167495216]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0], ![-115, -67, -4, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0], ![-115, -67, -4, 1]] 
 ![![43, 0, 0, 0], ![0, 43, 0, 0], ![38, 16, 1, 0], ![37, 40, 0, 1]] where
  M :=![![![43, 0, 0, 0], ![0, 43, 0, 0], ![0, 0, 43, 0], ![0, 0, 0, 43]], ![![-115, -67, -4, 1], ![383, 217, 13, -3], ![-1149, -613, -23, 10], ![3830, 2171, 187, -13]]]
  hmulB := by decide  
  f := ![![![43669, 18498, 1155, -6], ![-145641, -48633, 0, 0]], ![![-1482, -623, -39, 0], ![5031, 1677, 0, 0]], ![![38120, 16162, 1009, -6], ![-126804, -42354, 0, 0]], ![![36181, 15328, 957, -5], ![-120645, -40287, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-38, -16, 43, 0], ![-37, -40, 0, 43]], ![![0, -1, -4, 1], ![0, 3, 13, -3], ![-15, -15, -23, 10], ![-65, -7, 187, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [37, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 42], [0, 1]]
 g := ![![[32, 35], [21, 11], [38], [27, 13], [1]],![[1, 8], [26, 32], [38], [29, 30], [1]]]
 h' := ![![[20, 42], [40, 11], [27, 21], [33, 9], [6, 20], [0, 1]],![[0, 1], [2, 32], [17, 22], [41, 34], [19, 23], [20, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [11, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where 
  n := 2
  hpos := by decide  
  P := [37, 23, 1]
  hirr := P43P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![126022, 112292, 30529, 2339]
  a := ![-1, 0, 1, 2]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-26061, -10924, 30529, 2339]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0], ![1, 1, 0, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0, 0], ![1, 1, 0, 0]] 
 ![![43, 0, 0, 0], ![1, 1, 0, 0], ![42, 0, 1, 0], ![1, 0, 0, 1]] where
  M :=![![![43, 0, 0, 0], ![0, 43, 0, 0], ![0, 0, 43, 0], ![0, 0, 0, 43]], ![![1, 1, 0, 0], ![0, 1, 1, 0], ![0, 0, 1, 1], ![383, 332, 80, 2]]]
  hmulB := by decide  
  f := ![![![0, -4, -4, -1], ![43, 129, 43, 0]], ![![0, 0, 1, 1], ![1, 0, -43, 0]], ![![0, -2, -2, -1], ![42, 44, 43, 0]], ![![0, 0, 1, 1], ![1, -1, -42, 0]]]
  g := ![![![1, 0, 0, 0], ![-1, 43, 0, 0], ![-42, 0, 43, 0], ![-1, 0, 0, 43]], ![![0, 1, 0, 0], ![-1, 1, 1, 0], ![-1, 0, 1, 1], ![-77, 332, 80, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0], ![-18, 1, 0, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0, 0], ![-18, 1, 0, 0]] 
 ![![43, 0, 0, 0], ![25, 1, 0, 0], ![20, 0, 1, 0], ![16, 0, 0, 1]] where
  M :=![![![43, 0, 0, 0], ![0, 43, 0, 0], ![0, 0, 43, 0], ![0, 0, 0, 43]], ![![-18, 1, 0, 0], ![0, -18, 1, 0], ![0, 0, -18, 1], ![383, 332, 80, -17]]]
  hmulB := by decide  
  f := ![![![361, 34, 6045, -336], ![860, 129, 14448, 0]], ![![199, 25, 3670, -204], ![474, 86, 8772, 0]], ![![188, 26, 2806, -156], ![448, 87, 6708, 0]], ![![136, 18, 2249, -125], ![324, 61, 5376, 0]]]
  g := ![![![1, 0, 0, 0], ![-25, 43, 0, 0], ![-20, 0, 43, 0], ![-16, 0, 0, 43]], ![![-1, 1, 0, 0], ![10, -18, 1, 0], ![8, 0, -18, 1], ![-215, 332, 80, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0, 0], ![-115, -67, -4, 1]] ![![43, 0, 0, 0], ![1, 1, 0, 0]]
  ![![43, 0, 0, 0], ![225, 150, 9, -2]] where
 M :=  ![![![1849, 0, 0, 0], ![43, 43, 0, 0]], ![![-4945, -2881, -172, 43], ![268, 150, 9, -2]]]
 hmul := by decide  
 g :=  ![![![![-182, -150, -9, 2], ![43, 0, 0, 0]], ![![-224, -149, -9, 2], ![43, 0, 0, 0]]], ![![![-115, -67, -4, 1], ![0, 0, 0, 0]], ![![-224, -150, -9, 2], ![44, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0, 0], ![225, 150, 9, -2]] ![![43, 0, 0, 0], ![-18, 1, 0, 0]]
  ![![43, 0, 0, 0]] where
 M :=  ![![![1849, 0, 0, 0], ![-774, 43, 0, 0]], ![![9675, 6450, 387, -86], ![-4816, -3139, -172, 43]]]
 hmul := by decide  
 g :=  ![![![![43, 0, 0, 0]], ![![-18, 1, 0, 0]]], ![![![225, 150, 9, -2]], ![![-112, -73, -4, 1]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0], ![-151, -53, -4, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0], ![-151, -53, -4, 1]] 
 ![![47, 0, 0, 0], ![0, 47, 0, 0], ![11, 14, 1, 0], ![34, 3, 0, 1]] where
  M :=![![![47, 0, 0, 0], ![0, 47, 0, 0], ![0, 0, 47, 0], ![0, 0, 0, 47]], ![![-151, -53, -4, 1], ![383, 181, 27, -3], ![-1149, -613, -59, 24], ![9192, 6819, 1307, -35]]]
  hmulB := by decide  
  f := ![![![6058, 18891, 6228, -207], ![-41031, -16920, 0, 0]], ![![-500, -1851, -620, 20], ![4136, 1692, 0, 0]], ![![1346, 3897, 1275, -43], ![-8347, -3456, 0, 0]], ![![4434, 13577, 4468, -149], ![-29392, -12132, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-11, -14, 47, 0], ![-34, -3, 0, 47]], ![![-3, 0, -4, 1], ![4, -4, 27, -3], ![-28, 3, -59, 24], ![-85, -242, 1307, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [16, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 46], [0, 1]]
 g := ![![[45, 3], [24, 18], [21, 6], [19, 37], [1]],![[0, 44], [36, 29], [25, 41], [28, 10], [1]]]
 h' := ![![[32, 46], [39, 12], [40, 26], [25, 37], [31, 32], [0, 1]],![[0, 1], [0, 35], [26, 21], [34, 10], [21, 15], [32, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [11, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where 
  n := 2
  hpos := by decide  
  P := [16, 15, 1]
  hirr := P47P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![124058, 109100, 28780, 1982]
  a := ![-5, 0, 0, 2]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-5530, -6378, 28780, 1982]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0], ![-148, -46, -4, 1]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0, 0], ![-148, -46, -4, 1]] 
 ![![47, 0, 0, 0], ![0, 47, 0, 0], ![25, 32, 1, 0], ![46, 35, 0, 1]] where
  M :=![![![47, 0, 0, 0], ![0, 47, 0, 0], ![0, 0, 47, 0], ![0, 0, 0, 47]], ![![-148, -46, -4, 1], ![383, 184, 34, -3], ![-1149, -613, -56, 31], ![11873, 9143, 1867, -25]]]
  hmulB := by decide  
  f := ![![![9245, 43148, 14912, -318], ![-72474, -29140, 0, 0]], ![![-329, -2115, -742, 15], ![3666, 1457, 0, 0]], ![![4703, 21514, 7427, -159], ![-36051, -14508, 0, 0]], ![![8797, 40653, 14042, -300], ![-68204, -27435, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-25, -32, 47, 0], ![-46, -35, 0, 47]], ![![-2, 1, -4, 1], ![-7, -17, 34, -3], ![-25, 2, -56, 31], ![-716, -1058, 1867, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [25, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 46], [0, 1]]
 g := ![![[8, 32], [36, 3], [45, 8], [0, 3], [1]],![[0, 15], [0, 44], [43, 39], [11, 44], [1]]]
 h' := ![![[35, 46], [40, 19], [3, 12], [0, 33], [22, 35], [0, 1]],![[0, 1], [0, 28], [0, 35], [27, 14], [25, 12], [35, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [4, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where 
  n := 2
  hpos := by decide  
  P := [25, 12, 1]
  hirr := P47P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![84265, 63449, 9583, -1388]
  a := ![-10, 2, 13, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-1946, -4141, 9583, -1388]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0, 0], ![-151, -53, -4, 1]] ![![47, 0, 0, 0], ![-148, -46, -4, 1]]
  ![![47, 0, 0, 0]] where
 M :=  ![![![2209, 0, 0, 0], ![-6956, -2162, -188, 47]], ![![-7097, -2491, -188, 47], ![18518, 8789, 893, -141]]]
 hmul := by decide  
 g :=  ![![![![47, 0, 0, 0]], ![![-148, -46, -4, 1]]], ![![![-151, -53, -4, 1]], ![![394, 187, 19, -3]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-121, -67, -4, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-121, -67, -4, 1]] 
 ![![53, 0, 0, 0], ![0, 53, 0, 0], ![20, 10, 1, 0], ![12, 26, 0, 1]] where
  M :=![![![-121, -67, -4, 1], ![383, 211, 13, -3], ![-1149, -613, -29, 10], ![3830, 2171, 187, -19]]]
  hmulB := by decide  
  f := ![![![142, 67, 4, -1]], ![![-383, -190, -13, 3]], ![![3, 1, 0, 0]], ![![-228, -119, -9, 2]]]
  g := ![![![-1, -1, -4, 1], ![3, 3, 13, -3], ![-13, -11, -29, 10], ![6, 15, 187, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [26, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 52], [0, 1]]
 g := ![![[39, 49], [29], [22, 25], [52], [46, 1]],![[14, 4], [29], [6, 28], [52], [39, 52]]]
 h' := ![![[46, 52], [3, 46], [11, 33], [25, 5], [23, 23], [0, 1]],![[0, 1], [52, 7], [45, 20], [43, 48], [21, 30], [46, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [30, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where 
  n := 2
  hpos := by decide  
  P := [26, 7, 1]
  hirr := P53P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![39483, 37652, 11576, 1138]
  a := ![1, 1, -4, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-3881, -2032, 11576, 1138]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0], ![-10, 1, 0, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0, 0], ![-10, 1, 0, 0]] 
 ![![53, 0, 0, 0], ![43, 1, 0, 0], ![6, 0, 1, 0], ![7, 0, 0, 1]] where
  M :=![![![53, 0, 0, 0], ![0, 53, 0, 0], ![0, 0, 53, 0], ![0, 0, 0, 53]], ![![-10, 1, 0, 0], ![0, -10, 1, 0], ![0, 0, -10, 1], ![383, 332, 80, -9]]]
  hmulB := by decide  
  f := ![![![221, -12, 1439, -144], ![1166, 53, 7632, 0]], ![![171, -7, 1279, -128], ![902, 53, 6784, 0]], ![![42, 6, 159, -16], ![222, 54, 848, 0]], ![![39, -2, 190, -19], ![206, 10, 1008, 0]]]
  g := ![![![1, 0, 0, 0], ![-43, 53, 0, 0], ![-6, 0, 53, 0], ![-7, 0, 0, 53]], ![![-1, 1, 0, 0], ![8, -10, 1, 0], ![1, 0, -10, 1], ![-270, 332, 80, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0], ![-1, 1, 0, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0, 0], ![-1, 1, 0, 0]] 
 ![![53, 0, 0, 0], ![52, 1, 0, 0], ![52, 0, 1, 0], ![52, 0, 0, 1]] where
  M :=![![![53, 0, 0, 0], ![0, 53, 0, 0], ![0, 0, 53, 0], ![0, 0, 0, 53]], ![![-1, 1, 0, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![383, 332, 80, 0]]]
  hmulB := by decide  
  f := ![![![6, -55, 51, -1], ![265, -2650, 53, 0]], ![![3, -51, 50, -1], ![107, -2597, 53, 0]], ![![2, -1, 51, -51], ![54, 1, 2703, 0]], ![![3, -53, 51, 0], ![107, -2702, 1, 0]]]
  g := ![![![1, 0, 0, 0], ![-52, 53, 0, 0], ![-52, 0, 53, 0], ![-52, 0, 0, 53]], ![![-1, 1, 0, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-397, 332, 80, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-121, -67, -4, 1]] ![![53, 0, 0, 0], ![-10, 1, 0, 0]]
  ![![53, 0, 0, 0], ![1646, 881, 53, -13]] where
 M :=  ![![![-6413, -3551, -212, 53], ![1593, 881, 53, -13]]]
 hmul := by decide  
 g :=  ![![![![-121, -67, -4, 1], ![0, 0, 0, 0]], ![![-1, 0, 0, 0], ![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0, 0], ![1646, 881, 53, -13]] ![![53, 0, 0, 0], ![-1, 1, 0, 0]]
  ![![53, 0, 0, 0]] where
 M :=  ![![![2809, 0, 0, 0], ![-53, 53, 0, 0]], ![![87238, 46693, 2809, -689], ![-6625, -3551, -212, 53]]]
 hmul := by decide  
 g :=  ![![![![53, 0, 0, 0]], ![![-1, 1, 0, 0]]], ![![![1646, 881, 53, -13]], ![![-125, -67, -4, 1]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0]] 
 ![![59, 0, 0, 0], ![0, 59, 0, 0], ![0, 0, 59, 0], ![0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0], ![0, 59, 0, 0], ![0, 0, 59, 0], ![0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [28, 58, 37, 56, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 52, 7, 55], [8, 25, 32, 48], [16, 40, 20, 15], [0, 1]]
 g := ![![[45, 36, 11, 48], [54, 36, 44, 1], [3, 25, 20], [42, 31, 3, 1], []],![[0, 27, 50, 45, 38, 23], [55, 36, 43, 6, 38, 30], [34, 35, 17], [19, 16, 12, 10, 34, 50], [27, 42, 39, 47, 26, 54]],![[33, 8, 3, 42, 55, 17], [54, 5, 1, 13, 50, 45], [5, 25, 22], [12, 54, 33, 50, 1, 36], [28, 0, 43, 22, 12, 26]],![[28, 34, 11, 52, 1, 9], [11, 40, 20, 48, 3, 49], [12, 53, 28], [3, 15, 57, 8, 47, 16], [13, 28, 52, 27, 25, 12]]]
 h' := ![![[38, 52, 7, 55], [22, 12, 30, 44], [50, 11, 9, 58], [4, 0, 45, 16], [0, 0, 0, 1], [0, 1]],![[8, 25, 32, 48], [17, 44, 58, 3], [33, 12, 34, 9], [49, 17, 34, 31], [13, 33, 54, 31], [38, 52, 7, 55]],![[16, 40, 20, 15], [18, 20, 23, 6], [41, 38, 15, 37], [2, 21, 58, 50], [23, 49, 24, 35], [8, 25, 32, 48]],![[0, 1], [7, 42, 7, 6], [4, 57, 1, 14], [35, 21, 40, 21], [15, 36, 40, 51], [16, 40, 20, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [42, 40, 28], []]
 b := ![[], [], [8, 33, 39, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where 
  n := 4
  hpos := by decide  
  P := [28, 58, 37, 56, 1]
  hirr := P59P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![30550054270, 29149665847, 8949313225, 878144436]
  a := ![-3, 1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![517797530, 494062133, 151683275, 14883804]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀


def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0], ![-116, -67, -4, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0], ![-116, -67, -4, 1]] 
 ![![61, 0, 0, 0], ![0, 61, 0, 0], ![35, 15, 1, 0], ![24, 54, 0, 1]] where
  M :=![![![61, 0, 0, 0], ![0, 61, 0, 0], ![0, 0, 61, 0], ![0, 0, 0, 61]], ![![-116, -67, -4, 1], ![383, 216, 13, -3], ![-1149, -613, -24, 10], ![3830, 2171, 187, -14]]]
  hmulB := by decide  
  f := ![![![44677, 22362, 1404, -186], ![-109434, -40260, 0, 0]], ![![-733, -365, -23, 3], ![1830, 671, 0, 0]], ![![25456, 12742, 800, -106], ![-62339, -22935, 0, 0]], ![![16986, 8508, 534, -71], ![-41406, -15246, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-35, -15, 61, 0], ![-24, -54, 0, 61]], ![![0, -1, -4, 1], ![0, 3, 13, -3], ![-9, -13, -24, 10], ![-39, 2, 187, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [58, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 60], [0, 1]]
 g := ![![[39, 20], [16], [52, 15], [59, 52], [56, 1]],![[0, 41], [16], [38, 46], [43, 9], [51, 60]]]
 h' := ![![[56, 60], [45, 9], [34, 4], [55, 25], [46, 28], [0, 1]],![[0, 1], [0, 52], [14, 57], [52, 36], [28, 33], [56, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [18, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where 
  n := 2
  hpos := by decide  
  P := [58, 5, 1]
  hirr := P61P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![493769, 412628, 96045, 3357]
  a := ![3, 0, 7, -4]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-48334, -19825, 96045, 3357]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0], ![-8, 1, 0, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0, 0], ![-8, 1, 0, 0]] 
 ![![61, 0, 0, 0], ![53, 1, 0, 0], ![58, 0, 1, 0], ![37, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0], ![0, 61, 0, 0], ![0, 0, 61, 0], ![0, 0, 0, 61]], ![![-8, 1, 0, 0], ![0, -8, 1, 0], ![0, 0, -8, 1], ![383, 332, 80, -7]]]
  hmulB := by decide  
  f := ![![![217, -19, 3679, -460], ![1647, 61, 28060, 0]], ![![193, -16, 3311, -414], ![1465, 61, 25254, 0]], ![![210, -18, 3495, -437], ![1594, 62, 26657, 0]], ![![145, -9, 2231, -279], ![1101, 69, 17020, 0]]]
  g := ![![![1, 0, 0, 0], ![-53, 61, 0, 0], ![-58, 0, 61, 0], ![-37, 0, 0, 61]], ![![-1, 1, 0, 0], ![6, -8, 1, 0], ![7, 0, -8, 1], ![-354, 332, 80, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0, 0], ![-116, -67, -4, 1]] ![![61, 0, 0, 0], ![-8, 1, 0, 0]]
  ![![61, 0, 0, 0], ![1433, 752, 45, -11]] where
 M :=  ![![![3721, 0, 0, 0], ![-488, 61, 0, 0]], ![![-7076, -4087, -244, 61], ![1311, 752, 45, -11]]]
 hmul := by decide  
 g :=  ![![![![-1372, -752, -45, 11], ![61, 0, 0, 0]], ![![-8, 1, 0, 0], ![0, 0, 0, 0]]], ![![![-116, -67, -4, 1], ![0, 0, 0, 0]], ![![-2, 0, 0, 0], ![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0, 0], ![1433, 752, 45, -11]] ![![61, 0, 0, 0], ![-8, 1, 0, 0]]
  ![![61, 0, 0, 0]] where
 M :=  ![![![3721, 0, 0, 0], ![-488, 61, 0, 0]], ![![87413, 45872, 2745, -671], ![-15677, -8235, -488, 122]]]
 hmul := by decide  
 g :=  ![![![![61, 0, 0, 0]], ![![-8, 1, 0, 0]]], ![![![1433, 752, 45, -11]], ![![-257, -135, -8, 2]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0, 0]] 
 ![![67, 0, 0, 0], ![0, 67, 0, 0], ![0, 0, 67, 0], ![0, 0, 0, 67]] where
  M :=![![![67, 0, 0, 0], ![0, 67, 0, 0], ![0, 0, 67, 0], ![0, 0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 4 2 6 [4, 41, 21, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 50, 43, 39], [31, 33, 29, 41], [5, 50, 62, 54], [0, 1]]
 g := ![![[60, 58, 8, 15], [37, 10, 46, 65], [36, 39, 19], [0, 32, 9], [1], []],![[22, 40, 42, 48, 20, 10], [42, 27, 18, 30, 30, 23], [53, 35, 16], [23, 26, 62], [38, 49, 15], [14, 64, 47]],![[13, 30, 57, 44, 49, 18], [8, 1, 2, 61, 55, 27], [23, 51, 37], [23, 63, 56], [5, 14, 4], [26, 15, 6]],![[8, 32, 14, 38, 0, 10], [40, 39, 49, 54, 23, 56], [43, 46, 4], [34, 55, 37], [47, 42, 65], [59, 25, 35]]]
 h' := ![![[28, 50, 43, 39], [53, 66, 21, 22], [45, 11, 1, 20], [16, 66, 32, 35], [63, 26, 46, 64], [0, 0, 1], [0, 1]],![[31, 33, 29, 41], [17, 8, 34, 58], [3, 29, 24, 40], [58, 56, 65, 63], [63, 38, 65, 14], [58, 27, 60, 22], [28, 50, 43, 39]],![[5, 50, 62, 54], [65, 37, 57, 49], [51, 64, 61, 33], [64, 55, 18, 38], [42, 42, 12, 18], [53, 49, 27, 65], [31, 33, 29, 41]],![[0, 1], [44, 23, 22, 5], [58, 30, 48, 41], [37, 24, 19, 65], [46, 28, 11, 38], [57, 58, 46, 47], [5, 50, 62, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [60, 24, 61], []]
 b := ![[], [], [42, 19, 64, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where 
  n := 4
  hpos := by decide  
  P := [4, 41, 21, 3, 1]
  hirr := P67P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![27504193249, 26227687608, 8044822995, 788187933]
  a := ![0, 1, 1, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![410510347, 391458024, 120071985, 11763999]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 20151121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0], ![-98, -67, -4, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0, 0], ![-98, -67, -4, 1]] 
 ![![71, 0, 0, 0], ![0, 71, 0, 0], ![18, 33, 1, 0], ![45, 65, 0, 1]] where
  M :=![![![71, 0, 0, 0], ![0, 71, 0, 0], ![0, 0, 71, 0], ![0, 0, 0, 71]], ![![-98, -67, -4, 1], ![383, 234, 13, -3], ![-1149, -613, -6, 10], ![3830, 2171, 187, 4]]]
  hmulB := by decide  
  f := ![![![8707, 3780, 150, -18], ![-15336, -5538, 0, 0]], ![![-632, -264, -10, 1], ![1207, 426, 0, 0]], ![![1904, 829, 33, -4], ![-3334, -1206, 0, 0]], ![![4893, 2122, 84, -10], ![-8649, -3120, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-18, -33, 71, 0], ![-45, -65, 0, 71]], ![![-1, 0, -4, 1], ![4, 0, 13, -3], ![-21, -15, -6, 10], ![4, -60, 187, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [70, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 70], [0, 1]]
 g := ![![[64, 54], [31, 6], [56, 12], [4], [49], [1]],![[41, 17], [60, 65], [43, 59], [4], [49], [1]]]
 h' := ![![[64, 70], [31, 14], [56, 52], [19, 56], [50, 69], [1, 64], [0, 1]],![[0, 1], [4, 57], [47, 19], [53, 15], [64, 2], [50, 7], [64, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [28, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where 
  n := 2
  hpos := by decide  
  P := [70, 7, 1]
  hirr := P71P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![6192, 5327, 1309, 40]
  a := ![-1, 3, 4, 0]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-270, -570, 1309, 40]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0], ![-165, -67, -4, 1]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0, 0], ![-165, -67, -4, 1]] 
 ![![71, 0, 0, 0], ![0, 71, 0, 0], ![30, 37, 1, 0], ![26, 10, 0, 1]] where
  M :=![![![71, 0, 0, 0], ![0, 71, 0, 0], ![0, 0, 71, 0], ![0, 0, 0, 71]], ![![-165, -67, -4, 1], ![383, 167, 13, -3], ![-1149, -613, -73, 10], ![3830, 2171, 187, -63]]]
  hmulB := by decide  
  f := ![![![20611, 13190, 2060, -410], ![-60350, -29820, 0, 0]], ![![-3380, -2175, -342, 68], ![10082, 4970, 0, 0]], ![![6980, 4453, 693, -138], ![-20232, -10010, 0, 0]], ![![7146, 4554, 708, -141], ![-20648, -10220, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-30, -37, 71, 0], ![-26, -10, 0, 71]], ![![-1, 1, -4, 1], ![1, -4, 13, -3], ![11, 28, -73, 10], ![-2, -58, 187, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [7, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 70], [0, 1]]
 g := ![![[2, 12], [33, 36], [14, 5], [64], [54], [1]],![[47, 59], [26, 35], [15, 66], [64], [54], [1]]]
 h' := ![![[57, 70], [53, 15], [44, 65], [15, 17], [26, 8], [64, 57], [0, 1]],![[0, 1], [56, 56], [57, 6], [61, 54], [56, 63], [47, 14], [57, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [65, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where 
  n := 2
  hpos := by decide  
  P := [7, 14, 1]
  hirr := P71P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![1525483, 1341135, 353676, 24255]
  a := ![-1, 1, 0, 7]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-136837, -168837, 353676, 24255]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0, 0], ![-98, -67, -4, 1]] ![![71, 0, 0, 0], ![-165, -67, -4, 1]]
  ![![71, 0, 0, 0]] where
 M :=  ![![![5041, 0, 0, 0], ![-11715, -4757, -284, 71]], ![![-6958, -4757, -284, 71], ![-1065, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![71, 0, 0, 0]], ![![-165, -67, -4, 1]]], ![![![-98, -67, -4, 1]], ![![-15, 0, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)


lemma PB692I1_primes (p : ℕ) :
  p ∈ Set.range ![31, 37, 41, 43, 47, 53, 59, 61, 67, 71] ↔ Nat.Prime p ∧ 29 < p ∧ p ≤ 71 := by
  rw [← List.mem_ofFn']
  convert primes_range 29 71 (by omega)
  rfl

def PB692I1 : PrimesBelowBoundCertificateInterval' O 29 71 692 where
  m := 10
  g := ![2, 2, 1, 3, 2, 3, 1, 3, 1, 2]
  P := ![31, 37, 41, 43, 47, 53, 59, 61, 67, 71]
  hP := PB692I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![961, 961]
    · exact ![1369, 1369]
    · exact ![2825761]
    · exact ![1849, 43, 43]
    · exact ![2209, 2209]
    · exact ![2809, 53, 53]
    · exact ![12117361]
    · exact ![3721, 61, 61]
    · exact ![20151121]
    · exact ![5041, 5041]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
  Il := ![[], [], [], [I43N1, I43N2], [], [I53N1, I53N2], [], [I61N1, I61N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
