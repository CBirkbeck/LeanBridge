/-
Copyright (c) 2025 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_0_76176_2.RI4_0_76176_2
import LeanBridge.IdealArithmetic.Generation.ClassGroupGeneration
import LeanBridge.IdealArithmetic.IdealArithmetic
import LeanBridge.IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![-1, 1, 0, -1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0], ![-1, 1, 0, -1]] 
 ![![2, 0, 0, 0], ![1, 1, 0, 0], ![1, 0, 1, 0], ![0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]], ![![-1, 1, 0, -1], ![-6, 7, 9, -18], ![36, 3, 7, -9], ![16, 4, 6, -9]]]
  hmulB := by decide  
  f := ![![![174, -134, 7, 128], ![274, 0, -2, 0]], ![![86, -66, -1, 69], ![129, 1, -1, 0]], ![![88, -68, 4, 65], ![139, 0, -1, 0]], ![![-84, 64, -8, -55], ![-138, 1, 1, 0]]]
  g := ![![![1, 0, 0, 0], ![-1, 2, 0, 0], ![-1, 0, 2, 0], ![0, 0, 0, 2]], ![![-1, 1, 0, -1], ![-11, 7, 9, -18], ![13, 3, 7, -9], ![3, 4, 6, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![0, -1, 0, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0, 0], ![0, -1, 0, 0]] 
 ![![2, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]], ![![0, -1, 0, 0], ![0, 0, -1, 0], ![-16, 15, 16, -35], ![-6, 8, 8, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![-1, 0, 0, 0]], ![![0, 0, 0, 0], ![0, -1, 0, 0]], ![![8, -12, -6, 18], ![-9, 4, 1, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]], ![![0, -1, 0, 0], ![0, 0, -1, 0], ![-8, 15, 16, -35], ![-3, 8, 8, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0], ![-1, 1, 0, -1]] ![![2, 0, 0, 0], ![-1, 1, 0, -1]]
  ![![2, 0, 0, 0], ![-1, 0, 1, -2]] where
 M :=  ![![![4, 0, 0, 0], ![-2, 2, 0, -2]], ![![-2, 2, 0, -2], ![-21, 2, 3, -8]]]
 hmul := by decide  
 g :=  ![![![![2, 0, 0, 0], ![0, 0, 0, 0]], ![![-4, 1, -1, 2], ![2, 2, 0, 0]]], ![![![-4, 1, -1, 2], ![2, 2, 0, 0]], ![![-23, 1, -2, 7], ![7, 8, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0], ![-1, 0, 1, -2]] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![2, 0, 0, 0], ![-2, 0, 0, -1]] where
 M :=  ![![![4, 0, 0, 0], ![0, -2, 0, 0]], ![![-2, 0, 2, -4], ![-4, 0, 0, 1]]]
 hmul := by decide  
 g :=  ![![![![2, 0, 0, 0], ![0, 0, 0, 0]], ![![0, -1, 0, 0], ![0, 0, 0, 0]]], ![![![1, 0, 1, -1], ![2, 0, 0, 0]], ![![-1, 0, 0, 1], ![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0], ![-2, 0, 0, -1]] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![2, 0, 0, 0]] where
 M :=  ![![![4, 0, 0, 0], ![0, -2, 0, 0]], ![![-4, 0, 0, -2], ![6, -6, -8, 18]]]
 hmul := by decide  
 g :=  ![![![![2, 0, 0, 0]], ![![0, -1, 0, 0]]], ![![![-2, 0, 0, -1]], ![![3, -3, -4, 9]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![-1, 1, -1, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0], ![-1, 1, -1, 1]] 
 ![![3, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![2, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![0, 0, 0, 3]], ![![-1, 1, -1, 1], ![-10, 6, 9, -17], ![42, -9, -2, 9], ![16, -2, 2, -1]]]
  hmulB := by decide  
  f := ![![![23, -14, -16, 32], ![6, 6, 0, 0]], ![![-1390, 849, 1031, -2035], ![-272, -373, 4, 0]], ![![694, -424, -513, 1014], ![138, 186, -2, 0]], ![![15, -9, -11, 22], ![3, 4, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![-2, 0, 0, 3]], ![![-1, 1, -1, 1], ![8, 6, 9, -17], ![8, -9, -2, 9], ![6, -2, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![1, 0, 2, -3]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0], ![1, 0, 2, -3]] 
 ![![3, 0, 0, 0], ![2, 1, 0, 0], ![2, 0, 1, 0], ![1, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![0, 0, 0, 3]], ![![1, 0, 2, -3], ![14, -5, -8, 16], ![-32, 6, -5, 8], ![-10, 0, -6, 11]]]
  hmulB := by decide  
  f := ![![![253, -72, -46, 116], ![-60, -36, 6, 0]], ![![163, -46, -30, 75], ![-37, -23, 4, 0]], ![![126, -36, -24, 60], ![-28, -18, 3, 0]], ![![84, -24, -16, 40], ![-19, -12, 2, 0]]]
  g := ![![![1, 0, 0, 0], ![-2, 3, 0, 0], ![-2, 0, 3, 0], ![-1, 0, 0, 3]], ![![0, 0, 2, -3], ![8, -5, -8, 16], ![-14, 6, -5, 8], ![-3, 0, -6, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0], ![-1, 1, -1, 1]] ![![3, 0, 0, 0], ![-1, 1, -1, 1]]
  ![![3, 0, 0, 0], ![-1, 0, 1, -2]] where
 M :=  ![![![9, 0, 0, 0], ![-3, 3, -3, 3]], ![![-3, 3, -3, 3], ![-35, 12, 14, -28]]]
 hmul := by decide  
 g :=  ![![![![26, 0, 1, -8], ![-3, -18, 0, 0]], ![![-5, 1, -1, 2], ![0, 3, 0, 0]]], ![![![-5, 1, -1, 2], ![0, 3, 0, 0]], ![![-117, 4, -2, 32], ![20, 84, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0], ![-1, 0, 1, -2]] ![![3, 0, 0, 0], ![1, 0, 2, -3]]
  ![![3, 0, 0, 0], ![-1, 0, -1, 1]] where
 M :=  ![![![9, 0, 0, 0], ![3, 0, 6, -9]], ![![-3, 0, 3, -6], ![-13, 6, 5, -11]]]
 hmul := by decide  
 g :=  ![![![![3, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 1, -2], ![-3, 0, 0, 0]]], ![![![-1, 0, 1, -2], ![0, 0, 0, 0]], ![![-4, 2, 2, -4], ![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0], ![-1, 0, -1, 1]] ![![3, 0, 0, 0], ![1, 0, 2, -3]]
  ![![3, 0, 0, 0]] where
 M :=  ![![![9, 0, 0, 0], ![3, 0, 6, -9]], ![![-3, 0, -3, 3], ![21, -6, -3, 6]]]
 hmul := by decide  
 g :=  ![![![![3, 0, 0, 0]], ![![1, 0, 2, -3]]], ![![![-1, 0, -1, 1]], ![![7, -2, -1, 2]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0], ![-2, -1, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0, 0], ![-2, -1, 0, 0]] 
 ![![5, 0, 0, 0], ![2, 1, 0, 0], ![1, 0, 1, 0], ![0, 0, 0, 5]] where
  M :=![![![5, 0, 0, 0], ![0, 5, 0, 0], ![0, 0, 5, 0], ![0, 0, 0, 5]], ![![-2, -1, 0, 0], ![0, -2, -1, 0], ![-16, 15, 14, -35], ![-6, 8, 8, -20]]]
  hmulB := by decide  
  f := ![![![7, 5, 1, 0], ![15, 5, 0, 0]], ![![2, 3, 1, 0], ![4, 5, 0, 0]], ![![3, 3, 1, 0], ![7, 4, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![-2, 5, 0, 0], ![-1, 0, 5, 0], ![0, 0, 0, 1]], ![![0, -1, 0, 0], ![1, -2, -1, 0], ![-12, 15, 14, -7], ![-6, 8, 8, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 4], [0, 1]]
 g := ![![[4, 4], [1]],![[1, 1], [1]]]
 h' := ![![[3, 4], [2, 3], [0, 1]],![[0, 1], [1, 2], [3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [4, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where 
  n := 2
  hpos := by decide  
  P := [3, 2, 1]
  hirr := P5P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-215071, -100524, -162518, 287820]
  a := ![-6, 8, -60, -13]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![29699, -100524, -162518, 57564]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0], ![-4, 1, 2, -4]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0, 0], ![-4, 1, 2, -4]] 
 ![![5, 0, 0, 0], ![0, 5, 0, 0], ![2, 4, 1, 0], ![2, 3, 0, 1]] where
  M :=![![![5, 0, 0, 0], ![0, 5, 0, 0], ![0, 0, 5, 0], ![0, 0, 0, 5]], ![![-4, 1, 2, -4], ![8, -2, 1, -2], ![4, 9, -2, -1], ![6, 4, 0, -2]]]
  hmulB := by decide  
  f := ![![![-13, -13, -2, 10], ![5, 0, 0, 15]], ![![18, 13, 0, -6], ![0, 0, 0, -15]], ![![10, 5, -1, 0], ![3, 0, 0, -6]], ![![4, 3, 0, -1], ![0, 0, 0, -3]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-2, -4, 5, 0], ![-2, -3, 0, 5]], ![![0, 1, 2, -4], ![2, 0, 1, -2], ![2, 4, -2, -1], ![2, 2, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P1 : CertificateIrreducibleZModOfList' 5 2 2 2 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4], [0, 1]]
 g := ![![[1, 1], [1]],![[0, 4], [1]]]
 h' := ![![[4, 4], [4, 4], [0, 1]],![[0, 1], [0, 1], [4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [2, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N1 : CertifiedPrimeIdeal' SI5N1 5 where 
  n := 2
  hpos := by decide  
  P := [1, 1, 1]
  hirr := P5P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![367, 672, 2684, -7123]
  a := ![-59, 56, 59, -129]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![1849, 2261, 2684, -7123]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N1 B_one_repr
lemma NI5N1 : Nat.card (O ⧸ I5N1) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0], ![-2, -1, 0, 0]] ![![5, 0, 0, 0], ![-4, 1, 2, -4]]
  ![![5, 0, 0, 0]] where
 M :=  ![![![25, 0, 0, 0], ![-20, 5, 10, -20]], ![![-10, -5, 0, 0], ![0, 0, -5, 10]]]
 hmul := by decide  
 g :=  ![![![![5, 0, 0, 0]], ![![-4, 1, 2, -4]]], ![![![-2, -1, 0, 0]], ![![0, 0, -1, 2]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0], ![-5, 1, 2, -4]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0], ![-5, 1, 2, -4]] 
 ![![7, 0, 0, 0], ![0, 7, 0, 0], ![4, 6, 1, 0], ![5, 1, 0, 1]] where
  M :=![![![7, 0, 0, 0], ![0, 7, 0, 0], ![0, 0, 7, 0], ![0, 0, 0, 7]], ![![-5, 1, 2, -4], ![8, -3, 1, -2], ![4, 9, -3, -1], ![6, 4, 0, -3]]]
  hmulB := by decide  
  f := ![![![25, 16, 0, -12], ![0, 0, 0, -28]], ![![-1, -4, -2, 7], ![7, 0, 0, 7]], ![![12, 6, -1, -2], ![4, 0, 0, -10]], ![![17, 11, 0, -8], ![0, 0, 0, -19]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-4, -6, 7, 0], ![-5, -1, 0, 7]], ![![1, -1, 2, -4], ![2, -1, 1, -2], ![3, 4, -3, -1], ![3, 1, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [2, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 6], [0, 1]]
 g := ![![[6, 4], [2, 1]],![[0, 3], [4, 6]]]
 h' := ![![[2, 6], [3, 2], [0, 1]],![[0, 1], [0, 5], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [3, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where 
  n := 2
  hpos := by decide  
  P := [2, 5, 1]
  hirr := P7P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![578, -8, 22, -105]
  a := ![16, -16, -17, 35]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![145, -5, 22, -105]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0], ![-3, -1, 0, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0, 0], ![-3, -1, 0, 0]] 
 ![![7, 0, 0, 0], ![3, 1, 0, 0], ![5, 0, 1, 0], ![0, 0, 0, 7]] where
  M :=![![![7, 0, 0, 0], ![0, 7, 0, 0], ![0, 0, 7, 0], ![0, 0, 0, 7]], ![![-3, -1, 0, 0], ![0, -3, -1, 0], ![-16, 15, 13, -35], ![-6, 8, 8, -21]]]
  hmulB := by decide  
  f := ![![![10, 6, 1, 0], ![21, 7, 0, 0]], ![![6, 5, 1, 0], ![13, 7, 0, 0]], ![![8, 5, 1, 0], ![17, 6, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![-3, 7, 0, 0], ![-5, 0, 7, 0], ![0, 0, 0, 1]], ![![0, -1, 0, 0], ![2, -3, -1, 0], ![-18, 15, 13, -5], ![-10, 8, 8, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [3, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6], [0, 1]]
 g := ![![[2, 4], [1, 1]],![[6, 3], [2, 6]]]
 h' := ![![[1, 6], [4, 5], [0, 1]],![[0, 1], [2, 2], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [5, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where 
  n := 2
  hpos := by decide  
  P := [3, 6, 1]
  hirr := P7P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-129678, -19788, 43207, -137060]
  a := ![257, -234, -239, 561]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-40907, -19788, 43207, -19580]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0, 0], ![-5, 1, 2, -4]] ![![7, 0, 0, 0], ![-3, -1, 0, 0]]
  ![![7, 0, 0, 0]] where
 M :=  ![![![49, 0, 0, 0], ![-21, -7, 0, 0]], ![![-35, 7, 14, -28], ![7, 0, -7, 14]]]
 hmul := by decide  
 g :=  ![![![![7, 0, 0, 0]], ![![-3, -1, 0, 0]]], ![![![-5, 1, 2, -4]], ![![1, 0, -1, 2]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, 2, -4]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-1, 2, 2, -4]] 
 ![![11, 0, 0, 0], ![0, 11, 0, 0], ![3, 0, 1, 0], ![10, 5, 0, 1]] where
  M :=![![![-1, 2, 2, -4], ![8, 1, 2, -2], ![20, -6, -15, 34], ![12, -4, -8, 19]]]
  hmulB := by decide  
  f := ![![![-3, 2, 2, -4]], ![![8, -1, 2, -2]], ![![1, 0, -1, 2]], ![![2, 1, 2, -3]]]
  g := ![![![3, 2, 2, -4], ![2, 1, 2, -2], ![-25, -16, -15, 34], ![-14, -9, -8, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10], [0, 1]]
 g := ![![[9, 5], [8, 5], [1]],![[0, 6], [10, 6], [1]]]
 h' := ![![[7, 10], [5, 4], [2, 7], [0, 1]],![[0, 1], [0, 7], [7, 4], [7, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [9, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where 
  n := 2
  hpos := by decide  
  P := [9, 4, 1]
  hirr := P11P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![128, 0, 259, -726]
  a := ![21, -20, -21, 46]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![601, 330, 259, -726]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -2, -2, 4]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![3, -2, -2, 4]] 
 ![![11, 0, 0, 0], ![0, 11, 0, 0], ![4, 9, 1, 0], ![0, 4, 0, 1]] where
  M :=![![![3, -2, -2, 4], ![-8, 1, -2, 2], ![-20, 6, 17, -34], ![-12, 4, 8, -17]]]
  hmulB := by decide  
  f := ![![![1, -2, -2, 4]], ![![-8, -1, -2, 2]], ![![-8, -1, -1, 0]], ![![-4, 0, 0, -1]]]
  g := ![![![1, 0, -2, 4], ![0, 1, -2, 2], ![-8, -1, 17, -34], ![-4, 0, 8, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [10, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 10], [0, 1]]
 g := ![![[3, 1], [0, 9], [1]],![[6, 10], [5, 2], [1]]]
 h' := ![![[3, 10], [0, 10], [1, 3], [0, 1]],![[0, 1], [8, 1], [10, 8], [3, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [7, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where 
  n := 2
  hpos := by decide  
  P := [10, 8, 1]
  hirr := P11P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-4029, -936, -240, -420]
  a := ![-23, 20, 18, -50]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-279, 264, -240, -420]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-1, 2, 2, -4]] ![![3, -2, -2, 4]]
  ![![11, 0, 0, 0]] where
 M :=  ![![![-11, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![-1, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![1, 1, 0, -1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0], ![1, 1, 0, -1]] 
 ![![13, 0, 0, 0], ![4, 1, 0, 0], ![10, 0, 1, 0], ![3, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![1, 1, 0, -1], ![-6, 9, 9, -18], ![36, 3, 9, -9], ![16, 4, 6, -7]]]
  hmulB := by decide  
  f := ![![![12516, -17605, -17784, 35419], ![-3107, 25818, -130, 0]], ![![9128, -12838, -12969, 25829], ![-2272, 18828, -95, 0]], ![![9148, -12867, -12998, 25887], ![-2274, 18870, -95, 0]], ![![2888, -4063, -4104, 8174], ![-713, 5958, -30, 0]]]
  g := ![![![1, 0, 0, 0], ![-4, 13, 0, 0], ![-10, 0, 13, 0], ![-3, 0, 0, 13]], ![![0, 1, 0, -1], ![-6, 9, 9, -18], ![-3, 3, 9, -9], ![-3, 4, 6, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![4, 1, 0, -1]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0], ![4, 1, 0, -1]] 
 ![![13, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![9, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![4, 1, 0, -1], ![-6, 12, 9, -18], ![36, 3, 12, -9], ![16, 4, 6, -4]]]
  hmulB := by decide  
  f := ![![![434449, -847242, -636948, 1271910], ![-29328, 920348, -234, 0]], ![![83412, -162668, -122292, 244203], ![-5628, 176704, -45, 0]], ![![-16686, 32535, 24460, -48843], ![1134, -35343, 9, 0]], ![![300773, -586552, -440964, 880553], ![-20306, 637164, -162, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![-9, 0, 0, 13]], ![![1, 1, 0, -1], ![12, 12, 9, -18], ![9, 3, 12, -9], ![4, 4, 6, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![-5, 1, 0, -1]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![13, 0, 0, 0], ![-5, 1, 0, -1]] 
 ![![13, 0, 0, 0], ![12, 1, 0, 0], ![12, 0, 1, 0], ![4, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![-5, 1, 0, -1], ![-6, 3, 9, -18], ![36, 3, 3, -9], ![16, 4, 6, -13]]]
  hmulB := by decide  
  f := ![![![92066, -53456, -175695, 346271], ![-66157, 253825, -130, 0]], ![![120292, -69844, -229557, 452426], ![-86434, 331639, -170, 0]], ![![77924, -45244, -148703, 293074], ![-55988, 214830, -110, 0]], ![![28328, -16448, -54060, 106545], ![-20356, 78100, -40, 0]]]
  g := ![![![1, 0, 0, 0], ![-12, 13, 0, 0], ![-12, 0, 13, 0], ![-4, 0, 0, 13]], ![![-1, 1, 0, -1], ![-6, 3, 9, -18], ![0, 3, 3, -9], ![-4, 4, 6, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2

def I13N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![-8, 1, 0, -1]] i)))

def SI13N3: IdealEqSpanCertificate' Table ![![13, 0, 0, 0], ![-8, 1, 0, -1]] 
 ![![13, 0, 0, 0], ![8, 1, 0, 0], ![1, 0, 1, 0], ![3, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![-8, 1, 0, -1], ![-6, 0, 9, -18], ![36, 3, 0, -9], ![16, 4, 6, -16]]]
  hmulB := by decide  
  f := ![![![643697, 48298, -1539720, 3030782], ![-625534, 2224040, -780, 0]], ![![406020, 30464, -971190, 1911689], ![-394555, 1402830, -492, 0]], ![![39621, 2972, -94763, 186532], ![-38492, 136880, -48, 0]], ![![148551, 11145, -355320, 699412], ![-144345, 513240, -180, 0]]]
  g := ![![![1, 0, 0, 0], ![-8, 13, 0, 0], ![-1, 0, 13, 0], ![-3, 0, 0, 13]], ![![-1, 1, 0, -1], ![3, 0, 9, -18], ![3, 3, 0, -9], ![2, 4, 6, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N3 : Nat.card (O ⧸ I13N3) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N3)

lemma isPrimeI13N3 : Ideal.IsPrime I13N3 := prime_ideal_of_norm_prime hp13.out _ NI13N3
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0], ![1, 1, 0, -1]] ![![13, 0, 0, 0], ![4, 1, 0, -1]]
  ![![-5, 1, 1, -2]] where
 M :=  ![![![169, 0, 0, 0], ![52, 13, 0, -13]], ![![13, 13, 0, -13], ![-18, 9, 3, -15]]]
 hmul := by decide  
 g :=  ![![![![-39, -13, -13, 26]], ![![-10, -10, -9, 22]]], ![![![-1, -7, -6, 16]], ![![6, -3, -3, 9]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-5, 1, 1, -2]] ![![13, 0, 0, 0], ![-5, 1, 0, -1]]
  ![![13, 0, 0, 0], ![4, 5, 0, -1]] where
 M :=  ![![![-65, 13, 13, -26], ![23, -7, 0, 4]]]
 hmul := by decide  
 g :=  ![![![![-5, 1, 1, -2], ![0, 0, 0, 0]], ![![-1, -4, 0, 1], ![9, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N2 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0], ![4, 5, 0, -1]] ![![13, 0, 0, 0], ![-8, 1, 0, -1]]
  ![![13, 0, 0, 0]] where
 M :=  ![![![169, 0, 0, 0], ![-104, 13, 0, -13]], ![![52, 65, 0, -13], ![-78, 0, 39, -78]]]
 hmul := by decide  
 g :=  ![![![![13, 0, 0, 0]], ![![-8, 1, 0, -1]]], ![![![4, 5, 0, -1]], ![![-6, 0, 3, -6]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2, I13N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
    exact isPrimeI13N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1 ⊙ MulI13N2)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0], ![-4, -5, -4, 8]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0], ![-4, -5, -4, 8]] 
 ![![17, 0, 0, 0], ![0, 17, 0, 0], ![16, 16, 1, 0], ![16, 1, 0, 1]] where
  M :=![![![17, 0, 0, 0], ![0, 17, 0, 0], ![0, 0, 17, 0], ![0, 0, 0, 17]], ![![-4, -5, -4, 8], ![-16, -8, -5, 4], ![-56, 27, 40, -103], ![-30, 16, 24, -62]]]
  hmulB := by decide  
  f := ![![![1421, 599, 342, -96], ![-629, 1666, 0, 0]], ![![-100, -40, -23, 4], ![51, -119, 0, 0]], ![![1244, 527, 301, -88], ![-541, 1456, 0, 0]], ![![1332, 562, 321, -91], ![-587, 1561, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-16, -16, 17, 0], ![-16, -1, 0, 17]], ![![-4, 3, -4, 8], ![0, 4, -5, 4], ![56, -30, 40, -103], ![34, -18, 24, -62]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [15, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 16], [0, 1]]
 g := ![![[14, 8], [4], [2], [1]],![[0, 9], [4], [2], [1]]]
 h' := ![![[11, 16], [4, 12], [8, 15], [2, 11], [0, 1]],![[0, 1], [0, 5], [3, 2], [4, 6], [11, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [13, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where 
  n := 2
  hpos := by decide  
  P := [15, 6, 1]
  hirr := P17P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![9275, 3444, 8830, -24820]
  a := ![-126, 117, 129, -275]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![15595, -6648, 8830, -24820]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0], ![-14, 5, 6, -12]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0, 0], ![-14, 5, 6, -12]] 
 ![![17, 0, 0, 0], ![0, 17, 0, 0], ![7, 16, 1, 0], ![16, 9, 0, 1]] where
  M :=![![![17, 0, 0, 0], ![0, 17, 0, 0], ![0, 0, 17, 0], ![0, 0, 0, 17]], ![![-14, 5, 6, -12], ![24, -8, 5, -6], ![44, -3, -40, 67], ![30, -4, -16, 28]]]
  hmulB := by decide  
  f := ![![![1453, -474, 570, -828], ![-510, -1326, 0, 0]], ![![-102, 34, -48, 72], ![51, 102, 0, 0]], ![![499, -162, 191, -276], ![-166, -450, 0, 0]], ![![1302, -424, 516, -751], ![-467, -1194, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-7, -16, 17, 0], ![-16, -9, 0, 17]], ![![8, 1, 6, -12], ![5, -2, 5, -6], ![-44, 2, -40, 67], ![-18, 0, -16, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [7, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 16], [0, 1]]
 g := ![![[3, 16], [13], [16], [1]],![[7, 1], [13], [16], [1]]]
 h' := ![![[13, 16], [2, 4], [5, 9], [10, 13], [0, 1]],![[0, 1], [3, 13], [3, 8], [9, 4], [13, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [6, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where 
  n := 2
  hpos := by decide  
  P := [7, 4, 1]
  hirr := P17P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-910, -96, -98, 20]
  a := ![-5, 6, 2, -11]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-32, 76, -98, 20]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0], ![-4, -5, -4, 8]] ![![17, 0, 0, 0], ![-14, 5, 6, -12]]
  ![![17, 0, 0, 0]] where
 M :=  ![![![289, 0, 0, 0], ![-238, 85, 102, -204]], ![![-68, -85, -68, 136], ![0, 0, -17, 34]]]
 hmul := by decide  
 g :=  ![![![![17, 0, 0, 0]], ![![-14, 5, 6, -12]]], ![![![-4, -5, -4, 8]], ![![0, 0, -1, 2]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0], ![-5, -5, -4, 8]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0], ![-5, -5, -4, 8]] 
 ![![19, 0, 0, 0], ![0, 19, 0, 0], ![14, 18, 1, 0], ![4, 6, 0, 1]] where
  M :=![![![19, 0, 0, 0], ![0, 19, 0, 0], ![0, 0, 19, 0], ![0, 0, 0, 19]], ![![-5, -5, -4, 8], ![-16, -9, -5, 4], ![-56, 27, 39, -103], ![-30, 16, 24, -63]]]
  hmulB := by decide  
  f := ![![![-155, -79, -39, 12], ![76, -209, 0, 0]], ![![161, 85, 43, -20], ![-57, 209, 0, 0]], ![![37, 21, 11, -8], ![-3, 44, 0, 0]], ![![19, 11, 6, -5], ![1, 22, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-14, -18, 19, 0], ![-4, -6, 0, 19]], ![![1, 1, -4, 8], ![2, 3, -5, 4], ![-10, -3, 39, -103], ![-6, -2, 24, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [18, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 18], [0, 1]]
 g := ![![[16, 11], [6, 6], [9], [1]],![[2, 8], [7, 13], [9], [1]]]
 h' := ![![[16, 18], [6, 12], [10, 5], [1, 16], [0, 1]],![[0, 1], [8, 7], [14, 14], [10, 3], [16, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [10, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where 
  n := 2
  hpos := by decide  
  P := [18, 3, 1]
  hirr := P19P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-2416, -432, 0, -509]
  a := ![-17, 16, 13, -37]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-20, 138, 0, -509]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0], ![-15, 5, 6, -12]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0, 0], ![-15, 5, 6, -12]] 
 ![![19, 0, 0, 0], ![0, 19, 0, 0], ![11, 18, 1, 0], ![2, 7, 0, 1]] where
  M :=![![![19, 0, 0, 0], ![0, 19, 0, 0], ![0, 0, 19, 0], ![0, 0, 0, 19]], ![![-15, 5, 6, -12], ![24, -9, 5, -6], ![44, -3, -41, 67], ![30, -4, -16, 27]]]
  hmulB := by decide  
  f := ![![![1978, -767, 786, -1140], ![-779, -2052, 0, 0]], ![![-327, 128, -132, 192], ![133, 342, 0, 0]], ![![833, -322, 331, -480], ![-328, -864, 0, 0]], ![![98, -37, 30, -41], ![-20, -90, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-11, -18, 19, 0], ![-2, -7, 0, 19]], ![![-3, -1, 6, -12], ![-1, -3, 5, -6], ![19, 14, -41, 67], ![8, 5, -16, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [18, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 18], [0, 1]]
 g := ![![[7, 17], [16, 16], [11], [1]],![[12, 2], [14, 3], [11], [1]]]
 h' := ![![[7, 18], [16, 6], [12, 15], [1, 7], [0, 1]],![[0, 1], [1, 13], [3, 4], [12, 12], [7, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [3, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where 
  n := 2
  hpos := by decide  
  P := [18, 12, 1]
  hirr := P19P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![3441, -1224, -4341, 8610]
  a := ![-31, 30, 41, -68]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![1788, 876, -4341, 8610]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0, 0], ![-5, -5, -4, 8]] ![![19, 0, 0, 0], ![-15, 5, 6, -12]]
  ![![19, 0, 0, 0]] where
 M :=  ![![![361, 0, 0, 0], ![-285, 95, 114, -228]], ![![-95, -95, -76, 152], ![19, 0, -19, 38]]]
 hmul := by decide  
 g :=  ![![![![19, 0, 0, 0]], ![![-15, 5, 6, -12]]], ![![![-5, -5, -4, 8]], ![![1, 0, -1, 2]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0], ![6, 1, 0, -1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0], ![6, 1, 0, -1]] 
 ![![23, 0, 0, 0], ![4, 1, 0, 0], ![7, 0, 1, 0], ![21, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0], ![0, 23, 0, 0], ![0, 0, 23, 0], ![0, 0, 0, 23]], ![![6, 1, 0, -1], ![-6, 14, 9, -18], ![36, 3, 14, -9], ![16, 4, 6, -2]]]
  hmulB := by decide  
  f := ![![![490375, -1137267, -728364, 1461027], ![14973, 1868244, -4416, 0]], ![![110594, -256493, -164271, 329512], ![3386, 421353, -996, 0]], ![![147911, -343035, -219697, 440691], ![4521, 563520, -1332, 0]], ![![447735, -1038374, -665028, 1333981], ![13666, 1705788, -4032, 0]]]
  g := ![![![1, 0, 0, 0], ![-4, 23, 0, 0], ![-7, 0, 23, 0], ![-21, 0, 0, 23]], ![![1, 1, 0, -1], ![11, 14, 9, -18], ![5, 3, 14, -9], ![0, 4, 6, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0], ![-10, 1, 0, -1]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0, 0], ![-10, 1, 0, -1]] 
 ![![23, 0, 0, 0], ![18, 1, 0, 0], ![21, 0, 1, 0], ![5, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0], ![0, 23, 0, 0], ![0, 0, 23, 0], ![0, 0, 0, 23]], ![![-10, 1, 0, -1], ![-6, -2, 9, -18], ![36, 3, -2, -9], ![16, 4, 6, -18]]]
  hmulB := by decide  
  f := ![![![1211127, 535121, -2270744, 4510559], ![-699407, 5802808, -920, 0]], ![![989936, 437389, -1856027, 3686774], ![-571664, 4743013, -752, 0]], ![![1103183, 487426, -2068355, 4108538], ![-637064, 5285610, -838, 0]], ![![263295, 116330, -493640, 980557], ![-152030, 1261480, -200, 0]]]
  g := ![![![1, 0, 0, 0], ![-18, 23, 0, 0], ![-21, 0, 23, 0], ![-5, 0, 0, 23]], ![![-1, 1, 0, -1], ![-3, -2, 9, -18], ![3, 3, -2, -9], ![-4, 4, 6, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0], ![6, 1, 0, -1]] ![![23, 0, 0, 0], ![6, 1, 0, -1]]
  ![![-1, 3, 3, -6]] where
 M :=  ![![![529, 0, 0, 0], ![138, 23, 0, -23]], ![![138, 23, 0, -23], ![14, 16, 3, -22]]]
 hmul := by decide  
 g :=  ![![![![-115, 69, 69, -138]], ![![-36, 22, 33, -64]]], ![![![-36, 22, 33, -64]], ![![-8, 5, 12, -23]]]]
 hle2 := by decide  
def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-1, 3, 3, -6]] ![![23, 0, 0, 0], ![-10, 1, 0, -1]]
  ![![23, 0, 0, 0], ![2, 12, 4, -9]] where
 M :=  ![![![-23, 69, 69, -138], ![4, -22, -15, 28]]]
 hmul := by decide  
 g :=  ![![![![-3, -9, -1, 3], ![23, 0, 0, 0]], ![![0, -2, -1, 2], ![2, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N2 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0], ![2, 12, 4, -9]] ![![23, 0, 0, 0], ![-10, 1, 0, -1]]
  ![![23, 0, 0, 0]] where
 M :=  ![![![529, 0, 0, 0], ![-230, 23, 0, -23]], ![![46, 276, 92, -207], ![-92, -46, 46, -92]]]
 hmul := by decide  
 g :=  ![![![![23, 0, 0, 0]], ![![-10, 1, 0, -1]]], ![![![2, 12, 4, -9]], ![![-4, -2, 2, -4]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N0, I23N1, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1 ⊙ MulI23N2)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0], ![10, 0, 1, -2]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0], ![10, 0, 1, -2]] 
 ![![29, 0, 0, 0], ![0, 29, 0, 0], ![2, 7, 1, 0], ![25, 18, 0, 1]] where
  M :=![![![29, 0, 0, 0], ![0, 29, 0, 0], ![0, 0, 29, 0], ![0, 0, 0, 29]], ![![10, 0, 1, -2], ![4, 11, 0, -1], ![-6, 12, 19, -18], ![0, 6, 4, 2]]]
  hmulB := by decide  
  f := ![![![-9, 0, -1, 2], ![29, 0, 0, 0]], ![![-32, -87, 0, 8], ![0, 232, 0, 0]], ![![-8, -21, 0, 2], ![1, 56, 0, 0]], ![![-19, -54, 0, 5], ![0, 144, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-2, -7, 29, 0], ![-25, -18, 0, 29]], ![![2, 1, 1, -2], ![1, 1, 0, -1], ![14, 7, 19, -18], ![-2, -2, 4, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [25, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 28], [0, 1]]
 g := ![![[5, 7], [6], [21, 4], [20, 1]],![[0, 22], [6], [14, 25], [11, 28]]]
 h' := ![![[20, 28], [4, 23], [26, 21], [22, 27], [0, 1]],![[0, 1], [0, 6], [11, 8], [11, 2], [20, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [2, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where 
  n := 2
  hpos := by decide  
  P := [25, 9, 1]
  hirr := P29P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![377, 216, 260, -595]
  a := ![-16, 16, 17, -35]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![508, 314, 260, -595]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0], ![-11, 0, 1, -2]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0, 0], ![-11, 0, 1, -2]] 
 ![![29, 0, 0, 0], ![0, 29, 0, 0], ![10, 20, 1, 0], ![25, 10, 0, 1]] where
  M :=![![![29, 0, 0, 0], ![0, 29, 0, 0], ![0, 0, 29, 0], ![0, 0, 0, 29]], ![![-11, 0, 1, -2], ![4, -10, 0, -1], ![-6, 12, -2, -18], ![0, 6, 4, -19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![12, -29, 0, -3], ![0, -87, 0, 0]], ![![9, -20, 0, -2], ![1, -60, 0, 0]], ![![5, -10, 0, -1], ![0, -30, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-10, -20, 29, 0], ![-25, -10, 0, 29]], ![![1, 0, 1, -2], ![1, 0, 0, -1], ![16, 8, -2, -18], ![15, 4, 4, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [24, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 28], [0, 1]]
 g := ![![[15, 23], [1], [24, 16], [17, 1]],![[0, 6], [1], [6, 13], [5, 28]]]
 h' := ![![[17, 28], [21, 9], [4, 28], [27, 4], [0, 1]],![[0, 1], [0, 20], [16, 1], [8, 25], [17, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [7, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where 
  n := 2
  hpos := by decide  
  P := [24, 12, 1]
  hirr := P29P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![757, -118, -383, 876]
  a := ![-11, 13, 14, -24]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-597, -42, -383, 876]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0, 0], ![10, 0, 1, -2]] ![![29, 0, 0, 0], ![-11, 0, 1, -2]]
  ![![29, 0, 0, 0]] where
 M :=  ![![![841, 0, 0, 0], ![-319, 0, 29, -58]], ![![290, 0, 29, -58], ![-116, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![29, 0, 0, 0]], ![![-11, 0, 1, -2]]], ![![![10, 0, 1, -2]], ![![-4, 0, 0, 0]]]]
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


lemma PB42I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 29 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 29 (by omega)
  rfl

def PB42I0 : PrimesBelowBoundCertificateInterval' O 1 29 42 where
  m := 10
  g := ![4, 4, 2, 2, 2, 4, 2, 2, 4, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
  hP := PB42I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N0, I3N1, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2, I13N3]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N0, I23N1, I23N1]
    · exact ![I29N0, I29N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2]
    · exact ![3, 3, 3, 3]
    · exact ![25, 25]
    · exact ![49, 49]
    · exact ![121, 121]
    · exact ![13, 13, 13, 13]
    · exact ![289, 289]
    · exact ![361, 361]
    · exact ![23, 23, 23, 23]
    · exact ![841, 841]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N1
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
      exact NI13N3
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N0
      exact NI23N1
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
  Il := ![[I2N0, I2N0, I2N1, I2N1], [I3N0, I3N0, I3N1, I3N1], [I5N0, I5N1], [], [], [I13N0, I13N1, I13N2, I13N3], [], [], [I23N0, I23N0, I23N1, I23N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
