/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF3_1_24843_1.RI3_1_24843_1
import LeanBridge.IdealArithmetic.Generation.ClassGroupGeneration
import LeanBridge.IdealArithmetic.IdealArithmetic
import LeanBridge.IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 0, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 0, 1]] 
 ![![2, 0, 0], ![0, 2, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 0, 1], ![30, 0, 1], ![20, 10, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 2]], ![![0, 0, 1], ![15, 0, 1], ![10, 5, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]],![[1]]]
 h' := ![![[1, 1], [0, 1]],![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where 
  n := 2
  hpos := by decide  
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-1138, 640, 19]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide  
  g := ![-569, 320, 19]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 0], ![-1, 0, 3], ![30, 0, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 2], ![0, -1, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-2, 0, 3], ![14, 0, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 0, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0]] where
 M :=  ![![![4, 0, 0], ![2, 2, 0]], ![![0, 0, 2], ![30, 0, 2]]]
 hmul := by decide  
 g :=  ![![![![2, 0, 0]], ![![1, 1, 0]]], ![![![0, 0, 1]], ![![15, 0, 1]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 0, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![0, 0, 1]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![0, 0, 1], ![30, 0, 1], ![20, 10, 1]]]
  hmulB := by decide  
  f := ![![![-9, 10, 0], ![0, 3, -3]], ![![-6, 7, 0], ![0, 2, -2]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![0, 0, 3]], ![![0, 0, 1], ![10, 0, 1], ![0, 10, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 0, 1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 0, 1]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 0, 1], ![30, -1, 1], ![20, 10, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![10, 0, 1], ![-2, -1, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![-2, 0, 3]], ![![-1, 0, 1], ![10, -1, 1], ![0, 10, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![0, 0, 1]] ![![3, 0, 0], ![0, 0, 1]]
  ![![3, 0, 0], ![-1, 1, 1]] where
 M :=  ![![![9, 0, 0], ![0, 0, 3]], ![![0, 0, 3], ![20, 10, 1]]]
 hmul := by decide  
 g :=  ![![![![3, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0]]], ![![![0, 0, 1], ![0, 0, 0]], ![![7, 3, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-1, 1, 1]] ![![3, 0, 0], ![-1, 0, 1]]
  ![![3, 0, 0]] where
 M :=  ![![![9, 0, 0], ![-3, 0, 3]], ![![-3, 3, 3], ![51, 9, 0]]]
 hmul := by decide  
 g :=  ![![![![3, 0, 0]], ![![-1, 0, 1]]], ![![![-1, 1, 1]], ![![17, 3, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![0, 0, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![0, 0, 1]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![0, 0, 1], ![30, 0, 1], ![20, 10, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 5]], ![![0, 0, 1], ![6, 0, 1], ![4, 2, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [3, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 4], [0, 1]]
 g := ![![[], [1]],![[], [1]]]
 h' := ![![[0, 4], [2], [0, 1]],![[0, 1], [2], [0, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [0, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where 
  n := 2
  hpos := by decide  
  P := [3, 0, 1]
  hirr := P5P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![81740, 44890, 4099]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide  
  g := ![16348, 8978, 4099]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-1, 1, 0]] 
 ![![5, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-1, 1, 0], ![-1, -2, 3], ![30, 0, 0]]]
  hmulB := by decide  
  f := ![![![-11, -24, 36], ![0, -60, 0]], ![![-8, -18, 27], ![1, -45, 0]], ![![-9, -19, 29], ![-1, -48, 0]]]
  g := ![![![1, 0, 0], ![-4, 5, 0], ![-4, 0, 5]], ![![-1, 1, 0], ![-1, -2, 3], ![6, 0, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![0, 0, 1]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![5, 0, 0]] where
 M :=  ![![![25, 0, 0], ![-5, 5, 0]], ![![0, 0, 5], ![30, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![5, 0, 0]], ![![-1, 1, 0]]], ![![![0, 0, 1]], ![![6, 0, 0]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![-1, -1, 3], ![30, 0, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 3], ![0, -7, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![-2, -2, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![-2, 0, 7]], ![![0, 1, 0], ![-1, -1, 3], ![4, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0], ![2, 2, 1]] where
 M :=  ![![![49, 0, 0], ![0, 7, 0]], ![![0, 7, 0], ![-1, -1, 3]]]
 hmul := by decide  
 g :=  ![![![![5, -2, -1], ![7, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-1, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![2, 2, 1]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0]] where
 M :=  ![![![49, 0, 0], ![0, 7, 0]], ![![14, 14, 7], ![28, 0, 7]]]
 hmul := by decide  
 g :=  ![![![![7, 0, 0]], ![![0, 1, 0]]], ![![![2, 2, 1]], ![![4, 0, 1]]]]
 hle2 := by decide  

def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![1, -1, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![1, -1, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![1, 10, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![1, -1, 1], ![31, 2, -2], ![-10, 10, 1]]]
  hmulB := by decide  
  f := ![![![0, 1, -1], ![11, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -10, 11]], ![![0, -1, 1], ![3, 2, -2], ![-1, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 8, 1] where
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
 g := ![![[7, 5], [6, 9], [1]],![[0, 6], [0, 2], [1]]]
 h' := ![![[3, 10], [1, 7], [2, 3], [0, 1]],![[0, 1], [0, 4], [0, 8], [3, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [6, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where 
  n := 2
  hpos := by decide  
  P := [9, 8, 1]
  hirr := P11P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-614, 680, -64]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide  
  g := ![-50, 120, -64]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![2, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![2, 1, 0]] 
 ![![11, 0, 0], ![2, 1, 0], ![10, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![2, 1, 0], ![-1, 1, 3], ![30, 0, 3]]]
  hmulB := by decide  
  f := ![![![-47, 48, 144], ![0, -528, 0]], ![![-8, 8, 24], ![1, -88, 0]], ![![-44, 43, 131], ![7, -480, 0]]]
  g := ![![![1, 0, 0], ![-2, 11, 0], ![-10, 0, 11]], ![![0, 1, 0], ![-3, 1, 3], ![0, 0, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![1, -1, 1]] ![![11, 0, 0], ![2, 1, 0]]
  ![![11, 0, 0]] where
 M :=  ![![![121, 0, 0], ![22, 11, 0]], ![![11, -11, 11], ![33, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![11, 0, 0]], ![![2, 1, 0]]], ![![![1, -1, 1]], ![![3, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![0, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![0, 1, 0]] 
 ![![13, 0, 0], ![0, 1, 0], ![4, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![0, 1, 0], ![-1, -1, 3], ![30, 0, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 3], ![0, -13, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![-4, -4, 0]]]
  g := ![![![1, 0, 0], ![0, 13, 0], ![-4, 0, 13]], ![![0, 1, 0], ![-1, -1, 3], ![2, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![0, 1, 0]] ![![13, 0, 0], ![0, 1, 0]]
  ![![13, 0, 0], ![4, 4, 1]] where
 M :=  ![![![169, 0, 0], ![0, 13, 0]], ![![0, 13, 0], ![-1, -1, 3]]]
 hmul := by decide  
 g :=  ![![![![9, -4, -1], ![13, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-1, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  
def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![4, 4, 1]] ![![13, 0, 0], ![0, 1, 0]]
  ![![13, 0, 0]] where
 M :=  ![![![169, 0, 0], ![0, 13, 0]], ![![52, 52, 13], ![26, 0, 13]]]
 hmul := by decide  
 g :=  ![![![![13, 0, 0]], ![![0, 1, 0]]], ![![![4, 4, 1]], ![![2, 0, 1]]]]
 hle2 := by decide  

def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N0, I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N0
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![8, 7, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![8, 7, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![8, 7, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![8, 7, 1], ![23, 1, 22], ![230, 10, 16]]]
  hmulB := by decide  
  f := ![![![-7, -7, -1], ![17, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -7, 17]], ![![0, 0, 1], ![-9, -9, 22], ![6, -6, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [15, 4, 1] where
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
 g := ![![[15, 8], [8], [16], [1]],![[0, 9], [8], [16], [1]]]
 h' := ![![[13, 16], [3, 5], [2, 5], [2, 13], [0, 1]],![[0, 1], [0, 12], [16, 12], [1, 4], [13, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [14, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where 
  n := 2
  hpos := by decide  
  P := [15, 4, 1]
  hirr := P17P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![200, 90, -9]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide  
  g := ![16, 9, -9]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-5, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-5, 1, 0]] 
 ![![17, 0, 0], ![12, 1, 0], ![1, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-5, 1, 0], ![-1, -6, 3], ![30, 0, -4]]]
  hmulB := by decide  
  f := ![![![-129, -780, 390], ![0, -2210, 0]], ![![-90, -546, 273], ![1, -1547, 0]], ![![-7, -46, 23], ![2, -130, 0]]]
  g := ![![![1, 0, 0], ![-12, 17, 0], ![-1, 0, 17]], ![![-1, 1, 0], ![4, -6, 3], ![2, 0, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![8, 7, 1]] ![![17, 0, 0], ![-5, 1, 0]]
  ![![17, 0, 0]] where
 M :=  ![![![289, 0, 0], ![-85, 17, 0]], ![![136, 119, 17], ![-17, -34, 17]]]
 hmul := by decide  
 g :=  ![![![![17, 0, 0]], ![![-5, 1, 0]]], ![![![8, 7, 1]], ![![-1, -2, 1]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [16, 12, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 3, 18], [3, 15, 1], [0, 1]]
 g := ![![[12, 3, 1], [3, 15, 7], [1, 1], []],![[7, 17, 1, 13], [17, 0, 2, 3], [7, 16], [14, 1]],![[18, 0, 6, 16], [8, 17, 2, 16], [7, 9], [12, 1]]]
 h' := ![![[17, 3, 18], [9, 18, 18], [3, 10, 8], [0, 0, 1], [0, 1]],![[3, 15, 1], [3, 3, 5], [9, 1, 15], [8, 13, 15], [17, 3, 18]],![[0, 1], [18, 17, 15], [13, 8, 15], [7, 6, 3], [3, 15, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 15], []]
 b := ![[], [9, 15, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where 
  n := 3
  hpos := by decide  
  P := [16, 12, 18, 1]
  hirr := P19P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![749873, 123082, 49552]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide  
  g := ![39467, 6478, 2608]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![0, 7, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![0, 7, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 7, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![0, 7, 1], ![23, -7, 22], ![230, 10, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, -6, -1], ![23, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -7, 23]], ![![0, 0, 1], ![1, -7, 22], ![10, -2, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [22, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 22], [0, 1]]
 g := ![![[11, 4], [14, 12], [19, 6], [1]],![[9, 19], [8, 11], [16, 17], [1]]]
 h' := ![![[11, 22], [14, 21], [19, 9], [1, 11], [0, 1]],![[0, 1], [15, 2], [3, 14], [7, 12], [11, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [8, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where 
  n := 2
  hpos := by decide  
  P := [22, 12, 1]
  hirr := P23P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-621, 200, -24]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide  
  g := ![-27, 16, -24]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![1, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![1, 1, 0]] 
 ![![23, 0, 0], ![1, 1, 0], ![15, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![1, 1, 0], ![-1, 0, 3], ![30, 0, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![23, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 2], ![0, -15, 0]]]
  g := ![![![1, 0, 0], ![-1, 23, 0], ![-15, 0, 23]], ![![0, 1, 0], ![-2, 0, 3], ![0, 0, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![0, 7, 1]] ![![23, 0, 0], ![1, 1, 0]]
  ![![23, 0, 0]] where
 M :=  ![![![529, 0, 0], ![23, 23, 0]], ![![0, 161, 23], ![23, 0, 23]]]
 hmul := by decide  
 g :=  ![![![![23, 0, 0]], ![![1, 1, 0]]], ![![![0, 7, 1]], ![![1, 0, 1]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-12, -7, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-12, -7, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![17, 22, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-12, -7, 1], ![37, -5, -20], ![-190, 10, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -22, 29]], ![![-1, -1, 1], ![13, 15, -20], ![4, 14, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [14, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 28], [0, 1]]
 g := ![![[6, 1], [1], [2, 25], [3, 1]],![[9, 28], [1], [19, 4], [6, 28]]]
 h' := ![![[3, 28], [16, 1], [1, 28], [16, 24], [0, 1]],![[0, 1], [19, 28], [27, 1], [1, 5], [3, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [24, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where 
  n := 2
  hpos := by decide  
  P := [14, 26, 1]
  hirr := P29P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![325, 337, 159]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide  
  g := ![-82, -109, 159]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-9, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-9, 1, 0]] 
 ![![29, 0, 0], ![20, 1, 0], ![18, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-9, 1, 0], ![-1, -10, 3], ![30, 0, -8]]]
  hmulB := by decide  
  f := ![![![-79, -800, 240], ![0, -2320, 0]], ![![-54, -550, 165], ![1, -1595, 0]], ![![-45, -497, 149], ![13, -1440, 0]]]
  g := ![![![1, 0, 0], ![-20, 29, 0], ![-18, 0, 29]], ![![-1, 1, 0], ![5, -10, 3], ![6, 0, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![-12, -7, 1]] ![![29, 0, 0], ![-9, 1, 0]]
  ![![29, 0, 0]] where
 M :=  ![![![841, 0, 0], ![-261, 29, 0]], ![![-348, -203, 29], ![145, 58, -29]]]
 hmul := by decide  
 g :=  ![![![![29, 0, 0]], ![![-9, 1, 0]]], ![![![-12, -7, 1]], ![![5, 2, -1]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![4, 1, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![4, 1, 0]] 
 ![![31, 0, 0], ![4, 1, 0], ![6, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![4, 1, 0], ![-1, 3, 3], ![30, 0, 5]]]
  hmulB := by decide  
  f := ![![![-135, 408, 408], ![0, -4216, 0]], ![![-17, 51, 51], ![1, -527, 0]], ![![-30, 78, 79], ![30, -816, 0]]]
  g := ![![![1, 0, 0], ![-4, 31, 0], ![-6, 0, 31]], ![![0, 1, 0], ![-1, 3, 3], ![0, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![7, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![7, 1, 0]] 
 ![![31, 0, 0], ![7, 1, 0], ![27, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![7, 1, 0], ![-1, 6, 3], ![30, 0, 8]]]
  hmulB := by decide  
  f := ![![![-260, 1566, 783], ![0, -8091, 0]], ![![-58, 348, 174], ![1, -1798, 0]], ![![-226, 1364, 682], ![-2, -7047, 0]]]
  g := ![![![1, 0, 0], ![-7, 31, 0], ![-27, 0, 31]], ![![0, 1, 0], ![-4, 6, 3], ![-6, 0, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-11, 1, 0]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-11, 1, 0]] 
 ![![31, 0, 0], ![20, 1, 0], ![28, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-11, 1, 0], ![-1, -12, 3], ![30, 0, -10]]]
  hmulB := by decide  
  f := ![![![-223, -2688, 672], ![0, -6944, 0]], ![![-143, -1728, 432], ![1, -4464, 0]], ![![-200, -2428, 607], ![4, -6272, 0]]]
  g := ![![![1, 0, 0], ![-20, 31, 0], ![-28, 0, 31]], ![![-1, 1, 0], ![5, -12, 3], ![10, 0, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![4, 1, 0]] ![![31, 0, 0], ![7, 1, 0]]
  ![![31, 0, 0], ![9, -7, 1]] where
 M :=  ![![![961, 0, 0], ![217, 31, 0]], ![![124, 31, 0], ![27, 10, 3]]]
 hmul := by decide  
 g :=  ![![![![22, 7, -1], ![31, 0, 0]], ![![-2, 8, -1], ![31, 0, 0]]], ![![![-5, 8, -1], ![31, 0, 0]], ![![0, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![9, -7, 1]] ![![31, 0, 0], ![-11, 1, 0]]
  ![![31, 0, 0]] where
 M :=  ![![![961, 0, 0], ![-341, 31, 0]], ![![279, -217, 31], ![-62, 93, -31]]]
 hmul := by decide  
 g :=  ![![![![31, 0, 0]], ![![-11, 1, 0]]], ![![![9, -7, 1]], ![![-2, 3, -1]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB45I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)
  rfl

def PB45I0 : PrimesBelowBoundCertificateInterval' O 1 31 45 where
  m := 11
  g := ![2, 3, 2, 3, 2, 3, 2, 1, 2, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB45I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N0, I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N0, I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1, I31N2]
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
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![4, 2]
    · exact ![3, 3, 3]
    · exact ![25, 5]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![13, 13, 13]
    · exact ![289, 17]
    · exact ![6859]
    · exact ![529, 23]
    · exact ![841, 29]
    · exact ![31, 31, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N0
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  Il := ![[I2N0, I2N1], [I3N0, I3N0, I3N1], [I5N0, I5N1], [I7N0, I7N0, I7N0], [I11N1], [I13N0, I13N0, I13N0], [I17N1], [], [I23N1], [I29N1], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
