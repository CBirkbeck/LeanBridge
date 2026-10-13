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

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0]] 
 ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![1, 0, 1, 1, 0, 0], ![1, 1, 1, 0, 1, 0], ![1, 1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 2]], ![![1, 0, 1, 1, 0, 0], ![0, 1, 0, 1, 5, 0], ![0, 0, 1, 0, 1, 1], ![-5, 0, 10, 1, 5, 1], ![-1, -1, 2, 2, 2, 1], ![-5, -1, 5, 2, 15, 2]]]
  hmulB := by decide  
  f := ![![![0, 0, 0, -1, 1, 1], ![2, 0, -2, 0, 0, 0]], ![![0, 0, 0, -1, -5, 0], ![0, 2, 0, 0, 0, 0]], ![![0, 0, 0, 0, -1, -1], ![0, 0, 2, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0]], ![![0, 0, 0, -1, -2, 0], ![1, 1, 0, 0, 0, 0]], ![![0, 0, 0, -1, -2, 1], ![1, 1, -1, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![-1, 0, -1, 2, 0, 0], ![-1, -1, -1, 0, 2, 0], ![-1, -1, 0, 0, 0, 2]], ![![0, 0, 0, 1, 0, 0], ![-3, -2, -3, 1, 5, 0], ![-1, -1, 0, 0, 1, 1], ![-6, -3, 2, 1, 5, 1], ![-3, -2, -1, 2, 2, 1], ![-12, -9, -6, 2, 15, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 3 2 1 [1, 0, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [1, 1, 1], [0, 1]]
 g := ![![[]], ![[1, 1]], ![[1, 1]]]
 h' := ![![[0, 0, 1], [0, 1]], ![[1, 1, 1], [0, 0, 1]], ![[0, 1], [1, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], []]
 b := ![[], [0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 3
  hpos := by decide
  P := [1, 0, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-243405, 13050, -39331, 9769, -2332, -35188]
  a := ![-64, 1, -1, 1, 1, -3]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-107827, 25285, -23384, 9769, -2332, -35188]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 8 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0]] ![![2, 0, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0]]
  ![![2, 0, 0, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0, 0], ![2, 0, 2, 2, 0, 0]], ![![2, 0, 2, 2, 0, 0], ![-4, 0, 12, 2, 6, 2]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0, 0]], ![![1, 0, 1, 1, 0, 0]]], ![![![1, 0, 1, 1, 0, 0]], ![![-2, 0, 6, 1, 3, 1]]]]
 hle2 := by decide  

def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0, 0], ![1, -1, 0, -1, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0, 0], ![1, -1, 0, -1, 0, 0]] 
 ![![3, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0], ![2, 1, 0, 1, 0, 0], ![0, 1, 1, 0, 1, 0], ![1, 2, 2, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0], ![0, 0, 0, 3, 0, 0], ![0, 0, 0, 0, 3, 0], ![0, 0, 0, 0, 0, 3]], ![![1, -1, 0, -1, 0, 0], ![0, 1, -5, 0, -5, 0], ![0, 0, 1, -1, 0, -1], ![5, 0, -10, 1, -10, 0], ![0, 1, 0, -2, 1, -2], ![10, 0, -15, 0, -20, 1]]]
  hmulB := by decide  
  f := ![![![2, -1, 1, -2, 0, -1], ![-3, 0, -3, 0, 0, 0]], ![![-2, 3, 1, 1, 0, -1], ![6, 0, -3, 0, 0, 0]], ![![0, 0, 0, 1, 0, 1], ![0, 0, 3, 0, 0, 0]], ![![0, 1, 1, 0, 0, -1], ![2, 0, -3, 0, 0, 0]], ![![0, 0, 2, 0, 2, 0], ![0, 1, 0, 0, 0, 0]], ![![0, 1, 1, 0, 0, 0], ![1, 0, -1, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![-2, -1, 0, 3, 0, 0], ![0, -1, -1, 0, 3, 0], ![-1, -2, -2, 0, 0, 3]], ![![1, 0, 0, -1, 0, 0], ![0, 2, 0, 0, -5, 0], ![1, 1, 1, -1, 0, -1], ![1, 3, 0, 1, -10, 0], ![2, 2, 1, -2, 1, -2], ![3, 6, 1, 0, -20, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [2, 0, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 0, 2], [1, 2, 1], [0, 1]]
 g := ![![[1]], ![[0, 2, 1, 2]], ![[2, 1, 2, 1]]]
 h' := ![![[1, 0, 2], [0, 1]], ![[1, 2, 1], [1, 0, 2]], ![[0, 1], [1, 2, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 2], []]
 b := ![[], [2, 1, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [2, 0, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-28184, -6316, 34515, 9527, 65010, 10410]
  a := ![0, -1, -1, 1, 19, 1]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19216, -33891, -17105, 9527, 65010, 10410]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0, 0], ![-1, -1, 0, -1, 0, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0, 0], ![-1, -1, 0, -1, 0, 0]] 
 ![![3, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0], ![1, 1, 0, 1, 0, 0], ![0, 2, 1, 0, 1, 0], ![2, 2, 1, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0], ![0, 0, 0, 3, 0, 0], ![0, 0, 0, 0, 3, 0], ![0, 0, 0, 0, 0, 3]], ![![-1, -1, 0, -1, 0, 0], ![0, -1, -5, 0, -5, 0], ![0, 0, -1, -1, 0, -1], ![5, 0, -10, -1, -10, 0], ![0, 1, 0, -2, -1, -2], ![10, 0, -15, 0, -20, -1]]]
  hmulB := by decide  
  f := ![![![2, 1, 1, 2, 0, 1], ![3, 0, 3, 0, 0, 0]], ![![0, 1, 2, 2, 0, 2], ![0, 0, 6, 0, 0, 0]], ![![0, 0, 0, -1, 0, -1], ![0, 0, -3, 0, 0, 0]], ![![0, 0, 1, 1, 0, 1], ![-1, 0, 3, 0, 0, 0]], ![![0, 1, 3, 1, 2, 1], ![0, 1, 3, 0, 0, 0]], ![![0, 0, 2, 1, 0, 2], ![-2, 0, 5, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![-1, -1, 0, 3, 0, 0], ![0, -2, -1, 0, 3, 0], ![-2, -2, -1, 0, 0, 3]], ![![0, 0, 0, -1, 0, 0], ![0, 3, 0, 0, -5, 0], ![1, 1, 0, -1, 0, -1], ![2, 7, 0, -1, -10, 0], ![2, 3, 1, -2, -1, -2], ![4, 14, 2, 0, -20, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P1 : CertificateIrreducibleZModOfList' 3 3 2 1 [1, 2, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 1, 2], [0, 1, 1], [0, 1]]
 g := ![![[1]], ![[2, 1, 1, 2]], ![[0, 2, 2, 1]]]
 h' := ![![[2, 1, 2], [0, 1]], ![[0, 1, 1], [2, 1, 2]], ![[0, 1], [0, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 2], []]
 b := ![[], [2, 2, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N1 : CertifiedPrimeIdeal' SI3N1 3 where
  n := 3
  hpos := by decide
  P := [1, 2, 1, 1]
  hirr := P3P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-555, -1146, 994, 2104, 204, 1570]
  a := ![-1, 3, -1, 0, 1, 2]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1933, -2266, -260, 2104, 204, 1570]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N1 B_one_repr
lemma NI3N1 : Nat.card (O ⧸ I3N1) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0, 0], ![1, -1, 0, -1, 0, 0]] ![![3, 0, 0, 0, 0, 0], ![-1, -1, 0, -1, 0, 0]]
  ![![3, 0, 0, 0, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0, 0], ![-3, -3, 0, -3, 0, 0]], ![![3, -3, 0, -3, 0, 0], ![-6, 0, 15, 0, 15, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0, 0]], ![![-1, -1, 0, -1, 0, 0]]], ![![![1, -1, 0, -1, 0, 0]], ![![-2, 0, 5, 0, 5, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 0, 0, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![0, 1, 0, 0, 0, 0]] 
 ![![5, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 5, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 5, 0], ![0, 0, 0, 0, 0, 1]] where
  M :=![![![0, 1, 0, 0, 0, 0], ![0, 0, 5, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 5, 0], ![0, 0, 0, 0, 0, 1], ![-5, 0, 10, 0, 5, 0]]]
  hmulB := by decide  
  f := ![![![0, 2, 0, 1, 0, -1]], ![![1, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0, 0]], ![![0, 0, 0, 1, 0, 0]], ![![0, 0, 0, 0, 1, 0]]]
  g := ![![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![-1, 0, 2, 0, 1, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [3, 3, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4, 2], [1, 0, 3], [0, 1]]
 g := ![![[2, 0, 1], []], ![[0, 3], [1, 4]], ![[2, 3, 2, 3], [0, 4]]]
 h' := ![![[4, 4, 2], [0, 0, 1], [0, 1]], ![[1, 0, 3], [3, 2], [4, 4, 2]], ![[0, 1], [1, 3, 4], [1, 0, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 3], []]
 b := ![[], [3, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [3, 3, 0, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1825, -338, 1140, -112, -1100, 116]
  a := ![13, -1, 1, 1, -4, -1]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![365, -338, 228, -112, -220, 116]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 125 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![0, 1, 0, 0, 0, 0]] ![![0, 1, 0, 0, 0, 0]]
  ![![5, 0, 0, 0, 0, 0]] where
 M := ![![![0, 0, 5, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![0, 0, 1, 0, 0, 0]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0], ![3, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0, 0], ![0, 7, 0, 0, 0, 0], ![0, 0, 7, 0, 0, 0], ![0, 0, 0, 7, 0, 0], ![0, 0, 0, 0, 7, 0], ![0, 0, 0, 0, 0, 7]], ![![2, 1, 0, 0, 0, 0], ![0, 2, 5, 0, 0, 0], ![0, 0, 2, 1, 0, 0], ![0, 0, 0, 2, 5, 0], ![0, 0, 0, 0, 2, 1], ![-5, 0, 10, 0, 5, 2]]]
  hmulB := by decide  
  f := ![![![5, -2, 22, 56, 140, 20], ![-14, 14, -112, -140, -140, 0]], ![![-2, -13, -34, 14, 56, 8], ![8, 42, 14, -56, -56, 0]], ![![-2, -4, 1, 20, 56, 8], ![8, 10, -28, -56, -56, 0]], ![![1, -2, 8, 23, 64, 12], ![-2, 8, -48, -56, -84, 0]], ![![1, -2, 8, 24, 59, 8], ![-2, 8, -48, -60, -56, 0]], ![![-1, -2, 1, 8, 20, 3], ![4, 5, -16, -20, -20, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-2, 7, 0, 0, 0, 0], ![-2, 0, 7, 0, 0, 0], ![-3, 0, 0, 7, 0, 0], ![-3, 0, 0, 0, 7, 0], ![-1, 0, 0, 0, 0, 7]], ![![0, 1, 0, 0, 0, 0], ![-2, 2, 5, 0, 0, 0], ![-1, 0, 2, 1, 0, 0], ![-3, 0, 0, 2, 5, 0], ![-1, 0, 0, 0, 2, 1], ![-6, 0, 10, 0, 5, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0], ![4, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0, 0], ![0, 7, 0, 0, 0, 0], ![0, 0, 7, 0, 0, 0], ![0, 0, 0, 7, 0, 0], ![0, 0, 0, 0, 7, 0], ![0, 0, 0, 0, 0, 7]], ![![-2, 1, 0, 0, 0, 0], ![0, -2, 5, 0, 0, 0], ![0, 0, -2, 1, 0, 0], ![0, 0, 0, -2, 5, 0], ![0, 0, 0, 0, -2, 1], ![-5, 0, 10, 0, 5, -2]]]
  hmulB := by decide  
  f := ![![![23, -27, 46, 13, 0, -20], ![77, -56, 21, 56, 140, 0]], ![![19, -17, 24, 14, -8, -16], ![64, -28, 14, 56, 112, 0]], ![![6, 0, 1, 4, -4, -8], ![20, 10, 28, 28, 56, 0]], ![![14, -13, 20, 6, 4, -12], ![47, -22, 15, 28, 84, 0]], ![![9, -10, 18, 5, -1, -8], ![30, -20, 13, 24, 56, 0]], ![![18, -20, 34, 11, 0, -17], ![60, -40, 19, 48, 120, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-5, 7, 0, 0, 0, 0], ![-2, 0, 7, 0, 0, 0], ![-4, 0, 0, 7, 0, 0], ![-3, 0, 0, 0, 7, 0], ![-6, 0, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0, 0], ![0, -2, 5, 0, 0, 0], ![0, 0, -2, 1, 0, 0], ![-1, 0, 0, -2, 5, 0], ![0, 0, 0, 0, -2, 1], ![-4, 0, 10, 0, 5, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]]
  ![![4, -2, 1, -1, -2, 1]] where
 M := ![![![49, 0, 0, 0, 0, 0], ![14, 7, 0, 0, 0, 0]], ![![14, 7, 0, 0, 0, 0], ![4, 4, 5, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![35, 21, 14, 7, -14, -14]], ![![20, 11, -1, 4, -9, -6]]], ![![![20, 11, -1, 4, -9, -6]], ![![10, 6, -1, 1, -4, -3]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![4, -2, 1, -1, -2, 1]] ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]]
  ![![7, 0, 0, 0, 0, 0], ![1, -2, 2, -2, 0, 0]] where
 M := ![![![28, -14, 7, -7, -14, 7], ![3, 0, 2, -1, -4, 0]]]
 hmul := by decide  
 g := ![![![![24, -43, 54, -49, 14, -5], ![-140, 7, -21, 0, 0, 0]], ![![2, -4, 13, -7, 10, -2], ![-11, 6, -7, 0, 0, 0]]]]
 hle2 := by decide  
def MulI7N2 : IdealMulLeCertificate' Table 
  ![![7, 0, 0, 0, 0, 0], ![1, -2, 2, -2, 0, 0]] ![![7, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]]
  ![![5, -3, 2, -1, -2, 2]] where
 M := ![![![49, 0, 0, 0, 0, 0], ![-14, 7, 0, 0, 0, 0]], ![![7, -14, 14, -14, 0, 0], ![-2, 5, -14, 6, -10, 0]]]
 hmul := by decide  
 g := ![![![![28, 14, 7, 7, -14, -7]], ![![-3, 0, -2, -1, 4, 0]]], ![![![-2, -8, -9, -1, -4, 5]], ![![-3, 2, 4, -1, 4, -2]]]]
 hle2 := by decide  

def MulI7N3 : IdealMulLeCertificate' Table 
  ![![5, -3, 2, -1, -2, 2]] ![![7, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]]
  ![![7, 0, 0, 0, 0, 0], ![-3, 9, -3, 2, 1, -3]] where
 M := ![![![35, -21, 14, -7, -14, 14], ![-20, 11, 1, 4, 9, -6]]]
 hmul := by decide  
 g := ![![![![5, -3, 2, -1, -2, 2], ![0, 0, 0, 0, 0, 0]], ![![-2, -1, 1, 0, 1, 0], ![2, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N4 : IdealMulLeCertificate' Table 
  ![![7, 0, 0, 0, 0, 0], ![-3, 9, -3, 2, 1, -3]] ![![7, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]]
  ![![7, 0, 0, 0, 0, 0]] where
 M := ![![![49, 0, 0, 0, 0, 0], ![-14, 7, 0, 0, 0, 0]], ![![-21, 63, -21, 14, 7, -21], ![21, -21, 21, -7, -7, 7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0, 0, 0, 0]], ![![-2, 1, 0, 0, 0, 0]]], ![![![-3, 9, -3, 2, 1, -3]], ![![3, -3, 3, -1, -1, 1]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N0, I7N1, I7N1, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N1
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1 ⊙ MulI7N2 ⊙ MulI7N3 ⊙ MulI7N4)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0, 0], ![0, 11, 0, 0, 0, 0], ![0, 0, 11, 0, 0, 0], ![0, 0, 0, 11, 0, 0], ![0, 0, 0, 0, 11, 0], ![0, 0, 0, 0, 0, 11]] where
  M :=![![![11, 0, 0, 0, 0, 0], ![0, 11, 0, 0, 0, 0], ![0, 0, 11, 0, 0, 0], ![0, 0, 0, 11, 0, 0], ![0, 0, 0, 0, 11, 0], ![0, 0, 0, 0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0, 0]], ![![0, 0, 0, 1, 0, 0]], ![![0, 0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 6 2 3 [1, 10, 6, 0, 0, 1, 1] where
 m := 2
 P := ![2, 3]
 exp := ![1, 1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 6, 1, 6, 8, 2], [1, 7, 1, 6, 9, 3], [2, 9, 9, 4, 6, 8], [2, 8, 1, 9, 5, 8], [6, 2, 10, 8, 5, 1], [0, 1]]
 g := ![![[1, 6, 10, 1, 10, 1], [], []], ![[10, 3, 7, 4, 1, 1, 9, 7], [0, 1, 5, 10, 8, 6, 6, 10, 4, 6], [1, 7, 5, 6, 4]], ![[3, 6, 7, 5, 5, 9, 5, 8, 2, 9], [5, 4, 1, 1, 4, 8, 5, 7, 5, 4], [0, 9, 6, 1, 9]], ![[0, 4, 10, 9, 2, 3, 2, 10], [7, 6, 3, 10, 3, 6, 8, 0, 8, 2], [2, 3, 2, 10, 9]], ![[2, 2, 9, 8, 3, 4, 6, 8, 7, 2], [4, 9, 0, 0, 0, 0, 0, 4, 0, 7], [3, 8, 10, 5, 9]], ![[7, 4, 9, 10, 5, 1, 3, 9], [4, 9, 5, 2, 6, 4, 10, 8, 9, 1], [6, 2, 10, 9, 1]]]
 h' := ![![[10, 6, 1, 6, 8, 2], [0, 0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[1, 7, 1, 6, 9, 3], [0, 10, 2, 10, 3], [0, 4, 8, 1, 7, 5], [10, 6, 1, 6, 8, 2]], ![[2, 9, 9, 4, 6, 8], [7, 7, 1, 9, 9, 5], [1, 5, 10, 10, 4, 4], [1, 7, 1, 6, 9, 3]], ![[2, 8, 1, 9, 5, 8], [1, 9, 1, 10, 9], [2, 2, 7, 9, 1, 5], [2, 9, 9, 4, 6, 8]], ![[6, 2, 10, 8, 5, 1], [9, 1, 0, 4, 9, 5], [1, 5, 4, 9, 2, 7], [2, 8, 1, 9, 5, 8]], ![[0, 1], [6, 6, 7, 0, 3], [8, 6, 3, 4, 8, 1], [6, 2, 10, 8, 5, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 6, 7, 6, 10], [5, 2, 4, 2, 7], [], []]
 b := ![[], [], [10, 2, 9, 3, 1, 4], [9, 4, 10, 7, 4, 6], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 6
  hpos := by decide
  P := [1, 10, 6, 0, 0, 1, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-401896, -140151, 591184, 195547, 732820, 246719]
  a := ![-3, 1, -1, 1, 3, 0]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-36536, -12741, 53744, 17777, 66620, 22429]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1771561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![7, 0, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0], ![0, 0, 13, 0, 0, 0], ![0, 0, 0, 13, 0, 0], ![0, 0, 0, 0, 13, 0], ![0, 0, 0, 0, 0, 13]], ![![2, 1, 0, 0, 0, 0], ![0, 2, 5, 0, 0, 0], ![0, 0, 2, 1, 0, 0], ![0, 0, 0, 2, 5, 0], ![0, 0, 0, 0, 2, 1], ![-5, 0, 10, 0, 5, 2]]]
  hmulB := by decide  
  f := ![![![11, 3, 23, 182, 546, 63], ![-65, 13, -182, -1092, -819, 0]], ![![-2, -3, 9, 35, 98, 14], ![14, 13, -91, -182, -182, 0]], ![![5, 1, 11, 105, 315, 35], ![-29, 8, -91, -637, -455, 0]], ![![8, 2, 22, 167, 511, 63], ![-46, 10, -168, -1001, -819, 0]], ![![1, -1, 3, 42, 125, 14], ![-5, 9, -42, -252, -182, 0]], ![![5, 1, 12, 98, 294, 34], ![-29, 8, -98, -588, -441, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-2, 13, 0, 0, 0, 0], ![-7, 0, 13, 0, 0, 0], ![-12, 0, 0, 13, 0, 0], ![-3, 0, 0, 0, 13, 0], ![-7, 0, 0, 0, 0, 13]], ![![0, 1, 0, 0, 0, 0], ![-3, 2, 5, 0, 0, 0], ![-2, 0, 2, 1, 0, 0], ![-3, 0, 0, 2, 5, 0], ![-1, 0, 0, 0, 2, 1], ![-8, 0, 10, 0, 5, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0, 0], ![11, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0], ![0, 0, 13, 0, 0, 0], ![0, 0, 0, 13, 0, 0], ![0, 0, 0, 0, 13, 0], ![0, 0, 0, 0, 0, 13]], ![![-2, 1, 0, 0, 0, 0], ![0, -2, 5, 0, 0, 0], ![0, 0, -2, 1, 0, 0], ![0, 0, 0, -2, 5, 0], ![0, 0, 0, 0, -2, 1], ![-5, 0, 10, 0, 5, -2]]]
  hmulB := by decide  
  f := ![![![19, -7, 23, 0, 91, -63], ![117, 13, 182, 91, 819, 0]], ![![17, -6, 23, 0, 77, -56], ![105, 13, 182, 91, 728, 0]], ![![13, -5, 11, 7, 35, -35], ![81, 8, 91, 91, 455, 0]], ![![3, -1, 1, -1, 14, -7], ![19, 3, 14, 0, 91, 0]], ![![5, -1, 3, 0, 20, -14], ![31, 9, 42, 21, 182, 0]], ![![10, -4, 11, 0, 42, -29], ![62, 5, 84, 42, 378, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-11, 13, 0, 0, 0, 0], ![-7, 0, 13, 0, 0, 0], ![-1, 0, 0, 13, 0, 0], ![-3, 0, 0, 0, 13, 0], ![-6, 0, 0, 0, 0, 13]], ![![-1, 1, 0, 0, 0, 0], ![-1, -2, 5, 0, 0, 0], ![1, 0, -2, 1, 0, 0], ![-1, 0, 0, -2, 5, 0], ![0, 0, 0, 0, -2, 1], ![-6, 0, 10, 0, 5, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![8, 0, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0], ![0, 0, 13, 0, 0, 0], ![0, 0, 0, 13, 0, 0], ![0, 0, 0, 0, 13, 0], ![0, 0, 0, 0, 0, 13]], ![![5, 1, 0, 0, 0, 0], ![0, 5, 5, 0, 0, 0], ![0, 0, 5, 1, 0, 0], ![0, 0, 0, 5, 5, 0], ![0, 0, 0, 0, 5, 1], ![-5, 0, 10, 0, 5, 5]]]
  hmulB := by decide  
  f := ![![![21, -21, 175, 520, 520, 8], ![-52, 65, -520, -1248, -104, 0]], ![![5, -9, 70, 216, 240, 8], ![-12, 26, -208, -520, -104, 0]], ![![6, -17, 102, 344, 360, 8], ![-14, 47, -312, -832, -104, 0]], ![![14, -22, 160, 477, 480, 8], ![-34, 64, -480, -1144, -104, 0]], ![![-3, -6, 10, 40, 37, 0], ![8, 14, -40, -96, 0, 0]], ![![6, -17, 105, 320, 320, 5], ![-14, 47, -320, -768, -64, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-5, 13, 0, 0, 0, 0], ![-8, 0, 13, 0, 0, 0], ![-12, 0, 0, 13, 0, 0], ![-1, 0, 0, 0, 13, 0], ![-8, 0, 0, 0, 0, 13]], ![![0, 1, 0, 0, 0, 0], ![-5, 5, 5, 0, 0, 0], ![-4, 0, 5, 1, 0, 0], ![-5, 0, 0, 5, 5, 0], ![-1, 0, 0, 0, 5, 1], ![-10, 0, 10, 0, 5, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2

def I13N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0, 0], ![-5, 1, 0, 0, 0, 0]] i)))

def SI13N3: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0, 0], ![-5, 1, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0, 0], ![8, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![5, 0, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0], ![0, 0, 13, 0, 0, 0], ![0, 0, 0, 13, 0, 0], ![0, 0, 0, 0, 13, 0], ![0, 0, 0, 0, 0, 13]], ![![-5, 1, 0, 0, 0, 0], ![0, -5, 5, 0, 0, 0], ![0, 0, -5, 1, 0, 0], ![0, 0, 0, -5, 5, 0], ![0, 0, 0, 0, -5, 1], ![-5, 0, 10, 0, 5, -5]]]
  hmulB := by decide  
  f := ![![![96, -169, 180, 34, 0, -8], ![247, -390, 78, 104, 104, 0]], ![![66, -93, 100, 36, 0, -8], ![170, -208, 52, 104, 104, 0]], ![![66, -100, 107, 36, 0, -8], ![170, -226, 52, 104, 104, 0]], ![![22, -29, 10, 13, -10, 0], ![57, -64, -38, 26, 0, 0]], ![![12, -7, 10, 2, -3, 0], ![31, -12, 14, 8, 0, 0]], ![![45, -62, 65, 13, 0, -3], ![116, -138, 31, 40, 40, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-8, 13, 0, 0, 0, 0], ![-8, 0, 13, 0, 0, 0], ![-1, 0, 0, 13, 0, 0], ![-1, 0, 0, 0, 13, 0], ![-5, 0, 0, 0, 0, 13]], ![![-1, 1, 0, 0, 0, 0], ![0, -5, 5, 0, 0, 0], ![3, 0, -5, 1, 0, 0], ![0, 0, 0, -5, 5, 0], ![0, 0, 0, 0, -5, 1], ![-5, 0, 10, 0, 5, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N3 : Nat.card (O ⧸ I13N3) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N3)

lemma isPrimeI13N3 : Ideal.IsPrime I13N3 := prime_ideal_of_norm_prime hp13.out _ NI13N3

def I13N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 0, -1, 0, 2, 0]] i)))

def SI13N4: IdealEqSpanCertificate' Table ![![-2, 0, -1, 0, 2, 0]] 
 ![![13, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0], ![10, 0, 1, 0, 0, 0], ![0, 10, 0, 1, 0, 0], ![4, 0, 0, 0, 1, 0], ![0, 4, 0, 0, 0, 1]] where
  M :=![![![-2, 0, -1, 0, 2, 0], ![0, -2, 0, -1, 0, 2], ![-2, 0, 2, 0, 1, 0], ![0, -2, 0, 2, 0, 1], ![-1, 0, 0, 0, 3, 0], ![0, -1, 0, 0, 0, 3]]]
  hmulB := by decide  
  f := ![![![-6, 0, -3, 0, 5, 0]], ![![0, -6, 0, -3, 0, 5]], ![![-5, 0, -2, 0, 4, 0]], ![![0, -5, 0, -2, 0, 4]], ![![-2, 0, -1, 0, 2, 0]], ![![0, -2, 0, -1, 0, 2]]]
  g := ![![![0, 0, -1, 0, 2, 0], ![0, 0, 0, -1, 0, 2], ![-2, 0, 2, 0, 1, 0], ![0, -2, 0, 2, 0, 1], ![-1, 0, 0, 0, 3, 0], ![0, -1, 0, 0, 0, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P4 : CertificateIrreducibleZModOfList' 13 2 2 3 [4, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 12], [0, 1]]
 g := ![![[5, 10], [10], [6, 1]], ![[0, 3], [10], [12, 12]]]
 h' := ![![[6, 12], [3, 6], [2, 6], [0, 1]], ![[0, 1], [0, 7], [12, 7], [6, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [12, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N4 : CertifiedPrimeIdeal' SI13N4 13 where
  n := 2
  hpos := by decide
  P := [4, 7, 1]
  hirr := P13P4
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51, -84, 186, 23, 19, -33]
  a := ![7, -4, 0, 1, 1, -1]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-145, -14, 186, 23, 19, -33]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N4 : Ideal.IsPrime I13N4 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N4 B_one_repr
lemma NI13N4 : Nat.card (O ⧸ I13N4) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N4
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] ![![13, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]]
  ![![-3, 0, 1, 0, 1, 0]] where
 M := ![![![169, 0, 0, 0, 0, 0], ![-26, 13, 0, 0, 0, 0]], ![![26, 13, 0, 0, 0, 0], ![-4, 0, 5, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-91, 0, 26, 0, 39, 0]], ![![14, -7, -4, 2, -6, 3]]], ![![![-14, -7, 4, 2, 6, 3]], ![![1, 0, -1, 0, 1, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-3, 0, 1, 0, 1, 0]] ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0]]
  ![![13, 0, 0, 0, 0, 0], ![6, -4, -1, 5, 0, 0]] where
 M := ![![![-39, 0, 13, 0, 13, 0], ![-15, -3, 5, 1, 5, 1]]]
 hmul := by decide  
 g := ![![![![-633, 252, -786, 471, -457, -1210], ![1365, 364, 3146, 0, 0, 0]], ![![-249, 99, -312, 187, -179, -478], ![537, 143, 1243, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N2 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0, 0], ![6, -4, -1, 5, 0, 0]] ![![13, 0, 0, 0, 0, 0], ![-5, 1, 0, 0, 0, 0]]
  ![![6, 0, 3, 0, -5, 0]] where
 M := ![![![169, 0, 0, 0, 0, 0], ![-65, 13, 0, 0, 0, 0]], ![![78, -52, -13, 65, 0, 0], ![-30, 26, -15, -26, 25, 0]]]
 hmul := by decide  
 g := ![![![![26, 0, 13, 0, -26, 0]], ![![-10, 2, -5, 1, 10, -2]]], ![![![10, 2, 8, -14, -11, 3]], ![![-5, 0, 0, 6, 0, -2]]]]
 hle2 := by decide  

def MulI13N3 : IdealMulLeCertificate' Table 
  ![![6, 0, 3, 0, -5, 0]] ![![-2, 0, -1, 0, 2, 0]]
  ![![13, 0, 0, 0, 0, 0]] where
 M := ![![![-13, 0, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2, I13N3, I13N4] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
    exact isPrimeI13N3
    exact isPrimeI13N4
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1 ⊙ MulI13N2 ⊙ MulI13N3)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0, 0], ![0, 17, 0, 0, 0, 0], ![0, 0, 17, 0, 0, 0], ![0, 0, 0, 17, 0, 0], ![0, 0, 0, 0, 17, 0], ![0, 0, 0, 0, 0, 17]] where
  M :=![![![17, 0, 0, 0, 0, 0], ![0, 17, 0, 0, 0, 0], ![0, 0, 17, 0, 0, 0], ![0, 0, 0, 17, 0, 0], ![0, 0, 0, 0, 17, 0], ![0, 0, 0, 0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0, 0]], ![![0, 0, 0, 1, 0, 0]], ![![0, 0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 6 2 4 [12, 4, 15, 11, 10, 8, 1] where
 m := 2
 P := ![2, 3]
 exp := ![1, 1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 16, 13, 14, 3, 2], [0, 16, 11, 2, 4, 7], [6, 8, 9, 2, 1, 1], [11, 14, 11, 3, 15, 11], [4, 13, 7, 13, 11, 13], [0, 1]]
 g := ![![[1, 10, 6, 6, 12, 2], [3, 9, 1], [], []], ![[1, 5, 16, 11, 0, 6, 11, 4], [13, 12, 12, 1, 15], [12, 5, 4, 1, 9], [9, 2, 15, 14, 4]], ![[8, 15, 7, 5, 3, 6, 9, 3, 2, 11], [0, 13, 14, 9, 1], [7, 7, 8, 5, 13], [15, 15, 15, 4, 15]], ![[7, 3, 2, 3, 10, 10, 11, 8], [7, 2, 0, 13, 13], [4, 7, 5, 12, 8], [7, 16, 9, 11, 1]], ![[7, 14, 5, 2, 16, 9, 5, 0, 6, 5], [16, 4, 3, 12, 8], [5, 0, 5, 11, 4], [7, 2, 3, 8, 2]], ![[3, 7, 5, 7, 9, 16, 7, 2, 0, 1], [2, 5, 15, 6, 15], [15, 6, 0, 7, 13], [6, 6, 4, 5, 16]]]
 h' := ![![[5, 16, 13, 14, 3, 2], [15, 16, 9, 15, 9, 11], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[0, 16, 11, 2, 4, 7], [13, 1, 0, 15, 6], [13, 3, 8, 3, 12, 10], [2, 15, 12, 12, 2, 14], [5, 16, 13, 14, 3, 2]], ![[6, 8, 9, 2, 1, 1], [1, 5, 12, 1, 16, 2], [16, 13, 11, 14, 0, 1], [7, 15, 12, 7, 10, 8], [0, 16, 11, 2, 4, 7]], ![[11, 14, 11, 3, 15, 11], [9, 7, 7, 5, 5], [12, 6, 12, 8, 2, 8], [3, 12, 14, 6, 11, 5], [6, 8, 9, 2, 1, 1]], ![[4, 13, 7, 13, 11, 13], [12, 7, 6, 11, 13, 6], [0, 3, 2, 16, 11, 5], [3, 1, 0, 6, 2, 15], [11, 14, 11, 3, 15, 11]], ![[0, 1], [14, 15, 0, 4, 2, 15], [15, 9, 1, 10, 8, 10], [12, 8, 12, 3, 9, 9], [4, 13, 7, 13, 11, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 11, 11, 8, 4], [9, 8, 12, 11, 4], [], []]
 b := ![[], [], [1, 7, 9, 11, 13, 14], [2, 4, 0, 9, 12, 13], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 6
  hpos := by decide
  P := [12, 4, 15, 11, 10, 8, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9513931, -3116865, 12748368, 4636716, 19557973, 5439048]
  a := ![-1, 3, 4, 0, -1, 1]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-559643, -183345, 749904, 272748, 1150469, 319944]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 24137569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0, 0], ![0, 19, 0, 0, 0, 0], ![0, 0, 19, 0, 0, 0], ![0, 0, 0, 19, 0, 0], ![0, 0, 0, 0, 19, 0], ![0, 0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0, 0], ![0, 19, 0, 0, 0, 0], ![0, 0, 19, 0, 0, 0], ![0, 0, 0, 19, 0, 0], ![0, 0, 0, 0, 19, 0], ![0, 0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0, 0]], ![![0, 0, 0, 1, 0, 0]], ![![0, 0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 6 2 4 [12, 1, 9, 16, 4, 15, 1] where
 m := 2
 P := ![2, 3]
 exp := ![1, 1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 17, 13, 17, 12, 8], [7, 18, 5, 7, 8, 13], [17, 7, 13, 18, 18, 5], [11, 15, 15, 8, 17, 13], [16, 18, 11, 7, 2, 18], [0, 1]]
 g := ![![[15, 4, 9, 7], [16, 12, 4, 1], [], []], ![[18, 3, 10, 4, 5, 15, 5, 16, 7, 12], [2, 1, 12, 1, 7, 13, 14, 5, 15, 10], [18, 6, 13, 8, 11], [1, 3, 14, 11, 7]], ![[0, 7, 12, 18, 3, 1, 5, 9, 4, 3], [6, 9, 12, 8, 6, 1, 10, 3, 8, 2], [8, 4, 7, 4, 1], [17, 4, 9, 10, 17]], ![[7, 14, 17, 8, 10, 17, 1, 1, 2, 11], [2, 13, 7, 10, 5, 3, 4, 11, 16, 17], [6, 6, 5, 15, 7], [1, 15, 4, 14, 6]], ![[17, 17, 6, 3, 17, 15, 11, 5, 16, 2], [4, 12, 1, 10, 2, 5, 0, 8], [7, 15, 5, 2, 1], [4, 18, 18, 16, 17]], ![[2, 8, 0, 10, 15, 1, 15, 14, 9, 14], [15, 0, 11, 4, 10, 11, 18, 18, 3, 10], [13, 8, 10, 9, 9], [11, 10, 5, 0, 1]]]
 h' := ![![[10, 17, 13, 17, 12, 8], [17, 11, 5, 0, 11], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[7, 18, 5, 7, 8, 13], [3, 11, 15, 2, 1, 7], [4, 0, 2, 9, 9, 5], [12, 18, 8, 4, 11, 7], [10, 17, 13, 17, 12, 8]], ![[17, 7, 13, 18, 18, 5], [15, 12, 6, 12, 17, 3], [8, 0, 6, 18, 16, 5], [16, 16, 15, 12, 0, 18], [7, 18, 5, 7, 8, 13]], ![[11, 15, 15, 8, 17, 13], [0, 17, 1, 9, 3, 14], [11, 17, 16, 14, 9, 12], [11, 0, 1, 15, 2, 11], [17, 7, 13, 18, 18, 5]], ![[16, 18, 11, 7, 2, 18], [1, 5, 1, 16, 6, 5], [1, 8, 11, 9, 9], [16, 15, 0, 0, 1, 18], [11, 15, 15, 8, 17, 13]], ![[0, 1], [7, 1, 10, 18, 0, 9], [1, 13, 3, 7, 13, 16], [10, 8, 13, 7, 5, 3], [16, 18, 11, 7, 2, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 18, 10, 2, 2], [11, 12, 10, 10, 4], [], []]
 b := ![[], [], [18, 14, 14, 8, 10, 13], [18, 8, 0, 3, 17, 3], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 6
  hpos := by decide
  P := [12, 1, 9, 16, 4, 15, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-331317438556, 20493808519, 681645354187, -29594654904, 141151881182, -36973548161]
  a := ![0, 7, 2, -25, 0, 1]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17437759924, 1078621501, 35876071273, -1557613416, 7429046378, -1945976219]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 47045881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0, 0], ![-6, 4, 7, 5, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0, 0], ![-6, 4, 7, 5, 0, 0]] 
 ![![23, 0, 0, 0, 0, 0], ![0, 23, 0, 0, 0, 0], ![0, 0, 23, 0, 0, 0], ![8, 10, 6, 1, 0, 0], ![18, 8, 12, 0, 1, 0], ![19, 13, 14, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0, 0], ![0, 23, 0, 0, 0, 0], ![0, 0, 23, 0, 0, 0], ![0, 0, 0, 23, 0, 0], ![0, 0, 0, 0, 23, 0], ![0, 0, 0, 0, 0, 23]], ![![-6, 4, 7, 5, 0, 0], ![0, -6, 20, 7, 25, 0], ![0, 0, -6, 4, 7, 5], ![-25, 0, 50, -6, 45, 7], ![-7, -5, 14, 10, 1, 9], ![-45, -7, 65, 14, 95, 1]]]
  hmulB := by decide  
  f := ![![![-47, 32, 128, -8, -84, -60], ![-184, 0, 276, 0, 0, 0]], ![![54, -35, -57, -49, -7, -5], ![207, 0, 23, 0, 0, 0]], ![![0, 12, -39, -14, -50, 0], ![0, 46, 0, 0, 0, 0]], ![![10, -66, 183, 66, 257, 5], ![37, -230, -23, 0, 0, 0]], ![![-18, 10, 176, -77, -156, -120], ![-72, -11, 552, 0, 0, 0]], ![![-19, 7, 254, -114, -214, -173], ![-76, -26, 796, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![-8, -10, -6, 23, 0, 0], ![-18, -8, -12, 0, 23, 0], ![-19, -13, -14, 0, 0, 23]], ![![-2, -2, -1, 5, 0, 0], ![-22, -12, -14, 7, 25, 0], ![-11, -7, -8, 4, 7, 5], ![-40, -17, -24, -6, 45, 7], ![-12, -10, -8, 10, 1, 9], ![-82, -40, -51, 14, 95, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [16, 18, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 5], [11, 22, 18], [0, 1]]
 g := ![![[0, 18, 4], [2, 0, 1], [11, 11, 1], []], ![[18, 10], [0, 19, 13, 19], [12, 0, 11, 5], [22, 2]], ![[0, 10, 6, 3], [7, 3, 1, 8], [18, 9], [9, 2]]]
 h' := ![![[0, 0, 5], [14, 5, 2], [8, 17, 22], [0, 0, 1], [0, 1]], ![[11, 22, 18], [0, 18], [15, 14, 17], [16, 9, 22], [0, 0, 5]], ![[0, 1], [0, 0, 21], [11, 15, 7], [0, 14], [11, 22, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 5], []]
 b := ![[], [15, 22, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [16, 18, 12, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1779, -2113, 895, 3397, -10191, 3126]
  a := ![1, 3, -6, -1, -1, 3]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![4289, 209, 2567, 3397, -10191, 3126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0, 0], ![6, 4, -7, 5, 0, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0, 0], ![6, 4, -7, 5, 0, 0]] 
 ![![23, 0, 0, 0, 0, 0], ![0, 23, 0, 0, 0, 0], ![0, 0, 23, 0, 0, 0], ![15, 10, 17, 1, 0, 0], ![18, 15, 12, 0, 1, 0], ![4, 13, 9, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0, 0], ![0, 23, 0, 0, 0, 0], ![0, 0, 23, 0, 0, 0], ![0, 0, 0, 23, 0, 0], ![0, 0, 0, 0, 23, 0], ![0, 0, 0, 0, 0, 23]], ![![6, 4, -7, 5, 0, 0], ![0, 6, 20, -7, 25, 0], ![0, 0, 6, 4, -7, 5], ![-25, 0, 50, 6, 45, -7], ![7, -5, -14, 10, -1, 9], ![-45, 7, 65, -14, 95, -1]]]
  hmulB := by decide  
  f := ![![![205, 136, -166, 218, -84, 60], ![-782, 0, -276, 0, 0, 0]], ![![0, 49, 154, -60, 207, -5], ![0, -184, 23, 0, 0, 0]], ![![0, 0, -23, -16, 28, -20], ![0, 0, 92, 0, 0, 0]], ![![129, 86, -5, 203, -168, 120], ![-492, 0, -552, 0, 0, 0]], ![![162, 117, 58, 268, -215, 180], ![-618, -34, -828, 0, 0, 0]], ![![50, -9, -198, 93, -181, 2], ![-191, 164, -9, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![-15, -10, -17, 23, 0, 0], ![-18, -15, -12, 0, 23, 0], ![-4, -13, -9, 0, 0, 23]], ![![-3, -2, -4, 5, 0, 0], ![-15, -13, -7, -7, 25, 0], ![2, 0, -1, 4, -7, 5], ![-39, -28, -23, 6, 45, -7], ![-7, -9, -11, 10, -1, 9], ![-67, -55, -36, -14, 95, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 3 2 4 [4, 18, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 4, 19], [17, 18, 4], [0, 1]]
 g := ![![[3, 13, 8], [2, 18, 8], [7, 5, 1], []], ![[1, 14, 6, 17], [22, 2, 22, 15], [22, 6, 17, 15], [2, 16]], ![[5, 13, 13, 12], [2, 14, 22, 3], [11, 1, 3, 18], [17, 16]]]
 h' := ![![[11, 4, 19], [15, 9, 10], [18, 15, 10], [0, 0, 1], [0, 1]], ![[17, 18, 4], [2, 8, 6], [2, 9, 5], [21, 11, 18], [11, 4, 19]], ![[0, 1], [9, 6, 7], [22, 22, 8], [14, 12, 4], [17, 18, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 21], []]
 b := ![[], [12, 4, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 3
  hpos := by decide
  P := [4, 18, 18, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9226, -2915, 14167, 4722, 16868, 5510]
  a := ![0, 1, 5, 1, 3, 2]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17640, -16295, -13831, 4722, 16868, 5510]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0, 0], ![-6, 4, 7, 5, 0, 0]] ![![23, 0, 0, 0, 0, 0], ![6, 4, -7, 5, 0, 0]]
  ![![23, 0, 0, 0, 0, 0]] where
 M := ![![![529, 0, 0, 0, 0, 0], ![138, 92, -161, 115, 0, 0]], ![![-138, 92, 161, 115, 0, 0], ![-161, 0, 414, 0, 276, 0]]]
 hmul := by decide  
 g := ![![![![23, 0, 0, 0, 0, 0]], ![![6, 4, -7, 5, 0, 0]]], ![![![-6, 4, 7, 5, 0, 0]], ![![-7, 0, 18, 0, 12, 0]]]]
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


lemma PB87I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)
  rfl

def PB87I0 : PrimesBelowBoundCertificateInterval' O 1 23 87 where
  m := 9
  g := ![2, 2, 2, 6, 1, 5, 1, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB87I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N0]
    · exact ![I7N0, I7N0, I7N0, I7N1, I7N1, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1, I13N2, I13N3, I13N4]
    · exact ![I17N0]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![8, 8]
    · exact ![27, 27]
    · exact ![125, 125]
    · exact ![7, 7, 7, 7, 7, 7]
    · exact ![1771561]
    · exact ![13, 13, 13, 13, 169]
    · exact ![24137569]
    · exact ![47045881]
    · exact ![12167, 12167]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N0
      exact NI7N1
      exact NI7N1
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
      exact NI13N3
      exact NI13N4
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  Il := ![[I2N0, I2N0], [I3N0, I3N1], [], [I7N0, I7N0, I7N0, I7N1, I7N1, I7N1], [], [I13N0, I13N1, I13N2, I13N3], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
