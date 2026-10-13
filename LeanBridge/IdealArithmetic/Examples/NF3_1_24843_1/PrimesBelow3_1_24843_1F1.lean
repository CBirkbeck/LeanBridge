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
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [10, 23, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 9, 36], [3, 27, 1], [0, 1]]
 g := ![![[4, 4, 7], [26, 9], [32, 16, 11], [0, 1], []],![[0, 23, 22, 10], [36, 3], [0, 17, 30, 9], [30, 26], [19, 1]],![[30, 21, 25, 1], [29, 28], [35, 32, 35, 25], [27, 7], [17, 1]]]
 h' := ![![[34, 9, 36], [20, 29, 9], [13, 29, 3], [0, 27, 14], [0, 0, 1], [0, 1]],![[3, 27, 1], [6, 7, 29], [12, 16, 15], [12, 0, 18], [4, 17, 27], [34, 9, 36]],![[0, 1], [27, 1, 36], [24, 29, 19], [10, 10, 5], [24, 20, 9], [3, 27, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 35], []]
 b := ![[], [19, 12, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where 
  n := 3
  hpos := by decide  
  P := [10, 23, 0, 1]
  hirr := P37P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-8066, 0, -888]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide  
  g := ![-218, 0, -24]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![13, -17, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![13, -17, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![13, 24, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![13, -17, 1], ![47, 30, -50], ![-490, 10, -3]]]
  hmulB := by decide  
  f := ![![![-12, 17, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -24, 41]], ![![0, -1, 1], ![17, 30, -50], ![-11, 2, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [32, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 40], [0, 1]]
 g := ![![[7, 9], [20], [39], [15, 33], [1]],![[0, 32], [20], [39], [3, 8], [1]]]
 h' := ![![[22, 40], [25, 38], [3, 15], [12, 11], [9, 22], [0, 1]],![[0, 1], [0, 3], [5, 26], [8, 30], [1, 19], [22, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [33, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where 
  n := 2
  hpos := by decide  
  P := [32, 19, 1]
  hirr := P41P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-1161, 550, 163]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide  
  g := ![-80, -82, 163]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![9, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![9, 1, 0]] 
 ![![41, 0, 0], ![9, 1, 0], ![3, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![9, 1, 0], ![-1, 8, 3], ![30, 0, 10]]]
  hmulB := by decide  
  f := ![![![-1279, 10240, 3840], ![0, -52480, 0]], ![![-280, 2240, 840], ![1, -11480, 0]], ![![-96, 749, 281], ![11, -3840, 0]]]
  g := ![![![1, 0, 0], ![-9, 41, 0], ![-3, 0, 41]], ![![0, 1, 0], ![-2, 8, 3], ![0, 0, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![13, -17, 1]] ![![41, 0, 0], ![9, 1, 0]]
  ![![41, 0, 0]] where
 M :=  ![![![1681, 0, 0], ![369, 41, 0]], ![![533, -697, 41], ![164, -123, -41]]]
 hmul := by decide  
 g :=  ![![![![41, 0, 0]], ![![9, 1, 0]]], ![![![13, -17, 1]], ![![4, -3, -1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [24, 29, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 3, 1], [21, 39, 42], [0, 1]]
 g := ![![[34, 17, 40], [29, 9, 9], [5, 31], [25, 22, 1], []],![[35, 26, 33, 17], [5, 5, 0, 11], [12, 15], [36, 20, 31, 16], [28, 1]],![[15, 3, 29, 8], [8, 4, 39, 26], [35, 24], [1, 25, 32, 34], [30, 1]]]
 h' := ![![[1, 3, 1], [35, 15, 30], [13, 33, 3], [2, 37, 17], [0, 0, 1], [0, 1]],![[21, 39, 42], [1, 42, 24], [11, 17, 21], [27, 19, 12], [17, 30, 39], [1, 3, 1]],![[0, 1], [21, 29, 32], [41, 36, 19], [35, 30, 14], [22, 13, 3], [21, 39, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 1], []]
 b := ![[], [27, 0, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where 
  n := 3
  hpos := by decide  
  P := [24, 29, 21, 1]
  hirr := P43P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-93767133, -1684998, -8392869]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide  
  g := ![-2180631, -39186, -195183]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀



lemma PB45I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 44 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 44 (by omega)
  rfl

def PB45I1 : PrimesBelowBoundCertificateInterval' O 31 44 45 where
  m := 3
  g := ![1, 2, 1]
  P := ![37, 41, 43]
  hP := PB45I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![79507]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
  Il := ![[], [I41N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
