/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF2_0_231_1.RI2_0_231_1
import LeanBridge.IdealArithmetic.Generation.ClassGroupGeneration
import LeanBridge.IdealArithmetic.IdealArithmetic
import LeanBridge.IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0], ![0, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0], ![0, 1]] 
 ![![2, 0], ![0, 1]] where
  M :=![![![2, 0], ![0, 2]], ![![0, 1], ![-58, 1]]]
  hmulB := by decide  
  f := ![![![1, 0], ![0, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![0, 2]], ![![0, 1], ![-29, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0], ![1, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0], ![1, 1]] 
 ![![2, 0], ![1, 1]] where
  M :=![![![2, 0], ![0, 2]], ![![1, 1], ![-58, 2]]]
  hmulB := by decide  
  f := ![![![0, -1], ![2, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-1, 2]], ![![0, 1], ![-30, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0], ![0, 1]] ![![2, 0], ![1, 1]]
  ![![2, 0]] where
 M :=  ![![![4, 0], ![2, 2]], ![![0, 2], ![-58, 2]]]
 hmul := by decide  
 g :=  ![![![![2, 0]], ![![1, 1]]], ![![![0, 1]], ![![-29, 1]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0], ![1, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0], ![1, 1]] 
 ![![3, 0], ![1, 1]] where
  M :=![![![3, 0], ![0, 3]], ![![1, 1], ![-58, 2]]]
  hmulB := by decide  
  f := ![![![0, -1], ![3, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-1, 3]], ![![0, 1], ![-20, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0], ![1, 1]] ![![3, 0], ![1, 1]]
  ![![3, 0]] where
 M :=  ![![![9, 0], ![3, 3]], ![![3, 3], ![-57, 3]]]
 hmul := by decide  
 g :=  ![![![![3, 0]], ![![1, 1]]], ![![![1, 1]], ![![-19, 1]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0], ![1, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0], ![1, 1]] 
 ![![5, 0], ![1, 1]] where
  M :=![![![5, 0], ![0, 5]], ![![1, 1], ![-58, 2]]]
  hmulB := by decide  
  f := ![![![0, -1], ![5, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-1, 5]], ![![0, 1], ![-12, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0], ![3, 1]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0], ![3, 1]] 
 ![![5, 0], ![3, 1]] where
  M :=![![![5, 0], ![0, 5]], ![![3, 1], ![-58, 4]]]
  hmulB := by decide  
  f := ![![![-2, -1], ![5, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-3, 5]], ![![0, 1], ![-14, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0], ![1, 1]] ![![5, 0], ![3, 1]]
  ![![5, 0]] where
 M :=  ![![![25, 0], ![15, 5]], ![![5, 5], ![-55, 5]]]
 hmul := by decide  
 g :=  ![![![![5, 0]], ![![3, 1]]], ![![![1, 1]], ![![-11, 1]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0], ![3, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0], ![3, 1]] 
 ![![7, 0], ![3, 1]] where
  M :=![![![7, 0], ![0, 7]], ![![3, 1], ![-58, 4]]]
  hmulB := by decide  
  f := ![![![-2, -1], ![7, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-3, 7]], ![![0, 1], ![-10, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0], ![3, 1]] ![![7, 0], ![3, 1]]
  ![![7, 0]] where
 M :=  ![![![49, 0], ![21, 7]], ![![21, 7], ![-49, 7]]]
 hmul := by decide  
 g :=  ![![![![7, 0]], ![![3, 1]]], ![![![3, 1]], ![![-7, 1]]]]
 hle2 := by decide  

def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)


lemma PB10I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 9 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 9 (by omega)
  rfl

def PB10I0 : PrimesBelowBoundCertificateInterval' O 1 9 10 where
  m := 4
  g := ![2, 2, 2, 2]
  P := ![2, 3, 5, 7]
  hP := PB10I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2]
    · exact ![3, 3]
    · exact ![5, 5]
    · exact ![7, 7]
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
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
  Il := ![[I2N0, I2N1], [I3N0, I3N0], [I5N0, I5N1], [I7N0, I7N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
