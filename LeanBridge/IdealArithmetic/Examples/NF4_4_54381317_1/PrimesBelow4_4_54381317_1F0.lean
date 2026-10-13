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
instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0]] 
 ![![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]] where
  M :=![![![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 4 2 1 [1, 0, 0, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [1, 0, 0, 1], [0, 1, 1, 1], [0, 1]]
 g := ![![[]],![[1]],![[1, 1, 1]],![[0, 1, 1]]]
 h' := ![![[0, 0, 1], [0, 1]],![[1, 0, 0, 1], [0, 0, 1]],![[0, 1, 1, 1], [1, 0, 0, 1]],![[0, 1], [0, 1, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 1, 1], []]
 b := ![[], [], [0, 1, 0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where 
  n := 4
  hpos := by decide  
  P := [1, 0, 0, 1, 1]
  hirr := P2P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![59882581222, 57263856106, 17635603102, 1738324180]
  a := ![0, -1, -1, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![29941290611, 28631928053, 8817801551, 869162090]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 16 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def PBC2 : ContainsPrimesAboveP 2 ![I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![2, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 2 (by decide) 𝕀

instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![-132, -67, -4, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0], ![-132, -67, -4, 1]] 
 ![![3, 0, 0, 0], ![0, 3, 0, 0], ![2, 2, 1, 0], ![2, 1, 0, 1]] where
  M :=![![![3, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![0, 0, 0, 3]], ![![-132, -67, -4, 1], ![383, 200, 13, -3], ![-1149, -613, -40, 10], ![3830, 2171, 187, -30]]]
  hmulB := by decide  
  f := ![![![120, 66, 5, -1], ![-6, -3, 0, 0]], ![![0, 1, 0, 0], ![0, 0, 0, 0]], ![![124, 67, 5, -1], ![-3, -2, 0, 0]], ![![36, 22, 2, 0], ![-5, -2, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-2, -2, 3, 0], ![-2, -1, 0, 3]], ![![-42, -20, -4, 1], ![121, 59, 13, -3], ![-363, -181, -40, 10], ![1172, 609, 187, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [1, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 2], [0, 1]]
 g := ![![[0, 1]],![[0, 2]]]
 h' := ![![[0, 2], [0, 1]],![[0, 1], [0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [0, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where 
  n := 2
  hpos := by decide  
  P := [1, 0, 1]
  hirr := P3P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![1553070, 1297607, 282884, -6161]
  a := ![-2, 3, -64, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![333208, 246000, 282884, -6161]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![1, 1, 0, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0], ![1, 1, 0, 0]] 
 ![![3, 0, 0, 0], ![1, 1, 0, 0], ![2, 0, 1, 0], ![1, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![0, 0, 0, 3]], ![![1, 1, 0, 0], ![0, 1, 1, 0], ![0, 0, 1, 1], ![383, 332, 80, 2]]]
  hmulB := by decide  
  f := ![![![0, -2, 1, 2], ![3, 3, -6, 0]], ![![0, 0, 1, 1], ![1, 0, -3, 0]], ![![0, -1, 1, 1], ![2, 1, -3, 0]], ![![0, 0, 1, 1], ![1, -1, -2, 0]]]
  g := ![![![1, 0, 0, 0], ![-1, 3, 0, 0], ![-2, 0, 3, 0], ![-1, 0, 0, 3]], ![![0, 1, 0, 0], ![-1, 1, 1, 0], ![-1, 0, 1, 1], ![-37, 332, 80, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![-1, 1, 0, 0]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![3, 0, 0, 0], ![-1, 1, 0, 0]] 
 ![![3, 0, 0, 0], ![2, 1, 0, 0], ![2, 0, 1, 0], ![2, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![0, 0, 0, 3]], ![![-1, 1, 0, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![383, 332, 80, 0]]]
  hmulB := by decide  
  f := ![![![2, 1, 0, -2], ![3, 6, 6, 0]], ![![1, 1, 1, -2], ![1, 3, 6, 0]], ![![1, 1, 0, -1], ![1, 4, 3, 0]], ![![1, 1, 0, -1], ![1, 4, 4, 0]]]
  g := ![![![1, 0, 0, 0], ![-2, 3, 0, 0], ![-2, 0, 3, 0], ![-2, 0, 0, 3]], ![![-1, 1, 0, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-147, 332, 80, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0], ![-132, -67, -4, 1]] ![![3, 0, 0, 0], ![1, 1, 0, 0]]
  ![![3, 0, 0, 0], ![-169, -74, -3, 1]] where
 M :=  ![![![9, 0, 0, 0], ![3, 3, 0, 0]], ![![-396, -201, -12, 3], ![251, 133, 9, -2]]]
 hmul := by decide  
 g :=  ![![![![3, 0, 0, 0], ![0, 0, 0, 0]], ![![1, 1, 0, 0], ![0, 0, 0, 0]]], ![![![37, 7, -1, 0], ![3, 0, 0, 0]], ![![140, 69, 4, -1], ![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0], ![-169, -74, -3, 1]] ![![3, 0, 0, 0], ![-1, 1, 0, 0]]
  ![![3, 0, 0, 0]] where
 M :=  ![![![9, 0, 0, 0], ![-3, 3, 0, 0]], ![![-507, -222, -9, 3], ![552, 237, 9, -3]]]
 hmul := by decide  
 g :=  ![![![![3, 0, 0, 0]], ![![-1, 1, 0, 0]]], ![![![-169, -74, -3, 1]], ![![184, 79, 3, -1]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0], ![-133, -67, -4, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0, 0], ![-133, -67, -4, 1]] 
 ![![5, 0, 0, 0], ![0, 5, 0, 0], ![4, 3, 1, 0], ![3, 0, 0, 1]] where
  M :=![![![5, 0, 0, 0], ![0, 5, 0, 0], ![0, 0, 5, 0], ![0, 0, 0, 5]], ![![-133, -67, -4, 1], ![383, 199, 13, -3], ![-1149, -613, -41, 10], ![3830, 2171, 187, -31]]]
  hmulB := by decide  
  f := ![![![75, 110, 20, -2], ![-170, -60, 0, 0]], ![![48, 7, -3, 0], ![45, 15, 0, 0]], ![![9, 52, 12, -1], ![-112, -39, 0, 0]], ![![45, 66, 12, -1], ![-102, -36, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-4, -3, 5, 0], ![-3, 0, 0, 5]], ![![-24, -11, -4, 1], ![68, 32, 13, -3], ![-203, -98, -41, 10], ![635, 322, 187, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [1, 1, 1] where
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

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where 
  n := 2
  hpos := by decide  
  P := [1, 1, 1]
  hirr := P5P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![274995, 239524, 61883, 3951]
  a := ![-1, 1, 1, -3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![3122, 10775, 61883, 3951]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0], ![2, 1, 0, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0, 0], ![2, 1, 0, 0]] 
 ![![5, 0, 0, 0], ![2, 1, 0, 0], ![1, 0, 1, 0], ![3, 0, 0, 1]] where
  M :=![![![5, 0, 0, 0], ![0, 5, 0, 0], ![0, 0, 5, 0], ![0, 0, 0, 5]], ![![2, 1, 0, 0], ![0, 2, 1, 0], ![0, 0, 2, 1], ![383, 332, 80, 3]]]
  hmulB := by decide  
  f := ![![![3, 1, 6, 3], ![-5, 0, -15, 0]], ![![-2, -3, 5, 3], ![6, 5, -15, 0]], ![![-1, -1, 0, 0], ![3, 1, 0, 0]], ![![1, -1, 3, 2], ![-1, 3, -9, 0]]]
  g := ![![![1, 0, 0, 0], ![-2, 5, 0, 0], ![-1, 0, 5, 0], ![-3, 0, 0, 5]], ![![0, 1, 0, 0], ![-1, 2, 1, 0], ![-1, 0, 2, 1], ![-74, 332, 80, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1

def I5N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0], ![-1, 1, 0, 0]] i)))

def SI5N2: IdealEqSpanCertificate' Table ![![5, 0, 0, 0], ![-1, 1, 0, 0]] 
 ![![5, 0, 0, 0], ![4, 1, 0, 0], ![4, 0, 1, 0], ![4, 0, 0, 1]] where
  M :=![![![5, 0, 0, 0], ![0, 5, 0, 0], ![0, 0, 5, 0], ![0, 0, 0, 5]], ![![-1, 1, 0, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![383, 332, 80, 0]]]
  hmulB := by decide  
  f := ![![![4, -2, 3, -4], ![15, 5, 20, 0]], ![![3, -3, 2, -1], ![11, -5, 5, 0]], ![![2, -1, 3, -3], ![6, 1, 15, 0]], ![![2, -1, 3, -3], ![6, 1, 16, 0]]]
  g := ![![![1, 0, 0, 0], ![-4, 5, 0, 0], ![-4, 0, 5, 0], ![-4, 0, 0, 5]], ![![-1, 1, 0, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-253, 332, 80, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N2 : Nat.card (O ⧸ I5N2) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N2)

lemma isPrimeI5N2 : Ideal.IsPrime I5N2 := prime_ideal_of_norm_prime hp5.out _ NI5N2
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0], ![-133, -67, -4, 1]] ![![5, 0, 0, 0], ![2, 1, 0, 0]]
  ![![5, 0, 0, 0], ![92, 60, 5, -1]] where
 M :=  ![![![25, 0, 0, 0], ![10, 5, 0, 0]], ![![-665, -335, -20, 5], ![117, 65, 5, -1]]]
 hmul := by decide  
 g :=  ![![![![-87, -60, -5, 1], ![5, 0, 0, 0]], ![![-90, -59, -5, 1], ![5, 0, 0, 0]]], ![![![-41, -7, 1, 0], ![-5, 0, 0, 0]], ![![-87, -59, -5, 1], ![6, 0, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0], ![92, 60, 5, -1]] ![![5, 0, 0, 0], ![-1, 1, 0, 0]]
  ![![5, 0, 0, 0]] where
 M :=  ![![![25, 0, 0, 0], ![-5, 5, 0, 0]], ![![460, 300, 25, -5], ![-475, -300, -25, 5]]]
 hmul := by decide  
 g :=  ![![![![5, 0, 0, 0]], ![![-1, 1, 0, 0]]], ![![![92, 60, 5, -1]], ![![-95, -60, -5, 1]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0], ![-134, -65, -4, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0], ![-134, -65, -4, 1]] 
 ![![7, 0, 0, 0], ![0, 7, 0, 0], ![3, 1, 1, 0], ![4, 2, 0, 1]] where
  M :=![![![7, 0, 0, 0], ![0, 7, 0, 0], ![0, 0, 7, 0], ![0, 0, 0, 7]], ![![-134, -65, -4, 1], ![383, 198, 15, -3], ![-1149, -613, -42, 12], ![4596, 2835, 347, -30]]]
  hmulB := by decide  
  f := ![![![41, 166, 44, -2], ![-238, -84, 0, 0]], ![![114, -17, -18, 0], ![126, 42, 0, 0]], ![![53, 78, 17, -1], ![-83, -30, 0, 0]], ![![56, 90, 20, -1], ![-100, -36, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-3, -1, 7, 0], ![-4, -2, 0, 7]], ![![-18, -9, -4, 1], ![50, 27, 15, -3], ![-153, -85, -42, 12], ![525, 364, 347, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [4, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6], [0, 1]]
 g := ![![[0, 2], [0, 1]],![[0, 5], [0, 6]]]
 h' := ![![[0, 6], [0, 3], [0, 1]],![[0, 1], [0, 4], [0, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [0, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where 
  n := 2
  hpos := by decide  
  P := [4, 0, 1]
  hirr := P7P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![29878, 25513, 6292, 332]
  a := ![0, -1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![1382, 2651, 6292, 332]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0], ![-132, -70, -4, 1]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0, 0], ![-132, -70, -4, 1]] 
 ![![7, 0, 0, 0], ![0, 7, 0, 0], ![3, 5, 1, 0], ![6, 6, 0, 1]] where
  M :=![![![7, 0, 0, 0], ![0, 7, 0, 0], ![0, 0, 7, 0], ![0, 0, 0, 7]], ![![-132, -70, -4, 1], ![383, 200, 10, -3], ![-1149, -613, -40, 7], ![2681, 1175, -53, -33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![67, 21, -6, -1], ![-98, -35, 0, 0]], ![![86, 35, -3, -1], ![-68, -25, 0, 0]], ![![96, 38, -4, -1], ![-82, -30, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-3, -5, 7, 0], ![-6, -6, 0, 7]], ![![-18, -8, -4, 1], ![53, 24, 10, -3], ![-153, -65, -40, 7], ![434, 234, -53, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 6], [0, 1]]
 g := ![![[1, 4], [5, 1]],![[0, 3], [3, 6]]]
 h' := ![![[5, 6], [4, 2], [0, 1]],![[0, 1], [0, 5], [5, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [4, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where 
  n := 2
  hpos := by decide  
  P := [2, 2, 1]
  hirr := P7P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![279991, 243549, 62804, 4076]
  a := ![19, 1, -1, 3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![9589, -13561, 62804, 4076]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0, 0], ![-134, -65, -4, 1]] ![![7, 0, 0, 0], ![-132, -70, -4, 1]]
  ![![7, 0, 0, 0]] where
 M :=  ![![![49, 0, 0, 0], ![-924, -490, -28, 7]], ![![-938, -455, -28, 7], ![70, 7, -7, 0]]]
 hmul := by decide  
 g :=  ![![![![7, 0, 0, 0]], ![![-132, -70, -4, 1]]], ![![![-134, -65, -4, 1]], ![![10, 1, -1, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0], ![-130, -67, -4, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0], ![-130, -67, -4, 1]] 
 ![![11, 0, 0, 0], ![0, 11, 0, 0], ![4, 1, 1, 0], ![7, 3, 0, 1]] where
  M :=![![![11, 0, 0, 0], ![0, 11, 0, 0], ![0, 0, 11, 0], ![0, 0, 0, 11]], ![![-130, -67, -4, 1], ![383, 202, 13, -3], ![-1149, -613, -38, 10], ![3830, 2171, 187, -28]]]
  hmulB := by decide  
  f := ![![![121, 154, 28, -2], ![-638, -220, 0, 0]], ![![28, -3, -4, 0], ![132, 44, 0, 0]], ![![82, 74, 11, -1], ![-217, -76, 0, 0]], ![![61, 85, 16, -1], ![-372, -128, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-4, -1, 11, 0], ![-7, -3, 0, 11]], ![![-11, -6, -4, 1], ![32, 18, 13, -3], ![-97, -55, -38, 10], ![298, 188, 187, -28]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 10], [0, 1]]
 g := ![![[7, 4], [6, 4], [1]],![[4, 7], [3, 7], [1]]]
 h' := ![![[2, 10], [8, 2], [5, 2], [0, 1]],![[0, 1], [1, 9], [9, 9], [2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [1, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where 
  n := 2
  hpos := by decide  
  P := [6, 9, 1]
  hirr := P11P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![126005, 112292, 30515, 2311]
  a := ![-1, 0, 1, 2]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-1112, 6804, 30515, 2311]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0], ![-133, -67, -4, 1]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0, 0], ![-133, -67, -4, 1]] 
 ![![11, 0, 0, 0], ![0, 11, 0, 0], ![6, 9, 1, 0], ![1, 2, 0, 1]] where
  M :=![![![11, 0, 0, 0], ![0, 11, 0, 0], ![0, 0, 11, 0], ![0, 0, 0, 11]], ![![-133, -67, -4, 1], ![383, 199, 13, -3], ![-1149, -613, -41, 10], ![3830, 2171, 187, -31]]]
  hmulB := by decide  
  f := ![![![70, 59, 8, -1], ![-121, -44, 0, 0]], ![![64, 9, -4, 0], ![132, 44, 0, 0]], ![![18, 3, -1, 0], ![36, 12, 0, 0]], ![![18, 7, 0, 0], ![13, 4, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-6, -9, 11, 0], ![-1, -2, 0, 11]], ![![-10, -3, -4, 1], ![28, 8, 13, -3], ![-83, -24, -41, 10], ![249, 50, 187, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [3, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 10], [0, 1]]
 g := ![![[0, 4], [], [1]],![[0, 7], [], [1]]]
 h' := ![![[0, 10], [0, 9], [8], [0, 1]],![[0, 1], [0, 2], [8], [0, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [0, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where 
  n := 2
  hpos := by decide  
  P := [3, 0, 1]
  hirr := P11P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![124120, 109100, 28780, 1952]
  a := ![-5, 0, 0, 2]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-4592, -13984, 28780, 1952]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0, 0], ![-130, -67, -4, 1]] ![![11, 0, 0, 0], ![-133, -67, -4, 1]]
  ![![11, 0, 0, 0]] where
 M :=  ![![![121, 0, 0, 0], ![-1463, -737, -44, 11]], ![![-1430, -737, -44, 11], ![55, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![11, 0, 0, 0]], ![![-133, -67, -4, 1]]], ![![![-130, -67, -4, 1]], ![![5, 0, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![-136, -62, -4, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0], ![-136, -62, -4, 1]] 
 ![![13, 0, 0, 0], ![0, 13, 0, 0], ![11, 6, 1, 0], ![12, 1, 0, 1]] where
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![-136, -62, -4, 1], ![383, 196, 18, -3], ![-1149, -613, -44, 15], ![5745, 3831, 587, -29]]]
  hmulB := by decide  
  f := ![![![-275, 1158, 396, -9], ![-2223, -780, 0, 0]], ![![114, -161, -64, 1], ![377, 130, 0, 0]], ![![-201, 896, 305, -7], ![-1709, -600, 0, 0]], ![![-266, 1047, 360, -8], ![-2025, -710, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-11, -6, 13, 0], ![-12, -1, 0, 13]], ![![-8, -3, -4, 1], ![17, 7, 18, -3], ![-65, -28, -44, 15], ![-28, 26, 587, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 12], [0, 1]]
 g := ![![[7, 12], [1], [12, 1]],![[8, 1], [1], [11, 12]]]
 h' := ![![[12, 12], [2, 8], [2, 12], [0, 1]],![[0, 1], [7, 5], [3, 1], [12, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [2, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where 
  n := 2
  hpos := by decide  
  P := [2, 1, 1]
  hirr := P13P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![84352, 63427, 9440, -1377]
  a := ![-10, 2, 13, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-228, 628, 9440, -1377]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![-134, -70, -4, 1]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0], ![-134, -70, -4, 1]] 
 ![![13, 0, 0, 0], ![0, 13, 0, 0], ![3, 6, 1, 0], ![8, 6, 0, 1]] where
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![-134, -70, -4, 1], ![383, 198, 10, -3], ![-1149, -613, -42, 7], ![2681, 1175, -53, -35]]]
  hmulB := by decide  
  f := ![![![414, 56, -98, -14], ![-2821, -1001, 0, 0]], ![![-1, 15, 10, 1], ![260, 91, 0, 0]], ![![126, 36, -17, -3], ![-528, -189, 0, 0]], ![![244, 36, -56, -8], ![-1617, -574, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-3, -6, 13, 0], ![-8, -6, 0, 13]], ![![-10, -4, -4, 1], ![29, 12, 10, -3], ![-83, -31, -42, 7], ![240, 131, -53, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [3, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 12], [0, 1]]
 g := ![![[9, 9], [4], [12, 1]],![[0, 4], [4], [11, 12]]]
 h' := ![![[12, 12], [10, 10], [3, 11], [0, 1]],![[0, 1], [0, 3], [5, 2], [12, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [6, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where 
  n := 2
  hpos := by decide  
  P := [3, 1, 1]
  hirr := P13P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![39454, 37646, 11600, 1144]
  a := ![1, 1, -4, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-346, -2986, 11600, 1144]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0], ![-136, -62, -4, 1]] ![![13, 0, 0, 0], ![-134, -70, -4, 1]]
  ![![13, 0, 0, 0]] where
 M :=  ![![![169, 0, 0, 0], ![-1742, -910, -52, 13]], ![![-1768, -806, -52, 13], ![1755, 871, 39, -13]]]
 hmul := by decide  
 g :=  ![![![![13, 0, 0, 0]], ![![-134, -70, -4, 1]]], ![![![-136, -62, -4, 1]], ![![135, 67, 3, -1]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0], ![-129, -67, -4, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0], ![-129, -67, -4, 1]] 
 ![![17, 0, 0, 0], ![0, 17, 0, 0], ![13, 2, 1, 0], ![8, 9, 0, 1]] where
  M :=![![![17, 0, 0, 0], ![0, 17, 0, 0], ![0, 0, 17, 0], ![0, 0, 0, 17]], ![![-129, -67, -4, 1], ![383, 203, 13, -3], ![-1149, -613, -37, 10], ![3830, 2171, 187, -27]]]
  hmulB := by decide  
  f := ![![![248, 271, 47, -3], ![-1734, -595, 0, 0]], ![![28, -13, -7, 0], ![357, 119, 0, 0]], ![![155, 186, 34, -2], ![-1289, -441, 0, 0]], ![![86, 97, 17, -1], ![-633, -217, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-13, -2, 17, 0], ![-8, -9, 0, 17]], ![![-5, -4, -4, 1], ![14, 12, 13, -3], ![-44, -37, -37, 10], ![95, 120, 187, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [3, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 16], [0, 1]]
 g := ![![[6, 1], [8], [1], [1]],![[5, 16], [8], [1], [1]]]
 h' := ![![[16, 16], [12, 1], [6, 5], [14, 16], [0, 1]],![[0, 1], [11, 16], [1, 12], [15, 1], [16, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [14, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where 
  n := 2
  hpos := by decide  
  P := [3, 1, 1]
  hirr := P17P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![31415, 26836, 6617, 327]
  a := ![-3, 1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-3366, 627, 6617, 327]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0], ![7, 1, 0, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0, 0], ![7, 1, 0, 0]] 
 ![![17, 0, 0, 0], ![7, 1, 0, 0], ![2, 0, 1, 0], ![3, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0], ![0, 17, 0, 0], ![0, 0, 17, 0], ![0, 0, 0, 17]], ![![7, 1, 0, 0], ![0, 7, 1, 0], ![0, 0, 7, 1], ![383, 332, 80, 8]]]
  hmulB := by decide  
  f := ![![![50, -182, -34, -1], ![-119, 459, 17, 0]], ![![7, -83, -19, -1], ![-16, 204, 17, 0]], ![![-4, -8, 34, 5], ![10, 18, -85, 0]], ![![-6, -40, -13, -1], ![15, 95, 18, 0]]]
  g := ![![![1, 0, 0, 0], ![-7, 17, 0, 0], ![-2, 0, 17, 0], ![-3, 0, 0, 17]], ![![0, 1, 0, 0], ![-3, 7, 1, 0], ![-1, 0, 7, 1], ![-125, 332, 80, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0], ![-129, -67, -4, 1]] ![![17, 0, 0, 0], ![7, 1, 0, 0]]
  ![![17, 0, 0, 0], ![-554, -283, -15, 4]] where
 M :=  ![![![289, 0, 0, 0], ![119, 17, 0, 0]], ![![-2193, -1139, -68, 17], ![-520, -266, -15, 4]]]
 hmul := by decide  
 g :=  ![![![![17, 0, 0, 0], ![0, 0, 0, 0]], ![![7, 1, 0, 0], ![0, 0, 0, 0]]], ![![![425, 216, 11, -3], ![17, 0, 0, 0]], ![![2, 1, 0, 0], ![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0], ![-554, -283, -15, 4]] ![![17, 0, 0, 0], ![7, 1, 0, 0]]
  ![![17, 0, 0, 0]] where
 M :=  ![![![289, 0, 0, 0], ![119, 17, 0, 0]], ![![-9418, -4811, -255, 68], ![-2346, -1207, -68, 17]]]
 hmul := by decide  
 g :=  ![![![![17, 0, 0, 0]], ![![7, 1, 0, 0]]], ![![![-554, -283, -15, 4]], ![![-138, -71, -4, 1]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0], ![-131, -67, -4, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0], ![-131, -67, -4, 1]] 
 ![![19, 0, 0, 0], ![0, 19, 0, 0], ![9, 0, 1, 0], ![0, 9, 0, 1]] where
  M :=![![![19, 0, 0, 0], ![0, 19, 0, 0], ![0, 0, 19, 0], ![0, 0, 0, 19]], ![![-131, -67, -4, 1], ![383, 201, 13, -3], ![-1149, -613, -39, 10], ![3830, 2171, 187, -29]]]
  hmulB := by decide  
  f := ![![![688, 1139, 222, -17], ![-8455, -2926, 0, 0]], ![![-21, -66, -15, 1], ![608, 209, 0, 0]], ![![319, 536, 105, -8], ![-4006, -1386, 0, 0]], ![![59, 4, -5, 0], ![298, 99, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-9, 0, 19, 0], ![0, -9, 0, 19]], ![![-5, -4, -4, 1], ![14, 12, 13, -3], ![-42, -37, -39, 10], ![113, 128, 187, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [7, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 18], [0, 1]]
 g := ![![[9, 11], [6, 1], [17], [1]],![[0, 8], [0, 18], [17], [1]]]
 h' := ![![[13, 18], [15, 12], [6, 1], [12, 13], [0, 1]],![[0, 1], [0, 7], [0, 18], [10, 6], [13, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [4, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where 
  n := 2
  hpos := by decide  
  P := [7, 6, 1]
  hirr := P19P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![493721, 412628, 96052, 3353]
  a := ![3, 0, 7, -4]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-19513, 20129, 96052, 3353]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0], ![-132, -67, -4, 1]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0, 0], ![-132, -67, -4, 1]] 
 ![![19, 0, 0, 0], ![0, 19, 0, 0], ![6, 18, 1, 0], ![6, 5, 0, 1]] where
  M :=![![![19, 0, 0, 0], ![0, 19, 0, 0], ![0, 0, 19, 0], ![0, 0, 0, 19]], ![![-132, -67, -4, 1], ![383, 200, 13, -3], ![-1149, -613, -40, 10], ![3830, 2171, 187, -30]]]
  hmulB := by decide  
  f := ![![![415, 714, 138, -12], ![-4902, -1710, 0, 0]], ![![-2, -56, -14, 1], ![551, 190, 0, 0]], ![![150, 183, 31, -3], ![-1023, -360, 0, 0]], ![![200, 246, 42, -4], ![-1393, -490, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-6, -18, 19, 0], ![-6, -5, 0, 19]], ![![-6, 0, -4, 1], ![17, -1, 13, -3], ![-51, 3, -40, 10], ![152, -55, 187, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [9, 12, 1] where
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
 g := ![![[14, 17], [8, 7], [11], [1]],![[0, 2], [0, 12], [11], [1]]]
 h' := ![![[7, 18], [4, 13], [1, 8], [10, 7], [0, 1]],![[0, 1], [0, 6], [0, 11], [2, 12], [7, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [2, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where 
  n := 2
  hpos := by decide  
  P := [9, 12, 1]
  hirr := P19P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![29883, 25525, 6304, 320]
  a := ![0, 1, 1, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-519, -4713, 6304, 320]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0, 0], ![-131, -67, -4, 1]] ![![19, 0, 0, 0], ![-132, -67, -4, 1]]
  ![![19, 0, 0, 0]] where
 M :=  ![![![361, 0, 0, 0], ![-2508, -1273, -76, 19]], ![![-2489, -1273, -76, 19], ![57, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![19, 0, 0, 0]], ![![-132, -67, -4, 1]]], ![![![-131, -67, -4, 1]], ![![3, 0, 0, 0]]]]
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
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0], ![-131, -64, -4, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0], ![-131, -64, -4, 1]] 
 ![![23, 0, 0, 0], ![0, 23, 0, 0], ![9, 8, 1, 0], ![20, 14, 0, 1]] where
  M :=![![![23, 0, 0, 0], ![0, 23, 0, 0], ![0, 0, 23, 0], ![0, 0, 0, 23]], ![![-131, -64, -4, 1], ![383, 201, 16, -3], ![-1149, -613, -39, 13], ![4979, 3167, 427, -26]]]
  hmulB := by decide  
  f := ![![![205, 544, 144, -4], ![-2116, -736, 0, 0]], ![![80, -71, -32, 0], ![552, 184, 0, 0]], ![![165, 216, 47, -2], ![-626, -224, 0, 0]], ![![170, 402, 104, -3], ![-1514, -528, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-9, -8, 23, 0], ![-20, -14, 0, 23]], ![![-5, -2, -4, 1], ![13, 5, 16, -3], ![-46, -21, -39, 13], ![72, 5, 427, -26]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [9, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 22], [0, 1]]
 g := ![![[8, 18], [18, 6], [4, 9], [1]],![[0, 5], [0, 17], [0, 14], [1]]]
 h' := ![![[20, 22], [22, 15], [10, 11], [14, 20], [0, 1]],![[0, 1], [0, 8], [0, 12], [0, 3], [20, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [18, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where 
  n := 2
  hpos := by decide  
  P := [9, 3, 1]
  hirr := P23P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![6135, 5315, 1293, 40]
  a := ![-1, 3, 4, 0]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-274, -243, 1293, 40]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0], ![-131, -62, -4, 1]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0, 0], ![-131, -62, -4, 1]] 
 ![![23, 0, 0, 0], ![0, 23, 0, 0], ![6, 14, 1, 0], ![8, 17, 0, 1]] where
  M :=![![![23, 0, 0, 0], ![0, 23, 0, 0], ![0, 0, 23, 0], ![0, 0, 0, 23]], ![![-131, -62, -4, 1], ![383, 201, 18, -3], ![-1149, -613, -39, 15], ![5745, 3831, 587, -24]]]
  hmulB := by decide  
  f := ![![![143, 304, 80, -2], ![-782, -276, 0, 0]], ![![-11, -241, -76, 1], ![805, 276, 0, 0]], ![![42, -62, -25, 0], ![288, 96, 0, 0]], ![![53, -67, -28, 0], ![325, 108, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-6, -14, 23, 0], ![-8, -17, 0, 23]], ![![-5, -1, -4, 1], ![13, 0, 18, -3], ![-45, -14, -39, 15], ![105, -173, 587, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [12, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 22], [0, 1]]
 g := ![![[6, 2], [7, 3], [22, 9], [1]],![[0, 21], [21, 20], [18, 14], [1]]]
 h' := ![![[20, 22], [8, 18], [12, 16], [11, 20], [0, 1]],![[0, 1], [0, 5], [10, 7], [20, 3], [20, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [16, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where 
  n := 2
  hpos := by decide  
  P := [12, 3, 1]
  hirr := P23P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![1525499, 1341124, 353676, 24178]
  a := ![-1, 1, 0, 7]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-34347, -174842, 353676, 24178]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0], ![-131, -64, -4, 1]] ![![23, 0, 0, 0], ![-131, -62, -4, 1]]
  ![![23, 0, 0, 0]] where
 M :=  ![![![529, 0, 0, 0], ![-3013, -1426, -92, 23]], ![![-3013, -1472, -92, 23], ![2990, 1541, 115, -23]]]
 hmul := by decide  
 g :=  ![![![![23, 0, 0, 0]], ![![-131, -62, -4, 1]]], ![![![-131, -64, -4, 1]], ![![130, 67, 5, -1]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0], ![-136, -80, -4, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0], ![-136, -80, -4, 1]] 
 ![![29, 0, 0, 0], ![0, 29, 0, 0], ![19, 23, 1, 0], ![27, 12, 0, 1]] where
  M :=![![![29, 0, 0, 0], ![0, 29, 0, 0], ![0, 0, 29, 0], ![0, 0, 0, 29]], ![![-136, -80, -4, 1], ![383, 196, 0, -3], ![-1149, -613, -44, -3], ![-1149, -2145, -853, -47]]]
  hmulB := by decide  
  f := ![![![1457, -784, -588, -21], ![-4263, -1624, 0, 0]], ![![-330, 217, 148, 5], ![1073, 406, 0, 0]], ![![721, -325, -267, -10], ![-1936, -742, 0, 0]], ![![1295, -596, -484, -18], ![-3509, -1344, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-19, -23, 29, 0], ![-27, -12, 0, 29]], ![![-3, 0, -4, 1], ![16, 8, 0, -3], ![-8, 15, -44, -3], ![563, 622, -853, -47]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [25, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 28], [0, 1]]
 g := ![![[19, 7], [23], [28, 23], [18, 1]],![[0, 22], [23], [7, 6], [7, 28]]]
 h' := ![![[18, 28], [21, 23], [25, 9], [14, 9], [0, 1]],![[0, 1], [0, 6], [13, 20], [2, 20], [18, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [5, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where 
  n := 2
  hpos := by decide  
  P := [25, 11, 1]
  hirr := P29P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![11924, 10300, 3820, 458]
  a := ![2, -25, 0, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-2518, -2864, 3820, 458]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0], ![-133, -56, -4, 1]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0, 0], ![-133, -56, -4, 1]] 
 ![![29, 0, 0, 0], ![0, 29, 0, 0], ![18, 5, 1, 0], ![26, 22, 0, 1]] where
  M :=![![![29, 0, 0, 0], ![0, 29, 0, 0], ![0, 0, 29, 0], ![0, 0, 0, 29]], ![![-133, -56, -4, 1], ![383, 199, 24, -3], ![-1149, -613, -41, 21], ![8043, 5823, 1067, -20]]]
  hmulB := by decide  
  f := ![![![289, 4461, 1444, -16], ![-9541, -3335, 0, 0]], ![![-31, -880, -288, 3], ![1914, 667, 0, 0]], ![![119, 2594, 845, -9], ![-5604, -1955, 0, 0]], ![![231, 3330, 1076, -12], ![-7103, -2484, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-18, -5, 29, 0], ![-26, -22, 0, 29]], ![![-3, -2, -4, 1], ![1, 5, 24, -3], ![-33, -30, -41, 21], ![-367, 32, 1067, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [25, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 28], [0, 1]]
 g := ![![[6, 7], [7], [], [24, 1]],![[0, 22], [7], [], [19, 28]]]
 h' := ![![[24, 28], [28, 23], [0, 23], [9], [0, 1]],![[0, 1], [0, 6], [1, 6], [9], [24, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [2, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where 
  n := 2
  hpos := by decide  
  P := [25, 5, 1]
  hirr := P29P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![47140, 45836, 14506, 1452]
  a := ![1, 3, -6, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-8680, -2022, 14506, 1452]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0, 0], ![-136, -80, -4, 1]] ![![29, 0, 0, 0], ![-133, -56, -4, 1]]
  ![![29, 0, 0, 0]] where
 M :=  ![![![841, 0, 0, 0], ![-3857, -1624, -116, 29]], ![![-3944, -2320, -116, 29], ![87, -29, -145, 0]]]
 hmul := by decide  
 g :=  ![![![![29, 0, 0, 0]], ![![-133, -56, -4, 1]]], ![![![-136, -80, -4, 1]], ![![3, -1, -5, 0]]]]
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


lemma PB692I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 29 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 29 (by omega)
  rfl

def PB692I0 : PrimesBelowBoundCertificateInterval' O 1 29 692 where
  m := 10
  g := ![1, 3, 3, 2, 2, 2, 3, 2, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
  hP := PB692I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N1, I3N2]
    · exact ![I5N0, I5N1, I5N2]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
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
    · exact ![16]
    · exact ![9, 3, 3]
    · exact ![25, 5, 5]
    · exact ![49, 49]
    · exact ![121, 121]
    · exact ![169, 169]
    · exact ![289, 17, 17]
    · exact ![361, 361]
    · exact ![529, 529]
    · exact ![841, 841]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N2
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
  Il := ![[I2N0], [I3N0, I3N1, I3N2], [I5N0, I5N1, I5N2], [I7N0, I7N1], [I11N0, I11N1], [I13N0, I13N1], [I17N0, I17N1, I17N1], [I19N0, I19N1], [I23N0, I23N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
