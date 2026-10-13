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
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0, 0], ![-104, -67, -4, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0, 0], ![-104, -67, -4, 1]] 
 ![![233, 0, 0, 0], ![0, 233, 0, 0], ![71, 27, 1, 0], ![180, 41, 0, 1]] where
  M :=![![![233, 0, 0, 0], ![0, 233, 0, 0], ![0, 0, 233, 0], ![0, 0, 0, 233]], ![![-104, -67, -4, 1], ![383, 228, 13, -3], ![-1149, -613, -12, 10], ![3830, 2171, 187, -2]]]
  hmulB := by decide  
  f := ![![![439794, 255911, 14383, -3230], ![-270047, -340879, 0, 0]], ![![-2057, -1193, -67, 15], ![1398, 1631, 0, 0]], ![![133827, 77876, 4377, -983], ![-82013, -103684, 0, 0]], ![![339431, 197514, 11101, -2493], ![-208289, -263053, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-71, -27, 233, 0], ![-180, -41, 0, 233]], ![![0, 0, -4, 1], ![0, 0, 13, -3], ![-9, -3, -12, 10], ![-39, -12, 187, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [124, 142, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 232], [0, 1]]
 g := ![![[50, 171], [92], [120], [21, 30], [8], [197, 4], [91, 1]],![[0, 62], [92], [120], [188, 203], [8], [95, 229], [182, 232]]]
 h' := ![![[91, 232], [209, 95], [82, 201], [192, 54], [144, 27], [37, 170], [133, 2], [0, 1]],![[0, 1], [0, 138], [199, 32], [213, 179], [38, 206], [129, 63], [82, 231], [91, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [165]]
 b := ![[], [149, 199]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where 
  n := 2
  hpos := by decide  
  P := [124, 142, 1]
  hirr := P233P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![33062, 29559, 8118, 518]
  a := ![0, -1, -1, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-2732, -905, 8118, 518]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0, 0], ![-159, -67, -4, 1]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0, 0], ![-159, -67, -4, 1]] 
 ![![233, 0, 0, 0], ![0, 233, 0, 0], ![139, 205, 1, 0], ![164, 54, 0, 1]] where
  M :=![![![233, 0, 0, 0], ![0, 233, 0, 0], ![0, 0, 233, 0], ![0, 0, 0, 233]], ![![-159, -67, -4, 1], ![383, 173, 13, -3], ![-1149, -613, -67, 10], ![3830, 2171, 187, -57]]]
  hmulB := by decide  
  f := ![![![759577, 355948, 29506, -6604], ![-621178, -719970, 0, 0]], ![![-7356, -3447, -286, 64], ![6058, 6990, 0, 0]], ![![446759, 209353, 17353, -3884], ![-365108, -423360, 0, 0]], ![![533017, 249775, 20704, -4634], ![-435697, -505140, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-139, -205, 233, 0], ![-164, -54, 0, 233]], ![![1, 3, -4, 1], ![-4, -10, 13, -3], ![28, 54, -67, 10], ![-55, -142, 187, -57]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P1 : CertificateIrreducibleZModOfList' 233 2 2 7 [35, 126, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 232], [0, 1]]
 g := ![![[190, 89], [28], [121], [99, 121], [64], [133, 9], [107, 1]],![[160, 144], [28], [121], [231, 112], [64], [164, 224], [214, 232]]]
 h' := ![![[107, 232], [155, 136], [160, 93], [30, 11], [115, 11], [5, 225], [216, 230], [0, 1]],![[0, 1], [28, 97], [92, 140], [42, 222], [127, 222], [81, 8], [128, 3], [107, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [164]]
 b := ![[], [40, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N1 : CertifiedPrimeIdeal' SI233N1 233 where 
  n := 2
  hpos := by decide  
  P := [35, 126, 1]
  hirr := P233P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![1552852, 1297985, 274820, -6035]
  a := ![-2, 3, -64, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-153036, -234825, 274820, -6035]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N1 B_one_repr
lemma NI233N1 : Nat.card (O ⧸ I233N1) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0, 0], ![-104, -67, -4, 1]] ![![233, 0, 0, 0], ![-159, -67, -4, 1]]
  ![![233, 0, 0, 0]] where
 M :=  ![![![54289, 0, 0, 0], ![-37047, -15611, -932, 233]], ![![-24232, -15611, -932, 233], ![-699, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![233, 0, 0, 0]], ![![-159, -67, -4, 1]]], ![![![-104, -67, -4, 1]], ![![-3, 0, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -8, 1, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-19, -8, 1, 0]] 
 ![![239, 0, 0, 0], ![0, 239, 0, 0], ![220, 231, 1, 0], ![87, 156, 0, 1]] where
  M :=![![![-19, -8, 1, 0], ![0, -19, -8, 1], ![383, 332, 61, -7], ![-2681, -1941, -228, 54]]]
  hmulB := by decide  
  f := ![![![189, 75, 3, -1]], ![![-383, -143, -5, 2]], ![![-193, -68, -2, 1]], ![![-186, -67, -2, 1]]]
  g := ![![![-1, -1, 1, 0], ![7, 7, -8, 1], ![-52, -53, 61, -7], ![179, 177, -228, 54]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [66, 167, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 238], [0, 1]]
 g := ![![[151, 134], [83, 169], [181, 22], [174, 45], [33], [191, 2], [72, 1]],![[0, 105], [62, 70], [92, 217], [68, 194], [33], [96, 237], [144, 238]]]
 h' := ![![[72, 238], [19, 96], [4, 13], [227, 168], [109, 146], [61, 64], [28, 99], [0, 1]],![[0, 1], [0, 143], [223, 226], [134, 71], [105, 93], [128, 175], [225, 140], [72, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [198]]
 b := ![[], [21, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where 
  n := 2
  hpos := by decide  
  P := [66, 167, 1]
  hirr := P239P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![274894, 239690, 62049, 3453]
  a := ![-1, 1, 1, -3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-57223, -61223, 62049, 3453]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-189, -75, -3, 1]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-189, -75, -3, 1]] 
 ![![239, 0, 0, 0], ![0, 239, 0, 0], ![234, 7, 1, 0], ![35, 185, 0, 1]] where
  M :=![![![-189, -75, -3, 1], ![383, 143, 5, -2], ![-766, -281, -17, 3], ![1149, 230, -41, -14]]]
  hmulB := by decide  
  f := ![![![19, 8, -1, 0]], ![![0, 19, 8, -1]], ![![17, 7, -1, 0]], ![![14, 24, 7, -1]]]
  g := ![![![2, -1, -3, 1], ![-3, 2, 5, -2], ![13, -3, -17, 3], ![47, 13, -41, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P1 : CertificateIrreducibleZModOfList' 239 2 2 7 [161, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [217, 238], [0, 1]]
 g := ![![[61, 144], [15, 55], [166, 51], [31, 34], [226], [64, 125], [217, 1]],![[0, 95], [0, 184], [0, 188], [0, 205], [226], [182, 114], [195, 238]]]
 h' := ![![[217, 238], [214, 227], [42, 154], [28, 23], [193, 150], [212, 153], [196, 84], [0, 1]],![[0, 1], [0, 12], [0, 85], [0, 216], [0, 89], [192, 86], [21, 155], [217, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [33, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N1 : CertifiedPrimeIdeal' SI239N1 239 where 
  n := 2
  hpos := by decide  
  P := [161, 22, 1]
  hirr := P239P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![30035, 25491, 6270, 354]
  a := ![0, -1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-6065, -351, 6270, 354]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N1 B_one_repr
lemma NI239N1 : Nat.card (O ⧸ I239N1) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-19, -8, 1, 0]] ![![-189, -75, -3, 1]]
  ![![239, 0, 0, 0]] where
 M :=  ![![![-239, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![-1, 0, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-422, -201, -12, 3]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![-422, -201, -12, 3]] 
 ![![241, 0, 0, 0], ![0, 241, 0, 0], ![202, 151, 1, 0], ![105, 55, 0, 1]] where
  M :=![![![-422, -201, -12, 3], ![1149, 574, 39, -9], ![-3447, -1839, -146, 30], ![11490, 6513, 561, -116]]]
  hmulB := by decide  
  f := ![![![367, 201, 12, -3]], ![![-1149, -629, -39, 9]], ![![-398, -218, -14, 3]], ![![-150, -83, -6, 1]]]
  g := ![![![7, 6, -12, 3], ![-24, -20, 39, -9], ![95, 77, -146, 30], ![-372, -298, 561, -116]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [160, 153, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 240], [0, 1]]
 g := ![![[132, 119], [1], [150], [193], [136, 64], [214, 237], [88, 1]],![[0, 122], [1], [150], [193], [225, 177], [103, 4], [176, 240]]]
 h' := ![![[88, 240], [117, 100], [235, 240], [48, 106], [171, 124], [223, 233], [139, 113], [0, 1]],![[0, 1], [0, 141], [147, 1], [218, 135], [238, 117], [1, 8], [202, 128], [88, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [176]]
 b := ![[], [225, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where 
  n := 2
  hpos := by decide  
  P := [160, 153, 1]
  hirr := P241P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![283018, 243700, 62653, 4529]
  a := ![19, 1, -1, 3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-53313, -39278, 62653, 4529]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 1, 0, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![6, 1, 0, 0]] 
 ![![241, 0, 0, 0], ![6, 1, 0, 0], ![205, 0, 1, 0], ![216, 0, 0, 1]] where
  M :=![![![6, 1, 0, 0], ![0, 6, 1, 0], ![0, 0, 6, 1], ![383, 332, 80, 7]]]
  hmulB := by decide  
  f := ![![![104, 38, 7, -1]], ![![1, 0, 0, 0]], ![![98, 39, 7, -1]], ![![36, -6, 1, 0]]]
  g := ![![![0, 1, 0, 0], ![-1, 6, 1, 0], ![-6, 0, 6, 1], ![-81, 332, 80, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-125, -68, -4, 1]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![-125, -68, -4, 1]] 
 ![![241, 0, 0, 0], ![83, 1, 0, 0], ![100, 0, 1, 0], ![135, 0, 0, 1]] where
  M :=![![![-125, -68, -4, 1], ![383, 207, 12, -3], ![-1149, -613, -33, 9], ![3447, 1839, 107, -24]]]
  hmulB := by decide  
  f := ![![![1383, 632, 33, -9]], ![![462, 211, 11, -3]], ![![612, 281, 15, -4]], ![![673, 304, 16, -4]]]
  g := ![![![24, -68, -4, 1], ![-73, 207, 12, -3], ![215, -613, -33, 9], ![-650, 1839, 107, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![-422, -201, -12, 3]] ![![6, 1, 0, 0]]
  ![![-1383, -632, -33, 9]] where
 M :=  ![![![-1383, -632, -33, 9]]]
 hmul := by decide  
 g :=  ![![![![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![-1383, -632, -33, 9]] ![![-125, -68, -4, 1]]
  ![![241, 0, 0, 0]] where
 M :=  ![![![-241, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![-1, 0, 0, 0]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1, I241N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
    exact isPrimeI241N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0 ⊙ MulI241N1)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0, 0]] 
 ![![251, 0, 0, 0], ![0, 251, 0, 0], ![0, 0, 251, 0], ![0, 0, 0, 251]] where
  M :=![![![251, 0, 0, 0], ![0, 251, 0, 0], ![0, 0, 251, 0], ![0, 0, 0, 251]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 4 2 7 [190, 159, 88, 130, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 225, 153, 73], [54, 239, 46, 158], [64, 37, 52, 20], [0, 1]]
 g := ![![[70, 214, 136, 196], [221, 25, 149, 17], [202, 210, 92], [114, 244, 44, 83], [37, 33, 217, 196], [134, 246, 121, 1], []],![[14, 114, 137, 53, 95, 144], [204, 43, 120, 58, 181, 12], [235, 235, 232], [169, 119, 35, 39, 235, 73], [120, 217, 28, 145, 42, 108], [236, 220, 120, 9, 227, 69], [158, 12, 165, 234, 39, 218]],![[180, 35, 124, 33, 105, 185], [208, 226, 104, 157, 92, 133], [242, 221, 36], [54, 106, 237, 248, 5, 178], [20, 113, 230, 211, 227, 99], [77, 182, 248, 130, 89, 167], [118, 163, 199, 247, 118, 98]],![[58, 23, 87, 2, 17, 106], [164, 10, 146, 98, 183, 79], [62, 103, 122], [23, 132, 129, 212, 79, 28], [20, 32, 162, 192, 190, 23], [44, 194, 136, 51, 218, 21], [12, 171, 49, 45, 45, 219]]]
 h' := ![![[3, 225, 153, 73], [178, 47, 125, 237], [228, 84, 222, 206], [177, 25, 124, 43], [249, 230, 144, 130], [142, 226, 149, 237], [0, 0, 0, 1], [0, 1]],![[54, 239, 46, 158], [90, 186, 80, 168], [20, 25, 59, 120], [69, 238, 79, 105], [45, 64, 182, 250], [33, 131, 42, 109], [127, 8, 201, 216], [3, 225, 153, 73]],![[64, 37, 52, 20], [44, 41, 9, 5], [221, 164, 110, 225], [45, 221, 11, 6], [20, 9, 180, 88], [115, 55, 45, 222], [6, 159, 225, 248], [54, 239, 46, 158]],![[0, 1], [28, 228, 37, 92], [250, 229, 111, 202], [22, 18, 37, 97], [10, 199, 247, 34], [6, 90, 15, 185], [79, 84, 76, 37], [64, 37, 52, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [110, 171], []]
 b := ![[], [], [194, 246, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where 
  n := 4
  hpos := by decide  
  P := [190, 159, 88, 130, 1]
  hirr := P251P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![820576927788, 784820991609, 241761868194, 23839624835]
  a := ![-1, 0, 1, 2]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![3269230788, 3126776859, 963194694, 94978585]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 3969126001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def PBC251 : ContainsPrimesAboveP 251 ![I251N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![251, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 251 (by decide) 𝕀

instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-681, -382, -27, 6]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![-681, -382, -27, 6]] 
 ![![257, 0, 0, 0], ![0, 257, 0, 0], ![49, 66, 1, 0], ![107, 62, 0, 1]] where
  M :=![![![-681, -382, -27, 6], ![2298, 1311, 98, -21], ![-8043, -4674, -369, 77], ![29491, 17521, 1486, -292]]]
  hmulB := by decide  
  f := ![![![-781, -355, -17, 5]], ![![1915, 879, 45, -12]], ![![325, 150, 8, -2]], ![![186, 89, 6, -1]]]
  g := ![![![0, 4, -27, 6], ![-1, -15, 98, -21], ![7, 58, -369, 77], ![-47, -243, 1486, -292]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [81, 221, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 256], [0, 1]]
 g := ![![[228, 165], [46], [249], [228], [134], [236], [11], [1]],![[0, 92], [46], [249], [228], [134], [236], [11], [1]]]
 h' := ![![[36, 256], [253, 200], [155, 118], [147, 136], [232, 182], [158, 52], [16, 218], [176, 36], [0, 1]],![[0, 1], [0, 57], [34, 139], [160, 121], [102, 75], [231, 205], [154, 39], [187, 221], [36, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [202]]
 b := ![[], [238, 101]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where 
  n := 2
  hpos := by decide  
  P := [81, 221, 1]
  hirr := P257P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![123093, 109100, 28780, 2394]
  a := ![-5, 0, 0, 2]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-6005, -7544, 28780, 2394]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-781, -355, -17, 5]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![-781, -355, -17, 5]] 
 ![![257, 0, 0, 0], ![0, 257, 0, 0], ![181, 190, 1, 0], ![48, 61, 0, 1]] where
  M :=![![![-781, -355, -17, 5], ![1915, 879, 45, -12], ![-4596, -2069, -81, 33], ![12639, 6360, 571, -48]]]
  hmulB := by decide  
  f := ![![![-681, -382, -27, 6]], ![![2298, 1311, 98, -21]], ![![1188, 682, 52, -11]], ![![533, 308, 24, -5]]]
  g := ![![![8, 10, -17, 5], ![-22, -27, 45, -12], ![33, 44, -81, 33], ![-344, -386, 571, -48]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P1 : CertificateIrreducibleZModOfList' 257 2 2 8 [12, 134, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [123, 256], [0, 1]]
 g := ![![[54, 81], [244], [100], [137], [67], [246], [223], [1]],![[251, 176], [244], [100], [137], [67], [246], [223], [1]]]
 h' := ![![[123, 256], [92, 9], [129, 66], [185, 10], [95, 213], [34, 18], [38, 62], [245, 123], [0, 1]],![[0, 1], [171, 248], [23, 191], [130, 247], [80, 44], [192, 239], [211, 195], [211, 134], [123, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [127, 163]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N1 : CertifiedPrimeIdeal' SI257N1 257 where 
  n := 2
  hpos := by decide  
  P := [12, 134, 1]
  hirr := P257P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![83032, 63693, 11169, -1510]
  a := ![-10, 2, 13, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-7261, -7651, 11169, -1510]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N1 B_one_repr
lemma NI257N1 : Nat.card (O ⧸ I257N1) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![-681, -382, -27, 6]] ![![-781, -355, -17, 5]]
  ![![257, 0, 0, 0]] where
 M :=  ![![![257, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![1, 0, 0, 0]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0)
instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0, 0], ![-119, -159, -4, 1]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0, 0], ![-119, -159, -4, 1]] 
 ![![263, 0, 0, 0], ![0, 263, 0, 0], ![150, 237, 1, 0], ![218, 0, 0, 1]] where
  M :=![![![263, 0, 0, 0], ![0, 263, 0, 0], ![0, 0, 263, 0], ![0, 0, 0, 263]], ![![-119, -159, -4, 1], ![383, 213, -79, -3], ![-1149, -613, -27, -82], ![-31406, -28373, -7173, -109]]]
  hmulB := by decide  
  f := ![![![4913770, 1611459, -1358377, -37669], ![-3177040, -4361329, 0, 0]], ![![-47621, -15530, 13191, 365], ![31034, 42343, 0, 0]], ![![2759581, 905040, -762854, -21155], ![-1784114, -2449293, 0, 0]], ![![4073043, 1335777, -1125954, -31224], ![-2633369, -3615094, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-150, -237, 263, 0], ![-218, 0, 0, 263]], ![![1, 3, -4, 1], ![49, 72, -79, -3], ![79, 22, -27, -82], ![4062, 6356, -7173, -109]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [186, 251, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 262], [0, 1]]
 g := ![![[229, 222], [162, 140], [18, 216], [108], [198], [190], [144], [1]],![[0, 41], [1, 123], [243, 47], [108], [198], [190], [144], [1]]]
 h' := ![![[12, 262], [113, 144], [71, 156], [156, 189], [16, 138], [200, 143], [185, 157], [77, 12], [0, 1]],![[0, 1], [0, 119], [102, 107], [57, 74], [94, 125], [75, 120], [228, 106], [221, 251], [12, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128]]
 b := ![[], [142, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where 
  n := 2
  hpos := by decide  
  P := [186, 251, 1]
  hirr := P263P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![39887, 37896, 10600, 894]
  a := ![1, 1, -4, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-6635, -9408, 10600, 894]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0, 0], ![-82, -42, -4, 1]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0, 0], ![-82, -42, -4, 1]] 
 ![![263, 0, 0, 0], ![0, 263, 0, 0], ![157, 25, 1, 0], ![20, 58, 0, 1]] where
  M :=![![![263, 0, 0, 0], ![0, 263, 0, 0], ![0, 0, 263, 0], ![0, 0, 0, 263]], ![![-82, -42, -4, 1], ![383, 250, 38, -3], ![-1149, -613, 10, 35], ![13405, 10471, 2187, 45]]]
  hmulB := by decide  
  f := ![![![1016818, 682458, 107610, -7383], ![-427638, -789789, 0, 0]], ![![-26047, -17485, -2758, 189], ![11046, 20251, 0, 0]], ![![604573, 405763, 63979, -4390], ![-254068, -469546, 0, 0]], ![![71600, 48052, 7576, -520], ![-30021, -55594, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-157, -25, 263, 0], ![-20, -58, 0, 263]], ![![2, 0, -4, 1], ![-21, -2, 38, -3], ![-13, -11, 10, 35], ![-1258, -178, 2187, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P1 : CertificateIrreducibleZModOfList' 263 2 2 8 [43, 247, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 262], [0, 1]]
 g := ![![[177, 104], [31, 207], [93, 64], [4], [153], [210], [256], [1]],![[0, 159], [187, 56], [65, 199], [4], [153], [210], [256], [1]]]
 h' := ![![[16, 262], [245, 34], [209, 101], [24, 8], [249, 2], [187, 68], [46, 90], [220, 16], [0, 1]],![[0, 1], [0, 229], [247, 162], [152, 255], [18, 261], [223, 195], [171, 173], [213, 247], [16, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [163, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N1 : CertifiedPrimeIdeal' SI263N1 263 where 
  n := 2
  hpos := by decide  
  P := [43, 247, 1]
  hirr := P263P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![30717, 27082, 6371, 573]
  a := ![-3, 1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-3730, -629, 6371, 573]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N1 B_one_repr
lemma NI263N1 : Nat.card (O ⧸ I263N1) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0, 0], ![-119, -159, -4, 1]] ![![263, 0, 0, 0], ![-82, -42, -4, 1]]
  ![![263, 0, 0, 0]] where
 M :=  ![![![69169, 0, 0, 0], ![-21566, -11046, -1052, 263]], ![![-31297, -41817, -1052, 263], ![-33138, -21829, -3419, 263]]]
 hmul := by decide  
 g :=  ![![![![263, 0, 0, 0]], ![![-82, -42, -4, 1]]], ![![![-119, -159, -4, 1]], ![![-126, -83, -13, 1]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0, 0]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0, 0]] 
 ![![269, 0, 0, 0], ![0, 269, 0, 0], ![0, 0, 269, 0], ![0, 0, 0, 269]] where
  M :=![![![269, 0, 0, 0], ![0, 269, 0, 0], ![0, 0, 269, 0], ![0, 0, 0, 269]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 4 2 8 [225, 74, 178, 43, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 130, 194, 41], [92, 190, 126, 117], [127, 217, 218, 111], [0, 1]]
 g := ![![[153, 118, 126, 133], [157, 122, 185], [99, 70, 144, 142], [15, 222, 47, 218], [219, 52, 218], [63, 92, 235], [1], []],![[73, 99, 70, 104, 59, 166], [268, 144, 239], [244, 30, 218, 169, 93, 203], [265, 170, 39, 36, 216, 222], [262, 248, 117], [148, 104, 105], [246, 214, 21], [221, 115, 67]],![[20, 149, 168, 187, 158, 126], [119, 1, 235], [170, 67, 136, 160, 56, 170], [12, 158, 29, 147, 264, 89], [169, 194, 213], [203, 190, 249], [148, 256, 203], [238, 108, 239]],![[89, 52, 219, 254, 193, 156], [49, 92, 244], [108, 3, 163, 60, 32, 174], [138, 53, 62, 233, 34, 201], [99, 81, 20], [203, 182, 245], [121, 177, 143], [97, 103, 216]]]
 h' := ![![[7, 130, 194, 41], [197, 161, 149, 183], [52, 147, 14, 202], [122, 94, 189, 45], [154, 207, 210, 196], [135, 137, 153, 73], [44, 195, 91, 226], [0, 0, 1], [0, 1]],![[92, 190, 126, 117], [241, 40, 188, 131], [4, 78, 267, 152], [2, 140, 120, 8], [16, 168, 203, 39], [18, 1, 9, 99], [184, 78, 13, 188], [89, 210, 2, 212], [7, 130, 194, 41]],![[127, 217, 218, 111], [10, 167, 4, 132], [238, 138, 105, 43], [3, 153, 219, 257], [115, 145, 256, 83], [91, 30, 198, 80], [263, 70, 81, 49], [106, 42, 76, 206], [92, 190, 126, 117]],![[0, 1], [17, 170, 197, 92], [236, 175, 152, 141], [259, 151, 10, 228], [229, 18, 138, 220], [56, 101, 178, 17], [1, 195, 84, 75], [222, 17, 190, 120], [127, 217, 218, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [18, 31, 134], []]
 b := ![[], [], [263, 77, 214, 146], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where 
  n := 4
  hpos := by decide  
  P := [225, 74, 178, 43, 1]
  hirr := P269P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![5403807691939, 5126948236894, 1560909084807, 151175487271]
  a := ![3, 0, 7, -4]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![20088504431, 19059287126, 5802636003, 561990659]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 5236114321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def PBC269 : ContainsPrimesAboveP 269 ![I269N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![269, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 269 (by decide) 𝕀

instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0, 0], ![-102, -67, -4, 1]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![271, 0, 0, 0], ![-102, -67, -4, 1]] 
 ![![271, 0, 0, 0], ![0, 271, 0, 0], ![77, 29, 1, 0], ![206, 49, 0, 1]] where
  M :=![![![271, 0, 0, 0], ![0, 271, 0, 0], ![0, 0, 271, 0], ![0, 0, 0, 271]], ![![-102, -67, -4, 1], ![383, 230, 13, -3], ![-1149, -613, -10, 10], ![3830, 2171, 187, 0]]]
  hmulB := by decide  
  f := ![![![16701921, 9844777, 549582, -124349], ![-8728639, -14142406, 0, 0]], ![![-62062, -36579, -2042, 462], ![32520, 52574, 0, 0]], ![![4738903, 2793297, 155935, -35282], ![-2476666, -4012696, 0, 0]], ![![12684698, 7476866, 417394, -94440], ![-6629189, -10740810, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-77, -29, 271, 0], ![-206, -49, 0, 271]], ![![0, 0, -4, 1], ![0, 0, 13, -3], ![-9, -3, -10, 10], ![-39, -12, 187, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [221, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [191, 270], [0, 1]]
 g := ![![[161, 89], [265, 174], [21, 37], [], [128], [233], [167], [1]],![[87, 182], [166, 97], [42, 234], [], [128], [233], [167], [1]]]
 h' := ![![[191, 270], [242, 38], [237, 170], [0, 151], [91], [97, 226], [10, 49], [50, 191], [0, 1]],![[0, 1], [183, 233], [187, 101], [115, 120], [91], [174, 45], [155, 222], [217, 80], [191, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [225, 175]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where 
  n := 2
  hpos := by decide  
  P := [221, 80, 1]
  hirr := P271P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![30095, 25593, 6372, 252]
  a := ![0, 1, 1, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-1891, -633, 6372, 252]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0, 0], ![-161, -67, -4, 1]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![271, 0, 0, 0], ![-161, -67, -4, 1]] 
 ![![271, 0, 0, 0], ![0, 271, 0, 0], ![171, 241, 1, 0], ![252, 84, 0, 1]] where
  M :=![![![271, 0, 0, 0], ![0, 271, 0, 0], ![0, 0, 271, 0], ![0, 0, 0, 271]], ![![-161, -67, -4, 1], ![383, 171, 13, -3], ![-1149, -613, -69, 10], ![3830, 2171, 187, -59]]]
  hmulB := by decide  
  f := ![![![18079129, 8302566, 682857, -153948], ![-12803937, -18174615, 0, 0]], ![![-68685, -31544, -2595, 585], ![48780, 69105, 0, 0]], ![![11346721, 5210811, 428571, -96620], ![-8035960, -11406660, 0, 0]], ![![16790256, 7710672, 634176, -142973], ![-11891196, -16878960, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-171, -241, 271, 0], ![-252, -84, 0, 271]], ![![1, 3, -4, 1], ![-4, -10, 13, -3], ![30, 56, -69, 10], ![-49, -140, 187, -59]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P1 : CertificateIrreducibleZModOfList' 271 2 2 8 [184, 119, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [152, 270], [0, 1]]
 g := ![![[117, 242], [104, 63], [72, 67], [78, 49], [248], [167], [69], [1]],![[45, 29], [195, 208], [229, 204], [209, 222], [248], [167], [69], [1]]]
 h' := ![![[152, 270], [105, 28], [31, 92], [11, 107], [178, 264], [108, 178], [22, 80], [87, 152], [0, 1]],![[0, 1], [25, 243], [194, 179], [15, 164], [198, 7], [64, 93], [258, 191], [156, 119], [152, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [219]]
 b := ![[], [79, 245]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N1 : CertifiedPrimeIdeal' SI271N1 271 where 
  n := 2
  hpos := by decide  
  P := [184, 119, 1]
  hirr := P271P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![6194, 5663, 1757, 40]
  a := ![-1, 3, 4, 0]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-1123, -1554, 1757, 40]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N1 B_one_repr
lemma NI271N1 : Nat.card (O ⧸ I271N1) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![271, 0, 0, 0], ![-102, -67, -4, 1]] ![![271, 0, 0, 0], ![-161, -67, -4, 1]]
  ![![271, 0, 0, 0]] where
 M :=  ![![![73441, 0, 0, 0], ![-43631, -18157, -1084, 271]], ![![-27642, -18157, -1084, 271], ![-813, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![271, 0, 0, 0]], ![![-161, -67, -4, 1]]], ![![![-102, -67, -4, 1]], ![![-3, 0, 0, 0]]]]
 hle2 := by decide  


def PBC271 : ContainsPrimesAboveP 271 ![I271N0, I271N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
    exact isPrimeI271N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 271 (by decide) (𝕀 ⊙ MulI271N0)
instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0, 0], ![32, 1, 0, 0]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![277, 0, 0, 0], ![32, 1, 0, 0]] 
 ![![277, 0, 0, 0], ![32, 1, 0, 0], ![84, 0, 1, 0], ![82, 0, 0, 1]] where
  M :=![![![277, 0, 0, 0], ![0, 277, 0, 0], ![0, 0, 277, 0], ![0, 0, 0, 277]], ![![32, 1, 0, 0], ![0, 32, 1, 0], ![0, 0, 32, 1], ![383, 332, 80, 33]]]
  hmulB := by decide  
  f := ![![![1569, -21711, -712, -1], ![-13573, 188360, 277, 0]], ![![96, -2557, -112, -1], ![-830, 22160, 277, 0]], ![![420, -6611, -239, -1], ![-3633, 57340, 277, 0]], ![![426, -6447, -234, -1], ![-3685, 55922, 278, 0]]]
  g := ![![![1, 0, 0, 0], ![-32, 277, 0, 0], ![-84, 0, 277, 0], ![-82, 0, 0, 277]], ![![0, 1, 0, 0], ![-4, 32, 1, 0], ![-10, 0, 32, 1], ![-71, 332, 80, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N0 : Nat.card (O ⧸ I277N0) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N0)

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := prime_ideal_of_norm_prime hp277.out _ NI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0, 0], ![-114, 1, 0, 0]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![277, 0, 0, 0], ![-114, 1, 0, 0]] 
 ![![277, 0, 0, 0], ![163, 1, 0, 0], ![23, 0, 1, 0], ![129, 0, 0, 1]] where
  M :=![![![277, 0, 0, 0], ![0, 277, 0, 0], ![0, 0, 277, 0], ![0, 0, 0, 277]], ![![-114, 1, 0, 0], ![0, -114, 1, 0], ![0, 0, -114, 1], ![383, 332, 80, -113]]]
  hmulB := by decide  
  f := ![![![61333, -484354, 4928, -6], ![149026, -1175588, 1662, 0]], ![![36253, -284862, 2952, -4], ![88087, -691392, 1108, 0]], ![![5405, -40061, 465, -1], ![13133, -97226, 277, 0]], ![![28605, -225468, 2318, -3], ![69504, -547238, 832, 0]]]
  g := ![![![1, 0, 0, 0], ![-163, 277, 0, 0], ![-23, 0, 277, 0], ![-129, 0, 0, 277]], ![![-1, 1, 0, 0], ![67, -114, 1, 0], ![9, 0, -114, 1], ![-148, 332, 80, -113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1

def I277N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0, 0], ![-113, 1, 0, 0]] i)))

def SI277N2: IdealEqSpanCertificate' Table ![![277, 0, 0, 0], ![-113, 1, 0, 0]] 
 ![![277, 0, 0, 0], ![164, 1, 0, 0], ![250, 0, 1, 0], ![273, 0, 0, 1]] where
  M :=![![![277, 0, 0, 0], ![0, 277, 0, 0], ![0, 0, 277, 0], ![0, 0, 0, 277]], ![![-113, 1, 0, 0], ![0, -113, 1, 0], ![0, 0, -113, 1], ![383, 332, 80, -112]]]
  hmulB := by decide  
  f := ![![![13109, 336, 352104, -3116], ![32132, 1108, 863132, 0]], ![![7798, 270, 214697, -1900], ![19114, 831, 526300, 0]], ![![11686, 349, 317752, -2812], ![28644, 1109, 778924, 0]], ![![12781, 385, 347019, -3071], ![31328, 1221, 850668, 0]]]
  g := ![![![1, 0, 0, 0], ![-164, 277, 0, 0], ![-250, 0, 277, 0], ![-273, 0, 0, 277]], ![![-1, 1, 0, 0], ![66, -113, 1, 0], ![101, 0, -113, 1], ![-157, 332, 80, -112]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N2 : Nat.card (O ⧸ I277N2) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N2)

lemma isPrimeI277N2 : Ideal.IsPrime I277N2 := prime_ideal_of_norm_prime hp277.out _ NI277N2

def I277N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0, 0], ![-83, 1, 0, 0]] i)))

def SI277N3: IdealEqSpanCertificate' Table ![![277, 0, 0, 0], ![-83, 1, 0, 0]] 
 ![![277, 0, 0, 0], ![194, 1, 0, 0], ![36, 0, 1, 0], ![218, 0, 0, 1]] where
  M :=![![![277, 0, 0, 0], ![0, 277, 0, 0], ![0, 0, 277, 0], ![0, 0, 0, 277]], ![![-83, 1, 0, 0], ![0, -83, 1, 0], ![0, 0, -83, 1], ![383, 332, 80, -82]]]
  hmulB := by decide  
  f := ![![![45070, -214351, 2825, -3], ![150411, -713552, 831, 0]], ![![31541, -150029, 1969, -2], ![105261, -499431, 554, 0]], ![![6084, -27712, 416, -1], ![20304, -92240, 277, 0]], ![![35597, -168645, 2276, -3], ![118797, -561396, 832, 0]]]
  g := ![![![1, 0, 0, 0], ![-194, 277, 0, 0], ![-36, 0, 277, 0], ![-218, 0, 0, 277]], ![![-1, 1, 0, 0], ![58, -83, 1, 0], ![10, 0, -83, 1], ![-177, 332, 80, -82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N3 : Nat.card (O ⧸ I277N3) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N3)

lemma isPrimeI277N3 : Ideal.IsPrime I277N3 := prime_ideal_of_norm_prime hp277.out _ NI277N3
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![277, 0, 0, 0], ![32, 1, 0, 0]] ![![277, 0, 0, 0], ![-114, 1, 0, 0]]
  ![![277, 0, 0, 0], ![-65, -72, -4, 1]] where
 M :=  ![![![76729, 0, 0, 0], ![-31578, 277, 0, 0]], ![![8864, 277, 0, 0], ![-3648, -82, 1, 0]]]
 hmul := by decide  
 g :=  ![![![![452546699, 297783024, 7700184, -3219190], ![-183718034, -358477888, 0, 0]], ![![-186257794, -122560607, -3169216, 1324944], ![75614352, 147541280, 0, 0]]], ![![![52268613, 34393609, 889364, -371813], ![-21219031, -41403744, 0, 0]], ![![-21512517, -14155570, -366039, 153029], ![8733463, 17040832, 0, 0]]]]
 hle2 := by decide  

def MulI277N1 : IdealMulLeCertificate' Table 
  ![![277, 0, 0, 0], ![-65, -72, -4, 1]] ![![277, 0, 0, 0], ![-113, 1, 0, 0]]
  ![![277, 0, 0, 0], ![-3871, -1893, -115, 29]] where
 M :=  ![![![76729, 0, 0, 0], ![-31301, 277, 0, 0]], ![![-18005, -19944, -1108, 277], ![7728, 8403, 460, -116]]]
 hmul := by decide  
 g :=  ![![![![277, 0, 0, 0], ![0, 0, 0, 0]], ![![3758, 1894, 115, -29], ![277, 0, 0, 0]]], ![![![3806, 1821, 111, -28], ![277, 0, 0, 0]], ![![3843, 1896, 115, -29], ![273, 0, 0, 0]]]]
 hle2 := by decide  

def MulI277N2 : IdealMulLeCertificate' Table 
  ![![277, 0, 0, 0], ![-3871, -1893, -115, 29]] ![![277, 0, 0, 0], ![-83, 1, 0, 0]]
  ![![277, 0, 0, 0]] where
 M :=  ![![![76729, 0, 0, 0], ![-22991, 277, 0, 0]], ![![-1072267, -524361, -31855, 8033], ![332400, 162876, 9972, -2493]]]
 hmul := by decide  
 g :=  ![![![![277, 0, 0, 0]], ![![-83, 1, 0, 0]]], ![![![-3871, -1893, -115, 29]], ![![1200, 588, 36, -9]]]]
 hle2 := by decide  


def PBC277 : ContainsPrimesAboveP 277 ![I277N0, I277N1, I277N2, I277N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
    exact isPrimeI277N1
    exact isPrimeI277N2
    exact isPrimeI277N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 277 (by decide) (𝕀 ⊙ MulI277N0 ⊙ MulI277N1 ⊙ MulI277N2)
instance hp281 : Fact (Nat.Prime 281) := {out := by norm_num}

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, 0, 0, 0]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![281, 0, 0, 0]] 
 ![![281, 0, 0, 0], ![0, 281, 0, 0], ![0, 0, 281, 0], ![0, 0, 0, 281]] where
  M :=![![![281, 0, 0, 0], ![0, 281, 0, 0], ![0, 0, 281, 0], ![0, 0, 0, 281]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 4 2 8 [65, 26, 220, 55, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 162, 141, 88], [58, 277, 274, 199], [163, 122, 147, 275], [0, 1]]
 g := ![![[108, 180, 156, 247], [272, 62, 155], [51, 140, 267], [235, 113, 259, 57], [227, 4, 8, 36], [264, 11, 215], [1], []],![[19, 202, 43, 86, 79, 151], [130, 226, 271], [268, 37, 34], [121, 46, 266, 104, 134, 229], [34, 112, 117, 188, 280, 206], [170, 96, 228], [21, 238, 252], [56, 164, 157]],![[63, 128, 132, 260, 142, 190], [153, 17, 236], [67, 134, 163], [202, 250, 154, 18, 111, 61], [206, 218, 37, 169, 155, 188], [26, 270, 215], [1], [47, 0, 261]],![[134, 255, 67, 55, 249, 185], [52, 126, 183], [48, 68, 4], [235, 152, 206, 24, 26, 152], [63, 266, 165, 186, 188, 275], [8, 201, 252], [21, 238, 252], [89, 190, 36]]]
 h' := ![![[5, 162, 141, 88], [236, 10, 173, 99], [142, 51, 272, 163], [180, 250, 239, 148], [138, 101, 9, 251], [272, 16, 209, 275], [216, 255, 61, 226], [0, 0, 1], [0, 1]],![[58, 277, 274, 199], [86, 208, 152, 48], [227, 169, 171, 73], [266, 169, 18, 92], [100, 99, 212, 219], [249, 14, 187, 217], [79, 64, 21, 60], [38, 182, 22, 231], [5, 162, 141, 88]],![[163, 122, 147, 275], [169, 194, 22, 138], [29, 28, 6, 123], [13, 14, 96, 43], [78, 36, 217, 28], [198, 24, 259, 69], [157, 255, 5, 226], [28, 0, 280], [58, 277, 274, 199]],![[0, 1], [145, 150, 215, 277], [232, 33, 113, 203], [82, 129, 209, 279], [57, 45, 124, 64], [253, 227, 188, 1], [140, 269, 194, 50], [271, 99, 259, 50], [163, 122, 147, 275]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [97, 188, 140], []]
 b := ![[], [], [182, 246, 248, 269], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where 
  n := 4
  hpos := by decide  
  P := [65, 26, 220, 55, 1]
  hirr := P281P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![100239295118613, 95789812493111, 29471526103734, 2900754779345]
  a := ![-1, 1, 0, 7]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![356723470173, 340889012431, 104880875814, 10322970745]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 6234839521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def PBC281 : ContainsPrimesAboveP 281 ![I281N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI281N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![281, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 281 (by decide) 𝕀



lemma PB692I5_primes (p : ℕ) :
  p ∈ Set.range ![233, 239, 241, 251, 257, 263, 269, 271, 277, 281] ↔ Nat.Prime p ∧ 229 < p ∧ p ≤ 281 := by
  rw [← List.mem_ofFn']
  convert primes_range 229 281 (by omega)
  rfl

def PB692I5 : PrimesBelowBoundCertificateInterval' O 229 281 692 where
  m := 10
  g := ![2, 2, 3, 1, 2, 2, 1, 2, 4, 1]
  P := ![233, 239, 241, 251, 257, 263, 269, 271, 277, 281]
  hP := PB692I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1, I241N2]
    · exact ![I251N0]
    · exact ![I257N0, I257N1]
    · exact ![I263N0, I263N1]
    · exact ![I269N0]
    · exact ![I271N0, I271N1]
    · exact ![I277N0, I277N1, I277N2, I277N3]
    · exact ![I281N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
    · exact PBC257
    · exact PBC263
    · exact PBC269
    · exact PBC271
    · exact PBC277
    · exact PBC281
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![54289, 54289]
    · exact ![57121, 57121]
    · exact ![58081, 241, 241]
    · exact ![3969126001]
    · exact ![66049, 66049]
    · exact ![69169, 69169]
    · exact ![5236114321]
    · exact ![73441, 73441]
    · exact ![277, 277, 277, 277]
    · exact ![6234839521]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
      exact NI277N1
      exact NI277N2
      exact NI277N3
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
  Il := ![[], [], [I241N1, I241N2], [], [], [], [], [], [I277N0, I277N1, I277N2, I277N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
