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
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-321, -146, -7, 2]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-321, -146, -7, 2]] 
 ![![179, 0, 0, 0], ![0, 179, 0, 0], ![36, 83, 1, 0], ![55, 128, 0, 1]] where
  M :=![![![-321, -146, -7, 2], ![766, 343, 14, -5], ![-1915, -894, -57, 9], ![3447, 1073, -174, -48]]]
  hmulB := by decide  
  f := ![![![-411, -213, -11, 3]], ![![1149, 585, 27, -8]], ![![433, 220, 10, -3]], ![![736, 371, 16, -5]]]
  g := ![![![-1, 1, -7, 2], ![3, -1, 14, -5], ![-2, 15, -57, 9], ![69, 121, -174, -48]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [85, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 178], [0, 1]]
 g := ![![[125, 139], [28, 59], [93], [4], [31, 147], [52, 158], [1]],![[0, 40], [11, 120], [93], [4], [110, 32], [143, 21], [1]]]
 h' := ![![[115, 178], [126, 153], [115, 43], [12, 123], [50, 2], [55, 133], [94, 115], [0, 1]],![[0, 1], [0, 26], [48, 136], [16, 56], [101, 177], [135, 46], [73, 64], [115, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [81, 120]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where 
  n := 2
  hpos := by decide  
  P := [85, 64, 1]
  hirr := P179P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![33023, 29637, 8196, 596]
  a := ![0, -1, -1, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-1647, -4061, 8196, 596]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-411, -213, -11, 3]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-411, -213, -11, 3]] 
 ![![179, 0, 0, 0], ![0, 179, 0, 0], ![54, 95, 1, 0], ![61, 158, 0, 1]] where
  M :=![![![-411, -213, -11, 3], ![1149, 585, 27, -8], ![-3064, -1507, -55, 19], ![7277, 3244, 13, -36]]]
  hmulB := by decide  
  f := ![![![-321, -146, -7, 2]], ![![766, 343, 14, -5]], ![![299, 133, 5, -2]], ![![586, 259, 9, -4]]]
  g := ![![![0, 2, -11, 3], ![1, -4, 27, -8], ![-7, 4, -55, 19], ![49, 43, 13, -36]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [94, 115, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 178], [0, 1]]
 g := ![![[125, 173], [132, 149], [75], [89], [170, 77], [49, 158], [1]],![[99, 6], [2, 30], [75], [89], [86, 102], [137, 21], [1]]]
 h' := ![![[64, 178], [122, 129], [73, 68], [121, 84], [130, 39], [48, 163], [85, 64], [0, 1]],![[0, 1], [144, 50], [129, 111], [127, 95], [120, 140], [98, 16], [64, 115], [64, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [159, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where 
  n := 2
  hpos := by decide  
  P := [94, 115, 1]
  hirr := P179P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![1552933, 1297952, 275524, -6046]
  a := ![-2, 3, -64, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-72383, -133640, 275524, -6046]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-321, -146, -7, 2]] ![![-411, -213, -11, 3]]
  ![![179, 0, 0, 0]] where
 M :=  ![![![179, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![1, 0, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0, 0], ![37, 1, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0, 0], ![37, 1, 0, 0]] 
 ![![181, 0, 0, 0], ![37, 1, 0, 0], ![79, 0, 1, 0], ![154, 0, 0, 1]] where
  M :=![![![181, 0, 0, 0], ![0, 181, 0, 0], ![0, 0, 181, 0], ![0, 0, 0, 181]], ![![37, 1, 0, 0], ![0, 37, 1, 0], ![0, 0, 37, 1], ![383, 332, 80, 38]]]
  hmulB := by decide  
  f := ![![![3516, -238, 278786, 7535], ![-17195, 1629, -1363835, 0]], ![![666, -56, 60826, 1644], ![-3257, 362, -297564, 0]], ![![1488, -108, 121652, 3288], ![-7277, 725, -595128, 0]], ![![3014, -207, 237199, 6411], ![-14740, 1411, -1160390, 0]]]
  g := ![![![1, 0, 0, 0], ![-37, 181, 0, 0], ![-79, 0, 181, 0], ![-154, 0, 0, 181]], ![![0, 1, 0, 0], ![-8, 37, 1, 0], ![-17, 0, 37, 1], ![-133, 332, 80, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0, 0], ![64, 1, 0, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0, 0], ![64, 1, 0, 0]] 
 ![![181, 0, 0, 0], ![64, 1, 0, 0], ![67, 0, 1, 0], ![56, 0, 0, 1]] where
  M :=![![![181, 0, 0, 0], ![0, 181, 0, 0], ![0, 0, 181, 0], ![0, 0, 0, 181]], ![![64, 1, 0, 0], ![0, 64, 1, 0], ![0, 0, 64, 1], ![383, 332, 80, 65]]]
  hmulB := by decide  
  f := ![![![9217, -630576, -11007, -18], ![-26064, 1783755, 3258, 0]], ![![3136, -222991, -3933, -7], ![-8868, 630785, 1267, 0]], ![![3415, -233419, -4096, -7], ![-9657, 660289, 1267, 0]], ![![2840, -195133, -3434, -6], ![-8031, 551986, 1087, 0]]]
  g := ![![![1, 0, 0, 0], ![-64, 181, 0, 0], ![-67, 0, 181, 0], ![-56, 0, 0, 181]], ![![0, 1, 0, 0], ![-23, 64, 1, 0], ![-24, 0, 64, 1], ![-165, 332, 80, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0, 0], ![-89, 1, 0, 0]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![181, 0, 0, 0], ![-89, 1, 0, 0]] 
 ![![181, 0, 0, 0], ![92, 1, 0, 0], ![43, 0, 1, 0], ![26, 0, 0, 1]] where
  M :=![![![181, 0, 0, 0], ![0, 181, 0, 0], ![0, 0, 181, 0], ![0, 0, 0, 181]], ![![-89, 1, 0, 0], ![0, -89, 1, 0], ![0, 0, -89, 1], ![383, 332, 80, -88]]]
  hmulB := by decide  
  f := ![![![25900, -648033, 8791, -17], ![52671, -1317318, 3077, 0]], ![![13262, -329271, 4499, -9], ![26970, -669338, 1629, 0]], ![![6274, -153951, 2085, -4], ![12759, -312948, 724, 0]], ![![3806, -93004, 1312, -3], ![7740, -189056, 544, 0]]]
  g := ![![![1, 0, 0, 0], ![-92, 181, 0, 0], ![-43, 0, 181, 0], ![-26, 0, 0, 181]], ![![-1, 1, 0, 0], ![45, -89, 1, 0], ![21, 0, -89, 1], ![-173, 332, 80, -88]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2

def I181N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0, 0], ![-13, 1, 0, 0]] i)))

def SI181N3: IdealEqSpanCertificate' Table ![![181, 0, 0, 0], ![-13, 1, 0, 0]] 
 ![![181, 0, 0, 0], ![168, 1, 0, 0], ![12, 0, 1, 0], ![156, 0, 0, 1]] where
  M :=![![![181, 0, 0, 0], ![0, 181, 0, 0], ![0, 0, 181, 0], ![0, 0, 0, 181]], ![![-13, 1, 0, 0], ![0, -13, 1, 0], ![0, 0, -13, 1], ![383, 332, 80, -12]]]
  hmulB := by decide  
  f := ![![![209, -3, 30211, -2324], ![2896, 181, 420644, 0]], ![![378, -28213, 2181, -1], ![5250, -392408, 181, 0]], ![![27, -1991, 166, -1], ![375, -27692, 181, 0]], ![![182, 0, 26038, -2003], ![2522, 194, 362544, 0]]]
  g := ![![![1, 0, 0, 0], ![-168, 181, 0, 0], ![-12, 0, 181, 0], ![-156, 0, 0, 181]], ![![-1, 1, 0, 0], ![12, -13, 1, 0], ![0, 0, -13, 1], ![-301, 332, 80, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N3 : Nat.card (O ⧸ I181N3) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N3)

lemma isPrimeI181N3 : Ideal.IsPrime I181N3 := prime_ideal_of_norm_prime hp181.out _ NI181N3
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0, 0], ![37, 1, 0, 0]] ![![181, 0, 0, 0], ![64, 1, 0, 0]]
  ![![181, 0, 0, 0], ![-127, -92, -4, 1]] where
 M :=  ![![![32761, 0, 0, 0], ![11584, 181, 0, 0]], ![![6697, 181, 0, 0], ![2368, 101, 1, 0]]]
 hmul := by decide  
 g :=  ![![![![30241298, 12530987, -2161636, -236081], ![-27541684, -23424115, 0, 0]], ![![10659730, 4417066, -761944, -83216], ![-9707935, -8256677, 0, 0]]], ![![![6148534, 2547757, -439492, -47999], ![-5599597, -4762472, 0, 0]], ![![2167275, 898062, -154911, -16919], ![-1973692, -1678677, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![181, 0, 0, 0], ![-127, -92, -4, 1]] ![![181, 0, 0, 0], ![-89, 1, 0, 0]]
  ![![181, 0, 0, 0], ![-4484, -2303, -135, 34]] where
 M :=  ![![![32761, 0, 0, 0], ![-16109, 181, 0, 0]], ![![-22987, -16652, -724, 181], ![11686, 8393, 344, -92]]]
 hmul := by decide  
 g :=  ![![![![181, 0, 0, 0], ![0, 0, 0, 0]], ![![4395, 2304, 135, -34], ![181, 0, 0, 0]]], ![![![4357, 2211, 131, -33], ![181, 0, 0, 0]], ![![3954, 2044, 119, -30], ![157, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N2 : IdealMulLeCertificate' Table 
  ![![181, 0, 0, 0], ![-4484, -2303, -135, 34]] ![![181, 0, 0, 0], ![-13, 1, 0, 0]]
  ![![181, 0, 0, 0]] where
 M :=  ![![![32761, 0, 0, 0], ![-2353, 181, 0, 0]], ![![-811604, -416843, -24435, 6154], ![71314, 36743, 2172, -543]]]
 hmul := by decide  
 g :=  ![![![![181, 0, 0, 0]], ![![-13, 1, 0, 0]]], ![![![-4484, -2303, -135, 34]], ![![394, 203, 12, -3]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2, I181N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
    exact isPrimeI181N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1 ⊙ MulI181N2)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0, 0]] 
 ![![191, 0, 0, 0], ![0, 191, 0, 0], ![0, 0, 191, 0], ![0, 0, 0, 191]] where
  M :=![![![191, 0, 0, 0], ![0, 191, 0, 0], ![0, 0, 191, 0], ![0, 0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 4 2 7 [189, 185, 189, 115, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [186, 163, 2, 60], [71, 31, 126, 137], [10, 187, 63, 185], [0, 1]]
 g := ![![[93, 49, 144, 13], [163, 5, 141, 5], [98, 35, 57, 43], [129, 174, 94, 120], [105, 67, 36, 12], [76, 1], []],![[30, 78, 117, 96, 98, 49], [101, 117, 76, 162, 51, 51], [137, 91, 172, 16, 52, 92], [59, 100, 185, 7, 165, 30], [129, 48, 36, 7, 3, 102], [160, 128, 187, 155, 143, 43], [122, 137, 162]],![[114, 30, 113, 93, 61, 19], [41, 188, 103, 85, 147, 44], [156, 77, 65, 154, 166, 155], [58, 186, 135, 112, 96, 73], [125, 179, 110, 39, 26, 173], [157, 122, 143, 178, 10, 94], [135, 9, 51]],![[141, 3, 188, 39, 98, 82], [101, 105, 10, 163, 106, 186], [171, 22, 134, 56, 64, 179], [75, 67, 167, 148, 97, 126], [107, 105, 52, 66, 81, 21], [143, 140, 0, 42, 31, 82], [50, 70, 36]]]
 h' := ![![[186, 163, 2, 60], [135, 58, 156, 83], [5, 181, 29, 177], [67, 146, 78, 59], [19, 184, 104, 87], [152, 76, 158, 48], [0, 0, 1], [0, 1]],![[71, 31, 126, 137], [185, 34, 187, 2], [140, 118, 175, 121], [175, 13, 95, 72], [16, 146, 31, 67], [78, 142, 30, 21], [78, 140, 53, 65], [186, 163, 2, 60]],![[10, 187, 63, 185], [14, 128, 75, 9], [23, 86, 127, 29], [189, 160, 148, 117], [185, 184, 8, 56], [103, 63, 67, 183], [154, 73, 179, 32], [71, 31, 126, 137]],![[0, 1], [34, 162, 155, 97], [161, 188, 51, 55], [190, 63, 61, 134], [2, 59, 48, 172], [141, 101, 127, 130], [9, 169, 149, 94], [10, 187, 63, 185]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [67, 97, 28], []]
 b := ![[], [], [166, 62, 177, 142], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where 
  n := 4
  hpos := by decide  
  P := [189, 185, 189, 115, 1]
  hirr := P191P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![2861126016524, 2731243839888, 839028217754, 82388564340]
  a := ![-1, 1, 1, -3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![14979717364, 14299705968, 4392817894, 431353740]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 1330863361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def PBC191 : ContainsPrimesAboveP 191 ![I191N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![191, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 191 (by decide) 𝕀

instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0], ![21, 1, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0, 0], ![21, 1, 0, 0]] 
 ![![193, 0, 0, 0], ![21, 1, 0, 0], ![138, 0, 1, 0], ![190, 0, 0, 1]] where
  M :=![![![193, 0, 0, 0], ![0, 193, 0, 0], ![0, 0, 193, 0], ![0, 0, 0, 193]], ![![21, 1, 0, 0], ![0, 21, 1, 0], ![0, 0, 21, 1], ![383, 332, 80, 22]]]
  hmulB := by decide  
  f := ![![![883, 21, 6761, 322], ![-8106, 193, -62146, 0]], ![![63, -18, 965, 46], ![-578, 193, -8878, 0]], ![![654, 10, 4829, 230], ![-6004, 194, -44390, 0]], ![![898, 24, 6656, 317], ![-8244, 172, -61180, 0]]]
  g := ![![![1, 0, 0, 0], ![-21, 193, 0, 0], ![-138, 0, 193, 0], ![-190, 0, 0, 193]], ![![0, 1, 0, 0], ![-3, 21, 1, 0], ![-16, 0, 21, 1], ![-113, 332, 80, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0], ![34, 1, 0, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0, 0], ![34, 1, 0, 0]] 
 ![![193, 0, 0, 0], ![34, 1, 0, 0], ![2, 0, 1, 0], ![125, 0, 0, 1]] where
  M :=![![![193, 0, 0, 0], ![0, 193, 0, 0], ![0, 0, 193, 0], ![0, 0, 0, 193]], ![![34, 1, 0, 0], ![0, 34, 1, 0], ![0, 0, 34, 1], ![383, 332, 80, 35]]]
  hmulB := by decide  
  f := ![![![4081, -390, 580433, 17072], ![-23160, 2895, -3294896, 0]], ![![714, -81, 107709, 3168], ![-4052, 579, -611424, 0]], ![![6, -34, 5983, 176], ![-34, 194, -33968, 0]], ![![2653, -256, 375928, 11057], ![-15056, 1896, -2134000, 0]]]
  g := ![![![1, 0, 0, 0], ![-34, 193, 0, 0], ![-2, 0, 193, 0], ![-125, 0, 0, 193]], ![![0, 1, 0, 0], ![-6, 34, 1, 0], ![-1, 0, 34, 1], ![-80, 332, 80, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0], ![59, 1, 0, 0]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![193, 0, 0, 0], ![59, 1, 0, 0]] 
 ![![193, 0, 0, 0], ![59, 1, 0, 0], ![186, 0, 1, 0], ![27, 0, 0, 1]] where
  M :=![![![193, 0, 0, 0], ![0, 193, 0, 0], ![0, 0, 193, 0], ![0, 0, 0, 193]], ![![59, 1, 0, 0], ![0, 59, 1, 0], ![0, 0, 59, 1], ![383, 332, 80, 60]]]
  hmulB := by decide  
  f := ![![![3895, -76752, -1420, -2], ![-12738, 251286, 386, 0]], ![![1121, -23463, -457, -1], ![-3666, 76814, 193, 0]], ![![3618, -73984, -1373, -2], ![-11832, 242216, 386, 0]], ![![411, -10772, -242, -1], ![-1344, 35260, 194, 0]]]
  g := ![![![1, 0, 0, 0], ![-59, 193, 0, 0], ![-186, 0, 193, 0], ![-27, 0, 0, 193]], ![![0, 1, 0, 0], ![-19, 59, 1, 0], ![-57, 0, 59, 1], ![-185, 332, 80, 60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2

def I193N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0], ![78, 1, 0, 0]] i)))

def SI193N3: IdealEqSpanCertificate' Table ![![193, 0, 0, 0], ![78, 1, 0, 0]] 
 ![![193, 0, 0, 0], ![78, 1, 0, 0], ![92, 0, 1, 0], ![158, 0, 0, 1]] where
  M :=![![![193, 0, 0, 0], ![0, 193, 0, 0], ![0, 0, 193, 0], ![0, 0, 0, 193]], ![![78, 1, 0, 0], ![0, 78, 1, 0], ![0, 0, 78, 1], ![383, 332, 80, 79]]]
  hmulB := by decide  
  f := ![![![5305, -2116, 1218488, 15622], ![-13124, 5404, -3015046, 0]], ![![2106, -909, 501060, 6424], ![-5210, 2316, -1239832, 0]], ![![2528, -1060, 580774, 7446], ![-6254, 2703, -1437078, 0]], ![![4406, -1784, 997518, 12789], ![-10900, 4554, -2468276, 0]]]
  g := ![![![1, 0, 0, 0], ![-78, 193, 0, 0], ![-92, 0, 193, 0], ![-158, 0, 0, 193]], ![![0, 1, 0, 0], ![-32, 78, 1, 0], ![-38, 0, 78, 1], ![-235, 332, 80, 79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N3 : Nat.card (O ⧸ I193N3) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N3)

lemma isPrimeI193N3 : Ideal.IsPrime I193N3 := prime_ideal_of_norm_prime hp193.out _ NI193N3
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0, 0], ![21, 1, 0, 0]] ![![193, 0, 0, 0], ![34, 1, 0, 0]]
  ![![-407, -204, -11, 3]] where
 M :=  ![![![37249, 0, 0, 0], ![6562, 193, 0, 0]], ![![4053, 193, 0, 0], ![714, 55, 1, 0]]]
 hmul := by decide  
 g :=  ![![![![69287, 49022, 5790, -965]], ![![10291, 7335, 874, -145]]], ![![![5624, 4033, 484, -80]], ![![832, 602, 73, -12]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![-407, -204, -11, 3]] ![![193, 0, 0, 0], ![59, 1, 0, 0]]
  ![![193, 0, 0, 0], ![-2345, -1306, -71, 18]] where
 M :=  ![![![-78551, -39372, -2123, 579], ![-22864, -11447, -613, 169]]]
 hmul := by decide  
 g :=  ![![![![1938, 1102, 60, -15], ![193, 0, 0, 0]], ![![647, 367, 20, -5], ![63, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N2 : IdealMulLeCertificate' Table 
  ![![193, 0, 0, 0], ![-2345, -1306, -71, 18]] ![![193, 0, 0, 0], ![78, 1, 0, 0]]
  ![![193, 0, 0, 0]] where
 M :=  ![![![37249, 0, 0, 0], ![15054, 193, 0, 0]], ![![-452585, -252058, -13703, 3474], ![-176016, -98237, -5404, 1351]]]
 hmul := by decide  
 g :=  ![![![![193, 0, 0, 0]], ![![78, 1, 0, 0]]], ![![![-2345, -1306, -71, 18]], ![![-912, -509, -28, 7]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2, I193N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
    exact isPrimeI193N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1 ⊙ MulI193N2)
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0, 0]] 
 ![![197, 0, 0, 0], ![0, 197, 0, 0], ![0, 0, 197, 0], ![0, 0, 0, 197]] where
  M :=![![![197, 0, 0, 0], ![0, 197, 0, 0], ![0, 0, 197, 0], ![0, 0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 4 2 7 [119, 143, 113, 107, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [126, 123, 115, 169], [13, 8, 196, 23], [148, 65, 83, 5], [0, 1]]
 g := ![![[138, 5, 91, 154], [127, 70, 150], [68, 131, 146, 26], [107, 96, 9], [67, 153, 190], [107, 90, 1], []],![[125, 164, 180, 183, 192, 154], [164, 50, 112], [51, 130, 67, 21, 120, 196], [107, 177, 97], [127, 166, 136], [66, 40, 168], [141, 155, 164, 157, 32, 112]],![[126, 187, 139, 27, 59, 133], [191, 180, 193], [114, 183, 134, 60, 107, 55], [120, 190, 107], [92, 56, 136], [157, 176, 90], [169, 66, 161, 48, 93, 150]],![[5, 51, 8, 5, 158, 84], [172, 172, 142], [154, 81, 64, 111, 99, 8], [107, 110, 97], [29, 162, 64], [39, 72, 116], [105, 185, 29, 18, 139, 125]]]
 h' := ![![[126, 123, 115, 169], [84, 86, 114, 96], [182, 40, 120, 100], [48, 8, 162, 82], [166, 163, 78, 3], [72, 190, 136, 105], [0, 0, 0, 1], [0, 1]],![[13, 8, 196, 23], [159, 103, 196, 68], [70, 63, 194, 30], [114, 37, 1, 105], [47, 163, 18, 140], [42, 64, 159, 50], [4, 59, 185, 103], [126, 123, 115, 169]],![[148, 65, 83, 5], [33, 24, 27, 10], [111, 130, 80, 28], [54, 20, 10, 99], [100, 130, 174, 111], [4, 179, 20, 50], [13, 9, 196, 22], [13, 8, 196, 23]],![[0, 1], [193, 181, 57, 23], [31, 161, 0, 39], [12, 132, 24, 108], [48, 135, 124, 140], [97, 158, 79, 189], [73, 129, 13, 71], [148, 65, 83, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [153, 87, 3], []]
 b := ![[], [], [24, 99, 180, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where 
  n := 4
  hpos := by decide  
  P := [119, 143, 113, 107, 1]
  hirr := P197P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![29686790102, 28381411760, 8738400905, 861192001]
  a := ![0, -1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![150694366, 144068080, 44357365, 4371533]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 1506138481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀

instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0, 0]] 
 ![![199, 0, 0, 0], ![0, 199, 0, 0], ![0, 0, 199, 0], ![0, 0, 0, 199]] where
  M :=![![![199, 0, 0, 0], ![0, 199, 0, 0], ![0, 0, 199, 0], ![0, 0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 4 2 7 [29, 58, 82, 154, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [115, 96, 139, 59], [110, 134, 26, 130], [19, 167, 34, 10], [0, 1]]
 g := ![![[147, 114, 79, 124], [49, 105, 33, 92], [72, 25, 44, 172], [192, 188, 121], [104, 110, 106], [152, 45, 1], []],![[91, 133, 59, 97, 22, 41], [136, 163, 22, 20, 107, 77], [99, 40, 100, 127, 120, 135], [161, 29, 9], [27, 1, 111], [104, 167, 56], [63, 136, 189, 59, 168, 11]],![[53, 170, 1, 19, 195, 81], [149, 116, 18, 79, 54, 65], [25, 41, 49, 17, 36, 10], [110, 62, 193], [124, 96, 162], [79, 37, 47], [187, 177, 136, 100, 33, 40]],![[147, 94, 194, 138, 50, 98], [47, 183, 93, 127, 180, 2], [107, 139, 165, 24, 123, 45], [104, 46, 70], [10, 29, 43], [28, 151, 31], [128, 192, 22, 76, 77, 5]]]
 h' := ![![[115, 96, 139, 59], [171, 135, 126, 129], [101, 82, 71, 93], [159, 38, 139, 157], [73, 43, 49, 188], [169, 28, 21, 107], [0, 0, 0, 1], [0, 1]],![[110, 134, 26, 130], [153, 152, 166, 50], [115, 196, 109, 41], [29, 83, 13, 137], [188, 22, 129, 196], [162, 40, 64, 132], [81, 103, 7, 102], [115, 96, 139, 59]],![[19, 167, 34, 10], [5, 171, 185, 33], [51, 2, 69, 10], [193, 180, 158, 134], [0, 137, 52, 118], [148, 94, 116, 180], [38, 183, 106, 131], [110, 134, 26, 130]],![[0, 1], [157, 139, 120, 186], [105, 118, 149, 55], [92, 97, 88, 169], [116, 196, 168, 95], [159, 37, 197, 178], [162, 112, 86, 164], [19, 167, 34, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [192, 118, 126], []]
 b := ![[], [], [190, 130, 8, 97], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where 
  n := 4
  hpos := by decide  
  P := [29, 58, 82, 154, 1]
  hirr := P199P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![3167816453554, 3028206976714, 932148067059, 91819080784]
  a := ![19, 1, -1, 3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![15918675646, 15217120486, 4684161141, 461402416]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 1568239201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def PBC199 : ContainsPrimesAboveP 199 ![I199N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![199, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 199 (by decide) 𝕀

instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0, 0], ![-53, -50, -4, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0, 0], ![-53, -50, -4, 1]] 
 ![![211, 0, 0, 0], ![0, 211, 0, 0], ![200, 183, 1, 0], ![114, 49, 0, 1]] where
  M :=![![![211, 0, 0, 0], ![0, 211, 0, 0], ![0, 0, 211, 0], ![0, 0, 0, 211]], ![![-53, -50, -4, 1], ![383, 279, 30, -3], ![-1149, -613, 39, 27], ![10341, 7815, 1547, 66]]]
  hmulB := by decide  
  f := ![![![8869245, 6259800, 697392, -59148], ![-3724572, -5401600, 0, 0]], ![![-44307, -31261, -3484, 295], ![18779, 27008, 0, 0]], ![![8368408, 5906317, 658011, -55808], ![-3514240, -5096576, 0, 0]], ![![4781613, 3374801, 375980, -31888], ![-2008015, -2912128, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-200, -183, 211, 0], ![-114, -49, 0, 211]], ![![3, 3, -4, 1], ![-25, -24, 30, -3], ![-57, -43, 39, 27], ![-1453, -1320, 1547, 66]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [170, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [136, 210], [0, 1]]
 g := ![![[168, 36], [164, 5], [196], [183], [181, 49], [117], [136, 1]],![[0, 175], [0, 206], [196], [183], [93, 162], [117], [61, 210]]]
 h' := ![![[136, 210], [183, 205], [189, 146], [148, 197], [36, 82], [26, 204], [90, 180], [0, 1]],![[0, 1], [0, 6], [0, 65], [143, 14], [5, 129], [129, 7], [94, 31], [136, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [29, 133]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where 
  n := 2
  hpos := by decide  
  P := [170, 75, 1]
  hirr := P211P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![126103, 112292, 30581, 2443]
  a := ![-1, 0, 1, 2]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-29709, -26558, 30581, 2443]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0, 0], ![-197, -150, -4, 1]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0, 0], ![-197, -150, -4, 1]] 
 ![![211, 0, 0, 0], ![0, 211, 0, 0], ![54, 27, 1, 0], ![19, 169, 0, 1]] where
  M :=![![![211, 0, 0, 0], ![0, 211, 0, 0], ![0, 0, 211, 0], ![0, 0, 0, 211]], ![![-197, -150, -4, 1], ![383, 135, -70, -3], ![-1149, -613, -105, -73], ![-27959, -25385, -6453, -178]]]
  hmulB := by decide  
  f := ![![![4342195, -4800, -1556032, -44362], ![-4021238, -4460540, 0, 0]], ![![-30844, 166, 11118, 316], ![28907, 31861, 0, 0]], ![![1107351, -1188, -396803, -11313], ![-1025406, -1137483, 0, 0]], ![![366185, -386, -131214, -3741], ![-339071, -376141, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-54, -27, 211, 0], ![-19, -169, 0, 211]], ![![0, -1, -4, 1], ![20, 12, -70, -3], ![28, 69, -105, -73], ![1535, 848, -6453, -178]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P1 : CertificateIrreducibleZModOfList' 211 2 2 7 [161, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [178, 210], [0, 1]]
 g := ![![[12, 173], [15, 58], [154], [46], [105, 134], [93], [178, 1]],![[0, 38], [0, 153], [154], [46], [114, 77], [93], [145, 210]]]
 h' := ![![[178, 210], [117, 157], [101, 67], [182, 24], [186, 62], [186, 150], [38, 84], [0, 1]],![[0, 1], [0, 54], [0, 144], [23, 187], [39, 149], [89, 61], [9, 127], [178, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [127, 110]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N1 : CertifiedPrimeIdeal' SI211N1 211 where 
  n := 2
  hpos := by decide  
  P := [161, 33, 1]
  hirr := P211P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![124113, 109100, 28780, 2018]
  a := ![-5, 0, 0, 2]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-6959, -4782, 28780, 2018]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N1 B_one_repr
lemma NI211N1 : Nat.card (O ⧸ I211N1) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0, 0], ![-53, -50, -4, 1]] ![![211, 0, 0, 0], ![-197, -150, -4, 1]]
  ![![211, 0, 0, 0]] where
 M :=  ![![![44521, 0, 0, 0], ![-41567, -31650, -844, 211]], ![![-11183, -10550, -844, 211], ![-32072, -21733, -2321, 211]]]
 hmul := by decide  
 g :=  ![![![![211, 0, 0, 0]], ![![-197, -150, -4, 1]]], ![![![-53, -50, -4, 1]], ![![-152, -103, -11, 1]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0, 0]] 
 ![![223, 0, 0, 0], ![0, 223, 0, 0], ![0, 0, 223, 0], ![0, 0, 0, 223]] where
  M :=![![![223, 0, 0, 0], ![0, 223, 0, 0], ![0, 0, 223, 0], ![0, 0, 0, 223]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 4 2 7 [89, 48, 190, 74, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 192, 88, 128], [172, 141, 136, 199], [141, 112, 222, 119], [0, 1]]
 g := ![![[72, 48, 192, 101], [140, 68, 147, 33], [203, 26, 64, 169], [32, 126, 200, 58], [39, 160, 204, 136], [157, 149, 1], []],![[71, 167, 105, 208, 186, 200], [182, 85, 19, 2, 50, 130], [214, 103, 179, 106, 87, 55], [212, 145, 91, 78, 188, 181], [166, 76, 109, 29, 134, 30], [39, 179, 146], [9, 185, 128, 189, 88, 60]],![[152, 221, 182, 184, 180, 112], [63, 149, 217, 156, 84, 66], [172, 34, 207, 206, 29, 39], [83, 129, 128, 44, 214, 74], [210, 56, 142, 197, 48, 120], [177, 137, 201], [199, 43, 67, 107, 41, 2]],![[103, 105, 112, 158, 169, 218], [82, 195, 194, 75, 120, 100], [49, 71, 149, 58, 15, 33], [55, 22, 28, 175, 108, 152], [82, 148, 130, 94, 75, 199], [7, 147, 60], [151, 25, 185, 54, 167, 171]]]
 h' := ![![[59, 192, 88, 128], [28, 178, 151, 18], [219, 132, 163, 207], [51, 4, 209, 13], [97, 145, 85, 113], [76, 165, 170, 164], [0, 0, 0, 1], [0, 1]],![[172, 141, 136, 199], [116, 163, 9, 166], [51, 193, 68, 89], [154, 100, 148, 44], [130, 160, 16, 201], [84, 26, 130, 155], [87, 114, 44, 102], [59, 192, 88, 128]],![[141, 112, 222, 119], [139, 121, 38, 211], [217, 79, 171, 62], [116, 19, 80, 159], [85, 150, 141, 57], [112, 97, 194, 21], [163, 165, 202, 147], [172, 141, 136, 199]],![[0, 1], [44, 207, 25, 51], [34, 42, 44, 88], [184, 100, 9, 7], [151, 214, 204, 75], [74, 158, 175, 106], [52, 167, 200, 196], [141, 112, 222, 119]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [108, 213, 34], []]
 b := ![[], [], [101, 51, 162, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where 
  n := 4
  hpos := by decide  
  P := [89, 48, 190, 74, 1]
  hirr := P223P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![27040287362, 18043334076, 2012288891, -342409141]
  a := ![-10, 2, 13, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![121256894, 80911812, 9023717, -1535467]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 2472973441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def PBC223 : ContainsPrimesAboveP 223 ![I223N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![223, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 223 (by decide) 𝕀

instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0, 0], ![-19, -131, -4, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0, 0], ![-19, -131, -4, 1]] 
 ![![227, 0, 0, 0], ![0, 227, 0, 0], ![193, 149, 1, 0], ![72, 11, 0, 1]] where
  M :=![![![227, 0, 0, 0], ![0, 227, 0, 0], ![0, 0, 227, 0], ![0, 0, 0, 227]], ![![-19, -131, -4, 1], ![383, 313, -51, -3], ![-1149, -613, 73, -54], ![-20682, -19077, -4933, 19]]]
  hmulB := by decide  
  f := ![![![11337283, 6800778, -1649028, -70638], ![-4844634, -6959820, 0, 0]], ![![-53980, -32335, 7854, 336], ![23154, 33142, 0, 0]], ![![9603750, 5760894, -1396883, -59837], ![-4103879, -5895626, 0, 0]], ![![3593356, 2155545, -522658, -22389], ![-1535438, -2205914, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-193, -149, 227, 0], ![-72, -11, 0, 227]], ![![3, 2, -4, 1], ![46, 35, -51, -3], ![-50, -48, 73, -54], ![4097, 3153, -4933, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [132, 145, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 226], [0, 1]]
 g := ![![[106, 43], [186, 101], [160], [23], [166], [220, 81], [82, 1]],![[0, 184], [69, 126], [160], [23], [166], [52, 146], [164, 226]]]
 h' := ![![[82, 226], [191, 161], [113, 151], [24, 198], [136, 134], [16, 47], [72, 9], [0, 1]],![[0, 1], [0, 66], [10, 76], [143, 29], [1, 93], [11, 180], [129, 218], [82, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [210]]
 b := ![[], [8, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where 
  n := 2
  hpos := by decide  
  P := [132, 145, 1]
  hirr := P227P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![39727, 37790, 11024, 1000]
  a := ![1, 1, -4, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-9515, -7118, 11024, 1000]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0, 0], ![-158, -50, -4, 1]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0, 0], ![-158, -50, -4, 1]] 
 ![![227, 0, 0, 0], ![0, 227, 0, 0], ![58, 77, 1, 0], ![74, 31, 0, 1]] where
  M :=![![![227, 0, 0, 0], ![0, 227, 0, 0], ![0, 0, 227, 0], ![0, 0, 0, 227]], ![![-158, -50, -4, 1], ![383, 174, 30, -3], ![-1149, -613, -66, 27], ![10341, 7815, 1547, -39]]]
  hmulB := by decide  
  f := ![![![1448734, 771496, 157058, -12584], ![-1181081, -1345883, 0, 0]], ![![-11815, -6325, -1294, 103], ![9988, 11123, 0, 0]], ![![366097, 194959, 39689, -3180], ![-298467, -340109, 0, 0]], ![![470787, 250677, 51026, -4089], ![-383477, -437227, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-58, -77, 227, 0], ![-74, -31, 0, 227]], ![![0, 1, -4, 1], ![-5, -9, 30, -3], ![3, 16, -66, 27], ![-337, -485, 1547, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P1 : CertificateIrreducibleZModOfList' 227 2 2 7 [208, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [202, 226], [0, 1]]
 g := ![![[154, 79], [136, 129], [136], [16], [182], [17, 7], [202, 1]],![[222, 148], [89, 98], [136], [16], [182], [69, 220], [177, 226]]]
 h' := ![![[202, 226], [87, 144], [171, 122], [159, 131], [189, 223], [96, 149], [206, 190], [0, 1]],![[0, 1], [119, 83], [72, 105], [62, 96], [62, 4], [3, 78], [223, 37], [202, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136]]
 b := ![[], [169, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N1 : CertifiedPrimeIdeal' SI227N1 227 where 
  n := 2
  hpos := by decide  
  P := [208, 25, 1]
  hirr := P227P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![31548, 26860, 6593, 351]
  a := ![-3, 1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-1660, -2166, 6593, 351]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N1 B_one_repr
lemma NI227N1 : Nat.card (O ⧸ I227N1) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0, 0], ![-19, -131, -4, 1]] ![![227, 0, 0, 0], ![-158, -50, -4, 1]]
  ![![227, 0, 0, 0]] where
 M :=  ![![![51529, 0, 0, 0], ![-35866, -11350, -908, 227]], ![![-4313, -29737, -908, 227], ![-32234, -11577, -2043, 227]]]
 hmul := by decide  
 g :=  ![![![![227, 0, 0, 0]], ![![-158, -50, -4, 1]]], ![![![-19, -131, -4, 1]], ![![-142, -51, -9, 1]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0, 0], ![44, 1, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0, 0], ![44, 1, 0, 0]] 
 ![![229, 0, 0, 0], ![44, 1, 0, 0], ![125, 0, 1, 0], ![225, 0, 0, 1]] where
  M :=![![![229, 0, 0, 0], ![0, 229, 0, 0], ![0, 0, 229, 0], ![0, 0, 0, 229]], ![![44, 1, 0, 0], ![0, 44, 1, 0], ![0, 0, 44, 1], ![383, 332, 80, 45]]]
  hmulB := by decide  
  f := ![![![5941, 47, 98250, 2233], ![-30915, 458, -511357, 0]], ![![1100, -19, 26795, 609], ![-5724, 229, -139461, 0]], ![![3221, 29, 53591, 1218], ![-16761, 230, -278922, 0]], ![![5833, 53, 96534, 2194], ![-30353, 414, -502425, 0]]]
  g := ![![![1, 0, 0, 0], ![-44, 229, 0, 0], ![-125, 0, 229, 0], ![-225, 0, 0, 229]], ![![0, 1, 0, 0], ![-9, 44, 1, 0], ![-25, 0, 44, 1], ![-150, 332, 80, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N0 : Nat.card (O ⧸ I229N0) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N0)

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := prime_ideal_of_norm_prime hp229.out _ NI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0, 0], ![70, 1, 0, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0, 0], ![70, 1, 0, 0]] 
 ![![229, 0, 0, 0], ![70, 1, 0, 0], ![138, 0, 1, 0], ![187, 0, 0, 1]] where
  M :=![![![229, 0, 0, 0], ![0, 229, 0, 0], ![0, 0, 229, 0], ![0, 0, 0, 229]], ![![70, 1, 0, 0], ![0, 70, 1, 0], ![0, 0, 70, 1], ![383, 332, 80, 71]]]
  hmulB := by decide  
  f := ![![![4621, -91214, -1444, -2], ![-15114, 298616, 458, 0]], ![![1330, -27981, -470, -1], ![-4350, 91600, 229, 0]], ![![2682, -55052, -857, -1], ![-8772, 180224, 229, 0]], ![![3823, -74544, -1206, -2], ![-12504, 244044, 459, 0]]]
  g := ![![![1, 0, 0, 0], ![-70, 229, 0, 0], ![-138, 0, 229, 0], ![-187, 0, 0, 229]], ![![0, 1, 0, 0], ![-22, 70, 1, 0], ![-43, 0, 70, 1], ![-206, 332, 80, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0, 0], ![44, 1, 0, 0]] ![![229, 0, 0, 0], ![44, 1, 0, 0]]
  ![![229, 0, 0, 0], ![-179, 23, -4, 1]] where
 M :=  ![![![52441, 0, 0, 0], ![10076, 229, 0, 0]], ![![10076, 229, 0, 0], ![1936, 88, 1, 0]]]
 hmul := by decide  
 g :=  ![![![![539067877, 375277824, 219666048, -4902912], ![-387533952, -503433600, 0, 0]], ![![103537236, 72078457, 42190592, -941688], ![-74432328, -96692960, 0, 0]]], ![![![103537236, 72078457, 42190592, -941688], ![-74432328, -96692960, 0, 0]], ![![19886057, 13843891, 8103417, -180867], ![-14296017, -18571520, 0, 0]]]]
 hle2 := by decide  
def MulI229N1 : IdealMulLeCertificate' Table 
  ![![229, 0, 0, 0], ![-179, 23, -4, 1]] ![![229, 0, 0, 0], ![70, 1, 0, 0]]
  ![![229, 0, 0, 0], ![-5403, -2862, -163, 41]] where
 M :=  ![![![52441, 0, 0, 0], ![16030, 229, 0, 0]], ![![-40991, 5267, -916, 229], ![-12147, 1763, -177, 67]]]
 hmul := by decide  
 g :=  ![![![![229, 0, 0, 0], ![0, 0, 0, 0]], ![![70, 1, 0, 0], ![0, 0, 0, 0]]], ![![![5224, 2885, 159, -40], ![229, 0, 0, 0]], ![![2094, 1145, 64, -16], ![91, 0, 0, 0]]]]
 hle2 := by decide  

def MulI229N2 : IdealMulLeCertificate' Table 
  ![![229, 0, 0, 0], ![-5403, -2862, -163, 41]] ![![229, 0, 0, 0], ![70, 1, 0, 0]]
  ![![229, 0, 0, 0]] where
 M :=  ![![![52441, 0, 0, 0], ![16030, 229, 0, 0]], ![![-1237287, -655398, -37327, 9389], ![-362507, -192131, -10992, 2748]]]
 hmul := by decide  
 g :=  ![![![![229, 0, 0, 0]], ![![70, 1, 0, 0]]], ![![![-5403, -2862, -163, 41]], ![![-1583, -839, -48, 12]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N0, I229N1, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N0
    exact isPrimeI229N1
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0 ⊙ MulI229N1 ⊙ MulI229N2)


lemma PB692I4_primes (p : ℕ) :
  p ∈ Set.range ![179, 181, 191, 193, 197, 199, 211, 223, 227, 229] ↔ Nat.Prime p ∧ 173 < p ∧ p ≤ 229 := by
  rw [← List.mem_ofFn']
  convert primes_range 173 229 (by omega)
  rfl

def PB692I4 : PrimesBelowBoundCertificateInterval' O 173 229 692 where
  m := 10
  g := ![2, 4, 1, 4, 1, 1, 2, 1, 2, 4]
  P := ![179, 181, 191, 193, 197, 199, 211, 223, 227, 229]
  hP := PB692I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2, I181N3]
    · exact ![I191N0]
    · exact ![I193N0, I193N1, I193N2, I193N3]
    · exact ![I197N0]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N0, I229N1, I229N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![32041, 32041]
    · exact ![181, 181, 181, 181]
    · exact ![1330863361]
    · exact ![193, 193, 193, 193]
    · exact ![1506138481]
    · exact ![1568239201]
    · exact ![44521, 44521]
    · exact ![2472973441]
    · exact ![51529, 51529]
    · exact ![229, 229, 229, 229]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
      exact NI181N3
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
      exact NI193N3
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N0
      exact NI229N1
      exact NI229N1
  Il := ![[], [I181N0, I181N1, I181N2, I181N3], [], [I193N0, I193N1, I193N2, I193N3], [], [], [], [], [], [I229N0, I229N0, I229N1, I229N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
