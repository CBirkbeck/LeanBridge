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

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0, 0, 0], ![-4, 1, 1, 0, 32, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0, 0, 0, 0], ![-4, 1, 1, 0, 32, 0]] 
 ![![67, 0, 0, 0, 0, 0], ![0, 67, 0, 0, 0, 0], ![0, 0, 67, 0, 0, 0], ![14, 22, 15, 1, 0, 0], ![25, 44, 44, 0, 1, 0], ![54, 62, 29, 0, 0, 1]] where
  M :=![![![67, 0, 0, 0, 0, 0], ![0, 67, 0, 0, 0, 0], ![0, 0, 67, 0, 0, 0], ![0, 0, 0, 67, 0, 0], ![0, 0, 0, 0, 67, 0], ![0, 0, 0, 0, 0, 67]], ![![-4, 1, 1, 0, 32, 0], ![0, -4, 5, 1, 0, 32], ![-32, 0, 60, 1, 33, 0], ![0, -32, 0, 60, 5, 33], ![-33, 0, 34, 0, 93, 1], ![-5, -33, 10, 34, 5, 93]]]
  hmulB := by decide  
  f := ![![![1534205, -377763, -420522, -739, -12115748, -992], ![25318429, 2077, 47436, 0, 0, 0]], ![![6264392, -1542461, -1717065, -3018, -49470443, -4064], ![103378990, 8509, 193697, 0, 0, 0]], ![![-127840, 31480, 35039, 61, 1009563, 64], ![-2109696, -134, -3953, 0, 0, 0]], ![![2348922, -578366, -643839, -1132, -18549639, -1536], ![38763408, 3216, 72629, 0, 0, 0]], ![![4602439, -1133245, -1261522, -2217, -36345857, -2976], ![75952383, 6231, 142308, 0, 0, 0]], ![![6978090, -1718192, -1912688, -3362, -55106577, -4533], ![115156890, 9491, 215763, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![-14, -22, -15, 67, 0, 0], ![-25, -44, -44, 0, 67, 0], ![-54, -62, -29, 0, 0, 67]], ![![-12, -21, -21, 0, 32, 0], ![-26, -30, -14, 1, 0, 32], ![-13, -22, -21, 1, 33, 0], ![-41, -54, -31, 60, 5, 33], ![-36, -62, -61, 0, 93, 1], ![-84, -101, -51, 34, 5, 93]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [15, 39, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 43, 13], [24, 23, 54], [0, 1]]
 g := ![![[37, 30, 14], [6, 43, 59], [44, 59], [26, 62], [5, 1], []], ![[31, 27, 31, 28], [62, 30, 65, 52], [59, 1], [51, 29], [44, 60], [20, 35]], ![[19, 30, 22, 54], [54, 64, 39, 55], [40, 47], [53, 55], [29, 40], [46, 35]]]
 h' := ![![[48, 43, 13], [44, 32, 58], [24, 40, 27], [9, 9, 27], [59, 58, 53], [0, 0, 1], [0, 1]], ![[24, 23, 54], [26, 22, 8], [40, 20, 2], [11, 27, 1], [46, 23, 30], [61, 9, 23], [48, 43, 13]], ![[0, 1], [29, 13, 1], [50, 7, 38], [28, 31, 39], [32, 53, 51], [20, 58, 43], [24, 23, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 26], []]
 b := ![[], [58, 62, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [15, 39, 62, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3791, 123, 7437, 253, 3042, -925]
  a := ![0, -1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-499, -1223, -1543, 253, 3042, -925]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0, 0, 0], ![4, 1, -1, 0, -32, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0, 0, 0, 0], ![4, 1, -1, 0, -32, 0]] 
 ![![67, 0, 0, 0, 0, 0], ![0, 67, 0, 0, 0, 0], ![0, 0, 67, 0, 0, 0], ![53, 22, 52, 1, 0, 0], ![25, 23, 44, 0, 1, 0], ![13, 62, 38, 0, 0, 1]] where
  M :=![![![67, 0, 0, 0, 0, 0], ![0, 67, 0, 0, 0, 0], ![0, 0, 67, 0, 0, 0], ![0, 0, 0, 67, 0, 0], ![0, 0, 0, 0, 67, 0], ![0, 0, 0, 0, 0, 67]], ![![4, 1, -1, 0, -32, 0], ![0, 4, 5, -1, 0, -32], ![32, 0, -60, 1, -33, 0], ![0, 32, 0, -60, 5, -33], ![33, 0, -34, 0, -93, 1], ![-5, 33, 10, -34, 5, -93]]]
  hmulB := by decide  
  f := ![![![1571525, 387093, -429852, 739, -12414308, 992], ![-25943539, 2077, -47436, 0, 0, 0]], ![![2357184, 580613, -644755, 1109, -18620646, 1504], ![-38913600, 3149, -71154, 0, 0, 0]], ![![-130960, -32260, 35819, -61, 1034523, -64], ![2161956, -134, 3953, 0, 0, 0]], ![![1915515, 471823, -523943, 901, -15131668, 1216], ![-31622303, 2546, -57820, 0, 0, 0]], ![![1309575, 322570, -358203, 616, -10345027, 832], ![-21619135, 1742, -39530, 0, 0, 0]], ![![2411931, 594097, -659730, 1135, -19053122, 1547], ![-39817393, 3239, -72806, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![-53, -22, -52, 67, 0, 0], ![-25, -23, -44, 0, 67, 0], ![-13, -62, -38, 0, 0, 67]], ![![12, 11, 21, 0, -32, 0], ![7, 30, 19, -1, 0, -32], ![12, 11, 20, 1, -33, 0], ![52, 49, 62, -60, 5, -33], ![35, 31, 60, 0, -93, 1], ![43, 96, 76, -34, 5, -93]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 3 2 6 [60, 57, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 37], [42, 29], [0, 1]]
 g := ![![[46, 23, 65], [62, 37, 6], [60, 14], [55, 65], [29, 1], []], ![[12, 28, 9], [59, 19, 40], [12, 49], [14, 60], [16, 37], []], ![[30, 16, 60], [6, 11, 21], [45, 4], [38, 9], [4, 29], []]]
 h' := ![![[54, 37], [32, 3, 47], [53, 27, 26], [54, 49, 58], [2, 29, 47], [0, 0, 1], [0, 1]], ![[42, 29], [30, 55, 23], [9, 40, 17], [40, 19, 7], [64, 12, 23], [35, 43, 29], [54, 37]], ![[0, 1], [53, 9, 64], [17, 0, 24], [38, 66, 2], [43, 26, 64], [22, 24, 37], [42, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33], []]
 b := ![[], [44, 14, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 3
  hpos := by decide
  P := [60, 57, 38, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-98365, 8297, -29213, 5386, -4162, -21521]
  a := ![-64, 1, -1, 1, 1, -3]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![0, 19699, 10323, 5386, -4162, -21521]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0, 0, 0, 0], ![-4, 1, 1, 0, 32, 0]] ![![67, 0, 0, 0, 0, 0], ![4, 1, -1, 0, -32, 0]]
  ![![67, 0, 0, 0, 0, 0]] where
 M := ![![![4489, 0, 0, 0, 0, 0], ![268, 67, -67, 0, -2144, 0]], ![![-268, 67, 67, 0, 2144, 0], ![1072, 0, -1139, 0, -2881, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0, 0, 0, 0]], ![![4, 1, -1, 0, -32, 0]]], ![![![-4, 1, 1, 0, 32, 0]], ![![16, 0, -17, 0, -43, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 0, 1, 0, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![4, 0, 1, 0, 0, 0]] 
 ![![71, 0, 0, 0, 0, 0], ![0, 71, 0, 0, 0, 0], ![4, 0, 1, 0, 0, 0], ![0, 4, 0, 1, 0, 0], ![55, 0, 0, 0, 1, 0], ![0, 55, 0, 0, 0, 1]] where
  M :=![![![4, 0, 1, 0, 0, 0], ![0, 4, 0, 1, 0, 0], ![0, 0, 4, 0, 1, 0], ![0, 0, 0, 4, 0, 1], ![-1, 0, 2, 0, 5, 0], ![0, -1, 0, 2, 0, 5]]]
  hmulB := by decide  
  f := ![![![18, 0, -5, 0, 1, 0]], ![![0, 18, 0, -5, 0, 1]], ![![1, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0]], ![![14, 0, -4, 0, 1, 0]], ![![0, 14, 0, -4, 0, 1]]]
  g := ![![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, 0, 4, 0, 1, 0], ![0, -1, 0, 4, 0, 1], ![-4, 0, 2, 0, 5, 0], ![0, -4, 0, 2, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [14, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 70], [0, 1]]
 g := ![![[27, 54], [65, 32], [4, 12], [15], [32], [1]], ![[63, 17], [39, 39], [12, 59], [15], [32], [1]]]
 h' := ![![[48, 70], [13, 57], [15, 48], [33, 15], [32, 50], [57, 48], [0, 1]], ![[0, 1], [51, 14], [47, 23], [43, 56], [18, 21], [18, 23], [48, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [69, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [14, 23, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-329, -97, 292, 135, 1518, 133]
  a := ![0, -1, -1, 1, 19, 1]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1197, -112, 292, 135, 1518, 133]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 2, 1, 1, -1, -1]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![2, 2, 1, 1, -1, -1]] 
 ![![71, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0], ![14, 0, 1, 0, 0, 0], ![57, 0, 0, 1, 0, 0], ![17, 0, 0, 0, 1, 0], ![54, 0, 0, 0, 0, 1]] where
  M :=![![![2, 2, 1, 1, -1, -1], ![5, 2, 0, 1, 0, -1], ![1, 1, 0, 0, 0, 0], ![0, 1, 5, 0, 0, 0], ![0, 0, 1, 1, 0, 0], ![0, 0, 0, 1, 5, 0]]]
  hmulB := by decide  
  f := ![![![-25, 25, -4, 4, 5, -5]], ![![0, 0, 1, 0, 0, 0]], ![![-5, 5, -1, 1, 1, -1]], ![![-20, 20, -3, 3, 5, -4]], ![![-6, 6, -1, 1, 1, -1]], ![![-20, 19, -1, 3, 5, -4]]]
  g := ![![![0, 2, 1, 1, -1, -1], ![0, 2, 0, 1, 0, -1], ![0, 1, 0, 0, 0, 0], ![-1, 1, 5, 0, 0, 0], ![-1, 0, 1, 1, 0, 0], ![-2, 0, 0, 1, 5, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 2, -1, 1, 1, -1]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-2, 2, -1, 1, 1, -1]] 
 ![![71, 0, 0, 0, 0, 0], ![70, 1, 0, 0, 0, 0], ![14, 0, 1, 0, 0, 0], ![14, 0, 0, 1, 0, 0], ![17, 0, 0, 0, 1, 0], ![17, 0, 0, 0, 0, 1]] where
  M :=![![![-2, 2, -1, 1, 1, -1], ![5, -2, 0, -1, 0, 1], ![-1, 1, 0, 0, 0, 0], ![0, -1, 5, 0, 0, 0], ![0, 0, -1, 1, 0, 0], ![0, 0, 0, -1, 5, 0]]]
  hmulB := by decide  
  f := ![![![25, 25, 4, 4, -5, -5]], ![![25, 25, 5, 4, -5, -5]], ![![5, 5, 1, 1, -1, -1]], ![![5, 5, 1, 1, 0, -1]], ![![6, 6, 1, 1, -1, -1]], ![![5, 6, 3, 1, 0, -1]]]
  g := ![![![-2, 2, -1, 1, 1, -1], ![2, -2, 0, -1, 0, 1], ![-1, 1, 0, 0, 0, 0], ![0, -1, 5, 0, 0, 0], ![0, 0, -1, 1, 0, 0], ![-1, 0, 0, -1, 5, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2

def I71N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 2, 0, 0, 2, -1]] i)))

def SI71N3: IdealEqSpanCertificate' Table ![![-2, 2, 0, 0, 2, -1]] 
 ![![71, 0, 0, 0, 0, 0], ![33, 1, 0, 0, 0, 0], ![52, 0, 1, 0, 0, 0], ![59, 0, 0, 1, 0, 0], ![65, 0, 0, 0, 1, 0], ![56, 0, 0, 0, 0, 1]] where
  M :=![![![-2, 2, 0, 0, 2, -1], ![5, -2, 0, 0, -5, 2], ![-2, 1, 2, 0, 2, -1], ![5, -2, -5, 2, -5, 2], ![-2, 1, 2, -1, 4, -1], ![5, -2, -5, 2, -10, 4]]]
  hmulB := by decide  
  f := ![![![22, 23, 2, 15, 8, -11]], ![![11, 11, 1, 7, 4, -5]], ![![16, 17, 2, 11, 6, -8]], ![![18, 19, 3, 13, 7, -9]], ![![20, 21, 2, 14, 8, -10]], ![![17, 18, 2, 12, 8, -8]]]
  g := ![![![-2, 2, 0, 0, 2, -1], ![4, -2, 0, 0, -5, 2], ![-3, 1, 2, 0, 2, -1], ![6, -2, -5, 2, -5, 2], ![-4, 1, 2, -1, 4, -1], ![9, -2, -5, 2, -10, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N3 : Nat.card (O ⧸ I71N3) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N3)

lemma isPrimeI71N3 : Ideal.IsPrime I71N3 := prime_ideal_of_norm_prime hp71.out _ NI71N3

def I71N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 2, 0, 0, -2, -1]] i)))

def SI71N4: IdealEqSpanCertificate' Table ![![2, 2, 0, 0, -2, -1]] 
 ![![71, 0, 0, 0, 0, 0], ![38, 1, 0, 0, 0, 0], ![52, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![65, 0, 0, 0, 1, 0], ![15, 0, 0, 0, 0, 1]] where
  M :=![![![2, 2, 0, 0, -2, -1], ![5, 2, 0, 0, -5, -2], ![2, 1, -2, 0, -2, -1], ![5, 2, -5, -2, -5, -2], ![2, 1, -2, -1, -4, -1], ![5, 2, -5, -2, -10, -4]]]
  hmulB := by decide  
  f := ![![![-22, 23, -2, 15, -8, -11]], ![![-11, 12, -1, 8, -4, -6]], ![![-16, 17, -2, 11, -6, -8]], ![![-4, 4, 1, 2, -1, -2]], ![![-20, 21, -2, 14, -8, -10]], ![![-5, 5, 0, 3, 0, -3]]]
  g := ![![![1, 2, 0, 0, -2, -1], ![4, 2, 0, 0, -5, -2], ![3, 1, -2, 0, -2, -1], ![8, 2, -5, -2, -5, -2], ![5, 1, -2, -1, -4, -1], ![13, 2, -5, -2, -10, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N4 : Nat.card (O ⧸ I71N4) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N4)

lemma isPrimeI71N4 : Ideal.IsPrime I71N4 := prime_ideal_of_norm_prime hp71.out _ NI71N4
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![4, 0, 1, 0, 0, 0]] ![![2, 2, 1, 1, -1, -1]]
  ![![9, 9, 4, 4, -4, -4]] where
 M := ![![![9, 9, 4, 4, -4, -4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![9, 9, 4, 4, -4, -4]] ![![-2, 2, -1, 1, 1, -1]]
  ![![23, 0, 15, 0, -11, 0]] where
 M := ![![![23, 0, 15, 0, -11, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N2 : IdealMulLeCertificate' Table 
  ![![23, 0, 15, 0, -11, 0]] ![![-2, 2, 0, 0, 2, -1]]
  ![![-54, 50, 8, 11, 32, -27]] where
 M := ![![![-54, 50, 8, 11, 32, -27]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N3 : IdealMulLeCertificate' Table 
  ![![-54, 50, 8, 11, 32, -27]] ![![2, 2, 0, 0, -2, -1]]
  ![![71, 0, 0, 0, 0, 0]] where
 M := ![![![142, 0, 0, 0, -71, 0]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, -1, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2, I71N3, I71N4] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
    exact isPrimeI71N3
    exact isPrimeI71N4
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1 ⊙ MulI71N2 ⊙ MulI71N3)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0, 0, 0, 0]] 
 ![![73, 0, 0, 0, 0, 0], ![0, 73, 0, 0, 0, 0], ![0, 0, 73, 0, 0, 0], ![0, 0, 0, 73, 0, 0], ![0, 0, 0, 0, 73, 0], ![0, 0, 0, 0, 0, 73]] where
  M :=![![![73, 0, 0, 0, 0, 0], ![0, 73, 0, 0, 0, 0], ![0, 0, 73, 0, 0, 0], ![0, 0, 0, 73, 0, 0], ![0, 0, 0, 0, 73, 0], ![0, 0, 0, 0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0, 0]], ![![0, 0, 0, 1, 0, 0]], ![![0, 0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 6 2 6 [70, 68, 11, 9, 49, 71, 1] where
 m := 2
 P := ![2, 3]
 exp := ![1, 1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 47, 15, 64, 31, 67], [61, 1, 40, 37, 1, 36], [18, 62, 0, 9, 53, 71], [1, 61, 71, 69, 47], [55, 47, 20, 40, 14, 45], [0, 1]]
 g := ![![[53, 26, 48, 17, 31, 38], [1, 46, 51, 14, 69], [31, 2, 49, 39, 24], [22, 28, 2, 1], [], []], ![[59, 66, 25, 15, 66, 56, 59, 15, 2, 8], [67, 67, 64, 56, 37], [35, 18, 65, 0, 9], [57, 53, 67, 58, 67, 8, 36, 1, 70, 36], [16, 36, 48, 32, 27], [45, 25, 19, 65, 36]], ![[8, 12, 66, 57, 50, 2, 37, 25, 57, 9], [20, 45, 51, 47, 32], [37, 29, 69, 27, 70], [39, 45, 48, 4, 72, 2, 38, 59, 40, 70], [40, 14, 25, 51, 61], [19, 49, 42, 36, 55]], ![[72, 5, 38, 32, 26, 63, 13, 11, 50, 3], [27, 67, 36, 23, 27], [25, 1, 10, 71, 24], [72, 36, 16, 36, 8, 20, 33, 37, 1, 4], [4, 47, 67, 10, 2], [16, 68, 52, 15, 4]], ![[70, 66, 38, 15, 12, 7, 26, 61, 17], [4, 59, 11, 3, 23], [58, 59, 70, 30, 48], [11, 38, 39, 62, 50, 64, 49, 49, 34], [36, 47, 50, 26, 2], [46, 27, 19]], ![[72, 46, 19, 55, 39, 71, 5, 51, 70, 26], [55, 55, 16, 15, 65], [52, 52, 70, 57, 41], [18, 35, 5, 27, 39, 44, 13, 61, 27, 29], [46, 49, 72, 39, 38], [33, 41, 17, 54, 54]]]
 h' := ![![[13, 47, 15, 64, 31, 67], [19, 70, 35, 67, 70, 44], [69, 0, 33, 10, 34, 54], [66, 48, 50, 18, 40, 30], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[61, 1, 40, 37, 1, 36], [6, 59, 42, 8, 66, 60], [30, 3, 15, 25, 4, 16], [12, 21, 29, 22, 70, 3], [46, 70, 18, 50, 60, 33], [12, 62, 23, 56, 23, 63], [13, 47, 15, 64, 31, 67]], ![[18, 62, 0, 9, 53, 71], [57, 5, 68, 70, 32, 37], [56, 54, 24, 8, 39, 55], [50, 46, 30, 20, 57, 56], [6, 59, 1, 28, 46, 15], [55, 72, 6, 41, 15, 39], [61, 1, 40, 37, 1, 36]], ![[1, 61, 71, 69, 47], [35, 28, 19, 7, 2, 53], [63, 30, 55, 4, 24, 10], [34, 5, 19, 28, 13, 43], [61, 53, 57, 57, 39, 12], [7, 34, 3, 29, 48, 32], [18, 62, 0, 9, 53, 71]], ![[55, 47, 20, 40, 14, 45], [8, 3, 24, 29, 20, 47], [19, 41, 20, 70, 55, 60], [8, 19, 60, 49, 3, 62], [11, 26, 41, 20, 56, 44], [66, 68, 45, 8, 43, 41], [1, 61, 71, 69, 47]], ![[0, 1], [31, 54, 31, 38, 29, 51], [42, 18, 72, 29, 63, 24], [55, 7, 31, 9, 36, 25], [71, 11, 29, 64, 17, 42], [58, 56, 68, 12, 17, 44], [55, 47, 20, 40, 14, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [42, 18, 16, 71, 36], [0, 56, 7, 71, 72], [], []]
 b := ![[], [], [32, 51, 12, 55, 69, 72], [69, 31, 9, 20, 5, 36], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 6
  hpos := by decide
  P := [70, 68, 11, 9, 49, 71, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-86620340, -58311524, 119249880, 79737316, 168122650, 116333822]
  a := ![-1, 3, -1, 0, 1, 2]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1186580, -798788, 1633560, 1092292, 2303050, 1593614]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 151334226289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0, 0, 0, 0]] 
 ![![79, 0, 0, 0, 0, 0], ![0, 79, 0, 0, 0, 0], ![0, 0, 79, 0, 0, 0], ![0, 0, 0, 79, 0, 0], ![0, 0, 0, 0, 79, 0], ![0, 0, 0, 0, 0, 79]] where
  M :=![![![79, 0, 0, 0, 0, 0], ![0, 79, 0, 0, 0, 0], ![0, 0, 79, 0, 0, 0], ![0, 0, 0, 79, 0, 0], ![0, 0, 0, 0, 79, 0], ![0, 0, 0, 0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0, 0]], ![![0, 0, 0, 1, 0, 0]], ![![0, 0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 6 2 6 [19, 69, 47, 46, 46, 51, 1] where
 m := 2
 P := ![2, 3]
 exp := ![1, 1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 26, 16, 12, 65, 62], [30, 72, 28, 55, 10, 5], [78, 70, 72, 4, 28, 14], [5, 58, 6, 8, 47, 21], [17, 10, 36, 0, 8, 56], [0, 1]]
 g := ![![[22, 19, 64, 22, 26, 36], [75, 49, 24, 18, 52, 16], [72, 53, 58, 57, 56, 22], [54, 27, 28, 1], [], []], ![[14, 74, 24, 16, 42, 41, 3, 25, 0, 76], [42, 24, 39, 48, 29, 41, 56, 47, 33, 44], [18, 32, 4, 9, 64, 17, 29, 7, 75, 13], [55, 35, 68, 69, 19, 57, 61, 57, 21, 65], [18, 44, 1, 46, 55], [76, 75, 63, 36, 52]], ![[5, 29, 73, 37, 37, 19, 39, 58, 2, 22], [18, 50, 43, 22, 18, 7, 12, 7, 60, 65], [56, 18, 12, 10, 19, 45, 69, 43, 24, 36], [74, 8, 44, 50, 62, 57, 2, 18, 7, 49], [16, 15, 54, 21, 50], [7, 9, 17, 10, 25]], ![[12, 59, 6, 9, 18, 16, 10, 11, 25, 54], [53, 37, 59, 53, 5, 13, 74, 61, 50, 71], [16, 16, 49, 28, 38, 71, 44, 6, 62, 6], [22, 57, 1, 46, 0, 58, 67, 22, 12, 17], [22, 1, 1, 46, 51], [65, 67, 16, 31, 38]], ![[35, 18, 0, 47, 7, 54, 50, 11, 30, 10], [13, 51, 5, 22, 76, 25, 62, 69, 70, 18], [27, 29, 15, 27, 56, 7, 7, 46, 67, 13], [2, 23, 55, 36, 25, 39, 49, 59, 51, 50], [8, 47, 46, 52, 26], [50, 66, 46, 23, 46]], ![[63, 8, 58, 21, 58, 22, 20, 11, 76, 74], [73, 22, 61, 21, 63, 53, 57, 51, 31, 43], [2, 68, 18, 77, 76, 38, 68, 15, 61, 12], [33, 51, 26, 33, 71, 27, 24, 56, 69, 24], [12, 15, 5, 41, 4], [32, 43, 14, 66, 55]]]
 h' := ![![[56, 26, 16, 12, 65, 62], [76, 49, 65, 71, 63, 6], [54, 30, 48, 41, 10, 75], [1, 27, 44, 63, 24, 41], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[30, 72, 28, 55, 10, 5], [51, 3, 4, 44, 47, 68], [28, 61, 34, 68, 12, 75], [36, 70, 11, 12, 9, 56], [36, 74, 28, 21, 38, 65], [33, 35, 29, 78, 74, 23], [56, 26, 16, 12, 65, 62]], ![[78, 70, 72, 4, 28, 14], [44, 21, 38, 8, 61, 73], [23, 51, 36, 58, 1, 48], [70, 49, 41, 71, 43, 24], [67, 62, 66, 11, 23, 51], [56, 32, 61, 10, 47, 45], [30, 72, 28, 55, 10, 5]], ![[5, 58, 6, 8, 47, 21], [2, 62, 70, 58, 10, 7], [27, 38, 65, 37, 42, 38], [71, 77, 27, 41, 78, 55], [8, 4, 71, 64, 12, 62], [30, 27, 13, 28, 32, 50], [78, 70, 72, 4, 28, 14]], ![[17, 10, 36, 0, 8, 56], [57, 45, 36, 74, 37, 18], [60, 49, 1, 19, 13, 21], [2, 76, 63, 38, 51, 11], [61, 31, 10, 9, 43, 35], [23, 63, 70, 58, 7, 42], [5, 58, 6, 8, 47, 21]], ![[0, 1], [22, 57, 24, 61, 19, 65], [56, 8, 53, 14, 1, 59], [62, 17, 51, 12, 32, 50], [18, 66, 62, 53, 41, 24], [76, 1, 63, 63, 77, 77], [17, 10, 36, 0, 8, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [42, 53, 66, 2, 71], [70, 43, 48, 63], [], []]
 b := ![[], [], [34, 29, 23, 56, 78, 49], [65, 20, 36, 30, 35], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 6
  hpos := by decide
  P := [19, 69, 47, 46, 46, 51, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1690693141, 560495520, 2462354160, -811689292, 2997710300, -1002723932]
  a := ![-5, 0, 0, 2, -10, 2]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-21401179, 7094880, 31169040, -10274548, 37945700, -12692708]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 243087455521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀

instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0, 0], ![38, 1, 0, 0, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0, 0, 0, 0], ![38, 1, 0, 0, 0, 0]] 
 ![![83, 0, 0, 0, 0, 0], ![38, 1, 0, 0, 0, 0], ![10, 0, 1, 0, 0, 0], ![35, 0, 0, 1, 0, 0], ![66, 0, 0, 0, 1, 0], ![65, 0, 0, 0, 0, 1]] where
  M :=![![![83, 0, 0, 0, 0, 0], ![0, 83, 0, 0, 0, 0], ![0, 0, 83, 0, 0, 0], ![0, 0, 0, 83, 0, 0], ![0, 0, 0, 0, 83, 0], ![0, 0, 0, 0, 0, 83]], ![![38, 1, 0, 0, 0, 0], ![0, 38, 5, 0, 0, 0], ![0, 0, 38, 1, 0, 0], ![0, 0, 0, 38, 5, 0], ![0, 0, 0, 0, 38, 1], ![-5, 0, 10, 0, 5, 38]]]
  hmulB := by decide  
  f := ![![![1027, -1265, 55880, 44073, 93043, 2301], ![-2241, 2822, -122425, -93043, -190983, 0]], ![![418, -597, 26824, 20886, 43011, 1062], ![-912, 1328, -58764, -44073, -88146, 0]], ![![110, -172, 6703, 6903, 12095, 295], ![-240, 382, -14691, -14691, -24485, 0]], ![![423, -525, 23565, 18558, 40474, 1003], ![-923, 1171, -51625, -39176, -83249, 0]], ![![802, -1004, 44435, 35046, 73959, 1829], ![-1750, 2239, -97350, -73986, -151807, 0]], ![![753, -1003, 43760, 34515, 72865, 1802], ![-1643, 2234, -95875, -72865, -149565, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-38, 83, 0, 0, 0, 0], ![-10, 0, 83, 0, 0, 0], ![-35, 0, 0, 83, 0, 0], ![-66, 0, 0, 0, 83, 0], ![-65, 0, 0, 0, 0, 83]], ![![0, 1, 0, 0, 0, 0], ![-18, 38, 5, 0, 0, 0], ![-5, 0, 38, 1, 0, 0], ![-20, 0, 0, 38, 5, 0], ![-31, 0, 0, 0, 38, 1], ![-35, 0, 10, 0, 5, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0, 0], ![-38, 1, 0, 0, 0, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0, 0, 0, 0], ![-38, 1, 0, 0, 0, 0]] 
 ![![83, 0, 0, 0, 0, 0], ![45, 1, 0, 0, 0, 0], ![10, 0, 1, 0, 0, 0], ![48, 0, 0, 1, 0, 0], ![66, 0, 0, 0, 1, 0], ![18, 0, 0, 0, 0, 1]] where
  M :=![![![83, 0, 0, 0, 0, 0], ![0, 83, 0, 0, 0, 0], ![0, 0, 83, 0, 0, 0], ![0, 0, 0, 83, 0, 0], ![0, 0, 0, 0, 83, 0], ![0, 0, 0, 0, 0, 83]], ![![-38, 1, 0, 0, 0, 0], ![0, -38, 5, 0, 0, 0], ![0, 0, -38, 1, 0, 0], ![0, 0, 0, -38, 5, 0], ![0, 0, 0, 0, -38, 1], ![-5, 0, 10, 0, 5, -38]]]
  hmulB := by decide  
  f := ![![![7791, -103945, -38600, 3655, 87138, -2301], ![17015, -226590, -114125, 4980, 190983, 0]], ![![4257, -56238, -21951, 2064, 49154, -1298], ![9297, -122591, -64076, 2822, 107734, 0]], ![![946, -12466, -4557, 467, 11170, -295], ![2066, -27174, -13529, 664, 24485, 0]], ![![4480, -60086, -22319, 2125, 51391, -1357], ![9784, -130983, -65984, 2905, 112631, 0]], ![![6274, -82664, -30683, 2902, 69264, -1829], ![13702, -180195, -90728, 3951, 151807, 0]], ![![1794, -22464, -8379, 788, 18898, -499], ![3918, -48963, -24744, 1070, 41418, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-45, 83, 0, 0, 0, 0], ![-10, 0, 83, 0, 0, 0], ![-48, 0, 0, 83, 0, 0], ![-66, 0, 0, 0, 83, 0], ![-18, 0, 0, 0, 0, 83]], ![![-1, 1, 0, 0, 0, 0], ![20, -38, 5, 0, 0, 0], ![4, 0, -38, 1, 0, 0], ![18, 0, 0, -38, 5, 0], ![30, 0, 0, 0, -38, 1], ![3, 0, 10, 0, 5, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 0, 2, 0, 2, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-5, 0, 2, 0, 2, 0]] 
 ![![83, 0, 0, 0, 0, 0], ![0, 83, 0, 0, 0, 0], ![15, 0, 1, 0, 0, 0], ![0, 15, 0, 1, 0, 0], ![24, 0, 0, 0, 1, 0], ![0, 24, 0, 0, 0, 1]] where
  M :=![![![-5, 0, 2, 0, 2, 0], ![0, -5, 0, 2, 0, 2], ![-2, 0, -1, 0, 4, 0], ![0, -2, 0, -1, 0, 4], ![-4, 0, 6, 0, 3, 0], ![0, -4, 0, 6, 0, 3]]]
  hmulB := by decide  
  f := ![![![-27, 0, 6, 0, 10, 0]], ![![0, -27, 0, 6, 0, 10]], ![![-5, 0, 1, 0, 2, 0]], ![![0, -5, 0, 1, 0, 2]], ![![-8, 0, 2, 0, 3, 0]], ![![0, -8, 0, 2, 0, 3]]]
  g := ![![![-1, 0, 2, 0, 2, 0], ![0, -1, 0, 2, 0, 2], ![-1, 0, -1, 0, 4, 0], ![0, -1, 0, -1, 0, 4], ![-2, 0, 6, 0, 3, 0], ![0, -2, 0, 6, 0, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P2 : CertificateIrreducibleZModOfList' 83 2 2 6 [24, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 82], [0, 1]]
 g := ![![[6, 51], [75, 7], [59], [41], [47, 69], [1]], ![[49, 32], [63, 76], [59], [41], [71, 14], [1]]]
 h' := ![![[22, 82], [26, 36], [31, 67], [6, 15], [34, 37], [59, 22], [0, 1]], ![[0, 1], [71, 47], [11, 16], [4, 68], [18, 46], [45, 61], [22, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [33, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N2 : CertifiedPrimeIdeal' SI83N2 83 where
  n := 2
  hpos := by decide
  P := [24, 61, 1]
  hirr := P83P2
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![958, -85, 137, 73, -312, -63]
  a := ![13, -1, 1, 1, -4, -1]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![77, 4, 137, 73, -312, -63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N2 B_one_repr
lemma NI83N2 : Nat.card (O ⧸ I83N2) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N2

def I83N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 4, 0, -2, 0]] i)))

def SI83N3: IdealEqSpanCertificate' Table ![![3, 0, 4, 0, -2, 0]] 
 ![![83, 0, 0, 0, 0, 0], ![0, 83, 0, 0, 0, 0], ![57, 0, 1, 0, 0, 0], ![0, 57, 0, 1, 0, 0], ![71, 0, 0, 0, 1, 0], ![0, 71, 0, 0, 0, 1]] where
  M :=![![![3, 0, 4, 0, -2, 0], ![0, 3, 0, 4, 0, -2], ![2, 0, -1, 0, 2, 0], ![0, 2, 0, -1, 0, 2], ![-2, 0, 6, 0, 1, 0], ![0, -2, 0, 6, 0, 1]]]
  hmulB := by decide  
  f := ![![![13, 0, 16, 0, -6, 0]], ![![0, 13, 0, 16, 0, -6]], ![![9, 0, 11, 0, -4, 0]], ![![0, 9, 0, 11, 0, -4]], ![![11, 0, 14, 0, -5, 0]], ![![0, 11, 0, 14, 0, -5]]]
  g := ![![![-1, 0, 4, 0, -2, 0], ![0, -1, 0, 4, 0, -2], ![-1, 0, -1, 0, 2, 0], ![0, -1, 0, -1, 0, 2], ![-5, 0, 6, 0, 1, 0], ![0, -5, 0, 6, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P3 : CertificateIrreducibleZModOfList' 83 2 2 6 [65, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 82], [0, 1]]
 g := ![![[10, 23], [68, 7], [10], [69], [11, 30], [1]], ![[0, 60], [0, 76], [10], [69], [16, 53], [1]]]
 h' := ![![[14, 82], [62, 43], [58, 67], [25, 50], [32, 22], [18, 14], [0, 1]], ![[0, 1], [0, 40], [0, 16], [61, 33], [8, 61], [48, 69], [14, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [75, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N3 : CertifiedPrimeIdeal' SI83N3 83 where
  n := 2
  hpos := by decide
  P := [65, 69, 1]
  hirr := P83P3
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-141, 57, -51, 73, 226, 10]
  a := ![-3, 1, -1, 1, 3, 0]
  z := ![1, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-160, -58, -51, 73, 226, 10]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N3 : Ideal.IsPrime I83N3 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N3 B_one_repr
lemma NI83N3 : Nat.card (O ⧸ I83N3) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N3
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0, 0, 0, 0], ![38, 1, 0, 0, 0, 0]] ![![83, 0, 0, 0, 0, 0], ![-38, 1, 0, 0, 0, 0]]
  ![![-5, 0, -2, 0, 4, 0]] where
 M := ![![![6889, 0, 0, 0, 0, 0], ![-3154, 83, 0, 0, 0, 0]], ![![3154, 83, 0, 0, 0, 0], ![-1444, 0, 5, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1245, 0, -830, 0, 1328, 0]], ![![570, -15, 380, -10, -608, 16]]], ![![![-570, -15, -380, -10, 608, 16]], ![![260, 0, 175, 0, -278, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![-5, 0, -2, 0, 4, 0]] ![![-5, 0, 2, 0, 2, 0]]
  ![![13, 0, 16, 0, -6, 0]] where
 M := ![![![13, 0, 16, 0, -6, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N2 : IdealMulLeCertificate' Table 
  ![![13, 0, 16, 0, -6, 0]] ![![3, 0, 4, 0, -2, 0]]
  ![![83, 0, 0, 0, 0, 0]] where
 M := ![![![83, 0, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2, I83N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
    exact isPrimeI83N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1 ⊙ MulI83N2)


lemma PB87I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 86 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 86 (by omega)
  rfl

def PB87I2 : PrimesBelowBoundCertificateInterval' O 61 86 87 where
  m := 5
  g := ![2, 5, 1, 1, 4]
  P := ![67, 71, 73, 79, 83]
  hP := PB87I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2, I71N3, I71N4]
    · exact ![I73N0]
    · exact ![I79N0]
    · exact ![I83N0, I83N1, I83N2, I83N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
    · exact PBC83
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![300763, 300763]
    · exact ![5041, 71, 71, 71, 71]
    · exact ![151334226289]
    · exact ![243087455521]
    · exact ![83, 83, 6889, 6889]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
      exact NI71N3
      exact NI71N4
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
      exact NI83N3
  Il := ![[], [I71N1, I71N2, I71N3, I71N4], [], [], [I83N0, I83N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
