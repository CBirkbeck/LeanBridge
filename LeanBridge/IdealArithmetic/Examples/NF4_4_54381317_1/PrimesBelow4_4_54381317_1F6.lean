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
instance hp283 : Fact (Nat.Prime 283) := {out := by norm_num}

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![283, 0, 0, 0]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![283, 0, 0, 0]] 
 ![![283, 0, 0, 0], ![0, 283, 0, 0], ![0, 0, 283, 0], ![0, 0, 0, 283]] where
  M :=![![![283, 0, 0, 0], ![0, 283, 0, 0], ![0, 0, 283, 0], ![0, 0, 0, 283]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 4 2 8 [248, 199, 194, 267, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [253, 179, 191, 112], [276, 200, 111, 280], [53, 186, 264, 174], [0, 1]]
 g := ![![[80, 253, 42, 36], [154, 180, 156, 179], [253, 134, 179], [124, 189, 2, 16], [54, 74, 272, 36], [167, 152, 256], [1], []],![[48, 22, 31, 60, 231, 176], [81, 142, 282, 83, 230, 161], [75, 145, 129], [195, 243, 214, 104, 81, 73], [251, 175, 264, 244, 7, 16], [282, 211, 57], [151, 19, 85], [178, 108, 92]],![[8, 124, 266, 212, 146, 248], [206, 197, 174, 236, 50, 159], [39, 273, 214], [193, 14, 203, 234, 43, 110], [266, 151, 10, 108, 274, 228], [14, 184, 163], [52, 72, 278], [174, 44, 9]],![[186, 84, 82, 57, 193, 113], [221, 55, 273, 90, 190, 144], [94, 268, 240], [69, 51, 16, 96, 44, 28], [164, 34, 31, 83, 208, 160], [127, 175, 168], [33, 201, 207], [22, 100, 278]]]
 h' := ![![[253, 179, 191, 112], [13, 46, 97, 6], [51, 167, 88, 184], [95, 125, 132, 99], [192, 76, 39, 4], [278, 41, 69, 6], [35, 84, 89, 16], [0, 0, 1], [0, 1]],![[276, 200, 111, 280], [96, 123, 30, 222], [94, 212, 116, 14], [279, 228, 278, 107], [117, 131, 131, 32], [103, 154, 247, 274], [103, 170, 39, 118], [55, 68, 39, 59], [253, 179, 191, 112]],![[53, 186, 264, 174], [254, 52, 219, 39], [41, 11, 99, 71], [146, 22, 59, 110], [193, 143, 234, 111], [160, 59, 265, 115], [50, 148, 18, 27], [196, 55, 211, 109], [276, 200, 111, 280]],![[0, 1], [4, 62, 220, 16], [278, 176, 263, 14], [136, 191, 97, 250], [250, 216, 162, 136], [257, 29, 268, 171], [118, 164, 137, 122], [183, 160, 32, 115], [53, 186, 264, 174]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [203, 63, 114], []]
 b := ![[], [], [36, 213, 253, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where 
  n := 4
  hpos := by decide  
  P := [248, 199, 194, 267, 1]
  hirr := P283P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![49599191563, 47365264841, 14557973649, 1430578301]
  a := ![0, -1, -1, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![175262161, 167368427, 51441603, 5055047]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 6414247921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def PBC283 : ContainsPrimesAboveP 283 ![I283N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI283N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![283, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 283 (by decide) 𝕀

instance hp293 : Fact (Nat.Prime 293) := {out := by norm_num}

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![293, 0, 0, 0], ![-19, -67, -4, 1]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![293, 0, 0, 0], ![-19, -67, -4, 1]] 
 ![![293, 0, 0, 0], ![0, 293, 0, 0], ![33, 112, 1, 0], ![113, 88, 0, 1]] where
  M :=![![![293, 0, 0, 0], ![0, 293, 0, 0], ![0, 0, 293, 0], ![0, 0, 0, 293]], ![![-19, -67, -4, 1], ![383, 313, 13, -3], ![-1149, -613, 73, 10], ![3830, 2171, 187, 83]]]
  hmulB := by decide  
  f := ![![![20076844, 15552435, 625728, -143121], ![-4867023, -15600492, 0, 0]], ![![-98405, -76198, -3065, 701], ![24026, 76473, 0, 0]], ![![2223609, 1722548, 69305, -15852], ![-538824, -1727820, 0, 0]], ![![7713386, 5975133, 240400, -54986], ![-1869913, -5993604, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-33, -112, 293, 0], ![-113, -88, 0, 293]], ![![0, 1, -4, 1], ![1, -3, 13, -3], ![-16, -33, 73, 10], ![-40, -89, 187, 83]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 2 2 8 [182, 253, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 292], [0, 1]]
 g := ![![[3, 59], [205], [263, 193], [250], [38], [135, 69], [135], [1]],![[19, 234], [205], [72, 100], [250], [38], [258, 224], [135], [1]]]
 h' := ![![[40, 292], [216, 158], [186, 232], [149, 208], [122, 152], [42, 193], [57, 216], [111, 40], [0, 1]],![[0, 1], [90, 135], [90, 61], [265, 85], [49, 141], [144, 100], [200, 77], [246, 253], [40, 292]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [168]]
 b := ![[], [78, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where 
  n := 2
  hpos := by decide  
  P := [182, 253, 1]
  hirr := P293P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![1552745, 1298366, 266692, -5908]
  a := ![-2, 3, -64, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-22459, -95738, 266692, -5908]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 85849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![293, 0, 0, 0], ![-244, -67, -4, 1]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![293, 0, 0, 0], ![-244, -67, -4, 1]] 
 ![![293, 0, 0, 0], ![0, 293, 0, 0], ![237, 180, 1, 0], ![118, 67, 0, 1]] where
  M :=![![![293, 0, 0, 0], ![0, 293, 0, 0], ![0, 0, 293, 0], ![0, 0, 0, 293]], ![![-244, -67, -4, 1], ![383, 88, 13, -3], ![-1149, -613, -152, 10], ![3830, 2171, 187, -142]]]
  hmulB := by decide  
  f := ![![![8384049, 1651440, 392208, -88576], ![-7364848, -11105872, 0, 0]], ![![-45470, -8948, -2130, 481], ![40141, 60358, 0, 0]], ![![6753629, 1330289, 315937, -71351], ![-5932661, -8946168, 0, 0]], ![![3366052, 663022, 157466, -35562], ![-2956943, -4458870, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-237, -180, 293, 0], ![-118, -67, 0, 293]], ![![2, 2, -4, 1], ![-8, -7, 13, -3], ![115, 89, -152, 10], ![-81, -75, 187, -142]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P1 : CertificateIrreducibleZModOfList' 293 2 2 8 [187, 212, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 292], [0, 1]]
 g := ![![[291, 115], [43], [278, 140], [88], [57], [44, 211], [115], [1]],![[230, 178], [43], [191, 153], [88], [57], [141, 82], [115], [1]]]
 h' := ![![[81, 292], [259, 81], [168, 173], [236, 169], [172, 214], [269, 49], [279, 117], [106, 81], [0, 1]],![[0, 1], [81, 212], [117, 120], [154, 124], [219, 79], [136, 244], [87, 176], [221, 212], [81, 292]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131]]
 b := ![[], [204, 212]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N1 : CertifiedPrimeIdeal' SI293N1 293 where 
  n := 2
  hpos := by decide  
  P := [187, 212, 1]
  hirr := P293P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![274970, 239735, 62094, 3318]
  a := ![-1, 1, 1, -3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-50624, -38087, 62094, 3318]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N1 B_one_repr
lemma NI293N1 : Nat.card (O ⧸ I293N1) = 85849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N1
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![293, 0, 0, 0], ![-19, -67, -4, 1]] ![![293, 0, 0, 0], ![-244, -67, -4, 1]]
  ![![293, 0, 0, 0]] where
 M :=  ![![![85849, 0, 0, 0], ![-71492, -19631, -1172, 293]], ![![-5567, -19631, -1172, 293], ![-12599, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![293, 0, 0, 0]], ![![-244, -67, -4, 1]]], ![![![-19, -67, -4, 1]], ![![-43, 0, 0, 0]]]]
 hle2 := by decide  


def PBC293 : ContainsPrimesAboveP 293 ![I293N0, I293N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI293N0
    exact isPrimeI293N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 293 (by decide) (𝕀 ⊙ MulI293N0)
instance hp307 : Fact (Nat.Prime 307) := {out := by norm_num}

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![307, 0, 0, 0], ![-264, -67, -4, 1]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![307, 0, 0, 0], ![-264, -67, -4, 1]] 
 ![![307, 0, 0, 0], ![0, 307, 0, 0], ![205, 174, 1, 0], ![249, 15, 0, 1]] where
  M :=![![![307, 0, 0, 0], ![0, 307, 0, 0], ![0, 0, 307, 0], ![0, 0, 0, 307]], ![![-264, -67, -4, 1], ![383, 68, 13, -3], ![-1149, -613, -172, 10], ![3830, 2171, 187, -162]]]
  hmulB := by decide  
  f := ![![![1332064, 159090, 64293, -14541], ![-1180722, -1881603, 0, 0]], ![![-49189, -5854, -2379, 538], ![43901, 69689, 0, 0]], ![![861646, 102924, 41584, -9405], ![-763506, -1216947, 0, 0]], ![![1077855, 128711, 52028, -11767], ![-955678, -1522716, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-205, -174, 307, 0], ![-249, -15, 0, 307]], ![![1, 2, -4, 1], ![-5, -7, 13, -3], ![103, 95, -172, 10], ![19, -91, 187, -162]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 2 2 8 [92, 257, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 306], [0, 1]]
 g := ![![[193, 62], [193, 103], [212], [259], [105, 223], [282, 37], [44], [1]],![[223, 245], [124, 204], [212], [259], [203, 84], [290, 270], [44], [1]]]
 h' := ![![[50, 306], [50, 281], [148, 32], [305, 186], [164, 167], [151, 60], [118, 61], [215, 50], [0, 1]],![[0, 1], [285, 26], [213, 275], [88, 121], [225, 140], [81, 247], [98, 246], [259, 257], [50, 306]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [235]]
 b := ![[], [286, 271]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where 
  n := 2
  hpos := by decide  
  P := [92, 257, 1]
  hirr := P307P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![29966, 25256, 6035, 589]
  a := ![0, -1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-4410, -3367, 6035, 589]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 94249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![307, 0, 0, 0], ![36, 1, 0, 0]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![307, 0, 0, 0], ![36, 1, 0, 0]] 
 ![![307, 0, 0, 0], ![36, 1, 0, 0], ![239, 0, 1, 0], ![299, 0, 0, 1]] where
  M :=![![![307, 0, 0, 0], ![0, 307, 0, 0], ![0, 0, 307, 0], ![0, 0, 0, 307]], ![![36, 1, 0, 0], ![0, 36, 1, 0], ![0, 0, 36, 1], ![383, 332, 80, 37]]]
  hmulB := by decide  
  f := ![![![9577, -757282, -21331, -8], ![-81662, 6460201, 2456, 0]], ![![1116, -88853, -2505, -1], ![-9516, 757983, 307, 0]], ![![7385, -589547, -16634, -7], ![-62971, 5029275, 2149, 0]], ![![9281, -737558, -20783, -8], ![-79138, 6291929, 2457, 0]]]
  g := ![![![1, 0, 0, 0], ![-36, 307, 0, 0], ![-239, 0, 307, 0], ![-299, 0, 0, 307]], ![![0, 1, 0, 0], ![-5, 36, 1, 0], ![-29, 0, 36, 1], ![-136, 332, 80, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N1 : Nat.card (O ⧸ I307N1) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N1)

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := prime_ideal_of_norm_prime hp307.out _ NI307N1

def I307N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![307, 0, 0, 0], ![96, 1, 0, 0]] i)))

def SI307N2: IdealEqSpanCertificate' Table ![![307, 0, 0, 0], ![96, 1, 0, 0]] 
 ![![307, 0, 0, 0], ![96, 1, 0, 0], ![301, 0, 1, 0], ![269, 0, 0, 1]] where
  M :=![![![307, 0, 0, 0], ![0, 307, 0, 0], ![0, 0, 307, 0], ![0, 0, 0, 307]], ![![96, 1, 0, 0], ![0, 96, 1, 0], ![0, 0, 96, 1], ![383, 332, 80, 97]]]
  hmulB := by decide  
  f := ![![![2785, -24739, -354, -1], ![-8903, 79206, 307, 0]], ![![672, -7865, -178, -1], ![-2148, 25174, 307, 0]], ![![2815, -24259, -349, -1], ![-8999, 77672, 307, 0]], ![![2399, -21641, -322, -1], ![-7669, 69286, 308, 0]]]
  g := ![![![1, 0, 0, 0], ![-96, 307, 0, 0], ![-301, 0, 307, 0], ![-269, 0, 0, 307]], ![![0, 1, 0, 0], ![-31, 96, 1, 0], ![-95, 0, 96, 1], ![-266, 332, 80, 97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N2 : Nat.card (O ⧸ I307N2) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N2)

lemma isPrimeI307N2 : Ideal.IsPrime I307N2 := prime_ideal_of_norm_prime hp307.out _ NI307N2
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![307, 0, 0, 0], ![-264, -67, -4, 1]] ![![307, 0, 0, 0], ![36, 1, 0, 0]]
  ![![307, 0, 0, 0], ![-4209, -2344, -131, 33]] where
 M :=  ![![![94249, 0, 0, 0], ![11052, 307, 0, 0]], ![![-81048, -20569, -1228, 307], ![-9121, -2344, -131, 33]]]
 hmul := by decide  
 g :=  ![![![![307, 0, 0, 0], ![0, 0, 0, 0]], ![![36, 1, 0, 0], ![0, 0, 0, 0]]], ![![![3945, 2277, 127, -32], ![307, 0, 0, 0]], ![![4193, 2344, 131, -33], ![308, 0, 0, 0]]]]
 hle2 := by decide  

def MulI307N1 : IdealMulLeCertificate' Table 
  ![![307, 0, 0, 0], ![-4209, -2344, -131, 33]] ![![307, 0, 0, 0], ![96, 1, 0, 0]]
  ![![307, 0, 0, 0]] where
 M :=  ![![![94249, 0, 0, 0], ![29472, 307, 0, 0]], ![![-1292163, -719608, -40217, 10131], ![-391425, -218277, -12280, 3070]]]
 hmul := by decide  
 g :=  ![![![![307, 0, 0, 0]], ![![96, 1, 0, 0]]], ![![![-4209, -2344, -131, 33]], ![![-1275, -711, -40, 10]]]]
 hle2 := by decide  


def PBC307 : ContainsPrimesAboveP 307 ![I307N0, I307N1, I307N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI307N0
    exact isPrimeI307N1
    exact isPrimeI307N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 307 (by decide) (𝕀 ⊙ MulI307N0 ⊙ MulI307N1)
instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![311, 0, 0, 0], ![92, 1, 0, 0]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![311, 0, 0, 0], ![92, 1, 0, 0]] 
 ![![311, 0, 0, 0], ![92, 1, 0, 0], ![244, 0, 1, 0], ![255, 0, 0, 1]] where
  M :=![![![311, 0, 0, 0], ![0, 311, 0, 0], ![0, 0, 311, 0], ![0, 0, 0, 311]], ![![92, 1, 0, 0], ![0, 92, 1, 0], ![0, 0, 92, 1], ![383, 332, 80, 93]]]
  hmulB := by decide  
  f := ![![![11685, -466589, -5533, -5], ![-39497, 1577703, 1555, 0]], ![![3312, -138056, -1685, -2], ![-11195, 466811, 622, 0]], ![![9228, -365968, -4347, -4], ![-31192, 1237470, 1244, 0]], ![![9549, -382497, -4527, -4], ![-32277, 1293357, 1245, 0]]]
  g := ![![![1, 0, 0, 0], ![-92, 311, 0, 0], ![-244, 0, 311, 0], ![-255, 0, 0, 311]], ![![0, 1, 0, 0], ![-28, 92, 1, 0], ![-73, 0, 92, 1], ![-236, 332, 80, 93]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N0 : Nat.card (O ⧸ I311N0) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N0)

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := prime_ideal_of_norm_prime hp311.out _ NI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![311, 0, 0, 0], ![-71, 1, 0, 0]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![311, 0, 0, 0], ![-71, 1, 0, 0]] 
 ![![311, 0, 0, 0], ![240, 1, 0, 0], ![246, 0, 1, 0], ![50, 0, 0, 1]] where
  M :=![![![311, 0, 0, 0], ![0, 311, 0, 0], ![0, 0, 311, 0], ![0, 0, 0, 311]], ![![-71, 1, 0, 0], ![0, -71, 1, 0], ![0, 0, -71, 1], ![383, 332, 80, -70]]]
  hmulB := by decide  
  f := ![![![16260, -1428465, 21181, -15], ![71219, -6256076, 4665, 0]], ![![12426, -1102237, 16303, -11], ![54426, -4827342, 3421, 0]], ![![12726, -1129860, 16763, -12], ![55740, -4948320, 3732, 0]], ![![2784, -229566, 3446, -3], ![12194, -1005392, 934, 0]]]
  g := ![![![1, 0, 0, 0], ![-240, 311, 0, 0], ![-246, 0, 311, 0], ![-50, 0, 0, 311]], ![![-1, 1, 0, 0], ![54, -71, 1, 0], ![56, 0, -71, 1], ![-307, 332, 80, -70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N1 : Nat.card (O ⧸ I311N1) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N1)

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := prime_ideal_of_norm_prime hp311.out _ NI311N1

def I311N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![311, 0, 0, 0], ![-18, 1, 0, 0]] i)))

def SI311N2: IdealEqSpanCertificate' Table ![![311, 0, 0, 0], ![-18, 1, 0, 0]] 
 ![![311, 0, 0, 0], ![293, 1, 0, 0], ![298, 0, 1, 0], ![77, 0, 0, 1]] where
  M :=![![![311, 0, 0, 0], ![0, 311, 0, 0], ![0, 0, 311, 0], ![0, 0, 0, 311]], ![![-18, 1, 0, 0], ![0, -18, 1, 0], ![0, 0, -18, 1], ![383, 332, 80, -17]]]
  hmulB := by decide  
  f := ![![![4627, -413825, 23066, -5], ![79927, -7145536, 1555, 0]], ![![4375, -389853, 21735, -5], ![75574, -6731595, 1555, 0]], ![![4448, -396517, 22105, -5], ![76835, -6846664, 1555, 0]], ![![1189, -102449, 5724, -2], ![20539, -1768950, 623, 0]]]
  g := ![![![1, 0, 0, 0], ![-293, 311, 0, 0], ![-298, 0, 311, 0], ![-77, 0, 0, 311]], ![![-1, 1, 0, 0], ![16, -18, 1, 0], ![17, 0, -18, 1], ![-384, 332, 80, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N2 : Nat.card (O ⧸ I311N2) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N2)

lemma isPrimeI311N2 : Ideal.IsPrime I311N2 := prime_ideal_of_norm_prime hp311.out _ NI311N2

def I311N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![311, 0, 0, 0], ![-4, 1, 0, 0]] i)))

def SI311N3: IdealEqSpanCertificate' Table ![![311, 0, 0, 0], ![-4, 1, 0, 0]] 
 ![![311, 0, 0, 0], ![307, 1, 0, 0], ![295, 0, 1, 0], ![247, 0, 0, 1]] where
  M :=![![![311, 0, 0, 0], ![0, 311, 0, 0], ![0, 0, 311, 0], ![0, 0, 0, 311]], ![![-4, 1, 0, 0], ![0, -4, 1, 0], ![0, 0, -4, 1], ![383, 332, 80, -3]]]
  hmulB := by decide  
  f := ![![![321, -76, 42431, -10608], ![24880, 311, 3299088, 0]], ![![317, -75, 42119, -10530], ![24570, 311, 3274830, 0]], ![![305, -72, 40247, -10062], ![23640, 312, 3129282, 0]], ![![257, -60, 33699, -8425], ![19920, 315, 2620176, 0]]]
  g := ![![![1, 0, 0, 0], ![-307, 311, 0, 0], ![-295, 0, 311, 0], ![-247, 0, 0, 311]], ![![-1, 1, 0, 0], ![3, -4, 1, 0], ![3, 0, -4, 1], ![-400, 332, 80, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N3 : Nat.card (O ⧸ I311N3) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N3)

lemma isPrimeI311N3 : Ideal.IsPrime I311N3 := prime_ideal_of_norm_prime hp311.out _ NI311N3
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![311, 0, 0, 0], ![92, 1, 0, 0]] ![![311, 0, 0, 0], ![-71, 1, 0, 0]]
  ![![812, 369, 16, -5]] where
 M :=  ![![![96721, 0, 0, 0], ![-22081, 311, 0, 0]], ![![28612, 311, 0, 0], ![-6532, 21, 1, 0]]]
 hmul := by decide  
 g :=  ![![![![35765, 17727, 622, -311]], ![![-8548, -4264, -165, 72]]], ![![![10197, 5027, 161, -91]], ![![-2440, -1212, -44, 21]]]]
 hle2 := by decide  

def MulI311N1 : IdealMulLeCertificate' Table 
  ![![812, 369, 16, -5]] ![![311, 0, 0, 0], ![-18, 1, 0, 0]]
  ![![311, 0, 0, 0], ![-11771, -6052, -355, 89]] where
 M :=  ![![![252532, 114759, 4976, -1555], ![-16531, -7490, -319, 101]]]
 hmul := by decide  
 g :=  ![![![![812, 369, 16, -5], ![0, 0, 0, 0]], ![![3164, 1630, 96, -24], ![85, 0, 0, 0]]]]
 hle2 := by decide  

def MulI311N2 : IdealMulLeCertificate' Table 
  ![![311, 0, 0, 0], ![-11771, -6052, -355, 89]] ![![311, 0, 0, 0], ![-4, 1, 0, 0]]
  ![![311, 0, 0, 0]] where
 M :=  ![![![96721, 0, 0, 0], ![-1244, 311, 0, 0]], ![![-3660781, -1882172, -110405, 27679], ![81171, 41985, 2488, -622]]]
 hmul := by decide  
 g :=  ![![![![311, 0, 0, 0]], ![![-4, 1, 0, 0]]], ![![![-11771, -6052, -355, 89]], ![![261, 135, 8, -2]]]]
 hle2 := by decide  


def PBC311 : ContainsPrimesAboveP 311 ![I311N0, I311N1, I311N2, I311N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI311N0
    exact isPrimeI311N1
    exact isPrimeI311N2
    exact isPrimeI311N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 311 (by decide) (𝕀 ⊙ MulI311N0 ⊙ MulI311N1 ⊙ MulI311N2)
instance hp313 : Fact (Nat.Prime 313) := {out := by norm_num}

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![313, 0, 0, 0], ![-92, 50, -4, 1]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![313, 0, 0, 0], ![-92, 50, -4, 1]] 
 ![![313, 0, 0, 0], ![0, 313, 0, 0], ![46, 311, 1, 0], ![92, 42, 0, 1]] where
  M :=![![![313, 0, 0, 0], ![0, 313, 0, 0], ![0, 0, 313, 0], ![0, 0, 0, 313]], ![![-92, 50, -4, 1], ![383, 240, 130, -3], ![-1149, -613, 0, 127], ![48641, 41015, 9547, 127]]]
  hmulB := by decide  
  f := ![![![6422541, 4439990, 2285044, -49229], ![-1207867, -5538848, 0, 0]], ![![-28601, -19859, -10198, 219], ![5634, 24727, 0, 0]], ![![915439, 632807, 325687, -7017], ![-172020, -789447, 0, 0]], ![![1883986, 1302354, 670276, -14441], ![-354108, -1624714, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-46, -311, 313, 0], ![-92, -42, 0, 313]], ![![0, 4, -4, 1], ![-17, -128, 130, -3], ![-41, -19, 0, 127], ![-1285, -9372, 9547, 127]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 2 2 8 [270, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [263, 312], [0, 1]]
 g := ![![[290, 213], [232], [96], [271, 309], [165, 50], [94, 22], [309], [1]],![[282, 100], [232], [96], [158, 4], [169, 263], [246, 291], [309], [1]]]
 h' := ![![[263, 312], [97, 250], [235, 225], [72, 224], [209, 263], [286, 26], [112, 282], [43, 263], [0, 1]],![[0, 1], [117, 63], [253, 88], [140, 89], [205, 50], [238, 287], [97, 31], [39, 50], [263, 312]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [231]]
 b := ![[], [227, 272]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where 
  n := 2
  hpos := by decide  
  P := [270, 50, 1]
  hirr := P313P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![281171, 243597, 62756, 4220]
  a := ![19, 1, -1, 3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-9565, -62143, 62756, 4220]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 97969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![313, 0, 0, 0], ![-6, -129, -4, 1]] i)))

def SI313N1: IdealEqSpanCertificate' Table ![![313, 0, 0, 0], ![-6, -129, -4, 1]] 
 ![![313, 0, 0, 0], ![0, 313, 0, 0], ![189, 1, 1, 0], ![124, 188, 0, 1]] where
  M :=![![![313, 0, 0, 0], ![0, 313, 0, 0], ![0, 0, 313, 0], ![0, 0, 0, 313]], ![![-6, -129, -4, 1], ![383, 326, -49, -3], ![-1149, -613, 86, -52], ![-19916, -18413, -4773, 34]]]
  hmulB := by decide  
  f := ![![![19176843, 13919324, -2545926, -131722], ![-6072200, -15767062, 0, 0]], ![![-107735, -78196, 14303, 740], ![34117, 88579, 0, 0]], ![![11579284, 8404730, -1537270, -79536], ![-3666441, -9520403, 0, 0]], ![![7532510, 5467485, -1000016, -51740], ![-2384895, -6193172, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-189, -1, 313, 0], ![-124, -188, 0, 313]], ![![2, -1, -4, 1], ![32, 3, -49, -3], ![-35, 29, 86, -52], ![2805, -64, -4773, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P1 : CertificateIrreducibleZModOfList' 313 2 2 8 [208, 186, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 312], [0, 1]]
 g := ![![[34, 155], [78], [13], [270, 88], [296, 22], [15, 302], [166], [1]],![[0, 158], [78], [13], [178, 225], [273, 291], [183, 11], [166], [1]]]
 h' := ![![[127, 312], [8, 239], [274, 144], [180, 221], [93, 251], [10, 282], [285, 176], [105, 127], [0, 1]],![[0, 1], [0, 74], [95, 169], [77, 92], [44, 62], [142, 31], [101, 137], [271, 186], [127, 312]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [302, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N1 : CertifiedPrimeIdeal' SI313N1 313 where 
  n := 2
  hpos := by decide  
  P := [208, 186, 1]
  hirr := P313P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![126030, 112292, 30692, 2665]
  a := ![-1, 0, 1, 2]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-19186, -1340, 30692, 2665]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI313N1 : Ideal.IsPrime I313N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N1 B_one_repr
lemma NI313N1 : Nat.card (O ⧸ I313N1) = 97969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N1
def MulI313N0 : IdealMulLeCertificate' Table 
  ![![313, 0, 0, 0], ![-92, 50, -4, 1]] ![![313, 0, 0, 0], ![-6, -129, -4, 1]]
  ![![313, 0, 0, 0]] where
 M :=  ![![![97969, 0, 0, 0], ![-1878, -40377, -1252, 313]], ![![-28796, 15650, -1252, 313], ![4382, 12207, -7199, 0]]]
 hmul := by decide  
 g :=  ![![![![313, 0, 0, 0]], ![![-6, -129, -4, 1]]], ![![![-92, 50, -4, 1]], ![![14, 39, -23, 0]]]]
 hle2 := by decide  


def PBC313 : ContainsPrimesAboveP 313 ![I313N0, I313N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI313N0
    exact isPrimeI313N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 313 (by decide) (𝕀 ⊙ MulI313N0)
instance hp317 : Fact (Nat.Prime 317) := {out := by norm_num}

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![317, 0, 0, 0]] i)))

def SI317N0: IdealEqSpanCertificate' Table ![![317, 0, 0, 0]] 
 ![![317, 0, 0, 0], ![0, 317, 0, 0], ![0, 0, 317, 0], ![0, 0, 0, 317]] where
  M :=![![![317, 0, 0, 0], ![0, 317, 0, 0], ![0, 0, 317, 0], ![0, 0, 0, 317]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P0 : CertificateIrreducibleZModOfList' 317 4 2 8 [287, 167, 130, 82, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [173, 216, 236, 172], [127, 138, 60, 128], [252, 279, 21, 17], [0, 1]]
 g := ![![[122, 3, 226, 23], [66, 166, 235], [204, 210, 120, 54], [46, 164, 286, 160], [47, 2, 243, 235], [248, 140, 293, 67], [1], []],![[205, 311, 137, 88, 167, 289], [109, 134, 77], [244, 36, 117, 151, 247, 138], [119, 169, 95, 248, 291, 81], [43, 88, 109, 175, 286, 79], [56, 76, 198, 210, 309, 9], [174, 237, 63], [110, 145, 103]],![[266, 258, 102, 229, 257, 109], [43, 203, 266], [76, 216, 110, 34, 19, 304], [7, 32, 58, 205, 189, 183], [227, 55, 165, 153, 83, 303], [54, 277, 41, 12, 105, 200], [151, 250, 251], [135, 102, 217]],![[189, 129, 170, 283, 163, 249], [37, 7, 54], [232, 74, 118, 92, 115, 143], [278, 111, 297, 121, 267, 272], [106, 70, 152, 140, 117, 127], [249, 61, 60, 101, 158, 298], [120, 149, 10], [59, 157, 289]]]
 h' := ![![[173, 216, 236, 172], [294, 14, 306, 221], [97, 309, 237, 251], [112, 284, 159, 110], [142, 147, 107, 193], [149, 139, 210, 251], [30, 150, 187, 235], [0, 0, 1], [0, 1]],![[127, 138, 60, 128], [0, 247, 260, 81], [189, 169, 300, 146], [227, 71, 237, 253], [114, 69, 78, 69], [239, 96, 277, 197], [114, 17, 231, 294], [261, 169, 6, 54], [173, 216, 236, 172]],![[252, 279, 21, 17], [273, 173, 94, 104], [232, 276, 182, 30], [81, 253, 237, 291], [132, 196, 130, 59], [23, 307, 149, 219], [244, 231, 55, 239], [208, 34, 187, 232], [127, 138, 60, 128]],![[0, 1], [229, 200, 291, 228], [76, 197, 232, 207], [221, 26, 1, 297], [291, 222, 2, 313], [205, 92, 315, 284], [263, 236, 161, 183], [289, 114, 123, 31], [252, 279, 21, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [142, 20, 316], []]
 b := ![[], [], [66, 256, 10, 265], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N0 : CertifiedPrimeIdeal' SI317N0 317 where 
  n := 4
  hpos := by decide  
  P := [287, 167, 130, 82, 1]
  hirr := P317P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![675566232237, 645758988200, 198761700840, 19575808146]
  a := ![-5, 0, 0, 2]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![2131123761, 2037094600, 627008520, 61753338]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI317N0 : Ideal.IsPrime I317N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N0 B_one_repr
lemma NI317N0 : Nat.card (O ⧸ I317N0) = 10098039121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N0

def PBC317 : ContainsPrimesAboveP 317 ![I317N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI317N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![317, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 317 (by decide) 𝕀

instance hp331 : Fact (Nat.Prime 331) := {out := by norm_num}

def I331N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![331, 0, 0, 0]] i)))

def SI331N0: IdealEqSpanCertificate' Table ![![331, 0, 0, 0]] 
 ![![331, 0, 0, 0], ![0, 331, 0, 0], ![0, 0, 331, 0], ![0, 0, 0, 331]] where
  M :=![![![331, 0, 0, 0], ![0, 331, 0, 0], ![0, 0, 331, 0], ![0, 0, 0, 331]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P0 : CertificateIrreducibleZModOfList' 331 4 2 8 [39, 241, 239, 175, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 233, 118, 160], [56, 186, 208, 186], [38, 242, 5, 316], [0, 1]]
 g := ![![[270, 48, 90, 296], [184, 123, 7, 293], [260, 230, 319], [148, 116, 74, 318], [231, 151, 69], [238, 209, 53], [156, 1], []],![[169, 19, 113, 241, 257, 116], [294, 220, 142, 226, 151, 48], [44, 50, 291], [305, 327, 112, 17, 170, 2], [90, 112, 17], [234, 246, 139], [0, 221, 48, 177, 204, 178], [15, 111, 113]],![[306, 34, 218, 223, 164, 31], [74, 263, 223, 92, 44, 89], [252, 231, 294], [330, 30, 31, 314, 138, 195], [111, 278, 105], [273, 179, 215], [30, 309, 86, 223, 97, 215], [228, 274, 172]],![[254, 298, 317, 28, 231, 6], [78, 123, 87, 187, 5, 297], [114, 52, 281], [7, 168, 14, 16, 220, 161], [138, 6, 1], [273, 94, 274], [53, 74, 143, 154, 325, 150], [193, 195, 225]]]
 h' := ![![[62, 233, 118, 160], [106, 298, 178, 222], [293, 271, 172, 151], [186, 244, 278, 205], [273, 260, 15, 48], [305, 237, 75, 311], [205, 99, 209, 265], [0, 0, 1], [0, 1]],![[56, 186, 208, 186], [94, 79, 322, 3], [20, 245, 36, 35], [322, 190, 101, 195], [255, 10, 172, 38], [64, 214, 113, 103], [65, 275, 39, 158], [280, 95, 85, 236], [62, 233, 118, 160]],![[38, 242, 5, 316], [1, 127, 54, 291], [213, 95, 182, 121], [251, 300, 297, 306], [303, 84, 3, 280], [75, 324, 218, 247], [285, 292, 256, 154], [202, 214, 168, 27], [56, 186, 208, 186]],![[0, 1], [113, 158, 108, 146], [319, 51, 272, 24], [243, 259, 317, 287], [32, 308, 141, 296], [117, 218, 256, 1], [186, 327, 158, 85], [206, 22, 77, 68], [38, 242, 5, 316]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [184, 3, 317], []]
 b := ![[], [], [327, 230, 293, 146], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N0 : CertifiedPrimeIdeal' SI331N0 331 where 
  n := 4
  hpos := by decide  
  P := [39, 241, 239, 175, 1]
  hirr := P331P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![32394757167, 21707774400, 2445611043, -413681152]
  a := ![-10, 2, 13, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![97869357, 65582400, 7388553, -1249792]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI331N0 : Ideal.IsPrime I331N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N0 B_one_repr
lemma NI331N0 : Nat.card (O ⧸ I331N0) = 12003612721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N0

def PBC331 : ContainsPrimesAboveP 331 ![I331N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI331N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![331, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 331 (by decide) 𝕀

instance hp337 : Fact (Nat.Prime 337) := {out := by norm_num}

def I337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![337, 0, 0, 0], ![-60, -67, -4, 1]] i)))

def SI337N0: IdealEqSpanCertificate' Table ![![337, 0, 0, 0], ![-60, -67, -4, 1]] 
 ![![337, 0, 0, 0], ![0, 337, 0, 0], ![203, 71, 1, 0], ![78, 217, 0, 1]] where
  M :=![![![337, 0, 0, 0], ![0, 337, 0, 0], ![0, 0, 337, 0], ![0, 0, 0, 337]], ![![-60, -67, -4, 1], ![383, 272, 13, -3], ![-1149, -613, 32, 10], ![3830, 2171, 187, 42]]]
  hmulB := by decide  
  f := ![![![10586657, 7277058, 339904, -77678], ![-3335626, -9837704, 0, 0]], ![![-64514, -44328, -2070, 473], ![20557, 59986, 0, 0]], ![![6363501, 4374134, 204311, -46691], ![-2005147, -5913338, 0, 0]], ![![2408764, 1655740, 77338, -17674], ![-758911, -2238350, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-203, -71, 337, 0], ![-78, -217, 0, 337]], ![![2, 0, -4, 1], ![-6, 0, 13, -3], ![-25, -15, 32, 10], ![-111, -60, 187, 42]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P0 : CertificateIrreducibleZModOfList' 337 2 2 8 [294, 160, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [177, 336], [0, 1]]
 g := ![![[106, 47], [274], [182], [310], [30, 196], [206], [292, 325], [1]],![[0, 290], [274], [182], [310], [11, 141], [206], [190, 12], [1]]]
 h' := ![![[177, 336], [28, 76], [147, 264], [181, 70], [279, 240], [251, 323], [87, 108], [43, 177], [0, 1]],![[0, 1], [0, 261], [32, 73], [102, 267], [297, 97], [132, 14], [331, 229], [31, 160], [177, 336]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [278]]
 b := ![[], [336, 139]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N0 : CertifiedPrimeIdeal' SI337N0 337 where 
  n := 2
  hpos := by decide  
  P := [294, 160, 1]
  hirr := P337P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![39904, 37805, 10964, 985]
  a := ![1, 1, -4, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-6714, -2832, 10964, 985]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI337N0 : Ideal.IsPrime I337N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N0 B_one_repr
lemma NI337N0 : Nat.card (O ⧸ I337N0) = 113569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N0

def I337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![337, 0, 0, 0], ![-203, -67, -4, 1]] i)))

def SI337N1: IdealEqSpanCertificate' Table ![![337, 0, 0, 0], ![-203, -67, -4, 1]] 
 ![![337, 0, 0, 0], ![0, 337, 0, 0], ![111, 265, 1, 0], ![241, 319, 0, 1]] where
  M :=![![![337, 0, 0, 0], ![0, 337, 0, 0], ![0, 0, 337, 0], ![0, 0, 0, 337]], ![![-203, -67, -4, 1], ![383, 129, 13, -3], ![-1149, -613, -111, 10], ![3830, 2171, 187, -101]]]
  hmulB := by decide  
  f := ![![![2337595, 793722, 92784, -21054], ![-1567050, -2887416, 0, 0]], ![![-13849, -4702, -551, 125], ![9436, 17187, 0, 0]], ![![759180, 257776, 30130, -6837], ![-508530, -937533, 0, 0]], ![![1658564, 563160, 65831, -14938], ![-1111750, -2048619, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-111, -265, 337, 0], ![-241, -319, 0, 337]], ![![0, 2, -4, 1], ![-1, -7, 13, -3], ![26, 76, -111, 10], ![22, -45, 187, -101]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P1 : CertificateIrreducibleZModOfList' 337 2 2 8 [245, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [299, 336], [0, 1]]
 g := ![![[256, 265], [173], [6], [173], [235, 158], [167], [144, 96], [1]],![[296, 72], [173], [6], [173], [297, 179], [167], [203, 241], [1]]]
 h' := ![![[299, 336], [79, 172], [26, 39], [85, 178], [52, 39], [103, 81], [105, 29], [92, 299], [0, 1]],![[0, 1], [283, 165], [229, 298], [61, 159], [255, 298], [58, 256], [14, 308], [188, 38], [299, 336]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [74, 199]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N1 : CertifiedPrimeIdeal' SI337N1 337 where 
  n := 2
  hpos := by decide  
  P := [245, 38, 1]
  hirr := P337P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![31546, 26873, 6580, 364]
  a := ![-3, 1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-2334, -5439, 6580, 364]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI337N1 : Ideal.IsPrime I337N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N1 B_one_repr
lemma NI337N1 : Nat.card (O ⧸ I337N1) = 113569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N1
def MulI337N0 : IdealMulLeCertificate' Table 
  ![![337, 0, 0, 0], ![-60, -67, -4, 1]] ![![337, 0, 0, 0], ![-203, -67, -4, 1]]
  ![![337, 0, 0, 0]] where
 M :=  ![![![113569, 0, 0, 0], ![-68411, -22579, -1348, 337]], ![![-20220, -22579, -1348, 337], ![-5055, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![337, 0, 0, 0]], ![![-203, -67, -4, 1]]], ![![![-60, -67, -4, 1]], ![![-15, 0, 0, 0]]]]
 hle2 := by decide  


def PBC337 : ContainsPrimesAboveP 337 ![I337N0, I337N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI337N0
    exact isPrimeI337N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 337 (by decide) (𝕀 ⊙ MulI337N0)
instance hp347 : Fact (Nat.Prime 347) := {out := by norm_num}

def I347N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-287, -134, -8, 2]] i)))

def SI347N0: IdealEqSpanCertificate' Table ![![-287, -134, -8, 2]] 
 ![![347, 0, 0, 0], ![0, 347, 0, 0], ![126, 161, 1, 0], ![187, 230, 0, 1]] where
  M :=![![![-287, -134, -8, 2], ![766, 377, 26, -6], ![-2298, -1226, -103, 20], ![7660, 4342, 374, -83]]]
  hmulB := by decide  
  f := ![![![239, 134, 8, -2]], ![![-766, -425, -26, 6]], ![![-262, -145, -9, 2]], ![![-401, -222, -14, 3]]]
  g := ![![![1, 2, -8, 2], ![-4, -7, 26, -6], ![20, 31, -103, 20], ![-69, -106, 374, -83]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P0 : CertificateIrreducibleZModOfList' 347 2 2 8 [276, 247, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 346], [0, 1]]
 g := ![![[236, 325], [122, 85], [269], [135, 64], [139, 40], [341], [266, 284], [1]],![[118, 22], [294, 262], [269], [289, 283], [322, 307], [341], [212, 63], [1]]]
 h' := ![![[100, 346], [334, 280], [172, 248], [216, 160], [153, 339], [311, 97], [148, 102], [71, 100], [0, 1]],![[0, 1], [227, 67], [335, 99], [254, 187], [47, 8], [295, 250], [285, 245], [8, 247], [100, 346]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [325]]
 b := ![[], [203, 336]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N0 : CertifiedPrimeIdeal' SI347N0 347 where 
  n := 2
  hpos := by decide  
  P := [276, 247, 1]
  hirr := P347P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![494713, 412628, 97739, 2389]
  a := ![3, 0, 7, -4]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-35352, -45743, 97739, 2389]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI347N0 : Ideal.IsPrime I347N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N0 B_one_repr
lemma NI347N0 : Nat.card (O ⧸ I347N0) = 120409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N0

def I347N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, 9, -1, 0]] i)))

def SI347N1: IdealEqSpanCertificate' Table ![![24, 9, -1, 0]] 
 ![![347, 0, 0, 0], ![87, 1, 0, 0], ![65, 0, 1, 0], ![244, 0, 0, 1]] where
  M :=![![![24, 9, -1, 0], ![0, 24, 9, -1], ![-383, -332, -56, 8], ![3064, 2273, 308, -48]]]
  hmulB := by decide  
  f := ![![![-576, -232, -5, 4]], ![![-140, -56, -1, 1]], ![![-109, -40, 1, 1]], ![![-309, -81, 20, 5]]]
  g := ![![![-2, 9, -1, 0], ![-7, 24, 9, -1], ![87, -332, -56, 8], ![-585, 2273, 308, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI347N1 : Nat.card (O ⧸ I347N1) = 347 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI347N1)

lemma isPrimeI347N1 : Ideal.IsPrime I347N1 := prime_ideal_of_norm_prime hp347.out _ NI347N1

def I347N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![488, 217, 10, -3]] i)))

def SI347N2: IdealEqSpanCertificate' Table ![![488, 217, 10, -3]] 
 ![![347, 0, 0, 0], ![98, 1, 0, 0], ![112, 0, 1, 0], ![128, 0, 0, 1]] where
  M :=![![![488, 217, 10, -3], ![-1149, -508, -23, 7], ![2681, 1175, 52, -16], ![-6128, -2631, -105, 36]]]
  hmulB := by decide  
  f := ![![![-1215, -687, -48, 11]], ![![-331, -187, -13, 3]], ![![-433, -245, -17, 4]], ![![-276, -145, -5, 3]]]
  g := ![![![-62, 217, 10, -3], ![145, -508, -23, 7], ![-335, 1175, 52, -16], ![746, -2631, -105, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI347N2 : Nat.card (O ⧸ I347N2) = 347 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI347N2)

lemma isPrimeI347N2 : Ideal.IsPrime I347N2 := prime_ideal_of_norm_prime hp347.out _ NI347N2
def MulI347N0 : IdealMulLeCertificate' Table 
  ![![-287, -134, -8, 2]] ![![24, 9, -1, 0]]
  ![![2304, 1403, 145, -26]] where
 M :=  ![![![2304, 1403, 145, -26]]]
 hmul := by decide  
 g :=  ![![![![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI347N1 : IdealMulLeCertificate' Table 
  ![![2304, 1403, 145, -26]] ![![488, 217, 10, -3]]
  ![![347, 0, 0, 0]] where
 M :=  ![![![60378, 26025, 1041, -347]]]
 hmul := by decide  
 g :=  ![![![![174, 75, 3, -1]]]]
 hle2 := by decide  


def PBC347 : ContainsPrimesAboveP 347 ![I347N0, I347N1, I347N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI347N0
    exact isPrimeI347N1
    exact isPrimeI347N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 347 (by decide) (𝕀 ⊙ MulI347N0 ⊙ MulI347N1)
instance hp349 : Fact (Nat.Prime 349) := {out := by norm_num}

def I349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![349, 0, 0, 0]] i)))

def SI349N0: IdealEqSpanCertificate' Table ![![349, 0, 0, 0]] 
 ![![349, 0, 0, 0], ![0, 349, 0, 0], ![0, 0, 349, 0], ![0, 0, 0, 349]] where
  M :=![![![349, 0, 0, 0], ![0, 349, 0, 0], ![0, 0, 349, 0], ![0, 0, 0, 349]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P0 : CertificateIrreducibleZModOfList' 349 4 2 8 [343, 319, 68, 28, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [332, 226, 300, 330], [182, 316, 126, 170], [156, 155, 272, 198], [0, 1]]
 g := ![![[288, 284, 247, 147], [245, 300, 17], [339, 312, 315, 73], [288, 198, 251, 118], [97, 145, 221, 94], [54, 175, 324], [321, 1], []],![[73, 186, 214, 186, 28, 261], [339, 202, 204], [176, 228, 90, 290, 338, 263], [19, 156, 16, 78, 199, 139], [211, 170, 25, 328, 106, 66], [181, 76, 69], [250, 288, 252, 91, 338, 194], [176, 130, 12]],![[206, 105, 228, 121, 298, 39], [225, 161, 94], [216, 255, 199, 97, 258, 7], [108, 228, 65, 156, 215, 59], [24, 199, 329, 35, 5, 84], [53, 111, 280], [86, 237, 225, 332, 266, 229], [302, 44, 282]],![[64, 326, 94, 67, 290, 111], [237, 127, 67], [190, 65, 319, 64, 195, 180], [38, 119, 182, 307, 338, 268], [316, 331, 317, 264, 347, 204], [36, 54, 77], [113, 333, 158, 9, 120, 320], [68, 113, 116]]]
 h' := ![![[332, 226, 300, 330], [184, 116, 185, 241], [289, 116, 289, 296], [332, 250, 47, 259], [233, 304, 185, 269], [279, 204, 45, 276], [181, 213, 189, 18], [0, 0, 1], [0, 1]],![[182, 316, 126, 170], [132, 123, 89, 185], [76, 291, 135, 40], [181, 267, 161, 232], [168, 102, 181, 51], [165, 278, 188, 197], [210, 329, 157, 162], [298, 121, 74, 339], [332, 226, 300, 330]],![[156, 155, 272, 198], [236, 72, 209, 69], [170, 35, 98, 276], [343, 25, 288, 265], [273, 120, 65, 96], [281, 195, 238, 200], [115, 293, 218, 304], [36, 104, 113, 320], [182, 316, 126, 170]],![[0, 1], [148, 38, 215, 203], [226, 256, 176, 86], [111, 156, 202, 291], [297, 172, 267, 282], [135, 21, 227, 25], [177, 212, 134, 214], [314, 124, 161, 39], [156, 155, 272, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [308, 227, 297], []]
 b := ![[], [], [200, 203, 334, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N0 : CertifiedPrimeIdeal' SI349N0 349 where 
  n := 4
  hpos := by decide  
  P := [343, 319, 68, 28, 1]
  hirr := P349P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![27010177591, 25739937647, 7887619172, 771618409]
  a := ![0, 1, 1, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![77393059, 73753403, 22600628, 2210941]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI349N0 : Ideal.IsPrime I349N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N0 B_one_repr
lemma NI349N0 : Nat.card (O ⧸ I349N0) = 14835483601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N0

def PBC349 : ContainsPrimesAboveP 349 ![I349N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI349N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![349, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 349 (by decide) 𝕀



lemma PB692I6_primes (p : ℕ) :
  p ∈ Set.range ![283, 293, 307, 311, 313, 317, 331, 337, 347, 349] ↔ Nat.Prime p ∧ 281 < p ∧ p ≤ 349 := by
  rw [← List.mem_ofFn']
  convert primes_range 281 349 (by omega)
  rfl

def PB692I6 : PrimesBelowBoundCertificateInterval' O 281 349 692 where
  m := 10
  g := ![1, 2, 3, 4, 2, 1, 1, 2, 3, 1]
  P := ![283, 293, 307, 311, 313, 317, 331, 337, 347, 349]
  hP := PB692I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I283N0]
    · exact ![I293N0, I293N1]
    · exact ![I307N0, I307N1, I307N2]
    · exact ![I311N0, I311N1, I311N2, I311N3]
    · exact ![I313N0, I313N1]
    · exact ![I317N0]
    · exact ![I331N0]
    · exact ![I337N0, I337N1]
    · exact ![I347N0, I347N1, I347N2]
    · exact ![I349N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC283
    · exact PBC293
    · exact PBC307
    · exact PBC311
    · exact PBC313
    · exact PBC317
    · exact PBC331
    · exact PBC337
    · exact PBC347
    · exact PBC349
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6414247921]
    · exact ![85849, 85849]
    · exact ![94249, 307, 307]
    · exact ![311, 311, 311, 311]
    · exact ![97969, 97969]
    · exact ![10098039121]
    · exact ![12003612721]
    · exact ![113569, 113569]
    · exact ![120409, 347, 347]
    · exact ![14835483601]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI283N0
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
      exact NI307N2
    · dsimp ; intro j
      fin_cases j
      exact NI311N0
      exact NI311N1
      exact NI311N2
      exact NI311N3
    · dsimp ; intro j
      fin_cases j
      exact NI313N0
      exact NI313N1
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
    · dsimp ; intro j
      fin_cases j
      exact NI331N0
    · dsimp ; intro j
      fin_cases j
      exact NI337N0
      exact NI337N1
    · dsimp ; intro j
      fin_cases j
      exact NI347N0
      exact NI347N1
      exact NI347N2
    · dsimp ; intro j
      fin_cases j
      exact NI349N0
  Il := ![[], [], [I307N1, I307N2], [I311N0, I311N1, I311N2, I311N3], [], [], [], [], [I347N1, I347N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
