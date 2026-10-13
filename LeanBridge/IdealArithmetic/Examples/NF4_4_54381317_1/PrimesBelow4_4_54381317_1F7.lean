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
instance hp353 : Fact (Nat.Prime 353) := {out := by norm_num}

def I353N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![353, 0, 0, 0], ![-52, -35, -4, 1]] i)))

def SI353N0: IdealEqSpanCertificate' Table ![![353, 0, 0, 0], ![-52, -35, -4, 1]] 
 ![![353, 0, 0, 0], ![0, 353, 0, 0], ![285, 16, 1, 0], ![29, 29, 0, 1]] where
  M :=![![![353, 0, 0, 0], ![0, 353, 0, 0], ![0, 0, 353, 0], ![0, 0, 0, 353]], ![![-52, -35, -4, 1], ![383, 280, 45, -3], ![-1149, -613, 40, 42], ![16086, 12795, 2747, 82]]]
  hmulB := by decide  
  f := ![![![28975225, 21237720, 3442728, -216192], ![-6413304, -27576360, 0, 0]], ![![-103808, -76089, -12336, 774], ![23298, 98840, 0, 0]], ![![23388897, 17143157, 2778981, -174511], ![-5176777, -22259720, 0, 0]], ![![2371913, 1738518, 281820, -17698], ![-524685, -2257360, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-285, -16, 353, 0], ![-29, -29, 0, 353]], ![![3, 0, -4, 1], ![-35, -1, 45, -3], ![-39, -7, 40, 42], ![-2179, -95, 2747, 82]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P0 : CertificateIrreducibleZModOfList' 353 2 2 8 [52, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [277, 352], [0, 1]]
 g := ![![[273, 76], [311], [244], [30], [280], [39, 271], [294, 128], [1]],![[145, 277], [311], [244], [30], [280], [270, 82], [97, 225], [1]]]
 h' := ![![[277, 352], [288, 206], [218, 283], [145, 127], [247, 320], [90, 120], [244, 179], [301, 277], [0, 1]],![[0, 1], [164, 147], [243, 70], [24, 226], [284, 33], [148, 233], [54, 174], [76, 76], [277, 352]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [301, 203]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N0 : CertifiedPrimeIdeal' SI353N0 353 where 
  n := 2
  hpos := by decide  
  P := [52, 76, 1]
  hirr := P353P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![32990, 29625, 8184, 584]
  a := ![0, -1, -1, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-6562, -335, 8184, 584]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI353N0 : Ideal.IsPrime I353N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N0 B_one_repr
lemma NI353N0 : Nat.card (O ⧸ I353N0) = 124609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N0

def I353N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![353, 0, 0, 0], ![-150, 39, -4, 1]] i)))

def SI353N1: IdealEqSpanCertificate' Table ![![353, 0, 0, 0], ![-150, 39, -4, 1]] 
 ![![353, 0, 0, 0], ![0, 353, 0, 0], ![260, 336, 1, 0], ![184, 324, 0, 1]] where
  M :=![![![353, 0, 0, 0], ![0, 353, 0, 0], ![0, 0, 353, 0], ![0, 0, 0, 353]], ![![-150, 39, -4, 1], ![383, 182, 119, -3], ![-1149, -613, -58, 116], ![44428, 37363, 8667, 58]]]
  hmulB := by decide  
  f := ![![![785595, 462527, 278556, -6295], ![-285577, -835904, 0, 0]], ![![-5228, -3145, -1880, 42], ![2118, 5648, 0, 0]], ![![573564, 337700, 203377, -4596], ![-208524, -610304, 0, 0]], ![![404586, 238231, 143468, -3242], ![-147157, -430528, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-260, -336, 353, 0], ![-184, -324, 0, 353]], ![![2, 3, -4, 1], ![-85, -110, 119, -3], ![-21, -53, -58, 116], ![-6288, -8197, 8667, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P1 : CertificateIrreducibleZModOfList' 353 2 2 8 [2, 223, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 352], [0, 1]]
 g := ![![[288, 177], [314], [78], [317], [164], [228, 336], [114, 309], [1]],![[0, 176], [314], [78], [317], [164], [136, 17], [42, 44], [1]]]
 h' := ![![[130, 352], [265, 93], [295, 62], [243, 325], [44, 101], [250, 115], [125, 86], [351, 130], [0, 1]],![[0, 1], [0, 260], [236, 291], [133, 28], [113, 252], [21, 238], [9, 267], [307, 223], [130, 352]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [163]]
 b := ![[], [174, 258]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N1 : CertifiedPrimeIdeal' SI353N1 353 where 
  n := 2
  hpos := by decide  
  P := [2, 223, 1]
  hirr := P353P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![1552625, 1298276, 268612, -5938]
  a := ![-2, 3, -64, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-190351, -246548, 268612, -5938]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI353N1 : Ideal.IsPrime I353N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N1 B_one_repr
lemma NI353N1 : Nat.card (O ⧸ I353N1) = 124609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N1
def MulI353N0 : IdealMulLeCertificate' Table 
  ![![353, 0, 0, 0], ![-52, -35, -4, 1]] ![![353, 0, 0, 0], ![-150, 39, -4, 1]]
  ![![353, 0, 0, 0]] where
 M :=  ![![![124609, 0, 0, 0], ![-52950, 13767, -1412, 353]], ![![-18356, -12355, -1412, 353], ![43419, 31417, 4942, -353]]]
 hmul := by decide  
 g :=  ![![![![353, 0, 0, 0]], ![![-150, 39, -4, 1]]], ![![![-52, -35, -4, 1]], ![![123, 89, 14, -1]]]]
 hle2 := by decide  


def PBC353 : ContainsPrimesAboveP 353 ![I353N0, I353N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI353N0
    exact isPrimeI353N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 353 (by decide) (𝕀 ⊙ MulI353N0)
instance hp359 : Fact (Nat.Prime 359) := {out := by norm_num}

def I359N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-407, -201, -12, 3]] i)))

def SI359N0: IdealEqSpanCertificate' Table ![![-407, -201, -12, 3]] 
 ![![359, 0, 0, 0], ![0, 359, 0, 0], ![335, 115, 1, 0], ![247, 34, 0, 1]] where
  M :=![![![-407, -201, -12, 3], ![1149, 589, 39, -9], ![-3447, -1839, -131, 30], ![11490, 6513, 561, -101]]]
  hmulB := by decide  
  f := ![![![-382, -201, -12, 3]], ![![1149, 614, 39, -9]], ![![2, 4, 1, 0]], ![![-122, -62, -3, 1]]]
  g := ![![![8, 3, -12, 3], ![-27, -10, 39, -9], ![92, 34, -131, 30], ![-422, -152, 561, -101]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P0 : CertificateIrreducibleZModOfList' 359 2 2 8 [33, 323, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 358], [0, 1]]
 g := ![![[260, 272], [80, 264], [243, 204], [219], [316], [152, 45], [123, 219], [1]],![[0, 87], [250, 95], [48, 155], [219], [316], [336, 314], [109, 140], [1]]]
 h' := ![![[36, 358], [232, 193], [238, 303], [21, 113], [83, 323], [10, 291], [249, 85], [326, 36], [0, 1]],![[0, 1], [0, 166], [17, 56], [140, 246], [223, 36], [75, 68], [78, 274], [186, 323], [36, 358]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132]]
 b := ![[], [248, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N0 : CertifiedPrimeIdeal' SI359N0 359 where 
  n := 2
  hpos := by decide  
  P := [33, 323, 1]
  hirr := P359P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![274705, 239846, 62205, 2985]
  a := ![-1, 1, 1, -3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-59335, -19541, 62205, 2985]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI359N0 : Ideal.IsPrime I359N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N0 B_one_repr
lemma NI359N0 : Nat.card (O ⧸ I359N0) = 128881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N0

def I359N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-103, -59, -5, 1]] i)))

def SI359N1: IdealEqSpanCertificate' Table ![![-103, -59, -5, 1]] 
 ![![359, 0, 0, 0], ![115, 1, 0, 0], ![58, 0, 1, 0], ![151, 0, 0, 1]] where
  M :=![![![-103, -59, -5, 1], ![383, 229, 21, -4], ![-1532, -945, -91, 17], ![6511, 4112, 415, -74]]]
  hmulB := by decide  
  f := ![![![-2123, -1086, -61, 16]], ![![-663, -339, -19, 5]], ![![-391, -200, -11, 3]], ![![-734, -367, -17, 6]]]
  g := ![![![19, -59, -5, 1], ![-74, 229, 21, -4], ![306, -945, -91, 17], ![-1335, 4112, 415, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI359N1 : Nat.card (O ⧸ I359N1) = 359 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI359N1)

lemma isPrimeI359N1 : Ideal.IsPrime I359N1 := prime_ideal_of_norm_prime hp359.out _ NI359N1

def I359N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![311, 142, 7, -2]] i)))

def SI359N2: IdealEqSpanCertificate' Table ![![311, 142, 7, -2]] 
 ![![359, 0, 0, 0], ![128, 1, 0, 0], ![130, 0, 1, 0], ![233, 0, 0, 1]] where
  M :=![![![311, 142, 7, -2], ![-766, -353, -18, 5], ![1915, 894, 47, -13], ![-4979, -2401, -146, 34]]]
  hmulB := by decide  
  f := ![![![2809, 1527, 95, -23]], ![![977, 531, 33, -8]], ![![1094, 595, 37, -9]], ![![1566, 845, 50, -13]]]
  g := ![![![-51, 142, 7, -2], ![127, -353, -18, 5], ![-322, 894, 47, -13], ![873, -2401, -146, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI359N2 : Nat.card (O ⧸ I359N2) = 359 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI359N2)

lemma isPrimeI359N2 : Ideal.IsPrime I359N2 := prime_ideal_of_norm_prime hp359.out _ NI359N2
def MulI359N0 : IdealMulLeCertificate' Table 
  ![![-407, -201, -12, 3]] ![![-103, -59, -5, 1]]
  ![![2855, 1660, 151, -29]] where
 M :=  ![![![2855, 1660, 151, -29]]]
 hmul := by decide  
 g :=  ![![![![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI359N1 : IdealMulLeCertificate' Table 
  ![![2855, 1660, 151, -29]] ![![311, 142, 7, -2]]
  ![![359, 0, 0, 0]] where
 M :=  ![![![49901, 24053, 1436, -359]]]
 hmul := by decide  
 g :=  ![![![![139, 67, 4, -1]]]]
 hle2 := by decide  


def PBC359 : ContainsPrimesAboveP 359 ![I359N0, I359N1, I359N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI359N0
    exact isPrimeI359N1
    exact isPrimeI359N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 359 (by decide) (𝕀 ⊙ MulI359N0 ⊙ MulI359N1)
instance hp367 : Fact (Nat.Prime 367) := {out := by norm_num}

def I367N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![367, 0, 0, 0], ![-88, -67, -4, 1]] i)))

def SI367N0: IdealEqSpanCertificate' Table ![![367, 0, 0, 0], ![-88, -67, -4, 1]] 
 ![![367, 0, 0, 0], ![0, 367, 0, 0], ![119, 43, 1, 0], ![21, 105, 0, 1]] where
  M :=![![![367, 0, 0, 0], ![0, 367, 0, 0], ![0, 0, 367, 0], ![0, 0, 0, 367]], ![![-88, -67, -4, 1], ![383, 244, 13, -3], ![-1149, -613, 4, 10], ![3830, 2171, 187, 14]]]
  hmulB := by decide  
  f := ![![![2711057, 1698514, 89368, -20422], ![-960806, -2818560, 0, 0]], ![![-33864, -21212, -1116, 255], ![12111, 35232, 0, 0]], ![![875097, 548261, 28847, -6592], ![-310112, -909792, 0, 0]], ![![145475, 91148, 4796, -1096], ![-51367, -151200, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-119, -43, 367, 0], ![-21, -105, 0, 367]], ![![1, 0, -4, 1], ![-3, 0, 13, -3], ![-5, -5, 4, 10], ![-51, -20, 187, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P367P0 : CertificateIrreducibleZModOfList' 367 2 2 8 [185, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [336, 366], [0, 1]]
 g := ![![[143, 128], [290, 9], [104, 188], [282, 121], [9], [11, 237], [29, 227], [1]],![[212, 239], [11, 358], [148, 179], [201, 246], [9], [4, 130], [332, 140], [1]]]
 h' := ![![[336, 366], [299, 102], [211, 364], [311, 65], [167, 356], [167, 3], [140, 139], [182, 336], [0, 1]],![[0, 1], [73, 265], [304, 3], [131, 302], [141, 11], [74, 364], [235, 228], [42, 31], [336, 366]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [362]]
 b := ![[], [53, 181]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI367N0 : CertifiedPrimeIdeal' SI367N0 367 where 
  n := 2
  hpos := by decide  
  P := [185, 31, 1]
  hirr := P367P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![30059, 25482, 6261, 363]
  a := ![0, -1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-1969, -768, 6261, 363]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI367N0 : Ideal.IsPrime I367N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI367N0 B_one_repr
lemma NI367N0 : Nat.card (O ⧸ I367N0) = 134689 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI367N0

def I367N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![367, 0, 0, 0], ![77, 1, 0, 0]] i)))

def SI367N1: IdealEqSpanCertificate' Table ![![367, 0, 0, 0], ![77, 1, 0, 0]] 
 ![![367, 0, 0, 0], ![77, 1, 0, 0], ![310, 0, 1, 0], ![352, 0, 0, 1]] where
  M :=![![![367, 0, 0, 0], ![0, 367, 0, 0], ![0, 0, 367, 0], ![0, 0, 0, 367]], ![![77, 1, 0, 0], ![0, 77, 1, 0], ![0, 0, 77, 1], ![383, 332, 80, 78]]]
  hmulB := by decide  
  f := ![![![9164, -497, 1134125, 14729], ![-43673, 2936, -5405543, 0]], ![![1848, -130, 242240, 3146], ![-8807, 734, -1154582, 0]], ![![7794, -438, 957950, 12441], ![-37144, 2570, -4565847, 0]], ![![8844, -485, 1087771, 14127], ![-42148, 2859, -5184608, 0]]]
  g := ![![![1, 0, 0, 0], ![-77, 367, 0, 0], ![-310, 0, 367, 0], ![-352, 0, 0, 367]], ![![0, 1, 0, 0], ![-17, 77, 1, 0], ![-66, 0, 77, 1], ![-211, 332, 80, 78]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI367N1 : Nat.card (O ⧸ I367N1) = 367 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI367N1)

lemma isPrimeI367N1 : Ideal.IsPrime I367N1 := prime_ideal_of_norm_prime hp367.out _ NI367N1

def I367N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![367, 0, 0, 0], ![-121, 1, 0, 0]] i)))

def SI367N2: IdealEqSpanCertificate' Table ![![367, 0, 0, 0], ![-121, 1, 0, 0]] 
 ![![367, 0, 0, 0], ![246, 1, 0, 0], ![39, 0, 1, 0], ![315, 0, 0, 1]] where
  M :=![![![367, 0, 0, 0], ![0, 367, 0, 0], ![0, 0, 367, 0], ![0, 0, 0, 367]], ![![-121, 1, 0, 0], ![0, -121, 1, 0], ![0, 0, -121, 1], ![383, 332, 80, -120]]]
  hmulB := by decide  
  f := ![![![16094, 1319, 1761748, -14560], ![48811, 4404, 5343520, 0]], ![![10770, 879, 1189180, -9828], ![32664, 2936, 3606876, 0]], ![![1734, 228, 187185, -1547], ![5259, 735, 567749, 0]], ![![13782, 1136, 1512127, -12497], ![41799, 3791, 4586400, 0]]]
  g := ![![![1, 0, 0, 0], ![-246, 367, 0, 0], ![-39, 0, 367, 0], ![-315, 0, 0, 367]], ![![-1, 1, 0, 0], ![81, -121, 1, 0], ![12, 0, -121, 1], ![-127, 332, 80, -120]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI367N2 : Nat.card (O ⧸ I367N2) = 367 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI367N2)

lemma isPrimeI367N2 : Ideal.IsPrime I367N2 := prime_ideal_of_norm_prime hp367.out _ NI367N2
def MulI367N0 : IdealMulLeCertificate' Table 
  ![![367, 0, 0, 0], ![-88, -67, -4, 1]] ![![367, 0, 0, 0], ![77, 1, 0, 0]]
  ![![367, 0, 0, 0], ![-9696, -4915, -295, 74]] where
 M :=  ![![![134689, 0, 0, 0], ![28259, 367, 0, 0]], ![![-32296, -24589, -1468, 367], ![-6393, -4915, -295, 74]]]
 hmul := by decide  
 g :=  ![![![![367, 0, 0, 0], ![0, 0, 0, 0]], ![![77, 1, 0, 0], ![0, 0, 0, 0]]], ![![![9608, 4848, 291, -73], ![367, 0, 0, 0]], ![![9, 0, 0, 0], ![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI367N1 : IdealMulLeCertificate' Table 
  ![![367, 0, 0, 0], ![-9696, -4915, -295, 74]] ![![367, 0, 0, 0], ![-121, 1, 0, 0]]
  ![![367, 0, 0, 0]] where
 M :=  ![![![134689, 0, 0, 0], ![-44407, 367, 0, 0]], ![![-3558432, -1803805, -108265, 27158], ![1201558, 609587, 36700, -9175]]]
 hmul := by decide  
 g :=  ![![![![367, 0, 0, 0]], ![![-121, 1, 0, 0]]], ![![![-9696, -4915, -295, 74]], ![![3274, 1661, 100, -25]]]]
 hle2 := by decide  


def PBC367 : ContainsPrimesAboveP 367 ![I367N0, I367N1, I367N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI367N0
    exact isPrimeI367N1
    exact isPrimeI367N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 367 (by decide) (𝕀 ⊙ MulI367N0 ⊙ MulI367N1)
instance hp373 : Fact (Nat.Prime 373) := {out := by norm_num}

def I373N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![373, 0, 0, 0], ![-67, -67, -4, 1]] i)))

def SI373N0: IdealEqSpanCertificate' Table ![![373, 0, 0, 0], ![-67, -67, -4, 1]] 
 ![![373, 0, 0, 0], ![0, 373, 0, 0], ![182, 64, 1, 0], ![288, 189, 0, 1]] where
  M :=![![![373, 0, 0, 0], ![0, 373, 0, 0], ![0, 0, 373, 0], ![0, 0, 0, 373]], ![![-67, -67, -4, 1], ![383, 265, 13, -3], ![-1149, -613, 25, 10], ![3830, 2171, 187, 35]]]
  hmulB := by decide  
  f := ![![![-35590, -24027, -1158, 265], ![10817, 36554, 0, 0]], ![![35658, 24095, 1162, -266], ![-10444, -36554, 0, 0]], ![![-11203, -7545, -363, 83], ![3733, 11564, 0, 0]], ![![-9423, -6354, -306, 70], ![2997, 9702, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-182, -64, 373, 0], ![-288, -189, 0, 373]], ![![1, 0, -4, 1], ![-3, 0, 13, -3], ![-23, -11, 25, 10], ![-108, -44, 187, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P373P0 : CertificateIrreducibleZModOfList' 373 2 2 8 [124, 157, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [216, 372], [0, 1]]
 g := ![![[275, 370], [148], [223, 307], [243], [143, 46], [77, 71], [126, 31], [1]],![[0, 3], [148], [141, 66], [243], [8, 327], [120, 302], [108, 342], [1]]]
 h' := ![![[216, 372], [187, 177], [323, 68], [198, 143], [172, 313], [150, 267], [42, 329], [249, 216], [0, 1]],![[0, 1], [0, 196], [91, 305], [127, 230], [267, 60], [7, 106], [236, 44], [280, 157], [216, 372]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146]]
 b := ![[], [322, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI373N0 : CertifiedPrimeIdeal' SI373N0 373 where 
  n := 2
  hpos := by decide  
  P := [124, 157, 1]
  hirr := P373P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![283058, 243704, 62649, 4541]
  a := ![19, 1, -1, 3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-33316, -12397, 62649, 4541]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI373N0 : Ideal.IsPrime I373N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI373N0 B_one_repr
lemma NI373N0 : Nat.card (O ⧸ I373N0) = 139129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI373N0

def I373N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![373, 0, 0, 0], ![147, 1, 0, 0]] i)))

def SI373N1: IdealEqSpanCertificate' Table ![![373, 0, 0, 0], ![147, 1, 0, 0]] 
 ![![373, 0, 0, 0], ![147, 1, 0, 0], ![25, 0, 1, 0], ![55, 0, 0, 1]] where
  M :=![![![373, 0, 0, 0], ![0, 373, 0, 0], ![0, 0, 373, 0], ![0, 0, 0, 373]], ![![147, 1, 0, 0], ![0, 147, 1, 0], ![0, 0, 147, 1], ![383, 332, 80, 148]]]
  hmulB := by decide  
  f := ![![![18670, -5165, 5789118, 39382], ![-47371, 13428, -14689486, 0]], ![![7350, -2155, 2297742, 15631], ![-18649, 5595, -5830363, 0]], ![![1234, -433, 387930, 2639], ![-3131, 1120, -984347, 0]], ![![2656, -806, 853623, 5807], ![-6739, 2091, -2166010, 0]]]
  g := ![![![1, 0, 0, 0], ![-147, 373, 0, 0], ![-25, 0, 373, 0], ![-55, 0, 0, 373]], ![![0, 1, 0, 0], ![-58, 147, 1, 0], ![-10, 0, 147, 1], ![-157, 332, 80, 148]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI373N1 : Nat.card (O ⧸ I373N1) = 373 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI373N1)

lemma isPrimeI373N1 : Ideal.IsPrime I373N1 := prime_ideal_of_norm_prime hp373.out _ NI373N1

def I373N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![373, 0, 0, 0], ![161, 1, 0, 0]] i)))

def SI373N2: IdealEqSpanCertificate' Table ![![373, 0, 0, 0], ![161, 1, 0, 0]] 
 ![![373, 0, 0, 0], ![161, 1, 0, 0], ![189, 0, 1, 0], ![157, 0, 0, 1]] where
  M :=![![![373, 0, 0, 0], ![0, 373, 0, 0], ![0, 0, 373, 0], ![0, 0, 0, 373]], ![![161, 1, 0, 0], ![0, 161, 1, 0], ![0, 0, 161, 1], ![383, 332, 80, 162]]]
  hmulB := by decide  
  f := ![![![20287, -2611, 2825533, 17550], ![-46998, 6341, -6546150, 0]], ![![8533, -1235, 1243234, 7722], ![-19768, 2984, -2880306, 0]], ![![10213, -1386, 1431603, 8892], ![-23660, 3358, -3316716, 0]], ![![8615, -1165, 1189299, 7387], ![-19958, 2823, -2755350, 0]]]
  g := ![![![1, 0, 0, 0], ![-161, 373, 0, 0], ![-189, 0, 373, 0], ![-157, 0, 0, 373]], ![![0, 1, 0, 0], ![-70, 161, 1, 0], ![-82, 0, 161, 1], ![-251, 332, 80, 162]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI373N2 : Nat.card (O ⧸ I373N2) = 373 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI373N2)

lemma isPrimeI373N2 : Ideal.IsPrime I373N2 := prime_ideal_of_norm_prime hp373.out _ NI373N2
def MulI373N0 : IdealMulLeCertificate' Table 
  ![![373, 0, 0, 0], ![-67, -67, -4, 1]] ![![373, 0, 0, 0], ![147, 1, 0, 0]]
  ![![373, 0, 0, 0], ![-18791, -9957, -575, 144]] where
 M :=  ![![![139129, 0, 0, 0], ![54831, 373, 0, 0]], ![![-24991, -24991, -1492, 373], ![-9466, -9584, -575, 144]]]
 hmul := by decide  
 g :=  ![![![![373, 0, 0, 0], ![0, 0, 0, 0]], ![![147, 1, 0, 0], ![0, 0, 0, 0]]], ![![![18724, 9890, 571, -143], ![373, 0, 0, 0]], ![![25, 1, 0, 0], ![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI373N1 : IdealMulLeCertificate' Table 
  ![![373, 0, 0, 0], ![-18791, -9957, -575, 144]] ![![373, 0, 0, 0], ![161, 1, 0, 0]]
  ![![373, 0, 0, 0]] where
 M :=  ![![![139129, 0, 0, 0], ![60053, 373, 0, 0]], ![![-7009043, -3713961, -214475, 53712], ![-2970199, -1574060, -91012, 22753]]]
 hmul := by decide  
 g :=  ![![![![373, 0, 0, 0]], ![![161, 1, 0, 0]]], ![![![-18791, -9957, -575, 144]], ![![-7963, -4220, -244, 61]]]]
 hle2 := by decide  


def PBC373 : ContainsPrimesAboveP 373 ![I373N0, I373N1, I373N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI373N0
    exact isPrimeI373N1
    exact isPrimeI373N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 373 (by decide) (𝕀 ⊙ MulI373N0 ⊙ MulI373N1)
instance hp379 : Fact (Nat.Prime 379) := {out := by norm_num}

def I379N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![379, 0, 0, 0]] i)))

def SI379N0: IdealEqSpanCertificate' Table ![![379, 0, 0, 0]] 
 ![![379, 0, 0, 0], ![0, 379, 0, 0], ![0, 0, 379, 0], ![0, 0, 0, 379]] where
  M :=![![![379, 0, 0, 0], ![0, 379, 0, 0], ![0, 0, 379, 0], ![0, 0, 0, 379]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P379P0 : CertificateIrreducibleZModOfList' 379 4 2 8 [75, 240, 202, 22, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 278, 188, 171], [188, 135, 79, 116], [144, 344, 112, 92], [0, 1]]
 g := ![![[126, 341, 108, 92], [96, 200, 75, 316], [209, 352, 45], [346, 45, 339, 23], [230, 332, 65, 81], [136, 366, 347, 313], [357, 1], []],![[304, 324, 76, 254, 353, 348], [121, 364, 99, 158, 319, 76], [372, 173, 80], [129, 164, 5, 286, 70, 9], [125, 327, 314, 6, 65, 142], [174, 269, 6, 224, 56, 26], [11, 129, 163, 36, 286, 368], [19, 106, 58]],![[167, 282, 92, 224, 184, 220], [285, 358, 23, 97, 259, 11], [115, 324, 103], [7, 195, 131, 50, 168, 74], [237, 228, 373, 232, 116, 69], [276, 335, 175, 205, 352, 7], [62, 86, 195, 130, 288, 147], [124, 103, 191]],![[300, 38, 371, 31, 255, 347], [291, 351, 318, 226, 151, 41], [41, 318, 149], [299, 26, 231, 150, 23, 171], [306, 312, 335, 294, 56, 58], [34, 243, 321, 18, 71, 6], [350, 96, 53, 212, 161, 217], [233, 23, 126]]]
 h' := ![![[25, 278, 188, 171], [1, 182, 324, 146], [91, 151, 282, 165], [201, 122, 77, 117], [184, 200, 377, 73], [33, 314, 250, 9], [134, 278, 35, 282], [0, 0, 1], [0, 1]],![[188, 135, 79, 116], [219, 276, 208, 166], [200, 148, 119, 127], [317, 302, 323, 223], [52, 318, 28, 78], [234, 18, 370, 22], [69, 216, 25, 349], [337, 253, 375, 12], [25, 278, 188, 171]],![[144, 344, 112, 92], [140, 167, 32, 252], [180, 191, 56, 149], [344, 225, 328, 257], [204, 83, 80, 291], [30, 346, 256, 331], [348, 125, 135, 6], [272, 10, 133, 120], [188, 135, 79, 116]],![[0, 1], [177, 133, 194, 194], [196, 268, 301, 317], [121, 109, 30, 161], [15, 157, 273, 316], [283, 80, 261, 17], [209, 139, 184, 121], [229, 116, 249, 247], [144, 344, 112, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [357, 5, 330], []]
 b := ![[], [], [289, 60, 50, 252], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI379N0 : CertifiedPrimeIdeal' SI379N0 379 where 
  n := 4
  hpos := by decide  
  P := [75, 240, 202, 22, 1]
  hirr := P379P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![792069490964, 757302021093, 233170637703, 22975269935]
  a := ![-1, 0, 1, 2]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![2089893116, 1998158367, 615225957, 60620765]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI379N0 : Ideal.IsPrime I379N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI379N0 B_one_repr
lemma NI379N0 : Nat.card (O ⧸ I379N0) = 20632736881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI379N0

def PBC379 : ContainsPrimesAboveP 379 ![I379N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI379N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![379, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 379 (by decide) 𝕀

instance hp383 : Fact (Nat.Prime 383) := {out := by norm_num}

def I383N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 0, 0]] i)))

def SI383N0: IdealEqSpanCertificate' Table ![![0, 1, 0, 0]] 
 ![![383, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]] where
  M :=![![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![383, 332, 80, 1]]]
  hmulB := by decide  
  f := ![![![-332, -80, -1, 1]], ![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]]]
  g := ![![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![1, 332, 80, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI383N0 : Nat.card (O ⧸ I383N0) = 383 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI383N0)

lemma isPrimeI383N0 : Ideal.IsPrime I383N0 := prime_ideal_of_norm_prime hp383.out _ NI383N0

def I383N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![406, 201, 12, -3]] i)))

def SI383N1: IdealEqSpanCertificate' Table ![![406, 201, 12, -3]] 
 ![![383, 0, 0, 0], ![0, 383, 0, 0], ![360, 251, 1, 0], ![28, 171, 0, 1]] where
  M :=![![![406, 201, 12, -3], ![-1149, -590, -39, 9], ![3447, 1839, 130, -30], ![-11490, -6513, -561, 100]]]
  hmulB := by decide  
  f := ![![![383, 201, 12, -3]], ![![-1149, -613, -39, 9]], ![![-384, -208, -14, 3]], ![![-515, -276, -18, 4]]]
  g := ![![![-10, -6, 12, -3], ![33, 20, -39, 9], ![-111, -67, 130, -30], ![490, 306, -561, 100]]]
  hle1 := by decide   
  hle2 := by decide  


def P383P1 : CertificateIrreducibleZModOfList' 383 2 2 8 [308, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [311, 382], [0, 1]]
 g := ![![[45, 14], [86, 124], [201, 219], [241, 121], [213, 119], [333, 153], [101, 205], [1]],![[186, 369], [350, 259], [136, 164], [338, 262], [71, 264], [41, 230], [278, 178], [1]]]
 h' := ![![[311, 382], [322, 321], [138, 152], [74, 214], [272, 372], [80, 86], [298, 323], [75, 311], [0, 1]],![[0, 1], [190, 62], [301, 231], [369, 169], [298, 11], [16, 297], [22, 60], [280, 72], [311, 382]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [226]]
 b := ![[], [238, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI383N1 : CertifiedPrimeIdeal' SI383N1 383 where 
  n := 2
  hpos := by decide  
  P := [308, 72, 1]
  hirr := P383P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![124065, 109100, 28780, 2096]
  a := ![-5, 0, 0, 2]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-26881, -19512, 28780, 2096]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI383N1 : Ideal.IsPrime I383N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI383N1 B_one_repr
lemma NI383N1 : Nat.card (O ⧸ I383N1) = 146689 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI383N1

def I383N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-131, -68, -4, 1]] i)))

def SI383N2: IdealEqSpanCertificate' Table ![![-131, -68, -4, 1]] 
 ![![383, 0, 0, 0], ![131, 1, 0, 0], ![74, 0, 1, 0], ![264, 0, 0, 1]] where
  M :=![![![-131, -68, -4, 1], ![383, 201, 12, -3], ![-1149, -613, -39, 9], ![3447, 1839, 107, -30]]]
  hmulB := by decide  
  f := ![![![-1149, -590, -39, 9]], ![![-384, -197, -13, 3]], ![![-252, -131, -9, 2]], ![![-692, -350, -23, 5]]]
  g := ![![![23, -68, -4, 1], ![-68, 201, 12, -3], ![208, -613, -39, 9], ![-620, 1839, 107, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI383N2 : Nat.card (O ⧸ I383N2) = 383 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI383N2)

lemma isPrimeI383N2 : Ideal.IsPrime I383N2 := prime_ideal_of_norm_prime hp383.out _ NI383N2
def MulI383N0 : IdealMulLeCertificate' Table 
  ![![0, 1, 0, 0]] ![![406, 201, 12, -3]]
  ![![-1149, -590, -39, 9]] where
 M :=  ![![![-1149, -590, -39, 9]]]
 hmul := by decide  
 g :=  ![![![![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI383N1 : IdealMulLeCertificate' Table 
  ![![-1149, -590, -39, 9]] ![![-131, -68, -4, 1]]
  ![![383, 0, 0, 0]] where
 M :=  ![![![383, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![1, 0, 0, 0]]]]
 hle2 := by decide  


def PBC383 : ContainsPrimesAboveP 383 ![I383N0, I383N1, I383N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI383N0
    exact isPrimeI383N1
    exact isPrimeI383N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 383 (by decide) (𝕀 ⊙ MulI383N0 ⊙ MulI383N1)
instance hp389 : Fact (Nat.Prime 389) := {out := by norm_num}

def I389N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![389, 0, 0, 0]] i)))

def SI389N0: IdealEqSpanCertificate' Table ![![389, 0, 0, 0]] 
 ![![389, 0, 0, 0], ![0, 389, 0, 0], ![0, 0, 389, 0], ![0, 0, 0, 389]] where
  M :=![![![389, 0, 0, 0], ![0, 389, 0, 0], ![0, 0, 389, 0], ![0, 0, 0, 389]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P389P0 : CertificateIrreducibleZModOfList' 389 4 2 8 [185, 71, 303, 349, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [271, 237, 192, 52], [104, 137, 315, 239], [54, 14, 271, 98], [0, 1]]
 g := ![![[49, 277, 75, 223], [1, 38, 95], [90, 357, 294, 335], [252, 346, 141], [179, 300, 95], [294, 253, 121], [130, 40, 1], []],![[304, 34, 358, 249, 373, 223], [9, 280, 142], [65, 22, 306, 168, 43, 125], [123, 319, 127], [253, 255, 223], [99, 89, 340], [222, 37, 322], [205, 282, 388, 98, 106, 179]],![[58, 228, 343, 267, 375, 59], [138, 144, 304], [230, 275, 219, 311, 322, 78], [274, 7, 54], [324, 85, 337], [360, 92, 62], [8, 73, 42], [89, 89, 170, 31, 265, 353]],![[147, 206, 120, 321, 46, 185], [269, 71, 361], [262, 130, 349, 20, 79, 200], [249, 271, 210], [284, 321, 287], [139, 180, 309], [277, 27, 99], [24, 109, 29, 66, 304, 201]]]
 h' := ![![[271, 237, 192, 52], [298, 261, 155, 304], [77, 164, 109, 22], [213, 151, 360, 65], [237, 18, 21, 300], [26, 362, 221, 367], [68, 97, 375, 11], [0, 0, 0, 1], [0, 1]],![[104, 137, 315, 239], [310, 116, 127, 356], [315, 210, 72, 157], [180, 123, 177, 39], [71, 15, 283, 72], [14, 368, 337, 304], [128, 388, 243, 362], [301, 97, 247, 200], [271, 237, 192, 52]],![[54, 14, 271, 98], [71, 92, 118, 344], [263, 278, 105, 191], [355, 237, 69, 342], [53, 220, 184, 84], [288, 175, 83, 81], [59, 3, 293, 134], [138, 51, 294, 248], [104, 137, 315, 239]],![[0, 1], [69, 309, 378, 163], [248, 126, 103, 19], [237, 267, 172, 332], [369, 136, 290, 322], [86, 262, 137, 26], [317, 290, 256, 271], [147, 241, 237, 329], [54, 14, 271, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [372, 40, 6], []]
 b := ![[], [], [322, 346, 353, 249], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI389N0 : CertifiedPrimeIdeal' SI389N0 389 where 
  n := 4
  hpos := by decide  
  P := [185, 71, 303, 349, 1]
  hirr := P389P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![41617572283, 28019474722, 3191927441, -536438002]
  a := ![-10, 2, 13, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![106986047, 72029498, 8205469, -1379018]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI389N0 : Ideal.IsPrime I389N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI389N0 B_one_repr
lemma NI389N0 : Nat.card (O ⧸ I389N0) = 22898045041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI389N0

def PBC389 : ContainsPrimesAboveP 389 ![I389N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI389N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![389, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 389 (by decide) 𝕀

instance hp397 : Fact (Nat.Prime 397) := {out := by norm_num}

def I397N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![397, 0, 0, 0], ![-49, -67, -4, 1]] i)))

def SI397N0: IdealEqSpanCertificate' Table ![![397, 0, 0, 0], ![-49, -67, -4, 1]] 
 ![![397, 0, 0, 0], ![0, 397, 0, 0], ![236, 82, 1, 0], ![101, 261, 0, 1]] where
  M :=![![![397, 0, 0, 0], ![0, 397, 0, 0], ![0, 0, 397, 0], ![0, 0, 0, 397]], ![![-49, -67, -4, 1], ![383, 283, 13, -3], ![-1149, -613, 43, 10], ![3830, 2171, 187, 53]]]
  hmulB := by decide  
  f := ![![![19187366, 13812611, 623570, -142989], ![-4705641, -20490758, 0, 0]], ![![-146443, -105404, -4758, 1091], ![36127, 156418, 0, 0]], ![![11375860, 8189274, 369705, -84776], ![-2789716, -12148596, 0, 0]], ![![4785130, 3444724, 155512, -35660], ![-1173519, -5110180, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-236, -82, 397, 0], ![-101, -261, 0, 397]], ![![2, 0, -4, 1], ![-6, 0, 13, -3], ![-31, -17, 43, 10], ![-115, -68, 187, 53]]]
  hle1 := by decide   
  hle2 := by decide  


def P397P0 : CertificateIrreducibleZModOfList' 397 2 2 8 [87, 236, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [161, 396], [0, 1]]
 g := ![![[240, 324], [122], [185, 381], [125, 276], [111], [108], [47], [161, 1]],![[0, 73], [122], [388, 16], [97, 121], [111], [108], [47], [322, 396]]]
 h' := ![![[161, 396], [278, 18], [182, 330], [241, 252], [384, 101], [161, 184], [118, 277], [285, 29], [0, 1]],![[0, 1], [0, 379], [114, 67], [319, 145], [368, 296], [10, 213], [251, 120], [190, 368], [161, 396]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [90, 243]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI397N0 : CertifiedPrimeIdeal' SI397N0 397 where 
  n := 2
  hpos := by decide  
  P := [87, 236, 1]
  hirr := P397P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![39773, 37881, 10660, 909]
  a := ![1, 1, -4, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-6468, -2704, 10660, 909]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI397N0 : Ideal.IsPrime I397N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI397N0 B_one_repr
lemma NI397N0 : Nat.card (O ⧸ I397N0) = 157609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI397N0

def I397N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![397, 0, 0, 0], ![-214, -67, -4, 1]] i)))

def SI397N1: IdealEqSpanCertificate' Table ![![397, 0, 0, 0], ![-214, -67, -4, 1]] 
 ![![397, 0, 0, 0], ![0, 397, 0, 0], ![138, 314, 1, 0], ![338, 395, 0, 1]] where
  M :=![![![397, 0, 0, 0], ![0, 397, 0, 0], ![0, 0, 397, 0], ![0, 0, 0, 397]], ![![-214, -67, -4, 1], ![383, 118, 13, -3], ![-1149, -613, -122, 10], ![3830, 2171, 187, -112]]]
  hmulB := by decide  
  f := ![![![14363637, 4402509, 557346, -126973], ![-8491433, -19633238, 0, 0]], ![![-90775, -27821, -3525, 803], ![53992, 124261, 0, 0]], ![![4921192, 1508366, 190951, -43502], ![-2908816, -6726370, 0, 0]], ![![12138673, 3720551, 471009, -107304], ![-7175762, -16591817, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-138, -314, 397, 0], ![-338, -395, 0, 397]], ![![0, 2, -4, 1], ![-1, -7, 13, -3], ![31, 85, -122, 10], ![40, -31, 187, -112]]]
  hle1 := by decide   
  hle2 := by decide  


def P397P1 : CertificateIrreducibleZModOfList' 397 2 2 8 [298, 297, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [100, 396], [0, 1]]
 g := ![![[394, 4], [169], [65, 270], [213, 355], [226], [237], [104], [100, 1]],![[0, 393], [169], [69, 127], [380, 42], [226], [237], [104], [200, 396]]]
 h' := ![![[100, 396], [197, 2], [83, 13], [46, 238], [366, 281], [350, 267], [202, 112], [372, 174], [0, 1]],![[0, 1], [0, 395], [192, 384], [26, 159], [279, 116], [54, 130], [286, 285], [304, 223], [100, 396]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [236]]
 b := ![[], [55, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI397N1 : CertifiedPrimeIdeal' SI397N1 397 where 
  n := 2
  hpos := by decide  
  P := [298, 297, 1]
  hirr := P397P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![30822, 27132, 6321, 623]
  a := ![-3, 1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-2650, -5551, 6321, 623]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI397N1 : Ideal.IsPrime I397N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI397N1 B_one_repr
lemma NI397N1 : Nat.card (O ⧸ I397N1) = 157609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI397N1
def MulI397N0 : IdealMulLeCertificate' Table 
  ![![397, 0, 0, 0], ![-49, -67, -4, 1]] ![![397, 0, 0, 0], ![-214, -67, -4, 1]]
  ![![397, 0, 0, 0]] where
 M :=  ![![![157609, 0, 0, 0], ![-84958, -26599, -1588, 397]], ![![-19453, -26599, -1588, 397], ![-6749, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![397, 0, 0, 0]], ![![-214, -67, -4, 1]]], ![![![-49, -67, -4, 1]], ![![-17, 0, 0, 0]]]]
 hle2 := by decide  


def PBC397 : ContainsPrimesAboveP 397 ![I397N0, I397N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI397N0
    exact isPrimeI397N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 397 (by decide) (𝕀 ⊙ MulI397N0)
instance hp401 : Fact (Nat.Prime 401) := {out := by norm_num}

def I401N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![401, 0, 0, 0], ![39, 1, 0, 0]] i)))

def SI401N0: IdealEqSpanCertificate' Table ![![401, 0, 0, 0], ![39, 1, 0, 0]] 
 ![![401, 0, 0, 0], ![39, 1, 0, 0], ![83, 0, 1, 0], ![372, 0, 0, 1]] where
  M :=![![![401, 0, 0, 0], ![0, 401, 0, 0], ![0, 0, 401, 0], ![0, 0, 0, 401]], ![![39, 1, 0, 0], ![0, 39, 1, 0], ![0, 0, 39, 1], ![383, 332, 80, 40]]]
  hmulB := by decide  
  f := ![![![2653, 29, 81431, 2088], ![-27268, 401, -837288, 0]], ![![195, -34, 8423, 216], ![-2004, 401, -86616, 0]], ![![511, -26, 16847, 432], ![-5252, 402, -173232, 0]], ![![2466, 28, 75542, 1937], ![-25346, 362, -776736, 0]]]
  g := ![![![1, 0, 0, 0], ![-39, 401, 0, 0], ![-83, 0, 401, 0], ![-372, 0, 0, 401]], ![![0, 1, 0, 0], ![-4, 39, 1, 0], ![-9, 0, 39, 1], ![-85, 332, 80, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI401N0 : Nat.card (O ⧸ I401N0) = 401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI401N0)

lemma isPrimeI401N0 : Ideal.IsPrime I401N0 := prime_ideal_of_norm_prime hp401.out _ NI401N0

def I401N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![401, 0, 0, 0], ![172, 1, 0, 0]] i)))

def SI401N1: IdealEqSpanCertificate' Table ![![401, 0, 0, 0], ![172, 1, 0, 0]] 
 ![![401, 0, 0, 0], ![172, 1, 0, 0], ![90, 0, 1, 0], ![159, 0, 0, 1]] where
  M :=![![![401, 0, 0, 0], ![0, 401, 0, 0], ![0, 0, 401, 0], ![0, 0, 0, 401]], ![![172, 1, 0, 0], ![0, 172, 1, 0], ![0, 0, 172, 1], ![383, 332, 80, 173]]]
  hmulB := by decide  
  f := ![![![1893, -9449, -227, -1], ![-4411, 22055, 401, 0]], ![![516, -3953, -195, -1], ![-1202, 9223, 401, 0]], ![![246, -2235, -185, -1], ![-573, 5214, 401, 0]], ![![555, -3879, -195, -1], ![-1293, 9051, 402, 0]]]
  g := ![![![1, 0, 0, 0], ![-172, 401, 0, 0], ![-90, 0, 401, 0], ![-159, 0, 0, 401]], ![![0, 1, 0, 0], ![-74, 172, 1, 0], ![-39, 0, 172, 1], ![-228, 332, 80, 173]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI401N1 : Nat.card (O ⧸ I401N1) = 401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI401N1)

lemma isPrimeI401N1 : Ideal.IsPrime I401N1 := prime_ideal_of_norm_prime hp401.out _ NI401N1

def I401N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![401, 0, 0, 0], ![-137, 1, 0, 0]] i)))

def SI401N2: IdealEqSpanCertificate' Table ![![401, 0, 0, 0], ![-137, 1, 0, 0]] 
 ![![401, 0, 0, 0], ![264, 1, 0, 0], ![78, 0, 1, 0], ![260, 0, 0, 1]] where
  M :=![![![401, 0, 0, 0], ![0, 401, 0, 0], ![0, 0, 401, 0], ![0, 0, 0, 401]], ![![-137, 1, 0, 0], ![0, -137, 1, 0], ![0, 0, -137, 1], ![383, 332, 80, -136]]]
  hmulB := by decide  
  f := ![![![45622, 763, 1385884, -10116], ![133533, 3208, 4056516, 0]], ![![30004, 603, 923922, -6744], ![87820, 2406, 2704344, 0]], ![![8952, 209, 269477, -1967], ![26202, 803, 788767, 0]], ![![29566, 516, 898578, -6559], ![86538, 2142, 2630160, 0]]]
  g := ![![![1, 0, 0, 0], ![-264, 401, 0, 0], ![-78, 0, 401, 0], ![-260, 0, 0, 401]], ![![-1, 1, 0, 0], ![90, -137, 1, 0], ![26, 0, -137, 1], ![-145, 332, 80, -136]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI401N2 : Nat.card (O ⧸ I401N2) = 401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI401N2)

lemma isPrimeI401N2 : Ideal.IsPrime I401N2 := prime_ideal_of_norm_prime hp401.out _ NI401N2

def I401N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![401, 0, 0, 0], ![-75, 1, 0, 0]] i)))

def SI401N3: IdealEqSpanCertificate' Table ![![401, 0, 0, 0], ![-75, 1, 0, 0]] 
 ![![401, 0, 0, 0], ![326, 1, 0, 0], ![390, 0, 1, 0], ![378, 0, 0, 1]] where
  M :=![![![401, 0, 0, 0], ![0, 401, 0, 0], ![0, 0, 401, 0], ![0, 0, 0, 401]], ![![-75, 1, 0, 0], ![0, -75, 1, 0], ![0, 0, -75, 1], ![383, 332, 80, -74]]]
  hmulB := by decide  
  f := ![![![43126, -2726075, 37615, -17], ![230575, -14572340, 6817, 0]], ![![35101, -2216118, 30592, -14], ![187669, -11846342, 5614, 0]], ![![41865, -2651283, 36543, -16], ![223833, -14172542, 6416, 0]], ![![40653, -2569653, 35455, -16], ![217353, -13736180, 6417, 0]]]
  g := ![![![1, 0, 0, 0], ![-326, 401, 0, 0], ![-390, 0, 401, 0], ![-378, 0, 0, 401]], ![![-1, 1, 0, 0], ![60, -75, 1, 0], ![72, 0, -75, 1], ![-277, 332, 80, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI401N3 : Nat.card (O ⧸ I401N3) = 401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI401N3)

lemma isPrimeI401N3 : Ideal.IsPrime I401N3 := prime_ideal_of_norm_prime hp401.out _ NI401N3
def MulI401N0 : IdealMulLeCertificate' Table 
  ![![401, 0, 0, 0], ![39, 1, 0, 0]] ![![401, 0, 0, 0], ![172, 1, 0, 0]]
  ![![401, 0, 0, 0], ![-224, -161, -4, 1]] where
 M :=  ![![![160801, 0, 0, 0], ![68972, 401, 0, 0]], ![![15639, 401, 0, 0], ![6708, 211, 1, 0]]]
 hmul := by decide  
 g :=  ![![![![7411817861, 988255229, -2146046456, -66553489], ![-4515806563, -10401251884, 0, 0]], ![![3179074954, 423882156, -920481686, -28546105], ![-1936918621, -4461302242, 0, 0]]], ![![![720791329, 96106806, -208700690, -6472255], ![-439157155, -1011510470, 0, 0]], ![![309161646, 41222119, -89515845, -2776078], ![-188363140, -433856806, 0, 0]]]]
 hle2 := by decide  

def MulI401N1 : IdealMulLeCertificate' Table 
  ![![401, 0, 0, 0], ![-224, -161, -4, 1]] ![![401, 0, 0, 0], ![-137, 1, 0, 0]]
  ![![401, 0, 0, 0], ![-4564, -2377, -143, 36]] where
 M :=  ![![![160801, 0, 0, 0], ![-54937, 401, 0, 0]], ![![-89824, -64561, -1604, 401], ![31071, 22165, 467, -140]]]
 hmul := by decide  
 g :=  ![![![![401, 0, 0, 0], ![0, 0, 0, 0]], ![![4427, 2378, 143, -36], ![401, 0, 0, 0]]], ![![![4340, 2216, 139, -35], ![401, 0, 0, 0]], ![![3583, 1881, 111, -28], ![308, 0, 0, 0]]]]
 hle2 := by decide  

def MulI401N2 : IdealMulLeCertificate' Table 
  ![![401, 0, 0, 0], ![-4564, -2377, -143, 36]] ![![401, 0, 0, 0], ![-75, 1, 0, 0]]
  ![![401, 0, 0, 0]] where
 M :=  ![![![160801, 0, 0, 0], ![-30075, 401, 0, 0]], ![![-1830164, -953177, -57343, 14436], ![356088, 185663, 11228, -2807]]]
 hmul := by decide  
 g :=  ![![![![401, 0, 0, 0]], ![![-75, 1, 0, 0]]], ![![![-4564, -2377, -143, 36]], ![![888, 463, 28, -7]]]]
 hle2 := by decide  


def PBC401 : ContainsPrimesAboveP 401 ![I401N0, I401N1, I401N2, I401N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI401N0
    exact isPrimeI401N1
    exact isPrimeI401N2
    exact isPrimeI401N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 401 (by decide) (𝕀 ⊙ MulI401N0 ⊙ MulI401N1 ⊙ MulI401N2)
instance hp409 : Fact (Nat.Prime 409) := {out := by norm_num}

def I409N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![409, 0, 0, 0], ![-64, -67, -4, 1]] i)))

def SI409N0: IdealEqSpanCertificate' Table ![![409, 0, 0, 0], ![-64, -67, -4, 1]] 
 ![![409, 0, 0, 0], ![0, 409, 0, 0], ![191, 67, 1, 0], ![291, 201, 0, 1]] where
  M :=![![![409, 0, 0, 0], ![0, 409, 0, 0], ![0, 0, 409, 0], ![0, 0, 0, 409]], ![![-64, -67, -4, 1], ![383, 268, 13, -3], ![-1149, -613, 28, 10], ![3830, 2171, 187, 38]]]
  hmulB := by decide  
  f := ![![![3978169, 2725560, 130248, -29856], ![-1069944, -4427016, 0, 0]], ![![-120504, -82543, -3944, 904], ![32720, 134152, 0, 0]], ![![1838007, 1259265, 60177, -13794], ![-494478, -2045408, 0, 0]], ![![2771211, 1898646, 90732, -20798], ![-745185, -3083856, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-191, -67, 409, 0], ![-291, -201, 0, 409]], ![![1, 0, -4, 1], ![-3, 0, 13, -3], ![-23, -11, 28, 10], ![-105, -44, 187, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P409P0 : CertificateIrreducibleZModOfList' 409 2 2 8 [53, 290, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [119, 408], [0, 1]]
 g := ![![[291, 355], [34], [83], [143, 24], [77, 266], [401], [313], [119, 1]],![[0, 54], [34], [83], [136, 385], [238, 143], [401], [313], [238, 408]]]
 h' := ![![[119, 408], [237, 53], [154, 323], [192, 284], [9, 281], [75, 343], [316, 70], [237, 202], [0, 1]],![[0, 1], [0, 356], [145, 86], [41, 125], [319, 128], [401, 66], [57, 339], [144, 207], [119, 408]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [193, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI409N0 : CertifiedPrimeIdeal' SI409N0 409 where 
  n := 2
  hpos := by decide  
  P := [53, 290, 1]
  hirr := P409P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![494619, 412628, 98040, 2217]
  a := ![3, 0, 7, -4]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-46152, -16141, 98040, 2217]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI409N0 : Ideal.IsPrime I409N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI409N0 B_one_repr
lemma NI409N0 : Nat.card (O ⧸ I409N0) = 167281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI409N0

def I409N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![409, 0, 0, 0], ![-65, 1, 0, 0]] i)))

def SI409N1: IdealEqSpanCertificate' Table ![![409, 0, 0, 0], ![-65, 1, 0, 0]] 
 ![![409, 0, 0, 0], ![344, 1, 0, 0], ![274, 0, 1, 0], ![223, 0, 0, 1]] where
  M :=![![![409, 0, 0, 0], ![0, 409, 0, 0], ![0, 0, 409, 0], ![0, 0, 0, 409]], ![![-65, 1, 0, 0], ![0, -65, 1, 0], ![0, 0, -65, 1], ![383, 332, 80, -64]]]
  hmulB := by decide  
  f := ![![![18721, 362, 1727300, -26574], ![117792, 4090, 10868766, 0]], ![![15796, 342, 1458981, -22446], ![99388, 3681, 9180414, 0]], ![![12556, 262, 1157123, -17802], ![79002, 2864, 7281018, 0]], ![![10227, 243, 941779, -14489], ![64348, 2519, 5926002, 0]]]
  g := ![![![1, 0, 0, 0], ![-344, 409, 0, 0], ![-274, 0, 409, 0], ![-223, 0, 0, 409]], ![![-1, 1, 0, 0], ![54, -65, 1, 0], ![43, 0, -65, 1], ![-297, 332, 80, -64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI409N1 : Nat.card (O ⧸ I409N1) = 409 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI409N1)

lemma isPrimeI409N1 : Ideal.IsPrime I409N1 := prime_ideal_of_norm_prime hp409.out _ NI409N1

def I409N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![409, 0, 0, 0], ![-3, 1, 0, 0]] i)))

def SI409N2: IdealEqSpanCertificate' Table ![![409, 0, 0, 0], ![-3, 1, 0, 0]] 
 ![![409, 0, 0, 0], ![406, 1, 0, 0], ![400, 0, 1, 0], ![382, 0, 0, 1]] where
  M :=![![![409, 0, 0, 0], ![0, 409, 0, 0], ![0, 0, 409, 0], ![0, 0, 0, 409]], ![![-3, 1, 0, 0], ![0, -3, 1, 0], ![0, 0, -3, 1], ![383, 332, 80, -2]]]
  hmulB := by decide  
  f := ![![![1648, -111921, 37127, -1], ![224541, -15183716, 409, 0]], ![![1636, -111098, 36854, -1], ![222906, -15072059, 409, 0]], ![![1612, -109458, 36310, -1], ![219636, -14849562, 409, 0]], ![![1540, -104532, 34676, -1], ![209826, -14181254, 410, 0]]]
  g := ![![![1, 0, 0, 0], ![-406, 409, 0, 0], ![-400, 0, 409, 0], ![-382, 0, 0, 409]], ![![-1, 1, 0, 0], ![2, -3, 1, 0], ![2, 0, -3, 1], ![-405, 332, 80, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI409N2 : Nat.card (O ⧸ I409N2) = 409 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI409N2)

lemma isPrimeI409N2 : Ideal.IsPrime I409N2 := prime_ideal_of_norm_prime hp409.out _ NI409N2
def MulI409N0 : IdealMulLeCertificate' Table 
  ![![409, 0, 0, 0], ![-64, -67, -4, 1]] ![![409, 0, 0, 0], ![-65, 1, 0, 0]]
  ![![409, 0, 0, 0], ![9042, 4623, 273, -68]] where
 M :=  ![![![167281, 0, 0, 0], ![-26585, 409, 0, 0]], ![![-26176, -27403, -1636, 409], ![4543, 4623, 273, -68]]]
 hmul := by decide  
 g :=  ![![![![-8633, -4623, -273, 68], ![409, 0, 0, 0]], ![![-65, 1, 0, 0], ![0, 0, 0, 0]]], ![![![-64, -67, -4, 1], ![0, 0, 0, 0]], ![![-11, 0, 0, 0], ![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI409N1 : IdealMulLeCertificate' Table 
  ![![409, 0, 0, 0], ![9042, 4623, 273, -68]] ![![409, 0, 0, 0], ![-3, 1, 0, 0]]
  ![![409, 0, 0, 0]] where
 M :=  ![![![167281, 0, 0, 0], ![-1227, 409, 0, 0]], ![![3698178, 1890807, 111657, -27812], ![-53170, -27403, -1636, 409]]]
 hmul := by decide  
 g :=  ![![![![409, 0, 0, 0]], ![![-3, 1, 0, 0]]], ![![![9042, 4623, 273, -68]], ![![-130, -67, -4, 1]]]]
 hle2 := by decide  


def PBC409 : ContainsPrimesAboveP 409 ![I409N0, I409N1, I409N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI409N0
    exact isPrimeI409N1
    exact isPrimeI409N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 409 (by decide) (𝕀 ⊙ MulI409N0 ⊙ MulI409N1)


lemma PB692I7_primes (p : ℕ) :
  p ∈ Set.range ![353, 359, 367, 373, 379, 383, 389, 397, 401, 409] ↔ Nat.Prime p ∧ 349 < p ∧ p ≤ 409 := by
  rw [← List.mem_ofFn']
  convert primes_range 349 409 (by omega)
  rfl

def PB692I7 : PrimesBelowBoundCertificateInterval' O 349 409 692 where
  m := 10
  g := ![2, 3, 3, 3, 1, 3, 1, 2, 4, 3]
  P := ![353, 359, 367, 373, 379, 383, 389, 397, 401, 409]
  hP := PB692I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I353N0, I353N1]
    · exact ![I359N0, I359N1, I359N2]
    · exact ![I367N0, I367N1, I367N2]
    · exact ![I373N0, I373N1, I373N2]
    · exact ![I379N0]
    · exact ![I383N0, I383N1, I383N2]
    · exact ![I389N0]
    · exact ![I397N0, I397N1]
    · exact ![I401N0, I401N1, I401N2, I401N3]
    · exact ![I409N0, I409N1, I409N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC353
    · exact PBC359
    · exact PBC367
    · exact PBC373
    · exact PBC379
    · exact PBC383
    · exact PBC389
    · exact PBC397
    · exact PBC401
    · exact PBC409
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![124609, 124609]
    · exact ![128881, 359, 359]
    · exact ![134689, 367, 367]
    · exact ![139129, 373, 373]
    · exact ![20632736881]
    · exact ![383, 146689, 383]
    · exact ![22898045041]
    · exact ![157609, 157609]
    · exact ![401, 401, 401, 401]
    · exact ![167281, 409, 409]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI353N0
      exact NI353N1
    · dsimp ; intro j
      fin_cases j
      exact NI359N0
      exact NI359N1
      exact NI359N2
    · dsimp ; intro j
      fin_cases j
      exact NI367N0
      exact NI367N1
      exact NI367N2
    · dsimp ; intro j
      fin_cases j
      exact NI373N0
      exact NI373N1
      exact NI373N2
    · dsimp ; intro j
      fin_cases j
      exact NI379N0
    · dsimp ; intro j
      fin_cases j
      exact NI383N0
      exact NI383N1
      exact NI383N2
    · dsimp ; intro j
      fin_cases j
      exact NI389N0
    · dsimp ; intro j
      fin_cases j
      exact NI397N0
      exact NI397N1
    · dsimp ; intro j
      fin_cases j
      exact NI401N0
      exact NI401N1
      exact NI401N2
      exact NI401N3
    · dsimp ; intro j
      fin_cases j
      exact NI409N0
      exact NI409N1
      exact NI409N2
  Il := ![[], [I359N1, I359N2], [I367N1, I367N2], [I373N1, I373N2], [], [I383N0, I383N2], [], [], [I401N0, I401N1, I401N2, I401N3], [I409N1, I409N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
