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
instance hp419 : Fact (Nat.Prime 419) := {out := by norm_num}

def I419N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![419, 0, 0, 0], ![-68, -119, -4, 1]] i)))

def SI419N0: IdealEqSpanCertificate' Table ![![419, 0, 0, 0], ![-68, -119, -4, 1]] 
 ![![419, 0, 0, 0], ![0, 419, 0, 0], ![54, 199, 1, 0], ![148, 258, 0, 1]] where
  M :=![![![419, 0, 0, 0], ![0, 419, 0, 0], ![0, 0, 419, 0], ![0, 0, 0, 419]], ![![-68, -119, -4, 1], ![383, 264, -39, -3], ![-1149, -613, 24, -42], ![-16086, -15093, -3973, -18]]]
  hmulB := by decide  
  f := ![![![43353761, 27343330, -4799344, -323126], ![-14756342, -50048712, 0, 0]], ![![-137158, -86463, 15190, 1022], ![46928, 158382, 0, 0]], ![![5522248, 3482952, -611315, -41159], ![-1879289, -6374970, 0, 0]], ![![15229052, 9605037, -1685880, -113506], ![-5183325, -17580780, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-54, -199, 419, 0], ![-148, -258, 0, 419]], ![![0, 1, -4, 1], ![7, 21, -39, -3], ![9, 13, 24, -42], ![480, 1862, -3973, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P419P0 : CertificateIrreducibleZModOfList' 419 2 2 8 [48, 255, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [164, 418], [0, 1]]
 g := ![![[241, 323], [81, 373], [343], [215], [192], [307, 321], [186], [164, 1]],![[0, 96], [79, 46], [343], [215], [192], [157, 98], [186], [328, 418]]]
 h' := ![![[164, 418], [302, 177], [141, 293], [380, 379], [15, 220], [348, 232], [250, 166], [89, 32], [0, 1]],![[0, 1], [0, 242], [8, 126], [105, 40], [61, 199], [267, 187], [239, 253], [309, 387], [164, 418]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [223, 217]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI419N0 : CertifiedPrimeIdeal' SI419N0 419 where 
  n := 2
  hpos := by decide  
  P := [48, 255, 1]
  hirr := P419P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![32986, 29446, 8005, 405]
  a := ![0, -1, -1, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-1096, -3981, 8005, 405]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI419N0 : Ideal.IsPrime I419N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI419N0 B_one_repr
lemma NI419N0 : Nat.card (O ⧸ I419N0) = 175561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI419N0

def I419N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![419, 0, 0, 0], ![-9, 47, -4, 1]] i)))

def SI419N1: IdealEqSpanCertificate' Table ![![419, 0, 0, 0], ![-9, 47, -4, 1]] 
 ![![419, 0, 0, 0], ![0, 419, 0, 0], ![280, 219, 1, 0], ![273, 85, 0, 1]] where
  M :=![![![419, 0, 0, 0], ![0, 419, 0, 0], ![0, 0, 419, 0], ![0, 0, 0, 419]], ![![-9, 47, -4, 1], ![383, 323, 127, -3], ![-1149, -613, 83, 124], ![47492, 40019, 9307, 207]]]
  hmulB := by decide  
  f := ![![![22841090, 19057701, 7577755, -182405], ![1574602, -24951031, 0, 0]], ![![-126187, -105326, -41863, 1007], ![-8380, 137851, 0, 0]], ![![15197779, 12680416, 5042012, -121367], ![1047766, -16601669, 0, 0]], ![![14856544, 12395700, 4928804, -118642], ![1024263, -16228912, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-280, -219, 419, 0], ![-273, -85, 0, 419]], ![![2, 2, -4, 1], ![-82, -65, 127, -3], ![-139, -70, 83, 124], ![-6241, -4811, 9307, 207]]]
  hle1 := by decide   
  hle2 := by decide  


def P419P1 : CertificateIrreducibleZModOfList' 419 2 2 8 [265, 294, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [125, 418], [0, 1]]
 g := ![![[379, 369], [199, 208], [12], [59], [117], [336, 318], [337], [125, 1]],![[414, 50], [221, 211], [12], [59], [117], [281, 101], [337], [250, 418]]]
 h' := ![![[125, 418], [59, 358], [415, 135], [261, 361], [112, 152], [207, 213], [99, 385], [395, 276], [0, 1]],![[0, 1], [395, 61], [111, 284], [134, 58], [257, 267], [16, 206], [39, 34], [118, 143], [125, 418]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [352]]
 b := ![[], [313, 176]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI419N1 : CertifiedPrimeIdeal' SI419N1 419 where 
  n := 2
  hpos := by decide  
  P := [265, 294, 1]
  hirr := P419P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![1552746, 1298489, 264068, -5867]
  a := ![-2, 3, -64, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-168937, -133732, 264068, -5867]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI419N1 : Ideal.IsPrime I419N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI419N1 B_one_repr
lemma NI419N1 : Nat.card (O ⧸ I419N1) = 175561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI419N1
def MulI419N0 : IdealMulLeCertificate' Table 
  ![![419, 0, 0, 0], ![-68, -119, -4, 1]] ![![419, 0, 0, 0], ![-9, 47, -4, 1]]
  ![![419, 0, 0, 0]] where
 M :=  ![![![175561, 0, 0, 0], ![-3771, 19693, -1676, 419]], ![![-28492, -49861, -1676, 419], ![7123, 838, -5866, 0]]]
 hmul := by decide  
 g :=  ![![![![419, 0, 0, 0]], ![![-9, 47, -4, 1]]], ![![![-68, -119, -4, 1]], ![![17, 2, -14, 0]]]]
 hle2 := by decide  


def PBC419 : ContainsPrimesAboveP 419 ![I419N0, I419N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI419N0
    exact isPrimeI419N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 419 (by decide) (𝕀 ⊙ MulI419N0)
instance hp421 : Fact (Nat.Prime 421) := {out := by norm_num}

def I421N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![421, 0, 0, 0], ![-178, -67, -4, 1]] i)))

def SI421N0: IdealEqSpanCertificate' Table ![![421, 0, 0, 0], ![-178, -67, -4, 1]] 
 ![![421, 0, 0, 0], ![0, 421, 0, 0], ![270, 374, 1, 0], ![60, 166, 0, 1]] where
  M :=![![![421, 0, 0, 0], ![0, 421, 0, 0], ![0, 0, 421, 0], ![0, 0, 0, 421]], ![![-178, -67, -4, 1], ![383, 154, 13, -3], ![-1149, -613, -86, 10], ![3830, 2171, 187, -76]]]
  hmulB := by decide  
  f := ![![![9757943, 3975266, 354302, -80892], ![-4761510, -12939014, 0, 0]], ![![-80550, -32817, -2926, 668], ![39574, 106934, 0, 0]], ![![6186496, 2520301, 224625, -51285], ![-3018567, -8203184, 0, 0]], ![![1358892, 553596, 49340, -11265], ![-663062, -1801876, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-270, -374, 421, 0], ![-60, -166, 0, 421]], ![![2, 3, -4, 1], ![-7, -10, 13, -3], ![51, 71, -86, 10], ![-100, -131, 187, -76]]]
  hle1 := by decide   
  hle2 := by decide  


def P421P0 : CertificateIrreducibleZModOfList' 421 2 2 8 [236, 201, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [220, 420], [0, 1]]
 g := ![![[206, 283], [418], [81, 84], [100], [99], [360, 318], [272], [220, 1]],![[158, 138], [418], [37, 337], [100], [99], [13, 103], [272], [19, 420]]]
 h' := ![![[220, 420], [58, 53], [250, 41], [402, 318], [200, 411], [82, 283], [45, 209], [284, 170], [0, 1]],![[0, 1], [351, 368], [8, 380], [55, 103], [105, 10], [34, 138], [136, 212], [215, 251], [220, 420]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [250, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI421N0 : CertifiedPrimeIdeal' SI421N0 421 where 
  n := 2
  hpos := by decide  
  P := [236, 201, 1]
  hirr := P421P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![275030, 239724, 62083, 3351]
  a := ![-1, 1, 1, -3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-39640, -55904, 62083, 3351]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI421N0 : Ideal.IsPrime I421N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI421N0 B_one_repr
lemma NI421N0 : Nat.card (O ⧸ I421N0) = 177241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI421N0

def I421N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![421, 0, 0, 0], ![-210, 1, 0, 0]] i)))

def SI421N1: IdealEqSpanCertificate' Table ![![421, 0, 0, 0], ![-210, 1, 0, 0]] 
 ![![421, 0, 0, 0], ![211, 1, 0, 0], ![105, 0, 1, 0], ![158, 0, 0, 1]] where
  M :=![![![421, 0, 0, 0], ![0, 421, 0, 0], ![0, 0, 421, 0], ![0, 0, 0, 421]], ![![-210, 1, 0, 0], ![0, -210, 1, 0], ![0, 0, -210, 1], ![383, 332, 80, -209]]]
  hmulB := by decide  
  f := ![![![176611, -107101, 716, -1], ![354061, -213026, 421, 0]], ![![88831, -53553, 463, -1], ![178084, -106513, 421, 0]], ![![44205, -26460, 335, -1], ![88620, -52624, 421, 0]], ![![66518, -40112, 400, -1], ![133352, -79780, 422, 0]]]
  g := ![![![1, 0, 0, 0], ![-211, 421, 0, 0], ![-105, 0, 421, 0], ![-158, 0, 0, 421]], ![![-1, 1, 0, 0], ![105, -210, 1, 0], ![52, 0, -210, 1], ![-107, 332, 80, -209]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI421N1 : Nat.card (O ⧸ I421N1) = 421 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI421N1)

lemma isPrimeI421N1 : Ideal.IsPrime I421N1 := prime_ideal_of_norm_prime hp421.out _ NI421N1

def I421N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![421, 0, 0, 0], ![-165, 1, 0, 0]] i)))

def SI421N2: IdealEqSpanCertificate' Table ![![421, 0, 0, 0], ![-165, 1, 0, 0]] 
 ![![421, 0, 0, 0], ![256, 1, 0, 0], ![140, 0, 1, 0], ![366, 0, 0, 1]] where
  M :=![![![421, 0, 0, 0], ![0, 421, 0, 0], ![0, 0, 421, 0], ![0, 0, 0, 421]], ![![-165, 1, 0, 0], ![0, -165, 1, 0], ![0, 0, -165, 1], ![383, 332, 80, -164]]]
  hmulB := by decide  
  f := ![![![34816, -4228831, 29093, -21], ![88831, -10789388, 8841, 0]], ![![21286, -2571159, 17727, -13], ![54310, -6560022, 5473, 0]], ![![11780, -1406036, 9676, -7], ![30056, -3587340, 2947, 0]], ![![30471, -3676155, 25414, -19], ![77745, -9379294, 8000, 0]]]
  g := ![![![1, 0, 0, 0], ![-256, 421, 0, 0], ![-140, 0, 421, 0], ![-366, 0, 0, 421]], ![![-1, 1, 0, 0], ![100, -165, 1, 0], ![54, 0, -165, 1], ![-85, 332, 80, -164]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI421N2 : Nat.card (O ⧸ I421N2) = 421 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI421N2)

lemma isPrimeI421N2 : Ideal.IsPrime I421N2 := prime_ideal_of_norm_prime hp421.out _ NI421N2
def MulI421N0 : IdealMulLeCertificate' Table 
  ![![421, 0, 0, 0], ![-178, -67, -4, 1]] ![![421, 0, 0, 0], ![-210, 1, 0, 0]]
  ![![421, 0, 0, 0], ![-27492, -13983, -831, 208]] where
 M :=  ![![![177241, 0, 0, 0], ![-88410, 421, 0, 0]], ![![-74938, -28207, -1684, 421], ![37763, 14224, 853, -213]]]
 hmul := by decide  
 g :=  ![![![![421, 0, 0, 0], ![0, 0, 0, 0]], ![![27282, 13984, 831, -208], ![421, 0, 0, 0]]], ![![![27314, 13916, 827, -207], ![421, 0, 0, 0]], ![![155, 67, 4, -1], ![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI421N1 : IdealMulLeCertificate' Table 
  ![![421, 0, 0, 0], ![-27492, -13983, -831, 208]] ![![421, 0, 0, 0], ![-165, 1, 0, 0]]
  ![![421, 0, 0, 0]] where
 M :=  ![![![177241, 0, 0, 0], ![-69465, 421, 0, 0]], ![![-11574132, -5886843, -349851, 87568], ![4615844, 2348759, 139772, -34943]]]
 hmul := by decide  
 g :=  ![![![![421, 0, 0, 0]], ![![-165, 1, 0, 0]]], ![![![-27492, -13983, -831, 208]], ![![10964, 5579, 332, -83]]]]
 hle2 := by decide  


def PBC421 : ContainsPrimesAboveP 421 ![I421N0, I421N1, I421N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI421N0
    exact isPrimeI421N1
    exact isPrimeI421N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 421 (by decide) (𝕀 ⊙ MulI421N0 ⊙ MulI421N1)
instance hp431 : Fact (Nat.Prime 431) := {out := by norm_num}

def I431N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![431, 0, 0, 0], ![-12, -67, -4, 1]] i)))

def SI431N0: IdealEqSpanCertificate' Table ![![431, 0, 0, 0], ![-12, -67, -4, 1]] 
 ![![431, 0, 0, 0], ![0, 431, 0, 0], ![347, 119, 1, 0], ![83, 409, 0, 1]] where
  M :=![![![431, 0, 0, 0], ![0, 431, 0, 0], ![0, 0, 431, 0], ![0, 0, 0, 431]], ![![-12, -67, -4, 1], ![383, 320, 13, -3], ![-1149, -613, 80, 10], ![3830, 2171, 187, 90]]]
  hmulB := by decide  
  f := ![![![28520458, 23245291, 931243, -214114], ![-4416457, -32233197, 0, 0]], ![![-110973, -90439, -3623, 833], ![17240, 125421, 0, 0]], ![![22931305, 18689907, 748747, -172154], ![-3551006, -25916460, 0, 0]], ![![5387035, 4390675, 175898, -40443], ![-833972, -6088302, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-347, -119, 431, 0], ![-83, -409, 0, 431]], ![![3, 0, -4, 1], ![-9, 0, 13, -3], ![-69, -33, 80, 10], ![-159, -132, 187, 90]]]
  hle1 := by decide   
  hle2 := by decide  


def P431P0 : CertificateIrreducibleZModOfList' 431 2 2 8 [9, 185, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [246, 430], [0, 1]]
 g := ![![[260, 48], [57, 337], [381, 330], [425, 352], [209], [406, 200], [305], [246, 1]],![[0, 383], [207, 94], [102, 101], [386, 79], [209], [41, 231], [305], [61, 430]]]
 h' := ![![[246, 430], [349, 144], [19, 145], [54, 54], [41, 300], [225, 168], [305, 156], [372, 167], [0, 1]],![[0, 1], [0, 287], [347, 286], [408, 377], [140, 131], [177, 263], [322, 275], [78, 264], [246, 430]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [197]]
 b := ![[], [168, 314]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI431N0 : CertifiedPrimeIdeal' SI431N0 431 where 
  n := 2
  hpos := by decide  
  P := [9, 185, 1]
  hirr := P431P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![29883, 25328, 6107, 517]
  a := ![0, -1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-4947, -2118, 6107, 517]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI431N0 : Ideal.IsPrime I431N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI431N0 B_one_repr
lemma NI431N0 : Nat.card (O ⧸ I431N0) = 185761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI431N0

def I431N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![431, 0, 0, 0], ![70, 1, 0, 0]] i)))

def SI431N1: IdealEqSpanCertificate' Table ![![431, 0, 0, 0], ![70, 1, 0, 0]] 
 ![![431, 0, 0, 0], ![70, 1, 0, 0], ![272, 0, 1, 0], ![355, 0, 0, 1]] where
  M :=![![![431, 0, 0, 0], ![0, 431, 0, 0], ![0, 0, 431, 0], ![0, 0, 0, 431]], ![![70, 1, 0, 0], ![0, 70, 1, 0], ![0, 0, 70, 1], ![383, 332, 80, 71]]]
  hmulB := by decide  
  f := ![![![7351, -245, 843565, 12051], ![-45255, 2155, -5193981, 0]], ![![1190, -53, 139229, 1989], ![-7326, 431, -857259, 0]], ![![4632, -144, 532347, 7605], ![-28516, 1294, -3277755, 0]], ![![6135, -181, 694816, 9926], ![-37769, 1654, -4278105, 0]]]
  g := ![![![1, 0, 0, 0], ![-70, 431, 0, 0], ![-272, 0, 431, 0], ![-355, 0, 0, 431]], ![![0, 1, 0, 0], ![-12, 70, 1, 0], ![-45, 0, 70, 1], ![-162, 332, 80, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI431N1 : Nat.card (O ⧸ I431N1) = 431 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI431N1)

lemma isPrimeI431N1 : Ideal.IsPrime I431N1 := prime_ideal_of_norm_prime hp431.out _ NI431N1

def I431N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![431, 0, 0, 0], ![-190, 1, 0, 0]] i)))

def SI431N2: IdealEqSpanCertificate' Table ![![431, 0, 0, 0], ![-190, 1, 0, 0]] 
 ![![431, 0, 0, 0], ![241, 1, 0, 0], ![104, 0, 1, 0], ![365, 0, 0, 1]] where
  M :=![![![431, 0, 0, 0], ![0, 431, 0, 0], ![0, 0, 431, 0], ![0, 0, 0, 431]], ![![-190, 1, 0, 0], ![0, -190, 1, 0], ![0, 0, -190, 1], ![383, 332, 80, -189]]]
  hmulB := by decide  
  f := ![![![143831, -5928757, 36330, -27], ![326267, -13447200, 11637, 0]], ![![80941, -3315166, 20486, -16], ![183607, -7519226, 6896, 0]], ![![35234, -1430315, 8857, -7], ![79925, -3244136, 3017, 0]], ![![122315, -5021120, 30794, -23], ![277460, -11388554, 9914, 0]]]
  g := ![![![1, 0, 0, 0], ![-241, 431, 0, 0], ![-104, 0, 431, 0], ![-365, 0, 0, 431]], ![![-1, 1, 0, 0], ![106, -190, 1, 0], ![45, 0, -190, 1], ![-44, 332, 80, -189]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI431N2 : Nat.card (O ⧸ I431N2) = 431 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI431N2)

lemma isPrimeI431N2 : Ideal.IsPrime I431N2 := prime_ideal_of_norm_prime hp431.out _ NI431N2
def MulI431N0 : IdealMulLeCertificate' Table 
  ![![431, 0, 0, 0], ![-12, -67, -4, 1]] ![![431, 0, 0, 0], ![70, 1, 0, 0]]
  ![![431, 0, 0, 0], ![-8646, -4370, -267, 67]] where
 M :=  ![![![185761, 0, 0, 0], ![30170, 431, 0, 0]], ![![-5172, -28877, -1724, 431], ![-457, -4370, -267, 67]]]
 hmul := by decide  
 g :=  ![![![![431, 0, 0, 0], ![0, 0, 0, 0]], ![![70, 1, 0, 0], ![0, 0, 0, 0]]], ![![![8634, 4303, 263, -66], ![431, 0, 0, 0]], ![![19, 0, 0, 0], ![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI431N1 : IdealMulLeCertificate' Table 
  ![![431, 0, 0, 0], ![-8646, -4370, -267, 67]] ![![431, 0, 0, 0], ![-190, 1, 0, 0]]
  ![![431, 0, 0, 0]] where
 M :=  ![![![185761, 0, 0, 0], ![-81890, 431, 0, 0]], ![![-3726426, -1883470, -115077, 28877], ![1668401, 843898, 51720, -12930]]]
 hmul := by decide  
 g :=  ![![![![431, 0, 0, 0]], ![![-190, 1, 0, 0]]], ![![![-8646, -4370, -267, 67]], ![![3871, 1958, 120, -30]]]]
 hle2 := by decide  


def PBC431 : ContainsPrimesAboveP 431 ![I431N0, I431N1, I431N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI431N0
    exact isPrimeI431N1
    exact isPrimeI431N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 431 (by decide) (𝕀 ⊙ MulI431N0 ⊙ MulI431N1)
instance hp433 : Fact (Nat.Prime 433) := {out := by norm_num}

def I433N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![433, 0, 0, 0], ![-307, -67, -4, 1]] i)))

def SI433N0: IdealEqSpanCertificate' Table ![![433, 0, 0, 0], ![-307, -67, -4, 1]] 
 ![![433, 0, 0, 0], ![0, 433, 0, 0], ![328, 257, 1, 0], ![139, 95, 0, 1]] where
  M :=![![![433, 0, 0, 0], ![0, 433, 0, 0], ![0, 0, 433, 0], ![0, 0, 0, 433]], ![![-307, -67, -4, 1], ![383, 25, 13, -3], ![-1149, -613, -215, 10], ![3830, 2171, 187, -205]]]
  hmulB := by decide  
  f := ![![![1270775, -14542, 56462, -12870], ![-898908, -2157206, 0, 0]], ![![-11861, 166, -531, 121], ![8660, 20351, 0, 0]], ![![955493, -10936, 42454, -9677], ![-675910, -1622017, 0, 0]], ![![405359, -4627, 18009, -4105], ![-286633, -688033, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-328, -257, 433, 0], ![-139, -95, 0, 433]], ![![2, 2, -4, 1], ![-8, -7, 13, -3], ![157, 124, -215, 10], ![-67, -61, 187, -205]]]
  hle1 := by decide   
  hle2 := by decide  


def P433P0 : CertificateIrreducibleZModOfList' 433 2 2 8 [329, 129, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [304, 432], [0, 1]]
 g := ![![[336, 204], [13], [191], [415], [356, 288], [33, 106], [246], [304, 1]],![[0, 229], [13], [191], [415], [9, 145], [215, 327], [246], [175, 432]]]
 h' := ![![[304, 432], [47, 44], [55, 303], [191, 326], [219, 207], [401, 307], [86, 52], [7, 291], [0, 1]],![[0, 1], [0, 389], [371, 130], [138, 107], [362, 226], [201, 126], [306, 381], [139, 142], [304, 432]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [326]]
 b := ![[], [338, 163]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI433N0 : CertifiedPrimeIdeal' SI433N0 433 where 
  n := 2
  hpos := by decide  
  P := [329, 129, 1]
  hirr := P433P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![282731, 243676, 62677, 4457]
  a := ![19, 1, -1, 3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-48256, -37616, 62677, 4457]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI433N0 : Ideal.IsPrime I433N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI433N0 B_one_repr
lemma NI433N0 : Nat.card (O ⧸ I433N0) = 187489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI433N0

def I433N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![433, 0, 0, 0], ![-185, 1, 0, 0]] i)))

def SI433N1: IdealEqSpanCertificate' Table ![![433, 0, 0, 0], ![-185, 1, 0, 0]] 
 ![![433, 0, 0, 0], ![248, 1, 0, 0], ![415, 0, 1, 0], ![134, 0, 0, 1]] where
  M :=![![![433, 0, 0, 0], ![0, 433, 0, 0], ![0, 0, 433, 0], ![0, 0, 0, 433]], ![![-185, 1, 0, 0], ![0, -185, 1, 0], ![0, 0, -185, 1], ![383, 332, 80, -184]]]
  hmulB := by decide  
  f := ![![![70856, 912, 1434113, -7752], ![165839, 3031, 3356616, 0]], ![![40516, 521, 836566, -4522], ![94828, 1732, 1958026, 0]], ![![67790, 744, 1374359, -7429], ![158663, 2599, 3216757, 0]], ![![22208, 329, 443813, -2399], ![51978, 1051, 1038768, 0]]]
  g := ![![![1, 0, 0, 0], ![-248, 433, 0, 0], ![-415, 0, 433, 0], ![-134, 0, 0, 433]], ![![-1, 1, 0, 0], ![105, -185, 1, 0], ![177, 0, -185, 1], ![-209, 332, 80, -184]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI433N1 : Nat.card (O ⧸ I433N1) = 433 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI433N1)

lemma isPrimeI433N1 : Ideal.IsPrime I433N1 := prime_ideal_of_norm_prime hp433.out _ NI433N1

def I433N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![433, 0, 0, 0], ![-73, 1, 0, 0]] i)))

def SI433N2: IdealEqSpanCertificate' Table ![![433, 0, 0, 0], ![-73, 1, 0, 0]] 
 ![![433, 0, 0, 0], ![360, 1, 0, 0], ![300, 0, 1, 0], ![250, 0, 0, 1]] where
  M :=![![![433, 0, 0, 0], ![0, 433, 0, 0], ![0, 0, 433, 0], ![0, 0, 0, 433]], ![![-73, 1, 0, 0], ![0, -73, 1, 0], ![0, 0, -73, 1], ![383, 332, 80, -72]]]
  hmulB := by decide  
  f := ![![![41830, -3273455, 46075, -17], ![248109, -19413122, 7361, 0]], ![![34968, -2721408, 38368, -15], ![207408, -16139209, 6495, 0]], ![![29067, -2267997, 31939, -12], ![172407, -13450278, 5196, 0]], ![![24259, -1889925, 26615, -10], ![143889, -11208132, 4331, 0]]]
  g := ![![![1, 0, 0, 0], ![-360, 433, 0, 0], ![-300, 0, 433, 0], ![-250, 0, 0, 433]], ![![-1, 1, 0, 0], ![60, -73, 1, 0], ![50, 0, -73, 1], ![-289, 332, 80, -72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI433N2 : Nat.card (O ⧸ I433N2) = 433 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI433N2)

lemma isPrimeI433N2 : Ideal.IsPrime I433N2 := prime_ideal_of_norm_prime hp433.out _ NI433N2
def MulI433N0 : IdealMulLeCertificate' Table 
  ![![433, 0, 0, 0], ![-307, -67, -4, 1]] ![![433, 0, 0, 0], ![-185, 1, 0, 0]]
  ![![433, 0, 0, 0], ![24703, 12853, 753, -188]] where
 M :=  ![![![187489, 0, 0, 0], ![-80105, 433, 0, 0]], ![![-132931, -29011, -1732, 433], ![57178, 12420, 753, -188]]]
 hmul := by decide  
 g :=  ![![![![-24270, -12853, -753, 188], ![433, 0, 0, 0]], ![![-185, 1, 0, 0], ![0, 0, 0, 0]]], ![![![-307, -67, -4, 1], ![0, 0, 0, 0]], ![![-24628, -12854, -753, 188], ![434, 0, 0, 0]]]]
 hle2 := by decide  

def MulI433N1 : IdealMulLeCertificate' Table 
  ![![433, 0, 0, 0], ![24703, 12853, 753, -188]] ![![433, 0, 0, 0], ![-73, 1, 0, 0]]
  ![![433, 0, 0, 0]] where
 M :=  ![![![187489, 0, 0, 0], ![-31609, 433, 0, 0]], ![![10696399, 5565349, 326049, -81404], ![-1875323, -975982, -57156, 14289]]]
 hmul := by decide  
 g :=  ![![![![433, 0, 0, 0]], ![![-73, 1, 0, 0]]], ![![![24703, 12853, 753, -188]], ![![-4331, -2254, -132, 33]]]]
 hle2 := by decide  


def PBC433 : ContainsPrimesAboveP 433 ![I433N0, I433N1, I433N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI433N0
    exact isPrimeI433N1
    exact isPrimeI433N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 433 (by decide) (𝕀 ⊙ MulI433N0 ⊙ MulI433N1)
instance hp439 : Fact (Nat.Prime 439) := {out := by norm_num}

def I439N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-626, -335, -20, 5]] i)))

def SI439N0: IdealEqSpanCertificate' Table ![![-626, -335, -20, 5]] 
 ![![439, 0, 0, 0], ![0, 439, 0, 0], ![183, 357, 1, 0], ![80, 44, 0, 1]] where
  M :=![![![-626, -335, -20, 5], ![1915, 1034, 65, -15], ![-5745, -3065, -166, 50], ![19150, 10855, 935, -116]]]
  hmulB := by decide  
  f := ![![![-689, -335, -20, 5]], ![![1915, 971, 65, -15]], ![![1257, 643, 44, -10]], ![![110, 61, 5, -1]]]
  g := ![![![6, 15, -20, 5], ![-20, -49, 65, -15], ![47, 123, -166, 50], ![-325, -724, 935, -116]]]
  hle1 := by decide   
  hle2 := by decide  


def P439P0 : CertificateIrreducibleZModOfList' 439 2 2 8 [42, 302, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [137, 438], [0, 1]]
 g := ![![[49, 45], [181, 352], [92, 123], [81], [338, 199], [19, 261], [111], [137, 1]],![[68, 394], [115, 87], [261, 316], [81], [383, 240], [217, 178], [111], [274, 438]]]
 h' := ![![[137, 438], [300, 22], [87, 120], [64, 92], [291, 9], [80, 257], [181, 333], [392, 289], [0, 1]],![[0, 1], [241, 417], [284, 319], [376, 347], [207, 430], [169, 182], [146, 106], [36, 150], [137, 438]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [17, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI439N0 : CertifiedPrimeIdeal' SI439N0 439 where 
  n := 2
  hpos := by decide  
  P := [42, 302, 1]
  hirr := P439P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![125748, 112292, 30808, 2897]
  a := ![-1, 0, 1, 2]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-13084, -25088, 30808, 2897]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI439N0 : Ideal.IsPrime I439N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI439N0 B_one_repr
lemma NI439N0 : Nat.card (O ⧸ I439N0) = 192721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI439N0

def I439N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![439, 0, 0, 0], ![31, 1, 0, 0]] i)))

def SI439N1: IdealEqSpanCertificate' Table ![![439, 0, 0, 0], ![31, 1, 0, 0]] 
 ![![439, 0, 0, 0], ![31, 1, 0, 0], ![356, 0, 1, 0], ![378, 0, 0, 1]] where
  M :=![![![439, 0, 0, 0], ![0, 439, 0, 0], ![0, 0, 439, 0], ![0, 0, 0, 439]], ![![31, 1, 0, 0], ![0, 31, 1, 0], ![0, 0, 31, 1], ![383, 332, 80, 32]]]
  hmulB := by decide  
  f := ![![![5085, -224059, -7295, -2], ![-71996, 3175287, 878, 0]], ![![279, -15863, -543, -1], ![-3950, 224768, 439, 0]], ![![4095, -181683, -5896, -1], ![-57979, 2574736, 439, 0]], ![![4428, -192892, -6258, -1], ![-62694, 2733622, 440, 0]]]
  g := ![![![1, 0, 0, 0], ![-31, 439, 0, 0], ![-356, 0, 439, 0], ![-378, 0, 0, 439]], ![![0, 1, 0, 0], ![-3, 31, 1, 0], ![-26, 0, 31, 1], ![-115, 332, 80, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI439N1 : Nat.card (O ⧸ I439N1) = 439 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI439N1)

lemma isPrimeI439N1 : Ideal.IsPrime I439N1 := prime_ideal_of_norm_prime hp439.out _ NI439N1

def I439N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![439, 0, 0, 0], ![50, 1, 0, 0]] i)))

def SI439N2: IdealEqSpanCertificate' Table ![![439, 0, 0, 0], ![50, 1, 0, 0]] 
 ![![439, 0, 0, 0], ![50, 1, 0, 0], ![134, 0, 1, 0], ![324, 0, 0, 1]] where
  M :=![![![439, 0, 0, 0], ![0, 439, 0, 0], ![0, 0, 439, 0], ![0, 0, 0, 439]], ![![50, 1, 0, 0], ![0, 50, 1, 0], ![0, 0, 50, 1], ![383, 332, 80, 51]]]
  hmulB := by decide  
  f := ![![![14601, -1308, 6191968, 123840], ![-128188, 14048, -54365760, 0]], ![![1650, -167, 719996, 14400], ![-14486, 1756, -6321600, 0]], ![![4406, -412, 1889990, 37800], ![-38682, 4391, -16594200, 0]], ![![10816, -978, 4569926, 91399], ![-94958, 10486, -40124160, 0]]]
  g := ![![![1, 0, 0, 0], ![-50, 439, 0, 0], ![-134, 0, 439, 0], ![-324, 0, 0, 439]], ![![0, 1, 0, 0], ![-6, 50, 1, 0], ![-16, 0, 50, 1], ![-99, 332, 80, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI439N2 : Nat.card (O ⧸ I439N2) = 439 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI439N2)

lemma isPrimeI439N2 : Ideal.IsPrime I439N2 := prime_ideal_of_norm_prime hp439.out _ NI439N2
def MulI439N0 : IdealMulLeCertificate' Table 
  ![![-626, -335, -20, 5]] ![![439, 0, 0, 0], ![31, 1, 0, 0]]
  ![![439, 0, 0, 0], ![-3586, -1958, -111, 28]] where
 M :=  ![![![-274814, -147065, -8780, 2195], ![-17491, -9351, -555, 140]]]
 hmul := by decide  
 g :=  ![![![![2960, 1623, 91, -23], ![439, 0, 0, 0]], ![![1, 1, 0, 0], ![5, 0, 0, 0]]]]
 hle2 := by decide  

def MulI439N1 : IdealMulLeCertificate' Table 
  ![![439, 0, 0, 0], ![-3586, -1958, -111, 28]] ![![439, 0, 0, 0], ![50, 1, 0, 0]]
  ![![439, 0, 0, 0]] where
 M :=  ![![![192721, 0, 0, 0], ![21950, 439, 0, 0]], ![![-1574254, -859562, -48729, 12292], ![-168576, -92190, -5268, 1317]]]
 hmul := by decide  
 g :=  ![![![![439, 0, 0, 0]], ![![50, 1, 0, 0]]], ![![![-3586, -1958, -111, 28]], ![![-384, -210, -12, 3]]]]
 hle2 := by decide  


def PBC439 : ContainsPrimesAboveP 439 ![I439N0, I439N1, I439N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI439N0
    exact isPrimeI439N1
    exact isPrimeI439N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 439 (by decide) (𝕀 ⊙ MulI439N0 ⊙ MulI439N1)
instance hp443 : Fact (Nat.Prime 443) := {out := by norm_num}

def I443N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![386, 201, 12, -3]] i)))

def SI443N0: IdealEqSpanCertificate' Table ![![386, 201, 12, -3]] 
 ![![443, 0, 0, 0], ![0, 443, 0, 0], ![440, 150, 1, 0], ![7, 90, 0, 1]] where
  M :=![![![386, 201, 12, -3], ![-1149, -610, -39, 9], ![3447, 1839, 110, -30], ![-11490, -6513, -561, 80]]]
  hmulB := by decide  
  f := ![![![403, 201, 12, -3]], ![![-1149, -593, -39, 9]], ![![19, 3, -1, 0]], ![![-253, -132, -9, 2]]]
  g := ![![![-11, -3, 12, -3], ![36, 10, -39, 9], ![-101, -27, 110, -30], ![530, 159, -561, 80]]]
  hle1 := by decide   
  hle2 := by decide  


def P443P0 : CertificateIrreducibleZModOfList' 443 2 2 8 [172, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [382, 442], [0, 1]]
 g := ![![[312, 111], [18, 164], [103], [3, 371], [336, 191], [351, 409], [25], [382, 1]],![[186, 332], [203, 279], [103], [408, 72], [203, 252], [210, 34], [25], [321, 442]]]
 h' := ![![[382, 442], [5, 221], [17, 399], [370, 288], [241, 126], [319, 325], [238, 176], [303, 5], [0, 1]],![[0, 1], [257, 222], [43, 44], [79, 155], [86, 317], [429, 118], [134, 267], [441, 438], [382, 442]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [417]]
 b := ![[], [268, 430]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI443N0 : CertifiedPrimeIdeal' SI443N0 443 where 
  n := 2
  hpos := by decide  
  P := [172, 61, 1]
  hirr := P443P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![123984, 109100, 28780, 2074]
  a := ![-5, 0, 0, 2]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-28338, -9920, 28780, 2074]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI443N0 : Ideal.IsPrime I443N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI443N0 B_one_repr
lemma NI443N0 : Nat.card (O ⧸ I443N0) = 196249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI443N0

def I443N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![403, 201, 12, -3]] i)))

def SI443N1: IdealEqSpanCertificate' Table ![![403, 201, 12, -3]] 
 ![![443, 0, 0, 0], ![0, 443, 0, 0], ![423, 292, 1, 0], ![81, 215, 0, 1]] where
  M :=![![![403, 201, 12, -3], ![-1149, -593, -39, 9], ![3447, 1839, 127, -30], ![-11490, -6513, -561, 97]]]
  hmulB := by decide  
  f := ![![![386, 201, 12, -3]], ![![-1149, -610, -39, 9]], ![![-381, -206, -14, 3]], ![![-513, -274, -18, 4]]]
  g := ![![![-10, -6, 12, -3], ![33, 20, -39, 9], ![-108, -65, 127, -30], ![492, 308, -561, 97]]]
  hle1 := by decide   
  hle2 := by decide  


def P443P1 : CertificateIrreducibleZModOfList' 443 2 2 8 [77, 193, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [250, 442], [0, 1]]
 g := ![![[434, 420], [402, 289], [435], [169, 339], [251, 71], [244, 420], [271], [250, 1]],![[0, 23], [0, 154], [435], [306, 104], [281, 372], [253, 23], [271], [57, 442]]]
 h' := ![![[250, 442], [56, 340], [263, 426], [277, 401], [165, 35], [261, 300], [42, 103], [242, 403], [0, 1]],![[0, 1], [0, 103], [0, 17], [409, 42], [55, 408], [394, 143], [98, 340], [431, 40], [250, 442]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [429, 273]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI443N1 : CertifiedPrimeIdeal' SI443N1 443 where 
  n := 2
  hpos := by decide  
  P := [77, 193, 1]
  hirr := P443P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![82507, 63811, 11936, -1569]
  a := ![-10, 2, 13, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-10924, -6962, 11936, -1569]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI443N1 : Ideal.IsPrime I443N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI443N1 B_one_repr
lemma NI443N1 : Nat.card (O ⧸ I443N1) = 196249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI443N1
def MulI443N0 : IdealMulLeCertificate' Table 
  ![![386, 201, 12, -3]] ![![403, 201, 12, -3]]
  ![![443, 0, 0, 0]] where
 M :=  ![![![443, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![1, 0, 0, 0]]]]
 hle2 := by decide  


def PBC443 : ContainsPrimesAboveP 443 ![I443N0, I443N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI443N0
    exact isPrimeI443N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 443 (by decide) (𝕀 ⊙ MulI443N0)
instance hp449 : Fact (Nat.Prime 449) := {out := by norm_num}

def I449N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-109, -67, -4, 1]] i)))

def SI449N0: IdealEqSpanCertificate' Table ![![-109, -67, -4, 1]] 
 ![![449, 0, 0, 0], ![0, 449, 0, 0], ![56, 22, 1, 0], ![115, 21, 0, 1]] where
  M :=![![![-109, -67, -4, 1], ![383, 223, 13, -3], ![-1149, -613, -17, 10], ![3830, 2171, 187, -7]]]
  hmulB := by decide  
  f := ![![![154, 67, 4, -1]], ![![-383, -178, -13, 3]], ![![3, 1, 0, 0]], ![![13, 4, 0, 0]]]
  g := ![![![0, 0, -4, 1], ![0, 0, 13, -3], ![-3, -1, -17, 10], ![-13, -4, 187, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P449P0 : CertificateIrreducibleZModOfList' 449 2 2 8 [34, 393, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 448], [0, 1]]
 g := ![![[104, 204], [362], [324], [16], [413], [36], [171, 334], [56, 1]],![[303, 245], [362], [324], [16], [413], [36], [17, 115], [112, 448]]]
 h' := ![![[56, 448], [303, 334], [200, 132], [248, 18], [227, 4], [203, 47], [23, 6], [341, 408], [0, 1]],![[0, 1], [149, 115], [408, 317], [358, 431], [2, 445], [141, 402], [359, 443], [290, 41], [56, 448]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [179]]
 b := ![[], [188, 314]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI449N0 : CertifiedPrimeIdeal' SI449N0 449 where 
  n := 2
  hpos := by decide  
  P := [34, 393, 1]
  hirr := P449P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![39877, 38038, 10032, 752]
  a := ![1, 1, -4, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-1355, -442, 10032, 752]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI449N0 : Ideal.IsPrime I449N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI449N0 B_one_repr
lemma NI449N0 : Nat.card (O ⧸ I449N0) = 201601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI449N0

def I449N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![449, 0, 0, 0], ![82, 1, 0, 0]] i)))

def SI449N1: IdealEqSpanCertificate' Table ![![449, 0, 0, 0], ![82, 1, 0, 0]] 
 ![![449, 0, 0, 0], ![82, 1, 0, 0], ![11, 0, 1, 0], ![445, 0, 0, 1]] where
  M :=![![![449, 0, 0, 0], ![0, 449, 0, 0], ![0, 0, 449, 0], ![0, 0, 0, 449]], ![![82, 1, 0, 0], ![0, 82, 1, 0], ![0, 0, 82, 1], ![383, 332, 80, 83]]]
  hmulB := by decide  
  f := ![![![17385, -1086206, -13741, -6], ![-95188, 5948801, 2694, 0]], ![![3198, -198483, -2503, -1], ![-17510, 1087029, 449, 0]], ![![261, -26729, -408, -1], ![-1429, 146375, 449, 0]], ![![17223, -1076517, -13623, -6], ![-94301, 5895737, 2695, 0]]]
  g := ![![![1, 0, 0, 0], ![-82, 449, 0, 0], ![-11, 0, 449, 0], ![-445, 0, 0, 449]], ![![0, 1, 0, 0], ![-15, 82, 1, 0], ![-3, 0, 82, 1], ![-144, 332, 80, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI449N1 : Nat.card (O ⧸ I449N1) = 449 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI449N1)

lemma isPrimeI449N1 : Ideal.IsPrime I449N1 := prime_ideal_of_norm_prime hp449.out _ NI449N1

def I449N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![449, 0, 0, 0], ![-105, 1, 0, 0]] i)))

def SI449N2: IdealEqSpanCertificate' Table ![![449, 0, 0, 0], ![-105, 1, 0, 0]] 
 ![![449, 0, 0, 0], ![344, 1, 0, 0], ![200, 0, 1, 0], ![346, 0, 0, 1]] where
  M :=![![![449, 0, 0, 0], ![0, 449, 0, 0], ![0, 0, 449, 0], ![0, 0, 0, 449]], ![![-105, 1, 0, 0], ![0, -105, 1, 0], ![0, 0, -105, 1], ![383, 332, 80, -104]]]
  hmulB := by decide  
  f := ![![![74551, -4220660, 42290, -20], ![318790, -18045310, 8980, 0]], ![![57331, -3233601, 32471, -16], ![245155, -13825159, 7184, 0]], ![![33310, -1879922, 18846, -9], ![142438, -8037548, 4041, 0]], ![![57494, -3252478, 32651, -16], ![245852, -13905874, 7185, 0]]]
  g := ![![![1, 0, 0, 0], ![-344, 449, 0, 0], ![-200, 0, 449, 0], ![-346, 0, 0, 449]], ![![-1, 1, 0, 0], ![80, -105, 1, 0], ![46, 0, -105, 1], ![-209, 332, 80, -104]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI449N2 : Nat.card (O ⧸ I449N2) = 449 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI449N2)

lemma isPrimeI449N2 : Ideal.IsPrime I449N2 := prime_ideal_of_norm_prime hp449.out _ NI449N2
def MulI449N0 : IdealMulLeCertificate' Table 
  ![![-109, -67, -4, 1]] ![![449, 0, 0, 0], ![82, 1, 0, 0]]
  ![![449, 0, 0, 0], ![-10351, -5271, -315, 79]] where
 M :=  ![![![-48941, -30083, -1796, 449], ![-8555, -5271, -315, 79]]]
 hmul := by decide  
 g :=  ![![![![10242, 5204, 311, -78], ![449, 0, 0, 0]], ![![4, 0, 0, 0], ![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI449N1 : IdealMulLeCertificate' Table 
  ![![449, 0, 0, 0], ![-10351, -5271, -315, 79]] ![![449, 0, 0, 0], ![-105, 1, 0, 0]]
  ![![449, 0, 0, 0]] where
 M :=  ![![![201601, 0, 0, 0], ![-47145, 449, 0, 0]], ![![-4647599, -2366679, -141435, 35471], ![1117112, 569332, 34124, -8531]]]
 hmul := by decide  
 g :=  ![![![![449, 0, 0, 0]], ![![-105, 1, 0, 0]]], ![![![-10351, -5271, -315, 79]], ![![2488, 1268, 76, -19]]]]
 hle2 := by decide  


def PBC449 : ContainsPrimesAboveP 449 ![I449N0, I449N1, I449N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI449N0
    exact isPrimeI449N1
    exact isPrimeI449N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 449 (by decide) (𝕀 ⊙ MulI449N0 ⊙ MulI449N1)
instance hp457 : Fact (Nat.Prime 457) := {out := by norm_num}

def I457N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![457, 0, 0, 0], ![77, -67, -4, 1]] i)))

def SI457N0: IdealEqSpanCertificate' Table ![![457, 0, 0, 0], ![77, -67, -4, 1]] 
 ![![457, 0, 0, 0], ![0, 457, 0, 0], ![157, 208, 1, 0], ![248, 308, 0, 1]] where
  M :=![![![457, 0, 0, 0], ![0, 457, 0, 0], ![0, 0, 457, 0], ![0, 0, 0, 457]], ![![77, -67, -4, 1], ![383, 409, 13, -3], ![-1149, -613, 169, 10], ![3830, 2171, 187, 179]]]
  hmulB := by decide  
  f := ![![![740103, 793030, 25240, -5826], ![8226, -884752, 0, 0]], ![![-67331, -72050, -2292, 529], ![-457, 80432, 0, 0]], ![![223592, 239667, 7629, -1761], ![2745, -267344, 0, 0]], ![![356258, 381790, 12152, -2805], ![4126, -425920, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-157, -208, 457, 0], ![-248, -308, 0, 457]], ![![1, 1, -4, 1], ![-2, -3, 13, -3], ![-66, -85, 169, 10], ![-153, -201, 187, 179]]]
  hle1 := by decide   
  hle2 := by decide  


def P457P0 : CertificateIrreducibleZModOfList' 457 2 2 8 [395, 161, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [296, 456], [0, 1]]
 g := ![![[49, 1], [265], [393], [83, 399], [195], [385], [272, 243], [296, 1]],![[345, 456], [265], [393], [281, 58], [195], [385], [451, 214], [135, 456]]]
 h' := ![![[296, 456], [105, 1], [139, 308], [119, 415], [160, 221], [303, 295], [412, 222], [72, 391], [0, 1]],![[0, 1], [401, 456], [364, 149], [26, 42], [225, 236], [336, 162], [316, 235], [187, 66], [296, 456]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [198]]
 b := ![[], [429, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI457N0 : CertifiedPrimeIdeal' SI457N0 457 where 
  n := 2
  hpos := by decide  
  P := [395, 161, 1]
  hirr := P457P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![31327, 26996, 6457, 487]
  a := ![-3, 1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-2414, -3208, 6457, 487]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI457N0 : Ideal.IsPrime I457N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI457N0 B_one_repr
lemma NI457N0 : Nat.card (O ⧸ I457N0) = 208849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI457N0

def I457N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![457, 0, 0, 0], ![-116, 1, 0, 0]] i)))

def SI457N1: IdealEqSpanCertificate' Table ![![457, 0, 0, 0], ![-116, 1, 0, 0]] 
 ![![457, 0, 0, 0], ![341, 1, 0, 0], ![254, 0, 1, 0], ![216, 0, 0, 1]] where
  M :=![![![457, 0, 0, 0], ![0, 457, 0, 0], ![0, 0, 457, 0], ![0, 0, 0, 457]], ![![-116, 1, 0, 0], ![0, -116, 1, 0], ![0, 0, -116, 1], ![383, 332, 80, -115]]]
  hmulB := by decide  
  f := ![![![43269, -141, 341386, -2943], ![170461, 914, 1344951, 0]], ![![32249, -46, 265522, -2289], ![127047, 914, 1046073, 0]], ![![24158, -92, 189659, -1635], ![95172, 458, 747195, 0]], ![![20584, -32, 161355, -1391], ![81092, 573, 635688, 0]]]
  g := ![![![1, 0, 0, 0], ![-341, 457, 0, 0], ![-254, 0, 457, 0], ![-216, 0, 0, 457]], ![![-1, 1, 0, 0], ![86, -116, 1, 0], ![64, 0, -116, 1], ![-237, 332, 80, -115]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI457N1 : Nat.card (O ⧸ I457N1) = 457 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI457N1)

lemma isPrimeI457N1 : Ideal.IsPrime I457N1 := prime_ideal_of_norm_prime hp457.out _ NI457N1

def I457N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![457, 0, 0, 0], ![-93, 1, 0, 0]] i)))

def SI457N2: IdealEqSpanCertificate' Table ![![457, 0, 0, 0], ![-93, 1, 0, 0]] 
 ![![457, 0, 0, 0], ![364, 1, 0, 0], ![34, 0, 1, 0], ![420, 0, 0, 1]] where
  M :=![![![457, 0, 0, 0], ![0, 457, 0, 0], ![0, 0, 457, 0], ![0, 0, 0, 457]], ![![-93, 1, 0, 0], ![0, -93, 1, 0], ![0, 0, -93, 1], ![383, 332, 80, -92]]]
  hmulB := by decide  
  f := ![![![19903, 623, 1935507, -20812], ![97798, 4113, 9511084, 0]], ![![15904, 573, 1551604, -16684], ![78148, 3656, 7624588, 0]], ![![1600, 76, 143963, -1548], ![7862, 458, 707436, 0]], ![![18408, 565, 1778803, -19127], ![90452, 3749, 8741040, 0]]]
  g := ![![![1, 0, 0, 0], ![-364, 457, 0, 0], ![-34, 0, 457, 0], ![-420, 0, 0, 457]], ![![-1, 1, 0, 0], ![74, -93, 1, 0], ![6, 0, -93, 1], ![-185, 332, 80, -92]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI457N2 : Nat.card (O ⧸ I457N2) = 457 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI457N2)

lemma isPrimeI457N2 : Ideal.IsPrime I457N2 := prime_ideal_of_norm_prime hp457.out _ NI457N2
def MulI457N0 : IdealMulLeCertificate' Table 
  ![![457, 0, 0, 0], ![77, -67, -4, 1]] ![![457, 0, 0, 0], ![-116, 1, 0, 0]]
  ![![457, 0, 0, 0], ![15672, 8181, 477, -119]] where
 M :=  ![![![208849, 0, 0, 0], ![-53012, 457, 0, 0]], ![![35189, -30619, -1828, 457], ![-8549, 8181, 477, -119]]]
 hmul := by decide  
 g :=  ![![![![-15215, -8181, -477, 119], ![457, 0, 0, 0]], ![![-116, 1, 0, 0], ![0, 0, 0, 0]]], ![![![-15595, -8248, -481, 120], ![457, 0, 0, 0]], ![![-53, 0, 0, 0], ![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI457N1 : IdealMulLeCertificate' Table 
  ![![457, 0, 0, 0], ![15672, 8181, 477, -119]] ![![457, 0, 0, 0], ![-93, 1, 0, 0]]
  ![![457, 0, 0, 0]] where
 M :=  ![![![208849, 0, 0, 0], ![-42501, 457, 0, 0]], ![![7162104, 3738717, 217989, -54383], ![-1503073, -784669, -45700, 11425]]]
 hmul := by decide  
 g :=  ![![![![457, 0, 0, 0]], ![![-93, 1, 0, 0]]], ![![![15672, 8181, 477, -119]], ![![-3289, -1717, -100, 25]]]]
 hle2 := by decide  


def PBC457 : ContainsPrimesAboveP 457 ![I457N0, I457N1, I457N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI457N0
    exact isPrimeI457N1
    exact isPrimeI457N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 457 (by decide) (𝕀 ⊙ MulI457N0 ⊙ MulI457N1)
instance hp461 : Fact (Nat.Prime 461) := {out := by norm_num}

def I461N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![701, 335, 20, -5]] i)))

def SI461N0: IdealEqSpanCertificate' Table ![![701, 335, 20, -5]] 
 ![![461, 0, 0, 0], ![0, 461, 0, 0], ![239, 83, 1, 0], ![447, 265, 0, 1]] where
  M :=![![![701, 335, 20, -5], ![-1915, -959, -65, 15], ![5745, 3065, 241, -50], ![-19150, -10855, -935, 191]]]
  hmulB := by decide  
  f := ![![![-614, -335, -20, 5]], ![![1915, 1046, 65, -15]], ![![14, 8, 1, 0]], ![![547, 300, 20, -4]]]
  g := ![![![-4, 0, 20, -5], ![15, 1, -65, 15], ![-64, -8, 241, -50], ![258, 35, -935, 191]]]
  hle1 := by decide   
  hle2 := by decide  


def P461P0 : CertificateIrreducibleZModOfList' 461 2 2 8 [353, 336, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [125, 460], [0, 1]]
 g := ![![[253, 435], [388], [233, 114], [197, 195], [157], [244], [186, 254], [125, 1]],![[230, 26], [388], [192, 347], [139, 266], [157], [244], [127, 207], [250, 460]]]
 h' := ![![[125, 460], [15, 378], [270, 237], [70, 351], [251, 411], [228, 247], [265, 76], [131, 59], [0, 1]],![[0, 1], [243, 83], [391, 224], [150, 110], [455, 50], [216, 214], [84, 385], [130, 402], [125, 460]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [201]]
 b := ![[], [288, 331]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI461N0 : CertifiedPrimeIdeal' SI461N0 461 where 
  n := 2
  hpos := by decide  
  P := [353, 336, 1]
  hirr := P461P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![495057, 412628, 98362, 2033]
  a := ![3, 0, 7, -4]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-51892, -17983, 98362, 2033]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI461N0 : Ideal.IsPrime I461N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI461N0 B_one_repr
lemma NI461N0 : Nat.card (O ⧸ I461N0) = 212521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI461N0

def I461N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-614, -335, -20, 5]] i)))

def SI461N1: IdealEqSpanCertificate' Table ![![-614, -335, -20, 5]] 
 ![![461, 0, 0, 0], ![0, 461, 0, 0], ![199, 377, 1, 0], ![120, 58, 0, 1]] where
  M :=![![![-614, -335, -20, 5], ![1915, 1046, 65, -15], ![-5745, -3065, -154, 50], ![19150, 10855, 935, -104]]]
  hmulB := by decide  
  f := ![![![701, 335, 20, -5]], ![![-1915, -959, -65, 15]], ![![-1251, -633, -44, 10]], ![![-100, -57, -5, 1]]]
  g := ![![![6, 15, -20, 5], ![-20, -49, 65, -15], ![41, 113, -154, 50], ![-335, -728, 935, -104]]]
  hle1 := by decide   
  hle2 := by decide  


def P461P1 : CertificateIrreducibleZModOfList' 461 2 2 8 [142, 132, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [329, 460], [0, 1]]
 g := ![![[397, 237], [256], [296, 297], [155, 58], [298], [402], [39, 376], [329, 1]],![[0, 224], [256], [277, 164], [336, 403], [298], [402], [195, 85], [197, 460]]]
 h' := ![![[329, 460], [174, 148], [380, 445], [118, 183], [183, 141], [116, 41], [455, 223], [304, 225], [0, 1]],![[0, 1], [0, 313], [187, 16], [395, 278], [11, 320], [236, 420], [62, 238], [108, 236], [329, 460]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78]]
 b := ![[], [269, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI461N1 : CertifiedPrimeIdeal' SI461N1 461 where 
  n := 2
  hpos := by decide  
  P := [142, 132, 1]
  hirr := P461P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![30016, 25645, 6424, 200]
  a := ![0, 1, 1, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-2760, -5223, 6424, 200]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI461N1 : Ideal.IsPrime I461N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI461N1 B_one_repr
lemma NI461N1 : Nat.card (O ⧸ I461N1) = 212521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI461N1
def MulI461N0 : IdealMulLeCertificate' Table 
  ![![701, 335, 20, -5]] ![![-614, -335, -20, 5]]
  ![![461, 0, 0, 0]] where
 M :=  ![![![461, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![1, 0, 0, 0]]]]
 hle2 := by decide  


def PBC461 : ContainsPrimesAboveP 461 ![I461N0, I461N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI461N0
    exact isPrimeI461N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 461 (by decide) (𝕀 ⊙ MulI461N0)
instance hp463 : Fact (Nat.Prime 463) := {out := by norm_num}

def I463N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![463, 0, 0, 0], ![59, 1, 0, 0]] i)))

def SI463N0: IdealEqSpanCertificate' Table ![![463, 0, 0, 0], ![59, 1, 0, 0]] 
 ![![463, 0, 0, 0], ![59, 1, 0, 0], ![223, 0, 1, 0], ![270, 0, 0, 1]] where
  M :=![![![463, 0, 0, 0], ![0, 463, 0, 0], ![0, 0, 463, 0], ![0, 0, 0, 463]], ![![59, 1, 0, 0], ![0, 59, 1, 0], ![0, 0, 59, 1], ![383, 332, 80, 60]]]
  hmulB := by decide  
  f := ![![![17052, -1127, 5218231, 88445], ![-133807, 11112, -40950035, 0]], ![![2124, -200, 681564, 11552], ![-16667, 1852, -5348576, 0]], ![![8150, -570, 2513270, 42598], ![-63953, 5557, -19722874, 0]], ![![9882, -710, 3043028, 51577], ![-77544, 6886, -23880150, 0]]]
  g := ![![![1, 0, 0, 0], ![-59, 463, 0, 0], ![-223, 0, 463, 0], ![-270, 0, 0, 463]], ![![0, 1, 0, 0], ![-8, 59, 1, 0], ![-29, 0, 59, 1], ![-115, 332, 80, 60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI463N0 : Nat.card (O ⧸ I463N0) = 463 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI463N0)

lemma isPrimeI463N0 : Ideal.IsPrime I463N0 := prime_ideal_of_norm_prime hp463.out _ NI463N0

def I463N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![463, 0, 0, 0], ![125, 1, 0, 0]] i)))

def SI463N1: IdealEqSpanCertificate' Table ![![463, 0, 0, 0], ![125, 1, 0, 0]] 
 ![![463, 0, 0, 0], ![125, 1, 0, 0], ![117, 0, 1, 0], ![191, 0, 0, 1]] where
  M :=![![![463, 0, 0, 0], ![0, 463, 0, 0], ![0, 0, 463, 0], ![0, 0, 0, 463]], ![![125, 1, 0, 0], ![0, 125, 1, 0], ![0, 0, 125, 1], ![383, 332, 80, 126]]]
  hmulB := by decide  
  f := ![![![27376, -4406, 8439713, 67518], ![-101397, 17131, -31260834, 0]], ![![7250, -1317, 2314114, 18513], ![-26853, 5093, -8571519, 0]], ![![6784, -1196, 2132615, 17061], ![-25127, 4631, -7899243, 0]], ![![11282, -1876, 3481609, 27853], ![-41787, 7283, -12895938, 0]]]
  g := ![![![1, 0, 0, 0], ![-125, 463, 0, 0], ![-117, 0, 463, 0], ![-191, 0, 0, 463]], ![![0, 1, 0, 0], ![-34, 125, 1, 0], ![-32, 0, 125, 1], ![-161, 332, 80, 126]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI463N1 : Nat.card (O ⧸ I463N1) = 463 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI463N1)

lemma isPrimeI463N1 : Ideal.IsPrime I463N1 := prime_ideal_of_norm_prime hp463.out _ NI463N1

def I463N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![463, 0, 0, 0], ![127, 1, 0, 0]] i)))

def SI463N2: IdealEqSpanCertificate' Table ![![463, 0, 0, 0], ![127, 1, 0, 0]] 
 ![![463, 0, 0, 0], ![127, 1, 0, 0], ![76, 0, 1, 0], ![71, 0, 0, 1]] where
  M :=![![![463, 0, 0, 0], ![0, 463, 0, 0], ![0, 0, 463, 0], ![0, 0, 0, 463]], ![![127, 1, 0, 0], ![0, 127, 1, 0], ![0, 0, 127, 1], ![383, 332, 80, 128]]]
  hmulB := by decide  
  f := ![![![37974, -3898982, -32862, -17], ![-138437, 14215489, 7871, 0]], ![![10287, -1069513, -9057, -5], ![-37502, 3899386, 2315, 0]], ![![5877, -640161, -5422, -3], ![-21425, 2333984, 1389, 0]], ![![5736, -598090, -5091, -3], ![-20911, 2180603, 1390, 0]]]
  g := ![![![1, 0, 0, 0], ![-127, 463, 0, 0], ![-76, 0, 463, 0], ![-71, 0, 0, 463]], ![![0, 1, 0, 0], ![-35, 127, 1, 0], ![-21, 0, 127, 1], ![-123, 332, 80, 128]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI463N2 : Nat.card (O ⧸ I463N2) = 463 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI463N2)

lemma isPrimeI463N2 : Ideal.IsPrime I463N2 := prime_ideal_of_norm_prime hp463.out _ NI463N2

def I463N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![463, 0, 0, 0], ![151, 1, 0, 0]] i)))

def SI463N3: IdealEqSpanCertificate' Table ![![463, 0, 0, 0], ![151, 1, 0, 0]] 
 ![![463, 0, 0, 0], ![151, 1, 0, 0], ![349, 0, 1, 0], ![83, 0, 0, 1]] where
  M :=![![![463, 0, 0, 0], ![0, 463, 0, 0], ![0, 0, 463, 0], ![0, 0, 0, 463]], ![![151, 1, 0, 0], ![0, 151, 1, 0], ![0, 0, 151, 1], ![383, 332, 80, 152]]]
  hmulB := by decide  
  f := ![![![12987, -321242, -2430, -2], ![-39818, 985264, 926, 0]], ![![4077, -104767, -845, -1], ![-12500, 321322, 463, 0]], ![![9714, -242291, -1907, -2], ![-29783, 743116, 926, 0]], ![![2379, -57768, -534, -1], ![-7294, 177178, 464, 0]]]
  g := ![![![1, 0, 0, 0], ![-151, 463, 0, 0], ![-349, 0, 463, 0], ![-83, 0, 0, 463]], ![![0, 1, 0, 0], ![-50, 151, 1, 0], ![-114, 0, 151, 1], ![-195, 332, 80, 152]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI463N3 : Nat.card (O ⧸ I463N3) = 463 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI463N3)

lemma isPrimeI463N3 : Ideal.IsPrime I463N3 := prime_ideal_of_norm_prime hp463.out _ NI463N3
def MulI463N0 : IdealMulLeCertificate' Table 
  ![![463, 0, 0, 0], ![59, 1, 0, 0]] ![![463, 0, 0, 0], ![125, 1, 0, 0]]
  ![![463, 0, 0, 0], ![-278, 100, -4, 1]] where
 M :=  ![![![214369, 0, 0, 0], ![57875, 463, 0, 0]], ![![27317, 463, 0, 0], ![7375, 184, 1, 0]]]
 hmul := by decide  
 g :=  ![![![![9696685047, 2942113040, 5990224072, -89276698], ![-5238697766, -15524602980, 0, 0]], ![![2617846479, 794292021, 1617200752, -24102328], ![-1414308506, -4191228790, 0, 0]]], ![![![1235597629, 374897941, 763302720, -11376060], ![-667539510, -1978218430, 0, 0]], ![![333578459, 101212428, 206071379, -3071233], ![-180217781, -534066220, 0, 0]]]]
 hle2 := by decide  

def MulI463N1 : IdealMulLeCertificate' Table 
  ![![463, 0, 0, 0], ![-278, 100, -4, 1]] ![![463, 0, 0, 0], ![127, 1, 0, 0]]
  ![![463, 0, 0, 0], ![-15892, -8451, -487, 122]] where
 M :=  ![![![214369, 0, 0, 0], ![58801, 463, 0, 0]], ![![-128714, 46300, -1852, 463], ![-34923, 12754, -328, 124]]]
 hmul := by decide  
 g :=  ![![![![463, 0, 0, 0], ![0, 0, 0, 0]], ![![127, 1, 0, 0], ![0, 0, 0, 0]]], ![![![15614, 8551, 483, -121], ![463, 0, 0, 0]], ![![5691, 3094, 176, -44], ![168, 0, 0, 0]]]]
 hle2 := by decide  

def MulI463N2 : IdealMulLeCertificate' Table 
  ![![463, 0, 0, 0], ![-15892, -8451, -487, 122]] ![![463, 0, 0, 0], ![151, 1, 0, 0]]
  ![![463, 0, 0, 0]] where
 M :=  ![![![214369, 0, 0, 0], ![69913, 463, 0, 0]], ![![-7357996, -3912813, -225481, 56486], ![-2352966, -1251489, -72228, 18057]]]
 hmul := by decide  
 g :=  ![![![![463, 0, 0, 0]], ![![151, 1, 0, 0]]], ![![![-15892, -8451, -487, 122]], ![![-5082, -2703, -156, 39]]]]
 hle2 := by decide  


def PBC463 : ContainsPrimesAboveP 463 ![I463N0, I463N1, I463N2, I463N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI463N0
    exact isPrimeI463N1
    exact isPrimeI463N2
    exact isPrimeI463N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 463 (by decide) (𝕀 ⊙ MulI463N0 ⊙ MulI463N1 ⊙ MulI463N2)


lemma PB692I8_primes (p : ℕ) :
  p ∈ Set.range ![419, 421, 431, 433, 439, 443, 449, 457, 461, 463] ↔ Nat.Prime p ∧ 409 < p ∧ p ≤ 463 := by
  rw [← List.mem_ofFn']
  convert primes_range 409 463 (by omega)
  rfl

def PB692I8 : PrimesBelowBoundCertificateInterval' O 409 463 692 where
  m := 10
  g := ![2, 3, 3, 3, 3, 2, 3, 3, 2, 4]
  P := ![419, 421, 431, 433, 439, 443, 449, 457, 461, 463]
  hP := PB692I8_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I419N0, I419N1]
    · exact ![I421N0, I421N1, I421N2]
    · exact ![I431N0, I431N1, I431N2]
    · exact ![I433N0, I433N1, I433N2]
    · exact ![I439N0, I439N1, I439N2]
    · exact ![I443N0, I443N1]
    · exact ![I449N0, I449N1, I449N2]
    · exact ![I457N0, I457N1, I457N2]
    · exact ![I461N0, I461N1]
    · exact ![I463N0, I463N1, I463N2, I463N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC419
    · exact PBC421
    · exact PBC431
    · exact PBC433
    · exact PBC439
    · exact PBC443
    · exact PBC449
    · exact PBC457
    · exact PBC461
    · exact PBC463
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![175561, 175561]
    · exact ![177241, 421, 421]
    · exact ![185761, 431, 431]
    · exact ![187489, 433, 433]
    · exact ![192721, 439, 439]
    · exact ![196249, 196249]
    · exact ![201601, 449, 449]
    · exact ![208849, 457, 457]
    · exact ![212521, 212521]
    · exact ![463, 463, 463, 463]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI419N0
      exact NI419N1
    · dsimp ; intro j
      fin_cases j
      exact NI421N0
      exact NI421N1
      exact NI421N2
    · dsimp ; intro j
      fin_cases j
      exact NI431N0
      exact NI431N1
      exact NI431N2
    · dsimp ; intro j
      fin_cases j
      exact NI433N0
      exact NI433N1
      exact NI433N2
    · dsimp ; intro j
      fin_cases j
      exact NI439N0
      exact NI439N1
      exact NI439N2
    · dsimp ; intro j
      fin_cases j
      exact NI443N0
      exact NI443N1
    · dsimp ; intro j
      fin_cases j
      exact NI449N0
      exact NI449N1
      exact NI449N2
    · dsimp ; intro j
      fin_cases j
      exact NI457N0
      exact NI457N1
      exact NI457N2
    · dsimp ; intro j
      fin_cases j
      exact NI461N0
      exact NI461N1
    · dsimp ; intro j
      fin_cases j
      exact NI463N0
      exact NI463N1
      exact NI463N2
      exact NI463N3
  Il := ![[], [I421N1, I421N2], [I431N1, I431N2], [I433N1, I433N2], [I439N1, I439N2], [], [I449N1, I449N2], [I457N1, I457N2], [], [I463N0, I463N1, I463N2, I463N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
