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
instance hp607 : Fact (Nat.Prime 607) := {out := by norm_num}

def I607N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![361, 201, 12, -3]] i)))

def SI607N0: IdealEqSpanCertificate' Table ![![361, 201, 12, -3]] 
 ![![607, 0, 0, 0], ![0, 607, 0, 0], ![22, 213, 1, 0], ![170, 178, 0, 1]] where
  M :=![![![361, 201, 12, -3], ![-1149, -635, -39, 9], ![3447, 1839, 85, -30], ![-11490, -6513, -561, 55]]]
  hmulB := by decide  
  f := ![![![-428, -201, -12, 3]], ![![1149, 568, 39, -9]], ![![382, 189, 13, -3]], ![![236, 121, 9, -2]]]
  g := ![![![1, -3, 12, -3], ![-3, 10, -39, 9], ![11, -18, 85, -30], ![-14, 170, -561, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P607P0 : CertificateIrreducibleZModOfList' 607 2 2 9 [345, 134, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [473, 606], [0, 1]]
 g := ![![[208, 188], [489, 423], [224, 420], [98, 394], [74, 586], [104], [493, 542], [353], [1]],![[510, 419], [258, 184], [395, 187], [111, 213], [460, 21], [104], [98, 65], [353], [1]]]
 h' := ![![[473, 606], [41, 443], [416, 246], [182, 342], [571, 159], [383, 250], [482, 424], [275, 240], [262, 473], [0, 1]],![[0, 1], [165, 164], [230, 361], [486, 265], [510, 448], [268, 357], [117, 183], [286, 367], [8, 134], [473, 606]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [185]]
 b := ![[], [431, 396]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI607N0 : CertifiedPrimeIdeal' SI607N0 607 where 
  n := 2
  hpos := by decide  
  P := [345, 134, 1]
  hirr := P607P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![33283, 29567, 8126, 526]
  a := ![0, -1, -1, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-387, -2957, 8126, 526]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI607N0 : Ideal.IsPrime I607N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI607N0 B_one_repr
lemma NI607N0 : Nat.card (O ⧸ I607N0) = 368449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI607N0

def I607N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![607, 0, 0, 0], ![90, 1, 0, 0]] i)))

def SI607N1: IdealEqSpanCertificate' Table ![![607, 0, 0, 0], ![90, 1, 0, 0]] 
 ![![607, 0, 0, 0], ![90, 1, 0, 0], ![398, 0, 1, 0], ![600, 0, 0, 1]] where
  M :=![![![607, 0, 0, 0], ![0, 607, 0, 0], ![0, 0, 607, 0], ![0, 0, 0, 607]], ![![90, 1, 0, 0], ![0, 90, 1, 0], ![0, 0, 90, 1], ![383, 332, 80, 91]]]
  hmulB := by decide  
  f := ![![![24031, -1623, 7788669, 86541], ![-162069, 12747, -52530387, 0]], ![![3510, -321, 1169726, 12997], ![-23672, 2428, -7889179, 0]], ![![15854, -1084, 5106856, 56743], ![-106922, 8499, -34443001, 0]], ![![23820, -1612, 7698849, 85543], ![-160646, 12657, -51924600, 0]]]
  g := ![![![1, 0, 0, 0], ![-90, 607, 0, 0], ![-398, 0, 607, 0], ![-600, 0, 0, 607]], ![![0, 1, 0, 0], ![-14, 90, 1, 0], ![-60, 0, 90, 1], ![-191, 332, 80, 91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI607N1 : Nat.card (O ⧸ I607N1) = 607 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI607N1)

lemma isPrimeI607N1 : Ideal.IsPrime I607N1 := prime_ideal_of_norm_prime hp607.out _ NI607N1

def I607N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![607, 0, 0, 0], ![303, 1, 0, 0]] i)))

def SI607N2: IdealEqSpanCertificate' Table ![![607, 0, 0, 0], ![303, 1, 0, 0]] 
 ![![607, 0, 0, 0], ![303, 1, 0, 0], ![455, 0, 1, 0], ![531, 0, 0, 1]] where
  M :=![![![607, 0, 0, 0], ![0, 607, 0, 0], ![0, 0, 607, 0], ![0, 0, 0, 607]], ![![303, 1, 0, 0], ![0, 303, 1, 0], ![0, 0, 303, 1], ![383, 332, 80, 304]]]
  hmulB := by decide  
  f := ![![![37270, -72597, 110538705, 364815], ![-74661, 145680, -221442705, 0]], ![![18180, -36603, 55361009, 182710], ![-36419, 73447, -110904970, 0]], ![![27422, -54450, 82858200, 273460], ![-54933, 109261, -165990220, 0]], ![![32346, -63675, 96698603, 319138], ![-64797, 127774, -193716765, 0]]]
  g := ![![![1, 0, 0, 0], ![-303, 607, 0, 0], ![-455, 0, 607, 0], ![-531, 0, 0, 607]], ![![0, 1, 0, 0], ![-152, 303, 1, 0], ![-228, 0, 303, 1], ![-491, 332, 80, 304]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI607N2 : Nat.card (O ⧸ I607N2) = 607 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI607N2)

lemma isPrimeI607N2 : Ideal.IsPrime I607N2 := prime_ideal_of_norm_prime hp607.out _ NI607N2
def MulI607N0 : IdealMulLeCertificate' Table 
  ![![361, 201, 12, -3]] ![![607, 0, 0, 0], ![90, 1, 0, 0]]
  ![![607, 0, 0, 0], ![-11661, -6223, -347, 87]] where
 M :=  ![![![219127, 122007, 7284, -1821], ![31341, 17455, 1041, -261]]]
 hmul := by decide  
 g :=  ![![![![361, 201, 12, -3], ![0, 0, 0, 0]], ![![11655, 6221, 347, -87], ![604, 0, 0, 0]]]]
 hle2 := by decide  

def MulI607N1 : IdealMulLeCertificate' Table 
  ![![607, 0, 0, 0], ![-11661, -6223, -347, 87]] ![![607, 0, 0, 0], ![303, 1, 0, 0]]
  ![![607, 0, 0, 0]] where
 M :=  ![![![368449, 0, 0, 0], ![183921, 607, 0, 0]], ![![-7078227, -3777361, -210629, 52809], ![-3499962, -1868346, -104404, 26101]]]
 hmul := by decide  
 g :=  ![![![![607, 0, 0, 0]], ![![303, 1, 0, 0]]], ![![![-11661, -6223, -347, 87]], ![![-5766, -3078, -172, 43]]]]
 hle2 := by decide  


def PBC607 : ContainsPrimesAboveP 607 ![I607N0, I607N1, I607N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI607N0
    exact isPrimeI607N1
    exact isPrimeI607N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 607 (by decide) (𝕀 ⊙ MulI607N0 ⊙ MulI607N1)
instance hp613 : Fact (Nat.Prime 613) := {out := by norm_num}

def I613N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![613, 0, 0, 0], ![-91, -224, -4, 1]] i)))

def SI613N0: IdealEqSpanCertificate' Table ![![613, 0, 0, 0], ![-91, -224, -4, 1]] 
 ![![613, 0, 0, 0], ![0, 613, 0, 0], ![573, 101, 1, 0], ![362, 180, 0, 1]] where
  M :=![![![613, 0, 0, 0], ![0, 613, 0, 0], ![0, 0, 613, 0], ![0, 0, 0, 613]], ![![-91, -224, -4, 1], ![383, 241, -144, -3], ![-1149, -613, 1, -147], ![-56301, -49953, -12373, -146]]]
  hmulB := by decide  
  f := ![![![33863880, 18160072, -13453708, -259829], ![-11575279, -56950152, 0, 0]], ![![-71428, -38275, 28384, 548], ![24520, 120148, 0, 0]], ![![31642385, 16968741, -12571139, -242784], ![-10815996, -53214196, 0, 0]], ![![19976939, 10712964, -7936596, -153278], ![-6828489, -33595968, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-573, -101, 613, 0], ![-362, -180, 0, 613]], ![![3, 0, -4, 1], ![137, 25, -144, -3], ![84, 42, 1, -147], ![11560, 2000, -12373, -146]]]
  hle1 := by decide   
  hle2 := by decide  


def P613P0 : CertificateIrreducibleZModOfList' 613 2 2 9 [396, 250, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [363, 612], [0, 1]]
 g := ![![[561, 583], [455], [568, 48], [138], [357], [138, 175], [582, 329], [587], [1]],![[92, 30], [455], [215, 565], [138], [357], [524, 438], [474, 284], [587], [1]]]
 h' := ![![[363, 612], [52, 116], [43, 41], [518, 50], [543, 410], [522, 53], [16, 452], [376, 371], [217, 363], [0, 1]],![[0, 1], [476, 497], [214, 572], [278, 563], [414, 203], [145, 560], [421, 161], [189, 242], [191, 250], [363, 612]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [530]]
 b := ![[], [23, 265]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI613N0 : CertifiedPrimeIdeal' SI613N0 613 where 
  n := 2
  hpos := by decide  
  P := [396, 250, 1]
  hirr := P613P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![1552965, 1298357, 266884, -5911]
  a := ![-2, 3, -64, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-243445, -40119, 266884, -5911]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI613N0 : Ideal.IsPrime I613N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI613N0 B_one_repr
lemma NI613N0 : Nat.card (O ⧸ I613N0) = 375769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI613N0

def I613N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![613, 0, 0, 0], ![-257, -347, -4, 1]] i)))

def SI613N1: IdealEqSpanCertificate' Table ![![613, 0, 0, 0], ![-257, -347, -4, 1]] 
 ![![613, 0, 0, 0], ![0, 613, 0, 0], ![454, 511, 1, 0], ![333, 471, 0, 1]] where
  M :=![![![613, 0, 0, 0], ![0, 613, 0, 0], ![0, 0, 613, 0], ![0, 0, 0, 613]], ![![-257, -347, -4, 1], ![383, 75, -267, -3], ![-1149, -613, -165, -270], ![-103410, -90789, -22213, -435]]]
  hmulB := by decide  
  f := ![![![28050020, -98881, -23006687, -238807], ![-11553824, -52647505, 0, 0]], ![![-62868, 447, 51703, 536], ![26359, 118309, 0, 0]], ![![20721892, -73001, -16996112, -176418], ![-8535267, -38893167, 0, 0]], ![![15189233, -53473, -12458198, -129315], ![-6256310, -28508802, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-454, -511, 613, 0], ![-333, -471, 0, 613]], ![![2, 2, -4, 1], ![200, 225, -267, -3], ![267, 344, -165, -270], ![16519, 18703, -22213, -435]]]
  hle1 := by decide   
  hle2 := by decide  


def P613P1 : CertificateIrreducibleZModOfList' 613 2 2 9 [209, 595, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 612], [0, 1]]
 g := ![![[434, 566], [75], [337, 513], [564], [577], [438, 564], [81, 154], [324], [1]],![[201, 47], [75], [376, 100], [564], [577], [169, 49], [401, 459], [324], [1]]]
 h' := ![![[18, 612], [429, 343], [62, 244], [215, 263], [509, 245], [408, 403], [235, 368], [485, 147], [404, 18], [0, 1]],![[0, 1], [473, 270], [163, 369], [45, 350], [15, 368], [306, 210], [116, 245], [66, 466], [115, 595], [18, 612]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [510, 352]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI613N1 : CertifiedPrimeIdeal' SI613N1 613 where 
  n := 2
  hpos := by decide  
  P := [209, 595, 1]
  hirr := P613P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![274609, 240118, 62477, 2169]
  a := ![-1, 1, 1, -3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-47002, -53356, 62477, 2169]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI613N1 : Ideal.IsPrime I613N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI613N1 B_one_repr
lemma NI613N1 : Nat.card (O ⧸ I613N1) = 375769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI613N1
def MulI613N0 : IdealMulLeCertificate' Table 
  ![![613, 0, 0, 0], ![-91, -224, -4, 1]] ![![613, 0, 0, 0], ![-257, -347, -4, 1]]
  ![![613, 0, 0, 0]] where
 M :=  ![![![375769, 0, 0, 0], ![-157541, -212711, -2452, 613]], ![![-55783, -137312, -2452, 613], ![-161219, -73560, 38619, 1226]]]
 hmul := by decide  
 g :=  ![![![![613, 0, 0, 0]], ![![-257, -347, -4, 1]]], ![![![-91, -224, -4, 1]], ![![-263, -120, 63, 2]]]]
 hle2 := by decide  


def PBC613 : ContainsPrimesAboveP 613 ![I613N0, I613N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI613N0
    exact isPrimeI613N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 613 (by decide) (𝕀 ⊙ MulI613N0)
instance hp617 : Fact (Nat.Prime 617) := {out := by norm_num}

def I617N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![617, 0, 0, 0], ![35, 1, 0, 0]] i)))

def SI617N0: IdealEqSpanCertificate' Table ![![617, 0, 0, 0], ![35, 1, 0, 0]] 
 ![![617, 0, 0, 0], ![35, 1, 0, 0], ![9, 0, 1, 0], ![302, 0, 0, 1]] where
  M :=![![![617, 0, 0, 0], ![0, 617, 0, 0], ![0, 0, 617, 0], ![0, 0, 0, 617]], ![![35, 1, 0, 0], ![0, 35, 1, 0], ![0, 0, 35, 1], ![383, 332, 80, 36]]]
  hmulB := by decide  
  f := ![![![31116, -7930741, -227353, -21], ![-548513, 139823306, 12957, 0]], ![![1680, -449912, -12926, -2], ![-29615, 7932152, 1234, 0]], ![![387, -115734, -3342, -1], ![-6822, 2040420, 617, 0]], ![![15156, -3881870, -111308, -11], ![-267170, 68439456, 6788, 0]]]
  g := ![![![1, 0, 0, 0], ![-35, 617, 0, 0], ![-9, 0, 617, 0], ![-302, 0, 0, 617]], ![![0, 1, 0, 0], ![-2, 35, 1, 0], ![-1, 0, 35, 1], ![-37, 332, 80, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI617N0 : Nat.card (O ⧸ I617N0) = 617 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI617N0)

lemma isPrimeI617N0 : Ideal.IsPrime I617N0 := prime_ideal_of_norm_prime hp617.out _ NI617N0

def I617N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![617, 0, 0, 0], ![236, 1, 0, 0]] i)))

def SI617N1: IdealEqSpanCertificate' Table ![![617, 0, 0, 0], ![236, 1, 0, 0]] 
 ![![617, 0, 0, 0], ![236, 1, 0, 0], ![451, 0, 1, 0], ![305, 0, 0, 1]] where
  M :=![![![617, 0, 0, 0], ![0, 617, 0, 0], ![0, 0, 617, 0], ![0, 0, 0, 617]], ![![236, 1, 0, 0], ![0, 236, 1, 0], ![0, 0, 236, 1], ![383, 332, 80, 237]]]
  hmulB := by decide  
  f := ![![![84017, -11136248, -53325, -26], ![-219652, 29115613, 16042, 0]], ![![32096, -4259428, -20409, -10], ![-83911, 11136233, 6170, 0]], ![![61687, -8139851, -38976, -19], ![-161273, 21281565, 11723, 0]], ![![41237, -5504907, -26395, -13], ![-107809, 14392523, 8022, 0]]]
  g := ![![![1, 0, 0, 0], ![-236, 617, 0, 0], ![-451, 0, 617, 0], ![-305, 0, 0, 617]], ![![0, 1, 0, 0], ![-91, 236, 1, 0], ![-173, 0, 236, 1], ![-302, 332, 80, 237]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI617N1 : Nat.card (O ⧸ I617N1) = 617 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI617N1)

lemma isPrimeI617N1 : Ideal.IsPrime I617N1 := prime_ideal_of_norm_prime hp617.out _ NI617N1

def I617N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![617, 0, 0, 0], ![-140, 1, 0, 0]] i)))

def SI617N2: IdealEqSpanCertificate' Table ![![617, 0, 0, 0], ![-140, 1, 0, 0]] 
 ![![617, 0, 0, 0], ![477, 1, 0, 0], ![144, 0, 1, 0], ![416, 0, 0, 1]] where
  M :=![![![617, 0, 0, 0], ![0, 617, 0, 0], ![0, 0, 617, 0], ![0, 0, 0, 617]], ![![-140, 1, 0, 0], ![0, -140, 1, 0], ![0, 0, -140, 1], ![383, 332, 80, -139]]]
  hmulB := by decide  
  f := ![![![22541, 119, 499798, -3570], ![99337, 1234, 2202690, 0]], ![![17641, 14, 399839, -2856], ![77743, 617, 1762152, 0]], ![![5352, 102, 116619, -833], ![23586, 618, 513961, 0]], ![![15368, 62, 336979, -2407], ![67726, 757, 1485120, 0]]]
  g := ![![![1, 0, 0, 0], ![-477, 617, 0, 0], ![-144, 0, 617, 0], ![-416, 0, 0, 617]], ![![-1, 1, 0, 0], ![108, -140, 1, 0], ![32, 0, -140, 1], ![-181, 332, 80, -139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI617N2 : Nat.card (O ⧸ I617N2) = 617 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI617N2)

lemma isPrimeI617N2 : Ideal.IsPrime I617N2 := prime_ideal_of_norm_prime hp617.out _ NI617N2

def I617N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![617, 0, 0, 0], ![-132, 1, 0, 0]] i)))

def SI617N3: IdealEqSpanCertificate' Table ![![617, 0, 0, 0], ![-132, 1, 0, 0]] 
 ![![617, 0, 0, 0], ![485, 1, 0, 0], ![469, 0, 1, 0], ![208, 0, 0, 1]] where
  M :=![![![617, 0, 0, 0], ![0, 617, 0, 0], ![0, 0, 617, 0], ![0, 0, 0, 617]], ![![-132, 1, 0, 0], ![0, -132, 1, 0], ![0, 0, -132, 1], ![383, 332, 80, -131]]]
  hmulB := by decide  
  f := ![![![33925, 2647, 8516750, -64521], ![158569, 13574, 39809457, 0]], ![![26665, 2042, 6712579, -50853], ![124635, 10489, 31376301, 0]], ![![25769, 2049, 6473791, -49044], ![120447, 10490, 30260148, 0]], ![![11648, 864, 2871125, -21751], ![54444, 4451, 13420368, 0]]]
  g := ![![![1, 0, 0, 0], ![-485, 617, 0, 0], ![-469, 0, 617, 0], ![-208, 0, 0, 617]], ![![-1, 1, 0, 0], ![103, -132, 1, 0], ![100, 0, -132, 1], ![-277, 332, 80, -131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI617N3 : Nat.card (O ⧸ I617N3) = 617 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI617N3)

lemma isPrimeI617N3 : Ideal.IsPrime I617N3 := prime_ideal_of_norm_prime hp617.out _ NI617N3
def MulI617N0 : IdealMulLeCertificate' Table 
  ![![617, 0, 0, 0], ![35, 1, 0, 0]] ![![617, 0, 0, 0], ![236, 1, 0, 0]]
  ![![-94, 21, 10, -1]] where
 M :=  ![![![380689, 0, 0, 0], ![145612, 617, 0, 0]], ![![21595, 617, 0, 0], ![8260, 271, 1, 0]]]
 hmul := by decide  
 g :=  ![![![![48743, 28999, 1234, -617]], ![![18261, 10839, 439, -235]]], ![![![2382, 1392, 37, -34]], ![![890, 518, 12, -13]]]]
 hle2 := by decide  

def MulI617N1 : IdealMulLeCertificate' Table 
  ![![-94, 21, 10, -1]] ![![617, 0, 0, 0], ![-140, 1, 0, 0]]
  ![![617, 0, 0, 0], ![-3927, -2048, -127, 32]] where
 M :=  ![![![-57998, 12957, 6170, -617], ![12777, -3366, -1459, 149]]]
 hmul := by decide  
 g :=  ![![![![3833, 2069, 137, -33], ![617, 0, 0, 0]], ![![2382, 1226, 74, -19], ![371, 0, 0, 0]]]]
 hle2 := by decide  

def MulI617N2 : IdealMulLeCertificate' Table 
  ![![617, 0, 0, 0], ![-3927, -2048, -127, 32]] ![![617, 0, 0, 0], ![-132, 1, 0, 0]]
  ![![617, 0, 0, 0]] where
 M :=  ![![![380689, 0, 0, 0], ![-81444, 617, 0, 0]], ![![-2422959, -1263616, -78359, 19744], ![530620, 277033, 17276, -4319]]]
 hmul := by decide  
 g :=  ![![![![617, 0, 0, 0]], ![![-132, 1, 0, 0]]], ![![![-3927, -2048, -127, 32]], ![![860, 449, 28, -7]]]]
 hle2 := by decide  


def PBC617 : ContainsPrimesAboveP 617 ![I617N0, I617N1, I617N2, I617N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI617N0
    exact isPrimeI617N1
    exact isPrimeI617N2
    exact isPrimeI617N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 617 (by decide) (𝕀 ⊙ MulI617N0 ⊙ MulI617N1 ⊙ MulI617N2)
instance hp619 : Fact (Nat.Prime 619) := {out := by norm_num}

def I619N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![629, 335, 20, -5]] i)))

def SI619N0: IdealEqSpanCertificate' Table ![![629, 335, 20, -5]] 
 ![![619, 0, 0, 0], ![0, 619, 0, 0], ![377, 129, 1, 0], ![268, 449, 0, 1]] where
  M :=![![![629, 335, 20, -5], ![-1915, -1031, -65, 15], ![5745, 3065, 169, -50], ![-19150, -10855, -935, 119]]]
  hmulB := by decide  
  f := ![![![686, 335, 20, -5]], ![![-1915, -974, -65, 15]], ![![28, 6, -1, 0]], ![![-1123, -579, -40, 9]]]
  g := ![![![-9, 0, 20, -5], ![30, 1, -65, 15], ![-72, 6, 169, -50], ![487, 91, -935, 119]]]
  hle1 := by decide   
  hle2 := by decide  


def P619P0 : CertificateIrreducibleZModOfList' 619 2 2 9 [446, 465, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [154, 618], [0, 1]]
 g := ![![[602, 186], [192, 379], [194], [476, 247], [528], [605, 207], [365, 609], [194], [1]],![[153, 433], [372, 240], [194], [136, 372], [528], [295, 412], [63, 10], [194], [1]]]
 h' := ![![[154, 618], [409, 335], [577, 442], [21, 154], [172, 535], [54, 278], [7, 198], [353, 214], [173, 154], [0, 1]],![[0, 1], [3, 284], [555, 177], [215, 465], [235, 84], [155, 341], [168, 421], [502, 405], [367, 465], [154, 618]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [204]]
 b := ![[], [193, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI619N0 : CertifiedPrimeIdeal' SI619N0 619 where 
  n := 2
  hpos := by decide  
  P := [446, 465, 1]
  hirr := P619P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![30320, 25048, 5827, 797]
  a := ![0, -1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-3845, -1752, 5827, 797]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI619N0 : Ideal.IsPrime I619N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI619N0 B_one_repr
lemma NI619N0 : Nat.card (O ⧸ I619N0) = 383161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI619N0

def I619N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![619, 0, 0, 0], ![217, 1, 0, 0]] i)))

def SI619N1: IdealEqSpanCertificate' Table ![![619, 0, 0, 0], ![217, 1, 0, 0]] 
 ![![619, 0, 0, 0], ![217, 1, 0, 0], ![574, 0, 1, 0], ![480, 0, 0, 1]] where
  M :=![![![619, 0, 0, 0], ![0, 619, 0, 0], ![0, 0, 619, 0], ![0, 0, 0, 619]], ![![217, 1, 0, 0], ![0, 217, 1, 0], ![0, 0, 217, 1], ![383, 332, 80, 218]]]
  hmulB := by decide  
  f := ![![![53166, -2576, 5311062, 24475], ![-151655, 8047, -15150025, 0]], ![![18228, -1001, 1931295, 8900], ![-51995, 3095, -5509100, 0]], ![![49336, -2377, 4924803, 22695], ![-140730, 7429, -14048205, 0]], ![![40998, -1905, 4118433, 18979], ![-116946, 5973, -11748000, 0]]]
  g := ![![![1, 0, 0, 0], ![-217, 619, 0, 0], ![-574, 0, 619, 0], ![-480, 0, 0, 619]], ![![0, 1, 0, 0], ![-77, 217, 1, 0], ![-202, 0, 217, 1], ![-359, 332, 80, 218]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI619N1 : Nat.card (O ⧸ I619N1) = 619 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI619N1)

lemma isPrimeI619N1 : Ideal.IsPrime I619N1 := prime_ideal_of_norm_prime hp619.out _ NI619N1

def I619N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![619, 0, 0, 0], ![272, 1, 0, 0]] i)))

def SI619N2: IdealEqSpanCertificate' Table ![![619, 0, 0, 0], ![272, 1, 0, 0]] 
 ![![619, 0, 0, 0], ![272, 1, 0, 0], ![296, 0, 1, 0], ![577, 0, 0, 1]] where
  M :=![![![619, 0, 0, 0], ![0, 619, 0, 0], ![0, 0, 619, 0], ![0, 0, 0, 619]], ![![272, 1, 0, 0], ![0, 272, 1, 0], ![0, 0, 272, 1], ![383, 332, 80, 273]]]
  hmulB := by decide  
  f := ![![![33457, -1197765, -5220, -3], ![-76137, 2726076, 1857, 0]], ![![14144, -526540, -2480, -2], ![-32187, 1198384, 1238, 0]], ![![15896, -573046, -2651, -2], ![-36174, 1304234, 1238, 0]], ![![31411, -1116597, -4922, -3], ![-71481, 2541342, 1858, 0]]]
  g := ![![![1, 0, 0, 0], ![-272, 619, 0, 0], ![-296, 0, 619, 0], ![-577, 0, 0, 619]], ![![0, 1, 0, 0], ![-120, 272, 1, 0], ![-131, 0, 272, 1], ![-438, 332, 80, 273]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI619N2 : Nat.card (O ⧸ I619N2) = 619 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI619N2)

lemma isPrimeI619N2 : Ideal.IsPrime I619N2 := prime_ideal_of_norm_prime hp619.out _ NI619N2
def MulI619N0 : IdealMulLeCertificate' Table 
  ![![629, 335, 20, -5]] ![![619, 0, 0, 0], ![217, 1, 0, 0]]
  ![![619, 0, 0, 0], ![-27906, -14828, -855, 214]] where
 M :=  ![![![389351, 207365, 12380, -3095], ![134578, 71664, 4275, -1070]]]
 hmul := by decide  
 g :=  ![![![![629, 335, 20, -5], ![0, 0, 0, 0]], ![![27898, 14824, 855, -214], ![614, 0, 0, 0]]]]
 hle2 := by decide  

def MulI619N1 : IdealMulLeCertificate' Table 
  ![![619, 0, 0, 0], ![-27906, -14828, -855, 214]] ![![619, 0, 0, 0], ![272, 1, 0, 0]]
  ![![619, 0, 0, 0]] where
 M :=  ![![![383161, 0, 0, 0], ![168368, 619, 0, 0]], ![![-17273814, -9178532, -529245, 132466], ![-7508470, -3990074, -230268, 57567]]]
 hmul := by decide  
 g :=  ![![![![619, 0, 0, 0]], ![![272, 1, 0, 0]]], ![![![-27906, -14828, -855, 214]], ![![-12130, -6446, -372, 93]]]]
 hle2 := by decide  


def PBC619 : ContainsPrimesAboveP 619 ![I619N0, I619N1, I619N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI619N0
    exact isPrimeI619N1
    exact isPrimeI619N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 619 (by decide) (𝕀 ⊙ MulI619N0 ⊙ MulI619N1)
instance hp631 : Fact (Nat.Prime 631) := {out := by norm_num}

def I631N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![631, 0, 0, 0], ![13, -67, -4, 1]] i)))

def SI631N0: IdealEqSpanCertificate' Table ![![631, 0, 0, 0], ![13, -67, -4, 1]] 
 ![![631, 0, 0, 0], ![0, 631, 0, 0], ![422, 144, 1, 0], ![439, 509, 0, 1]] where
  M :=![![![631, 0, 0, 0], ![0, 631, 0, 0], ![0, 0, 631, 0], ![0, 0, 0, 631]], ![![13, -67, -4, 1], ![383, 345, 13, -3], ![-1149, -613, 105, 10], ![3830, 2171, 187, 115]]]
  hmulB := by decide  
  f := ![![![8047269, 7174306, 268939, -61990], ![-597557, -13237749, 0, 0]], ![![-42591, -37892, -1419, 327], ![3786, 70041, 0, 0]], ![![5372131, 4789381, 179537, -41383], ![-398789, -8837154, 0, 0]], ![![5564311, 4960685, 185958, -42863], ![-413292, -9153282, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-422, -144, 631, 0], ![-439, -509, 0, 631]], ![![2, 0, -4, 1], ![-6, 0, 13, -3], ![-79, -33, 105, 10], ![-199, -132, 187, 115]]]
  hle1 := by decide   
  hle2 := by decide  


def P631P0 : CertificateIrreducibleZModOfList' 631 2 2 9 [129, 247, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [384, 630], [0, 1]]
 g := ![![[584, 558], [51, 331], [453, 177], [344], [23, 72], [78, 385], [515, 160], [433], [1]],![[316, 73], [324, 300], [273, 454], [344], [538, 559], [264, 246], [117, 471], [433], [1]]]
 h' := ![![[384, 630], [362, 172], [246, 392], [433, 290], [188, 69], [34, 67], [451, 442], [537, 314], [502, 384], [0, 1]],![[0, 1], [155, 459], [596, 239], [106, 341], [182, 562], [522, 564], [440, 189], [592, 317], [304, 247], [384, 630]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [479]]
 b := ![[], [79, 555]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI631N0 : CertifiedPrimeIdeal' SI631N0 631 where 
  n := 2
  hpos := by decide  
  P := [129, 247, 1]
  hirr := P631P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![284773, 243794, 62559, 4811]
  a := ![19, 1, -1, 3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-44734, -17771, 62559, 4811]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI631N0 : Ideal.IsPrime I631N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI631N0 B_one_repr
lemma NI631N0 : Nat.card (O ⧸ I631N0) = 398161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI631N0

def I631N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![631, 0, 0, 0], ![191, 1, 0, 0]] i)))

def SI631N1: IdealEqSpanCertificate' Table ![![631, 0, 0, 0], ![191, 1, 0, 0]] 
 ![![631, 0, 0, 0], ![191, 1, 0, 0], ![117, 0, 1, 0], ![369, 0, 0, 1]] where
  M :=![![![631, 0, 0, 0], ![0, 631, 0, 0], ![0, 0, 631, 0], ![0, 0, 0, 631]], ![![191, 1, 0, 0], ![0, 191, 1, 0], ![0, 0, 191, 1], ![383, 332, 80, 192]]]
  hmulB := by decide  
  f := ![![![119949, -38028236, -215912, -88], ![-396268, 125634624, 55528, 0]], ![![36099, -11510999, -65425, -27], ![-119258, 38029108, 17037, 0]], ![![22023, -7051414, -40166, -17], ![-72756, 23295890, 10727, 0]], ![![69942, -22238661, -126367, -52], ![-231063, 73470294, 32813, 0]]]
  g := ![![![1, 0, 0, 0], ![-191, 631, 0, 0], ![-117, 0, 631, 0], ![-369, 0, 0, 631]], ![![0, 1, 0, 0], ![-58, 191, 1, 0], ![-36, 0, 191, 1], ![-227, 332, 80, 192]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI631N1 : Nat.card (O ⧸ I631N1) = 631 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI631N1)

lemma isPrimeI631N1 : Ideal.IsPrime I631N1 := prime_ideal_of_norm_prime hp631.out _ NI631N1

def I631N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![631, 0, 0, 0], ![295, 1, 0, 0]] i)))

def SI631N2: IdealEqSpanCertificate' Table ![![631, 0, 0, 0], ![295, 1, 0, 0]] 
 ![![631, 0, 0, 0], ![295, 1, 0, 0], ![53, 0, 1, 0], ![140, 0, 0, 1]] where
  M :=![![![631, 0, 0, 0], ![0, 631, 0, 0], ![0, 0, 631, 0], ![0, 0, 0, 631]], ![![295, 1, 0, 0], ![0, 295, 1, 0], ![0, 0, 295, 1], ![383, 332, 80, 296]]]
  hmulB := by decide  
  f := ![![![53101, -37580, 62266702, 211074], ![-113580, 80768, -133187694, 0]], ![![24485, -17912, 29253909, 99166], ![-52372, 38491, -62573746, 0]], ![![3973, -3232, 5229749, 17728], ![-8498, 6942, -11186368, 0]], ![![11530, -8378, 13815116, 46831], ![-24662, 18004, -29550360, 0]]]
  g := ![![![1, 0, 0, 0], ![-295, 631, 0, 0], ![-53, 0, 631, 0], ![-140, 0, 0, 631]], ![![0, 1, 0, 0], ![-138, 295, 1, 0], ![-25, 0, 295, 1], ![-227, 332, 80, 296]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI631N2 : Nat.card (O ⧸ I631N2) = 631 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI631N2)

lemma isPrimeI631N2 : Ideal.IsPrime I631N2 := prime_ideal_of_norm_prime hp631.out _ NI631N2
def MulI631N0 : IdealMulLeCertificate' Table 
  ![![631, 0, 0, 0], ![13, -67, -4, 1]] ![![631, 0, 0, 0], ![191, 1, 0, 0]]
  ![![631, 0, 0, 0], ![-24898, -13083, -751, 188]] where
 M :=  ![![![398161, 0, 0, 0], ![120521, 631, 0, 0]], ![![8203, -42277, -2524, 631], ![2866, -12452, -751, 188]]]
 hmul := by decide  
 g :=  ![![![![631, 0, 0, 0], ![0, 0, 0, 0]], ![![191, 1, 0, 0], ![0, 0, 0, 0]]], ![![![24911, 13016, 747, -187], ![631, 0, 0, 0]], ![![44, 1, 0, 0], ![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI631N1 : IdealMulLeCertificate' Table 
  ![![631, 0, 0, 0], ![-24898, -13083, -751, 188]] ![![631, 0, 0, 0], ![295, 1, 0, 0]]
  ![![631, 0, 0, 0]] where
 M :=  ![![![398161, 0, 0, 0], ![186145, 631, 0, 0]], ![![-15710638, -8255373, -473881, 118628], ![-7272906, -3821967, -219588, 54897]]]
 hmul := by decide  
 g :=  ![![![![631, 0, 0, 0]], ![![295, 1, 0, 0]]], ![![![-24898, -13083, -751, 188]], ![![-11526, -6057, -348, 87]]]]
 hle2 := by decide  


def PBC631 : ContainsPrimesAboveP 631 ![I631N0, I631N1, I631N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI631N0
    exact isPrimeI631N1
    exact isPrimeI631N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 631 (by decide) (𝕀 ⊙ MulI631N0 ⊙ MulI631N1)
instance hp641 : Fact (Nat.Prime 641) := {out := by norm_num}

def I641N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![641, 0, 0, 0], ![-87, -67, -4, 1]] i)))

def SI641N0: IdealEqSpanCertificate' Table ![![641, 0, 0, 0], ![-87, -67, -4, 1]] 
 ![![641, 0, 0, 0], ![0, 641, 0, 0], ![122, 44, 1, 0], ![401, 109, 0, 1]] where
  M :=![![![641, 0, 0, 0], ![0, 641, 0, 0], ![0, 0, 641, 0], ![0, 0, 0, 641]], ![![-87, -67, -4, 1], ![383, 245, 13, -3], ![-1149, -613, 5, 10], ![3830, 2171, 187, 15]]]
  hmulB := by decide  
  f := ![![![20733638, 13188741, 696898, -160319], ![-4196627, -35653702, 0, 0]], ![![-50992, -32425, -1713, 394], ![10897, 87817, 0, 0]], ![![3942676, 2507950, 132521, -30486], ![-798042, -6779856, 0, 0]], ![![12961968, 8245154, 435677, -100226], ![-2623600, -22289489, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-122, -44, 641, 0], ![-401, -109, 0, 641]], ![![0, 0, -4, 1], ![0, 0, 13, -3], ![-9, -3, 5, 10], ![-39, -12, 187, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P641P0 : CertificateIrreducibleZModOfList' 641 2 2 9 [69, 578, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 640], [0, 1]]
 g := ![![[445, 288], [440], [389], [352], [160], [224], [103], [337, 123], [1]],![[0, 353], [440], [389], [352], [160], [224], [103], [394, 518], [1]]]
 h' := ![![[63, 640], [628, 163], [340, 296], [30, 355], [160, 54], [476, 77], [505, 497], [464, 198], [572, 63], [0, 1]],![[0, 1], [0, 478], [399, 345], [601, 286], [357, 587], [199, 564], [407, 144], [118, 443], [54, 578], [63, 640]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [331]]
 b := ![[], [75, 486]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI641N0 : CertifiedPrimeIdeal' SI641N0 641 where 
  n := 2
  hpos := by decide  
  P := [69, 578, 1]
  hirr := P641P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![125499, 112292, 31084, 3449]
  a := ![-1, 0, 1, 2]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-7878, -2545, 31084, 3449]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI641N0 : Ideal.IsPrime I641N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI641N0 B_one_repr
lemma NI641N0 : Nat.card (O ⧸ I641N0) = 410881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI641N0

def I641N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![641, 0, 0, 0], ![-176, -67, -4, 1]] i)))

def SI641N1: IdealEqSpanCertificate' Table ![![641, 0, 0, 0], ![-176, -67, -4, 1]] 
 ![![641, 0, 0, 0], ![0, 641, 0, 0], ![496, 596, 1, 0], ![526, 394, 0, 1]] where
  M :=![![![641, 0, 0, 0], ![0, 641, 0, 0], ![0, 0, 641, 0], ![0, 0, 0, 641]], ![![-176, -67, -4, 1], ![383, 156, 13, -3], ![-1149, -613, -84, 10], ![3830, 2171, 187, -74]]]
  hmulB := by decide  
  f := ![![![8924651, 3655830, 311654, -71580], ![-2834502, -16239094, 0, 0]], ![![-84145, -34469, -2939, 675], ![26922, 153199, 0, 0]], ![![6827516, 2796776, 238421, -54760], ![-2168500, -12423220, 0, 0]], ![![7271760, 2978752, 253934, -58323], ![-2309510, -13231518, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-496, -596, 641, 0], ![-526, -394, 0, 641]], ![![2, 3, -4, 1], ![-7, -10, 13, -3], ![55, 71, -84, 10], ![-78, -125, 187, -74]]]
  hle1 := by decide   
  hle2 := by decide  


def P641P1 : CertificateIrreducibleZModOfList' 641 2 2 9 [557, 396, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [245, 640], [0, 1]]
 g := ![![[270, 520], [320], [443], [633], [56], [543], [8], [439, 412], [1]],![[111, 121], [320], [443], [633], [56], [543], [8], [101, 229], [1]]]
 h' := ![![[245, 640], [439, 229], [320, 610], [594, 173], [616, 124], [600, 72], [213, 207], [339, 507], [84, 245], [0, 1]],![[0, 1], [136, 412], [417, 31], [32, 468], [228, 517], [292, 569], [289, 434], [200, 134], [496, 396], [245, 640]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [617]]
 b := ![[], [188, 629]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI641N1 : CertifiedPrimeIdeal' SI641N1 641 where 
  n := 2
  hpos := by decide  
  P := [557, 396, 1]
  hirr := P641P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![122694, 109100, 28780, 2744]
  a := ![-5, 0, 0, 2]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-24330, -28276, 28780, 2744]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI641N1 : Ideal.IsPrime I641N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI641N1 B_one_repr
lemma NI641N1 : Nat.card (O ⧸ I641N1) = 410881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI641N1
def MulI641N0 : IdealMulLeCertificate' Table 
  ![![641, 0, 0, 0], ![-87, -67, -4, 1]] ![![641, 0, 0, 0], ![-176, -67, -4, 1]]
  ![![641, 0, 0, 0]] where
 M :=  ![![![410881, 0, 0, 0], ![-112816, -42947, -2564, 641]], ![![-55767, -42947, -2564, 641], ![-1923, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![641, 0, 0, 0]], ![![-176, -67, -4, 1]]], ![![![-87, -67, -4, 1]], ![![-3, 0, 0, 0]]]]
 hle2 := by decide  


def PBC641 : ContainsPrimesAboveP 641 ![I641N0, I641N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI641N0
    exact isPrimeI641N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 641 (by decide) (𝕀 ⊙ MulI641N0)
instance hp643 : Fact (Nat.Prime 643) := {out := by norm_num}

def I643N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![841, 402, 24, -6]] i)))

def SI643N0: IdealEqSpanCertificate' Table ![![841, 402, 24, -6]] 
 ![![643, 0, 0, 0], ![0, 643, 0, 0], ![284, 98, 1, 0], ![460, 325, 0, 1]] where
  M :=![![![841, 402, 24, -6], ![-2298, -1151, -78, 18], ![6894, 3678, 289, -60], ![-22980, -13026, -1122, 229]]]
  hmulB := by decide  
  f := ![![![-737, -402, -24, 6]], ![![2298, 1255, 78, -18]], ![![14, 8, 1, 0]], ![![670, 367, 24, -5]]]
  g := ![![![-5, 0, 24, -6], ![18, 1, -78, 18], ![-74, -8, 289, -60], ![296, 35, -1122, 229]]]
  hle1 := by decide   
  hle2 := by decide  


def P643P0 : CertificateIrreducibleZModOfList' 643 2 2 9 [265, 483, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [160, 642], [0, 1]]
 g := ![![[606, 529], [55, 135], [234], [33], [495], [593], [225], [166, 523], [1]],![[370, 114], [436, 508], [234], [33], [495], [593], [225], [256, 120], [1]]]
 h' := ![![[160, 642], [214, 23], [412, 357], [401, 155], [12, 617], [524, 522], [200, 256], [377, 628], [378, 160], [0, 1]],![[0, 1], [36, 620], [305, 286], [124, 488], [353, 26], [454, 121], [8, 387], [549, 15], [258, 483], [160, 642]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [279]]
 b := ![[], [414, 461]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI643N0 : CertifiedPrimeIdeal' SI643N0 643 where 
  n := 2
  hpos := by decide  
  P := [265, 483, 1]
  hirr := P643P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![79795, 64391, 15706, -1859]
  a := ![-10, 2, 13, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-5483, -1354, 15706, -1859]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI643N0 : Ideal.IsPrime I643N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI643N0 B_one_repr
lemma NI643N0 : Nat.card (O ⧸ I643N0) = 413449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI643N0

def I643N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-737, -402, -24, 6]] i)))

def SI643N1: IdealEqSpanCertificate' Table ![![-737, -402, -24, 6]] 
 ![![643, 0, 0, 0], ![0, 643, 0, 0], ![336, 544, 1, 0], ![471, 180, 0, 1]] where
  M :=![![![-737, -402, -24, 6], ![2298, 1255, 78, -18], ![-6894, -3678, -185, 60], ![22980, 13026, 1122, -125]]]
  hmulB := by decide  
  f := ![![![841, 402, 24, -6]], ![![-2298, -1151, -78, 18]], ![![-1494, -758, -53, 12]], ![![-63, -48, -6, 1]]]
  g := ![![![7, 18, -24, 6], ![-24, -59, 78, -18], ![42, 134, -185, 60], ![-459, -894, 1122, -125]]]
  hle1 := by decide   
  hle2 := by decide  


def P643P1 : CertificateIrreducibleZModOfList' 643 2 2 9 [229, 292, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [351, 642], [0, 1]]
 g := ![![[546, 570], [353, 206], [156], [381], [129], [310], [323], [507, 388], [1]],![[0, 73], [0, 437], [156], [381], [129], [310], [323], [379, 255], [1]]]
 h' := ![![[351, 642], [181, 408], [14, 163], [403, 99], [159, 611], [506, 393], [575, 140], [280, 86], [414, 351], [0, 1]],![[0, 1], [0, 235], [0, 480], [430, 544], [501, 32], [204, 250], [204, 503], [245, 557], [159, 292], [351, 642]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [492]]
 b := ![[], [551, 246]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI643N1 : CertifiedPrimeIdeal' SI643N1 643 where 
  n := 2
  hpos := by decide  
  P := [229, 292, 1]
  hirr := P643P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![39971, 37937, 10436, 853]
  a := ![1, 1, -4, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-6016, -9009, 10436, 853]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI643N1 : Ideal.IsPrime I643N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI643N1 B_one_repr
lemma NI643N1 : Nat.card (O ⧸ I643N1) = 413449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI643N1
def MulI643N0 : IdealMulLeCertificate' Table 
  ![![841, 402, 24, -6]] ![![-737, -402, -24, 6]]
  ![![643, 0, 0, 0]] where
 M :=  ![![![643, 0, 0, 0]]]
 hmul := by decide  
 g :=  ![![![![1, 0, 0, 0]]]]
 hle2 := by decide  


def PBC643 : ContainsPrimesAboveP 643 ![I643N0, I643N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI643N0
    exact isPrimeI643N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 643 (by decide) (𝕀 ⊙ MulI643N0)
instance hp647 : Fact (Nat.Prime 647) := {out := by norm_num}

def I647N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![647, 0, 0, 0]] i)))

def SI647N0: IdealEqSpanCertificate' Table ![![647, 0, 0, 0]] 
 ![![647, 0, 0, 0], ![0, 647, 0, 0], ![0, 0, 647, 0], ![0, 0, 0, 647]] where
  M :=![![![647, 0, 0, 0], ![0, 647, 0, 0], ![0, 0, 647, 0], ![0, 0, 0, 647]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P647P0 : CertificateIrreducibleZModOfList' 647 4 2 9 [407, 623, 404, 229, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [491, 629, 258, 423], [304, 360, 405, 179], [270, 304, 631, 45], [0, 1]]
 g := ![![[614, 540, 237, 191], [261, 126, 337, 343], [606, 386, 250, 612], [435, 509, 504], [580, 616, 119], [497, 228, 555], [288, 459, 383], [418, 1], []],![[75, 70, 127, 362, 585, 311], [133, 436, 224, 288, 296, 532], [462, 223, 480, 497, 39, 132], [120, 303, 468], [191, 250, 344], [103, 303, 41], [149, 61, 450], [277, 351, 614, 208, 24, 482], [87, 645, 357]],![[539, 240, 153, 289, 72, 489], [502, 488, 580, 54, 270, 401], [252, 113, 388, 188, 262, 481], [507, 50, 562], [457, 71, 113], [146, 166, 581], [188, 38, 233], [347, 524, 566, 408, 20, 604], [308, 300, 338]],![[618, 581, 229, 456, 643, 478], [613, 417, 245, 236, 400, 151], [594, 635, 586, 357, 116, 524], [94, 110, 147], [125, 579, 217], [335, 57, 607], [348, 463, 337], [139, 156, 146, 251, 251, 298], [208, 28, 84]]]
 h' := ![![[491, 629, 258, 423], [528, 381, 372, 400], [512, 77, 348, 65], [100, 349, 534, 501], [174, 425, 38, 342], [213, 367, 155, 380], [469, 188, 137, 604], [35, 567, 19, 277], [0, 0, 1], [0, 1]],![[304, 360, 405, 179], [124, 194, 198, 255], [106, 507, 391, 308], [193, 155, 554, 107], [283, 556, 534, 306], [136, 345, 267, 337], [611, 96, 440, 161], [270, 254, 116, 107], [573, 107, 74, 234], [491, 629, 258, 423]],![[270, 304, 631, 45], [38, 179, 500, 634], [398, 582, 558, 484], [615, 30, 583, 178], [291, 232, 70, 439], [520, 252, 319, 280], [79, 104, 558, 462], [191, 554, 183, 381], [57, 5, 53, 67], [304, 360, 405, 179]],![[0, 1], [624, 540, 224, 5], [355, 128, 644, 437], [629, 113, 270, 508], [347, 81, 5, 207], [135, 330, 553, 297], [226, 259, 159, 67], [13, 566, 329, 529], [537, 535, 519, 346], [270, 304, 631, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [103, 85, 535], []]
 b := ![[], [], [441, 476, 477, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI647N0 : CertifiedPrimeIdeal' SI647N0 647 where 
  n := 4
  hpos := by decide  
  P := [407, 623, 404, 229, 1]
  hirr := P647P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![34072973293, 32647474425, 10086081706, 999560652]
  a := ![-3, 1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![52663019, 50459775, 15588998, 1544916]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI647N0 : Ideal.IsPrime I647N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI647N0 B_one_repr
lemma NI647N0 : Nat.card (O ⧸ I647N0) = 175233494881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI647N0

def PBC647 : ContainsPrimesAboveP 647 ![I647N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI647N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![647, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 647 (by decide) 𝕀

instance hp653 : Fact (Nat.Prime 653) := {out := by norm_num}

def I653N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![653, 0, 0, 0], ![36, -34, -4, 1]] i)))

def SI653N0: IdealEqSpanCertificate' Table ![![653, 0, 0, 0], ![36, -34, -4, 1]] 
 ![![653, 0, 0, 0], ![0, 653, 0, 0], ![533, 584, 1, 0], ![209, 343, 0, 1]] where
  M :=![![![653, 0, 0, 0], ![0, 653, 0, 0], ![0, 0, 653, 0], ![0, 0, 0, 653]], ![![36, -34, -4, 1], ![383, 368, 46, -3], ![-1149, -613, 128, 43], ![16469, 13127, 2827, 171]]]
  hmulB := by decide  
  f := ![![![58222368, 55968662, 6995986, -456546], ![252711, -99290609, 0, 0]], ![![-230147, -221201, -27650, 1804], ![-653, 392453, 0, 0]], ![![47317192, 45485614, 5685623, -371034], ![205407, -80693265, 0, 0]], ![![18513839, 17797207, 2224620, -145175], ![80474, -31572934, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-533, -584, 653, 0], ![-209, -343, 0, 653]], ![![3, 3, -4, 1], ![-36, -39, 46, -3], ![-120, -138, 128, 43], ![-2337, -2598, 2827, 171]]]
  hle1 := by decide   
  hle2 := by decide  


def P653P0 : CertificateIrreducibleZModOfList' 653 2 2 9 [283, 553, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 652], [0, 1]]
 g := ![![[265, 397], [401], [99, 482], [321, 165], [359], [544], [143], [468, 205], [1]],![[132, 256], [401], [630, 171], [496, 488], [359], [544], [143], [72, 448], [1]]]
 h' := ![![[100, 652], [65, 425], [62, 75], [577, 484], [147, 538], [630, 570], [182, 480], [115, 309], [370, 100], [0, 1]],![[0, 1], [120, 228], [379, 578], [2, 169], [401, 115], [166, 83], [513, 173], [324, 344], [575, 553], [100, 652]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [286]]
 b := ![[], [33, 143]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI653N0 : CertifiedPrimeIdeal' SI653N0 653 where 
  n := 2
  hpos := by decide  
  P := [283, 553, 1]
  hirr := P653P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![495638, 412628, 99881, 1165]
  a := ![3, 0, 7, -4]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-81140, -89307, 99881, 1165]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI653N0 : Ideal.IsPrime I653N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI653N0 B_one_repr
lemma NI653N0 : Nat.card (O ⧸ I653N0) = 426409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI653N0

def I653N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![653, 0, 0, 0], ![162, -164, -4, 1]] i)))

def SI653N1: IdealEqSpanCertificate' Table ![![653, 0, 0, 0], ![162, -164, -4, 1]] 
 ![![653, 0, 0, 0], ![0, 653, 0, 0], ![161, 68, 1, 0], ![153, 108, 0, 1]] where
  M :=![![![653, 0, 0, 0], ![0, 653, 0, 0], ![0, 0, 653, 0], ![0, 0, 0, 653]], ![![162, -164, -4, 1], ![383, 494, -84, -3], ![-1149, -613, 254, -87], ![-33321, -30033, -7573, 167]]]
  hmulB := by decide  
  f := ![![![44385023, 55596396, -9594896, -337612], ![-2892790, -74451142, 0, 0]], ![![-84952, -106215, 18348, 645], ![5877, 142354, 0, 0]], ![![10934401, 13696548, -2363751, -83173], ![-712321, -18341430, 0, 0]], ![![10385487, 13008864, -2245080, -78997], ![-676752, -17420598, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-161, -68, 653, 0], ![-153, -108, 0, 653]], ![![1, 0, -4, 1], ![22, 10, -84, -3], ![-44, -13, 254, -87], ![1777, 715, -7573, 167]]]
  hle1 := by decide   
  hle2 := by decide  


def P653P1 : CertificateIrreducibleZModOfList' 653 2 2 9 [465, 192, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [461, 652], [0, 1]]
 g := ![![[388, 587], [133], [619, 10], [230, 644], [490], [478], [131], [270, 296], [1]],![[0, 66], [133], [5, 643], [652, 9], [490], [478], [131], [249, 357], [1]]]
 h' := ![![[461, 652], [297, 175], [138, 493], [142, 140], [197, 447], [495, 327], [52, 264], [479, 625], [188, 461], [0, 1]],![[0, 1], [0, 478], [167, 160], [35, 513], [569, 206], [399, 326], [298, 389], [631, 28], [484, 192], [461, 652]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162]]
 b := ![[], [593, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI653N1 : CertifiedPrimeIdeal' SI653N1 653 where 
  n := 2
  hpos := by decide  
  P := [465, 192, 1]
  hirr := P653P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![30339, 25705, 6484, 140]
  a := ![0, 1, 1, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-1585, -659, 6484, 140]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI653N1 : Ideal.IsPrime I653N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI653N1 B_one_repr
lemma NI653N1 : Nat.card (O ⧸ I653N1) = 426409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI653N1
def MulI653N0 : IdealMulLeCertificate' Table 
  ![![653, 0, 0, 0], ![36, -34, -4, 1]] ![![653, 0, 0, 0], ![162, -164, -4, 1]]
  ![![653, 0, 0, 0]] where
 M :=  ![![![426409, 0, 0, 0], ![105786, -107092, -2612, 653]], ![![23508, -22202, -2612, 653], ![-35915, -50281, -5877, 653]]]
 hmul := by decide  
 g :=  ![![![![653, 0, 0, 0]], ![![162, -164, -4, 1]]], ![![![36, -34, -4, 1]], ![![-55, -77, -9, 1]]]]
 hle2 := by decide  


def PBC653 : ContainsPrimesAboveP 653 ![I653N0, I653N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI653N0
    exact isPrimeI653N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 653 (by decide) (𝕀 ⊙ MulI653N0)
instance hp659 : Fact (Nat.Prime 659) := {out := by norm_num}

def I659N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![659, 0, 0, 0], ![-119, -381, -4, 1]] i)))

def SI659N0: IdealEqSpanCertificate' Table ![![659, 0, 0, 0], ![-119, -381, -4, 1]] 
 ![![659, 0, 0, 0], ![0, 659, 0, 0], ![381, 363, 1, 0], ![87, 412, 0, 1]] where
  M :=![![![659, 0, 0, 0], ![0, 659, 0, 0], ![0, 0, 659, 0], ![0, 0, 0, 659]], ![![-119, -381, -4, 1], ![383, 213, -301, -3], ![-1149, -613, -27, -304], ![-116432, -102077, -24933, -331]]]
  hmulB := by decide  
  f := ![![![65764959, 24339402, -55474737, -512492], ![-25610717, -121114315, 0, 0]], ![![-159130, -58589, 134325, 1240], ![62605, 293255, 0, 0]], ![![37934206, 14039310, -31998659, -295613], ![-14772683, -69860550, 0, 0]], ![![8582681, 3176600, -7239697, -66883], ![-3341967, -15805955, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-381, -363, 659, 0], ![-87, -412, 0, 659]], ![![2, 1, -4, 1], ![175, 168, -301, -3], ![54, 204, -27, -304], ![14282, 13786, -24933, -331]]]
  hle1 := by decide   
  hle2 := by decide  


def P659P0 : CertificateIrreducibleZModOfList' 659 2 2 9 [428, 309, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [350, 658], [0, 1]]
 g := ![![[341, 562], [450, 187], [321], [173], [399, 606], [182], [58], [46, 585], [1]],![[0, 97], [0, 472], [321], [173], [301, 53], [182], [58], [506, 74], [1]]]
 h' := ![![[350, 658], [487, 362], [1, 450], [137, 342], [568, 606], [537, 449], [352, 630], [82, 306], [231, 350], [0, 1]],![[0, 1], [0, 297], [0, 209], [558, 317], [470, 53], [186, 210], [87, 29], [424, 353], [157, 309], [350, 658]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [276]]
 b := ![[], [233, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI659N0 : CertifiedPrimeIdeal' SI659N0 659 where 
  n := 2
  hpos := by decide  
  P := [428, 309, 1]
  hirr := P659P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![6248, 6233, 2517, 40]
  a := ![-1, 3, 4, 0]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-1451, -1402, 2517, 40]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI659N0 : Ideal.IsPrime I659N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI659N0 B_one_repr
lemma NI659N0 : Nat.card (O ⧸ I659N0) = 434281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI659N0

def I659N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![659, 0, 0, 0], ![-310, -28, -4, 1]] i)))

def SI659N1: IdealEqSpanCertificate' Table ![![659, 0, 0, 0], ![-310, -28, -4, 1]] 
 ![![659, 0, 0, 0], ![0, 659, 0, 0], ![530, 295, 1, 0], ![492, 493, 0, 1]] where
  M :=![![![659, 0, 0, 0], ![0, 659, 0, 0], ![0, 0, 659, 0], ![0, 0, 0, 659]], ![![-310, -28, -4, 1], ![383, 22, 52, -3], ![-1149, -613, -218, 49], ![18767, 15119, 3307, -169]]]
  hmulB := by decide  
  f := ![![![18197975, 912028, 2968792, -161218], ![-8617084, -38286582, 0, 0]], ![![-42934, -2139, -7048, 382], ![21088, 90942, 0, 0]], ![![14616360, 732529, 2384491, -129488], ![-6921098, -30751230, 0, 0]], ![![13554142, 679299, 2211184, -120077], ![-6417802, -28516182, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-530, -295, 659, 0], ![-492, -493, 0, 659]], ![![2, 1, -4, 1], ![-39, -21, 52, -3], ![137, 60, -218, 49], ![-2505, -1331, 3307, -169]]]
  hle1 := by decide   
  hle2 := by decide  


def P659P1 : CertificateIrreducibleZModOfList' 659 2 2 9 [268, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [613, 658], [0, 1]]
 g := ![![[310, 251], [131, 375], [241], [240], [536, 275], [69], [174], [469, 139], [1]],![[626, 408], [15, 284], [241], [240], [407, 384], [69], [174], [6, 520], [1]]]
 h' := ![![[613, 658], [478, 426], [196, 315], [458, 629], [14, 252], [188, 319], [513, 58], [177, 477], [391, 613], [0, 1]],![[0, 1], [652, 233], [204, 344], [520, 30], [284, 407], [12, 340], [481, 601], [641, 182], [530, 46], [613, 658]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [558]]
 b := ![[], [486, 279]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI659N1 : CertifiedPrimeIdeal' SI659N1 659 where 
  n := 2
  hpos := by decide  
  P := [268, 46, 1]
  hirr := P659P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![1525712, 1341167, 353676, 24479]
  a := ![-1, 1, 0, 7]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-300404, -174600, 353676, 24479]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI659N1 : Ideal.IsPrime I659N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI659N1 B_one_repr
lemma NI659N1 : Nat.card (O ⧸ I659N1) = 434281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI659N1
def MulI659N0 : IdealMulLeCertificate' Table 
  ![![659, 0, 0, 0], ![-119, -381, -4, 1]] ![![659, 0, 0, 0], ![-310, -28, -4, 1]]
  ![![659, 0, 0, 0]] where
 M :=  ![![![434281, 0, 0, 0], ![-204290, -18452, -2636, 659]], ![![-78421, -251079, -2636, 659], ![-85670, 12521, -15157, 659]]]
 hmul := by decide  
 g :=  ![![![![659, 0, 0, 0]], ![![-310, -28, -4, 1]]], ![![![-119, -381, -4, 1]], ![![-130, 19, -23, 1]]]]
 hle2 := by decide  


def PBC659 : ContainsPrimesAboveP 659 ![I659N0, I659N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI659N0
    exact isPrimeI659N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 659 (by decide) (𝕀 ⊙ MulI659N0)


lemma PB692I11_primes (p : ℕ) :
  p ∈ Set.range ![607, 613, 617, 619, 631, 641, 643, 647, 653, 659] ↔ Nat.Prime p ∧ 601 < p ∧ p ≤ 659 := by
  rw [← List.mem_ofFn']
  convert primes_range 601 659 (by omega)
  rfl

def PB692I11 : PrimesBelowBoundCertificateInterval' O 601 659 692 where
  m := 10
  g := ![3, 2, 4, 3, 3, 2, 2, 1, 2, 2]
  P := ![607, 613, 617, 619, 631, 641, 643, 647, 653, 659]
  hP := PB692I11_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I607N0, I607N1, I607N2]
    · exact ![I613N0, I613N1]
    · exact ![I617N0, I617N1, I617N2, I617N3]
    · exact ![I619N0, I619N1, I619N2]
    · exact ![I631N0, I631N1, I631N2]
    · exact ![I641N0, I641N1]
    · exact ![I643N0, I643N1]
    · exact ![I647N0]
    · exact ![I653N0, I653N1]
    · exact ![I659N0, I659N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC607
    · exact PBC613
    · exact PBC617
    · exact PBC619
    · exact PBC631
    · exact PBC641
    · exact PBC643
    · exact PBC647
    · exact PBC653
    · exact PBC659
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![368449, 607, 607]
    · exact ![375769, 375769]
    · exact ![617, 617, 617, 617]
    · exact ![383161, 619, 619]
    · exact ![398161, 631, 631]
    · exact ![410881, 410881]
    · exact ![413449, 413449]
    · exact ![175233494881]
    · exact ![426409, 426409]
    · exact ![434281, 434281]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI607N0
      exact NI607N1
      exact NI607N2
    · dsimp ; intro j
      fin_cases j
      exact NI613N0
      exact NI613N1
    · dsimp ; intro j
      fin_cases j
      exact NI617N0
      exact NI617N1
      exact NI617N2
      exact NI617N3
    · dsimp ; intro j
      fin_cases j
      exact NI619N0
      exact NI619N1
      exact NI619N2
    · dsimp ; intro j
      fin_cases j
      exact NI631N0
      exact NI631N1
      exact NI631N2
    · dsimp ; intro j
      fin_cases j
      exact NI641N0
      exact NI641N1
    · dsimp ; intro j
      fin_cases j
      exact NI643N0
      exact NI643N1
    · dsimp ; intro j
      fin_cases j
      exact NI647N0
    · dsimp ; intro j
      fin_cases j
      exact NI653N0
      exact NI653N1
    · dsimp ; intro j
      fin_cases j
      exact NI659N0
      exact NI659N1
  Il := ![[I607N1, I607N2], [], [I617N0, I617N1, I617N2, I617N3], [I619N1, I619N2], [I631N1, I631N2], [], [], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
