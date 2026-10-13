/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.RI5_1_3790297_2
import LeanBridge.IdealArithmetic.Generation.ClassGroupGeneration
import LeanBridge.IdealArithmetic.IdealArithmetic
import LeanBridge.IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0, 0, 0]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![0, 0, 0, 0, 107]] where
  M :=![![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![0, 0, 0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 5 2 6 [93, 95, 74, 53, 97, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 105, 90, 79, 92], [75, 94, 1, 47, 103], [100, 84, 90, 0, 1], [47, 37, 33, 88, 18], [0, 1]]
 g := ![![[46, 59, 86, 55, 101], [83, 1, 69, 14, 52], [82, 97, 16, 23], [80, 72, 9, 89, 69], [10, 1], []],![[57, 32, 106, 98, 90, 97, 44, 48], [65, 42, 56, 52, 40, 86, 99, 75], [16, 59, 29, 105], [28, 72, 0, 90, 85, 40, 38, 99], [89, 1, 96, 33], [30, 15, 13, 101, 106, 22, 101, 49]],![[30, 77, 33, 28, 84, 74, 39, 98], [84, 48, 59, 25, 87, 51, 67, 18], [58, 45, 66, 35], [101, 69, 8, 63, 65, 40, 27, 63], [30, 73, 82, 10], [29, 99, 92, 91, 15, 47, 11, 43]],![[19, 45, 76, 85, 32, 45, 6, 75], [93, 69, 80, 82, 41, 44, 79, 41], [18, 81, 104, 47], [24, 43, 75, 87, 65, 22, 13, 41], [13, 79, 32, 92], [91, 81, 64, 48, 36, 103, 10, 1]],![[15, 17, 38, 92, 77, 52, 59, 31], [36, 66, 64, 39, 89, 20, 27, 78], [2, 106, 67, 42], [27, 38, 18, 39, 37, 95, 2, 18], [85, 3, 30, 56], [60, 49, 74, 7, 4, 75, 48, 54]]]
 h' := ![![[2, 105, 90, 79, 92], [92, 40, 73, 56, 23], [10, 96, 105, 85, 65], [50, 61, 62, 0, 68], [33, 27, 21, 38, 47], [0, 0, 0, 1], [0, 1]],![[75, 94, 1, 47, 103], [21, 44, 54, 103, 32], [95, 84, 92, 53, 40], [70, 56, 72, 32, 76], [69, 12, 27, 30, 20], [0, 11, 102, 4, 51], [2, 105, 90, 79, 92]],![[100, 84, 90, 0, 1], [63, 71, 41, 85, 55], [31, 78, 1, 89, 7], [17, 64, 54, 79, 28], [49, 65, 11, 45, 15], [59, 104, 18, 61, 63], [75, 94, 1, 47, 103]],![[47, 37, 33, 88, 18], [103, 97, 53, 104, 17], [100, 24, 85, 76, 83], [13, 56, 1, 102, 58], [29, 68, 48, 43, 24], [75, 22, 37, 19, 78], [100, 84, 90, 0, 1]],![[0, 1], [59, 69, 100, 80, 87], [42, 39, 38, 18, 19], [11, 84, 25, 1, 91], [88, 42, 0, 58, 1], [17, 77, 57, 22, 22], [47, 37, 33, 88, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 73, 62, 24], [], [], []]
 b := ![[], [4, 92, 9, 95, 23], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where 
  n := 5
  hpos := by decide  
  P := [93, 95, 74, 53, 97, 1]
  hirr := P107P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-1442708927, -4578103712, -3036128317, -823483235, 3243606132]
  a := ![9, 11, 12, 3, -36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide  
  g := ![-13483261, -42786016, -28375031, -7696105, 30314076]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 14025517307 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0, 0, 0], ![23, -28, -33, 1, 30]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0, 0, 0], ![23, -28, -33, 1, 30]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![59, 60, 95, 1, 0], ![86, 77, 3, 0, 1]] where
  M :=![![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]], ![![23, -28, -33, 1, 30], ![-34, -42, -64, -35, 106], ![34, -71, 62, 6, -242], ![218, 488, 135, 50, -630], ![62, 91, 63, 0, -197]]]
  hmulB := by decide  
  f := ![![![58629, 43540, 71296, 48742, -130708], ![-55808, 150202, 0, 0, 0]], ![![-4524, -3331, -5464, -3750, 10036], ![4360, -11554, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![29243, 21736, 35587, 24319, -65228], ![-27800, 74942, 0, 0, 0]], ![![43064, 31997, 52389, 35808, -96035], ![-40962, 110346, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-59, -60, -95, 109, 0], ![-86, -77, -3, 0, 109]], ![![-24, -22, -2, 1, 30], ![-65, -56, 27, -35, 106], ![188, 167, 2, 6, -242], ![472, 422, -25, 50, -630], ![156, 140, 6, 0, -197]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [106, 33, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [102, 0, 62], [83, 108, 47], [0, 1]]
 g := ![![[34, 75, 81], [67, 49], [45, 38, 94], [69, 15, 100], [31, 108], [1]],![[92, 85, 79, 65], [3, 64], [34, 103, 78, 56], [42, 82, 41, 59], [68, 94], [24, 62, 71, 54]],![[21, 82, 2, 39], [20, 1], [75, 31, 1, 59], [37, 69, 69, 40], [72, 80], [75, 79, 60, 55]]]
 h' := ![![[102, 0, 62], [5, 80, 9], [26, 58, 7], [98, 106, 58], [102, 84, 10], [3, 76, 76], [0, 1]],![[83, 108, 47], [98, 86, 46], [31, 79, 101], [52, 94, 83], [70, 35, 75], [56, 48, 58], [102, 0, 62]],![[0, 1], [48, 52, 54], [36, 81, 1], [63, 18, 77], [71, 99, 24], [89, 94, 84], [83, 108, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 40], []]
 b := ![[], [74, 91, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where 
  n := 3
  hpos := by decide  
  P := [106, 33, 33, 1]
  hirr := P109P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![-70629138, -201022068, -131743320, -32241242, 178258772]
  a := ![51, 47, 47, -6, -201]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide  
  g := ![-123840828, -110022688, 21985306, -32241242, 178258772]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0, 0, 0], ![-39, -48, -1, 0, 1]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0, 0, 0], ![-39, -48, -1, 0, 1]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![13, 13, 1, 0, 0], ![49, 62, 0, 1, 0], ![83, 74, 0, 0, 1]] where
  M :=![![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]], ![![-39, -48, -1, 0, 1], ![-1, -41, -49, -1, 3], ![1, -2, -38, -47, -7], ![195, 250, 287, 56, -773], ![49, 97, 49, 0, -187]]]
  hmulB := by decide  
  f := ![![![1272691, -10749018, -15105558, -271386, 894330], ![4424964, -33761442, 88944, 0, 0]], ![![412286, -3482122, -4893428, -87931, 289714], ![1433459, -10936951, 28776, 0, 0]], ![![200643, -1694356, -2381119, -42781, 140974], ![697589, -5321881, 14016, 0, 0]], ![![806666, -6812750, -9573989, -172015, 566829], ![2804643, -21398180, 56352, 0, 0]], ![![1249020, -10549034, -14824541, -266348, 877690], ![4342659, -33133340, 87264, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-13, -13, 109, 0, 0], ![-49, -62, 0, 109, 0], ![-83, -74, 0, 0, 109]], ![![-1, -1, -1, 0, 1], ![4, 4, -49, -1, 3], ![31, 36, -38, -47, -7], ![531, 461, 287, 56, -773], ![137, 122, 49, 0, -187]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [22, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 108], [0, 1]]
 g := ![![[101, 5], [64], [104, 36], [92, 3], [4], [67, 1]],![[0, 104], [64], [9, 73], [75, 106], [4], [25, 108]]]
 h' := ![![[67, 108], [10, 21], [1, 101], [47, 103], [0, 60], [52, 107], [0, 1]],![[0, 1], [0, 88], [10, 8], [81, 6], [96, 49], [27, 2], [67, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [100, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where 
  n := 2
  hpos := by decide  
  P := [22, 42, 1]
  hirr := P109P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![226, 15, 86, -85, -935]
  a := ![4, 4, 5, 0, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide  
  g := ![742, 673, 86, -85, -935]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0, 0, 0], ![23, -28, -33, 1, 30]] ![![109, 0, 0, 0, 0], ![-39, -48, -1, 0, 1]]
  ![![109, 0, 0, 0, 0]] where
 M :=  ![![![11881, 0, 0, 0, 0], ![-4251, -5232, -109, 0, 109]], ![![2507, -3052, -3597, 109, 3270], ![763, 3270, 4360, 1635, -6213]]]
 hmul := by decide  
 g :=  ![![![![109, 0, 0, 0, 0]], ![![-39, -48, -1, 0, 1]]], ![![![23, -28, -33, 1, 30]], ![![7, 30, 40, 15, -57]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0], ![47, -22, -16, 1, 13]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0, 0, 0], ![47, -22, -16, 1, 13]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![84, 60, 77, 1, 0], ![58, 98, 45, 0, 1]] where
  M :=![![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]], ![![47, -22, -16, 1, 13], ![-17, 16, -41, -18, 55], ![17, -37, 69, -5, -123], ![143, 288, 116, 79, -449], ![39, 62, 40, 0, -87]]]
  hmulB := by decide  
  f := ![![![70874, -65570, 164332, 72555, -220877], ![-5763, 455164, 0, 0, 0]], ![![-1896, 1741, -4314, -1910, 5804], ![226, -11978, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![51700, -47828, 119861, 52921, -161104], ![-4216, 331992, 0, 0, 0]], ![![34726, -32142, 80609, 35584, -108339], ![-2744, 223236, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-84, -60, -77, 113, 0], ![-58, -98, -45, 0, 113]], ![![-7, -12, -6, 1, 13], ![-15, -38, -10, -18, 55], ![67, 109, 53, -5, -123], ![173, 350, 126, 79, -449], ![45, 76, 35, 0, -87]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [2, 2, 77, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 25, 85], [55, 87, 28], [0, 1]]
 g := ![![[66, 59, 95], [78, 109], [15, 91], [8, 8], [91, 69, 53], [1]],![[2, 56, 55, 91], [34, 41], [35, 22], [17, 22], [84, 19, 100, 31], [21, 15, 90, 83]],![[73, 110, 104, 52], [93, 18], [89, 18], [0, 109], [51, 84, 62, 4], [19, 88, 44, 30]]]
 h' := ![![[94, 25, 85], [7, 44, 35], [84, 98, 83], [112, 71, 59], [44, 23, 102], [111, 111, 36], [0, 1]],![[55, 87, 28], [95, 21, 5], [29, 1, 70], [72, 11, 94], [85, 65, 94], [105, 109, 24], [94, 25, 85]],![[0, 1], [54, 48, 73], [50, 14, 73], [62, 31, 73], [66, 25, 30], [1, 6, 53], [55, 87, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 15], []]
 b := ![[], [104, 11, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where 
  n := 3
  hpos := by decide  
  P := [2, 2, 77, 1]
  hirr := P113P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![4047235, 14179454, 9553938, 2812675, -7983323]
  a := ![-34, -38, -40, -8, 137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide  
  g := ![2042613, 5555616, 1347146, 2812675, -7983323]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0], ![39, 1, 0, 0, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0, 0, 0], ![39, 1, 0, 0, 0]] 
 ![![113, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![61, 0, 1, 0, 0], ![107, 0, 0, 1, 0], ![84, 0, 0, 0, 1]] where
  M :=![![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]], ![![39, 1, 0, 0, 0], ![0, 39, 1, 0, 0], ![0, 0, 39, 1, 0], ![-4, -5, -6, 37, 16], ![-1, -2, -1, 0, 42]]]
  hmulB := by decide  
  f := ![![![42988552, -684359240, -19383116, -245391, -85728], ![-124494473, 1986156817, 5327385, 605454, 0]], ![![15091710, -240253594, -6804710, -86148, -30096], ![-43705461, 697267291, 1870263, 212553, 0]], ![![23323502, -371301202, -10516382, -133138, -46512], ![-67544659, 1077595460, 2890427, 328491, 0]], ![![40701877, -647957141, -18352088, -232338, -81168], ![-117872282, 1880510140, 5043982, 573249, 0]], ![![31956099, -508727199, -14408666, -182414, -63727], ![-92544585, 1476435088, 3960118, 450072, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-39, 113, 0, 0, 0], ![-61, 0, 113, 0, 0], ![-107, 0, 0, 113, 0], ![-84, 0, 0, 0, 113]], ![![0, 1, 0, 0, 0], ![-14, 39, 1, 0, 0], ![-22, 0, 39, 1, 0], ![-42, -5, -6, 37, 16], ![-30, -2, -1, 0, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] 
 ![![113, 0, 0, 0, 0], ![109, 1, 0, 0, 0], ![97, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]], ![![-4, 1, 0, 0, 0], ![0, -4, 1, 0, 0], ![0, 0, -4, 1, 0], ![-4, -5, -6, -6, 16], ![-1, -2, -1, 0, -1]]]
  hmulB := by decide  
  f := ![![![2979477, -40002013, 9834678, 3407, -17280], ![84048157, -1109197378, 347249, 122040, 0]], ![![2880165, -38668589, 9506847, 3294, -16704], ![81246662, -1072223439, 335610, 117972, 0]], ![![2582205, -34668331, 8523367, 2953, -14976], ![72841499, -961302186, 300919, 105768, 0]], ![![1291113, -17334210, 4261696, 1476, -7488], ![36421046, -480652276, 150517, 52884, 0]], ![![659181, -8850001, 2175816, 753, -3823], ![18594857, -245397564, 76911, 27000, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-109, 113, 0, 0, 0], ![-97, 0, 113, 0, 0], ![-49, 0, 0, 113, 0], ![-25, 0, 0, 0, 113]], ![![-1, 1, 0, 0, 0], ![3, -4, 1, 0, 0], ![3, 0, -4, 1, 0], ![9, -5, -6, -6, 16], ![3, -2, -1, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0, 0, 0], ![47, -22, -16, 1, 13]] ![![113, 0, 0, 0, 0], ![39, 1, 0, 0, 0]]
  ![![113, 0, 0, 0, 0], ![45, 38, -54, -9, 82]] where
 M :=  ![![![12769, 0, 0, 0, 0], ![4407, 113, 0, 0, 0]], ![![5311, -2486, -1808, 113, 1469], ![1816, -842, -665, 21, 562]]]
 hmul := by decide  
 g :=  ![![![![68, -38, 54, 9, -82], ![113, 0, 0, 0, 0]], ![![-6, -37, 54, 9, -82], ![113, 0, 0, 0, 0]]], ![![![2, -60, 38, 10, -69], ![113, 0, 0, 0, 0]], ![![-13, -32, 29, 6, -48], ![73, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0, 0, 0], ![45, 38, -54, -9, 82]] ![![113, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]]
  ![![113, 0, 0, 0, 0]] where
 M :=  ![![![12769, 0, 0, 0, 0], ![-452, 113, 0, 0, 0]], ![![5085, 4294, -6102, -1017, 9266], ![-226, -226, 226, 0, -226]]]
 hmul := by decide  
 g :=  ![![![![113, 0, 0, 0, 0]], ![![-4, 1, 0, 0, 0]]], ![![![45, 38, -54, -9, 82]], ![![-2, -2, 2, 0, -2]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)


lemma PB122I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 121 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 121 (by omega)
  rfl

def PB122I3 : PrimesBelowBoundCertificateInterval' O 103 121 122 where
  m := 3
  g := ![1, 2, 3]
  P := ![107, 109, 113]
  hP := PB122I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC107
    · exact PBC109
    · exact PBC113
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![14025517307]
    · exact ![1295029, 11881]
    · exact ![1442897, 113, 113]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
  Il := ![[], [], [I113N1, I113N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
