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
instance hp661 : Fact (Nat.Prime 661) := {out := by norm_num}

def I661N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![661, 0, 0, 0], ![-209, -67, -4, 1]] i)))

def SI661N0: IdealEqSpanCertificate' Table ![![661, 0, 0, 0], ![-209, -67, -4, 1]] 
 ![![661, 0, 0, 0], ![0, 661, 0, 0], ![417, 583, 1, 0], ![137, 282, 0, 1]] where
  M :=![![![661, 0, 0, 0], ![0, 661, 0, 0], ![0, 0, 661, 0], ![0, 0, 0, 661]], ![![-209, -67, -4, 1], ![383, 123, 13, -3], ![-1149, -613, -117, 10], ![3830, 2171, 187, -107]]]
  hmulB := by decide  
  f := ![![![80560672, 25877073, 2866026, -658119], ![-28112991, -154376550, 0, 0]], ![![-155212, -49855, -5522, 1268], ![54202, 297450, 0, 0]], ![![50685773, 16280891, 1803197, -414064], ![-17687696, -97128000, 0, 0]], ![![16630944, 5342063, 591662, -135862], ![-5803567, -31869450, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-417, -583, 661, 0], ![-137, -282, 0, 661]], ![![2, 3, -4, 1], ![-7, -10, 13, -3], ![70, 98, -117, 10], ![-90, -116, 187, -107]]]
  hle1 := by decide   
  hle2 := by decide  


def P661P0 : CertificateIrreducibleZModOfList' 661 2 2 9 [253, 244, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [417, 660], [0, 1]]
 g := ![![[628, 423], [126], [244, 646], [188], [412, 205], [85], [245], [531, 46], [1]],![[532, 238], [126], [599, 15], [188], [628, 456], [85], [245], [544, 615], [1]]]
 h' := ![![[417, 660], [170, 111], [402, 470], [511, 549], [202, 74], [547, 463], [631, 561], [501, 144], [408, 417], [0, 1]],![[0, 1], [187, 550], [75, 191], [77, 112], [654, 587], [606, 198], [574, 100], [398, 517], [454, 244], [417, 660]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [609]]
 b := ![[], [133, 635]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI661N0 : CertifiedPrimeIdeal' SI661N0 661 where 
  n := 2
  hpos := by decide  
  P := [253, 244, 1]
  hirr := P661P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![33191, 29457, 8016, 416]
  a := ![0, -1, -1, -1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-5093, -7203, 8016, 416]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI661N0 : Ideal.IsPrime I661N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI661N0 B_one_repr
lemma NI661N0 : Nat.card (O ⧸ I661N0) = 436921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI661N0

def I661N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![661, 0, 0, 0], ![14, 1, 0, 0]] i)))

def SI661N1: IdealEqSpanCertificate' Table ![![661, 0, 0, 0], ![14, 1, 0, 0]] 
 ![![661, 0, 0, 0], ![14, 1, 0, 0], ![465, 0, 1, 0], ![100, 0, 0, 1]] where
  M :=![![![661, 0, 0, 0], ![0, 661, 0, 0], ![0, 0, 661, 0], ![0, 0, 0, 661]], ![![14, 1, 0, 0], ![0, 14, 1, 0], ![0, 0, 14, 1], ![383, 332, 80, 15]]]
  hmulB := by decide  
  f := ![![![11649, -2528114, -180723, -6], ![-549952, 119402379, 3966, 0]], ![![210, -53563, -3841, -1], ![-9914, 2529647, 661, 0]], ![![8163, -1778481, -127146, -5], ![-385377, 83997237, 3305, 0]], ![![1746, -382495, -27344, -1], ![-82429, 18065116, 662, 0]]]
  g := ![![![1, 0, 0, 0], ![-14, 661, 0, 0], ![-465, 0, 661, 0], ![-100, 0, 0, 661]], ![![0, 1, 0, 0], ![-1, 14, 1, 0], ![-10, 0, 14, 1], ![-65, 332, 80, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI661N1 : Nat.card (O ⧸ I661N1) = 661 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI661N1)

lemma isPrimeI661N1 : Ideal.IsPrime I661N1 := prime_ideal_of_norm_prime hp661.out _ NI661N1

def I661N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![661, 0, 0, 0], ![63, 1, 0, 0]] i)))

def SI661N2: IdealEqSpanCertificate' Table ![![661, 0, 0, 0], ![63, 1, 0, 0]] 
 ![![661, 0, 0, 0], ![63, 1, 0, 0], ![658, 0, 1, 0], ![189, 0, 0, 1]] where
  M :=![![![661, 0, 0, 0], ![0, 661, 0, 0], ![0, 0, 661, 0], ![0, 0, 0, 661]], ![![63, 1, 0, 0], ![0, 63, 1, 0], ![0, 0, 63, 1], ![383, 332, 80, 64]]]
  hmulB := by decide  
  f := ![![![2458, -27870, -506, -1], ![-25779, 292823, 661, 0]], ![![63, -2771, -107, -1], ![-660, 29084, 661, 0]], ![![2464, -27744, -504, -1], ![-25842, 291502, 661, 0]], ![![567, -8049, -191, -1], ![-5946, 84545, 662, 0]]]
  g := ![![![1, 0, 0, 0], ![-63, 661, 0, 0], ![-658, 0, 661, 0], ![-189, 0, 0, 661]], ![![0, 1, 0, 0], ![-7, 63, 1, 0], ![-63, 0, 63, 1], ![-129, 332, 80, 64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI661N2 : Nat.card (O ⧸ I661N2) = 661 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI661N2)

lemma isPrimeI661N2 : Ideal.IsPrime I661N2 := prime_ideal_of_norm_prime hp661.out _ NI661N2
def MulI661N0 : IdealMulLeCertificate' Table 
  ![![661, 0, 0, 0], ![-209, -67, -4, 1]] ![![661, 0, 0, 0], ![14, 1, 0, 0]]
  ![![661, 0, 0, 0], ![-1221, -815, -43, 11]] where
 M :=  ![![![436921, 0, 0, 0], ![9254, 661, 0, 0]], ![![-138149, -44287, -2644, 661], ![-2543, -815, -43, 11]]]
 hmul := by decide  
 g :=  ![![![![661, 0, 0, 0], ![0, 0, 0, 0]], ![![14, 1, 0, 0], ![0, 0, 0, 0]]], ![![![1012, 748, 39, -10], ![661, 0, 0, 0]], ![![1219, 815, 43, -11], ![662, 0, 0, 0]]]]
 hle2 := by decide  

def MulI661N1 : IdealMulLeCertificate' Table 
  ![![661, 0, 0, 0], ![-1221, -815, -43, 11]] ![![661, 0, 0, 0], ![63, 1, 0, 0]]
  ![![661, 0, 0, 0]] where
 M :=  ![![![436921, 0, 0, 0], ![41643, 661, 0, 0]], ![![-807081, -538715, -28423, 7271], ![-72710, -48914, -2644, 661]]]
 hmul := by decide  
 g :=  ![![![![661, 0, 0, 0]], ![![63, 1, 0, 0]]], ![![![-1221, -815, -43, 11]], ![![-110, -74, -4, 1]]]]
 hle2 := by decide  


def PBC661 : ContainsPrimesAboveP 661 ![I661N0, I661N1, I661N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI661N0
    exact isPrimeI661N1
    exact isPrimeI661N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 661 (by decide) (𝕀 ⊙ MulI661N0 ⊙ MulI661N1)
instance hp673 : Fact (Nat.Prime 673) := {out := by norm_num}

def I673N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![673, 0, 0, 0], ![27, 1, 0, 0]] i)))

def SI673N0: IdealEqSpanCertificate' Table ![![673, 0, 0, 0], ![27, 1, 0, 0]] 
 ![![673, 0, 0, 0], ![27, 1, 0, 0], ![617, 0, 1, 0], ![166, 0, 0, 1]] where
  M :=![![![673, 0, 0, 0], ![0, 673, 0, 0], ![0, 0, 673, 0], ![0, 0, 0, 673]], ![![27, 1, 0, 0], ![0, 27, 1, 0], ![0, 0, 27, 1], ![383, 332, 80, 28]]]
  hmulB := by decide  
  f := ![![![8992, 306, 113075, 4188], ![-224109, 673, -2818524, 0]], ![![324, -15, 9422, 349], ![-8075, 673, -234877, 0]], ![![8264, 279, 103652, 3839], ![-205965, 674, -2583647, 0]], ![![2212, 56, 27890, 1033], ![-55130, 646, -695208, 0]]]
  g := ![![![1, 0, 0, 0], ![-27, 673, 0, 0], ![-617, 0, 673, 0], ![-166, 0, 0, 673]], ![![0, 1, 0, 0], ![-2, 27, 1, 0], ![-25, 0, 27, 1], ![-93, 332, 80, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI673N0 : Nat.card (O ⧸ I673N0) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI673N0)

lemma isPrimeI673N0 : Ideal.IsPrime I673N0 := prime_ideal_of_norm_prime hp673.out _ NI673N0

def I673N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![673, 0, 0, 0], ![31, 1, 0, 0]] i)))

def SI673N1: IdealEqSpanCertificate' Table ![![673, 0, 0, 0], ![31, 1, 0, 0]] 
 ![![673, 0, 0, 0], ![31, 1, 0, 0], ![385, 0, 1, 0], ![179, 0, 0, 1]] where
  M :=![![![673, 0, 0, 0], ![0, 673, 0, 0], ![0, 0, 673, 0], ![0, 0, 0, 673]], ![![31, 1, 0, 0], ![0, 31, 1, 0], ![0, 0, 31, 1], ![383, 332, 80, 32]]]
  hmulB := by decide  
  f := ![![![9239, -716236, -23176, -2], ![-200554, 15555722, 1346, 0]], ![![341, -33035, -1097, -1], ![-7402, 717418, 673, 0]], ![![5303, -409742, -13254, -1], ![-115114, 8899080, 673, 0]], ![![2467, -190538, -6180, -1], ![-53552, 4138246, 674, 0]]]
  g := ![![![1, 0, 0, 0], ![-31, 673, 0, 0], ![-385, 0, 673, 0], ![-179, 0, 0, 673]], ![![0, 1, 0, 0], ![-2, 31, 1, 0], ![-18, 0, 31, 1], ![-69, 332, 80, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI673N1 : Nat.card (O ⧸ I673N1) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI673N1)

lemma isPrimeI673N1 : Ideal.IsPrime I673N1 := prime_ideal_of_norm_prime hp673.out _ NI673N1

def I673N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![673, 0, 0, 0], ![37, 1, 0, 0]] i)))

def SI673N2: IdealEqSpanCertificate' Table ![![673, 0, 0, 0], ![37, 1, 0, 0]] 
 ![![673, 0, 0, 0], ![37, 1, 0, 0], ![650, 0, 1, 0], ![178, 0, 0, 1]] where
  M :=![![![673, 0, 0, 0], ![0, 673, 0, 0], ![0, 0, 673, 0], ![0, 0, 0, 673]], ![![37, 1, 0, 0], ![0, 37, 1, 0], ![0, 0, 37, 1], ![383, 332, 80, 38]]]
  hmulB := by decide  
  f := ![![![13247, 210, 1653674, 44694], ![-240934, 2692, -30079062, 0]], ![![703, -18, 98937, 2674], ![-12786, 673, -1799602, 0]], ![![12768, 197, 1597138, 43166], ![-232222, 2693, -29050718, 0]], ![![3440, 21, 437375, 11821], ![-62566, 1309, -7955532, 0]]]
  g := ![![![1, 0, 0, 0], ![-37, 673, 0, 0], ![-650, 0, 673, 0], ![-178, 0, 0, 673]], ![![0, 1, 0, 0], ![-3, 37, 1, 0], ![-36, 0, 37, 1], ![-105, 332, 80, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI673N2 : Nat.card (O ⧸ I673N2) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI673N2)

lemma isPrimeI673N2 : Ideal.IsPrime I673N2 := prime_ideal_of_norm_prime hp673.out _ NI673N2

def I673N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![673, 0, 0, 0], ![-96, 1, 0, 0]] i)))

def SI673N3: IdealEqSpanCertificate' Table ![![673, 0, 0, 0], ![-96, 1, 0, 0]] 
 ![![673, 0, 0, 0], ![577, 1, 0, 0], ![206, 0, 1, 0], ![259, 0, 0, 1]] where
  M :=![![![673, 0, 0, 0], ![0, 673, 0, 0], ![0, 0, 673, 0], ![0, 0, 0, 673]], ![![-96, 1, 0, 0], ![0, -96, 1, 0], ![0, 0, -96, 1], ![383, 332, 80, -95]]]
  hmulB := by decide  
  f := ![![![128161, -432183, 4584, -1], ![898455, -3020424, 673, 0]], ![![109921, -370553, 3944, -1], ![770586, -2589704, 673, 0]], ![![39470, -132219, 1469, -1], ![276699, -924028, 673, 0]], ![![49411, -166197, 1822, -1], ![346389, -1161502, 674, 0]]]
  g := ![![![1, 0, 0, 0], ![-577, 673, 0, 0], ![-206, 0, 673, 0], ![-259, 0, 0, 673]], ![![-1, 1, 0, 0], ![82, -96, 1, 0], ![29, 0, -96, 1], ![-272, 332, 80, -95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI673N3 : Nat.card (O ⧸ I673N3) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI673N3)

lemma isPrimeI673N3 : Ideal.IsPrime I673N3 := prime_ideal_of_norm_prime hp673.out _ NI673N3
def MulI673N0 : IdealMulLeCertificate' Table 
  ![![673, 0, 0, 0], ![27, 1, 0, 0]] ![![673, 0, 0, 0], ![31, 1, 0, 0]]
  ![![673, 0, 0, 0], ![-73, -67, -4, 1]] where
 M :=  ![![![452929, 0, 0, 0], ![20863, 673, 0, 0]], ![![18171, 673, 0, 0], ![837, 58, 1, 0]]]
 hmul := by decide  
 g :=  ![![![![2687516318, 1805044205, 90154085, -20750865], ![-471779730, -4812370625, 0, 0]], ![![123784130, 83138422, 4152402, -955763], ![-21729151, -221652550, 0, 0]]], ![![![107810744, 72410044, 3616566, -832429], ![-18925433, -193050050, 0, 0]], ![![4965662, 3335143, 166576, -38341], ![-871532, -8891675, 0, 0]]]]
 hle2 := by decide  

def MulI673N1 : IdealMulLeCertificate' Table 
  ![![673, 0, 0, 0], ![-73, -67, -4, 1]] ![![673, 0, 0, 0], ![37, 1, 0, 0]]
  ![![673, 0, 0, 0], ![-4337, -2220, -135, 34]] where
 M :=  ![![![452929, 0, 0, 0], ![24901, 673, 0, 0]], ![![-49129, -45091, -2692, 673], ![-2318, -2220, -135, 34]]]
 hmul := by decide  
 g :=  ![![![![673, 0, 0, 0], ![0, 0, 0, 0]], ![![37, 1, 0, 0], ![0, 0, 0, 0]]], ![![![4264, 2153, 131, -33], ![673, 0, 0, 0]], ![![3, 0, 0, 0], ![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI673N2 : IdealMulLeCertificate' Table 
  ![![673, 0, 0, 0], ![-4337, -2220, -135, 34]] ![![673, 0, 0, 0], ![-96, 1, 0, 0]]
  ![![673, 0, 0, 0]] where
 M :=  ![![![452929, 0, 0, 0], ![-64608, 673, 0, 0]], ![![-2918801, -1494060, -90855, 22882], ![429374, 220071, 13460, -3365]]]
 hmul := by decide  
 g :=  ![![![![673, 0, 0, 0]], ![![-96, 1, 0, 0]]], ![![![-4337, -2220, -135, 34]], ![![638, 327, 20, -5]]]]
 hle2 := by decide  


def PBC673 : ContainsPrimesAboveP 673 ![I673N0, I673N1, I673N2, I673N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI673N0
    exact isPrimeI673N1
    exact isPrimeI673N2
    exact isPrimeI673N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 673 (by decide) (𝕀 ⊙ MulI673N0 ⊙ MulI673N1 ⊙ MulI673N2)
instance hp677 : Fact (Nat.Prime 677) := {out := by norm_num}

def I677N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![677, 0, 0, 0], ![-316, 250, -4, 1]] i)))

def SI677N0: IdealEqSpanCertificate' Table ![![677, 0, 0, 0], ![-316, 250, -4, 1]] 
 ![![677, 0, 0, 0], ![0, 677, 0, 0], ![622, 458, 1, 0], ![141, 51, 0, 1]] where
  M :=![![![677, 0, 0, 0], ![0, 677, 0, 0], ![0, 0, 677, 0], ![0, 0, 0, 677]], ![![-316, 250, -4, 1], ![383, 16, 330, -3], ![-1149, -613, -224, 327], ![125241, 107415, 25547, 103]]]
  hmulB := by decide  
  f := ![![![25980001, 5124936, 26502288, -226140], ![-10390596, -54495792, 0, 0]], ![![-83014, -16627, -84940, 724], ![33850, 174666, 0, 0]], ![![23813074, 4697438, 24291757, -207278], ![-9523838, -49950348, 0, 0]], ![![5404635, 1066137, 5513280, -47044], ![-2161545, -11336778, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-622, -458, 677, 0], ![-141, -51, 0, 677]], ![![3, 3, -4, 1], ![-302, -223, 330, -3], ![136, 126, -224, 327], ![-23308, -17132, 25547, 103]]]
  hle1 := by decide   
  hle2 := by decide  


def P677P0 : CertificateIrreducibleZModOfList' 677 2 2 9 [162, 222, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [455, 676], [0, 1]]
 g := ![![[553, 631], [383], [460, 459], [60], [668], [383, 542], [591], [115, 540], [1]],![[610, 46], [383], [112, 218], [60], [668], [565, 135], [591], [64, 137], [1]]]
 h' := ![![[455, 676], [30, 595], [627, 315], [618, 62], [557, 74], [238, 599], [379, 178], [326, 567], [515, 455], [0, 1]],![[0, 1], [632, 82], [428, 362], [394, 615], [377, 603], [629, 78], [129, 499], [374, 110], [378, 222], [455, 676]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [326]]
 b := ![[], [491, 163]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI677N0 : CertifiedPrimeIdeal' SI677N0 677 where 
  n := 2
  hpos := by decide  
  P := [162, 222, 1]
  hirr := P677P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![1552787, 1298273, 268676, -5939]
  a := ![-2, 3, -64, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-243318, -179398, 268676, -5939]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI677N0 : Ideal.IsPrime I677N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI677N0 B_one_repr
lemma NI677N0 : Nat.card (O ⧸ I677N0) = 458329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI677N0

def I677N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![677, 0, 0, 0], ![-155, -2, -4, 1]] i)))

def SI677N1: IdealEqSpanCertificate' Table ![![677, 0, 0, 0], ![-155, -2, -4, 1]] 
 ![![677, 0, 0, 0], ![0, 677, 0, 0], ![327, 218, 1, 0], ![476, 193, 0, 1]] where
  M :=![![![677, 0, 0, 0], ![0, 677, 0, 0], ![0, 0, 677, 0], ![0, 0, 0, 677]], ![![-155, -2, -4, 1], ![383, 177, 78, -3], ![-1149, -613, -63, 75], ![28725, 23751, 5387, 12]]]
  hmulB := by decide  
  f := ![![![8392338, 4078356, 1788288, -66351], ![-1943667, -15621098, 0, 0]], ![![-101049, -49135, -21544, 799], ![23695, 188206, 0, 0]], ![![4021052, 1954078, 856829, -31791], ![-931275, -7484594, 0, 0]], ![![5871903, 2853493, 1251208, -46424], ![-1359661, -10929570, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-327, -218, 677, 0], ![-476, -193, 0, 677]], ![![1, 1, -4, 1], ![-35, -24, 78, -3], ![-24, -2, -63, 75], ![-2568, -1703, 5387, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P677P1 : CertificateIrreducibleZModOfList' 677 2 2 9 [245, 215, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [462, 676], [0, 1]]
 g := ![![[443, 85], [401], [362, 441], [637], [508], [503, 384], [232], [400, 189], [1]],![[447, 592], [401], [327, 236], [637], [508], [537, 293], [232], [385, 488], [1]]]
 h' := ![![[462, 676], [606, 631], [674, 194], [458, 656], [549, 433], [656, 339], [173, 559], [165, 159], [432, 462], [0, 1]],![[0, 1], [341, 46], [261, 483], [234, 21], [203, 244], [210, 338], [494, 118], [507, 518], [621, 215], [462, 676]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [487]]
 b := ![[], [281, 582]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI677N1 : CertifiedPrimeIdeal' SI677N1 677 where 
  n := 2
  hpos := by decide  
  P := [245, 215, 1]
  hirr := P677P1
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![275025, 239738, 62097, 3309]
  a := ![-1, 1, 1, -3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-31914, -20585, 62097, 3309]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI677N1 : Ideal.IsPrime I677N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI677N1 B_one_repr
lemma NI677N1 : Nat.card (O ⧸ I677N1) = 458329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI677N1
def MulI677N0 : IdealMulLeCertificate' Table 
  ![![677, 0, 0, 0], ![-316, 250, -4, 1]] ![![677, 0, 0, 0], ![-155, -2, -4, 1]]
  ![![677, 0, 0, 0]] where
 M :=  ![![![458329, 0, 0, 0], ![-104935, -1354, -2708, 677]], ![![-213932, 169250, -2708, 677], ![178051, 71085, 26403, -1354]]]
 hmul := by decide  
 g :=  ![![![![677, 0, 0, 0]], ![![-155, -2, -4, 1]]], ![![![-316, 250, -4, 1]], ![![263, 105, 39, -2]]]]
 hle2 := by decide  


def PBC677 : ContainsPrimesAboveP 677 ![I677N0, I677N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI677N0
    exact isPrimeI677N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 677 (by decide) (𝕀 ⊙ MulI677N0)
instance hp683 : Fact (Nat.Prime 683) := {out := by norm_num}

def I683N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![683, 0, 0, 0], ![-30, -67, -4, 1]] i)))

def SI683N0: IdealEqSpanCertificate' Table ![![683, 0, 0, 0], ![-30, -67, -4, 1]] 
 ![![683, 0, 0, 0], ![0, 683, 0, 0], ![293, 101, 1, 0], ![459, 337, 0, 1]] where
  M :=![![![683, 0, 0, 0], ![0, 683, 0, 0], ![0, 0, 683, 0], ![0, 0, 0, 683]], ![![-30, -67, -4, 1], ![383, 302, 13, -3], ![-1149, -613, 62, 10], ![3830, 2171, 187, 72]]]
  hmulB := by decide  
  f := ![![![247661, 193419, 8278, -1907], ![-29369, -443950, 0, 0]], ![![-9898, -7717, -330, 76], ![1366, 17758, 0, 0]], ![![104785, 81844, 3503, -807], ![-12291, -187824, 0, 0]], ![![161551, 126172, 5400, -1244], ![-19111, -289588, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-293, -101, 683, 0], ![-459, -337, 0, 683]], ![![1, 0, -4, 1], ![-3, 0, 13, -3], ![-35, -15, 62, 10], ![-123, -60, 187, 72]]]
  hle1 := by decide   
  hle2 := by decide  


def P683P0 : CertificateIrreducibleZModOfList' 683 2 2 9 [337, 300, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [383, 682], [0, 1]]
 g := ![![[161, 531], [475, 400], [311], [472, 27], [108], [151, 623], [264], [388, 527], [1]],![[0, 152], [0, 283], [311], [568, 656], [108], [393, 60], [264], [61, 156], [1]]]
 h' := ![![[383, 682], [430, 434], [536, 20], [75, 440], [669, 572], [338, 461], [109, 504], [380, 565], [346, 383], [0, 1]],![[0, 1], [0, 249], [0, 663], [577, 243], [502, 111], [4, 222], [535, 179], [264, 118], [190, 300], [383, 682]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [198]]
 b := ![[], [507, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI683N0 : CertifiedPrimeIdeal' SI683N0 683 where 
  n := 2
  hpos := by decide  
  P := [337, 300, 1]
  hirr := P683P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![30211, 25213, 5992, 632]
  a := ![0, -1, -1, 1]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-2951, -1161, 5992, 632]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI683N0 : Ideal.IsPrime I683N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI683N0 B_one_repr
lemma NI683N0 : Nat.card (O ⧸ I683N0) = 466489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI683N0

def I683N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![683, 0, 0, 0], ![9, 1, 0, 0]] i)))

def SI683N1: IdealEqSpanCertificate' Table ![![683, 0, 0, 0], ![9, 1, 0, 0]] 
 ![![683, 0, 0, 0], ![9, 1, 0, 0], ![602, 0, 1, 0], ![46, 0, 0, 1]] where
  M :=![![![683, 0, 0, 0], ![0, 683, 0, 0], ![0, 0, 683, 0], ![0, 0, 0, 683]], ![![9, 1, 0, 0], ![0, 9, 1, 0], ![0, 0, 9, 1], ![383, 332, 80, 10]]]
  hmulB := by decide  
  f := ![![![1342, -51853, -5787, -1], ![-101767, 3946374, 683, 0]], ![![-9, -703, -87, -1], ![684, 53274, 683, 0]], ![![1180, -45706, -5102, -1], ![-89482, 3478520, 683, 0]], ![![89, -3509, -400, -1], ![-6749, 267044, 684, 0]]]
  g := ![![![1, 0, 0, 0], ![-9, 683, 0, 0], ![-602, 0, 683, 0], ![-46, 0, 0, 683]], ![![0, 1, 0, 0], ![-1, 9, 1, 0], ![-8, 0, 9, 1], ![-75, 332, 80, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI683N1 : Nat.card (O ⧸ I683N1) = 683 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI683N1)

lemma isPrimeI683N1 : Ideal.IsPrime I683N1 := prime_ideal_of_norm_prime hp683.out _ NI683N1

def I683N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![683, 0, 0, 0], ![-111, 1, 0, 0]] i)))

def SI683N2: IdealEqSpanCertificate' Table ![![683, 0, 0, 0], ![-111, 1, 0, 0]] 
 ![![683, 0, 0, 0], ![572, 1, 0, 0], ![656, 0, 1, 0], ![418, 0, 0, 1]] where
  M :=![![![683, 0, 0, 0], ![0, 683, 0, 0], ![0, 0, 683, 0], ![0, 0, 0, 683]], ![![-111, 1, 0, 0], ![0, -111, 1, 0], ![0, 0, -111, 1], ![383, 332, 80, -110]]]
  hmulB := by decide  
  f := ![![![11545, 784, 3818392, -34400], ![71032, 5464, 23495200, 0]], ![![9658, 690, 3205673, -28880], ![59422, 4781, 19725040, 0]], ![![11008, 789, 3667432, -33040], ![67728, 5465, 22566320, 0]], ![![6998, 510, 2336878, -21053], ![43056, 3526, 14379200, 0]]]
  g := ![![![1, 0, 0, 0], ![-572, 683, 0, 0], ![-656, 0, 683, 0], ![-418, 0, 0, 683]], ![![-1, 1, 0, 0], ![92, -111, 1, 0], ![106, 0, -111, 1], ![-287, 332, 80, -110]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI683N2 : Nat.card (O ⧸ I683N2) = 683 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI683N2)

lemma isPrimeI683N2 : Ideal.IsPrime I683N2 := prime_ideal_of_norm_prime hp683.out _ NI683N2
def MulI683N0 : IdealMulLeCertificate' Table 
  ![![683, 0, 0, 0], ![-30, -67, -4, 1]] ![![683, 0, 0, 0], ![9, 1, 0, 0]]
  ![![683, 0, 0, 0], ![-570, -301, -23, 6]] where
 M :=  ![![![466489, 0, 0, 0], ![6147, 683, 0, 0]], ![![-20490, -45761, -2732, 683], ![113, -301, -23, 6]]]
 hmul := by decide  
 g :=  ![![![![683, 0, 0, 0], ![0, 0, 0, 0]], ![![9, 1, 0, 0], ![0, 0, 0, 0]]], ![![![540, 234, 19, -5], ![683, 0, 0, 0]], ![![1, 0, 0, 0], ![1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI683N1 : IdealMulLeCertificate' Table 
  ![![683, 0, 0, 0], ![-570, -301, -23, 6]] ![![683, 0, 0, 0], ![-111, 1, 0, 0]]
  ![![683, 0, 0, 0]] where
 M :=  ![![![466489, 0, 0, 0], ![-75813, 683, 0, 0]], ![![-389310, -205583, -15709, 4098], ![65568, 34833, 2732, -683]]]
 hmul := by decide  
 g :=  ![![![![683, 0, 0, 0]], ![![-111, 1, 0, 0]]], ![![![-570, -301, -23, 6]], ![![96, 51, 4, -1]]]]
 hle2 := by decide  


def PBC683 : ContainsPrimesAboveP 683 ![I683N0, I683N1, I683N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI683N0
    exact isPrimeI683N1
    exact isPrimeI683N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 683 (by decide) (𝕀 ⊙ MulI683N0 ⊙ MulI683N1)
instance hp691 : Fact (Nat.Prime 691) := {out := by norm_num}

def I691N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![541, 268, 16, -4]] i)))

def SI691N0: IdealEqSpanCertificate' Table ![![541, 268, 16, -4]] 
 ![![691, 0, 0, 0], ![0, 691, 0, 0], ![150, 514, 1, 0], ![292, 607, 0, 1]] where
  M :=![![![541, 268, 16, -4], ![-1532, -787, -52, 12], ![4596, 2452, 173, -40], ![-15320, -8684, -748, 133]]]
  hmulB := by decide  
  f := ![![![511, 268, 16, -4]], ![![-1532, -817, -52, 12]], ![![-1022, -546, -35, 8]], ![![-1152, -617, -40, 9]]]
  g := ![![![-1, -8, 16, -4], ![4, 27, -52, 12], ![-14, -90, 173, -40], ![84, 427, -748, 133]]]
  hle1 := by decide   
  hle2 := by decide  


def P691P0 : CertificateIrreducibleZModOfList' 691 2 2 9 [502, 400, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [291, 690], [0, 1]]
 g := ![![[188, 574], [138, 143], [139], [210], [186, 54], [548, 193], [351], [549, 379], [1]],![[0, 117], [291, 548], [139], [210], [7, 637], [49, 498], [351], [278, 312], [1]]]
 h' := ![![[291, 690], [515, 580], [208, 88], [271, 39], [604, 625], [613, 259], [577, 350], [111, 385], [189, 291], [0, 1]],![[0, 1], [0, 111], [249, 603], [564, 652], [55, 66], [663, 432], [159, 341], [204, 306], [568, 400], [291, 690]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [249]]
 b := ![[], [24, 470]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI691N0 : CertifiedPrimeIdeal' SI691N0 691 where 
  n := 2
  hpos := by decide  
  P := [502, 400, 1]
  hirr := P691P0
  hd := by decide  
  hij := by decide  
  hcard := by decide  
  hneq := by decide  
  hlen := by decide  
  c := ![288053, 243947, 62406, 5270]
  a := ![19, 1, -1, 3]
  z := ![1, 0, 0, 0]
  hpol := by decide  
  g := ![-15357, -50697, 62406, 5270]
  hcmem := by decide  
  hpmem := by decide  

lemma isPrimeI691N0 : Ideal.IsPrime I691N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI691N0 B_one_repr
lemma NI691N0 : Nat.card (O ⧸ I691N0) = 477481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI691N0

def I691N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![691, 0, 0, 0], ![218, 1, 0, 0]] i)))

def SI691N1: IdealEqSpanCertificate' Table ![![691, 0, 0, 0], ![218, 1, 0, 0]] 
 ![![691, 0, 0, 0], ![218, 1, 0, 0], ![155, 0, 1, 0], ![69, 0, 0, 1]] where
  M :=![![![691, 0, 0, 0], ![0, 691, 0, 0], ![0, 0, 691, 0], ![0, 0, 0, 691]], ![![218, 1, 0, 0], ![0, 218, 1, 0], ![0, 0, 218, 1], ![383, 332, 80, 219]]]
  hmulB := by decide  
  f := ![![![31393, -1600, 3918760, 17976], ![-99504, 5528, -12421416, 0]], ![![9810, -609, 1245213, 5712], ![-31094, 2073, -3946992, 0]], ![![7045, -404, 878974, 4032], ![-22330, 1383, -2786112, 0]], ![![2883, -354, 391308, 1795], ![-9138, 1164, -1240344, 0]]]
  g := ![![![1, 0, 0, 0], ![-218, 691, 0, 0], ![-155, 0, 691, 0], ![-69, 0, 0, 691]], ![![0, 1, 0, 0], ![-69, 218, 1, 0], ![-49, 0, 218, 1], ![-144, 332, 80, 219]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI691N1 : Nat.card (O ⧸ I691N1) = 691 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI691N1)

lemma isPrimeI691N1 : Ideal.IsPrime I691N1 := prime_ideal_of_norm_prime hp691.out _ NI691N1

def I691N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![691, 0, 0, 0], ![-42, 1, 0, 0]] i)))

def SI691N2: IdealEqSpanCertificate' Table ![![691, 0, 0, 0], ![-42, 1, 0, 0]] 
 ![![691, 0, 0, 0], ![649, 1, 0, 0], ![309, 0, 1, 0], ![540, 0, 0, 1]] where
  M :=![![![691, 0, 0, 0], ![0, 691, 0, 0], ![0, 0, 691, 0], ![0, 0, 0, 691]], ![![-42, 1, 0, 0], ![0, -42, 1, 0], ![0, 0, -42, 1], ![383, 332, 80, -41]]]
  hmulB := by decide  
  f := ![![![8359, 95, 3094007, -73667], ![137509, 4837, 50903897, 0]], ![![7813, 108, 2911559, -69323], ![128527, 4837, 47902193, 0]], ![![3741, 37, 1383561, -32942], ![61541, 2074, 22762922, 0]], ![![6492, 58, 2417893, -57569], ![106796, 3497, 39780180, 0]]]
  g := ![![![1, 0, 0, 0], ![-649, 691, 0, 0], ![-309, 0, 691, 0], ![-540, 0, 0, 691]], ![![-1, 1, 0, 0], ![39, -42, 1, 0], ![18, 0, -42, 1], ![-315, 332, 80, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI691N2 : Nat.card (O ⧸ I691N2) = 691 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI691N2)

lemma isPrimeI691N2 : Ideal.IsPrime I691N2 := prime_ideal_of_norm_prime hp691.out _ NI691N2
def MulI691N0 : IdealMulLeCertificate' Table 
  ![![541, 268, 16, -4]] ![![691, 0, 0, 0], ![218, 1, 0, 0]]
  ![![691, 0, 0, 0], ![-28065, -14582, -859, 215]] where
 M :=  ![![![373831, 185188, 11056, -2764], ![116406, 57637, 3436, -860]]]
 hmul := by decide  
 g :=  ![![![![541, 268, 16, -4], ![0, 0, 0, 0]], ![![6, -1, 0, 0], ![-4, 0, 0, 0]]]]
 hle2 := by decide  

def MulI691N1 : IdealMulLeCertificate' Table 
  ![![691, 0, 0, 0], ![-28065, -14582, -859, 215]] ![![691, 0, 0, 0], ![-42, 1, 0, 0]]
  ![![691, 0, 0, 0]] where
 M :=  ![![![477481, 0, 0, 0], ![-29022, 691, 0, 0]], ![![-19392915, -10076162, -593569, 148565], ![1261075, 655759, 38696, -9674]]]
 hmul := by decide  
 g :=  ![![![![691, 0, 0, 0]], ![![-42, 1, 0, 0]]], ![![![-28065, -14582, -859, 215]], ![![1825, 949, 56, -14]]]]
 hle2 := by decide  


def PBC691 : ContainsPrimesAboveP 691 ![I691N0, I691N1, I691N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI691N0
    exact isPrimeI691N1
    exact isPrimeI691N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 691 (by decide) (𝕀 ⊙ MulI691N0 ⊙ MulI691N1)


lemma PB692I12_primes (p : ℕ) :
  p ∈ Set.range ![661, 673, 677, 683, 691] ↔ Nat.Prime p ∧ 659 < p ∧ p ≤ 691 := by
  rw [← List.mem_ofFn']
  convert primes_range 659 691 (by omega)
  rfl

def PB692I12 : PrimesBelowBoundCertificateInterval' O 659 691 692 where
  m := 5
  g := ![3, 4, 2, 3, 3]
  P := ![661, 673, 677, 683, 691]
  hP := PB692I12_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I661N0, I661N1, I661N2]
    · exact ![I673N0, I673N1, I673N2, I673N3]
    · exact ![I677N0, I677N1]
    · exact ![I683N0, I683N1, I683N2]
    · exact ![I691N0, I691N1, I691N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC661
    · exact PBC673
    · exact PBC677
    · exact PBC683
    · exact PBC691
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![436921, 661, 661]
    · exact ![673, 673, 673, 673]
    · exact ![458329, 458329]
    · exact ![466489, 683, 683]
    · exact ![477481, 691, 691]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI661N0
      exact NI661N1
      exact NI661N2
    · dsimp ; intro j
      fin_cases j
      exact NI673N0
      exact NI673N1
      exact NI673N2
      exact NI673N3
    · dsimp ; intro j
      fin_cases j
      exact NI677N0
      exact NI677N1
    · dsimp ; intro j
      fin_cases j
      exact NI683N0
      exact NI683N1
      exact NI683N2
    · dsimp ; intro j
      fin_cases j
      exact NI691N0
      exact NI691N1
      exact NI691N2
  Il := ![[I661N1, I661N2], [I673N0, I673N1, I673N2, I673N3], [], [I683N1, I683N2], [I691N1, I691N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
