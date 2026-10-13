/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import LeanBridge.IdealArithmetic.Examples.NF4_0_76176_2.RI4_0_76176_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section 


def alpha0 := B.equivFun.symm ![-2, 0, 1, -2]

def alpha1 := B.equivFun.symm ![0, 0, -1, 2]

def v := B.equivFun.symm ![-1, 0, 0, 0]

def zeta1 := B.equivFun.symm ![3, -1, -1, 2]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![0, -1, 0, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0], ![0, -1, 0, 0]] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![2, 0, 0, 0], ![0, 0, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0], ![0, -2, 0, 0]], ![![0, -2, 0, 0], ![0, 0, 1, 0]]]
 hmul := by decide
 f :=  ![![![![-33013, 49602, 26208, -72345], ![37203, -13104, -4095, 0]], ![![0, 0, 0, 0], ![1269, 72, 3, 0]]], ![![![-24, 36, 20, -53], ![27, -8, -3, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0]]]]
 g :=  ![![![![2, 0, 0, 0], ![0, 0, 0, 0]], ![![4, 0, 0, -1], ![0, -2, 0, 0]]], ![![![4, 0, 0, -1], ![0, -2, 0, 0]], ![![0, 0, 0, 1], ![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0], ![0, 0, 1, -2]] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![4, 0, 0, 0], ![0, 1, 0, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0], ![0, -2, 0, 0]], ![![0, 0, 2, -4], ![-4, -1, 0, 1]]]
 hmul := by decide
 f :=  ![![![![514, -648, -356, 954], ![-486, 179, 54, 0]], ![![0, 0, 0, 0], ![72, -6, 0, 0]]], ![![![-1, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![-1, 0, 0, 0]]]]
 g :=  ![![![![13699, -14904, -20454, 37635], ![-13134, 9096, -6, 0]], ![![-20169, 21942, 30114, -55409], ![19339, -13392, 9, 0]]], ![![![13437, -14619, -20062, 36914], ![-12882, 8922, -6, 0]], ![![-27145, 29532, 40530, -74574], ![26027, -18024, 12, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0], ![0, 1, 0, -1]] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![4, 0, 0, 0], ![-2, 0, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0], ![0, -4, 0, 0]], ![![0, 2, 0, -2], ![6, -8, -9, 18]]]
 hmul := by decide
 f :=  ![![![![-5489649, 8190336, 4403284, -11992992], ![6142752, -2201642, -682528, 0]], ![![156148, -18725, 0, 0], ![1605, -36, 3, 0]]], ![![![5499896, -8205624, -4411503, 12015378], ![-6154218, 2205752, 683802, 0]], ![![-156440, 18760, 0, 0], ![-1608, 36, -3, 0]]]]
 g :=  ![![![![2, 0, 0, 0], ![0, 0, 0, 0]], ![![-4, 0, 0, 1], ![0, 4, 0, 0]]], ![![![2, 0, 0, -1], ![0, -2, 0, 0]], ![![-5, 0, -3, 8], ![3, 8, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0, 0], ![-2, 0, 1, -2]] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![8, 0, 0, 0], ![-8, 1, 2, -7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0], ![0, -4, 0, 0]], ![![-4, 0, 2, -4], ![-4, 1, 0, 1]]]
 hmul := by decide
 f :=  ![![![![11984, -17976, -9620, 26322], ![-13482, 4811, 1498, 0]], ![![124, 0, 0, 0], ![-144, -12, 0, 0]]], ![![![-12152, 18228, 9756, -26691], ![13671, -4876, -1519, 0]], ![![-125, 0, 0, 0], ![145, 12, 0, 0]]]]
 g :=  ![![![![-413489, -452599, -574049, 1060752], ![-714742, 240912, -14, 0]], ![![204780, 224141, 284287, -525315], ![353971, -119308, 7, 0]]], ![![![1856, 2025, 2568, -4743], ![3204, -1078, 0, 0]], ![![206776, 226325, 287056, -530431], ![357420, -120470, 7, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![8, 0, 0, 0], ![-8, 1, 2, -7]] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![-2, 0, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M :=  ![![![16, 0, 0, 0], ![0, -8, 0, 0]], ![![-16, 2, 4, -14], ![10, -18, -25, 56]]]
 hmul := by decide
 f :=  ![![![![16355765821, -24339507840, -12989569191, 35562725344], ![-18254630880, 6494784597, 2028292320, 0]], ![![139099173, -7635720, 0, 0], ![190893, -1932, -14, 0]]]]
 g :=  ![![![![-2, 0, -2, 4]], ![![4, 2, 0, -1]]], ![![![4, 4, 4, -7]], ![![-11, 0, 2, -7]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 =  Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 0, 0, 0], ![-4, 4, -1, -1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![6, 0, 0, 0], ![-4, 4, -1, -1]] ![![6, 0, 0, 0], ![-4, 4, -1, -1]]
  ![![0, 0, -1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![36, 0, 0, 0], ![-24, 24, -6, -6]], ![![-24, 24, -6, -6], ![-256, 80, 115, -232]]]
 hmul := by decide
 f :=  ![![![![1523803724377733666738360, -1115639879562883018729025, -4176848776080472568476050, 6843501284350605993639641], ![-2204071154005433361172181, 816322170115342881218772, -147843736715976059, 0]], ![![0, 0, 0, 0], ![1519191128027, -2142256, -6, 0]]]]
 g :=  ![![![![-6, 0, 6, -12]], ![![26, -18, -16, 31]]], ![![![26, -18, -16, 31]], ![![-19, -2, -44, 75]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 =  Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1, 1, 1, -2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0, 0], ![-4, 4, -1, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![0, -1, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0, 0], ![0, -1, 0, 0]] ![![6, 0, 0, 0], ![-4, 4, -1, -1]]
  ![![6, 0, 0, 0], ![-4, 3, 4, -9]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![12, 0, 0, 0], ![-8, 8, -2, -2]], ![![0, -6, 0, 0], ![22, -19, -28, 53]]]
 hmul := by decide
 f :=  ![![![![313054092621307, -229195592686878, -858090169543977, 1405925949532322], ![-452805753536844, 167704772348760, -327522462, 0]], ![![0, 0, 0, 0], ![-24921, 126, 3, 0]]], ![![![-317917096944419, 232755933165872, 871419802672786, -1427765702251429], ![459839670003304, -170309910093838, 332610219, 0]], ![![0, 0, 0, 0], ![25308, -128, -3, 0]]]]
 g :=  ![![![![21838, 5160, 7322, -12656], ![11898, -8316, -6, 0]], ![![-6390, -1513, -2148, 3714], ![-3476, 2434, 2, 0]]], ![![![-720, -174, -246, 427], ![-390, 276, 0, 0]], ![![138535, 32746, 46462, -80314], ![75468, -52760, -39, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0, 0], ![-4, 3, 4, -9]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![0, 0, 1, -2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00] 
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![2, 0, 0, 0], ![0, 0, 1, -2]] ![![6, 0, 0, 0], ![-4, 4, -1, -1]]
  ![![12, 0, 0, 0], ![2, 0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M :=  ![![![12, 0, 0, 0], ![-8, 8, -2, -2]], ![![0, 0, 6, -12], ![22, -14, -17, 30]]]
 hmul := by decide
 f :=  ![![![![190764623133, -139664076886, -522891256361, 856723934372], ![-275924579676, 102193641444, -199581, 0]], ![![0, 0, 0, 0], ![-18, 0, 0, 0]]], ![![![31799360837, -23281194930, -87162952260, 142810931496], ![-45995033714, 17035089767, -33269, 0]], ![![0, 0, 0, 0], ![-3, 0, 0, 0]]]]
 g :=  ![![![![2669665, -2237760, -2776793, 6028225], ![213546, -2051280, -7770, 0]], ![![-908902, 761856, 945371, -2052336], ![-72701, 698368, 2645, 0]]], ![![![-2692341, 2256768, 2800380, -6079431], ![-215358, 2068704, 7836, 0]], ![![12541784, -10512744, -13045060, 28319920], ![1003217, -9636682, -36502, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0, 0], ![2, 0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0], ![0, 1, 0, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01] 
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![4, 0, 0, 0], ![0, 1, 0, -1]] ![![6, 0, 0, 0], ![-4, 4, -1, -1]]
  ![![12, 0, 0, 0], ![2, 0, -5, 6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M :=  ![![![24, 0, 0, 0], ![-16, 16, -4, -4]], ![![0, 6, 0, -6], ![-76, 21, 22, -51]]]
 hmul := by decide
 f :=  ![![![![-2831750449760444852, 2073236550332403552, 7762003718106464132, -12717549495825508853], ![4095915629681739726, -1517003694666588033, 645650759373, 0]], ![![-205523325, -2840775, 0, 0], ![-29925, -13950, -27, 0]]], ![![![-1257636892435112091, 920765730844506454, 3447260769724609172, -5648117555229047497], ![1819077879770485418, -673731618029571524, 286746388505, 0]], ![![-91277010, -1261645, 0, 0], ![-13290, -6195, -12, 0]]]]
 g :=  ![![![![1530, -1224, -708, 2062], ![1590, 504, 6, 0]], ![![-864, 680, 391, -1141], ![-874, -280, -2, 0]]], ![![![-134, 102, 62, -175], ![-120, -42, 0, 0]], ![![-8115, 6477, 3758, -10924], ![-8372, -2667, -30, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0, 0], ![2, 0, -5, 6]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0], ![-2, 0, 1, -2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02] 
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![4, 0, 0, 0], ![-2, 0, 1, -2]] ![![6, 0, 0, 0], ![-4, 4, -1, -1]]
  ![![24, 0, 0, 0], ![-20, 9, -12, 13]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M :=  ![![![24, 0, 0, 0], ![-16, 16, -4, -4]], ![![-12, 0, 6, -12], ![30, -22, -15, 32]]]
 hmul := by decide
 f :=  ![![![![674861152639615, -494092552580240, -1849836300507837, 3030839144785672], ![-976136277526206, 361531455574698, -153870279, 0]], ![![51828, -1188, 0, 0], ![-36, 0, 0, 0]]], ![![![-12709905872094272, 9305424991251751, 34838640757846471, -57080897445367918], ![18383930023484267, -6808853572594748, 2897895004, 0]], ![![-976094, 22374, 0, 0], ![678, -9, 0, 0]]]]
 g :=  ![![![![858878572623319, -418622226004211, -615265204411476, 1219643496717202], ![95557350989886, 164052093996024, -17466, 0]], ![![251228968950768, -122450406345202, -179970077101174, 356755643852968], ![27951302465891, 47986571958536, -5109, 0]]], ![![![-577109287001872, 281286298288387, 413417303391852, -819519325807705], ![-64208185482048, -110232098011290, 11736, 0]], ![![441292298718461, -215088337625879, -316123611684608, 626653521742210], ![49097421244300, 84290059126705, -8974, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0, 0], ![-20, 9, -12, 13]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0, 0], ![-8, 1, 2, -7]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03] 
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![8, 0, 0, 0], ![-8, 1, 2, -7]] ![![6, 0, 0, 0], ![-4, 4, -1, -1]]
  ![![24, 0, 0, 0], ![-30, 14, 11, -32]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M :=  ![![![48, 0, 0, 0], ![-32, 32, -8, -8]], ![![-48, 6, 12, -42], ![-108, -35, -16, 21]]]
 hmul := by decide
 f :=  ![![![![2181824900056455245077, -1597405834531299080118, -5980533105772997541699, 9798723519907408139666], ![-3155852225414237983116, 1168833779514955273470, -116558592595689, 0]], ![![8301292776, -22226205, 0, 0], ![-795339, -23022, -63, 0]]], ![![![-1695335455816389375159, 1241226437803879700024, 4647031857890301956410, -7613866449416338777575], ![2452180361001185520320, -908214654767349284474, 90569098694591, 0]], ![![-6450323292, 17270347, 0, 0], ![617999, 17889, 49, 0]]]]
 g :=  ![![![![-2012856, -510736, -1649410, 2564582], ![-1957266, 650184, -18, 0]], ![![-7759090, -1968774, -6358105, 9885893], ![-7544806, 2506312, -70, 0]]], ![![![681024, 172794, 558045, -867671], ![662214, -219978, 6, 0]], ![![13796421, 3500638, 11305271, -17577965], ![13415394, -4456451, 124, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0, 0], ![-30, 14, 11, -32]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
