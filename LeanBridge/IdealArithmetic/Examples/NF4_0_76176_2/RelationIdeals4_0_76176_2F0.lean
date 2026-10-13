/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_0_76176_2.PrimesBelow4_0_76176_2F0
import LeanBridge.IdealArithmetic.Examples.NF4_0_76176_2.ClassGroupData4_0_76176_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 8 ![![2, 0, 0, 0], ![-1, 1, 0, -1]] 
  ![2, -2, -2, 5] ![![8, 0, 0, 0], ![-8, 1, 2, -7]] where
    su := ![![16, 0, 0, 0], ![-8, 8, 0, -8]]
    hsu := by decide  
    w := ![![16, -16, -16, 40], ![56, 40, 32, -56]]
    hw := by decide  
    g := ![![![-48853381, -53465068, -67808371, 125298927], ![-84418400, 28452111, 15, 0]], ![![-80964, -88608, -112380, 207661], ![-139905, 47154, 0, 0]]]
    h := ![![![-36374, 35483, -280, -35198], ![-71292, 27, 45, 0]], ![![170246, -166083, 1295, 164770], ![333669, -124, -210, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R2N0 : Ideal.span {8} * I2N0 =  Ideal.span {B.equivFun.symm ![2, -2, -2, 5]} * (J0 ^ 5*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0, 0], ![0, -1, 0, 0]] 
  ![1, 0, 0, 0] ![![2, 0, 0, 0], ![0, -1, 0, 0]] where
    su := ![![2, 0, 0, 0], ![0, -1, 0, 0]]
    hsu := by decide  
    w := ![![2, 0, 0, 0], ![0, -1, 0, 0]]
    hw := by decide  
    g := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0]]]
    h := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 6 ![![3, 0, 0, 0], ![-1, 1, -1, 1]] 
  ![-1, 0, -1, 1] ![![6, 0, 0, 0], ![-4, 3, 4, -9]] where
    su := ![![18, 0, 0, 0], ![-6, 6, -6, 6]]
    hsu := by decide  
    w := ![![-6, 0, -6, 6], ![-12, -12, -6, 12]]
    hw := by decide  
    g := ![![![6602111, -4955796, -6608753, 14868833], ![9906636, 2554, -265, 0]], ![![-1318965, 990052, 1320274, -2970447], ![-1979129, -505, 53, 0]]]
    h := ![![![-5903, 3605, 4372, -8633], ![-1164, -1583, 17, 0]], ![![17681, -10800, -13093, 25855], ![3493, 4741, -51, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R3N0 : Ideal.span {6} * I3N0 =  Ideal.span {B.equivFun.symm ![-1, 0, -1, 1]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 8 ![![3, 0, 0, 0], ![1, 0, 2, -3]] 
  ![-1, 0, -1, 2] ![![24, 0, 0, 0], ![-30, 14, 11, -32]] where
    su := ![![24, 0, 0, 0], ![8, 0, 16, -24]]
    hsu := by decide  
    w := ![![-24, 0, -24, 48], ![40, 32, 48, -72]]
    hw := by decide  
    g := ![![![-3742610, -949709, -3066577, 4768124], ![-3638685, 1208754, 6, 0]], ![![-75592, -19185, -61944, 96317], ![-73495, 24416, 0, 0]]]
    h := ![![![-127, 36, 22, -56], ![30, 18, -3, 0]], ![![147, -40, -26, 65], ![-28, -20, 4, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R3N1 : Ideal.span {8} * I3N1 =  Ideal.span {B.equivFun.symm ![-1, 0, -1, 2]} * (J0 ^ 5*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 6 ![![5, 0, 0, 0], ![-2, -1, 0, 0]] 
  ![2, 0, 2, -5] ![![6, 0, 0, 0], ![-4, 4, -1, -1]] where
    su := ![![30, 0, 0, 0], ![-12, -6, 0, 0]]
    hsu := by decide  
    w := ![![12, 0, 12, -30], ![-18, -18, -42, 60]]
    hw := by decide  
    g := ![![![45420420, -45408536, 11354034, 11350149], ![68112425, -537, -651, 0]], ![![-9001121, 8998768, -2250088, -2249270], ![-13498094, 110, 129, 0]]]
    h := ![![![14, 10, 2, -1], ![34, 8, 0, 0]], ![![-23, -13, -2, 2], ![-56, -3, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R5N0 : Ideal.span {6} * I5N0 =  Ideal.span {B.equivFun.symm ![2, 0, 2, -5]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 6 ![![5, 0, 0, 0], ![-4, 1, 2, -4]] 
  ![-4, 0, -4, 7] ![![6, 0, 0, 0], ![-4, 4, -1, -1]] where
    su := ![![30, 0, 0, 0], ![-24, 6, 12, -24]]
    hsu := by decide  
    w := ![![-24, 0, -24, 42], ![-126, 42, 66, -114]]
    hw := by decide  
    g := ![![![11539889925, -2089901325, -38935159954, 59277469245], ![-32067732429, 7340873377, -55, -666871256]], ![![-11780015429, 2133388621, 39745335272, -60510933825], ![32735008134, -7493624624, 55, 680747708]]]
    h := ![![![116, 94, 8, -61], ![-22, 0, 0, -112]], ![![819, 658, 61, -435], ![-147, 0, 0, -784]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R5N1 : Ideal.span {6} * I5N1 =  Ideal.span {B.equivFun.symm ![-4, 0, -4, 7]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS1 


noncomputable def E13RS0 : RelationCertificate Table 12 ![![13, 0, 0, 0], ![1, 1, 0, -1]] 
  ![-10, 6, 2, -5] ![![12, 0, 0, 0], ![2, 0, 1, 0]] where
    su := ![![156, 0, 0, 0], ![12, 12, 0, -12]]
    hsu := by decide  
    w := ![![-120, 72, 24, -60], ![84, -36, -60, 120]]
    hw := by decide  
    g := ![![![-115473698804, 95099006435, 117830481328, -256035798240], ![-9426409681, 87783650175, 26039, 0]], ![![-17965224, 14795359, 18331887, -39833661], ![-1466541, 13657247, 4, 0]]]
    h := ![![![21072, -29636, -29938, 59625], ![-5242, 43464, -220, 0]], ![![-6691, 9409, 9505, -18930], ![1670, -13800, 70, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R13N0 : Ideal.span {12} * I13N0 =  Ideal.span {B.equivFun.symm ![-10, 6, 2, -5]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 24 ![![13, 0, 0, 0], ![4, 1, 0, -1]] 
  ![2, -6, -10, 19] ![![24, 0, 0, 0], ![-20, 9, -12, 13]] where
    su := ![![312, 0, 0, 0], ![96, 24, 0, -24]]
    hsu := by decide  
    w := ![![48, -144, -240, 456], ![-600, 264, 120, -240]]
    hw := by decide  
    g := ![![![-1395609257247565700, 680227767662399340, 999756941872030869, -1981823518967235918], ![-155273083130230367, -266571583533001463, -26204581, 0]], ![![-322071238126839036, 156979325123824440, 230718558523798360, -457354629304699039], ![-35833091441477760, -61517963937291470, -6047353, 0]]]
    h := ![![![-257107514, 502075007, 377561858, -753783670], ![17494519, -545373700, 4928, 0]], ![![-38145, 74487, 56015, -111830], ![2600, -80910, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R13N1 : Ideal.span {24} * I13N1 =  Ideal.span {B.equivFun.symm ![2, -6, -10, 19]} * (J0 ^ 4*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 12 ![![13, 0, 0, 0], ![-5, 1, 0, -1]] 
  ![-4, 6, 8, -17] ![![12, 0, 0, 0], ![2, 0, 1, 0]] where
    su := ![![156, 0, 0, 0], ![-60, 12, 0, -12]]
    hsu := by decide  
    w := ![![-48, 72, 96, -204], ![60, 36, 12, -12]]
    hw := by decide  
    g := ![![![1037984418127, -854837109030, -1059168381141, 2301484564548], ![84733371265, -789080242797, -89667, 0]], ![![-479130084749, 394589908424, 488908530180, -1062357464330], ![-39112636599, 364236762133, 41390, 0]]]
    h := ![![![27139541, -15819297, -51967114, 102430942], ![-19534455, 75064528, -2754, 0]], ![![28650047, -16699752, -54859448, 108131942], ![-20621682, 79242394, -2907, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R13N2 : Ideal.span {12} * I13N2 =  Ideal.span {B.equivFun.symm ![-4, 6, 8, -17]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS2 


noncomputable def E13RS3 : RelationCertificate Table 24 ![![13, 0, 0, 0], ![-8, 1, 0, -1]] 
  ![8, -6, -4, 7] ![![24, 0, 0, 0], ![-20, 9, -12, 13]] where
    su := ![![312, 0, 0, 0], ![-192, 24, 0, -24]]
    hsu := by decide  
    w := ![![192, -144, -96, 168], ![-72, -24, -408, 696]]
    hw := by decide  
    g := ![![![535441557254711, -260976794222372, -383567808427795, 760348388017259], ![59571685510943, 102273061785175, -79404551, 0]], ![![-370705828580494, 180683806536263, 265558061964906, -526417076468535], ![-41243662801398, -70807391762650, 54974683, 0]]]
    h := ![![![300502912, 22488596, -720535708, 1418577365], ![-292316300, 1040773800, -11818, 0]], ![![7905757, 591639, -18956153, 37320523], ![-7690375, 27381108, -311, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R13N3 : Ideal.span {24} * I13N3 =  Ideal.span {B.equivFun.symm ![8, -6, -4, 7]} * (J0 ^ 4*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E13RS3 


noncomputable def E23RS0 : RelationCertificate Table 12 ![![23, 0, 0, 0], ![6, 1, 0, -1]] 
  ![-5, 0, -5, 8] ![![12, 0, 0, 0], ![2, 0, -5, 6]] where
    su := ![![276, 0, 0, 0], ![72, 12, 0, -12]]
    hsu := by decide  
    w := ![![-60, 0, -60, 96], ![-240, 84, 48, -96]]
    hw := by decide  
    g := ![![![1400015633, -1074650647, -609575248, 1791317468], ![1382984371, 444683359, -805, 0]], ![![365221468, -280343646, -159019629, 467300207], ![360778531, 116004354, -210, 0]]]
    h := ![![![-2206735, 5117750, 3277670, -6574684], ![-67285, -8407185, 19875, 0]], ![![-5619838, 13033271, 8347176, -16743616], ![-171387, -21410406, 50615, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R23N0 : Ideal.span {12} * I23N0 =  Ideal.span {B.equivFun.symm ![-5, 0, -5, 8]} * (J0 ^ 3*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 12 ![![23, 0, 0, 0], ![-10, 1, 0, -1]] 
  ![-1, 0, -1, 4] ![![12, 0, 0, 0], ![2, 0, -5, 6]] where
    su := ![![276, 0, 0, 0], ![-120, 12, 0, -12]]
    hsu := by decide  
    w := ![![-12, 0, -12, 48], ![48, 60, 96, -168]]
    hw := by decide  
    g := ![![![-7615763, 5589474, 3086972, -9189803], ![-7150421, -2325547, 30599, 0]], ![![2881618, -2114920, -1168032, 3477193], ![2705549, 879930, -11578, 0]]]
    h := ![![![-50023, -22104, 93795, -186312], ![28898, -239690, 38, 0]], ![![400058, 176759, -750063, 1489910], ![-231018, 1916761, -304, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R23N1 : Ideal.span {12} * I23N1 =  Ideal.span {B.equivFun.symm ![-1, 0, -1, 4]} * (J0 ^ 3*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E23RS1 
