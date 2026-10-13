/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F1
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

set_option linter.all false

noncomputable section


noncomputable def E43RS1 : RelationCertificate Table 9 ![![43, 0, 0, 0], ![1, 1, 0, 0]] 
  ![611, 285, 14, -4] ![![9, 0, 0, 0], ![-2, 1, 0, 0]] where
    su := ![![387, 0, 0, 0], ![9, 9, 0, 0]]
    hsu := by decide  
    w := ![![5499, 2565, 126, -36], ![-2754, -1287, -63, 18]]
    hw := by decide  
    g := ![![![-108350, -4605715, 2330108, -77], ![-487659, -20969586, 692, 0]], ![![-5637, -239602, 121218, -4], ![-25364, -1090890, 36, 0]]]
    h := ![![![42, 26, -9, -1], ![-1195, 362, 39, 0]], ![![-24, -18, 2, 0], ![726, -95, 2, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R43N1 : Ideal.span {9} * I43N1 =  Ideal.span {B.equivFun.symm ![611, 285, 14, -4]} * (J0 ^ 0*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E43RS1 


noncomputable def E43RS2 : RelationCertificate Table 9 ![![43, 0, 0, 0], ![-18, 1, 0, 0]] 
  ![-617, -331, -21, 5] ![![9, 0, 0, 0], ![-4, 1, 0, 0]] where
    su := ![![387, 0, 0, 0], ![-162, 9, 0, 0]]
    hsu := by decide  
    w := ![![-5553, -2979, -189, 45], ![4383, 2367, 153, -36]]
    hw := by decide  
    g := ![![![345227441000655577, 8371765444265898356, -2114518076140398309, 2845685], ![776761742251475126, 19030662685161140120, -25611163, 0]], ![![-148528042290053000, -3601805025533785602, 909734259031471940, -1224306], ![-334188095152619287, -8187608331239172444, 11018753, 0]]]
    h := ![![![-8525, 92672, -5895, 43], ![-20331, 220272, -1844, 0]], ![![6799, -73096, 4669, -35], ![16215, -173732, 1501, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R43N2 : Ideal.span {9} * I43N2 =  Ideal.span {B.equivFun.symm ![-617, -331, -21, 5]} * (J0 ^ 2*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E43RS2 


noncomputable def E53RS1 : RelationCertificate Table 9 ![![53, 0, 0, 0], ![-10, 1, 0, 0]] 
  ![-167, -81, -5, 1] ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
    su := ![![477, 0, 0, 0], ![-90, 9, 0, 0]]
    hsu := by decide  
    w := ![![-1503, -729, -45, 9], ![-8676, -3897, -144, 63]]
    hw := by decide  
    g := ![![![-2828249528658967079, 8256997084489842346, 1695677916179129347, -277251225578274886], ![-1405182369803149648, -1090078660399632626, 130130, 0]], ![![466194983971818289, -1361043495085208171, -279507352849917790, 45700752127736436], ![231623470888891411, 179683298260457660, -21450, 0]]]
    h := ![![![-619, 21, -13566, 1357], ![-3264, -207, -71920, 0]], ![![-3648, 115, -74485, 7451], ![-19238, -1271, -394896, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R53N1 : Ideal.span {9} * I53N1 =  Ideal.span {B.equivFun.symm ![-167, -81, -5, 1]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E53RS1 


noncomputable def E53RS2 : RelationCertificate Table 9 ![![53, 0, 0, 0], ![-1, 1, 0, 0]] 
  ![440, 280, 27, -5] ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
    su := ![![477, 0, 0, 0], ![-9, 9, 0, 0]]
    hsu := by decide  
    w := ![![3960, 2520, 243, -45], ![8982, 5031, 378, -81]]
    hw := by decide  
    g := ![![![98578328308, -288131857950, -31866261267, -6929887757], ![2082720379613, 773224011049, -2756, 0]], ![![-5685, 17822, 1961, 422], ![-127562, -47361, 0, 0]]]
    h := ![![![27, -439, 427, -1], ![991, -22556, 48, 0]], ![![60, -998, 969, -1], ![2182, -51271, 44, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R53N2 : Ideal.span {9} * I53N2 =  Ideal.span {B.equivFun.symm ![440, 280, 27, -5]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E53RS2 


noncomputable def E61RS1 : RelationCertificate Table 9 ![![61, 0, 0, 0], ![-8, 1, 0, 0]] 
  ![53, 17, -2, 0] ![![9, 0, 0, 0], ![-128, -67, -4, 1]] where
    su := ![![549, 0, 0, 0], ![-72, 9, 0, 0]]
    hsu := by decide  
    w := ![![477, 153, -18, 0], ![2025, 1143, 81, -18]]
    hw := by decide  
    g := ![![![53, -179, -51, 1], ![1147, 399, 0, 0]], ![![99, 80, 10, -1], ![-134, -50, 0, 0]]]
    h := ![![![193, -8, 5150, -644], ![1465, 120, 39284, 0]], ![![1533, -25470, 3216, -7], ![11661, -192767, 425, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R61N1 : Ideal.span {9} * I61N1 =  Ideal.span {B.equivFun.symm ![53, 17, -2, 0]} * (J0 ^ 2*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E61RS1 
