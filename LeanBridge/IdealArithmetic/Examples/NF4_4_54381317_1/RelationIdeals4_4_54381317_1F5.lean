/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F5
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

set_option linter.all false

noncomputable section


noncomputable def E277RS0 : RelationCertificate Table 3 ![![277, 0, 0, 0], ![32, 1, 0, 0]] 
  ![224, 127, 9, -2] ![![3, 0, 0, 0], ![-1, 1, 0, 0]] where
    su := ![![831, 0, 0, 0], ![96, 3, 0, 0]]
    hsu := by decide  
    w := ![![672, 381, 27, -6], ![-990, -567, -42, 9]]
    hw := by decide  
    g := ![![![-226593425, -2265920475, 2492513137, -1468], ![-679775681, -7477535072, 4432, 0]], ![![-25767813, -257676657, 283444398, -167], ![-77302947, -850332700, 504, 0]]]
    h := ![![![1248, -17217, -571, -1], ![-10796, 149376, 275, 0]], ![![-1986, 25230, 790, 0], ![17181, -218940, 3, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R277N0 : Ideal.span {3} * I277N0 =  Ideal.span {B.equivFun.symm ![224, 127, 9, -2]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E277RS0 


noncomputable def E277RS1 : RelationCertificate Table 9 ![![277, 0, 0, 0], ![-114, 1, 0, 0]] 
  ![-319, -147, -7, 2] ![![9, 0, 0, 0], ![-2, 1, 0, 0]] where
    su := ![![2493, 0, 0, 0], ![-1026, 9, 0, 0]]
    hsu := by decide  
    w := ![![-2871, -1323, -63, 18], ![1404, 639, 27, -9]]
    hw := by decide  
    g := ![![![3061239466, 130102689256, -65827339173, 5342263], ![13775578927, 592349891792, -48080348, 0]], ![![-1258493683, -53485986576, 27062009245, -2196236], ![-5663222134, -243518550944, 19766116, 0]]]
    h := ![![![-670501, 5157746, -51917, 59], ![-1629197, 12518128, -16341, 0]], ![![328044, -2523121, 25527, -30], ![797088, -6123750, 8309, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R277N1 : Ideal.span {9} * I277N1 =  Ideal.span {B.equivFun.symm ![-319, -147, -7, 2]} * (J0 ^ 0*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E277RS1 


noncomputable def E277RS2 : RelationCertificate Table 9 ![![277, 0, 0, 0], ![-113, 1, 0, 0]] 
  ![-544, -281, -15, 4] ![![9, 0, 0, 0], ![-4, 1, 0, 0]] where
    su := ![![2493, 0, 0, 0], ![-1017, 9, 0, 0]]
    hsu := by decide  
    w := ![![-4896, -2529, -135, 36], ![3708, 1908, 99, -27]]
    hw := by decide  
    g := ![![![431389345297092, 10461191623458778, -2642259757204260, 4314615], ![970626026918942, 23780337659512207, -38831523, 0]], ![![-174698978084500, -4236450218551001, 1070031247757175, -1747282], ![-393072700690327, -9630281166912426, 15725533, 0]]]
    h := ![![![-25398, -2762, -2442128, 21612], ![-62254, -7319, -5986520, 0]], ![![19320, 2182, 1844477, -16323], ![47356, 5766, 4521468, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R277N2 : Ideal.span {9} * I277N2 =  Ideal.span {B.equivFun.symm ![-544, -281, -15, 4]} * (J0 ^ 2*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E277RS2 


noncomputable def E277RS3 : RelationCertificate Table 3 ![![277, 0, 0, 0], ![-83, 1, 0, 0]] 
  ![-301, -141, -7, 2] ![![3, 0, 0, 0], ![1, 1, 0, 0]] where
    su := ![![831, 0, 0, 0], ![-249, 3, 0, 0]]
    hsu := by decide  
    w := ![![-903, -423, -21, 6], ![465, 222, 12, -3]]
    hw := by decide  
    g := ![![![37187, -372302, -409300, 240], ![-111705, 1228654, -723, 0]], ![![-11008, 110196, 121148, -71], ![33063, -363668, 214, 0]]]
    h := ![![![-150054, 681127, -8848, 8], ![-500779, 2267127, -2214, 0]], ![![77406, -350303, 4624, -5], ![258329, -1165972, 1384, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R277N3 : Ideal.span {3} * I277N3 =  Ideal.span {B.equivFun.symm ![-301, -141, -7, 2]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E277RS3 
