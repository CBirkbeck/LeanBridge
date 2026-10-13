/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F1
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.ClassGroupData5_1_3790297_2

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 2 ![![37, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] 
  ![-15, 2, 6, 3, -16] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
    su := ![![74, 0, 0, 0, 0], ![4, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![-30, 4, 12, 6, -32], ![4, 2, 0, 0, 0]]
    hw := by decide  
    g := ![![![2353, 3768, -4741, 2373, -7064], ![1886, 14186, -4741, 0, 4704]], ![![147, 235, -296, 148, -441], ![119, 886, -296, 0, 294]]]
    h := ![![![-30399, 265480, 140588, 203, 560], ![559782, -5194510, -7508, -1296, 0]], ![![13854, -121005, -64080, -93, -256], ![-255114, 2367630, 3441, 592, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R37N1 : Ideal.span {2} * I37N1 =  Ideal.span {B.equivFun.symm ![-15, 2, 6, 3, -16]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E37RS1 


noncomputable def E37RS3 : RelationCertificate Table 2 ![![37, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] 
  ![3, -2, -2, -1, 6] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
    su := ![![74, 0, 0, 0, 0], ![-4, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![6, -4, -4, -2, 12], ![-2, -4, -2, 0, 2]]
    hw := by decide  
    g := ![![![-49, -86, -884, 0, 180], ![-42, 1641, -4, 0, -111]], ![![1, 2, 23, 0, -5], ![1, -42, 0, 0, 3]]]
    h := ![![![29061, -246941, 116842, -46, -498], ![535323, -4303626, 6309, 1152, 0]], ![![-107091, 909993, -430567, 167, 1837], ![-1972687, 15859148, -23171, -4248, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R37N3 : Ideal.span {2} * I37N3 =  Ideal.span {B.equivFun.symm ![3, -2, -2, -1, 6]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E37RS3 


noncomputable def E41RS1 : RelationCertificate Table 2 ![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] 
  ![5, -2, -2, -1, 6] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
    su := ![![82, 0, 0, 0, 0], ![8, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![10, -4, -4, -2, 12], ![-2, -2, -2, 0, 2]]
    hw := by decide  
    g := ![![![-5128, -8216, 41114, -20557, 15403], ![-4106, -92503, 41117, 0, -10269]], ![![-570, -913, 4568, -2284, 1712], ![-456, -10278, 4568, 0, -1141]]]
    h := ![![![5497, -90851, -23262, -60, -42], ![-56235, 945416, 2243, 108, 0]], ![![-23897, 394127, 100899, 256, 185], ![244470, -4101512, -9548, -474, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R41N1 : Ideal.span {2} * I41N1 =  Ideal.span {B.equivFun.symm ![5, -2, -2, -1, 6]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 4 ![![43, 0, 0, 0, 0], ![14, 1, 0, 0, 0]] 
  ![9, 0, -2, -1, 6] ![![4, 0, 0, 0, 0], ![2, 1, -1, 0, 2]] where
    su := ![![172, 0, 0, 0, 0], ![56, 4, 0, 0, 0]]
    hsu := by decide  
    w := ![![36, 0, -8, -4, 24], ![16, -4, -12, -4, 28]]
    hw := by decide  
    g := ![![![1026883, 918443, 295708, 404409, -2209295], ![-435522, 1617997, 301, 0, -63]], ![![334793, 299438, 96409, 131849, -720294], ![-141992, 527514, 98, 0, -21]]]
    h := ![![![2792877, -92210779, -7214120, -46851, -3918], ![-8575113, 283835090, 1888232, 10530, 0]], ![![-3823066, 126221508, 9874932, 64131, 5365], ![11738155, -388523935, -2584618, -14418, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R43N1 : Ideal.span {4} * I43N1 =  Ideal.span {B.equivFun.symm ![9, 0, -2, -1, 6]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 2 ![![53, 0, 0, 0, 0], ![-19, 1, 0, 0, 0]] 
  ![-2, -1, 2, 1, -5] ![![2, 0, 0, 0, 0], ![-2, 0, 1, 1, -4]] where
    su := ![![106, 0, 0, 0, 0], ![-38, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![-4, -2, 4, 2, -10], ![8, -4, 2, 2, -6]]
    hw := by decide  
    g := ![![![10791, -7378, 9377, 1988, -7951], ![10805, 14770, 0, 0, 0]], ![![-3852, 2635, -3350, -711, 2844], ![-3857, -5275, 0, 0, 0]]]
    h := ![![![45804, -634128, 37210, 134, -257], ![127590, -1762392, 10770, 851, 0]], ![![66910, -926854, 54389, 195, -375], ![186382, -2575952, 15748, 1242, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R53N1 : Ideal.span {2} * I53N1 =  Ideal.span {B.equivFun.symm ![-2, -1, 2, 1, -5]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 4 ![![59, 0, 0, 0, 0], ![5, 1, 0, 0, 0]] 
  ![1, -2, 0, 1, -2] ![![4, 0, 0, 0, 0], ![2, 1, -1, 0, 2]] where
    su := ![![236, 0, 0, 0, 0], ![20, 4, 0, 0, 0]]
    hsu := by decide  
    w := ![![4, -8, 0, 4, -8], ![4, 8, -8, 0, 0]]
    hw := by decide  
    g := ![![![-61975941, -59763300, -18946544, -23501047, 132995625], ![25305653, -96283792, -2321088, 0, -41448]], ![![-5634178, -5433028, -1722413, -2136459, 12090512], ![2300515, -8753073, -211008, 0, -3768]]]
    h := ![![![-3616, 19141, 3959, 28, 122], ![42309, -234776, -301, -450, 0]], ![![4250, -22632, -4685, -34, -144], ![-49725, 277534, 413, 531, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R59N1 : Ideal.span {4} * I59N1 =  Ideal.span {B.equivFun.symm ![1, -2, 0, 1, -2]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] 
  ![9, -2, -2, -1, 6] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
    su := ![![122, 0, 0, 0, 0], ![-16, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![18, -4, -4, -2, 12], ![-2, 2, -2, 0, 2]]
    hw := by decide  
    g := ![![![-50, -92, 285, 30, 165], ![-46, -687, -61, 0, -107]], ![![6, 11, -38, -4, -20], ![6, 90, 8, 0, 13]]]
    h := ![![![560373, -9200359, 1162982, 974, -5442], ![4262469, -69632896, 148065, 20748, 0]], ![![-157005, 2577959, -325862, -274, 1525], ![-1194256, 19511289, -41426, -5814, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![9, -2, -2, -1, 6]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 2 ![![61, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] 
  ![-3, 0, 2, 1, -4] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
    su := ![![122, 0, 0, 0, 0], ![-10, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![-6, 0, 4, 2, -8], ![0, 0, -2, 0, 4]]
    hw := by decide  
    g := ![![![-626, 0, 18375, -9472, 1821], ![-2454, -37969, 18954, 0, -1228]], ![![41, 0, -1178, 607, -118], ![160, 2435, -1215, 0, 80]]]
    h := ![![![-313848, 1691286, -328399, -49, 1116], ![-3825541, 19872836, -26795, -4255, 0]], ![![-101760, 548418, -106487, -16, 362], ![-1240368, 6444006, -8684, -1380, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R61N2 : Ideal.span {2} * I61N2 =  Ideal.span {B.equivFun.symm ![-3, 0, 2, 1, -4]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E61RS2 
