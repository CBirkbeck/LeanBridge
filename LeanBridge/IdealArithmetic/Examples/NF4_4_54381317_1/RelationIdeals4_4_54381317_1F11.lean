/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F11
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

set_option linter.all false

noncomputable section


noncomputable def E607RS1 : RelationCertificate Table 9 ![![607, 0, 0, 0], ![90, 1, 0, 0]] 
  ![-712, -332, -9, 4] ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
    su := ![![5463, 0, 0, 0], ![810, 9, 0, 0]]
    hsu := by decide  
    w := ![![-6408, -2988, -81, 36], ![-16164, -8865, -477, 126]]
    hw := by decide  
    g := ![![![-228853837, 668926777, 73952700, 16086667], ![-4835449553, -1795109282, 31564, 0]], ![![-33743676, 98630891, 10904064, 2371922], ![-712969919, -264682509, 4654, 0]]]
    h := ![![![-968326, 172959485, 1963201, 459], ![6530813, -1166588206, -278609, 0]], ![![-2442698, 436189372, 4950978, 1157], ![16474621, -2942038049, -702285, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R607N1 : Ideal.span {9} * I607N1 =  Ideal.span {B.equivFun.symm ![-712, -332, -9, 4]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E607RS1 


noncomputable def E607RS2 : RelationCertificate Table 9 ![![607, 0, 0, 0], ![303, 1, 0, 0]] 
  ![-68, -18, 4, 1] ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
    su := ![![5463, 0, 0, 0], ![2727, 9, 0, 0]]
    hsu := by decide  
    w := ![![-612, -162, 36, 9], ![-8631, -4365, -459, 18]]
    hw := by decide  
    g := ![![![3464870857, -10115577874, -2077317128, 339669870], ![1721666003, 1335568131, 15782, 0]], ![![1740997577, -5082786313, -1043791971, 170674318], ![865087537, 671084483, 7930, 0]]]
    h := ![![![-150053, 112283879, 444204, 243], ![300601, -224939324, -147500, 0]], ![![-2108021, 1583408043, 6265990, 3433], ![4222996, -3172055794, -2083829, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R607N2 : Ideal.span {9} * I607N2 =  Ideal.span {B.equivFun.symm ![-68, -18, 4, 1]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E607RS2 


noncomputable def E617RS0 : RelationCertificate Table 9 ![![617, 0, 0, 0], ![35, 1, 0, 0]] 
  ![188, 84, 2, -1] ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
    su := ![![5553, 0, 0, 0], ![315, 9, 0, 0]]
    hsu := by decide  
    w := ![![1692, 756, 18, -9], ![14535, 7857, 585, -126]]
    hw := by decide  
    g := ![![![4268, -12905, -2642, 433], ![2227, 1708, 0, 0]], ![![449351, -1311969, -269430, 44052], ![223261, 173196, -1, 0]]]
    h := ![![![107869, -27451445, -786935, -72], ![-1901571, 483984092, 44423, 0]], ![![926735, -235776847, -6758867, -618], ![-16336968, 4156875784, 381292, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R617N0 : Ideal.span {9} * I617N0 =  Ideal.span {B.equivFun.symm ![188, 84, 2, -1]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E617RS0 


noncomputable def E617RS1 : RelationCertificate Table 9 ![![617, 0, 0, 0], ![236, 1, 0, 0]] 
  ![194, 130, 9, -2] ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
    su := ![![5553, 0, 0, 0], ![2124, 9, 0, 0]]
    hsu := by decide  
    w := ![![1746, 1170, 81, -18], ![22104, 11187, 621, -162]]
    hw := by decide  
    g := ![![![6450130080045, -18852906091912, -2085058115735, -453433113076], ![136275563907524, 50593224124879, -32084, 0]], ![![2477602619676, -7241715893392, -800905622821, -174171226741], ![52345718598472, 19433701810452, -12324, 0]]]
    h := ![![![26378, -3493580, -16691, -8], ![-68962, 9133932, 4934, 0]], ![![335648, -44248339, -211564, -102], ![-877510, 115686881, 62916, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R617N1 : Ideal.span {9} * I617N1 =  Ideal.span {B.equivFun.symm ![194, 130, 9, -2]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E617RS1 


noncomputable def E617RS2 : RelationCertificate Table 9 ![![617, 0, 0, 0], ![-140, 1, 0, 0]] 
  ![-679, -348, -19, 5] ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
    su := ![![5553, 0, 0, 0], ![-1260, 9, 0, 0]]
    hsu := by decide  
    w := ![![-6111, -3132, -171, 45], ![-23985, -12132, -720, 180]]
    hw := by decide  
    g := ![![![-11818981010, 34505193185, 7086078971, -1158604814], ![-5872100838, -4555320154, 1719, 0]], ![![2674568418, -7808330204, -1603539611, 262185720], ![1328823228, 1030843198, -389, 0]]]
    h := ![![![-24507, -1631, -5228986, 37350], ![-108001, -7957, -23044945, 0]], ![![-96885, -6253, -20282866, 144878], ![-426967, -30598, -89389706, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R617N2 : Ideal.span {9} * I617N2 =  Ideal.span {B.equivFun.symm ![-679, -348, -19, 5]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E617RS2 


noncomputable def E617RS3 : RelationCertificate Table 9 ![![617, 0, 0, 0], ![-132, 1, 0, 0]] 
  ![-359, -151, -6, 2] ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
    su := ![![5553, 0, 0, 0], ![-1188, 9, 0, 0]]
    hsu := by decide  
    w := ![![-3231, -1359, -54, 18], ![15030, 6993, 351, -99]]
    hw := by decide  
    g := ![![![52990900523157, -154885631471401, -17129748895716, -3725169689008], ![1119568868278207, 415647509703228, -353, 0]], ![![-11258689912391, 32907712069221, 3639465062841, 791466647803], ![-237868739719156, -88310377415700, 75, 0]]]
    h := ![![![-37231, 6410917, -50677, 16], ![-174024, 29964863, -9870, 0]], ![![173314, -29817510, 235778, -75], ![810099, -139368139, 46264, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R617N3 : Ideal.span {9} * I617N3 =  Ideal.span {B.equivFun.symm ![-359, -151, -6, 2]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E617RS3 


noncomputable def E619RS1 : RelationCertificate Table 9 ![![619, 0, 0, 0], ![217, 1, 0, 0]] 
  ![719, 414, 35, -7] ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
    su := ![![5571, 0, 0, 0], ![1953, 9, 0, 0]]
    hsu := by decide  
    w := ![![6471, 3726, 315, -63], ![-6219, -6912, -1134, 162]]
    hw := by decide  
    g := ![![![-2921009973172107, 8527808668621851, 1751292484860418, -286344460520435], ![-1451269244889121, -1125830837876805, 4762920, 0]], ![![-1045414095682922, 3052057839357981, 626778363015366, -102481175346230], ![-519401624497144, -402928931458804, 1704624, 0]]]
    h := ![![![750194, -209530, 423315460, 1950767], ![-2139951, 607555, -1207524780, 0]], ![![-1736704, 581042808, 2970163, 1348], ![4954005, -1657467525, -834394, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R619N1 : Ideal.span {9} * I619N1 =  Ideal.span {B.equivFun.symm ![719, 414, 35, -7]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E619RS1 


noncomputable def E619RS2 : RelationCertificate Table 9 ![![619, 0, 0, 0], ![272, 1, 0, 0]] 
  ![-293, -148, -9, 2] ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
    su := ![![5571, 0, 0, 0], ![2448, 9, 0, 0]]
    hsu := by decide  
    w := ![![-2637, -1332, -81, 18], ![-513, -639, -72, 9]]
    hw := by decide  
    g := ![![![-7045928, 20595469, 2276414, 495262], ![-148881579, -55269260, 1518, 0]], ![![-3109883, 9090217, 1004741, 218594], ![-65711892, -24394204, 670, 0]]]
    h := ![![![-16799, 562405, 2339, 1], ![38229, -1280026, -617, 0]], ![![-3243, 107823, 396, 0], ![7380, -245404, 1, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R619N2 : Ideal.span {9} * I619N2 =  Ideal.span {B.equivFun.symm ![-293, -148, -9, 2]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E619RS2 


noncomputable def E631RS1 : RelationCertificate Table 3 ![![631, 0, 0, 0], ![191, 1, 0, 0]] 
  ![-16, -4, 1, 0] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![1893, 0, 0, 0], ![573, 3, 0, 0]]
    hsu := by decide  
    w := ![![-48, -12, 3, 0], ![-585, -345, -27, 6]]
    hw := by decide  
    g := ![![![-1189, 2774, 783, -45], ![-4867, -1722, 0, 0]], ![![-311, 866, 239, -14], ![-1478, -523, 0, 0]]]
    h := ![![![-11783, 3691395, 20855, 8], ![38927, -12195336, -5048, 0]], ![![-142710, 44968984, 255116, 103], ![471465, -148564924, -64991, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R631N1 : Ideal.span {3} * I631N1 =  Ideal.span {B.equivFun.symm ![-16, -4, 1, 0]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E631RS1 


noncomputable def E631RS2 : RelationCertificate Table 3 ![![631, 0, 0, 0], ![295, 1, 0, 0]] 
  ![-153, -73, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![1893, 0, 0, 0], ![885, 3, 0, 0]]
    hsu := by decide  
    w := ![![-459, -219, -12, 3], ![510, 201, 6, -3]]
    hw := by decide  
    g := ![![![1144366, -2425343, -733440, 36201], ![5189036, 1765858, 0, 0]], ![![537311, -1138541, -344313, 16994], ![2436012, 828988, 0, 0]]]
    h := ![![![-129408, 72002416, 287737, 148], ![276801, -154012886, -93387, 0]], ![![142410, -80006901, -319886, -165], ![-304612, 171134438, 104114, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R631N2 : Ideal.span {3} * I631N2 =  Ideal.span {B.equivFun.symm ![-153, -73, -4, 1]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E631RS2 
