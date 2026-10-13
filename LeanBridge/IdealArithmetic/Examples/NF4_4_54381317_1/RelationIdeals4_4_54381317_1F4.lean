/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F4
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

set_option linter.all false

noncomputable section


noncomputable def E181RS0 : RelationCertificate Table 9 ![![181, 0, 0, 0], ![37, 1, 0, 0]] 
  ![-283, -138, -7, 2] ![![9, 0, 0, 0], ![-2, 1, 0, 0]] where
    su := ![![1629, 0, 0, 0], ![333, 9, 0, 0]]
    hsu := by decide  
    w := ![![-2547, -1242, -63, 18], ![1332, 657, 36, -9]]
    hw := by decide  
    g := ![![![227835, 9687402, -4900727, 8], ![1025753, 44106400, -67, 0]], ![![57804, 2457478, -1243204, 2], ![260214, 11188800, -17, 0]]]
    h := ![![![-64596, 10258, -11166202, -301798], ![315989, -58725, 54625440, 0]], ![![33744, -5423, 5876317, 158824], ![-165068, 30992, -28747145, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R181N0 : Ideal.span {9} * I181N0 =  Ideal.span {B.equivFun.symm ![-283, -138, -7, 2]} * (J0 ^ 0*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E181RS0 


noncomputable def E181RS1 : RelationCertificate Table 3 ![![181, 0, 0, 0], ![64, 1, 0, 0]] 
  ![-175, -74, -3, 1] ![![3, 0, 0, 0], ![-1, 1, 0, 0]] where
    su := ![![543, 0, 0, 0], ![192, 3, 0, 0]]
    hsu := by decide  
    w := ![![-525, -222, -9, 3], ![558, 231, 9, -3]]
    hw := by decide  
    g := ![![![25028, 247361, -271862, -3], ![74111, 815628, 0, 0]], ![![8886, 87880, -96590, -1], ![26333, 289784, 0, 0]]]
    h := ![![![-42515, 2830591, 49102, 76], ![120235, -8007145, -13755, 0]], ![![44946, -3008857, -52272, -82], ![-127110, 8511411, 14841, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R181N1 : Ideal.span {3} * I181N1 =  Ideal.span {B.equivFun.symm ![-175, -74, -3, 1]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E181RS1 


noncomputable def E181RS2 : RelationCertificate Table 3 ![![181, 0, 0, 0], ![-89, 1, 0, 0]] 
  ![98, 60, 5, -1] ![![3, 0, 0, 0], ![1, 1, 0, 0]] where
    su := ![![543, 0, 0, 0], ![-267, 3, 0, 0]]
    hsu := by decide  
    w := ![![294, 180, 15, -3], ![-285, -174, -15, 3]]
    hw := by decide  
    g := ![![![-2730, 24959, 27525, -1], ![7410, -82592, 7, 0]], ![![838, -7207, -7963, 0], ![-2122, 23896, -2, 0]]]
    h := ![![![55806, -1391382, 18741, -35], ![113492, -2828390, 6334, 0]], ![![-53847, 1348996, -18087, 33], ![-109508, 2742234, -5972, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R181N2 : Ideal.span {3} * I181N2 =  Ideal.span {B.equivFun.symm ![98, 60, 5, -1]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E181RS2 


noncomputable def E181RS3 : RelationCertificate Table 9 ![![181, 0, 0, 0], ![-13, 1, 0, 0]] 
  ![599, 331, 21, -5] ![![9, 0, 0, 0], ![-4, 1, 0, 0]] where
    su := ![![1629, 0, 0, 0], ![-117, 9, 0, 0]]
    hsu := by decide  
    w := ![![5391, 2979, 189, -45], ![-4311, -2385, -153, 36]]
    hw := by decide  
    g := ![![![6037725, 146419504, -27736704, -2311392], ![13585402, 332840459, 20802540, 0]], ![![-416977, -10112127, 1915572, 159631], ![-938242, -22986865, -1436680, 0]]]
    h := ![![![1351, -100231, 7754, -4], ![18764, -1394106, 719, 0]], ![![-1042, 80174, -6187, 2], ![-14471, 1115176, -358, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R181N3 : Ideal.span {9} * I181N3 =  Ideal.span {B.equivFun.symm ![599, 331, 21, -5]} * (J0 ^ 2*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E181RS3 


noncomputable def E193RS0 : RelationCertificate Table 9 ![![193, 0, 0, 0], ![21, 1, 0, 0]] 
  ![86, 63, 5, -1] ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
    su := ![![1737, 0, 0, 0], ![189, 9, 0, 0]]
    hsu := by decide  
    w := ![![774, 567, 45, -9], ![-7029, -2763, -108, 36]]
    hw := by decide  
    g := ![![![-43074774, 125755286, 25825972, -4222435], ![-21398822, -16600572, 193, 0]], ![![-5133325, 14985831, 3077609, -503175], ![-2550031, -1978244, 23, 0]]]
    h := ![![![368, -6, 17492, 833], ![-3378, 219, -160770, 0]], ![![-3739, -148, -97985, -4666], ![34326, -289, 900542, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R193N0 : Ideal.span {9} * I193N0 =  Ideal.span {B.equivFun.symm ![86, 63, 5, -1]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E193RS0 


noncomputable def E193RS1 : RelationCertificate Table 9 ![![193, 0, 0, 0], ![34, 1, 0, 0]] 
  ![893, 373, 15, -5] ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
    su := ![![1737, 0, 0, 0], ![306, 9, 0, 0]]
    hsu := by decide  
    w := ![![8037, 3357, 135, -45], ![-40824, -19098, -963, 270]]
    hw := by decide  
    g := ![![![-6436909398888, 18814263716651, 2080784447377, 452503723228], ![-135996242755038, -50489524343689, 298, 0]], ![![-1166419837405, 3409296148953, 377054904199, 81997319918], ![-24643614742571, -9149108543408, 54, 0]]]
    h := ![![![186449, -35143, 46132556, 1356875], ![-1058346, 230627, -261876880, 0]], ![![-2108178, 241628849, 7322103, 6281], ![11966877, -1371951084, -1212203, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R193N1 : Ideal.span {9} * I193N1 =  Ideal.span {B.equivFun.symm ![893, 373, 15, -5]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E193RS1 


noncomputable def E193RS2 : RelationCertificate Table 9 ![![193, 0, 0, 0], ![59, 1, 0, 0]] 
  ![-217, -117, -10, 2] ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
    su := ![![1737, 0, 0, 0], ![531, 9, 0, 0]]
    hsu := by decide  
    w := ![![-1953, -1053, -90, 18], ![-1944, 819, 342, -36]]
    hw := by decide  
    g := ![![![5900834482154504665, -17227324753877287381, -3537847215046152306, 578454473529662264], ![2931759909234683436, 2274330352522591557, -745030, 0]], ![![1815641379532377728, -5300715310076215295, -1088568374104920004, 177985991895268285], ![902079972274877938, 699793954779556509, -229240, 0]]]
    h := ![![![-4516, 85040, 1560, 2], ![14769, -278434, -384, 0]], ![![-4527, 86688, 1590, 2], ![14805, -283822, -390, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R193N2 : Ideal.span {9} * I193N2 =  Ideal.span {B.equivFun.symm ![-217, -117, -10, 2]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E193RS2 


noncomputable def E193RS3 : RelationCertificate Table 9 ![![193, 0, 0, 0], ![78, 1, 0, 0]] 
  ![230, 130, 9, -2] ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
    su := ![![1737, 0, 0, 0], ![702, 9, 0, 0]]
    hsu := by decide  
    w := ![![2070, 1170, 81, -18], ![6732, 3627, 225, -54]]
    hw := by decide  
    g := ![![![389892015, -1139604032, -126035771, -27408733], ![8237467281, 3058215372, -11, 0]], ![![212584969, -621358437, -68719825, -14944355], ![4491401926, 1667463305, -6, 0]]]
    h := ![![![190634, -22950760, -335455, -528], ![-471694, 56794468, 101902, 0]], ![![620272, -74646123, -1090871, -1715], ![-1534766, 184720986, 330989, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R193N3 : Ideal.span {9} * I193N3 =  Ideal.span {B.equivFun.symm ![230, 130, 9, -2]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E193RS3 


noncomputable def E229RS0 : RelationCertificate Table 9 ![![229, 0, 0, 0], ![44, 1, 0, 0]] 
  ![212, 130, 9, -2] ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
    su := ![![2061, 0, 0, 0], ![396, 9, 0, 0]]
    hsu := by decide  
    w := ![![1908, 1170, 81, -18], ![14418, 7407, 423, -108]]
    hw := by decide  
    g := ![![![830545925194, -2427579617821, -268480870983, -58385958224], ![17547415728858, 6514596694534, -286, 0]], ![![159720508349, -466842637806, -51630981366, -11228078597], ![3374505942314, 1252808139795, -55, 0]]]
    h := ![![![55708, -7772, 11226703, 255157], ![-289930, 47042, -58430955, 0]], ![![421082, -48353, 72195294, 1640832], ![-2191504, 301481, -375750540, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R229N0 : Ideal.span {9} * I229N0 =  Ideal.span {B.equivFun.symm ![212, 130, 9, -2]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E229RS0 


noncomputable def E229RS1 : RelationCertificate Table 9 ![![229, 0, 0, 0], ![70, 1, 0, 0]] 
  ![104, 63, 5, -1] ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
    su := ![![2061, 0, 0, 0], ![630, 9, 0, 0]]
    hsu := by decide  
    w := ![![936, 567, 45, -9], ![-2007, -1071, -108, 18]]
    hw := by decide  
    g := ![![![-2743730667, 8010246394, 1645006320, -268965434], ![-1363182657, -1057498108, 627, 0]], ![![-848938765, 2478453084, 508981977, -83220688], ![-421782816, -327200857, 194, 0]]]
    h := ![![![2006, -40804, -653, -1], ![-6561, 133582, 228, 0]], ![![-4687, 87479, 1320, 1], ![15330, -286402, -227, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R229N1 : Ideal.span {9} * I229N1 =  Ideal.span {B.equivFun.symm ![104, 63, 5, -1]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E229RS1 
