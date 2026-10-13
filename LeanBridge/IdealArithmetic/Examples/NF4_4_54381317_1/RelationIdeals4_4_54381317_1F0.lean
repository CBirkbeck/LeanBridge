/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F0
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 9 ![![3, 0, 0, 0], ![-132, -67, -4, 1]] 
  ![-126, -67, -4, 1] ![![9, 0, 0, 0], ![-128, -67, -4, 1]] where
    su := ![![27, 0, 0, 0], ![-1188, -603, -36, 9]]
    hsu := by decide  
    w := ![![-1134, -603, -36, 9], ![-1107, -603, -36, 9]]
    hw := by decide  
    g := ![![![127, 67, 4, -1], ![10, 0, 0, 0]], ![![25, -66, -22, 0], ![592, 198, 0, 0]]]
    h := ![![![152, -159, -54, 3], ![370, 126, 0, 0]], ![![140, -160, -53, 3], ![361, 123, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R3N0 : Ideal.span {9} * I3N0 =  Ideal.span {B.equivFun.symm ![-126, -67, -4, 1]} * (J0 ^ 2*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0, 0], ![1, 1, 0, 0]] 
  ![1, 0, 0, 0] ![![3, 0, 0, 0], ![1, 1, 0, 0]] where
    su := ![![3, 0, 0, 0], ![1, 1, 0, 0]]
    hsu := by decide  
    w := ![![3, 0, 0, 0], ![1, 1, 0, 0]]
    hw := by decide  
    g := ![![![0, -2, 1, 2], ![3, 3, -6, 0]], ![![0, 0, 1, 1], ![1, 0, -3, 0]]]
    h := ![![![0, -2, 1, 2], ![3, 3, -6, 0]], ![![0, 0, 1, 1], ![1, 0, -3, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS1 


noncomputable def E3RS2 : RelationCertificate Table 1 ![![3, 0, 0, 0], ![-1, 1, 0, 0]] 
  ![1, 0, 0, 0] ![![3, 0, 0, 0], ![-1, 1, 0, 0]] where
    su := ![![3, 0, 0, 0], ![-1, 1, 0, 0]]
    hsu := by decide  
    w := ![![3, 0, 0, 0], ![-1, 1, 0, 0]]
    hw := by decide  
    g := ![![![2, 1, 0, -2], ![3, 6, 6, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0]]]
    h := ![![![2, 1, 0, -2], ![3, 6, 6, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R3N2 : Ideal.span {1} * I3N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS2 


noncomputable def E5RS0 : RelationCertificate Table 3 ![![5, 0, 0, 0], ![-133, -67, -4, 1]] 
  ![-138, -67, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![15, 0, 0, 0], ![-399, -201, -12, 3]]
    hsu := by decide  
    w := ![![-414, -201, -12, 3], ![843, 402, 24, -6]]
    hw := by decide  
    g := ![![![42, 0, -4, 0], ![37, 12, 0, 0]], ![![-198, 603, 174, -9], ![-1214, -414, 0, 0]]]
    h := ![![![2619, -6322, -1789, 132], ![18256, 6305, 0, 0]], ![![-5138, 13009, 3658, -271], ![-37257, -12870, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![-138, -67, -4, 1]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 9 ![![5, 0, 0, 0], ![2, 1, 0, 0]] 
  ![-73, -50, -6, 1] ![![9, 0, 0, 0], ![-4, 1, 0, 0]] where
    su := ![![45, 0, 0, 0], ![18, 9, 0, 0]]
    hsu := by decide  
    w := ![![-657, -450, -54, 9], ![675, 459, 54, -9]]
    hw := by decide  
    g := ![![![-615, -14567, 3677, 0], ![-1339, -33092, 1, 0]], ![![5, 15, -4, 0], ![10, 36, 0, 0]]]
    h := ![![![-1939, 2265, 1811, 97], ![4811, -8093, -484, 0]], ![![1983, -2341, -1868, -101], ![-4920, 8338, 504, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R5N1 : Ideal.span {9} * I5N1 =  Ideal.span {B.equivFun.symm ![-73, -50, -6, 1]} * (J0 ^ 2*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 9 ![![5, 0, 0, 0], ![-1, 1, 0, 0]] 
  ![620, 285, 14, -4] ![![9, 0, 0, 0], ![-2, 1, 0, 0]] where
    su := ![![45, 0, 0, 0], ![-9, 9, 0, 0]]
    hsu := by decide  
    w := ![![5580, 2565, 126, -36], ![-2772, -1278, -63, 18]]
    hw := by decide  
    g := ![![![-2392430, -101678778, 51438757, -627], ![-10765986, -462937524, 5642, 0]], ![![-683565, -29051080, 14696783, -179], ![-3075994, -132267828, 1612, 0]]]
    h := ![![![414, -630, 416, -17], ![1450, -1985, 81, 0]], ![![-204, 312, -207, 8], ![-712, 990, -38, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R5N2 : Ideal.span {9} * I5N2 =  Ideal.span {B.equivFun.symm ![620, 285, 14, -4]} * (J0 ^ 0*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 9 ![![7, 0, 0, 0], ![-134, -65, -4, 1]] 
  ![-166, -71, -3, 1] ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
    su := ![![63, 0, 0, 0], ![-1206, -585, -36, 9]]
    hsu := by decide  
    w := ![![-1494, -639, -27, 9], ![6921, 3222, 162, -45]]
    hw := by decide  
    g := ![![![222616353, -650679587, -71960141, -15649408], ![4703364872, 1746148488, -2820, 0]], ![![-5906771887, 17264775614, 1909350740, 415232681], ![-124796480465, -46331337642, 74824, 0]]]
    h := ![![![9346, -23706, -7967, 258], ![46741, 16182, 0, 0]], ![![-42051, 107279, 36026, -1168], ![-211309, -73160, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R7N0 : Ideal.span {9} * I7N0 =  Ideal.span {B.equivFun.symm ![-166, -71, -3, 1]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 9 ![![7, 0, 0, 0], ![-132, -70, -4, 1]] 
  ![482, 264, 17, -4] ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
    su := ![![63, 0, 0, 0], ![-1188, -630, -36, 9]]
    hsu := by decide  
    w := ![![4338, 2376, 153, -36], ![6939, 3429, 135, -45]]
    hw := by decide  
    g := ![![![668761213641, -1952430060148, -400956006759, 65558169631], ![332266087184, 257757415057, -1880, 0]], ![![-24610430383360, 71849477949138, 14755191673334, -2412542379590], ![-12227400812737, -9485479704181, 69184, 0]]]
    h := ![![![5066, -4458, -3541, -265], ![-46461, -16104, 0, 0]], ![![7278, -6457, -5113, -382], ![-67054, -23241, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R7N1 : Ideal.span {9} * I7N1 =  Ideal.span {B.equivFun.symm ![482, 264, 17, -4]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 3 ![![11, 0, 0, 0], ![-130, -67, -4, 1]] 
  ![-141, -67, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![33, 0, 0, 0], ![-390, -201, -12, 3]]
    hsu := by decide  
    w := ![![-423, -201, -12, 3], ![1236, 603, 36, -9]]
    hw := by decide  
    g := ![![![-66, 469, 126, -7], ![-862, -294, 0, 0]], ![![-6273, 13333, 4030, -199], ![-28510, -9702, 0, 0]]]
    h := ![![![63, -1036, -280, 12], ![7525, 2552, 0, 0]], ![![210, 3222, 828, -38], ![-21893, -7436, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R11N0 : Ideal.span {3} * I11N0 =  Ideal.span {B.equivFun.symm ![-141, -67, -4, 1]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 9 ![![11, 0, 0, 0], ![-133, -67, -4, 1]] 
  ![-144, -67, -4, 1] ![![9, 0, 0, 0], ![-128, -67, -4, 1]] where
    su := ![![99, 0, 0, 0], ![-1197, -603, -36, 9]]
    hsu := by decide  
    w := ![![-1296, -603, -36, 9], ![1197, 603, 36, -9]]
    hw := by decide  
    g := ![![![3, -12, -4, 0], ![107, 36, 0, 0]], ![![98, 157, 34, -1], ![-802, -270, 0, 0]]]
    h := ![![![48, -145, -40, 3], ![892, 308, 0, 0]], ![![15, 153, 36, -3], ![-760, -264, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R11N1 : Ideal.span {9} * I11N1 =  Ideal.span {B.equivFun.symm ![-144, -67, -4, 1]} * (J0 ^ 2*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 9 ![![13, 0, 0, 0], ![-136, -62, -4, 1]] 
  ![341, 151, 6, -2] ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
    su := ![![117, 0, 0, 0], ![-1224, -558, -36, 9]]
    hsu := by decide  
    w := ![![3069, 1359, 54, -18], ![-7344, -3213, -153, 45]]
    hw := by decide  
    g := ![![![-3525509427766, 10304613596397, 1139650216079, 247837283943], ![-74485441111838, -27653223472462, 15, 0]], ![![52406749963583, -153178234023250, -16940917373672, -3684104903597], ![1107227187448048, 411065577275858, -223, 0]]]
    h := ![![![-87949, 315475, 109338, -2408], ![-616788, -216030, 0, 0]], ![![211038, -755469, -261881, 5765], ![1477398, 517446, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R13N0 : Ideal.span {9} * I13N0 =  Ideal.span {B.equivFun.symm ![341, 151, 6, -2]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 9 ![![13, 0, 0, 0], ![-134, -70, -4, 1]] 
  ![-206, -84, -2, 1] ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
    su := ![![117, 0, 0, 0], ![-1206, -630, -36, 9]]
    hsu := by decide  
    w := ![![-1854, -756, -18, 9], ![-19557, -9549, -585, 144]]
    hw := by decide  
    g := ![![![-11312075876283, 33025295887738, 6782158736335, -1108914495938], ![-5620271275761, -4359959187540, 11, 0]], ![![288961850611940, -843616213441216, -173247170639799, 28326718139695], ![143567282130685, 111373181122915, -281, 0]]]
    h := ![![![-68654, 2790, 24646, 3154], ![685605, 242202, 0, 0]], ![![-718873, 29101, 257995, 33019], ![7177155, 2535462, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R13N1 : Ideal.span {9} * I13N1 =  Ideal.span {B.equivFun.symm ![-206, -84, -2, 1]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS1 


noncomputable def E17RS0 : RelationCertificate Table 3 ![![17, 0, 0, 0], ![-129, -67, -4, 1]] 
  ![-129, -67, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![51, 0, 0, 0], ![-387, -201, -12, 3]]
    hsu := by decide  
    w := ![![-387, -201, -12, 3], ![-336, -201, -12, 3]]
    hw := by decide  
    g := ![![![681, -1206, -376, 18], ![2683, 912, 0, 0]], ![![683, -1206, -376, 18], ![2682, 912, 0, 0]]]
    h := ![![![-725, -1347, -290, 13], ![11918, 4046, 0, 0]], ![![-606, -1143, -247, 11], ![10167, 3451, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R17N0 : Ideal.span {3} * I17N0 =  Ideal.span {B.equivFun.symm ![-129, -67, -4, 1]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0, 0], ![7, 1, 0, 0]] 
  ![31, 16, 2, 0] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![51, 0, 0, 0], ![21, 3, 0, 0]]
    hsu := by decide  
    w := ![![93, 48, 6, 0], ![-231, -87, 6, 3]]
    hw := by decide  
    g := ![![![89, 36, 1, 0], ![-39, -17, 0, 0]], ![![126, 72, 6, -1], ![-19, -8, 0, 0]]]
    h := ![![![106, -300, -52, -1], ![-253, 767, 17, 0]], ![![-287, 751, 127, 2], ![686, -1926, -33, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![31, 16, 2, 0]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 9 ![![19, 0, 0, 0], ![-131, -67, -4, 1]] 
  ![-243, -134, -8, 2] ![![9, 0, 0, 0], ![-128, -67, -4, 1]] where
    su := ![![171, 0, 0, 0], ![-1179, -603, -36, 9]]
    hsu := by decide  
    w := ![![-2187, -1206, -72, 18], ![-3366, -1809, -108, 27]]
    hw := by decide  
    g := ![![![95, 175, 40, -1], ![-965, -324, 0, 0]], ![![71, -216, -72, 0], ![1945, 648, 0, 0]]]
    h := ![![![-117879, -203680, -40196, 3040], ![1540294, 532684, 0, 0]], ![![-181653, -313828, -61931, 4684], ![2373122, 820705, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R19N0 : Ideal.span {9} * I19N0 =  Ideal.span {B.equivFun.symm ![-243, -134, -8, 2]} * (J0 ^ 2*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 3 ![![19, 0, 0, 0], ![-132, -67, -4, 1]] 
  ![-132, -67, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![57, 0, 0, 0], ![-396, -201, -12, 3]]
    hsu := by decide  
    w := ![![-396, -201, -12, 3], ![57, 0, 0, 0]]
    hw := by decide  
    g := ![![![-2206, 4958, 1486, -74], ![-10487, -3570, 0, 0]], ![![21162, -44823, -13556, 669], ![95913, 32640, 0, 0]]]
    h := ![![![-11100, -21489, -4284, 363], ![154528, 53808, 0, 0]], ![![1777, 3320, 656, -56], ![-23560, -8208, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R19N1 : Ideal.span {3} * I19N1 =  Ideal.span {B.equivFun.symm ![-132, -67, -4, 1]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 9 ![![23, 0, 0, 0], ![-131, -64, -4, 1]] 
  ![464, 264, 17, -4] ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
    su := ![![207, 0, 0, 0], ![-1179, -576, -36, 9]]
    hsu := by decide  
    w := ![![4176, 2376, 153, -36], ![1917, 1737, 135, -27]]
    hw := by decide  
    g := ![![![175349963308, -511929423688, -105131140117, 17189425170], ![87120506979, 67584263131, -4340, 0]], ![![-2254498358205, 6581946309422, 1351685384283, -221006780101], ![-1120120221427, -868940074082, 55800, 0]]]
    h := ![![![2189, 8760, 2451, -59], ![-36855, -12736, 0, 0]], ![![975, 3663, 1017, -25], ![-15244, -5272, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R23N0 : Ideal.span {9} * I23N0 =  Ideal.span {B.equivFun.symm ![464, 264, 17, -4]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 9 ![![23, 0, 0, 0], ![-131, -62, -4, 1]] 
  ![-148, -71, -3, 1] ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
    su := ![![207, 0, 0, 0], ![-1179, -558, -36, 9]]
    hsu := by decide  
    w := ![![-1332, -639, -27, 9], ![-765, -558, -36, 9]]
    hw := by decide  
    g := ![![![-11187, 33239, 3631, 794], ![-240020, -88988, 46, 0]], ![![49520, -144278, -15784, -3462], ![1044791, 387352, -200, 0]]]
    h := ![![![-1168, -13501, -4173, 59], ![43920, 15092, 0, 0]], ![![-265, -3994, -1244, 17], ![13134, 4508, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R23N1 : Ideal.span {9} * I23N1 =  Ideal.span {B.equivFun.symm ![-148, -71, -3, 1]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E23RS1 
