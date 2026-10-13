/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F3
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

set_option linter.all false

noncomputable section


noncomputable def E149RS0 : RelationCertificate Table 3 ![![149, 0, 0, 0], ![27, 1, 0, 0]] 
  ![-2, -5, -1, 0] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![447, 0, 0, 0], ![81, 3, 0, 0]]
    hsu := by decide  
    w := ![![-6, -15, -3, 0], ![-504, -258, -18, 3]]
    hw := by decide  
    g := ![![![-47, 153, 46, -1], ![-454, -159, 0, 0]], ![![88, 80, 12, -1], ![-81, -29, 0, 0]]]
    h := ![![![-247, 21510, 797, 0], ![1363, -118754, 0, 0]], ![![-9030, 1183, -1308769, -48475], ![49826, -8377, 7222776, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R149N0 : Ideal.span {3} * I149N0 =  Ideal.span {B.equivFun.symm ![-2, -5, -1, 0]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E149RS0 


noncomputable def E149RS1 : RelationCertificate Table 3 ![![149, 0, 0, 0], ![34, 1, 0, 0]] 
  ![-59, -17, 2, 0] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![447, 0, 0, 0], ![102, 3, 0, 0]]
    hsu := by decide  
    w := ![![-177, -51, 6, 0], ![-1080, -690, -63, 12]]
    hw := by decide  
    g := ![![![15, 243, 59, -4], ![-388, -135, 0, 0]], ![![9, 60, 14, -1], ![-92, -32, 0, 0]]]
    h := ![![![-661, 14, -34883, -1026], ![2895, -147, 152874, 0]], ![![-8274, 264481, 8159, 11], ![36249, -1160122, -1635, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R149N1 : Ideal.span {3} * I149N1 =  Ideal.span {B.equivFun.symm ![-59, -17, 2, 0]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E149RS1 


noncomputable def E149RS2 : RelationCertificate Table 3 ![![149, 0, 0, 0], ![42, 1, 0, 0]] 
  ![-479, -264, -17, 4] ![![3, 0, 0, 0], ![1, 1, 0, 0]] where
    su := ![![447, 0, 0, 0], ![126, 3, 0, 0]]
    hsu := by decide  
    w := ![![-1437, -792, -51, 12], ![1053, 585, 39, -9]]
    hw := by decide  
    g := ![![![715, 123, -127, -5], ![280, 430, 0, 0]], ![![590, -3969, -4435, -1], ![-1125, 13319, -1, 0]]]
    h := ![![![-78601, 6061677, 154911, 251], ![278835, -21511166, -37395, 0]], ![![57411, -4441893, -113561, -185], ![-203664, 15762998, 27562, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R149N2 : Ideal.span {3} * I149N2 =  Ideal.span {B.equivFun.symm ![-479, -264, -17, 4]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E149RS2 


noncomputable def E149RS3 : RelationCertificate Table 3 ![![149, 0, 0, 0], ![45, 1, 0, 0]] 
  ![-163, -71, -3, 1] ![![3, 0, 0, 0], ![-1, 1, 0, 0]] where
    su := ![![447, 0, 0, 0], ![135, 3, 0, 0]]
    hsu := by decide  
    w := ![![-489, -213, -9, 3], ![546, 240, 12, -3]]
    hw := by decide  
    g := ![![![17053, 164607, -180706, 102], ![49188, 541877, -324, 0]], ![![5143, 49779, -54659, 31], ![14880, 163902, -98, 0]]]
    h := ![![![-2162, 146, -117581, -2613], ![7155, -644, 389338, 0]], ![![2308, -188, 131890, 2931], ![-7638, 794, -436720, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R149N3 : Ideal.span {3} * I149N3 =  Ideal.span {B.equivFun.symm ![-163, -71, -3, 1]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E149RS3 


noncomputable def E151RS1 : RelationCertificate Table 3 ![![151, 0, 0, 0], ![-27, 1, 0, 0]] 
  ![-233, -127, -9, 2] ![![3, 0, 0, 0], ![-1, 1, 0, 0]] where
    su := ![![453, 0, 0, 0], ![-81, 3, 0, 0]]
    hsu := by decide  
    w := ![![-699, -381, -27, 6], ![999, 558, 42, -9]]
    hw := by decide  
    g := ![![![352797, 3530184, -3884161, 807], ![1059131, 11650046, -2416, 0]], ![![-64247, -642913, 707380, -147], ![-192886, -2121696, 440, 0]]]
    h := ![![![-2804, 142482, -5435, 6], ![-15673, 796268, -904, 0]], ![![4086, -203553, 7776, -9], ![22839, -1137550, 1356, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R151N1 : Ideal.span {3} * I151N1 =  Ideal.span {B.equivFun.symm ![-233, -127, -9, 2]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E151RS1 


noncomputable def E151RS2 : RelationCertificate Table 3 ![![151, 0, 0, 0], ![-2, 1, 0, 0]] 
  ![614, 285, 14, -4] ![![3, 0, 0, 0], ![1, 1, 0, 0]] where
    su := ![![453, 0, 0, 0], ![-6, 3, 0, 0]]
    hsu := by decide  
    w := ![![1842, 855, 42, -12], ![-918, -429, -21, 6]]
    hw := by decide  
    g := ![![![-385165, 3852199, 4237255, -145], ![1155681, -12712200, 434, 0]], ![![2661, -26626, -29287, 1], ![-7988, 87864, -3, 0]]]
    h := ![![![6218, -232153, 114546, -11], ![469152, -17293118, 1657, 0]], ![![-3096, 115696, -57085, 5], ![-233595, 8618322, -753, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R151N2 : Ideal.span {3} * I151N2 =  Ideal.span {B.equivFun.symm ![614, 285, 14, -4]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E151RS2 


noncomputable def E167RS1 : RelationCertificate Table 9 ![![167, 0, 0, 0], ![-34, 1, 0, 0]] 
  ![-535, -272, -15, 4] ![![9, 0, 0, 0], ![-4, 1, 0, 0]] where
    su := ![![1503, 0, 0, 0], ![-306, 9, 0, 0]]
    hsu := by decide  
    w := ![![-4815, -2448, -135, 36], ![3672, 1881, 108, -27]]
    hw := by decide  
    g := ![![![24903593, 603909656, -152534210, 89], ![56032819, 1372804725, -818, 0]], ![![-5053779, -122553600, 30954325, -18], ![-11370939, -278588286, 166, 0]]]
    h := ![![![-345239, 8409639, -256903, 290], ![-1695717, 41256302, -48426, 0]], ![![263364, -6412785, 195931, -222], ![1293570, -31460051, 37071, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R167N1 : Ideal.span {9} * I167N1 =  Ideal.span {B.equivFun.symm ![-535, -272, -15, 4]} * (J0 ^ 2*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E167RS1 


noncomputable def E167RS2 : RelationCertificate Table 9 ![![167, 0, 0, 0], ![-6, 1, 0, 0]] 
  ![-236, -114, 1, 1] ![![9, 0, 0, 0], ![-2, 1, 0, 0]] where
    su := ![![1503, 0, 0, 0], ![-54, 9, 0, 0]]
    hsu := by decide  
    w := ![![-2124, -1026, 9, 9], ![855, 324, -36, 0]]
    hw := by decide  
    g := ![![![-965434542, -41030968903, 20757347419, -252164], ![-4344455534, -186811587847, 2269472, 0]], ![![34683328, 1474041492, -745709697, 9059], ![156074984, 6711224210, -81531, 0]]]
    h := ![![![-244, 34, -28049, 4675], ![-6752, -160, -780724, 0]], ![![109, -12, 9911, -1652], ![3018, 163, 275884, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R167N2 : Ideal.span {9} * I167N2 =  Ideal.span {B.equivFun.symm ![-236, -114, 1, 1]} * (J0 ^ 0*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E167RS2 


noncomputable def E173RS0 : RelationCertificate Table 9 ![![173, 0, 0, 0], ![56, 1, 0, 0]] 
  ![-1280, -574, -27, 8] ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
    su := ![![1557, 0, 0, 0], ![504, 9, 0, 0]]
    hsu := by decide  
    w := ![![-11520, -5166, -243, 72], ![37170, 16803, 801, -234]]
    hw := by decide  
    g := ![![![1267761196647, -3705503997072, -409814333103, -89121443768], ![26784711314152, 9944005093831, -8996, 0]], ![![406709522954, -1188759970629, -131472230220, -28590983834], ![8592783238251, 3190128849595, -2886, 0]]]
    h := ![![![-25904, 475408, 9279, 14], ![80002, -1470110, -2414, 0]], ![![83090, -1534134, -30045, -47], ![-256615, 4743994, 8105, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R173N0 : Ideal.span {9} * I173N0 =  Ideal.span {B.equivFun.symm ![-1280, -574, -27, 8]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E173RS0 


noncomputable def E173RS1 : RelationCertificate Table 9 ![![173, 0, 0, 0], ![65, 1, 0, 0]] 
  ![-502, -297, -25, 5] ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
    su := ![![1557, 0, 0, 0], ![585, 9, 0, 0]]
    hsu := by decide  
    w := ![![-4518, -2673, -225, 45], ![8163, 6093, 792, -126]]
    hw := by decide  
    g := ![![![5244949467051403, -15312486405071836, -3144611142911151, 514158546868324], ![2605891187085711, 2021535734727011, -166, 0]], ![![2022147141019816, -5903603228293801, -1212378969941148, 198229600134782], ![1004679920536352, 779386480675841, -64, 0]]]
    h := ![![![-2979, 11654, 178, 0], ![7921, -31144, 5, 0]], ![![5274, -20960, -383, -1], ![-14023, 56012, 159, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R173N1 : Ideal.span {9} * I173N1 =  Ideal.span {B.equivFun.symm ![-502, -297, -25, 5]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E173RS1 


noncomputable def E173RS2 : RelationCertificate Table 9 ![![173, 0, 0, 0], ![78, 1, 0, 0]] 
  ![746, 352, 18, -5] ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
    su := ![![1557, 0, 0, 0], ![702, 9, 0, 0]]
    hsu := by decide  
    w := ![![6714, 3168, 162, -45], ![-11376, -4698, -189, 63]]
    hw := by decide  
    g := ![![![-220719890367, 645136890603, 71348034628, 15516151474], ![-4663292616056, -1731274103406, 1802620, 0]], ![![-101210934144, 295827019806, 32716585828, 7114919199], ![-2138349204787, -793874394573, 826590, 0]]]
    h := ![![![612922, -62041324, -928880, -1710], ![-1359420, 137621908, 295825, 0]], ![![-1038548, 105144744, 1574143, 2897], ![2303430, -233235188, -501174, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R173N2 : Ideal.span {9} * I173N2 =  Ideal.span {B.equivFun.symm ![746, 352, 18, -5]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E173RS2 


noncomputable def E173RS3 : RelationCertificate Table 9 ![![173, 0, 0, 0], ![-27, 1, 0, 0]] 
  ![-199, -117, -10, 2] ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
    su := ![![1557, 0, 0, 0], ![-243, 9, 0, 0]]
    hsu := by decide  
    w := ![![-1791, -1053, -90, 18], ![3078, 2511, 342, -54]]
    hw := by decide  
    g := ![![![8868571, -25891844, -5317208, 869388], ![4406261, 3418196, 0, 0]], ![![21430696515, -62566332718, -12848781228, 2100835458], ![10647588246, 8259930544, -26, 0]]]
    h := ![![![-98600, 1488793, -56301, 48], ![-631763, 9515909, -8302, 0]], ![![169542, -2538978, 96044, -83], ![1086312, -16228043, 14353, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R173N3 : Ideal.span {9} * I173N3 =  Ideal.span {B.equivFun.symm ![-199, -117, -10, 2]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E173RS3 
