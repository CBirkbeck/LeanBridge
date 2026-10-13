/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F12
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

set_option linter.all false

noncomputable section


noncomputable def E661RS1 : RelationCertificate Table 3 ![![661, 0, 0, 0], ![14, 1, 0, 0]] 
  ![266, 170, 16, -3] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![1983, 0, 0, 0], ![42, 3, 0, 0]]
    hsu := by decide  
    w := ![![798, 510, 48, -9], ![390, 27, -39, 3]]
    hw := by decide  
    g := ![![![-605, 1519, 439, -24], ![-3079, -1051, 0, 0]], ![![41, 64, 12, -1], ![-72, -25, 0, 0]]]
    h := ![![![19264, -4175861, -298514, -10], ![-909517, 197225272, 6607, 0]], ![![9386, -2043497, -146082, -5], ![-443144, 96513905, 3306, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R661N1 : Ideal.span {3} * I661N1 =  Ideal.span {B.equivFun.symm ![266, 170, 16, -3]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E661RS1 


noncomputable def E661RS2 : RelationCertificate Table 3 ![![661, 0, 0, 0], ![63, 1, 0, 0]] 
  ![-29, -11, -1, 0] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![1983, 0, 0, 0], ![189, 3, 0, 0]]
    hsu := by decide  
    w := ![![-87, -33, -3, 0], ![735, 345, 12, -6]]
    hw := by decide  
    g := ![![![26904, -56909, -17221, 845], ![122294, 41636, 0, 0]], ![![7715, -16307, -4934, 243], ![34952, 11896, 0, 0]]]
    h := ![![![-131, 1195, 19, 0], ![1374, -12560, 0, 0]], ![![833, -10205, -225, -1], ![-8736, 107212, 659, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R661N2 : Ideal.span {3} * I661N2 =  Ideal.span {B.equivFun.symm ![-29, -11, -1, 0]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E661RS2 


noncomputable def E673RS0 : RelationCertificate Table 9 ![![673, 0, 0, 0], ![27, 1, 0, 0]] 
  ![-310, -138, -7, 2] ![![9, 0, 0, 0], ![-2, 1, 0, 0]] where
    su := ![![6057, 0, 0, 0], ![243, 9, 0, 0]]
    hsu := by decide  
    w := ![![-2790, -1242, -63, 18], ![1386, 630, 36, -9]]
    hw := by decide  
    g := ![![![259746815218, 11039239631022, -5584587311757, 15396326], ![1168860666737, 50261008672000, -138566962, 0]], ![![10524752936, 447301999191, -226283435518, 623848], ![47361388150, 2036539690400, -5614633, 0]]]
    h := ![![![-68344, -1827, -11931301, -441901], ![1703526, -17559, 297399375, 0]], ![![33916, 877, 6043045, 223817], ![-845382, 9453, -150628842, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R673N0 : Ideal.span {9} * I673N0 =  Ideal.span {B.equivFun.symm ![-310, -138, -7, 2]} * (J0 ^ 0*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E673RS0 


noncomputable def E673RS1 : RelationCertificate Table 9 ![![673, 0, 0, 0], ![31, 1, 0, 0]] 
  ![626, 331, 21, -5] ![![9, 0, 0, 0], ![-4, 1, 0, 0]] where
    su := ![![6057, 0, 0, 0], ![279, 9, 0, 0]]
    hsu := by decide  
    w := ![![5634, 2979, 189, -45], ![-4419, -2358, -153, 36]]
    hw := by decide  
    g := ![![![-33342004956767, -808543620209313, 204219913073452, -33177814], ![-75019511153576, -1837978023259765, 298600302, 0]], ![![-1576410968161, -38227965978232, 9655523454663, -1568648], ![-3546924678398, -86899654620639, 14117831, 0]]]
    h := ![![![8545, -663938, -21488, -2], ![-185489, 14419874, 1341, 0]], ![![-6793, 520680, 16834, 1], ![147458, -11308560, -669, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R673N1 : Ideal.span {9} * I673N1 =  Ideal.span {B.equivFun.symm ![626, 331, 21, -5]} * (J0 ^ 2*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E673RS1 


noncomputable def E673RS2 : RelationCertificate Table 3 ![![673, 0, 0, 0], ![37, 1, 0, 0]] 
  ![-139, -65, -3, 1] ![![3, 0, 0, 0], ![-1, 1, 0, 0]] where
    su := ![![2019, 0, 0, 0], ![111, 3, 0, 0]]
    hsu := by decide  
    w := ![![-417, -195, -9, 3], ![522, 258, 18, -3]]
    hw := by decide  
    g := ![![![317582, 3197273, -3518623, 20], ![959897, 10555608, 0, 0]], ![![17687, 177939, -195815, 1], ![53420, 587432, 0, 0]]]
    h := ![![![-12399, -37, -3903603, -105503], ![225524, -5424, 71003520, 0]], ![![15438, -29, 5054447, 136607], ![-280800, 8119, -91936512, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R673N2 : Ideal.span {3} * I673N2 =  Ideal.span {B.equivFun.symm ![-139, -65, -3, 1]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E673RS2 


noncomputable def E673RS3 : RelationCertificate Table 3 ![![673, 0, 0, 0], ![-96, 1, 0, 0]] 
  ![107, 63, 5, -1] ![![3, 0, 0, 0], ![1, 1, 0, 0]] where
    su := ![![2019, 0, 0, 0], ![-288, 3, 0, 0]]
    hsu := by decide  
    w := ![![321, 189, 15, -3], ![-276, -162, -12, 3]]
    hw := by decide  
    g := ![![![-2395, -717, 64, 16], ![-1036, -343, 0, 0]], ![![69, 2902, 3066, -5], ![993, -9184, 8, 0]]]
    h := ![![![61739, -189488, 2063, -1], ![432815, -1323882, 672, 0]], ![![-52796, 163187, -1694, 0], ![-370121, 1140154, 1, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R673N3 : Ideal.span {3} * I673N3 =  Ideal.span {B.equivFun.symm ![107, 63, 5, -1]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E673RS3 


noncomputable def E683RS1 : RelationCertificate Table 3 ![![683, 0, 0, 0], ![9, 1, 0, 0]] 
  ![89, 60, 5, -1] ![![3, 0, 0, 0], ![1, 1, 0, 0]] where
    su := ![![2049, 0, 0, 0], ![27, 3, 0, 0]]
    hsu := by decide  
    w := ![![267, 180, 15, -3], ![-294, -183, -15, 3]]
    hw := by decide  
    g := ![![![-1055681903, 10556818242, 11611496218, -1003847], ![3167045448, -34837500184, 3011540, 0]], ![![-19390075, 193900734, 213272370, -18438], ![58170221, -639872424, 55314, 0]]]
    h := ![![![154, -6715, -757, -1], ![-11677, 510898, 682, 0]], ![![-199, 7376, 822, 0], ![15091, -561440, 1, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R683N1 : Ideal.span {3} * I683N1 =  Ideal.span {B.equivFun.symm ![89, 60, 5, -1]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E683RS1 


noncomputable def E683RS2 : RelationCertificate Table 3 ![![683, 0, 0, 0], ![-111, 1, 0, 0]] 
  ![-166, -74, -3, 1] ![![3, 0, 0, 0], ![-1, 1, 0, 0]] where
    su := ![![2049, 0, 0, 0], ![-333, 3, 0, 0]]
    hsu := by decide  
    w := ![![-498, -222, -9, 3], ![549, 240, 9, -3]]
    hw := by decide  
    g := ![![![-1497, -617, -357, 12], ![295, 933, 0, 0]], ![![250, 104, 58, -2], ![-48, -151, 0, 0]]]
    h := ![![![-5168, 1299874, -11932, 2], ![-31798, 7998038, -1365, 0]], ![![5946, -1432859, 13241, -3], ![36585, -8816272, 2048, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R683N2 : Ideal.span {3} * I683N2 =  Ideal.span {B.equivFun.symm ![-166, -74, -3, 1]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E683RS2 


noncomputable def E691RS1 : RelationCertificate Table 9 ![![691, 0, 0, 0], ![218, 1, 0, 0]] 
  ![-1057, -611, -48, 10] ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
    su := ![![6219, 0, 0, 0], ![1962, 9, 0, 0]]
    hsu := by decide  
    w := ![![-9513, -5499, -432, 90], ![-19368, -10953, -765, 171]]
    hw := by decide  
    g := ![![![-520002479699, 1519900807568, 168095121171, 36555285034], ![-10986387905323, -4078770765040, 1382, 0]], ![![-163676620879, 478405849737, 52909827327, 11506186531], ![-3458088985470, -1283838908510, 435, 0]]]
    h := ![![![-100939, 9388191, 46770, 17], ![319944, -29759452, -11737, 0]], ![![-204442, 19115288, 95531, 36], ![648015, -60593180, -24857, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R691N1 : Ideal.span {9} * I691N1 =  Ideal.span {B.equivFun.symm ![-1057, -611, -48, 10]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E691RS1 


noncomputable def E691RS2 : RelationCertificate Table 9 ![![691, 0, 0, 0], ![-42, 1, 0, 0]] 
  ![3625, 1647, 79, -23] ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
    su := ![![6219, 0, 0, 0], ![-378, 9, 0, 0]]
    hsu := by decide  
    w := ![![32625, 14823, 711, -207], ![235800, 106515, 5076, -1485]]
    hw := by decide  
    g := ![![![3775749169798046176, -11023196352012552125, -2263751631412051731, 370133919984198525], ![1875936373832310490, 1455268905588198237, -33636768, 0]], ![![-226168003513737032, 660291295623309103, 135599099384775380, -22171083393237409], ![-112368900927586254, -87170849585357402, 2014848, 0]]]
    h := ![![![85117, -20318318, 485526, -43], ![1400291, -334251407, 29690, 0]], ![![615220, -146853611, 3509051, -307], ![10121210, -2415850853, 211972, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R691N2 : Ideal.span {9} * I691N2 =  Ideal.span {B.equivFun.symm ![3625, 1647, 79, -23]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E691RS2 
