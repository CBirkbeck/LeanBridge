/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F2
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.ClassGroupData5_1_3790297_2

set_option linter.all false

noncomputable section


noncomputable def E67RS2 : RelationCertificate Table 2 ![![67, 0, 0, 0, 0], ![-27, 1, 0, 0, 0]] 
  ![-1, -2, 2, 1, -4] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
    su := ![![134, 0, 0, 0, 0], ![-54, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![-2, -4, 4, 2, -8], ![0, 2, -4, 0, 4]]
    hw := by decide  
    g := ![![![-14193, -22641, 28381, 14193, 42414], ![-11320, -85040, -28369, 0, -28302]], ![![5624, 8970, -11246, -5624, -16805], ![4487, 33696, 11241, 0, 11214]]]
    h := ![![![17165, -345958, 14683, 244, -172], ![42488, -857048, 4533, 720, 0]], ![![-46707, 946027, -40119, -668, 470], ![-115611, 2343631, -12316, -1968, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R67N2 : Ideal.span {2} * I67N2 =  Ideal.span {B.equivFun.symm ![-1, -2, 2, 1, -4]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E67RS2 


noncomputable def E71RS1 : RelationCertificate Table 4 ![![71, 0, 0, 0, 0], ![-22, 1, 0, 0, 0]] 
  ![1, 0, 0, -1, 4] ![![4, 0, 0, 0, 0], ![2, 1, -1, 0, 2]] where
    su := ![![284, 0, 0, 0, 0], ![-88, 4, 0, 0, 0]]
    hsu := by decide  
    w := ![![4, 0, 0, -4, 16], ![0, -16, 0, 0, 4]]
    hw := by decide  
    g := ![![![12521096, 11205360, 3607371, 4929789, -26938145], ![-5309027, 19726640, 6958, 0, -497]], ![![-3690891, -3303045, -1063357, -1453172, 7940655], ![1564963, -5814895, -2051, 0, 147]]]
    h := ![![![327425, -3861241, 190385, -555, -100], ![1056609, -12413351, 50060, 444, 0]], ![![-389070, 4588693, -226244, 659, 119], ![-1255539, 14752014, -59461, -528, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R71N1 : Ideal.span {4} * I71N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0, -1, 4]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E71RS1 


noncomputable def E79RS1 : RelationCertificate Table 2 ![![79, 0, 0, 0, 0], ![-12, 1, 0, 0, 0]] 
  ![19, -3, -7, -4, 20] ![![2, 0, 0, 0, 0], ![-2, 0, 1, 1, -4]] where
    su := ![![158, 0, 0, 0, 0], ![-24, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![38, -6, -14, -8, 40], ![-54, 6, 20, 10, -52]]
    hw := by decide  
    g := ![![![-20036, 13706, -17404, -3689, 14768], ![-20035, -27405, 0, 0, 0]], ![![2765, -1891, 2400, 508, -2034], ![2765, 3780, 0, 0, 0]]]
    h := ![![![-48811, 967265, -82171, -41, 220], ![-320979, 6341532, -11955, -1085, 0]], ![![65275, -1292275, 109791, 54, -294], ![429246, -8472311, 16039, 1450, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R79N1 : Ideal.span {2} * I79N1 =  Ideal.span {B.equivFun.symm ![19, -3, -7, -4, 20]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E79RS1 


noncomputable def E83RS1 : RelationCertificate Table 4 ![![83, 0, 0, 0, 0], ![-37, 1, 0, 0, 0]] 
  ![13, -2, -4, -3, 14] ![![4, 0, 0, 0, 0], ![2, 1, -1, 0, 2]] where
    su := ![![332, 0, 0, 0, 0], ![-148, 4, 0, 0, 0]]
    hsu := by decide  
    w := ![![52, -8, -16, -12, 56], ![28, -12, -8, -4, 24]]
    hw := by decide  
    g := ![![![-1037163, -464836, -233449, -537176, 2293330], ![570240, -1718990, 322301, 0, -107406]], ![![460960, 206593, 103756, 238745, -1019260], ![-253437, 763996, -143245, 0, 47736]]]
    h := ![![![-954685, 23073178, -728608, -6567, 3850], ![-2139432, 51703627, -233811, -19971, 0]], ![![-409093, 9888122, -312229, -2815, 1650], ![-916770, 22157842, -100157, -8559, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R83N1 : Ideal.span {4} * I83N1 =  Ideal.span {B.equivFun.symm ![13, -2, -4, -3, 14]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 4 ![![89, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] 
  ![-1, 4, -2, 1, -2] ![![4, 0, 0, 0, 0], ![2, 1, -1, 0, 2]] where
    su := ![![356, 0, 0, 0, 0], ![12, 4, 0, 0, 0]]
    hsu := by decide  
    w := ![![-4, 16, -8, 4, -8], ![-8, 12, -8, -8, 28]]
    hw := by decide  
    g := ![![![12321350, 11013959, 3546900, 4853999, -26509685], ![-5227397, 19415710, -301, 0, -43]], ![![585183, 523091, 168455, 230533, -1259037], ![-248265, 922119, -14, 0, -2]]]
    h := ![![![593374, -8447833, -2881164, -1923, -13330], ![-17504565, 256577482, 97000, 74148, 0]], ![![302031, -4299976, -1466523, -979, -6785], ![-8909931, 130598836, 49387, 37742, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R89N1 : Ideal.span {4} * I89N1 =  Ideal.span {B.equivFun.symm ![-1, 4, -2, 1, -2]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E89RS1 


noncomputable def E89RS2 : RelationCertificate Table 4 ![![89, 0, 0, 0, 0], ![20, 1, 0, 0, 0]] 
  ![-29, 4, 10, 5, -26] ![![4, 0, 0, 0, 0], ![2, 1, -1, 0, 2]] where
    su := ![![356, 0, 0, 0, 0], ![80, 4, 0, 0, 0]]
    hsu := by decide  
    w := ![![-116, 16, 40, 20, -104], ![-64, 0, 24, 12, -60]]
    hw := by decide  
    g := ![![![7202, 6405, 2047, 2836, -15498], ![-3056, 11384, 0, 0, -31]], ![![-34324, -30689, -9886, -13522, 73846], ![14563, -54078, 1, 0, -7]]]
    h := ![![![-12033809, 348537789, 18289356, 46875, 4598], ![53545333, -1553676822, -3711466, -25578, 0]], ![![-6514220, 188672989, 9900532, 25375, 2489], ![28985509, -841047538, -2009144, -13846, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R89N2 : Ideal.span {4} * I89N2 =  Ideal.span {B.equivFun.symm ![-29, 4, 10, 5, -26]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E89RS2 


noncomputable def E89RS3 : RelationCertificate Table 2 ![![89, 0, 0, 0, 0], ![21, 1, 0, 0, 0]] 
  ![1, -1, -1, 0, 2] ![![2, 0, 0, 0, 0], ![-2, 0, 1, 1, -4]] where
    su := ![![178, 0, 0, 0, 0], ![42, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![2, -2, -2, 0, 4], ![-2, 4, 2, 2, -8]]
    hw := by decide  
    g := ![![![-167, 116, -170, -33, 140], ![-214, -267, 0, 0, 0]], ![![-40, 29, -43, -9, 38], ![-51, -66, 0, 0, 0]]]
    h := ![![![-29965, 255435, 12790, 241, 178], ![126806, -1088832, -2639, -990, 0]], ![![59800, -511060, -25610, -483, -356], ![-253061, 2178443, 5368, 1980, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R89N3 : Ideal.span {2} * I89N3 =  Ideal.span {B.equivFun.symm ![1, -1, -1, 0, 2]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E89RS3 


noncomputable def E97RS2 : RelationCertificate Table 2 ![![97, 0, 0, 0, 0], ![-39, 1, 0, 0, 0]] 
  ![-2, -1, 0, -1, 3] ![![2, 0, 0, 0, 0], ![-2, 0, 1, 1, -4]] where
    su := ![![194, 0, 0, 0, 0], ![-78, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![-4, -2, 0, -2, 6], ![0, -6, 2, -4, 10]]
    hw := by decide  
    g := ![![![-7113, 4838, -6140, -1306, 5219], ![-7041, -9675, 0, 0, 0]], ![![2563, -1742, 2210, 470, -1878], ![2534, 3483, 0, 0, 0]]]
    h := ![![![-199876, 6017384, -176358, -2978, 1379], ![-496270, 14954661, -53895, -8360, 0]], ![![-116687, 3512299, -102954, -1738, 805], ![-289721, 8728915, -31496, -4880, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R97N2 : Ideal.span {2} * I97N2 =  Ideal.span {B.equivFun.symm ![-2, -1, 0, -1, 3]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E97RS2 


noncomputable def E101RS1 : RelationCertificate Table 2 ![![101, 0, 0, 0, 0], ![-23, 1, 0, 0, 0]] 
  ![-1, -1, 1, 0, 0] ![![2, 0, 0, 0, 0], ![-2, 0, 1, 1, -4]] where
    su := ![![202, 0, 0, 0, 0], ![-46, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![-2, -2, 2, 0, 0], ![2, -4, 4, 0, -4]]
    hw := by decide  
    g := ![![![-39518, 27016, -34265, -7275, 29082], ![-39409, -54002, 0, 0, 0]], ![![8554, -5847, 7415, 1574, -6292], ![8529, 11687, 0, 0, 0]]]
    h := ![![![5, 391, -17, 0, 0], ![22, 1718, 0, 0, 0]], ![![200647, -6204042, 282985, 409, -634], ![880406, -27206428, 58741, 4002, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R101N1 : Ideal.span {2} * I101N1 =  Ideal.span {B.equivFun.symm ![-1, -1, 1, 0, 0]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 2 ![![101, 0, 0, 0, 0], ![-9, 1, 0, 0, 0]] 
  ![-3, 2, -2, -1, 4] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
    su := ![![202, 0, 0, 0, 0], ![-18, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![-6, 4, -4, -2, 8], ![0, -6, 4, 0, -4]]
    hw := by decide  
    g := ![![![-39528, -63188, -237257, 118639, 118463], ![-31594, 395546, -237267, 0, -78988]], ![![3227, 5158, 19370, -9686, -9670], ![2579, -32294, 19371, 0, 6448]]]
    h := ![![![-974382, 24834067, -2770904, -667, 4484], ![-10922151, 277495571, -243989, -28305, 0]], ![![-1120829, 28566485, -3187358, -767, 5158], ![-12563721, 319201563, -280693, -32560, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R101N2 : Ideal.span {2} * I101N2 =  Ideal.span {B.equivFun.symm ![-3, 2, -2, -1, 4]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E101RS2 


noncomputable def E103RS1 : RelationCertificate Table 2 ![![103, 0, 0, 0, 0], ![-28, 1, 0, 0, 0]] 
  ![3, 0, -2, -1, 6] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
    su := ![![206, 0, 0, 0, 0], ![-56, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![6, 0, -4, -2, 12], ![-2, -4, 0, 0, 2]]
    hw := by decide  
    g := ![![![32691, 52274, -163385, -9, -97986], ![26138, 392094, 0, 0, 65349]], ![![-8841, -14138, 44195, 3, 26499], ![-7067, -106056, -1, 0, -17673]]]
    h := ![![![696309, -3142280, 119505, 173, -246], ![2561196, -11467913, 29700, 1584, 0]], ![![-698671, 3153016, -119879, -175, 247], ![-2569884, 11507097, -29675, -1590, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R103N1 : Ideal.span {2} * I103N1 =  Ideal.span {B.equivFun.symm ![3, 0, -2, -1, 6]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 2 ![![103, 0, 0, 0, 0], ![-23, 1, 0, 0, 0]] 
  ![-2, 1, 2, 1, -5] ![![2, 0, 0, 0, 0], ![-2, 0, 1, 1, -4]] where
    su := ![![206, 0, 0, 0, 0], ![-46, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![-4, 2, 4, 2, -10], ![8, -2, -2, 0, 2]]
    hw := by decide  
    g := ![![![54363, -37192, 47216, 10014, -40065], ![54385, 74391, 0, 0, 0]], ![![-11713, 8014, -10174, -2158, 8634], ![-11718, -16029, 0, 0, 0]]]
    h := ![![![404, -13692, 633, 3, -3], ![1806, -61242, 167, 19, 0]], ![![5539, -196621, 8970, 46, -41], ![24759, -879501, 1862, 264, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R103N2 : Ideal.span {2} * I103N2 =  Ideal.span {B.equivFun.symm ![-2, 1, 2, 1, -5]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E103RS2 
