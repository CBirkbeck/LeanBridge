/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F7
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

set_option linter.all false

noncomputable section


noncomputable def E367RS1 : RelationCertificate Table 9 ![![367, 0, 0, 0], ![77, 1, 0, 0]] 
  ![-555, -314, -23, 5] ![![9, 0, 0, 0], ![-128, -67, -4, 1]] where
    su := ![![3303, 0, 0, 0], ![693, 9, 0, 0]]
    hsu := by decide  
    w := ![![-4995, -2826, -207, 45], ![-3645, -1917, -99, 27]]
    hw := by decide  
    g := ![![![29904, 7987156, 2334047, -17910], ![-60923626, -20361625, 0, 0]], ![![6514, 1725719, 504292, -3870], ![-13163058, -4399300, 0, 0]]]
    h := ![![![-29550, 2374612, 32075, 16], ![140835, -11319789, -5867, 0]], ![![-21576, 1733194, 23436, 12], ![102831, -8262146, -4401, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R367N1 : Ideal.span {9} * I367N1 =  Ideal.span {B.equivFun.symm ![-555, -314, -23, 5]} * (J0 ^ 2*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E367RS1 


noncomputable def E367RS2 : RelationCertificate Table 9 ![![367, 0, 0, 0], ![-121, 1, 0, 0]] 
  ![786, 356, 17, -5] ![![9, 0, 0, 0], ![-128, -67, -4, 1]] where
    su := ![![3303, 0, 0, 0], ![-1089, 9, 0, 0]]
    hsu := by decide  
    w := ![![7074, 3204, 153, -45], ![-2943, -1314, -63, 18]]
    hw := by decide  
    g := ![![![104, 628, 166, -3], ![-4141, -1348, 0, 0]], ![![93, -138, -50, 0], ![1353, 437, 0, 0]]]
    h := ![![![63177, -6487525, 58934, -44], ![191613, -19675458, 16143, 0]], ![![-26127, 2699198, -24483, 18], ![-79242, 8186170, -6604, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R367N2 : Ideal.span {9} * I367N2 =  Ideal.span {B.equivFun.symm ![786, 356, 17, -5]} * (J0 ^ 2*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E367RS2 


noncomputable def E373RS1 : RelationCertificate Table 9 ![![373, 0, 0, 0], ![147, 1, 0, 0]] 
  ![1207, 662, 42, -10] ![![9, 0, 0, 0], ![-4, 1, 0, 0]] where
    su := ![![3357, 0, 0, 0], ![1323, 9, 0, 0]]
    hsu := by decide  
    w := ![![10863, 5958, 378, -90], ![-8658, -4761, -306, 72]]
    hw := by decide  
    g := ![![![-1536550876268809, -37261358749483123, 9411374498540514, -95350808], ![-3457239471600871, -84702367054235476, 858157370, 0]], ![![-603498003933289, -14634826595368550, 3696425423888352, -37450125], ![-1357870508848369, -33267827466790644, 337051163, 0]]]
    h := ![![![2189731, -307744457, -2374367, -1910], ![-5556248, 780913193, 712420, 0]], ![![-1745546, 245276476, 1892212, 1521], ![4429168, -622398335, -567325, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R373N1 : Ideal.span {9} * I373N1 =  Ideal.span {B.equivFun.symm ![1207, 662, 42, -10]} * (J0 ^ 2*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E373RS1 


noncomputable def E373RS2 : RelationCertificate Table 9 ![![373, 0, 0, 0], ![161, 1, 0, 0]] 
  ![575, 276, 14, -4] ![![9, 0, 0, 0], ![-2, 1, 0, 0]] where
    su := ![![3357, 0, 0, 0], ![1449, 9, 0, 0]]
    hsu := by decide  
    w := ![![5175, 2484, 126, -36], ![-2682, -1305, -72, 18]]
    hw := by decide  
    g := ![![![-3151647, -133939057, 67757482, -76], ![-14181747, -609816080, 708, 0]], ![![-1406663, -59780732, 30242054, -34], ![-6329709, -272177920, 316, 0]]]
    h := ![![![434585, -142484, 149587742, 929122], ![-1006830, 336358, -346562510, 0]], ![![-225570, 74411, -78161488, -485478], ![522592, -175640, 181083296, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R373N2 : Ideal.span {9} * I373N2 =  Ideal.span {B.equivFun.symm ![575, 276, 14, -4]} * (J0 ^ 0*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E373RS2 


noncomputable def E401RS0 : RelationCertificate Table 9 ![![401, 0, 0, 0], ![39, 1, 0, 0]] 
  ![-1630, -725, -33, 10] ![![9, 0, 0, 0], ![-4, 1, 0, 0]] where
    su := ![![3609, 0, 0, 0], ![351, 9, 0, 0]]
    hsu := by decide  
    w := ![![-14670, -6525, -297, 90], ![10350, 4590, 207, -63]]
    hw := by decide  
    g := ![![![3153833680654, 76480466740466, -19317247456309, 4041576], ![7096125779766, 173855081610056, -36374240, 0]], ![![306935599282, 7443188281150, -1879982118557, 393332], ![690605098232, 16919824907062, -3539993, 0]]]
    h := ![![![-11054, -127, -696303, -17854], ![113616, -1626, 7159464, 0]], ![![7706, 53, 490500, 12577], ![-79204, 1499, -5043384, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R401N0 : Ideal.span {9} * I401N0 =  Ideal.span {B.equivFun.symm ![-1630, -725, -33, 10]} * (J0 ^ 2*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E401RS0 


noncomputable def E401RS1 : RelationCertificate Table 3 ![![401, 0, 0, 0], ![172, 1, 0, 0]] 
  ![274, 135, 7, -2] ![![3, 0, 0, 0], ![1, 1, 0, 0]] where
    su := ![![1203, 0, 0, 0], ![516, 3, 0, 0]]
    hsu := by decide  
    w := ![![822, 405, 21, -6], ![-492, -255, -18, 3]]
    hw := by decide  
    g := ![![![-535235, 5338935, 5873343, -228], ![1601235, -17621128, 744, 0]], ![![-231626, 2310680, 2541958, -99], ![693018, -7626344, 322, 0]]]
    h := ![![![1242, -5991, -206, -1], ![-2894, 13985, 399, 0]], ![![-1056, 3338, 19, 0], ![2461, -7797, 1, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R401N1 : Ideal.span {3} * I401N1 =  Ideal.span {B.equivFun.symm ![274, 135, 7, -2]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E401RS1 


noncomputable def E401RS2 : RelationCertificate Table 3 ![![401, 0, 0, 0], ![-137, 1, 0, 0]] 
  ![289, 203, 24, -4] ![![3, 0, 0, 0], ![-1, 1, 0, 0]] where
    su := ![![1203, 0, 0, 0], ![-411, 3, 0, 0]]
    hsu := by decide  
    w := ![![867, 609, 72, -12], ![-1821, -1242, -141, 24]]
    hw := by decide  
    g := ![![![-10516113, -105151375, 115666151, -290], ![-31545087, -346997640, 893, 0]], ![![3591737, 35913962, -39505231, 99], ![10774078, 118515416, -305, 0]]]
    h := ![![![243242, -12738707, 102833, -72], ![711969, -37281093, 28868, 0]], ![![-265322, -17982, -26449483, 193063], ![-776595, -58299, -77418255, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R401N2 : Ideal.span {3} * I401N2 =  Ideal.span {B.equivFun.symm ![289, 203, 24, -4]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E401RS2 


noncomputable def E401RS3 : RelationCertificate Table 9 ![![401, 0, 0, 0], ![-75, 1, 0, 0]] 
  ![305, 213, 23, -4] ![![9, 0, 0, 0], ![-2, 1, 0, 0]] where
    su := ![![3609, 0, 0, 0], ![-675, 9, 0, 0]]
    hsu := by decide  
    w := ![![2745, 1917, 207, -36], ![-2142, -1449, -153, 27]]
    hw := by decide  
    g := ![![![-638558147418888480540542, -27138721265302760422974529, 13729000169506891034868339, -394351622955], ![-2873511663384998162432600, -123561001525554920984601840, 3549164606590, 0]], ![![116246262594296537823389, 4940466160257602857494286, -2499294645777519142617030, 71789707017], ![523108181674334420205283, 22493651811996380068826960, -646107363152, 0]]]
    h := ![![![432955, -27306349, 376382, -165], ![2314862, -145967084, 66161, 0]], ![![-337613, 21311740, -293696, 128], ![-1805101, 113922704, -51325, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R401N3 : Ideal.span {9} * I401N3 =  Ideal.span {B.equivFun.symm ![305, 213, 23, -4]} * (J0 ^ 0*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E401RS3 


noncomputable def E409RS1 : RelationCertificate Table 3 ![![409, 0, 0, 0], ![-65, 1, 0, 0]] 
  ![-292, -144, -7, 2] ![![3, 0, 0, 0], ![1, 1, 0, 0]] where
    su := ![![1227, 0, 0, 0], ![-195, 3, 0, 0]]
    hsu := by decide  
    w := ![![-876, -432, -21, 6], ![474, 228, 9, -3]]
    hw := by decide  
    g := ![![![763858084, -7638583795, -8401452139, 989922], ![-2291575236, 25207326152, -2969760, 0]], ![![-120210626, 1202106743, 1322161612, -155787], ![360632040, -3966952192, 467360, 0]]]
    h := ![![![-108408, 7510292, -118312, 43], ![-682132, 47246576, -17585, 0]], ![![58782, -4064064, 64070, -24], ![369872, -25566652, 9815, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R409N1 : Ideal.span {3} * I409N1 =  Ideal.span {B.equivFun.symm ![-292, -144, -7, 2]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E409RS1 


noncomputable def E409RS2 : RelationCertificate Table 3 ![![409, 0, 0, 0], ![-3, 1, 0, 0]] 
  ![-187, -74, -3, 1] ![![3, 0, 0, 0], ![-1, 1, 0, 0]] where
    su := ![![1227, 0, 0, 0], ![-9, 3, 0, 0]]
    hsu := by decide  
    w := ![![-561, -222, -9, 3], ![570, 219, 9, -3]]
    hw := by decide  
    g := ![![![8270010, 82699663, -91601334, 631733], ![24809885, 272908800, -1895200, 0]], ![![-48175, -481746, 533600, -3680], ![-144523, -1589760, 11040, 0]]]
    h := ![![![-3004, 203909, -67639, 1], ![-409483, 27663124, -408, 0]], ![![3061, -207195, 68731, -2], ![417253, -28108525, 817, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R409N2 : Ideal.span {3} * I409N2 =  Ideal.span {B.equivFun.symm ![-187, -74, -3, 1]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E409RS2 
