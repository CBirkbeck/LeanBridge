/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F0
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.ClassGroupData5_1_3790297_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
  ![1, 0, 0, 0, 0] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
    su := ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
    hsu := by decide  
    w := ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
    hw := by decide  
    g := ![![![0, -2, 0, 0, 3], ![0, -2, 0, 0, -2]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]]
    h := ![![![0, -2, 0, 0, 3], ![0, -2, 0, 0, -2]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0, 0]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0, 0, 0], ![2, 0, -1, 0, 1]] 
  ![4, -1, -2, -1, 5] ![![2, 0, 0, 0, 0], ![-2, 0, 1, 1, -4]] where
    su := ![![4, 0, 0, 0, 0], ![4, 0, -2, 0, 2]]
    hsu := by decide  
    w := ![![8, -2, -4, -2, 10], ![-12, 2, 4, 2, -10]]
    hw := by decide  
    g := ![![![1, 1, 0, -1, 2], ![1, 0, 0, 0, -2]], ![![1, -1, 0, -1, 3], ![1, 0, 0, 0, 0]]]
    h := ![![![7, 0, -2, 0, 2], ![-4, 1, 0, 0, -1]], ![![2, 0, 3, 4, -11], ![-2, 7, 0, 0, 1]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![4, -1, -2, -1, 5]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E2RS1 


noncomputable def E2RS2 : RelationCertificate Table 4 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
  ![-17, 2, 6, 3, -16] ![![4, 0, 0, 0, 0], ![2, 1, -1, 0, 2]] where
    su := ![![8, 0, 0, 0, 0], ![4, 4, 0, 0, 0]]
    hsu := by decide  
    w := ![![-68, 8, 24, 12, -64], ![-36, 4, 16, 8, -40]]
    hw := by decide  
    g := ![![![-2832, -1259, -491, -1381, 6191], ![1490, -4864, 675, 0, 15]], ![![-5722, -2543, -992, -2791, 12511], ![3010, -9829, 1365, 0, 30]]]
    h := ![![![-12, -3, -8, -9, -8], ![7, 1, 21, 0, 0]], ![![-9, -1, 5, 1, -5], ![9, -6, 0, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R2N2 : Ideal.span {4} * I2N2 =  Ideal.span {B.equivFun.symm ![-17, 2, 6, 3, -16]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E2RS2 


noncomputable def E5RS0 : RelationCertificate Table 2 ![![5, 0, 0, 0, 0], ![1, 2, -1, 0, 1]] 
  ![7, 0, -2, -1, 6] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
    su := ![![10, 0, 0, 0, 0], ![2, 4, -2, 0, 2]]
    hsu := by decide  
    w := ![![14, 0, -4, -2, 12], ![-2, 0, 0, 0, 2]]
    hw := by decide  
    g := ![![![0, 0, 0, 0, 1], ![-4, 0, 0, 0, -1]], ![![-3, -11, 25, 2, 9], ![9, -57, -3, 0, -7]]]
    h := ![![![118, 236, -261, 45, -255], ![123, 946, 240, 0, 0]], ![![-16, -32, 35, -6, 34], ![-15, -126, -32, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R5N0 : Ideal.span {2} * I5N0 =  Ideal.span {B.equivFun.symm ![7, 0, -2, -1, 6]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 4 ![![7, 0, 0, 0, 0], ![3, 2, -1, 0, 1]] 
  ![1, 0, -2, -1, 6] ![![4, 0, 0, 0, 0], ![2, 1, -1, 0, 2]] where
    su := ![![28, 0, 0, 0, 0], ![12, 8, -4, 0, 4]]
    hsu := by decide  
    w := ![![4, 0, -8, -4, 24], ![0, -12, -4, -4, 12]]
    hw := by decide  
    g := ![![![-2492183, -2038224, -670205, -1022004, 5377439], ![1100628, -3985933, 102135, 0, 55]], ![![2520374, 2061279, 677788, 1033564, -5438270], ![-1113069, 4031022, -103290, 0, -55]]]
    h := ![![![229, -210, -362, 181, -596], ![10, 1814, 182, 0, 0]], ![![-564, 509, 883, -443, 1457], ![-12, -4426, -442, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R7N0 : Ideal.span {4} * I7N0 =  Ideal.span {B.equivFun.symm ![1, 0, -2, -1, 6]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 4 ![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
  ![-5, 0, 2, 1, -6] ![![4, 0, 0, 0, 0], ![2, 1, -1, 0, 2]] where
    su := ![![28, 0, 0, 0, 0], ![-4, 4, 0, 0, 0]]
    hsu := by decide  
    w := ![![-20, 0, 8, 4, -24], ![-8, 8, 8, 4, -20]]
    hw := by decide  
    g := ![![![-7602270, -6791471, -2187335, -2995740, 16356724], ![3226196, -11980818, 2310, 0, 165]], ![![-20322, -18153, -5846, -8008, 43720], ![8627, -32024, 7, 0, 0]]]
    h := ![![![-72, 121, -132, -15, 86], ![-347, 690, -8, -38, 0]], ![![42, -64, 71, 8, -51], ![208, -352, 11, 22, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R7N1 : Ideal.span {4} * I7N1 =  Ideal.span {B.equivFun.symm ![-5, 0, 2, 1, -6]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 2 ![![11, 0, 0, 0, 0], ![3, 1, -1, 0, 1]] 
  ![-5, 2, 2, 1, -4] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
    su := ![![22, 0, 0, 0, 0], ![6, 2, -2, 0, 2]]
    hsu := by decide  
    w := ![![-10, 4, 4, 2, -8], ![0, -2, 0, 0, 4]]
    hw := by decide  
    g := ![![![127, 206, -1500915, -49945, -386], ![104, 3002088, 99889, 0, 258]], ![![64, 102, -749488, -24940, -194], ![53, 1499106, 49880, 0, 129]]]
    h := ![![![-5991, 5776, 240, -5817, 17360], ![454, -65080, -546, 0, 0]], ![![-1858, 1791, 74, -1804, 5384], ![142, -20180, -168, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R11N0 : Ideal.span {2} * I11N0 =  Ideal.span {B.equivFun.symm ![-5, 2, 2, 1, -4]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 4 ![![11, 0, 0, 0, 0], ![-3, -5, -1, 0, 1]] 
  ![21, -4, -8, -5, 24] ![![4, 0, 0, 0, 0], ![2, 1, -1, 0, 2]] where
    su := ![![44, 0, 0, 0, 0], ![-12, -20, -4, 0, 4]]
    hsu := by decide  
    w := ![![84, -16, -32, -20, 96], ![48, -12, -12, -8, 36]]
    hw := by decide  
    g := ![![![-123149, -60404, 61827, -265, -123378], ![246805, -15, 783, 0, -261]], ![![124663, 61155, -62585, 267, 124888], ![-249832, 19, -787, 0, 261]]]
    h := ![![![-1692, -25133, -37732, -7258, 16545], ![16830, -71265, -2142, 0, 0]], ![![-798, -11849, -17788, -3421, 7801], ![7933, -33597, -1008, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R11N1 : Ideal.span {4} * I11N1 =  Ideal.span {B.equivFun.symm ![21, -4, -8, -5, 24]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 2 ![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] 
  ![-6, 1, 2, 1, -5] ![![2, 0, 0, 0, 0], ![-2, 0, 1, 1, -4]] where
    su := ![![22, 0, 0, 0, 0], ![-10, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![-12, 2, 4, 2, -10], ![16, -2, -6, -4, 18]]
    hw := by decide  
    g := ![![![-599, 409, -520, -111, 443], ![-597, -817, 0, 0, 0]], ![![223, -151, 191, 40, -160], ![222, 301, 0, 0, 0]]]
    h := ![![![-57666, 18887, -2618, -353, 1105], ![-126256, 17060, -1436, -760, 0]], ![![80448, -26327, 3654, 491, -1541], ![176136, -23752, 2017, 1060, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R11N2 : Ideal.span {2} * I11N2 =  Ideal.span {B.equivFun.symm ![-6, 1, 2, 1, -5]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS2 


noncomputable def E17RS1 : RelationCertificate Table 2 ![![17, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] 
  ![2, 0, -1, 0, 1] ![![2, 0, 0, 0, 0], ![-2, 0, 1, 1, -4]] where
    su := ![![34, 0, 0, 0, 0], ![-16, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![4, 0, -2, 0, 2], ![-4, 4, 0, 2, -6]]
    hw := by decide  
    g := ![![![6, 1, 2, -1, 0], ![0, 0, 0, 0, -7]], ![![-2, 1, 0, 0, -1], ![1, 0, 0, 0, 0]]]
    h := ![![![10458, -2145, 221, 39, -79], ![22181, -1838, 177, 84, 0]], ![![6630, -1262, 130, 25, -51], ![14062, -958, 116, 54, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R17N1 : Ideal.span {2} * I17N1 =  Ideal.span {B.equivFun.symm ![2, 0, -1, 0, 1]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS1 
