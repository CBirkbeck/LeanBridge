/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF3_1_24843_1.PrimesBelow3_1_24843_1F0
import LeanBridge.IdealArithmetic.Examples.NF3_1_24843_1.ClassGroupData3_1_24843_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 4 ![![2, 0, 0], ![0, 0, 1]] 
  ![0, -2, 1] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![8, 0, 0], ![0, 0, 4]]
    hsu := by decide  
    w := ![![0, -8, 4], ![32, 0, -4]]
    hw := by decide  
    g := ![![![0, -10, -11], ![39, 15, -1]], ![![0, -10, 0], ![35, 0, -2]]]
    h := ![![![0, -1, 0], ![1, 0, 0]], ![![4, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R2N0 : Ideal.span {4} * I2N0 =  Ideal.span {B.equivFun.symm ![0, -2, 1]} * (J0 ^ 2*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![1, 1, 0]] 
  ![1, 0, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![2, 0, 0], ![1, 1, 0]]
    hsu := by decide  
    w := ![![2, 0, 0], ![1, 1, 0]]
    hw := by decide  
    g := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![0, 0, 1]] 
  ![1, 0, 0] ![![3, 0, 0], ![0, 0, 1]] where
    su := ![![3, 0, 0], ![0, 0, 1]]
    hsu := by decide  
    w := ![![3, 0, 0], ![0, 0, 1]]
    hw := by decide  
    g := ![![![-9, 10, 0], ![0, 3, -3]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-9, 10, 0], ![0, 3, -3]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 3 ![![3, 0, 0], ![-1, 0, 1]] 
  ![-4, 1, 0] ![![3, 0, 0], ![0, 0, 1]] where
    su := ![![9, 0, 0], ![-3, 0, 3]]
    hsu := by decide  
    w := ![![-12, 3, 0], ![30, 0, -3]]
    hw := by decide  
    g := ![![![-1385, -693, -63], ![-18, 0, 208]], ![![525, 261, 24], ![8, 0, -78]]]
    h := ![![![8, 0, 1], ![-2, -1, 0]], ![![3, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R3N1 : Ideal.span {3} * I3N1 =  Ideal.span {B.equivFun.symm ![-4, 1, 0]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 6 ![![5, 0, 0], ![0, 0, 1]] 
  ![-10, 0, 1] ![![6, 0, 0], ![2, 1, 1]] where
    su := ![![30, 0, 0], ![0, 0, 6]]
    hsu := by decide  
    w := ![![-60, 0, 6], ![30, 0, -6]]
    hw := by decide  
    g := ![![![-3, -1, -1], ![5, 0, 0]], ![![-3, -1, -1], ![4, 0, 0]]]
    h := ![![![-2, 0, 0], ![1, 0, 0]], ![![1, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R5N0 : Ideal.span {6} * I5N0 =  Ideal.span {B.equivFun.symm ![-10, 0, 1]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 12 ![![5, 0, 0], ![-1, 1, 0]] 
  ![-16, -2, 3] ![![12, 0, 0], ![-3, 0, 1]] where
    su := ![![60, 0, 0], ![-12, 12, 0]]
    hsu := by decide  
    w := ![![-192, -24, 36], ![48, 36, -24]]
    hw := by decide  
    g := ![![![-472, 55, -28], ![127, 205, -4]], ![![5, 0, 0], ![4, -1, 0]]]
    h := ![![![743, 1411, -2157], ![135, 3596, 0]], ![![-155, -296, 452], ![-25, -754, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R5N1 : Ideal.span {12} * I5N1 =  Ideal.span {B.equivFun.symm ![-16, -2, 3]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 6 ![![7, 0, 0], ![0, 1, 0]] 
  ![20, 4, 3] ![![6, 0, 0], ![3, 0, 1]] where
    su := ![![42, 0, 0], ![0, 6, 0]]
    hsu := by decide  
    w := ![![120, 24, 18], ![240, 42, 36]]
    hw := by decide  
    g := ![![![32765019, 4087538, -1330692], ![16160731, -8167577, -2250]], ![![-1, 0, -1], ![5, 0, 0]]]
    h := ![![![0, -3, 9], ![5, -20, 0]], ![![0, -5, 18], ![2, -40, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R7N0 : Ideal.span {6} * I7N0 =  Ideal.span {B.equivFun.symm ![20, 4, 3]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E7RS0 


noncomputable def E11RS1 : RelationCertificate Table 3 ![![11, 0, 0], ![2, 1, 0]] 
  ![2, 1, 0] ![![3, 0, 0], ![0, 0, 1]] where
    su := ![![33, 0, 0], ![6, 3, 0]]
    hsu := by decide  
    w := ![![6, 3, 0], ![30, 0, 3]]
    hw := by decide  
    g := ![![![67, 33, 3], ![2, 0, -10]], ![![21, 10, 0], ![3, 0, -3]]]
    h := ![![![-30, 30, 90], ![1, -330, 0]], ![![-162, 164, 491], ![-4, -1800, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R11N1 : Ideal.span {3} * I11N1 =  Ideal.span {B.equivFun.symm ![2, 1, 0]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 12 ![![13, 0, 0], ![0, 1, 0]] 
  ![-4, 2, -1] ![![12, 0, 0], ![2, 1, 1]] where
    su := ![![156, 0, 0], ![0, 12, 0]]
    hsu := by decide  
    w := ![![-48, 24, -12], ![0, -12, 0]]
    hw := by decide  
    g := ![![![-32, -1, -4], ![-5, 13, 0]], ![![0, 0, 0], ![-1, 0, 0]]]
    h := ![![![0, 0, -1], ![6, 4, 0]], ![![0, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R13N0 : Ideal.span {12} * I13N0 =  Ideal.span {B.equivFun.symm ![-4, 2, -1]} * (J0 ^ 2*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E13RS0 


noncomputable def E17RS1 : RelationCertificate Table 4 ![![17, 0, 0], ![-5, 1, 0]] 
  ![8, 2, 1] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![68, 0, 0], ![-20, 4, 0]]
    hsu := by decide  
    w := ![![32, 8, 4], ![36, 8, 8]]
    hw := by decide  
    g := ![![![-64, 3, 203], ![-15, -270, 0]], ![![-3826, 225, 12155], ![-899, -16207, 0]]]
    h := ![![![-297, -1761, 881], ![-13, -4992, 0]], ![![-334, -1987, 994], ![-11, -5632, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![8, 2, 1]} * (J0 ^ 2*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E17RS1 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![1, 1, 0]] 
  ![-8, 0, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![46, 0, 0], ![2, 2, 0]]
    hsu := by decide  
    w := ![![-16, 0, 2], ![22, -8, 2]]
    hw := by decide  
    g := ![![![9, 0, 2], ![5, 0, 0]], ![![1, 0, 5], ![1, -3, 0]]]
    h := ![![![0, 0, -1], ![0, 8, 0]], ![![0, 0, 2], ![-4, -15, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![-8, 0, 1]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 12 ![![29, 0, 0], ![-9, 1, 0]] 
  ![0, 2, 1] ![![12, 0, 0], ![2, 1, 1]] where
    su := ![![348, 0, 0], ![-108, 12, 0]]
    hsu := by decide  
    w := ![![0, 24, 12], ![108, 12, 12]]
    hw := by decide  
    g := ![![![0, -267, 93], ![12, -667, 386]], ![![0, 87, -39], ![95, 230, -137]]]
    h := ![![![5, 3, -1], ![15, 10, 0]], ![![-20, -247, 74], ![14, -715, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R29N1 : Ideal.span {12} * I29N1 =  Ideal.span {B.equivFun.symm ![0, 2, 1]} * (J0 ^ 2*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS1 


noncomputable def E31RS0 : RelationCertificate Table 6 ![![31, 0, 0], ![4, 1, 0]] 
  ![-2, -2, 1] ![![6, 0, 0], ![2, 1, 1]] where
    su := ![![186, 0, 0], ![24, 6, 0]]
    hsu := by decide  
    w := ![![-12, -12, 6], ![-12, 6, -6]]
    hw := by decide  
    g := ![![![-1482, 28, -143], ![-511, 341, 0]], ![![-193, 3, -19], ![-63, 44, 0]]]
    h := ![![![74, -234, -233], ![28, 2408, 0]], ![![90, -284, -283], ![33, 2924, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R31N0 : Ideal.span {6} * I31N0 =  Ideal.span {B.equivFun.symm ![-2, -2, 1]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 6 ![![31, 0, 0], ![7, 1, 0]] 
  ![-4, 0, 1] ![![6, 0, 0], ![2, 1, 1]] where
    su := ![![186, 0, 0], ![42, 6, 0]]
    hsu := by decide  
    w := ![![-24, 0, 6], ![42, 6, 0]]
    hw := by decide  
    g := ![![![-1478, 29, -142], ![-510, 341, 0]], ![![-287, 5, -28], ![-95, 66, 0]]]
    h := ![![![207, -1283, -641], ![29, 6624, 0]], ![![-368, 2208, 1104], ![1, -11408, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R31N1 : Ideal.span {6} * I31N1 =  Ideal.span {B.equivFun.symm ![-4, 0, 1]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 6 ![![31, 0, 0], ![-11, 1, 0]] 
  ![6, 2, 1] ![![6, 0, 0], ![2, 1, 1]] where
    su := ![![186, 0, 0], ![-66, 6, 0]]
    hsu := by decide  
    w := ![![36, 12, 6], ![120, 18, 18]]
    hw := by decide  
    g := ![![![1475, -29, 143], ![511, -341, 0]], ![![-523, 10, -51], ![-180, 121, 0]]]
    h := ![![![-450, -5428, 1357], ![6, -14022, 0]], ![![-1533, -18335, 4584], ![-16, -47367, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R31N2 : Ideal.span {6} * I31N2 =  Ideal.span {B.equivFun.symm ![6, 2, 1]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E31RS2 
