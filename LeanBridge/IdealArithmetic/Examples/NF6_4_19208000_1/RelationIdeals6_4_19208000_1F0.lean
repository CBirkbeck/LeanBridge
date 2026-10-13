/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF6_4_19208000_1.PrimesBelow6_4_19208000_1F0
import LeanBridge.IdealArithmetic.Examples.NF6_4_19208000_1.ClassGroupData6_4_19208000_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 7 ![![2, 0, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0]]
  ![-11, 9, -4, 2, 6, -3] ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] where
    su := ![![14, 0, 0, 0, 0, 0], ![7, 0, 7, 7, 0, 0]]
    hsu := by decide
    w := ![![-77, 63, -28, 14, 42, -21], ![-7, 7, 7, 0, 7, 0]]
    hw := by decide
    g := ![![![-1205, -631, 1022, 0, 1467, 585], ![-901, 2660, 13, -6, 0, -2048]], ![![-257, -563, -724, 0, 492, 195], ![-807, 2375, 13, -6, 0, -683]]]
    h := ![![![-8, 4, -8, -2, -3, -5], ![5, 1, 7, 0, 0, 0]], ![![0, 0, 0, 0, -3, -1], ![-1, 1, 2, 0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {7} * I2N0 =  Ideal.span {B.equivFun.symm ![-11, 9, -4, 2, 6, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 7 ![![3, 0, 0, 0, 0, 0], ![1, -1, 0, -1, 0, 0]]
  ![11, -2, -3, -2, -6, 3] ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] where
    su := ![![21, 0, 0, 0, 0, 0], ![7, -7, 0, -7, 0, 0]]
    hsu := by decide
    w := ![![77, -14, -21, -14, -42, 21], ![7, 7, 14, -7, -7, 0]]
    hw := by decide
    g := ![![![-2104106, 55758788, 142141801, 67352, 24673, -167], ![7364373, -198837944, -401444, -35010, 1168, 0]], ![![526304, -13947063, -35554227, -16847, -6171, 42], ![-1842065, 49735752, 100416, 8757, -292, 0]]]
    h := ![![![6, -3, 3, -7, -2, -3], ![-7, 0, -12, 0, 0, 0]], ![![0, 1, -1, 0, -2, 0], ![1, -1, 0, 0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {7} * I3N0 =  Ideal.span {B.equivFun.symm ![11, -2, -3, -2, -6, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 7 ![![3, 0, 0, 0, 0, 0], ![-1, -1, 0, -1, 0, 0]]
  ![-5, 6, 2, -1, 4, -2] ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] where
    su := ![![21, 0, 0, 0, 0, 0], ![-7, -7, 0, -7, 0, 0]]
    hsu := by decide
    w := ![![-35, 42, 14, -7, 28, -14], ![0, 7, 14, 0, -7, 0]]
    hw := by decide
    g := ![![![-17283, -9493, 1962, 2956, 1820, -228], ![60491, 2981, -14319, -3186, 1595, 0]], ![![10910, 5991, -1242, -1869, -1155, 145], ![-38186, -1876, 9036, 2023, -1015, 0]]]
    h := ![![![-2, 2, 4, 1, 3, 1], ![-1, 1, 5, 0, 0, 0]], ![![0, 0, -1, 0, -2, 0], ![0, -1, 0, 0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {7} * I3N1 =  Ideal.span {B.equivFun.symm ![-5, 6, 2, -1, 4, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 1 ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]]
  ![1, 0, 0, 0, 0, 0] ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] where
    su := ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]]
    hsu := by decide
    w := ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]]
    hw := by decide
    g := ![![![5, -2, 22, 56, 140, 20], ![-14, 14, -112, -140, -140, 0]], ![![-2, -13, -34, 14, 56, 8], ![8, 42, 14, -56, -56, 0]]]
    h := ![![![5, -2, 22, 56, 140, 20], ![-14, 14, -112, -140, -140, 0]], ![![-2, -13, -34, 14, 56, 8], ![8, 42, 14, -56, -56, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {1} * I7N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 7 ![![7, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]]
  ![-17, -9, -3, -2, 8, 3] ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] where
    su := ![![49, 0, 0, 0, 0, 0], ![-14, 7, 0, 0, 0, 0]]
    hsu := by decide
    w := ![![-119, -63, -21, -14, 56, 21], ![-49, -35, -21, -7, 21, 14]]
    hw := by decide
    g := ![![![94261765, -2497936828, -6368543918, -2946727, -23547, -14], ![-329916182, 8907736992, 20561232, 32928, 96, 0]], ![![-19099518, 506137198, 1290407726, 597072, 4771, 3], ![66848315, -1804904352, -4166160, -6672, -20, 0]]]
    h := ![![![-505, 566, -929, -943, 770, 881], ![-1759, 1106, -485, -3542, -6164, 0]], ![![-399, 644, -501, 5, -881, 51], ![-1393, 1560, 2148, 1092, -355, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {7} * I7N1 =  Ideal.span {B.equivFun.symm ![-17, -9, -3, -2, 8, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 7 ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]]
  ![-1, -3, -1, -3, 5, 1] ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] where
    su := ![![91, 0, 0, 0, 0, 0], ![14, 7, 0, 0, 0, 0]]
    hsu := by decide
    w := ![![-7, -21, -7, -21, 35, 7], ![-7, -7, -7, -7, 0, 7]]
    hw := by decide
    g := ![![![-2557, 67765, 141437, -16247, -1667, -9], ![8952, -241658, 109112, 2307, 65, 0]], ![![-556, 14687, 30657, -3521, -362, -2], ![1946, -52378, 23644, 501, 14, 0]]]
    h := ![![![-57, 199, 1319, 755, 967, 8], ![370, -1480, -4874, -2472, -103, 0]], ![![-43, 152, 579, 91, -320, -183], ![279, -1128, -944, -120, 2380, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {7} * I13N0 =  Ideal.span {B.equivFun.symm ![-1, -3, -1, -3, 5, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 7 ![![13, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]]
  ![-12, 6, 2, -1, 4, -2] ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] where
    su := ![![91, 0, 0, 0, 0, 0], ![-14, 7, 0, 0, 0, 0]]
    hsu := by decide
    w := ![![-84, 42, 14, -7, 28, -14], ![-14, 0, 14, 0, -7, 0]]
    hw := by decide
    g := ![![![-1490712, 39503796, 100707624, 39520, -7086, 22], ![5217483, -140872032, -296607, 9982, -152, 0]], ![![137448, -3642403, -9285631, -3644, 653, -2], ![-481067, 12988944, 27348, -920, 14, 0]]]
    h := ![![![-180, 92, -31, 183, -1497, 536], ![-1164, 13, -170, 1105, -6970, 0]], ![![-26, 10, -71, 170, -497, 85], ![-168, -19, -510, 850, -1105, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {7} * I13N1 =  Ideal.span {B.equivFun.symm ![-12, 6, 2, -1, 4, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 7 ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0]]
  ![-2, -6, -2, 1, 3, 2] ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] where
    su := ![![91, 0, 0, 0, 0, 0], ![35, 7, 0, 0, 0, 0]]
    hsu := by decide
    w := ![![-14, -42, -14, 7, 21, 14], ![-14, -14, -14, 0, 21, 7]]
    hw := by decide
    g := ![![![-148884, 3945408, 9858594, -95788, -694, -8], ![521097, -14069481, 668622, 946, 62, 0]], ![![-70906, 1878958, 4695050, -45618, -330, -4], ![248171, -6700440, 318425, 450, 30, 0]]]
    h := ![![![-174, 774, 1476, 375, -1809, -410], ![452, -2104, -1734, -628, 5332, 0]], ![![-154, 991, 1551, 227, -904, -205], ![400, -2657, -1376, -315, 2666, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {7} * I13N2 =  Ideal.span {B.equivFun.symm ![-2, -6, -2, 1, 3, 2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS2 


noncomputable def E13RS3 : RelationCertificate Table 7 ![![13, 0, 0, 0, 0, 0], ![-5, 1, 0, 0, 0, 0]]
  ![13, -3, -1, -3, -9, 1] ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] where
    su := ![![91, 0, 0, 0, 0, 0], ![-35, 7, 0, 0, 0, 0]]
    hsu := by decide
    w := ![![91, -21, -7, -21, -63, 7], ![21, 7, -7, -7, -28, -7]]
    hw := by decide
    g := ![![![-6665, 176650, 453794, 670, -3143, -10], ![23335, -629941, -13427, 4371, 68, 0]], ![![1333, -35362, -90851, -136, 639, 2], ![-4668, 126101, 2726, -888, -14, 0]]]
    h := ![![![551, -6, 888, -331, -993, 225], ![1430, 271, 2580, -344, -2924, 0]], ![![246, -296, 313, 119, -298, 33], ![639, -642, 172, 344, -430, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N3 : Ideal.span {7} * I13N3 =  Ideal.span {B.equivFun.symm ![13, -3, -1, -3, -9, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS3 
