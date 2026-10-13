/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF6_4_19208000_1.PrimesBelow6_4_19208000_1F2
import LeanBridge.IdealArithmetic.Examples.NF6_4_19208000_1.ClassGroupData6_4_19208000_1

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 7 ![![83, 0, 0, 0, 0, 0], ![38, 1, 0, 0, 0, 0]]
  ![19, 15, 5, 1, -11, -5] ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] where
    su := ![![581, 0, 0, 0, 0, 0], ![266, 7, 0, 0, 0, 0]]
    hsu := by decide
    w := ![![133, 105, 35, 7, -77, -35], ![63, 49, 35, 7, -42, -21]]
    hw := by decide
    g := ![![![-114817, 3042268, 7801383, 26748, 1609, 18], ![401811, -10848804, -182849, -2181, -166, 0]], ![![-58908, 1560862, 4002571, 13723, 826, 10], ![206157, -5566078, -93812, -1119, -88, 0]]]
    h := ![![![5757, -295329, -46533, 262461, 315839, 7402], ![-12574, 645392, 16718, -573710, -614371, 0]], ![![1049, -3108, 137804, 166845, 177542, 4107], ![-2291, 6849, -301894, -356480, -340884, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {7} * I83N0 =  Ideal.span {B.equivFun.symm ![19, 15, 5, 1, -11, -5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E83RS0 


noncomputable def E83RS1 : RelationCertificate Table 7 ![![83, 0, 0, 0, 0, 0], ![-38, 1, 0, 0, 0, 0]]
  ![4, -9, -3, -2, 1, 3] ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] where
    su := ![![581, 0, 0, 0, 0, 0], ![-266, 7, 0, 0, 0, 0]]
    hsu := by decide
    w := ![![28, -63, -21, -14, 7, 21], ![-7, -14, -21, -7, 7, 7]]
    hw := by decide
    g := ![![![9141, -242267, -603478, 7594, 1856, -60], ![-31993, 863919, -47638, -2768, 429, 0]], ![![-3935, 104223, 259619, -3267, -799, 26], ![13772, -371661, 20492, 1192, -186, 0]]]
    h := ![![![4870, -85680, 130330, -995, -508, 6], ![10637, -186863, 260081, 4671, -495, 0]], ![![-1075, 14786, 46081, 42303, -6796, 28], ![-2348, 32234, 104892, 95159, -2323, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {7} * I83N1 =  Ideal.span {B.equivFun.symm ![4, -9, -3, -2, 1, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E83RS1 
