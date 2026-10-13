/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF6_4_19208000_1.PrimesBelow6_4_19208000_1F1
import LeanBridge.IdealArithmetic.Examples.NF6_4_19208000_1.ClassGroupData6_4_19208000_1

set_option linter.all false

noncomputable section


noncomputable def E43RS1 : RelationCertificate Table 7 ![![43, 0, 0, 0, 0, 0], ![21, 1, 0, 0, 0, 0]]
  ![-11, 9, 3, 2, 6, -3] ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] where
    su := ![![301, 0, 0, 0, 0, 0], ![147, 7, 0, 0, 0, 0]]
    hsu := by decide
    w := ![![-77, 63, 21, 14, 42, -21], ![-7, 7, 21, 7, 7, 0]]
    hw := by decide
    g := ![![![25271, -669689, -1700050, 2235, -1513, 52], ![-88443, 2388144, -20172, 2268, -378, 0]], ![![13125, -347841, -883016, 1161, -786, 27], ![-45934, 1240416, -10478, 1178, -196, 0]]]
    h := ![![![-410, -326, 5914, 43362, 619, -459], ![839, 628, -12259, -88205, 19734, 0]], ![![-274, 12061, 2007, -621, 12420, 598], ![561, -24723, 1777, 1187, -25714, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {7} * I43N1 =  Ideal.span {B.equivFun.symm ![-11, 9, 3, 2, 6, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS1 


noncomputable def E43RS2 : RelationCertificate Table 7 ![![43, 0, 0, 0, 0, 0], ![-21, 1, 0, 0, 0, 0]]
  ![-10, -2, -3, -2, 8, 3] ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] where
    su := ![![301, 0, 0, 0, 0, 0], ![-147, 7, 0, 0, 0, 0]]
    hsu := by decide
    w := ![![-70, -14, -21, -14, 56, 21], ![-35, -14, 14, -7, 21, 14]]
    hw := by decide
    g := ![![![-227587, 6030954, 18264030, 768041, -1878339, -85362], ![796543, -21506609, -10157596, 2390660, 597536, 0]], ![![108183, -2866815, -8681813, -365088, 892876, 40577], ![-378635, 10223169, 4828430, -1136410, -284040, 0]]]
    h := ![![![-4420, 606, 34566, -4970, -65358, 3150], ![-9050, 810, 70971, -6797, -135447, 0]], ![![-2210, -244, 19348, -2236, -24948, 1203], ![-4525, -715, 39447, -2700, -51727, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {7} * I43N2 =  Ideal.span {B.equivFun.symm ![-10, -2, -3, -2, 8, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS2 
