/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F3
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.ClassGroupData5_1_3790297_2

set_option linter.all false

noncomputable section


noncomputable def E113RS1 : RelationCertificate Table 2 ![![113, 0, 0, 0, 0], ![39, 1, 0, 0, 0]] 
  ![-4, -1, 2, 1, -5] ![![2, 0, 0, 0, 0], ![-2, 0, 1, 1, -4]] where
    su := ![![226, 0, 0, 0, 0], ![78, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![-8, -2, 4, 2, -10], ![12, -4, 0, 0, 2]]
    hw := by decide  
    g := ![![![-256, 170, -216, -44, 187], ![-236, -339, 0, 0, 0]], ![![-90, 60, -77, -16, 68], ![-83, -120, 0, 0, 0]]]
    h := ![![![-4610847, 73400843, 2078891, 26319, 9195], ![13352973, -213024947, -571266, -64940, 0]], ![![5286654, -84161638, -2383729, -30179, -10543], ![-15310104, 244255064, 655207, 74460, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R113N1 : Ideal.span {2} * I113N1 =  Ideal.span {B.equivFun.symm ![-4, -1, 2, 1, -5]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E113RS1 


noncomputable def E113RS2 : RelationCertificate Table 2 ![![113, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] 
  ![-1, 0, 0, 1, -2] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
    su := ![![226, 0, 0, 0, 0], ![-8, 2, 0, 0, 0]]
    hsu := by decide  
    w := ![![-2, 0, 0, 2, -4], ![-2, -2, -4, -2, 10]]
    hw := by decide  
    g := ![![![-49001, -78294, -97786, -146787, 146734], ![-39147, 97754, 293601, 0, -97867]], ![![1581, 2525, 3154, 4735, -4733], ![1264, -3153, -9471, 0, 3157]]]
    h := ![![![-63413, 852161, -209412, 6, 158], ![-1790301, 23627368, -7373, -1116, 0]], ![![-188165, 2528588, -621382, 18, 469], ![-5312349, 70108664, -21907, -3312, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R113N2 : Ideal.span {2} * I113N2 =  Ideal.span {B.equivFun.symm ![-1, 0, 0, 1, -2]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E113RS2 
