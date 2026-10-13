/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F2
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

set_option linter.all false

noncomputable section


noncomputable def E97RS1 : RelationCertificate Table 9 ![![97, 0, 0, 0], ![-42, 1, 0, 0]] 
  ![102, 83, 14, -2] ![![9, 0, 0, 0], ![-128, -67, -4, 1]] where
    su := ![![873, 0, 0, 0], ![-378, 9, 0, 0]]
    hsu := by decide  
    w := ![![918, 747, 126, -18], ![-5013, -2826, -207, 45]]
    hw := by decide  
    g := ![![![22, 646, 189, -1], ![-4850, -1620, 0, 0]], ![![51, -242, -78, 0], ![2064, 688, 0, 0]]]
    h := ![![![86754, -1062553, 29365, -98], ![200358, -2449223, 9504, 0]], ![![-474071, 5864779, -161837, 535], ![-1094865, 13518786, -51890, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R97N1 : Ideal.span {9} * I97N1 =  Ideal.span {B.equivFun.symm ![102, 83, 14, -2]} * (J0 ^ 2*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E97RS1 


noncomputable def E97RS2 : RelationCertificate Table 9 ![![97, 0, 0, 0], ![-25, 1, 0, 0]] 
  ![-40, -4, 1, 0] ![![9, 0, 0, 0], ![-128, -67, -4, 1]] where
    su := ![![873, 0, 0, 0], ![-225, 9, 0, 0]]
    hsu := by decide  
    w := ![![-360, -36, 9, 0], ![2439, 1251, 72, -18]]
    hw := by decide  
    g := ![![![-1689, -451046, -131808, 1010], ![3440787, 1149971, 0, 0]], ![![442, 111608, 32612, -250], ![-851317, -284526, 0, 0]]]
    h := ![![![-9970, 174, -105241, 4210], ![-38682, -872, -408370, 0]], ![![67793, 804, 1462509, -58506], ![263026, 13635, 5675080, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R97N2 : Ideal.span {9} * I97N2 =  Ideal.span {B.equivFun.symm ![-40, -4, 1, 0]} * (J0 ^ 2*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E97RS2 
