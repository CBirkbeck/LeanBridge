/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F6
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

set_option linter.all false

noncomputable section


noncomputable def E307RS1 : RelationCertificate Table 3 ![![307, 0, 0, 0], ![36, 1, 0, 0]] 
  ![-532, -281, -15, 4] ![![3, 0, 0, 0], ![-1, 1, 0, 0]] where
    su := ![![921, 0, 0, 0], ![108, 3, 0, 0]]
    hsu := by decide  
    w := ![![-1596, -843, -45, 12], ![2064, 1077, 54, -15]]
    hw := by decide  
    g := ![![![1128107, 11250371, -12375097, 1616], ![3374089, 37120598, -4912, 0]], ![![135925, 1355888, -1491461, 195], ![406655, 4473815, -592, 0]]]
    h := ![![![-16660, 1307939, 36812, 13], ![142058, -11157767, -3987, 0]], ![![21460, -1691606, -47653, -18], ![-182987, 14430733, 5521, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R307N1 : Ideal.span {3} * I307N1 =  Ideal.span {B.equivFun.symm ![-532, -281, -15, 4]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E307RS1 


noncomputable def E307RS2 : RelationCertificate Table 3 ![![307, 0, 0, 0], ![96, 1, 0, 0]] 
  ![-196, -117, -10, 2] ![![3, 0, 0, 0], ![1, 1, 0, 0]] where
    su := ![![921, 0, 0, 0], ![288, 3, 0, 0]]
    hsu := by decide  
    w := ![![-588, -351, -30, 6], ![570, 351, 33, -6]]
    hw := by decide  
    g := ![![![29696, -346608, -379435, 35], ![-105634, 1137944, 0, 0]], ![![469671, -4711844, -5182469, 11], ![-1414056, 15547298, -1, 0]]]
    h := ![![![-2188, 15016, 156, 0], ![6995, -48094, 2, 0]], ![![1642, -14734, -249, -1], ![-5249, 47174, 305, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R307N2 : Ideal.span {3} * I307N2 =  Ideal.span {B.equivFun.symm ![-196, -117, -10, 2]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E307RS2 


noncomputable def E311RS0 : RelationCertificate Table 3 ![![311, 0, 0, 0], ![92, 1, 0, 0]] 
  ![-847, -366, -16, 5] ![![3, 0, 0, 0], ![1, 1, 0, 0]] where
    su := ![![933, 0, 0, 0], ![276, 3, 0, 0]]
    hsu := by decide  
    w := ![![-2541, -1098, -48, 15], ![1068, 447, 18, -6]]
    hw := by decide  
    g := ![![![246361, -2461690, -2707125, 827], ![-738442, 8123892, -2488, 0]], ![![74459, -744049, -818230, 250], ![-223196, 2455450, -752, 0]]]
    h := ![![![-32445, 1263591, 14749, 11], ![109669, -4272683, -3416, 0]], ![![13500, -531209, -6327, -6], ![-45632, 1796215, 1864, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R311N0 : Ideal.span {3} * I311N0 =  Ideal.span {B.equivFun.symm ![-847, -366, -16, 5]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E311RS0 


noncomputable def E311RS1 : RelationCertificate Table 9 ![![311, 0, 0, 0], ![-71, 1, 0, 0]] 
  ![-335, -105, 1, 1] ![![9, 0, 0, 0], ![-2, 1, 0, 0]] where
    su := ![![2799, 0, 0, 0], ![-639, 9, 0, 0]]
    hsu := by decide  
    w := ![![-3015, -945, 9, 9], ![1053, 207, -27, 0]]
    hw := by decide  
    g := ![![![-4337217753, -184331757043, 93262681347, -6249175], ![-19517480169, -839251646950, 56242571, 0]], ![![975048505, 41439562040, -20966352905, 1404875], ![4387718339, 188671888390, -12643874, 0]]]
    h := ![![![-17247, 1535989, -22695, 15], ![-75542, 6727002, -4664, 0]], ![![6063, -536775, 7985, -6], ![26556, -2350852, 1866, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R311N1 : Ideal.span {9} * I311N1 =  Ideal.span {B.equivFun.symm ![-335, -105, 1, 1]} * (J0 ^ 0*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E311RS1 


noncomputable def E311RS2 : RelationCertificate Table 9 ![![311, 0, 0, 0], ![-18, 1, 0, 0]] 
  ![-163, -86, -6, 1] ![![9, 0, 0, 0], ![-4, 1, 0, 0]] where
    su := ![![2799, 0, 0, 0], ![-162, 9, 0, 0]]
    hsu := by decide  
    w := ![![-1467, -774, -54, 9], ![1035, 513, 18, -9]]
    hw := by decide  
    g := ![![![85129, 2075909, -526527, 533], ![192831, 4719584, -4766, 0]], ![![-4779, -116724, 29606, -30], ![-10837, -265376, 268, 0]]]
    h := ![![![-2369, 216276, -12044, 2], ![-40922, 3734500, -621, 0]], ![![1733, -152575, 8507, -2], ![29936, -2634497, 621, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R311N2 : Ideal.span {9} * I311N2 =  Ideal.span {B.equivFun.symm ![-163, -86, -6, 1]} * (J0 ^ 2*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E311RS2 


noncomputable def E311RS3 : RelationCertificate Table 3 ![![311, 0, 0, 0], ![-4, 1, 0, 0]] 
  ![-79, -50, -6, 1] ![![3, 0, 0, 0], ![-1, 1, 0, 0]] where
    su := ![![933, 0, 0, 0], ![-12, 3, 0, 0]]
    hsu := by decide  
    w := ![![-237, -150, -18, 3], ![462, 303, 36, -6]]
    hw := by decide  
    g := ![![![769851, 7699388, -8471017, 1659], ![2309846, 25408078, -4976, 0]], ![![-7425, -74272, 81715, -16], ![-22280, -245097, 48, 0]]]
    h := ![![![-161, 18456, -4604, 0], ![-12498, 1431842, 1, 0]], ![![314, -35966, 8976, -1], ![24375, -2790288, 309, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R311N3 : Ideal.span {3} * I311N3 =  Ideal.span {B.equivFun.symm ![-79, -50, -6, 1]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E311RS3 
