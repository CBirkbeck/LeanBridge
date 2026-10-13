/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF3_1_24843_1.PrimesBelow3_1_24843_1F1
import LeanBridge.IdealArithmetic.Examples.NF3_1_24843_1.ClassGroupData3_1_24843_1

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 12 ![![41, 0, 0], ![9, 1, 0]] 
  ![-28, -6, -5] ![![12, 0, 0], ![2, 1, 1]] where
    su := ![![492, 0, 0], ![108, 12, 0]]
    hsu := by decide  
    w := ![![-336, -72, -60], ![-480, -84, -72]]
    hw := by decide  
    g := ![![![-4517, -94, -576], ![-803, 1927, 0]], ![![-993, -21, -127], ![-170, 423, 0]]]
    h := ![![![10599, -85273, -31975], ![267, 436990, 0]], ![![15161, -121969, -45735], ![378, 625043, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R41N1 : Ideal.span {12} * I41N1 =  Ideal.span {B.equivFun.symm ![-28, -6, -5]} * (J0 ^ 2*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E41RS1 
