/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF2_0_231_1.PrimesBelow2_0_231_1F0
import LeanBridge.IdealArithmetic.Examples.NF2_0_231_1.ClassGroupData2_0_231_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 32 ![![2, 0], ![0, 1]]
  ![2, 1] ![![32, 0], ![29, 1]] where
    su := ![![64, 0], ![0, 32]]
    hsu := by decide
    w := ![![64, 32], ![0, 32]]
    hw := by decide
    g := ![![![1, 0], ![-1, 0]], ![![0, 0], ![1, 0]]]
    h := ![![![1, 0], ![1, 0]], ![![0, 0], ![1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {32} * I2N0 =  Ideal.span {B.equivFun.symm ![2, 1]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E2RS0


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0], ![1, 1]]
  ![1, 0] ![![2, 0], ![1, 1]] where
    su := ![![2, 0], ![1, 1]]
    hsu := by decide
    w := ![![2, 0], ![1, 1]]
    hw := by decide
    g := ![![![0, -1], ![2, 0]], ![![0, 0], ![1, 0]]]
    h := ![![![0, -1], ![2, 0]], ![![0, 0], ![1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1


noncomputable def E3RS0 : RelationCertificate Table 56 ![![3, 0], ![1, 1]]
  ![-10, -1] ![![56, 0], ![45, 1]] where
    su := ![![168, 0], ![56, 56]]
    hsu := by decide
    w := ![![-560, -56], ![-392, -56]]
    hw := by decide
    g := ![![![-1, 0], ![1, 0]], ![![-43, -1], ![53, 0]]]
    h := ![![![-3, 0], ![-1, 0]], ![![-3, -1], ![2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {56} * I3N0 =  Ideal.span {B.equivFun.symm ![-10, -1]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E3RS0


noncomputable def E5RS0 : RelationCertificate Table 14 ![![5, 0], ![1, 1]]
  ![4, -1] ![![14, 0], ![3, 1]] where
    su := ![![70, 0], ![14, 14]]
    hsu := by decide
    w := ![![56, -14], ![70, 0]]
    hw := by decide
    g := ![![![0, 0], ![1, 0]], ![![-1, 0], ![1, 0]]]
    h := ![![![0, -1], ![4, 0]], ![![0, -1], ![5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {14} * I5N0 =  Ideal.span {B.equivFun.symm ![4, -1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E5RS0


noncomputable def E5RS1 : RelationCertificate Table 224 ![![5, 0], ![3, 1]]
  ![-26, 3] ![![224, 0], ![157, 1]] where
    su := ![![1120, 0], ![672, 224]]
    hsu := by decide
    w := ![![-5824, 672], ![-4256, 448]]
    hw := by decide
    g := ![![![-155, -1], ![221, 0]], ![![-152, -1], ![217, 0]]]
    h := ![![![-4, 1], ![-2, 0]], ![![-5, 0], ![2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {224} * I5N1 =  Ideal.span {B.equivFun.symm ![-26, 3]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E5RS1


noncomputable def E7RS0 : RelationCertificate Table 1 ![![7, 0], ![3, 1]]
  ![1, 0] ![![7, 0], ![3, 1]] where
    su := ![![7, 0], ![3, 1]]
    hsu := by decide
    w := ![![7, 0], ![3, 1]]
    hw := by decide
    g := ![![![-2, -1], ![7, 0]], ![![0, 0], ![1, 0]]]
    h := ![![![-2, -1], ![7, 0]], ![![0, 0], ![1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {1} * I7N0 =  Ideal.span {B.equivFun.symm ![1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS0
