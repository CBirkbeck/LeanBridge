/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F0
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F1
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F2
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F3

noncomputable section

def PB122 : PrimesBelowBoundCertificate' O 122 := by
  refine primesBelowBoundCertificate_of_Interval' O ![1, 23, 61, 103, 121] 121 rfl rfl ?_ ?_
  · decide
  · rintro ⟨i,hi⟩
    interval_cases i 
    exact PB122I0
    exact PB122I1
    exact PB122I2
    exact PB122I3
