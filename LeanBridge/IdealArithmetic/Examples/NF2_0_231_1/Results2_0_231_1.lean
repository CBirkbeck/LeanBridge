/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF2_0_231_1.Invariants2_0_231_1

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^2 - X + 58`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^2 - X + 58)) := rfl

lemma T_irreducible' : Irreducible (X^2 - X + 58 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = -231 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 1 := K_nrComplexPlaces

def class_group_equiv' :
  (∀ i : Fin 2 , (ZMod (![6, 2] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_12' : classNumber K = 12 := class_number_K_eq_12 