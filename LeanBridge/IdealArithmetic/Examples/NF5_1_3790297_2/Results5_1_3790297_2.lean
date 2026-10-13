/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.Invariants5_1_3790297_2

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^5 - X^4 + 3*X^2 + 21*X + 4`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^5 - X^4 + 3*X^2 + 21*X + 4)) := rfl

lemma T_irreducible' : Irreducible (X^5 - X^4 + 3*X^2 + 21*X + 4 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = 3790297 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 2 := K_nrComplexPlaces

def class_group_equiv' :
  (∀ i : Fin 2 , (ZMod (![2, 2] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_4' : classNumber K = 4 := class_number_K_eq_4 