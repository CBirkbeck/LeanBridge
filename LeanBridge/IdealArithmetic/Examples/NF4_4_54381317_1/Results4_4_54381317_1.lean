/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.Invariants4_4_54381317_1

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^4 - X^3 - 80*X^2 - 332*X - 383`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^4 - X^3 - 80*X^2 - 332*X - 383)) := rfl

lemma T_irreducible' : Irreducible (X^4 - X^3 - 80*X^2 - 332*X - 383 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = 54381317 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 0 := K_nrComplexPlaces

def class_group_equiv' :
  (∀ i : Fin 2 , (ZMod (![3, 3] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_9' : classNumber K = 9 := class_number_K_eq_9
