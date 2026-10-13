/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF6_4_19208000_1.Invariants6_4_19208000_1

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^6 - 5*X^4 - 50*X^2 + 125`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^6 - 5*X^4 - 50*X^2 + 125)) := rfl

lemma T_irreducible' : Irreducible (X^6 - 5*X^4 - 50*X^2 + 125 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = -19208000 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 1 := K_nrComplexPlaces

def class_group_equiv' :
  (∀ i : Fin 1 , (ZMod (![2] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_2' : classNumber K = 2 := class_number_K_eq_2
