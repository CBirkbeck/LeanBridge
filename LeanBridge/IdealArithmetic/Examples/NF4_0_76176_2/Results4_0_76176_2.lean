/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_0_76176_2.Invariants4_0_76176_2

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^4 - 2*X^3 + 7*X^2 - 6*X + 78`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^4 - 2*X^3 + 7*X^2 - 6*X + 78)) := rfl

lemma T_irreducible' : Irreducible (X^4 - 2*X^3 + 7*X^2 - 6*X + 78 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = 76176 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 2 := K_nrComplexPlaces

def class_group_equiv' :
  (∀ i : Fin 2 , (ZMod (![6, 2] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_12' : classNumber K = 12 := class_number_K_eq_12 