/-
Copyright (c) 2025 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import Mathlib.Data.List.Indexes
import LeanBridge.ForMathlib.Algebra.Polynomial.PolynomialsAsLists
import LeanBridge.IdealArithmetic.DedekindProject.Auxiliary.LinearAlgebraAuxiliaryLemmas
import LeanBridge.IdealArithmetic.DedekindProject.TimesTable.Defs
import LeanBridge.IdealArithmetic.DedekindProject.TimesTable.TimesTableAsLists

open BigOperators

/- By reflection, we can provide Decidable instances for basic arithmetic operations on a
ring `S` with a `TimesTable`.

TO DO: Define inductively the expressions composing these operations and give a Decidable
instance.

Note: We don't use this in our certificates. In the fields that include a proof by computation,
we usually operate directly with the list representation. -/

variable {n : ℕ} {R : Type*} [Semiring R]

lemma table_add_list_eq_add_iff {S : Type*} [AddCommMonoid S] [Module R S] [Mul S]
    (TT : TimesTable (Fin n) R S) (a b c : Fin n → R) :
    List.ofFn c = (List.ofFn a) + (List.ofFn b) ↔
      (TT.basis.equivFun.symm a) + (TT.basis.equivFun.symm b) = TT.basis.equivFun.symm c := by
  constructor
  · intro h
    exact table_add_list_eq_add TT.basis a b c h
  · intro hc
    rw [List.add_ofFn, List.ofFn_inj]
    apply_fun TT.basis.equivFun.symm
    rw [← hc, map_add]
    exact LinearEquiv.injective TT.basis.equivFun.symm

lemma table_mulPointwise_eq_smul_iff {S : Type*} [AddCommMonoid S] [Module R S] [Mul S]
    (TT : TimesTable (Fin n) R S) (a c : Fin n → R) (d : R) :
   List.ofFn c = List.mulPointwise d (List.ofFn a) ↔
    d • (TT.basis.equivFun.symm a ) = (TT.basis.equivFun.symm c ) := by
  constructor
  · intro h
    exact table_mulPointwise_eq_smul TT.basis a c d h
  · intro h
    by_contra! hcc
    let e := FnOfList n (List.mulPointwise d (List.ofFn a)) (by rw [List.mulPointwise_length, List.length_ofFn])
    have : List.ofFn e = (List.mulPointwise d (List.ofFn a)) := listOfFn_of_FnOfList _ _ _
    have hc := table_mulPointwise_eq_smul TT.basis a e d this
    rw [hc] at h
    rw [LinearEquiv.injective TT.basis.equivFun.symm h] at this
    exact hcc this

lemma table_mul_list_eq_mul_iff {S : Type*} [NonUnitalNonAssocSemiring S] [Module R S]
  [SMulCommClass R S S] [IsScalarTower R S S] (TT : TimesTable (Fin n) R S) (a b c : Fin n → R) :
   List.ofFn c = table_mul_list' TT.table (List.ofFn a) (List.ofFn b) ↔
   (TT.basis.equivFun.symm a) * (TT.basis.equivFun.symm b) = (TT.basis.equivFun.symm c) := by
  constructor
  · intro h
    exact table_mul_list_eq_mul TT.table TT.basis a b c TT.basis_mul_basis h
  · intro h
    by_contra! hcc
    let d := FnOfList n (table_mul_list' TT.table (List.ofFn a) (List.ofFn b)) (table_mul_list_length TT.table _ _ )
    have : List.ofFn d = table_mul_list' TT.table (List.ofFn a) (List.ofFn b) := listOfFn_of_FnOfList _ _ _
    have hc := table_mul_list_eq_mul TT.table TT.basis a b d TT.basis_mul_basis this
    rw [hc] at h
    rw [LinearEquiv.injective TT.basis.equivFun.symm h] at this
    exact hcc this

instance (priority := 10001) [DecidableEq R] {S : Type*} [NonUnitalNonAssocSemiring S] [Module R S]
  [SMulCommClass R S S] [IsScalarTower R S S] {TT : TimesTable (Fin n) R S} : ∀ (a b c : Fin n → R),
  Decidable ((TT.basis.equivFun.symm a) + (TT.basis.equivFun.symm b) = TT.basis.equivFun.symm c) :=
  fun a b c => decidable_of_iff _ (table_add_list_eq_add_iff TT a b c)

instance (priority := 10001) [DecidableEq R] {S : Type*} [AddCommMonoid S] [Module R S] [Mul S]
    {TT : TimesTable (Fin n) R S} : ∀ (a b : Fin n → R), ∀ (d : R),
  Decidable (d • (TT.basis.equivFun.symm a) = TT.basis.equivFun.symm b) :=
  fun a b d => decidable_of_iff _ (table_mulPointwise_eq_smul_iff TT a b d)

instance (priority := 10001) [DecidableEq R] {S : Type*} [NonUnitalNonAssocSemiring S] [Module R S]
  [SMulCommClass R S S] [IsScalarTower R S S] {TT : TimesTable (Fin n) R S} : ∀ (a b c : Fin n → R),
  Decidable ((TT.basis.equivFun.symm a) * (TT.basis.equivFun.symm b) = TT.basis.equivFun.symm c) :=
  fun a b c => decidable_of_iff _ (table_mul_list_eq_mul_iff TT a b c)

/- Example -/

open Polynomial

noncomputable def T : ℤ[X] := X^3 + 27*X - 18

@[reducible]
def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

def O : Subalgebra ℤ K := sorry

noncomputable def T3 : TimesTable (Fin 3) ℤ O where
  basis := sorry
  table := ![ ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]],
          ![![0, 1, 0], ![0, 0, 3], ![6, -9, 0]],
          ![![0, 0, 1], ![6, -9, 0], ![0, 2, -9]]]
  basis_mul_basis := sorry

#count_heartbeats
example : T3.basis.equivFun.symm ![1,2,3] * T3.basis.equivFun.symm ![-1,3,4]  =
  T3.basis.equivFun.symm ![101, -128, -89] := by decide

example : T3.basis.equivFun.symm ![1,2,3] + T3.basis.equivFun.symm ![-1,3,4]  =
  T3.basis.equivFun.symm ![0, 5, 7] := by decide

-- This is slightly faster
example : List.ofFn ![101, -128, -89] = table_mul_list' T3.table (List.ofFn ![1,2,3]) (List.ofFn ![-1,3,4]) := by decide
