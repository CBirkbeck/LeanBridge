/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import LeanBridge.IdealArithmetic.Examples.NF6_4_19208000_1.RI6_4_19208000_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![4, -2, 1, -1, -2, 1]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-1, 0, 1, 0, 0, 0]

def zeta2 := B.equivFun.symm ![-1, 0, -1, 0, 1, 0]

def zeta3 := B.equivFun.symm ![3, 2, 0, 0, -2, -1]

def zeta4 := B.equivFun.symm ![-2, -2, -1, 0, 0, 1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] ![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]]
  ![![4, -2, 1, -1, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0, 0, 0, 0], ![14, 7, 0, 0, 0, 0]], ![![14, 7, 0, 0, 0, 0], ![4, 4, 5, 0, 0, 0]]]
 hmul := by decide
 f := ![![![![68942, -388608, -1714055, 778287, 2877610, 55704], ![-240494, 1480376, 2288612, -3879562, -398921, 0]], ![![0, 0, 0, 0, 0, 0], ![-3212, 3208, 22522, 12848, -322, 0]]]]
 g := ![![![![35, 21, 14, 7, -14, -14]], ![![20, 11, -1, 4, -9, -6]]], ![![![20, 11, -1, 4, -9, -6]], ![![10, 6, -1, 1, -4, -3]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-2, 0, 0, 0, 1, 0])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-1, 0, 0, 0, 1, 0])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta3 : IsUnit zeta3 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-6, 4, -1, 1, 3, -2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta4 : IsUnit zeta4 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![3, -1, -1, -1, -3, 0])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
