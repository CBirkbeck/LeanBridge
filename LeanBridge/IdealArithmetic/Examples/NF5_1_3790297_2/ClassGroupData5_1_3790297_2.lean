/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.RI5_1_3790297_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section 


def alpha0 := B.equivFun.symm ![0, 1, 0, 0, 0]

def alpha1 := B.equivFun.symm ![0, 0, -1, -1, 4]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-4, 0, 2, 1, -5]

def zeta2 := B.equivFun.symm ![5, -1, -2, -1, 6]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![0, 1, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![0, 2, 0, 0, 0]], ![![0, 2, 0, 0, 0], ![0, 0, 1, 0, 0]]]
 hmul := by decide
 f :=  ![![![![0, 0, 0, 0, -1], ![-1, -2, 0, 0, -2]], ![![0, 0, 0, 0, 0], ![6, 2, 1, 0, 0]]]]
 g :=  ![![![![-17, 2, 6, 3, -16]], ![![2, 0, 0, 0, 0]]], ![![![2, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 =  Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-2, 0, 1, 1, -4]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![2, 0, 0, 0, 0], ![-2, 0, 1, 1, -4]] ![![2, 0, 0, 0, 0], ![-2, 0, 1, 1, -4]]
  ![![0, 0, -1, -1, 4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-4, 0, 2, 2, -8]], ![![-4, 0, 2, 2, -8], ![8, 1, -2, 1, 0]]]
 hmul := by decide
 f :=  ![![![![-7, 0, 0, -2, 5], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![3, -1, 0, 0, 0]]]]
 g :=  ![![![![4, -1, -2, -1, 5]], ![![-6, 1, 2, 1, -5]]], ![![![-6, 1, 2, 1, -5]], ![![8, -1, -3, -2, 9]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 =  Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![0, 0, 0, 0, -1])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1, 2, -1, 1, -2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-2, 0, 1, 1, -4]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![-2, 0, 1, 1, -4]]
  ![![4, 0, 0, 0, 0], ![2, 1, -1, 0, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-4, 0, 2, 2, -8]], ![![0, 2, 0, 0, 0], ![0, 1, -2, -1, 4]]]
 hmul := by decide
 f :=  ![![![![2, 0, 0, 0, 3], ![2, 2, 0, 0, 0]], ![![-6, 0, 0, 0, -2], ![0, 0, 0, 0, 0]]], ![![![3, 0, 0, 0, 3], ![3, 1, 0, 0, 0]], ![![-3, 0, 0, 0, -1], ![4, 1, 0, 0, 0]]]]
 g :=  ![![![![384, 321, 109, 158, -833], ![-166, 610, -16, 0, 6]], ![![-324, -270, -90, -132, 693], ![144, -510, 14, 0, -6]]], ![![![636, 531, 179, 262, -1379], ![-278, 1012, -27, 0, 9]], ![![147, 123, 42, 61, -321], ![-63, 235, -7, 0, 3]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![2, 1, -1, 0, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
