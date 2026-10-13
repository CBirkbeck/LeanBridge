/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import LeanBridge.IdealArithmetic.Examples.NF2_0_231_1.RI2_0_231_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section 


def alpha0 := B.equivFun.symm ![3, -1]

def alpha1 := B.equivFun.symm ![7, 0]

def v := B.equivFun.symm ![-1, 0]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0], ![1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0], ![1, 1]] ![![2, 0], ![1, 1]]
  ![![4, 0], ![1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0], ![2, 2]], ![![2, 2], ![-57, 3]]]
 hmul := by decide
 f :=  ![![![![48, -13], ![20, 0]], ![![0, 0], ![4, 0]]], ![![![12, -3], ![5, 0]], ![![0, 0], ![1, 0]]]]
 g :=  ![![![![0, -1], ![4, 0]], ![![0, 0], ![2, 0]]], ![![![0, 0], ![2, 0]], ![![-14, 1], ![-1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0], ![1, 1]] ![![2, 0], ![1, 1]]
  ![![8, 0], ![5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M :=  ![![![8, 0], ![4, 4]], ![![2, 2], ![-57, 3]]]
 hmul := by decide
 f :=  ![![![![30, -31], ![32, 0]], ![![48, 0], ![8, 0]]], ![![![18, -20], ![22, 0]], ![![29, 0], ![5, 0]]]]
 g :=  ![![![![-4, -1], ![8, 0]], ![![-2, 0], ![4, 0]]], ![![![-1, 0], ![2, 0]], ![![-9, 0], ![3, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0], ![5, 1]] ![![2, 0], ![1, 1]]
  ![![16, 0], ![13, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M :=  ![![![16, 0], ![8, 8]], ![![10, 2], ![-53, 7]]]
 hmul := by decide
 f :=  ![![![![1558, -15], ![772, 0]], ![![-3024, 0], ![16, 0]]], ![![![1266, -12], ![627, 0]], ![![-2457, 0], ![13, 0]]]]
 g :=  ![![![![-12, -1], ![16, 0]], ![![-6, 0], ![8, 0]]], ![![![-1, 0], ![2, 0]], ![![-9, 0], ![7, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![16, 0], ![13, 1]] ![![2, 0], ![1, 1]]
  ![![32, 0], ![29, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M :=  ![![![32, 0], ![16, 16]], ![![26, 2], ![-45, 15]]]
 hmul := by decide
 f :=  ![![![![1512, -205], ![656, 0]], ![![-2208, 0], ![32, 0]]], ![![![1371, -185], ![593, 0]], ![![-2001, 0], ![29, 0]]]]
 g :=  ![![![![-28, -1], ![32, 0]], ![![-14, 0], ![16, 0]]], ![![![-1, 0], ![2, 0]], ![![-15, 0], ![15, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![32, 0], ![29, 1]] ![![2, 0], ![1, 1]]
  ![![3, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M :=  ![![![64, 0], ![32, 32]], ![![58, 2], ![-29, 31]]]
 hmul := by decide
 f :=  ![![![![912, -154], ![381, 0]], ![![-1215, 0], ![3, 0]]]]
 g :=  ![![![![2, 1]], ![![-28, 2]]], ![![![0, 1]], ![![-29, 1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 =  Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0], ![3, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![7, 0], ![3, 1]] ![![7, 0], ![3, 1]]
  ![![7, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![49, 0], ![21, 7]], ![![21, 7], ![-49, 7]]]
 hmul := by decide
 f :=  ![![![![205, -46], ![82, 0]], ![![0, 0], ![240, 0]]]]
 g :=  ![![![![7, 0]], ![![3, 1]]], ![![![3, 1]], ![![-7, 1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 =  Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0], ![3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0], ![1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0], ![1, 1]] ![![7, 0], ![3, 1]]
  ![![14, 0], ![3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![14, 0], ![6, 2]], ![![7, 7], ![-55, 5]]]
 hmul := by decide
 f :=  ![![![![5, 6], ![7, 0]], ![![-14, 0], ![0, 0]]], ![![![0, 1], ![4, 0]], ![![-3, 0], ![0, 0]]]]
 g :=  ![![![![-2, -1], ![14, 0]], ![![0, 0], ![2, 0]]], ![![![-1, 0], ![7, 0]], ![![-5, 0], ![5, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![14, 0], ![3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0], ![1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00] 
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0], ![1, 1]] ![![7, 0], ![3, 1]]
  ![![28, 0], ![17, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M :=  ![![![28, 0], ![12, 4]], ![![7, 7], ![-55, 5]]]
 hmul := by decide
 f :=  ![![![![5, 6], ![7, 0]], ![![-28, 0], ![0, 0]]], ![![![1, 3], ![9, 0]], ![![-17, 0], ![0, 0]]]]
 g :=  ![![![![-16, -1], ![28, 0]], ![![-2, 0], ![4, 0]]], ![![![-4, 0], ![7, 0]], ![![-5, 0], ![5, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![28, 0], ![17, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0], ![5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01] 
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![8, 0], ![5, 1]] ![![7, 0], ![3, 1]]
  ![![56, 0], ![45, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M :=  ![![![56, 0], ![24, 8]], ![![35, 7], ![-43, 9]]]
 hmul := by decide
 f :=  ![![![![146, 25], ![70, 0]], ![![-280, 0], ![0, 0]]], ![![![117, 20], ![57, 0]], ![![-225, 0], ![0, 0]]]]
 g :=  ![![![![-44, -1], ![56, 0]], ![![-6, 0], ![8, 0]]], ![![![-5, 0], ![7, 0]], ![![-8, 0], ![9, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![56, 0], ![45, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0], ![13, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02] 
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![16, 0], ![13, 1]] ![![7, 0], ![3, 1]]
  ![![112, 0], ![45, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M :=  ![![![112, 0], ![48, 16]], ![![91, 7], ![-19, 17]]]
 hmul := by decide
 f :=  ![![![![998, 29], ![434, 0]], ![![-1456, 0], ![0, 0]]], ![![![399, 11], ![179, 0]], ![![-585, 0], ![0, 0]]]]
 g :=  ![![![![-44, -1], ![112, 0]], ![![-6, 0], ![16, 0]]], ![![![-2, 0], ![7, 0]], ![![-7, 0], ![17, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![112, 0], ![45, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0], ![29, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03] 
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![32, 0], ![29, 1]] ![![7, 0], ![3, 1]]
  ![![224, 0], ![157, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M :=  ![![![224, 0], ![96, 32]], ![![203, 7], ![29, 33]]]
 hmul := by decide
 f :=  ![![![![4979, -100], ![2121, 0]], ![![-6496, 0], ![0, 0]]], ![![![3490, -70], ![1486, 0]], ![![-4553, 0], ![0, 0]]]]
 g :=  ![![![![-156, -1], ![224, 0]], ![![-22, 0], ![32, 0]]], ![![![-4, 0], ![7, 0]], ![![-23, 0], ![33, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![224, 0], ![157, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
