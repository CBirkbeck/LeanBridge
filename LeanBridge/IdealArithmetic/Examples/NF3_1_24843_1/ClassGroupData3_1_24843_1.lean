/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import LeanBridge.IdealArithmetic.Examples.NF3_1_24843_1.RI3_1_24843_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section 


def alpha0 := B.equivFun.symm ![6, 1, 1]

def alpha1 := B.equivFun.symm ![5, 1, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-9, 2, 0]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![4, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0], ![2, 2, 0]], ![![2, 2, 0], ![0, 1, 3]]]
 hmul := by decide
 f :=  ![![![![0, -67, 78], ![134, -46, 0]], ![![0, 0, 0], ![-4, -4, 0]]], ![![![0, -17, 18], ![34, -11, 0]], ![![0, 0, 0], ![0, -1, 0]]]]
 g :=  ![![![![0, -1, 0], ![4, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![6, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M :=  ![![![8, 0, 0], ![4, 4, 0]], ![![2, 2, 0], ![0, 1, 3]]]
 hmul := by decide
 f :=  ![![![![0, -35, 104], ![70, 70, 0]], ![![0, -270, 0], ![-5, -6, 0]]]]
 g :=  ![![![![0, 2, -1]], ![![-16, 0, 2]]], ![![![-8, 0, 1]], ![![11, -4, 1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 =  Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 0, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0], ![0, 0, 1]] ![![3, 0, 0], ![0, 0, 1]]
  ![![3, 0, 0], ![-1, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![9, 0, 0], ![0, 0, 3]], ![![0, 0, 3], ![20, 10, 1]]]
 hmul := by decide
 f :=  ![![![![377, 39190, 7084], ![-17262, 7817, -11221]], ![![0, 0, 0], ![-1603, 0, -5]]], ![![![-159, -15671, -2834], ![6906, -3125, 4487]], ![![0, 0, 0], ![641, 0, 2]]]]
 g :=  ![![![![3, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0]]], ![![![0, 0, 1], ![0, 0, 0]], ![![7, 3, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![3, 0, 0], ![-1, 1, 1]] ![![3, 0, 0], ![0, 0, 1]]
  ![![5, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M :=  ![![![9, 0, 0], ![0, 0, 3]], ![![-3, 3, 3], ![50, 10, 1]]]
 hmul := by decide
 f :=  ![![![![-5, 289, 52], ![-129, 60, -85]], ![![0, 0, 0], ![-5, 0, 0]]]]
 g :=  ![![![![-4, 1, 0]], ![![10, 0, -1]]], ![![![11, -2, 0]], ![![-20, 0, 3]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 =  Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-77, -14, -12])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10] 
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![0, 0, 1]]
  ![![6, 0, 0], ![3, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![6, 0, 0], ![0, 0, 2]], ![![3, 3, 0], ![30, 0, 2]]]
 hmul := by decide
 f :=  ![![![![34, 1118, 52], ![-284, 215, -312]], ![![-156, 50, 0], ![0, 0, 0]]], ![![![12, 559, 26], ![-142, 108, -156]], ![![-78, 25, 0], ![0, 0, 0]]]]
 g :=  ![![![![21, 8, 10], ![-40, 4, -6]], ![![-1, 0, 0], ![2, 0, 0]]], ![![![9, 4, 6], ![-27, 3, -3]], ![![146, 42, 58], ![-242, 16, -30]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![3, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![-1, 1, 1]]
  ![![6, 0, 0], ![2, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M :=  ![![![6, 0, 0], ![-2, 2, 2]], ![![3, 3, 0], ![28, -1, 5]]]
 hmul := by decide
 f :=  ![![![![96, 86, -67], ![-24, 0, 0]], ![![-156, 50, 0], ![0, 0, 0]]], ![![![29, 26, -20], ![-7, 0, 0]], ![![-47, 15, 0], ![0, 0, 0]]]]
 g :=  ![![![![-12, -2, -3], ![10, 2, 0]], ![![-1, 0, 0], ![2, 0, 0]]], ![![![-5, 0, -1], ![2, 1, 0]], ![![-16, -6, -6], ![33, 2, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![2, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00] 
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![0, 0, 1]]
  ![![12, 0, 0], ![-3, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M :=  ![![![12, 0, 0], ![0, 0, 4]], ![![3, 3, 0], ![30, 0, 2]]]
 hmul := by decide
 f :=  ![![![![-8, -4984, -1104], ![2413, -940, 1344]], ![![2016, 220, 0], ![0, 0, 0]]], ![![![-8, 1246, 276], ![-604, 236, -336]], ![![-504, -55, 0], ![0, 0, 0]]]]
 g :=  ![![![![-14, 11, 6], ![-100, 4, -12]], ![![1, 0, 0], ![4, 0, 0]]], ![![![-5, 3, 2], ![-31, 1, -3]], ![![-38, 27, 18], ![-282, 8, -30]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0], ![-3, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![-1, 1, 1]]
  ![![12, 0, 0], ![2, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M :=  ![![![12, 0, 0], ![-4, 4, 4]], ![![3, 3, 0], ![28, -1, 5]]]
 hmul := by decide
 f :=  ![![![![-466, -486, -147], ![-54, 0, 0]], ![![2016, 220, 0], ![0, 0, 0]]], ![![![-70, -73, -22], ![-8, 0, 0]], ![![303, 33, 0], ![0, 0, 0]]]]
 g :=  ![![![![100, 54, 53], ![-652, 4, 0]], ![![-50, -20, -21], ![240, 4, 0]]], ![![![17, 12, 11], ![-144, 3, 0]], ![![254, 128, 128], ![-1539, 2, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0], ![2, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
