/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.RI4_4_54381317_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section 


def alpha0 := B.equivFun.symm ![5, 1, 0, 0]

def alpha1 := B.equivFun.symm ![5, 2, 0, 0]

def v := B.equivFun.symm ![-1, 0, 0, 0]

def zeta1 := B.equivFun.symm ![3, 1, 0, 0]

def zeta2 := B.equivFun.symm ![-124, -67, -4, 1]

def zeta3 := B.equivFun.symm ![-173, -110, -11, 2]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![-1, 1, 0, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0, 0], ![-1, 1, 0, 0]] ![![3, 0, 0, 0], ![-1, 1, 0, 0]]
  ![![9, 0, 0, 0], ![-4, 1, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![9, 0, 0, 0], ![-3, 3, 0, 0]], ![![-3, 3, 0, 0], ![1, -2, 1, 0]]]
 hmul := by decide
 f :=  ![![![![0, 8, -7, 0], ![0, 15, 3, 0]], ![![0, 0, 0, 0], ![9, -9, 0, 0]]], ![![![0, 276, -200, 12], ![0, 449, -21, 0]], ![![0, 0, 0, 0], ![379, -46, -1, 0]]]]
 g :=  ![![![![69, -57, 14, -1], ![153, -90, 9, 0]], ![![-7, 2, -28, 7], ![-15, 0, -63, 0]]], ![![![-7, 2, -28, 7], ![-15, 0, -63, 0]], ![![5, -1, 0, 0], ![11, 1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0, 0], ![-4, 1, 0, 0]] ![![3, 0, 0, 0], ![-1, 1, 0, 0]]
  ![![5, 1, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M :=  ![![![27, 0, 0, 0], ![-9, 9, 0, 0]], ![![-12, 3, 0, 0], ![4, -5, 1, 0]]]
 hmul := by decide
 f :=  ![![![![9312, -20130, -18933, 25266], ![15132, -2703, -77944, 0]], ![![9312, -29256, 6400, 0], ![-776, 110, -1, 0]]]]
 g :=  ![![![![82, 50, 6, -1]], ![![-155, -100, -12, 2]]], ![![![-79, -50, -6, 1]], ![![154, 101, 12, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 =  Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![1, 1, 0, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0, 0], ![1, 1, 0, 0]] ![![3, 0, 0, 0], ![1, 1, 0, 0]]
  ![![9, 0, 0, 0], ![-2, 1, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![9, 0, 0, 0], ![3, 3, 0, 0]], ![![3, 3, 0, 0], ![1, 2, 1, 0]]]
 hmul := by decide
 f :=  ![![![![0, 0, 2, 1], ![0, 0, 3, 0]], ![![0, 0, 0, 0], ![9, -18, 0, 0]]], ![![![0, 0, 210, 153], ![0, 0, 122, 0]], ![![0, 0, 0, 0], ![1530, -1731, -4, 0]]]]
 g :=  ![![![![15, -5, 19, -10], ![63, 9, 90, 0]], ![![9, -10, 5, -1], ![39, -27, 9, 0]]], ![![![9, -10, 5, -1], ![39, -27, 9, 0]], ![![5, -4, 3, -1], ![22, -8, 9, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![9, 0, 0, 0], ![-2, 1, 0, 0]] ![![3, 0, 0, 0], ![1, 1, 0, 0]]
  ![![5, 2, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M :=  ![![![27, 0, 0, 0], ![9, 9, 0, 0]], ![![-6, 3, 0, 0], ![-2, -1, 1, 0]]]
 hmul := by decide
 f :=  ![![![![8370, -8652, -1677, 8944], ![-9765, -6231, -8320, 0]], ![![24552, -52392, -57856, 0], ![-6138, 6960, -8, 0]]]]
 g :=  ![![![![1231, 570, 28, -8]], ![![-611, -285, -14, 4]]], ![![![-614, -285, -14, 4]], ![![306, 143, 7, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 =  Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![128, 68, 4, -1])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-139, -67, -4, 1])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta3 : IsUnit zeta3 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-797, -359, -17, 5])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![1, 1, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0, 0], ![-2, 1, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10] 
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![-1, 1, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![3, 0, 0, 0], ![-1, 1, 0, 0]] ![![3, 0, 0, 0], ![1, 1, 0, 0]]
  ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![9, 0, 0, 0], ![3, 3, 0, 0]], ![![-3, 3, 0, 0], ![-1, 0, 1, 0]]]
 hmul := by decide
 f :=  ![![![![0, -1, 0, 0], ![1, 1, 0, 0]], ![![1, 0, 0, 0], ![-3, 0, 0, 0]]], ![![![-14, 0, -9, 0], ![19, 4, -22, 0]], ![![-23, 0, 0, 0], ![131, 67, 0, 0]]]]
 g :=  ![![![![14, 67, 16, -1], ![-105, -36, 0, 0]], ![![112, 68, 6, -1], ![-15, -6, 0, 0]]], ![![![59, 1, -6, 0], ![54, 18, 0, 0]], ![![13, 0, -1, 0], ![12, 4, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![-131, -67, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![3, 0, 0, 0], ![-1, 1, 0, 0]] ![![9, 0, 0, 0], ![-2, 1, 0, 0]]
  ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M :=  ![![![27, 0, 0, 0], ![-6, 3, 0, 0]], ![![-9, 9, 0, 0], ![2, -3, 1, 0]]]
 hmul := by decide
 f :=  ![![![![-72, 254, -113, 2], ![-321, 975, -18, 0]], ![![1, 0, 0, 0], ![18, 0, 0, 0]]], ![![![2779, -1461, -702, 361], ![12285, -304, -3312, 0]], ![![240, 0, 0, 0], ![558, 188, 0, 0]]]]
 g :=  ![![![![499626, -1459471, -299502, 49057], ![249228, 193221, 72, 0]], ![![-111183, 324275, 66556, -10901], ![-55379, -42938, -16, 0]]], ![![![-166914, 486366, 99834, -16351], ![-83064, -64407, -24, 0]], ![![34687, -101363, -20800, 3407], ![17309, 13419, 5, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0, 0], ![279, 94, 0, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0, 0], ![-4, 1, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00] 
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![9, 0, 0, 0], ![-4, 1, 0, 0]] ![![3, 0, 0, 0], ![1, 1, 0, 0]]
  ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M :=  ![![![27, 0, 0, 0], ![9, 9, 0, 0]], ![![-12, 3, 0, 0], ![-4, -3, 1, 0]]]
 hmul := by decide
 f :=  ![![![![101646, 21072, 105779, 108976], ![-118585, 8405, -326672, 0]], ![![139758, -288, -768, 0], ![18, 0, 0, 0]]], ![![![-4753548, -987352, -4948639, -5102992], ![5545809, -394147, 15294647, 0]], ![![-6535806, 8624, 43128, 0], ![-854, -420, 0, 0]]]]
 g :=  ![![![![-1763532, 5154885, 569790, 123960], ![-37263600, -13833405, 360, 0]], ![![-587611, 1718391, 189934, 41318], ![-12421074, -4611090, 120, 0]]], ![![![784012, -2290958, -253235, -55095], ![16561645, 6148195, -160, 0]], ![![274680, -801690, -88624, -19285], ![5796519, 2151845, -56, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0, 0], ![-427, -210, -11, 3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![9, 0, 0, 0], ![-4, 1, 0, 0]] ![![9, 0, 0, 0], ![-2, 1, 0, 0]]
  ![![9, 0, 0, 0], ![-128, -67, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M :=  ![![![81, 0, 0, 0], ![-18, 9, 0, 0]], ![![-36, 9, 0, 0], ![8, -6, 1, 0]]]
 hmul := by decide
 f :=  ![![![![2732059, -1361348, 2303435, -1151966], ![12227923, 4273, 10367742, 0]], ![![33187, 0, 0, 0], ![72, -432, 0, 0]]], ![![![-35350204, 17614418, -29809078, 14907781], ![-158217508, -55750, -134170652, 0]], ![![-429429, 0, 0, 0], ![-1024, 5608, 0, 0]]]]
 g :=  ![![![![101, 175, 40, -1], ![-963, -324, 0, 0]], ![![8, -29, -10, 0], ![270, 90, 0, 0]]], ![![![14, -53, -18, 0], ![486, 162, 0, 0]], ![![124, 81, 9, -1], ![-123, -44, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0, 0], ![-128, -67, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
