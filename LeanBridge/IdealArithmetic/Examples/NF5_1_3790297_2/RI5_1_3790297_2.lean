/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import LeanBridge.IdealArithmetic.Examples.NF5_1_3790297_2.Irreducible5_1_3790297_2
import LeanBridge.IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - X^4 + 3*X^2 + 21*X + 4 
lemma T_def : T = X^5 - X^4 + 3*X^2 + 21*X + 4 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _ 

instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local notation "l" => [4, 21, 3, 0, -1, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, a^3, 1/16*a^4 + 1/8*a^3 + 3/8*a^2 + 5/16*a + 1/4] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  16
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![16, 0, 0, 0, 0], ![0, 16, 0, 0, 0], ![0, 0, 16, 0, 0], ![0, 0, 0, 16, 0], ![4, 5, 6, 2, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
  ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![-4, -5, -6, -2, 16],![-1, -2, -1, 0, 3]], 
  ![![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![-4, -5, -6, -2, 16],![-8, -26, -9, -2, 16],![-3, -7, -5, -1, 9]], 
  ![![0, 0, 0, 1, 0],![-4, -5, -6, -2, 16],![-8, -26, -9, -2, 16],![-8, -30, -30, -5, 16],![-5, -16, -10, -3, 11]], 
  ![![0, 0, 0, 0, 1],![-1, -2, -1, 0, 3],![-3, -7, -5, -1, 9],![-5, -16, -10, -3, 11],![-2, -6, -4, -1, 5]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-16]],![[], [], [], [-256], [-48, -16]],![[], [], [-256], [-256, -256], [-144, -48, -16]],![[], [-16], [-48, -16], [-144, -48, -16], [-52, -21, -5, -1]]]
 h := Adj
 honed := by decide
 hd := by norm_num
 hcc := by decide 
 hin := by decide
 hsymma := by decide
 hc_le := by decide 

lemma T_degree : T.natDegree = 5 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B' : Basis (Fin 5) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 5) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ 

noncomputable def B : Basis (Fin 5) ℤ O := timesTableO.basis 

def Table : Fin 5 → Fin 5 → List ℤ := 
 ![ ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [-4, -5, -6, -2, 16], [-1, -2, -1, 0, 3]], 
 ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [-4, -5, -6, -2, 16], [-8, -26, -9, -2, 16], [-3, -7, -5, -1, 9]], 
 ![[0, 0, 0, 1, 0], [-4, -5, -6, -2, 16], [-8, -26, -9, -2, 16], [-8, -30, -30, -5, 16], [-5, -16, -10, -3, 11]], 
 ![[0, 0, 0, 0, 1], [-1, -2, -1, 0, 3], [-3, -7, -5, -1, 9], [-5, -16, -10, -3, 11], [-2, -6, -4, -1, 5]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp751: Fact $ Nat.Prime 751 := fact_iff.2 (by norm_num)
instance hp103: Fact $ Nat.Prime 103 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)

def CD7: CertificateDedekindCriterionLists l 7 where
 n :=  3
 a' := [6, 2]
 b' :=  [5, 4, 4]
 k := [2, 5, 3, 4, 1]
 f := [0, 0, 1, 1, 1]
 g :=  [4, 1, 1, 1]
 h :=  [1, 5, 1]
 a :=  [4, 4, 4]
 b :=  [2, 3, 3, 3]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

def CD103: CertificateDedekindCriterionLists l 103 where
 n :=  2
 a' := [25, 71, 16]
 b' :=  [19, 61, 84, 99]
 k := [72, 30, 55, 1]
 f := [32, 41, 26, 20, 1]
 g :=  [44, 56, 35, 27, 1]
 h :=  [75, 1]
 a :=  [11, 37, 87, 93]
 b :=  [88, 3, 49, 10]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

def CD751: CertificateDedekindCriterionLists l 751 where
 n :=  2
 a' := [225, 476, 376]
 b' :=  [286, 745, 398, 657]
 k := [688, 614, 708, 1]
 f := [5, 2, 13, 21, 1]
 g :=  [179, 64, 462, 729, 1]
 h :=  [21, 1]
 a :=  [296, 41, 634, 241]
 b :=  [684, 116, 268, 510]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
 n := 4
 p := ![2, 7, 103, 751]
 exp := ![8, 2, 1, 1]
 pdgood := [7, 103, 751]
 hsub := by decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp7.out
  exact hp103.out
  exact hp751.out
 a := [-24330362, -3662106, 16948722, -15670690]
 b := [50839880, 10502226, 908908, -4016572, 3134138]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
  exact satisfiesDedekindCriterion_of_certificate_lists T l 103 T_ofList CD103
  exact satisfiesDedekindCriterion_of_certificate_lists T l 751 T_ofList CD751

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
 n := 5
 t :=  3
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
  ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [1, 0, 1, 0, 1]], 
  ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 1, 1, 1, 1]], 
  ![[0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [1, 0, 0, 1, 1]], 
  ![[0, 0, 0, 0, 1], [1, 0, 1, 0, 1], [1, 1, 1, 1, 1], [1, 0, 0, 1, 1], [0, 0, 0, 1, 1]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 1, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by decide 

open BigOperators Classical Matrix Polynomial

lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ

lemma B_one_repr : B.equivFun.symm ![1, 0, 0, 0, 0] = 1 := by
  rw [Basis.equivFun_symm_eq_repr_symm']
  apply_fun B.repr
  rw [← B_one]
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination, Fin.isValue, Basis.repr_self]
  ext i
  fin_cases i <;> norm_num
  · exact LinearEquiv.injective B.repr 

lemma B_int_repr {n : ℤ} : B.equivFun.symm ![n, 0,0,0,0] = n := by
  suffices B.equivFun.symm ![n, 0,0,0,0] = n • 1 by convert this ; simp only [zsmul_eq_mul,mul_one]
  rw [← B_one_repr, ← LinearEquiv.map_smul]
  simp only [Basis.equivFun_symm_apply, zsmul_eq_mul, Matrix.smul_cons, smul_eq_mul, mul_one,
    mul_zero, Matrix.smul_empty]

instance : IsDomain O := by
  haveI hirr : Fact $ Irreducible (map (algebraMap ℤ ℚ) T) :=
  {out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible}
  letI hola : Field K := by
    unfold K
    exact AdjoinRoot.instField
  haveI : IsDomain K := by infer_instance
  refine Subalgebra.isDomain O 

--  We add these shortcuts for faster typeclass inference  
 noncomputable instance : Mul (Ideal ↥O) := Submodule.mul (R := O) (A := O)
 noncomputable instance  : AddCommMonoid ↥O := AddSubmonoidClass.toAddCommMonoid O
 noncomputable instance : Module ℤ O := inferInstance
 noncomputable instance  : Algebra ℤ O := O.algebra'  


