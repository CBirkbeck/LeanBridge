/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import LeanBridge.IdealArithmetic.Examples.NF3_1_24843_1.Irreducible3_1_24843_1
import LeanBridge.IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^3 - 91 
lemma T_def : T = X^3 - 91 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _ 

instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local notation "l" => [-91, 0, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, 1/3*a^2 + 1/3*a + 1/3] 

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d :=  3
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![3, 0, 0], ![0, 3, 0], ![1, 1, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]], 
  ![![0, 1, 0],![-1, -1, 3],![30, 0, 1]], 
  ![![0, 0, 1],![30, 0, 1],![20, 10, 1]]]
 s := ![![[], [], []],![[], [], [-3]],![[], [-3], [-2, -1]]]
 h := Adj
 honed := by decide
 hd := by norm_num
 hcc := by decide 
 hin := by decide
 hsymma := by decide
 hc_le := by decide 

lemma T_degree : T.natDegree = 3 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B' : Basis (Fin 3) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 3) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ 

noncomputable def B : Basis (Fin 3) ℤ O := timesTableO.basis 

def Table : Fin 3 → Fin 3 → List ℤ := 
 ![ ![[1, 0, 0], [0, 1, 0], [0, 0, 1]], 
 ![[0, 1, 0], [-1, -1, 3], [30, 0, 1]], 
 ![[0, 0, 1], [30, 0, 1], [20, 10, 1]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)

instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp13: Fact $ Nat.Prime 13 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)

def CD7: CertificateDedekindCriterionLists l 7 where
 n :=  3
 a' := []
 b' :=  [1]
 k := [1]
 f := [13]
 g :=  [0, 1]
 h :=  [0, 0, 1]
 a :=  [6]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

def CD13: CertificateDedekindCriterionLists l 13 where
 n :=  3
 a' := []
 b' :=  [1]
 k := [1]
 f := [7]
 g :=  [0, 1]
 h :=  [0, 0, 1]
 a :=  [2]
 b :=  []
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
 n := 3
 p := ![3, 7, 13]
 exp := ![3, 2, 2]
 pdgood := [7, 13]
 hsub := by decide
 hp := by
  intro i ; fin_cases i 
  exact hp3.out
  exact hp7.out
  exact hp13.out
 a := [-2457]
 b := [0, 819]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
  exact satisfiesDedekindCriterion_of_certificate_lists T l 13 T_ofList CD13

noncomputable def M3 : MaximalOrderCertificateLists 3 O Om hm where
 m := 1
 n := 2
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0], [0, 1, 0], [0, 0, 1]], 
  ![[0, 1, 0], [2, 2, 0], [0, 0, 1]], 
  ![[0, 0, 1], [0, 0, 1], [2, 1, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 2, 0]]
 b2 := ![![1, 0, 0],![1, 0, 1]]
 v := ![![1, 2, 0]]
 w := ![![1, 0, 0],![1, 0, 1]]
 wFrob := ![![1, 0, 0],![0, 1, 1]]
 v_ind := ![0]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![0, 2, 2],![1, 2, 0],![1, 2, 2]]
 a := ![![![-1]],![![0]],![![0]]]
 c := ![![![33, 6]],![![-5, 4]],![![33, 6]]]
 d := ![![![3],![33]],![![3],![3]],![![3],![33]]]
 e := ![![![-3, 2],![83, 6]],![![0, 0],![57, 3]],![![-2, 2],![83, 7]]]
 ab_ind := ![(Sum.inl 0, Sum.inl 0),(Sum.inl 0, Sum.inr 0),(Sum.inr 0, Sum.inr 0)]
 hindab := by decide
 hmul1 := by decide
 hmul2 := by decide
            

open BigOperators Classical Matrix Polynomial

lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ

lemma B_one_repr : B.equivFun.symm ![1, 0, 0] = 1 := by
  rw [Basis.equivFun_symm_eq_repr_symm']
  apply_fun B.repr
  rw [← B_one]
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination, Fin.isValue, Basis.repr_self]
  ext i
  fin_cases i <;> norm_num
  · exact LinearEquiv.injective B.repr 

lemma B_int_repr {n : ℤ} : B.equivFun.symm ![n, 0,0] = n := by
  suffices B.equivFun.symm ![n, 0,0] = n • 1 by convert this ; simp only [zsmul_eq_mul,mul_one]
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


