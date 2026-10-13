/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import LeanBridge.IdealArithmetic.Examples.NF2_0_231_1.Irreducible2_0_231_1
import LeanBridge.IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^2 - X + 58 
lemma T_def : T = X^2 - X + 58 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _ 

instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local notation "l" => [58, -1, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a] 

noncomputable def BQ : SubalgebraBuilderLists 2 ℤ  ℚ K T l where
 d :=  1
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![1, 0], ![0, 1]]
 a := ![ ![![1, 0],![0, 1]], 
  ![![0, 1],![-58, 1]]]
 s := ![![[], []],![[], [-1]]]
 h := Adj
 honed := by decide
 hd := by norm_num
 hcc := by decide 
 hin := by decide
 hsymma := by decide
 hc_le := by decide 

lemma T_degree : T.natDegree = 2 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B' : Basis (Fin 2) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 2) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ 

noncomputable def B : Basis (Fin 2) ℤ O := timesTableO.basis 

def Table : Fin 2 → Fin 2 → List ℤ := 
 ![ ![[1, 0], [0, 1]], 
 ![[0, 1], [-58, 1]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1] [] (by decide)

instance hp11: Fact $ Nat.Prime 11 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  2
 a' := []
 b' :=  [1]
 k := [1]
 f := [-19, 1]
 g :=  [1, 1]
 h :=  [1, 1]
 a :=  [1]
 b :=  [2]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

def CD7: CertificateDedekindCriterionLists l 7 where
 n :=  2
 a' := []
 b' :=  [1]
 k := [1]
 f := [-7, 1]
 g :=  [3, 1]
 h :=  [3, 1]
 a :=  [2]
 b :=  [5]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

def CD11: CertificateDedekindCriterionLists l 11 where
 n :=  2
 a' := []
 b' :=  [1]
 k := [1]
 f := [-3, 1]
 g :=  [5, 1]
 h :=  [5, 1]
 a :=  [4]
 b :=  [7]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
 n := 3
 p := ![3, 7, 11]
 exp := ![1, 1, 1]
 pdgood := [3, 7, 11]
 hsub := by decide
 hp := by
  intro i ; fin_cases i 
  exact hp3.out
  exact hp7.out
  exact hp11.out
 a := [4]
 b := [1, -2]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
  exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11


open BigOperators Classical Matrix Polynomial

lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ

lemma B_one_repr : B.equivFun.symm ![1, 0] = 1 := by
  rw [Basis.equivFun_symm_eq_repr_symm']
  apply_fun B.repr
  rw [← B_one]
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination, Fin.isValue, Basis.repr_self]
  ext i
  fin_cases i <;> norm_num
  · exact LinearEquiv.injective B.repr 

lemma B_int_repr {n : ℤ} : B.equivFun.symm ![n, 0] = n := by
  suffices B.equivFun.symm ![n, 0] = n • 1 by convert this ; simp only [zsmul_eq_mul,mul_one]
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


