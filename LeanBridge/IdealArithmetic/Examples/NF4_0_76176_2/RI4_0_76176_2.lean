/-
Copyright (c) 2025 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import LeanBridge.IdealArithmetic.Examples.NF4_0_76176_2.Irreducible4_0_76176_2
import LeanBridge.IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^4 - 2*X^3 + 7*X^2 - 6*X + 78 
lemma T_def : T = X^4 - 2*X^3 + 7*X^2 - 6*X + 78 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _ 

instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local notation "l" => [78, -6, 7, -2, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/35*a^3 + 16/35*a^2 + 3/7*a - 16/35] 

noncomputable def BQ : SubalgebraBuilderLists 4 ℤ  ℚ K T l where
 d :=  35
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![35, 0, 0, 0], ![0, 35, 0, 0], ![0, 0, 35, 0], ![-16, 15, 16, 1]]
 a := ![ ![![1, 0, 0, 0],![0, 1, 0, 0],![0, 0, 1, 0],![0, 0, 0, 1]], 
  ![![0, 1, 0, 0],![0, 0, 1, 0],![16, -15, -16, 35],![6, -8, -8, 18]], 
  ![![0, 0, 1, 0],![16, -15, -16, 35],![-46, -24, -39, 70],![-20, -18, -24, 44]], 
  ![![0, 0, 0, 1],![6, -8, -8, 18],![-20, -18, -24, 44],![-10, -12, -14, 26]]]
 s := ![![[], [], [], []],![[], [], [], [-35]],![[], [], [-1225], [-630, -35]],![[], [-35], [-630, -35], [-347, -34, -1]]]
 h := Adj
 honed := by decide
 hd := by norm_num
 hcc := by decide 
 hin := by decide
 hsymma := by decide
 hc_le := by decide 

lemma T_degree : T.natDegree = 4 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B' : Basis (Fin 4) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 4) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ 

noncomputable def B : Basis (Fin 4) ℤ O := timesTableO.basis 

def Table : Fin 4 → Fin 4 → List ℤ := 
 ![ ![[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], 
 ![[0, 1, 0, 0], [0, 0, 1, 0], [16, -15, -16, 35], [6, -8, -8, 18]], 
 ![[0, 0, 1, 0], [16, -15, -16, 35], [-46, -24, -39, 70], [-20, -18, -24, 44]], 
 ![[0, 0, 0, 1], [6, -8, -8, 18], [-20, -18, -24, 44], [-10, -12, -14, 26]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0] [] (by decide)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)
instance hp23: Fact $ Nat.Prime 23 := fact_iff.2 (by norm_num)

def CD2: CertificateDedekindCriterionLists l 2 where
 n :=  2
 a' := []
 b' :=  [1]
 k := [1]
 f := [-39, 3, -3, 2]
 g :=  [0, 1, 1]
 h :=  [0, 1, 1]
 a :=  [1]
 b :=  [1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

def CD3: CertificateDedekindCriterionLists l 3 where
 n :=  2
 a' := [2]
 b' :=  [2, 2]
 k := [1]
 f := [-26, 2, -1, 2]
 g :=  [0, 2, 1]
 h :=  [0, 2, 1]
 a :=  [1]
 b :=  [2, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

def CD23: CertificateDedekindCriterionLists l 23 where
 n :=  2
 a' := [15]
 b' :=  [21, 4]
 k := [1]
 f := [-3, 6, 21, 2]
 g :=  [3, 22, 1]
 h :=  [3, 22, 1]
 a :=  [15]
 b :=  [0, 16]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [5, 7] where
 n := 5
 p := ![2, 3, 5, 7, 23]
 exp := ![4, 2, 2, 2, 2]
 pdgood := [2, 3, 23]
 hsub := by decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp7.out
  exact hp23.out
 a := [1206672, 48576, -48576]
 b := [134136, -262200, -18216, 12144]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  exact satisfiesDedekindCriterion_of_certificate_lists T l 23 T_ofList CD23

noncomputable def M5 : MaximalOrderCertificateOfUnramifiedLists 5 O Om hm where
 n := 4
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], 
  ![[0, 1, 0, 0], [0, 0, 1, 0], [1, 0, 4, 0], [1, 2, 2, 3]], 
  ![[0, 0, 1, 0], [1, 0, 4, 0], [4, 1, 1, 0], [0, 2, 1, 4]], 
  ![[0, 0, 0, 1], [1, 2, 2, 3], [0, 2, 1, 4], [0, 3, 1, 1]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0],![1, 4, 0, 0],![1, 3, 1, 0],![0, 4, 1, 4]]
 wFrob := ![![1, 0, 0, 0],![0, 1, 0, 0],![0, 0, 1, 0],![0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3]
 hindw := by decide
 hwFrobComp := by decide 
noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
 n := 4
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], 
  ![[0, 1, 0, 0], [0, 0, 1, 0], [2, 6, 5, 0], [6, 6, 6, 4]], 
  ![[0, 0, 1, 0], [2, 6, 5, 0], [3, 4, 3, 0], [1, 3, 4, 2]], 
  ![[0, 0, 0, 1], [6, 6, 6, 4], [1, 3, 4, 2], [4, 2, 0, 5]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0],![1, 6, 0, 0],![1, 5, 1, 0],![0, 6, 1, 6]]
 wFrob := ![![1, 0, 0, 0],![0, 1, 0, 0],![0, 0, 1, 0],![0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3]
 hindw := by decide
 hwFrobComp := by decide 

open BigOperators Classical Matrix Polynomial

lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ

lemma B_one_repr : B.equivFun.symm ![1, 0, 0, 0] = 1 := by
  rw [Basis.equivFun_symm_eq_repr_symm']
  apply_fun B.repr
  rw [← B_one]
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination, Fin.isValue, Basis.repr_self]
  ext i
  fin_cases i <;> norm_num
  · exact LinearEquiv.injective B.repr 

lemma B_int_repr {n : ℤ} : B.equivFun.symm ![n, 0,0,0] = n := by
  suffices B.equivFun.symm ![n, 0,0,0] = n • 1 by convert this ; simp only [zsmul_eq_mul,mul_one]
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


