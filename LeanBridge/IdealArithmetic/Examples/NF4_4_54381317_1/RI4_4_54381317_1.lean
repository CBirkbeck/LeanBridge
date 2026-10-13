/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.Irreducible4_4_54381317_1
import LeanBridge.IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^4 - X^3 - 80*X^2 - 332*X - 383 
lemma T_def : T = X^4 - X^3 - 80*X^2 - 332*X - 383 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _ 

instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local notation "l" => [-383, -332, -80, -1, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, a^3] 

noncomputable def BQ : SubalgebraBuilderLists 4 ℤ  ℚ K T l where
 d :=  1
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]
 a := ![ ![![1, 0, 0, 0],![0, 1, 0, 0],![0, 0, 1, 0],![0, 0, 0, 1]], 
  ![![0, 1, 0, 0],![0, 0, 1, 0],![0, 0, 0, 1],![383, 332, 80, 1]], 
  ![![0, 0, 1, 0],![0, 0, 0, 1],![383, 332, 80, 1],![383, 715, 412, 81]], 
  ![![0, 0, 0, 1],![383, 332, 80, 1],![383, 715, 412, 81],![31023, 27275, 7195, 493]]]
 s := ![![[], [], [], []],![[], [], [], [-1]],![[], [], [-1], [-1, -1]],![[], [-1], [-1, -1], [-81, -1, -1]]]
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
 ![[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [383, 332, 80, 1]], 
 ![[0, 0, 1, 0], [0, 0, 0, 1], [383, 332, 80, 1], [383, 715, 412, 81]], 
 ![[0, 0, 0, 1], [383, 332, 80, 1], [383, 715, 412, 81], [31023, 27275, 7195, 493]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0] [] (by decide)

instance hp17: Fact $ Nat.Prime 17 := fact_iff.2 (by norm_num)
instance hp61: Fact $ Nat.Prime 61 := fact_iff.2 (by norm_num)
instance hp229: Fact $ Nat.Prime 229 := fact_iff.2 (by norm_num)

def CD17: CertificateDedekindCriterionLists l 17 where
 n :=  2
 a' := [4]
 b' :=  [13, 10]
 k := [13, 2, 1]
 f := [25, 24, 9, 1]
 g :=  [6, 10, 9, 1]
 h :=  [7, 1]
 a :=  [5, 15, 8]
 b :=  [2, 2, 9]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

def CD61: CertificateDedekindCriterionLists l 61 where
 n :=  2
 a' := [19, 60]
 b' :=  [35, 8, 41]
 k := [35, 15, 1]
 f := [28, 38, 8, 1]
 g :=  [25, 37, 7, 1]
 h :=  [53, 1]
 a :=  [13, 21, 37]
 b :=  [5, 3, 24]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

def CD229: CertificateDedekindCriterionLists l 229 where
 n :=  2
 a' := [42]
 b' :=  [177, 208]
 k := [1]
 f := [48, 104, 58, 1]
 g :=  [103, 114, 1]
 h :=  [103, 114, 1]
 a :=  [95, 203]
 b :=  [38, 52, 26]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
 n := 3
 p := ![17, 61, 229]
 exp := ![1, 1, 2]
 pdgood := [17, 61, 229]
 hsub := by decide
 hp := by
  intro i ; fin_cases i 
  exact hp17.out
  exact hp61.out
  exact hp229.out
 a := [44221045, 5571112, -1520560]
 b := [-51177836, -25983943, -1487813, 380140]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17
  exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61
  exact satisfiesDedekindCriterion_of_certificate_lists T l 229 T_ofList CD229


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


