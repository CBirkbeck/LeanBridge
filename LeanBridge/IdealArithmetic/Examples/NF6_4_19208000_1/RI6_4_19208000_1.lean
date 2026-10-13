/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import LeanBridge.IdealArithmetic.Examples.NF6_4_19208000_1.Irreducible6_4_19208000_1
import LeanBridge.IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^6 - 5*X^4 - 50*X^2 + 125
lemma T_def : T = X^6 - 5*X^4 - 50*X^2 + 125 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local notation "l" => [125, 0, -50, 0, -5, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, 1/5*a^2, 1/5*a^3, 1/25*a^4, 1/25*a^5] 

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ  ℚ K T l where
 d := 25
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![25, 0, 0, 0, 0, 0], ![0, 25, 0, 0, 0, 0], ![0, 0, 5, 0, 0, 0], ![0, 0, 0, 5, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
 a := ![ ![![1, 0, 0, 0, 0, 0],![0, 1, 0, 0, 0, 0],![0, 0, 1, 0, 0, 0],![0, 0, 0, 1, 0, 0],![0, 0, 0, 0, 1, 0],![0, 0, 0, 0, 0, 1]], 
  ![![0, 1, 0, 0, 0, 0],![0, 0, 5, 0, 0, 0],![0, 0, 0, 1, 0, 0],![0, 0, 0, 0, 5, 0],![0, 0, 0, 0, 0, 1],![-5, 0, 10, 0, 5, 0]], 
  ![![0, 0, 1, 0, 0, 0],![0, 0, 0, 1, 0, 0],![0, 0, 0, 0, 1, 0],![0, 0, 0, 0, 0, 1],![-1, 0, 2, 0, 1, 0],![0, -1, 0, 2, 0, 1]], 
  ![![0, 0, 0, 1, 0, 0],![0, 0, 0, 0, 5, 0],![0, 0, 0, 0, 0, 1],![-5, 0, 10, 0, 5, 0],![0, -1, 0, 2, 0, 1],![-5, 0, 5, 0, 15, 0]], 
  ![![0, 0, 0, 0, 1, 0],![0, 0, 0, 0, 0, 1],![-1, 0, 2, 0, 1, 0],![0, -1, 0, 2, 0, 1],![-1, 0, 1, 0, 3, 0],![0, -1, 0, 1, 0, 3]], 
  ![![0, 0, 0, 0, 0, 1],![-5, 0, 10, 0, 5, 0],![0, -1, 0, 2, 0, 1],![-5, 0, 5, 0, 15, 0],![0, -1, 0, 1, 0, 3],![-15, 0, 25, 0, 20, 0]]]
 s := ![![[], [], [], [], [], []],![[], [], [], [], [], [-25]],![[], [], [], [], [-5], [0, -5]],![[], [], [], [-25], [0, -5], [-25, 0, -5]],![[], [], [-5], [0, -5], [-5, 0, -1], [0, -5, 0, -1]],![[], [-25], [0, -5], [-25, 0, -5], [0, -5, 0, -1], [-75, 0, -5, 0, -1]]]
 h := Adj
 honed := by decide
 hd := by norm_num
 hcc := by decide
 hin := by decide
 hsymma := by decide
 hc_le := by decide 

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ

noncomputable def B : Basis (Fin 6) ℤ O := timesTableO.basis
def Table : Fin 6 → Fin 6 → List ℤ := 
 ![ ![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], 
 ![[0, 1, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 5, 0], [0, 0, 0, 0, 0, 1], [-5, 0, 10, 0, 5, 0]], 
 ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [-1, 0, 2, 0, 1, 0], [0, -1, 0, 2, 0, 1]], 
 ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 5, 0], [0, 0, 0, 0, 0, 1], [-5, 0, 10, 0, 5, 0], [0, -1, 0, 2, 0, 1], [-5, 0, 5, 0, 15, 0]], 
 ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [-1, 0, 2, 0, 1, 0], [0, -1, 0, 2, 0, 1], [-1, 0, 1, 0, 3, 0], [0, -1, 0, 1, 0, 3]], 
 ![[0, 0, 0, 0, 0, 1], [-5, 0, 10, 0, 5, 0], [0, -1, 0, 2, 0, 1], [-5, 0, 5, 0, 15, 0], [0, -1, 0, 1, 0, 3], [-15, 0, 25, 0, 20, 0]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)

def CD2: CertificateDedekindCriterionLists l 2 where
 n := 2
 a' := [1]
 b' := [1, 1]
 k := [1]
 f := [-62, 0, 26, 1, 3, 1]
 g := [1, 0, 1, 1]
 h := [1, 0, 1, 1]
 a := [1]
 b := [1, 0, 1]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD7: CertificateDedekindCriterionLists l 7 where
 n := 3
 a' := [5]
 b' := [0, 1]
 k := [1]
 f := [-17, 0, 10, 0, 2]
 g := [3, 0, 1]
 h := [2, 0, 6, 0, 1]
 a := [6]
 b := [4, 0, 2]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [5] where
 n := 3
 p := ![2, 5, 7]
 exp := ![6, 15, 4]
 pdgood := [2, 7]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp5.out
  exact hp7.out
 a := [37515625000000, 0, 0, 0, -1929375000000]
 b := [0, -18757812500000, 0, -535937500000, 0, 321562500000]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
  exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7

noncomputable def M5 : MaximalOrderCertificateWLists 5 O Om hm where
 m := 3
 n := 3
 t := 2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], 
  ![[0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0]], 
  ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [4, 0, 2, 0, 1, 0], [0, 4, 0, 2, 0, 1]], 
  ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0], [0, 4, 0, 2, 0, 1], [0, 0, 0, 0, 0, 0]], 
  ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [4, 0, 2, 0, 1, 0], [0, 4, 0, 2, 0, 1], [4, 0, 1, 0, 3, 0], [0, 4, 0, 1, 0, 3]], 
  ![[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0], [0, 4, 0, 2, 0, 1], [0, 0, 0, 0, 0, 0], [0, 4, 0, 1, 0, 3], [0, 0, 0, 0, 0, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 0, 0, 0],![0, 0, 0, 1, 0, 0],![0, 0, 0, 0, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0, 0],![2, 0, 0, 0, 4, 0],![3, 0, 1, 0, 4, 0]]
 v := ![![0, 1, 0, 0, 0, 0],![0, 0, 0, 1, 0, 0],![0, 0, 0, 0, 0, 1]]
 w := ![![1, 0, 0, 0, 0, 0],![2, 0, 0, 0, 4, 0],![3, 0, 1, 0, 4, 0]]
 wFrob := ![![1, 0, 0, 0, 0, 0],![0, 0, 1, 0, 0, 0],![0, 0, 0, 0, 1, 0]]
 v_ind := ![1, 3, 5]
 w_ind := ![0, 2, 4]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![2, 0, 6, 0, 4, 2],![6, 8, 0, 4, 0, 2],![0, 4, 3, 1, 0, 3],![0, 0, 0, 6, 0, 8],![0, 2, 0, 1, 0, 3],![0, 6, 0, 4, 0, 8]]
 w1 := ![0, 2, 0]
 w2 := ![0, 1, 0]
 a := ![![-48, 60, 160],![-40, 252, 380],![-40, 110, 316],![-280, 460, 680],![-60, 110, 270],![-180, 360, 760]]
 c := ![![-170, -55, 80],![-50, -5, 20],![-80, -30, 40],![-98, -25, 40],![-30, -4, 10],![-90, -15, 32]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 


open BigOperators Classical Matrix Polynomial

lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ

lemma B_one_repr : B.equivFun.symm ![1, 0, 0, 0, 0, 0] = 1 := by
  rw [Basis.equivFun_symm_eq_repr_symm']
  apply_fun B.repr
  rw [← B_one]
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination, Fin.isValue, Basis.repr_self]
  ext i
  fin_cases i <;> norm_num
  · exact LinearEquiv.injective B.repr

lemma B_int_repr {n : ℤ} : B.equivFun.symm ![n, 0,0,0,0,0] = n := by
  suffices B.equivFun.symm ![n, 0,0,0,0,0] = n • 1 by convert this ; simp only [zsmul_eq_mul,mul_one]
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

 noncomputable instance : Mul (Ideal ↥O) := Submodule.mul (R := O) (A := O)
 noncomputable instance  : AddCommMonoid ↥O := AddSubmonoidClass.toAddCommMonoid O
 noncomputable instance : Module ℤ O := inferInstance
 noncomputable instance  : Algebra ℤ O := O.algebra'

