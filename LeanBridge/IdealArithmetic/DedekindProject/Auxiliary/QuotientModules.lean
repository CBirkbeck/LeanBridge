/-
Copyright (c) 2024 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
--import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/- !

# Index of modules over PIDs

For a finite and free module over a PID, we define the index of a submodule and prove
some of its properties.

## Main Definitions:
- `Submodule.indexPID`: The index of a submodule.

## Main Results:
- `Submodule.eq_top_of_index_isUnit` : if the index is a unit, then the submodule is maximal.
- `prod_moduleSmithCoeffs_associated_index` : The index is associated to the product of the Smith
  coefficients corresponding to the inclusion map.
- `Submodule.prime_dvd_index` : a consequence of a prime dividing the index of a submodule.
- `indexPID_eq_index_int` : in the case of `ℤ`-modules, the absolute value of the index is equal to
  the cardinality of the quotient.

## Notes
- For some of the results, we closely followed an approach
  adapted from the proofs involving quotients by ideals such as
  `Ideal.quotientEquivPiZMod`.  -/

open scoped BigOperators

open scoped Classical

open Module

/- Here we prove that the quotient of free `ℤ`-modules of the same rank is finite· The proof
is essentially the same as that of `Ideal.quotientEquivDirectSum`, which was written by Anne Baanen.
-/
variable {ι ι' R M : Type _} [CommRing R] [AddCommGroup M] [Module R M]

variable [IsDomain R] [IsPrincipalIdealRing R] [Fintype ι] [Fintype ι']

/-- For `N` a submodule of a free and finite module `M` of the same rank,
  we extract a basis for `N` of cardinality the rank of `M`-/
noncomputable def Submodule.basisOfPID_of_eq_rank  (N : Submodule R M) [Module.Free R M] [Module.Finite R M]
    (heq : Module.rank R M = Module.rank R N) : Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex R M))) R N := by
  let B := Basis.reindex (Module.Free.chooseBasis R M) (Fintype.equivFin (Module.Free.ChooseBasisIndex R M))
  obtain ⟨n,b⟩ :=  Submodule.basisOfPid B N
  rw [rank_eq_card_basis (Module.Free.chooseBasis R M), rank_eq_card_basis b, Nat.cast_inj, Fintype.card_fin] at heq
  rw [← heq] at b
  exact b

noncomputable def Submodule.indexPID_aux (N : Submodule R M) [Module.Free R M] [Module.Finite R M]
    (heq : Module.rank R M = Module.rank R N) : R := by
  let B := Basis.reindex (Module.Free.chooseBasis R M) (Fintype.equivFin (Module.Free.ChooseBasisIndex R M))
  exact ((LinearMap.toMatrix (Submodule.basisOfPID_of_eq_rank N heq) B (Submodule.subtype N)).det)

/-- Auxiliary definition: for `N` a submodule of `M` of the same rank,
  the determinant of the matrix representing the inclusion map `N → M` with
  respect to some choice of bases.  -/
lemma Submodule.indexPID_aux_def (N : Submodule R M) [Module.Free R M] [Module.Finite R M]
    (heq : Module.rank R M = Module.rank R N) : Submodule.indexPID_aux N heq =
  (LinearMap.toMatrix (Submodule.basisOfPID_of_eq_rank N heq)
  (Basis.reindex (Module.Free.chooseBasis R M) (Fintype.equivFin (Module.Free.ChooseBasisIndex R M)))
  (Submodule.subtype N)).det := rfl

/-- The index `[M : N]` of `N` in `M` as an element in `R`. -/
noncomputable def Submodule.indexPID (N : Submodule R M) [Module.Free R M][Module.Finite R M] : R :=
 if heq : Module.rank R M = Module.rank R N then (Submodule.indexPID_aux N heq) else 0

lemma Submodule.eq_top_of_index_isUnit  (N : Submodule R M) [Module.Free R M] [Module.Finite R M]
   (hu : IsUnit (Submodule.indexPID N)) : N = ⊤ := by
  have heq : Module.rank R M = Module.rank R N := by
    by_contra hc
    have : Submodule.indexPID N = 0 := by
      unfold Submodule.indexPID
      simp only [dite_false, hc]
    rw [this] at hu
    simp only [isUnit_zero_iff, zero_ne_one] at hu
  unfold Submodule.indexPID at hu
  simp only [heq, dite_true, Submodule.indexPID_aux_def] at hu
  rw [Submodule.eq_top_iff']
  intro x
  have aux : (LinearEquiv.ofIsUnitDet hu) ((LinearEquiv.ofIsUnitDet hu).symm x) =
    ((LinearEquiv.ofIsUnitDet hu).symm x).1 := by
    simp only [LinearEquiv.ofIsUnitDet_symm_apply, LinearEquiv.ofIsUnitDet_apply, coe_subtype]
  rw [← LinearEquiv.apply_symm_apply (LinearEquiv.ofIsUnitDet hu) x, aux]
  simp only [LinearEquiv.ofIsUnitDet_symm_apply, SetLike.coe_mem]

omit [IsDomain R] [IsPrincipalIdealRing R]
lemma LinearMap.toMatrix_eq_of_index_equiv {N : Type*} [AddCommMonoid N]
    [Module R N] (B : Basis ι R M) (b : Basis ι R N) (f : N →ₗ[R] M )
    (e : ι ≃ ι') :
    (LinearMap.toMatrix b B f).det = (LinearMap.toMatrix (b.reindex e) (B.reindex e) f).det := by
  have : Matrix.reindexAlgEquiv R _ e (LinearMap.toMatrix b B f) = (LinearMap.toMatrix
    (b.reindex e) (B.reindex e) f) := by
    simp only [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
    ext
    simp only [Matrix.submatrix_apply, LinearMap.toMatrix_apply, Basis.coe_reindex,
      Function.comp_apply, Basis.repr_reindex, Finsupp.equivMapDomain_apply]
  rw [← this, Matrix.det_reindexAlgEquiv]

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Given bases for `N` and  `M`, the determinant of the matrix representing
`N → M` is an associate to `[M : N]` -/
lemma associated_index_of_basis  [Module.Free R M]
    [Module.Finite R M] (N : Submodule R M) (B : Basis ι R M ) (b : Basis ι R N ) :
    Associated (Submodule.indexPID N) ((LinearMap.toMatrix b B (Submodule.subtype N)).det) := by
  if heq : Module.rank R M ≠ Module.rank R N then
  · rw [rank_eq_card_basis B, rank_eq_card_basis b] at heq
    simp only [ne_eq, not_true] at heq
  else
  · push Not at heq
    let B' := Basis.reindex (Module.Free.chooseBasis R M) (Fintype.equivFin
      (Module.Free.ChooseBasisIndex R M))
    let b' := (Submodule.basisOfPID_of_eq_rank N heq)
    have heq' := heq
    rw [rank_eq_card_basis B, rank_eq_card_basis b' ] at heq'
    simp only [Fintype.card_fin, Nat.cast_inj] at heq'
    let Bc := B.reindex (Basis.indexEquiv B B')
    let bc := b.reindex (Basis.indexEquiv B B')
    unfold Submodule.indexPID
    simp only [heq, dite_true]
    have : Submodule.indexPID_aux N heq =
       (LinearMap.toMatrix b' B' (Submodule.subtype N)).det := rfl
    simp_rw [this]
    have := LinearMap.toMatrix_comp b' Bc B' (LinearMap.id) (LinearMap.comp
      (Submodule.subtype N) (LinearMap.id (M:= N) ) )
    rw [LinearMap.toMatrix_comp b' bc Bc (Submodule.subtype N) (LinearMap.id)] at this
    rw [(show LinearMap.comp (LinearMap.id) (LinearMap.comp (Submodule.subtype N)
      (LinearMap.id (M := N))) = (Submodule.subtype N) by rfl)] at this
    have aux1 : IsUnit (LinearMap.toMatrix Bc B' (LinearMap.id)).det :=
      LinearEquiv.isUnit_det (LinearEquiv.refl R M) Bc B'
    have aux2 : IsUnit (LinearMap.toMatrix b' bc (LinearMap.id)).det :=
      LinearEquiv.isUnit_det (LinearEquiv.refl R N) b' bc
    rw [this, Matrix.det_mul, Matrix.det_mul,
      LinearMap.toMatrix_eq_of_index_equiv B b _ (Basis.indexEquiv B B'),
      associated_isUnit_mul_left_iff aux1, associated_mul_isUnit_left_iff aux2]
    convert Associated.refl _

/-- If `N₁ ≤ N₂ ≤ M`, then `[M : N₂]` divides `[M : N₁]`. -/
lemma Submodule.indexPID_dvd_of_le [Module.Free R M]
    [Module.Finite R M] (N₁ N₂ : Submodule R M) (hle : N₁ ≤ N₂) :
    Submodule.indexPID N₂ ∣ Submodule.indexPID N₁ := by
  if heq :  Module.rank R M ≠ Module.rank R N₁ then
  · unfold indexPID
    simp only [heq, dite_false, dvd_zero]
  else
  · push Not at heq
    have heqc := heq
    let B := Basis.reindex (Module.Free.chooseBasis R M)
       (Fintype.equivFin (Module.Free.ChooseBasisIndex R M))
    haveI aux : Module.Finite R N₁ := Module.Finite.of_basis (Submodule.basisOfPid B N₁).2
    haveI : Module.Finite R N₂ := Module.Finite.of_basis  (Submodule.basisOfPid B N₂).2
    rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at heq
    norm_cast at heq
    have heq2': Module.rank R M = Module.rank R N₂ := by
      rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank ,
      LE.le.antisymm (by rw [heq] ; exact (Submodule.finrank_mono hle)) (Submodule.finrank_le N₂)]
    let f := Submodule.inclusion hle
    let g := (Submodule.subtype N₂)
    let b₁ := Submodule.basisOfPID_of_eq_rank N₁ heqc
    let b₂ := Submodule.basisOfPID_of_eq_rank N₂ heq2'
    have assoc1 := associated_index_of_basis N₁ B b₁
    rw [←(show g.comp f = Submodule.subtype N₁ by rfl)] at assoc1
    have := LinearMap.toMatrix_comp b₁ b₂ B g f
    rw [Associated.dvd_iff_dvd_left (associated_index_of_basis N₂ B b₂), Associated.dvd_iff_dvd_right assoc1]
    use (LinearMap.toMatrix b₁ b₂ f).det
    apply_fun Matrix.det at this
    rw [Matrix.det_mul] at this
    convert this

/- Version of `Submodule.smithNormalFormTopBasis` which takes two bases as input instead of a
  proof of equalities of ranks. -/
noncomputable def smithBasisModule (N : Submodule R M) (b : Basis ι R M) (b2 : Basis ι R N) :
    Basis ι R M := by
    refine Submodule.smithNormalFormTopBasis b (N := N) ?_
    rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b2]

    --(module_exists_smith_normal_form N b b2).choose

/-- Version of `Submodule.smithNormalFormCoeffs` which takes two bases as input instead of a
  proof of equalities of ranks.  -/
noncomputable def moduleSmithCoeffs (N : Submodule R M) (b : Basis ι R M) (b2 : Basis ι R N) :
    ι → R := by
  refine Submodule.smithNormalFormCoeffs b (N := N) ?_
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b2]

noncomputable def moduleSmithSubmodule (N : Submodule R M) (b : Basis ι R M) (b2 : Basis ι R N) :
    Basis ι R N := by
  refine Submodule.smithNormalFormBotBasis b (N := N) ?_
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b2]

@[simp]
theorem smith_coeffs_property (N : Submodule R M) (b : Basis ι R M) (b2 : Basis ι R N) :
    ∀ i,  (moduleSmithSubmodule N b b2 i : M) =
    moduleSmithCoeffs N b b2 i • smithBasisModule N b b2 i := Submodule.smithNormalFormBotBasis_def b _

theorem moduleSmithCoeffs_ne_zero (N : Submodule R M) (b : Basis ι R M) (b2 : Basis ι R N) :
    ∀ i, moduleSmithCoeffs N b b2 i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b _

/-- If `N` is a proper submodule of `M`, then at least one of the smith coefficients is not a unit. -/
lemma moduleSmithCoeff_ne_unit (N : Submodule R M) (b : Basis ι R M) (b2 : Basis ι R N)
    (hneq : N ≠ ⊤) : ∃ i, ¬ (IsUnit (moduleSmithCoeffs N b b2 i)) := by
  by_contra h
  push Not at h
  have : ⊤ ≤ N := by
    intro x _
    set c := λ i => (IsUnit.exists_right_inv (h i)).choose with hc
    have aux : ∀ i, c i • (moduleSmithSubmodule N b b2 i : M) = smithBasisModule N b b2 i := by
      intro i
      rw [smith_coeffs_property, ← mul_smul, mul_comm, hc,
        ((IsUnit.exists_right_inv (h i)).choose_spec), one_smul]
    have := Basis.sum_repr (smithBasisModule N b b2) x
    simp_rw [← aux] at this
    set y : N := ∑ i : ι , (((smithBasisModule N b b2).repr x) i) •
      (c i • (moduleSmithSubmodule N b b2 i)) with hy
    have : y.1 = x := by
      rw [← this, hy]
      norm_cast
    rw [← this]
    exact y.2
  exact hneq (top_le_iff.1 this)

/-- The index `[M : N]` is associated wih the product of the smith coefficients of `N` in `M`. -/
lemma prod_moduleSmithCoeffs_associated_index [Module.Free R M]
    [Module.Finite R M] (N : Submodule R M) (B : Basis ι R M) (b : Basis ι R N) :
    Associated (Submodule.indexPID N) (∏ i : ι, (moduleSmithCoeffs N B b i)) := by
  have : LinearMap.toMatrix (moduleSmithSubmodule N B b) (smithBasisModule N B b)
    (Submodule.subtype N) = Matrix.diagonal (λ i => (moduleSmithCoeffs N B b i)) := by
    ext x y
    rw [LinearMap.toMatrix_apply]
    simp only [Submodule.coe_subtype, smith_coeffs_property, map_smul, Basis.repr_self,
      Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases h : x = y
    case _ =>
      rw [h]
      simp only [Finsupp.single_eq_same, Matrix.diagonal_apply_eq]
    case _ =>
      simp only [ne_eq, not_false_eq_true, Matrix.diagonal_apply_ne, h]
      rw [Finsupp.single_eq_of_ne h]
  convert associated_index_of_basis N (smithBasisModule N B b) (moduleSmithSubmodule N B b)
  simp_rw [this]
  exact Matrix.det_diagonal.symm

/-- If a prime `π` divides the index `[M : N]`, then there is `m` in `M` that is not in `N`
 and such that `π • m` is in `N`.  -/
lemma Submodule.prime_dvd_index [Module.Free R M]
    [Module.Finite R M] (N : Submodule R M) {π : R} (hp : Prime π)
    (B : Basis ι R M) (b : Basis ι R N) (hdvd : π ∣ Submodule.indexPID N) :
      ∃ m : M, m ∉ N ∧ π • m ∈ N := by
  rw [Associated.dvd_iff_dvd_right (prod_moduleSmithCoeffs_associated_index N B b),
    Prime.dvd_finset_prod_iff hp] at hdvd
  obtain ⟨i, _, ⟨t , ht⟩⟩  := hdvd
  use (t • smithBasisModule N B b i)
  constructor
  · by_contra hn
    have : π • Basis.coord (moduleSmithSubmodule N B b) i (⟨ (t • smithBasisModule N B b i), hn ⟩ ) =
        Basis.coord (moduleSmithSubmodule N B b) i (π • ⟨ (t • smithBasisModule N B b i), hn ⟩) := by
      rw [← map_smul]
    simp only [Basis.coord_apply, smul_eq_mul, SetLike.mk_smul_mk] at this
    simp_rw [← mul_smul, ← ht, ← smith_coeffs_property N B b] at this
    simp only [Subtype.coe_eta, Basis.repr_self, Finsupp.single_eq_same] at this
    exact (Prime.not_dvd_one hp) (dvd_of_mul_right_eq _ this )
  · rw [← mul_smul, ← ht, ← smith_coeffs_property N B b]
    simp only [SetLike.coe_mem]

/-- If `M` is a free and finite `ℤ`-module and `N` is a submodule of the same rank,
  then the absolute value of the index of `N` in `M` (as modules over a PID)
  coincides with the classical notion of index as the cardinality of `M ⧸ N`. -/
lemma indexPID_eq_index_int {n : ℕ} [Module.Free ℤ M]
    [Module.Finite ℤ M] (N : Submodule ℤ M) (b : Basis (Fin n) ℤ M)
    (b2 : Basis (Fin n) ℤ N) : (Submodule.indexPID N).natAbs = Nat.card (M ⧸ N) := by
  let aux : M ⧸ N ≃+ ∀ i, ZMod (moduleSmithCoeffs N b b2 i).natAbs :=
    Submodule.quotientEquivPiZMod N b _
  rw [← Int.natAbs_natCast (Nat.card (M ⧸ N)), Int.natAbs_eq_iff_associated]
  refine Associated.trans (prod_moduleSmithCoeffs_associated_index N b b2 ) ?_
  rw [Nat.card_eq_of_bijective aux, Nat.card_pi]
  simp only [Nat.card_zmod, Nat.cast_prod]
  rw [← Int.natAbs_eq_iff_associated, ← Int.natCast_inj]
  simp only [Int.natCast_natAbs, Finset.abs_prod, abs_abs]
  exact AddEquiv.bijective aux
