import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.OrthogonalIsotypic
import TauCeti.Combinatorics.Young.Dominance
import TauCeti.RepresentationTheory.Symmetric.Factorization
import TauCeti.RepresentationTheory.Symmetric.Specht.Decomposition

/-!
# Young symmetrizers through the column antisymmetrisers

The Young symmetrizer of a partition, in any representation of the symmetric group, is the row
symmetriser after the column antisymmetriser of its row-superstandard tableau. By Tau Ceti's
decomposition of the group algebra into Specht modules, an operator commuting with the group which
is killed by the Young symmetrizer of `μ` and by the column antisymmetrisers of the partitions
strictly dominated by `μ` is also killed by the column antisymmetriser of `μ`.

## Main definitions

* `SatoTateGroup.partitionTableau`: the row-superstandard tableau of a partition.
* `SatoTateGroup.partitionLabel`: the labels of that tableau, as `Fin m`.
* `SatoTateGroup.partitionRow`, `SatoTateGroup.partitionCol`: the row and the column of a label.

## Main results

* `SatoTateGroup.asAlgebraHom_youngSymmetrizer`: the Young symmetrizer is the row symmetriser after
  the column antisymmetriser.
* `SatoTateGroup.asAlgebraHom_youngSymmetrizer_mul_mul_eq_zero`: the Young symmetrizers of two
  distinct partitions annihilate each other, through any element of the group algebra.
* `SatoTateGroup.asAlgebraHom_youngSymmetrizer_mul_ne_zero`: the Young symmetrizer of `μ` does not
  kill an operator on which the column antisymmetriser of `μ` does not vanish, while those of the
  partitions strictly dominated by `μ` do.
-/

open Equiv Module TauCeti YoungDiagram YoungTableau

open Nat (Partition.youngSymmetrizer_def)

namespace SatoTateGroup

variable {m : ℕ} (ν : m.Partition)

/-- The row-superstandard tableau of a partition. -/
noncomputable abbrev partitionTableau : YoungTableau (ofPartition ν) :=
  (StandardYoungTableau.rowSuperstandard (ofPartition ν)).toTableau

/-- The identification of the labels of the tableau of a partition of `m` with `Fin m`. -/
abbrev partitionLabel : Fin (ofPartition ν).card ≃ Fin m :=
  finCongr (card_ofPartition ν)

/-- The row of a label, in the tableau of a partition. -/
noncomputable def partitionRow (x : Fin m) : ℕ :=
  rowIndex (partitionTableau ν) ((partitionLabel ν).symm x)

/-- The column of a label, in the tableau of a partition. -/
noncomputable def partitionCol (x : Fin m) : Fin ((ofPartition ν).rowLen 0) :=
  ⟨colIndex (partitionTableau ν) ((partitionLabel ν).symm x),
    (colIndex_lt_rowLen _ _).trans_le ((ofPartition ν).rowLen_anti _ _ (Nat.zero_le _))⟩

lemma card_partitionCol (k : Fin ((ofPartition ν).rowLen 0)) :
    Fintype.card {x // partitionCol ν x = k} = (ofPartition ν).colLen k := by
  rw [← card_filter_colIndex_eq (partitionTableau ν) k, Fintype.card_subtype]
  refine Finset.card_equiv (partitionLabel ν).symm fun x ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Fin.ext_iff

variable {M : Type*} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (Perm (Fin m)) M)

/-- **The Young symmetrizer of a partition is the row symmetriser after the column
antisymmetriser.** -/
lemma asAlgebraHom_youngSymmetrizer : ρ.asAlgebraHom (ν.youngSymmetrizer ℂ) =
    rowOp ρ (partitionRow ν) * columnOp ρ (partitionCol ν) := by
  let E : Perm (Fin (ofPartition ν).card) ≃* Perm (Fin m) := (partitionLabel ν).permCongrHom
  have hE (p : Perm (Fin (ofPartition ν).card)) (x : Fin m) :
      (partitionLabel ν).symm (E p x) = p ((partitionLabel ν).symm x) := by
    simp [E]
  have hE' (p : Perm (Fin (ofPartition ν).card)) (k : Fin (ofPartition ν).card) :
      E p (partitionLabel ν k) = partitionLabel ν (p k) := by
    simp [E]
  have hrow (p : Perm (Fin (ofPartition ν).card)) :
      p ∈ rowSubgroup (partitionTableau ν) ↔ E p ∈ fiberSubgroup (partitionRow ν) := by
    constructor
    · intro hp x
      rw [partitionRow, partitionRow, hE]
      exact mem_rowSubgroup.mp hp _
    · intro hp
      refine mem_rowSubgroup.mpr fun k ↦ ?_
      have h₁ : partitionRow ν (E p (partitionLabel ν k)) = partitionRow ν (partitionLabel ν k) :=
        hp (partitionLabel ν k)
      rw [hE', partitionRow, partitionRow, symm_apply_apply, symm_apply_apply] at h₁
      exact h₁
  have hcol (q : Perm (Fin (ofPartition ν).card)) :
      q ∈ colSubgroup (partitionTableau ν) ↔ E q ∈ fiberSubgroup (partitionCol ν) := by
    constructor
    · intro hq x
      refine Fin.ext ?_
      have h₁ : ((partitionCol ν (E q x) : Fin _) : ℕ) =
          colIndex (partitionTableau ν) ((partitionLabel ν).symm (E q x)) := rfl
      rw [h₁, hE]
      exact mem_colSubgroup.mp hq _
    · intro hq
      refine mem_colSubgroup.mpr fun k ↦ ?_
      have h₁ : colIndex (partitionTableau ν) ((partitionLabel ν).symm (E q (partitionLabel ν k))) =
          colIndex (partitionTableau ν) ((partitionLabel ν).symm (partitionLabel ν k)) :=
        Fin.ext_iff.mp (hq (partitionLabel ν k))
      rwa [hE, symm_apply_apply] at h₁
  have h₁ : ρ.asAlgebraHom (ν.youngSymmetrizer ℂ) =
      Representation.asAlgebraHom (ρ.comp E.toMonoidHom)
        (MonoidAlgebra.mapAlgHom _ (Algebra.ofId ℚ ℂ) (rowSymmetrizer (partitionTableau ν))) *
      Representation.asAlgebraHom (ρ.comp E.toMonoidHom) (MonoidAlgebra.mapAlgHom _
        (Algebra.ofId ℚ ℂ) (columnAntisymmetrizer (partitionTableau ν))) := by
    rw [Partition.youngSymmetrizer_def, Representation.asAlgebraHom_domCongr,
      youngSymmetrizerOver_def, youngSymmetrizer_def, map_mul, map_mul]
  rw [h₁]
  congr 1
  · rw [rowSymmetrizer_def, map_sum, map_sum, rowOp_eq_sum]
    refine Finset.sum_equiv (E.toEquiv.subtypeEquiv hrow) (by simp) fun p _ ↦ ?_
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.mapAlgHom_single, map_one,
      Representation.asAlgebraHom_single_one]
    rfl
  · rw [columnAntisymmetrizer_def, map_sum, map_sum, columnOp_eq_sum]
    refine Finset.sum_equiv (E.toEquiv.subtypeEquiv hcol) (by simp) fun q _ ↦ ?_
    rw [Int.cast_smul_eq_zsmul ℚ, map_zsmul, map_zsmul, MonoidAlgebra.of_apply,
      MonoidAlgebra.mapAlgHom_single, map_one, Representation.asAlgebraHom_single_one,
      ← Int.cast_smul_eq_zsmul ℂ]
    have h₂ : Perm.sign ((E.toEquiv.subtypeEquiv hcol q : fiberSubgroup (partitionCol ν)) :
        Perm (Fin m)) = Perm.sign (q : Perm (Fin (ofPartition ν).card)) :=
      Perm.sign_permCongr _ _
    rw [h₂]
    rfl

lemma exists_youngSymmetrizer_mul_mul (z : MonoidAlgebra ℂ (Perm (Fin m))) :
    ∃ κ : ℂ, ν.youngSymmetrizer ℂ * z * ν.youngSymmetrizer ℂ = κ • ν.youngSymmetrizer ℂ := by
  let E : MonoidAlgebra ℂ (Perm (Fin (ofPartition ν).card)) ≃ₐ[ℂ] MonoidAlgebra ℂ (Perm (Fin m)) :=
    MonoidAlgebra.domCongr ℂ ℂ (partitionLabel ν).permCongrHom
  rcases exists_eq_smul_youngSymmetrizerOver_mul_mul ℂ (partitionTableau ν) (E.symm z) with ⟨κ, hκ⟩
  refine ⟨κ, ?_⟩
  have h₁ : E (youngSymmetrizerOver ℂ (partitionTableau ν) * E.symm z *
      youngSymmetrizerOver ℂ (partitionTableau ν)) =
        E (κ • youngSymmetrizerOver ℂ (partitionTableau ν)) :=
    congrArg E hκ
  rw [map_mul, map_mul, map_smul, AlgEquiv.apply_symm_apply] at h₁
  exact h₁

lemma exists_youngSymmetrizer_mul_self :
    ∃ κ : ℂ, κ ≠ 0 ∧ ν.youngSymmetrizer ℂ * ν.youngSymmetrizer ℂ = κ • ν.youngSymmetrizer ℂ := by
  refine ⟨_, ?_, ν.youngSymmetrizer_mul_self ℂ⟩
  rw [map_ne_zero]
  exact div_ne_zero (Nat.cast_ne_zero.mpr m.factorial_ne_zero)
    (Nat.cast_ne_zero.mpr (finrank_spechtModule_pos ν).ne')

variable {μ : m.Partition}

variable {ν} in
lemma columnOp_mul_mul_rowOp_eq_zero_of_not_dominates (h : ¬Dominates μ ν)
    (z : MonoidAlgebra ℂ (Perm (Fin m))) :
    columnOp ρ (partitionCol μ) * ρ.asAlgebraHom z * rowOp ρ (partitionRow ν) = 0 := by
  rw [ρ.asAlgebraHom_eq_sum z, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun σ _ ↦ ?_
  rcases exists_ne_rowIndex_eq_colIndex_eq_of_not_dominates (μ := ν) (ν := μ) (partitionTableau μ)
    (partitionTableau ν) ((partitionLabel ν).trans (σ.trans (partitionLabel μ).symm)) h with
    ⟨x, y, hxy, hr, hc⟩
  have h₁ : partitionRow ν (partitionLabel ν x) = partitionRow ν (partitionLabel ν y) := by
    rw [partitionRow, partitionRow, symm_apply_apply, symm_apply_apply]
    exact hr
  have h₂ : partitionCol μ (σ (partitionLabel ν x)) = partitionCol μ (σ (partitionLabel ν y)) :=
    Fin.ext hc
  rw [mul_smul_comm, smul_mul_assoc,
    columnOp_mul_mul_rowOp_eq_zero ρ σ ((partitionLabel ν).injective.ne hxy) h₁ h₂, smul_zero]

variable {ν} in
lemma rowOp_mul_mul_columnOp_eq_zero_of_not_dominates (h : ¬Dominates μ ν)
    (z : MonoidAlgebra ℂ (Perm (Fin m))) :
    rowOp ρ (partitionRow ν) * ρ.asAlgebraHom z * columnOp ρ (partitionCol μ) = 0 := by
  rw [ρ.asAlgebraHom_eq_sum z, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun σ _ ↦ ?_
  rcases exists_ne_rowIndex_eq_colIndex_eq_of_not_dominates (μ := ν) (ν := μ) (partitionTableau μ)
    (partitionTableau ν) ((partitionLabel ν).trans (σ.symm.trans (partitionLabel μ).symm)) h with
    ⟨x, y, hxy, hr, hc⟩
  have hσ (l : Fin (ofPartition ν).card) : σ (σ.symm (partitionLabel ν l)) = partitionLabel ν l :=
    σ.apply_symm_apply _
  have h₁ : partitionRow ν (σ (σ.symm (partitionLabel ν x))) =
      partitionRow ν (σ (σ.symm (partitionLabel ν y))) := by
    rw [hσ, hσ, partitionRow, partitionRow, symm_apply_apply, symm_apply_apply]
    exact hr
  have h₂ :
      partitionCol μ (σ.symm (partitionLabel ν x)) = partitionCol μ (σ.symm (partitionLabel ν y)) :=
    Fin.ext hc
  rw [mul_smul_comm, smul_mul_assoc, rowOp_mul_mul_columnOp_eq_zero ρ σ
    (σ.symm.injective.ne ((partitionLabel ν).injective.ne hxy)) h₂ h₁, smul_zero]

/-- **The Young symmetrizers of two distinct partitions of `m` annihilate each other, through any
element of the group algebra.** -/
lemma asAlgebraHom_youngSymmetrizer_mul_mul_eq_zero (h : ν ≠ μ)
    (z : MonoidAlgebra ℂ (Perm (Fin m))) : ρ.asAlgebraHom (ν.youngSymmetrizer ℂ) *
      ρ.asAlgebraHom z * ρ.asAlgebraHom (μ.youngSymmetrizer ℂ) = 0 := by
  rw [asAlgebraHom_youngSymmetrizer, asAlgebraHom_youngSymmetrizer]
  have h₁ : rowOp ρ (partitionRow ν) * columnOp ρ (partitionCol ν) * ρ.asAlgebraHom z *
      (rowOp ρ (partitionRow μ) * columnOp ρ (partitionCol μ)) = rowOp ρ (partitionRow ν) *
        (columnOp ρ (partitionCol ν) * ρ.asAlgebraHom z * rowOp ρ (partitionRow μ)) *
          columnOp ρ (partitionCol μ) := by
    simp only [mul_assoc]
  rw [h₁]
  by_cases hd : Dominates ν μ
  · have h₂ : columnOp ρ (partitionCol ν) * ρ.asAlgebraHom z * rowOp ρ (partitionRow μ) =
        ρ.asAlgebraHom (subgroupCharSum ((Units.coeHom ℂ).comp (signLinearCharacter ℂ (Fin m)))
          (fiberSubgroup (partitionCol ν)) * z *
            subgroupCharSum 1 (fiberSubgroup (partitionRow μ))) := by
      rw [map_mul, map_mul]
      rfl
    rw [h₂]
    exact rowOp_mul_mul_columnOp_eq_zero_of_not_dominates ρ (fun h₃ ↦ h (hd.antisymm h₃)) _
  · rw [columnOp_mul_mul_rowOp_eq_zero_of_not_dominates ρ hd z, mul_zero, zero_mul]

variable [FiniteDimensional ℂ M] {P : End ℂ M}

/-- **The Young symmetrizer of `μ` does not kill a module on which the column antisymmetriser of `μ`
acts nontrivially while those of the partitions strictly dominated by `μ` vanish.** -/
lemma asAlgebraHom_youngSymmetrizer_mul_ne_zero (hP : ∀ σ, Commute P (ρ σ))
    (h₁ : columnOp ρ (partitionCol μ) * P ≠ 0)
    (h₂ : ∀ ν : m.Partition, Dominates μ ν → ν ≠ μ → columnOp ρ (partitionCol ν) * P = 0) :
    ρ.asAlgebraHom (μ.youngSymmetrizer ℂ) * P ≠ 0 := by
  intro h₀
  have hgen (ν : m.Partition) (r : MonoidAlgebra ℂ (Perm (Fin m))) (v : M) :
      columnOp ρ (partitionCol μ) (ρ.asAlgebraHom r (ρ.asAlgebraHom (ν.youngSymmetrizer ℂ) (P v))) =
        0 := by
    by_cases hν : ν = μ
    · subst hν
      have h₃ : ρ.asAlgebraHom (ν.youngSymmetrizer ℂ) (P v) = 0 := LinearMap.congr_fun h₀ v
      rw [h₃, map_zero, map_zero]
    · by_cases hd : Dominates μ ν
      · have h₃ : columnOp ρ (partitionCol ν) (P v) = 0 := LinearMap.congr_fun (h₂ ν hd hν) v
        have h₄ : ρ.asAlgebraHom (ν.youngSymmetrizer ℂ) (P v) =
            rowOp ρ (partitionRow ν) (columnOp ρ (partitionCol ν) (P v)) := by
          rw [asAlgebraHom_youngSymmetrizer]
          rfl
        rw [h₄, h₃, map_zero, map_zero, map_zero]
      · rw [asAlgebraHom_youngSymmetrizer]
        exact LinearMap.congr_fun (columnOp_mul_mul_rowOp_eq_zero_of_not_dominates ρ hd r) _
  refine h₁ (LinearMap.ext fun x ↦ ?_)
  rcases ρ.youngSymmetrizerEval_surjective x with ⟨z, rfl⟩
  rw [End.mul_apply, LinearMap.zero_apply]
  induction z using DirectSum.induction_on with
  | zero => simp
  | add z z' hz hz' =>
    rw [map_add, map_add, map_add, hz, hz', add_zero]
  | of ν t =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' =>
      rw [map_add, map_add, map_add, map_add, ht, ht', add_zero]
    | tmul a w =>
      rw [← DirectSum.lof_eq_of ℂ, Representation.youngSymmetrizerEval_lof_tmul]
      rcases Ideal.mem_span_singleton'.mp a.2 with ⟨r, hr⟩
      rcases w with ⟨_, y, rfl⟩
      have hcomm (r' : MonoidAlgebra ℂ (Perm (Fin m))) : Commute P (ρ.asAlgebraHom r') :=
        Representation.commute_asAlgebraHom_of_forall_commute ρ hP r'
      rw [← hr, map_mul]
      have h₃ : P ((ρ.asAlgebraHom r * ρ.asAlgebraHom (ν.youngSymmetrizer ℂ))
          (ρ.asAlgebraHom (ν.youngSymmetrizer ℂ) y)) = ρ.asAlgebraHom r (ρ.asAlgebraHom
            (ν.youngSymmetrizer ℂ) (P (ρ.asAlgebraHom (ν.youngSymmetrizer ℂ) y))) :=
        LinearMap.congr_fun ((hcomm r).mul_right (hcomm (ν.youngSymmetrizer ℂ)))
          (ρ.asAlgebraHom (ν.youngSymmetrizer ℂ) y)
      rw [h₃]
      exact hgen ν r _

end SatoTateGroup
