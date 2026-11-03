import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.SpWeyl
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.TensorModel

/-!
# Tensor powers of the standard module of the symplectic Lie algebra

The tensor powers of the standard module of `𝔰𝔭(2g, ℂ)`, in coordinates, and their highest weight
vectors: the tensor products of the wedges `e₁ ∧ ⋯ ∧ e_k`.

## Main definitions

* `SatoTateGroup.SpTensor`: the tensor power of the standard module of `𝔰𝔭(2g, ℂ)`.
* `SatoTateGroup.spPartitionWeight`: the weight of a partition.
* `SatoTateGroup.youngVector`: the highest weight vector of a partition, in the tensor power indexed
  by the boxes of its Young diagram.

## Main results

* `SatoTateGroup.isHighestWeightVector_youngVector`: it is a highest weight vector.
-/

open LieAlgebra LieModule Matrix Module TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

namespace SatoTateGroup

variable {P : Type*} {g : ℕ} [Fintype P] [DecidableEq P]

variable (P g) in
/-- The **tensor power** `(ℂ^{2g})^{⊗P}` of the standard module of `𝔰𝔭(2g, ℂ)`, in coordinates. -/
def SpTensor : Type _ :=
  (P → Fin g ⊕ Fin g) → ℂ

instance : AddCommGroup (SpTensor P g) :=
  inferInstanceAs (AddCommGroup ((P → Fin g ⊕ Fin g) → ℂ))

noncomputable instance : Module ℂ (SpTensor P g) :=
  inferInstanceAs (Module ℂ ((P → Fin g ⊕ Fin g) → ℂ))

instance : FiniteDimensional ℂ (SpTensor P g) :=
  inferInstanceAs (FiniteDimensional ℂ ((P → Fin g ⊕ Fin g) → ℂ))

noncomputable instance : LieRingModule (Symplectic.sp (Fin g) ℂ) (SpTensor P g) where
  bracket X f := tensorAction (P := P) (X : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ) *ᵥ f
  add_lie X Y f := tensorAction_add_mulVec X.1 Y.1 f
  lie_add _ f f' := mulVec_add _ f f'
  leibniz_lie X Y f := tensorAction_leibniz X.1 Y.1 f

lemma lie_spTensor_def (X : Symplectic.sp (Fin g) ℂ) (f : SpTensor P g) :
    ⁅X, f⁆ = tensorAction (P := P) (X : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ) *ᵥ f :=
  rfl

noncomputable instance : LieModule ℂ (Symplectic.sp (Fin g) ℂ) (SpTensor P g) where
  smul_lie c X f := tensorAction_smul_mulVec c X.1 f
  lie_smul c _ f := mulVec_smul _ c f

section Young

variable (c : Fin g → ℕ)

/-- The columns of the Young diagram of the partition `∑ c_k ω_k`: `c_k` columns of length
`k + 1`. -/
abbrev YoungColumn : Type :=
  Σ k : Fin g, Fin (c k)

/-- The boxes of the Young diagram of the partition `∑ c_k ω_k`. -/
abbrev YoungBox : Type :=
  Σ col : YoungColumn c, ↥(Finset.Iic col.1)

/-- The highest weight vector of the partition `∑ c_k ω_k`, the tensor product over the columns of
length `k` of the wedges `e₁ ∧ ⋯ ∧ e_k`. -/
def youngVector : SpTensor (YoungBox c) g :=
  columnTensor (C := YoungColumn c) (R := fun col ↦ ↥(Finset.Iic col.1)) fun _ j ↦ Sum.inl j.1

/-- The **weight of the partition** with exponent vector `c`. -/
noncomputable def spPartitionWeight : Dual ℂ (spCartan (g := g)) :=
  ∑ j, (highestWeight c j : ℂ) • spEpsilon j

lemma spPartitionWeight_spDiag (d : Fin g → ℂ) :
    spPartitionWeight c ⟨spDiag d, spDiag_mem_spCartan d⟩ = ∑ j, (highestWeight c j : ℂ) * d j := by
  rw [spPartitionWeight, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [LinearMap.smul_apply, spEpsilon_spDiag, smul_eq_mul]

lemma spPartitionWeight_spDelta (i : Fin g) :
    spPartitionWeight c (spDelta i) = (highestWeight c i : ℂ) := by
  rw [spDelta, spPartitionWeight_spDiag, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

lemma sum_trace_columns (d : Fin g → ℂ) : ∑ col : YoungColumn c, ∑ j : ↥(Finset.Iic col.1), d j.1 =
    ∑ j, (highestWeight c j : ℂ) * d j := by
  rw [Fintype.sum_sigma]
  simp only [Finset.univ_eq_attach, Finset.sum_attach (Finset.Iic _) d, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, highestWeight, Nat.cast_sum, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_comm' fun k j ↦ ?_
  simp

lemma youngVector_ne_zero : youngVector (g := g) c ≠ 0 := fun h ↦ by
  have h₁ : youngVector (g := g) c (fun p ↦ Sum.inl p.2.1) = 1 := by
    refine Finset.prod_eq_one fun col _ ↦ ?_
    have h₂ : (of fun i j : ↥(Finset.Iic col.1) ↦
        if (Sum.inl i.1 : Fin g ⊕ Fin g) = Sum.inl j.1 then (1 : ℂ) else 0) = 1 := by
      ext i j
      by_cases h₃ : i = j
      · subst h₃
        simp
      · simp [h₃]
    rw [wedgeCoord, h₂, det_one]
  rw [h] at h₁
  exact zero_ne_one h₁

lemma lie_spDiag_youngVector (d : Fin g → ℂ) :
    ⁅spDiag d, youngVector c⁆ = (∑ j, (highestWeight c j : ℂ) * d j) • youngVector (g := g) c := by
  rw [lie_spTensor_def, coe_spDiag, ← sum_trace_columns]
  refine (tensorAction_mulVec_columnTensor (C := YoungColumn c)
    (R := fun col ↦ ↥(Finset.Iic col.1)) (fun _ j ↦ Sum.inl j.1)
    (U := fun _ ↦ diagonal fun j ↦ d j.1) fun col a j ↦ ?_).trans ?_
  · rw [Finset.sum_eq_single j]
    · by_cases h : a = Sum.inl j.1
      · simp [h, spValue_inl]
      · simp [h]
    · intro j' _ hj'
      rw [diagonal_apply_ne _ hj']
      simp
    · simp
  · simp only [trace_diagonal]
    rfl

lemma lie_of_upper_youngVector {X : Symplectic.sp (Fin g) ℂ}
    (hX : ∀ a b, X.1 a b ≠ 0 → spHeight b < spHeight a) : ⁅X, youngVector c⁆ = 0 := by
  rw [lie_spTensor_def]
  have h₁ : tensorAction X.1 *ᵥ youngVector c = (∑ col : YoungColumn c, (of fun j' j :
      ↥(Finset.Iic col.1) ↦ X.1 (Sum.inl j'.1) (Sum.inl j.1)).trace) • youngVector (g := g) c :=
    tensorAction_mulVec_columnTensor (C := YoungColumn c) (R := fun col ↦ ↥(Finset.Iic col.1))
      (fun _ j ↦ (Sum.inl j.1 : Fin g ⊕ Fin g)) (X := X.1)
      (U := fun _ ↦ of fun j' j ↦ X.1 (Sum.inl j'.1) (Sum.inl j.1)) fun col a j ↦ by
      by_cases h : ∃ j' : ↥(Finset.Iic col.1), a = Sum.inl j'.1
      · rcases h with ⟨j', rfl⟩
        rw [Finset.sum_eq_single j']
        · simp
        · intro j'' _ hj''
          have h₃ : j'.1 ≠ j''.1 := fun h₄ ↦ hj'' (Subtype.ext h₄.symm)
          simp [h₃]
        · simp
      · have h₂ : X.1 a (Sum.inl j.1) = 0 := by
          by_contra h₃
          have h₄ : spHeight (Sum.inl j.1) < spHeight a := hX _ _ h₃
          rcases a with i | i
          · refine h ⟨⟨i, ?_⟩, rfl⟩
            have h₅ : (j.1 : ℕ) ≤ col.1 := Fin.le_def.mp (Finset.mem_Iic.mp j.2)
            have hj : (j.1 : ℕ) < g := j.1.2
            simp only [spHeight, Sum.elim_inl] at h₄
            exact Finset.mem_Iic.mpr (Fin.le_def.mpr (by omega))
          · have hj : (j.1 : ℕ) < g := j.1.2
            simp only [spHeight, Sum.elim_inl, Sum.elim_inr] at h₄
            omega
        rw [h₂]
        refine (Finset.sum_eq_zero fun j' _ ↦ ?_).symm
        rw [ite_eq_right fun h₃ ↦ h ⟨j', h₃⟩]
  refine h₁.trans ?_
  have h₂ (col : YoungColumn c) :
      (of fun j' j : ↥(Finset.Iic col.1) ↦ X.1 (Sum.inl j'.1) (Sum.inl j.1)).trace = 0 := by
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    by_contra h₃
    exact lt_irrefl _ (hX _ _ h₃)
  simp only [h₂, Finset.sum_const_zero, zero_smul]
  rfl

lemma spRootVector_upper {a b : Fin g ⊕ Fin g} (hab : spHeight b < spHeight a) (p q : Fin g ⊕ Fin g)
    (h : (spRootVector a b).1 p q ≠ 0) : spHeight q < spHeight p := by
  rw [spRootVector_apply] at h
  by_cases h₁ : a = p ∧ b = q
  · rw [← h₁.1, ← h₁.2]
    exact hab
  · by_cases h₂ : b.swap = p ∧ a.swap = q
    · rw [← h₂.1, ← h₂.2, spHeight_swap, spHeight_swap]
      omega
    · simp [h₁, h₂] at h

/-- **The tensor products of wedges are highest weight vectors.** -/
lemma isHighestWeightVector_youngVector :
    IsHighestWeightVector spBase (spPartitionWeight c) (youngVector (g := g) c) := by
  refine isHighestWeightVector_of_spRootVector (youngVector_ne_zero c) ?_ fun a b _ h ↦
    lie_of_upper_youngVector c (spRootVector_upper h)
  rintro ⟨_, d, rfl⟩
  rw [spPartitionWeight_spDiag]
  exact lie_spDiag_youngVector c d

end Young

end SatoTateGroup
