import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Tensor powers in coordinates

A tensor of `(ℂ^I)^{⊗P}` is a function on the tuples `P → I`, its coordinates. The Kronecker product
`SatoTateGroup.kroneckerFamily` of a family of matrices `(M_p)_{p ∈ P}` acts on these. It is
multiplicative, so that `A ↦ A^{⊗P}` (`SatoTateGroup.tensorRep`) and
`X ↦ ∑_p 1 ⊗ ⋯ ⊗ X ⊗ ⋯ ⊗ 1` (`SatoTateGroup.tensorAction`) are the actions of the general linear
group and of its Lie algebra on the tensor power.

The second part computes the action of the Lie algebra on the tensor attached to a family of
columns: a tensor product of the wedges of the vectors `e j`, the coordinates of a wedge being
minors. A matrix preserving the span of the vectors of each column acts by the sum of the traces of
its blocks. With the columns of a Young diagram, these tensors are the highest weight vectors of
the tensor powers.

## Main definitions

* `SatoTateGroup.kroneckerFamily`: the Kronecker product of a family of matrices.
* `SatoTateGroup.tensorRep`: the tensor power of a matrix.
* `SatoTateGroup.tensorAction`: the action of a matrix as a derivation of the tensor power.
* `SatoTateGroup.columnTensor`: a tensor product of wedges.

## Main results

* `SatoTateGroup.tensorAction_mulVec_columnTensor`: a matrix preserving the span of each column acts
  on the tensor product of the wedges by the sum of the traces of its blocks.
-/

open Matrix

namespace SatoTateGroup

section Kronecker

variable {P I : Type*} (M M' : P → Matrix I I ℂ) (p : P) (c : ℂ) (X Y A B : Matrix I I ℂ)
  (f : (P → I) → ℂ) (a b : P → I)

variable [DecidableEq P] [DecidableEq I] in
/-- The family of matrices with `X` at `p` and `1` elsewhere. -/
def oneAt : P → Matrix I I ℂ :=
  Function.update 1 p X

variable [DecidableEq P] [DecidableEq I] in
lemma oneAt_self : oneAt p X p = X :=
  Function.update_self ..

variable [DecidableEq P] [DecidableEq I] {p} in
lemma oneAt_of_ne {r : P} (h : r ≠ p) : oneAt p X r = 1 :=
  Function.update_of_ne h ..

variable [DecidableEq P] [DecidableEq I] [Fintype I] in
lemma oneAt_mul_oneAt_self : oneAt p X * oneAt p Y = oneAt p (X * Y) := by
  funext r
  rw [Pi.mul_apply]
  by_cases h : r = p
  · rw [h, oneAt_self, oneAt_self, oneAt_self]
  · rw [oneAt_of_ne _ h, oneAt_of_ne _ h, oneAt_of_ne _ h, Matrix.one_mul]

variable [DecidableEq P] [DecidableEq I] [Fintype I] {p} in
lemma commute_oneAt {q : P} (hpq : p ≠ q) : oneAt p X * oneAt q Y = oneAt q Y * oneAt p X := by
  funext r
  rw [Pi.mul_apply, Pi.mul_apply]
  by_cases h : r = p
  · rw [h, oneAt_self, oneAt_of_ne _ hpq, Matrix.mul_one, Matrix.one_mul]
  · rw [oneAt_of_ne _ h, Matrix.one_mul, Matrix.mul_one]

variable [Fintype P]

/-- The **Kronecker product** of a family of matrices, on the coordinates of tensors. -/
def kroneckerFamily : Matrix (P → I) (P → I) ℂ :=
  of fun a b ↦ ∏ p, M p (a p) (b p)

lemma kroneckerFamily_apply : kroneckerFamily M a b = ∏ p, M p (a p) (b p) :=
  rfl

/-- The **tensor power** of a matrix. -/
def tensorRep : Matrix (P → I) (P → I) ℂ :=
  kroneckerFamily fun _ ↦ A

variable [DecidableEq P] [Fintype I] in
lemma kroneckerFamily_mul : kroneckerFamily M * kroneckerFamily M' = kroneckerFamily (M * M') := by
  ext a c
  simp only [Matrix.mul_apply, kroneckerFamily_apply, Pi.mul_apply, Finset.prod_univ_sum,
    Fintype.piFinset_univ, Finset.prod_mul_distrib]

variable [DecidableEq P] [Fintype I] in
lemma tensorRep_mul : tensorRep (P := P) (A * B) = tensorRep A * tensorRep B :=
  (kroneckerFamily_mul _ _).symm

variable [DecidableEq I] in
lemma kroneckerFamily_one : kroneckerFamily (1 : P → Matrix I I ℂ) = 1 := by
  ext a b
  rw [kroneckerFamily_apply]
  by_cases h : a = b
  · rw [h, one_apply_eq]
    simp
  · rw [one_apply_ne h]
    rcases Function.ne_iff.mp h with ⟨p, hp⟩
    exact Finset.prod_eq_zero (Finset.mem_univ p) (one_apply_ne hp)

variable [DecidableEq I] in
lemma tensorRep_one : tensorRep (P := P) (1 : Matrix I I ℂ) = 1 :=
  kroneckerFamily_one

variable [DecidableEq I] in
lemma kroneckerFamily_diagonal (d : P → I → ℂ) :
    kroneckerFamily (fun p ↦ diagonal (d p)) = diagonal fun a ↦ ∏ p, d p (a p) := by
  ext a b
  rw [kroneckerFamily_apply]
  by_cases h : a = b
  · rw [h, diagonal_apply_eq]
    exact Finset.prod_congr rfl fun p _ ↦ diagonal_apply_eq _ _
  · rw [diagonal_apply_ne _ h]
    rcases Function.ne_iff.mp h with ⟨p, hp⟩
    exact Finset.prod_eq_zero (Finset.mem_univ p) (diagonal_apply_ne _ hp)

variable [DecidableEq I] in
lemma tensorRep_diagonal (d : I → ℂ) :
    tensorRep (P := P) (diagonal d) = diagonal fun a ↦ ∏ p, d (a p) :=
  kroneckerFamily_diagonal _

variable [DecidableEq P] [Fintype I] in
lemma tensorRep_mul_mulVec : tensorRep (A * B) *ᵥ f = tensorRep A *ᵥ tensorRep B *ᵥ f := by
  rw [tensorRep_mul, mulVec_mulVec]

variable [DecidableEq P] [DecidableEq I]

lemma kroneckerFamily_oneAt_apply : kroneckerFamily (oneAt p X) a b = X (a p) (b p) *
    ∏ r ∈ Finset.univ.erase p, (1 : Matrix I I ℂ) (a r) (b r) := by
  rw [kroneckerFamily_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ p), oneAt_self]
  refine congrArg _ (Finset.prod_congr rfl fun r hr ↦ ?_)
  rw [oneAt_of_ne _ (Finset.ne_of_mem_erase hr)]

lemma kroneckerFamily_oneAt_add : kroneckerFamily (oneAt p (X + Y)) =
    kroneckerFamily (oneAt p X) + kroneckerFamily (oneAt p Y) := by
  ext a b
  rw [Matrix.add_apply, kroneckerFamily_oneAt_apply, kroneckerFamily_oneAt_apply,
    kroneckerFamily_oneAt_apply, Matrix.add_apply, add_mul]

lemma kroneckerFamily_oneAt_smul :
    kroneckerFamily (oneAt p (c • X)) = c • kroneckerFamily (oneAt p X) := by
  ext a b
  rw [Matrix.smul_apply, kroneckerFamily_oneAt_apply, kroneckerFamily_oneAt_apply,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

/-- The **action of a matrix on the tensor power** as a derivation. -/
def tensorAction : Matrix (P → I) (P → I) ℂ :=
  ∑ p, kroneckerFamily (oneAt p X)

lemma tensorAction_add : tensorAction (P := P) (X + Y) = tensorAction X + tensorAction Y := by
  simp only [tensorAction, kroneckerFamily_oneAt_add, Finset.sum_add_distrib]

lemma tensorAction_smul : tensorAction (P := P) (c • X) = c • tensorAction X := by
  simp only [tensorAction, kroneckerFamily_oneAt_smul, Finset.smul_sum]

lemma tensorAction_sub : tensorAction (P := P) (X - Y) = tensorAction X - tensorAction Y := by
  have h : X - Y = X + (-1 : ℂ) • Y := by
    rw [neg_one_smul, sub_eq_add_neg]
  rw [h, tensorAction_add, tensorAction_smul, neg_one_smul, sub_eq_add_neg]

lemma tensorAction_diagonal (z : I → ℂ) :
    tensorAction (P := P) (diagonal z) = diagonal fun a ↦ ∑ p, z (a p) := by
  have h₁ (p : P) : oneAt p (diagonal z) = fun r ↦ diagonal (if r = p then z else 1) := by
    funext r
    by_cases h : r = p
    · rw [h, oneAt_self, ite_eq_left rfl]
    · rw [oneAt_of_ne _ h, ite_eq_right h]
      exact diagonal_one.symm
  have h₂ (p : P) : kroneckerFamily (oneAt p (diagonal z)) = diagonal fun a ↦ z (a p) := by
    rw [h₁, kroneckerFamily_diagonal]
    congr 1
    funext a
    rw [Finset.prod_eq_single p]
    · rw [ite_eq_left rfl]
    · intro r _ hr
      rw [ite_eq_right hr, Pi.one_apply]
    · simp
  simp only [tensorAction, h₂]
  ext a b
  rw [Matrix.sum_apply]
  by_cases h : a = b
  · simp only [h, diagonal_apply_eq]
  · simp only [diagonal_apply_ne _ h, Finset.sum_const_zero]

variable [Fintype I]

lemma tensorAction_commutator : tensorAction (P := P) (X * Y - Y * X) =
    tensorAction X * tensorAction Y - tensorAction Y * tensorAction X := by
  have h₁ : tensorAction (P := P) X * tensorAction Y - tensorAction Y * tensorAction X =
      ∑ p, ∑ q, (kroneckerFamily (oneAt p X * oneAt q Y) -
        kroneckerFamily (oneAt q Y * oneAt p X)) := by
    simp only [tensorAction, Finset.sum_mul_sum, kroneckerFamily_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun q p ↦ kroneckerFamily (oneAt q Y * oneAt p X))]
  rw [h₁, tensorAction_sub, tensorAction, tensorAction, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Finset.sum_eq_single p, oneAt_mul_oneAt_self, oneAt_mul_oneAt_self]
  · intro q _ hq
    rw [commute_oneAt _ _ (Ne.symm hq), sub_self]
  · simp

lemma tensorAction_add_mulVec :
    tensorAction (X + Y) *ᵥ f = tensorAction X *ᵥ f + tensorAction Y *ᵥ f := by
  rw [tensorAction_add, add_mulVec]

lemma tensorAction_smul_mulVec : tensorAction (c • X) *ᵥ f = c • tensorAction X *ᵥ f := by
  rw [tensorAction_smul, smul_mulVec]

lemma tensorAction_leibniz : tensorAction X *ᵥ tensorAction Y *ᵥ f =
    tensorAction (X * Y - Y * X) *ᵥ f + tensorAction Y *ᵥ tensorAction X *ᵥ f := by
  rw [tensorAction_commutator, mulVec_mulVec, mulVec_mulVec, sub_mulVec, sub_add_cancel]

lemma tensorRep_one_mulVec : tensorRep (1 : Matrix I I ℂ) *ᵥ f = f := by
  rw [tensorRep_one, one_mulVec]

lemma tensorRep_diagonal_mulVec_apply (d : I → ℂ) :
    (tensorRep (diagonal d) *ᵥ f) a = (∏ p, d (a p)) * f a := by
  rw [tensorRep_diagonal, mulVec_diagonal]

lemma tensorAction_diagonal_mulVec_apply (z : I → ℂ) :
    (tensorAction (diagonal z) *ᵥ f) a = (∑ p, z (a p)) * f a := by
  rw [tensorAction_diagonal, mulVec_diagonal]

variable {A B} in
lemma tensorRep_mul_tensorAction_mul (h : A * B = 1) :
    tensorRep A * tensorAction (P := P) X * tensorRep B = tensorAction (A * X * B) := by
  simp only [tensorAction, Finset.mul_sum, Finset.sum_mul, tensorRep, kroneckerFamily_mul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  congr 1
  funext r
  simp only [Pi.mul_apply]
  by_cases hr : r = p
  · rw [hr, oneAt_self, oneAt_self]
  · rw [oneAt_of_ne _ hr, oneAt_of_ne _ hr, Matrix.mul_one, h]

lemma kroneckerFamily_oneAt_mulVec :
    (kroneckerFamily (oneAt p X) *ᵥ f) a = ∑ t, X (a p) t * f (Function.update a p t) := by
  rw [mulVec, dotProduct, ← Finset.sum_fiberwise Finset.univ (fun b : P → I ↦ b p)]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Finset.sum_eq_single_of_mem (Function.update a p t) (by simp)]
  · rw [kroneckerFamily_oneAt_apply, Function.update_self, Finset.prod_eq_one, mul_one]
    intro r hr
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hr), one_apply_eq]
  · intro b hb hne
    have hbp : b p = t := (Finset.mem_filter.mp hb).2
    have h₁ : ∃ r, r ≠ p ∧ a r ≠ b r := by
      by_contra h₂
      refine hne (funext fun r ↦ ?_)
      by_cases hr : r = p
      · rw [hr, Function.update_self, hbp]
      · rw [Function.update_of_ne hr]
        by_contra h₃
        exact h₂ ⟨r, hr, Ne.symm h₃⟩
    rcases h₁ with ⟨r, hr, hab⟩
    rw [kroneckerFamily_apply, Finset.prod_eq_zero (Finset.mem_univ r), zero_mul]
    rw [oneAt_of_ne _ hr, one_apply_ne hab]

end Kronecker

section Columns

variable {C I : Type*} [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I] {R : C → Type*}
  [∀ c, Fintype (R c)] [∀ c, DecidableEq (R c)]

lemma sum_det_updateRow_mul {r : Type*} [Fintype r] [DecidableEq r] (M U : Matrix r r ℂ) :
    ∑ i, (M.updateRow i ((M * U) i)).det = U.trace * M.det := by
  have h₁ (i : r) : (M.updateRow i ((M * U) i)).det = (Mᵀ.adjugate *ᵥ (M * U) i) i := by
    rw [← cramer_eq_adjugate_mulVec, cramer_transpose_apply]
  have h₂ : ∑ i, (Mᵀ.adjugate *ᵥ (M * U) i) i = (M.adjugate * (M * U)).trace := by
    simp only [trace, ← adjugate_transpose]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl fun i _ ↦ h₁ i, h₂, ← Matrix.mul_assoc, adjugate_mul, smul_mul,
    Matrix.one_mul, trace_smul, smul_eq_mul, mul_comm]

/-- The coordinate of a wedge of the vectors `e j` at a tuple: a minor. -/
def wedgeCoord {r : Type*} [Fintype r] [DecidableEq r] (e : r → I) (a : r → I) : ℂ :=
  (of fun i j ↦ if a i = e j then (1 : ℂ) else 0).det

lemma sum_mul_wedgeCoord_update {r : Type*} [Fintype r] [DecidableEq r] (e : r → I)
    {X : Matrix I I ℂ} {U : Matrix r r ℂ}
    (hU : ∀ c j, X c (e j) = ∑ j', if c = e j' then U j' j else 0) (a : r → I) :
    ∑ i, ∑ t, X (a i) t * wedgeCoord e (Function.update a i t) = U.trace * wedgeCoord e a := by
  let M : Matrix r r ℂ := of fun i j ↦ if a i = e j then (1 : ℂ) else 0
  have h₁ (i : r) :
      ∑ t, X (a i) t * wedgeCoord e (Function.update a i t) = (M.updateRow i ((M * U) i)).det := by
    have h₂ (t : I) : wedgeCoord e (Function.update a i t) =
        (M.updateRow i fun j ↦ if t = e j then (1 : ℂ) else 0).det := by
      refine congrArg det (Matrix.ext fun i' j ↦ ?_)
      by_cases h : i' = i
      · subst h
        simp
      · simp [updateRow_ne h, Function.update_of_ne h, M]
    have h₃ : (M * U) i = ∑ t, X (a i) t • fun j ↦ if t = e j then (1 : ℂ) else 0 := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single (e j)]
      · simp only [Pi.smul_apply, smul_eq_mul, ite_true, mul_one]
        rw [hU, Matrix.mul_apply]
        exact Finset.sum_congr rfl fun j' _ ↦ by simp [M]
      · intro t _ ht
        simp [ht]
      · simp
    have h₄ : ∀ (s : Finset I) (c : I → r → ℂ),
        (M.updateRow i (∑ t ∈ s, c t)).det = ∑ t ∈ s, (M.updateRow i (c t)).det := by
      intro s c
      induction s using Finset.cons_induction with
      | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        exact det_eq_zero_of_row_eq_zero i fun j ↦ by simp
      | cons t s ht ih =>
        rw [Finset.sum_cons, Finset.sum_cons, det_updateRow_add, ih]
    rw [h₃, h₄]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [det_updateRow_smul, h₂]
  rw [Finset.sum_congr rfl fun i _ ↦ h₁ i, sum_det_updateRow_mul]
  rfl

variable (e : ∀ c, R c → I)

/-- The **tensor product of the wedges** of the columns `e c`, on the coordinates of the tensor
power indexed by the boxes of the columns. -/
def columnTensor (a : (Σ c, R c) → I) : ℂ :=
  ∏ c, wedgeCoord (e c) fun i ↦ a ⟨c, i⟩

/-- **A matrix preserving the span of each column acts on the tensor product of the wedges by the
sum of the traces of its blocks.** -/
lemma tensorAction_mulVec_columnTensor {X : Matrix I I ℂ} {U : ∀ c, Matrix (R c) (R c) ℂ}
    (hU : ∀ col a j, X a (e col j) = ∑ j', if a = e col j' then U col j' j else 0) :
    tensorAction X *ᵥ columnTensor e = (∑ col, (U col).trace) • columnTensor e := by
  funext a
  rw [tensorAction, sum_mulVec, Finset.sum_apply, Fintype.sum_sigma]
  simp only [kroneckerFamily_oneAt_mulVec]
  have h₁ (col : C) (i : R col) (t : I) : columnTensor e (Function.update a ⟨col, i⟩ t) =
      wedgeCoord (e col) (Function.update (fun i' ↦ a ⟨col, i'⟩) i t) *
        ∏ c ∈ Finset.univ.erase col, wedgeCoord (e c) fun i' ↦ a ⟨c, i'⟩ := by
    rw [columnTensor, ← Finset.mul_prod_erase _ _ (Finset.mem_univ col)]
    congr 1
    · congr 1
      funext i'
      by_cases h : i' = i
      · subst h
        simp
      · have h₂ : (⟨col, i'⟩ : Σ c, R c) ≠ ⟨col, i⟩ := fun h₃ ↦ h (by simpa using h₃)
        rw [Function.update_of_ne h, Function.update_of_ne h₂]
    · refine Finset.prod_congr rfl fun c hc ↦ congrArg _ (funext fun i' ↦ ?_)
      have h₂ : (⟨c, i'⟩ : Σ c, R c) ≠ ⟨col, i⟩ := fun h₃ ↦
        Finset.ne_of_mem_erase hc (congrArg Sigma.fst h₃)
      rw [Function.update_of_ne h₂]
  simp only [h₁, ← mul_assoc, ← Finset.sum_mul]
  have h₂ (col : C) : ∑ i, ∑ t, X (a ⟨col, i⟩) t *
      wedgeCoord (e col) (Function.update (fun i' ↦ a ⟨col, i'⟩) i t) =
        (U col).trace * wedgeCoord (e col) fun i' ↦ a ⟨col, i'⟩ :=
    sum_mul_wedgeCoord_update (e col) (hU col) _
  simp only [h₂, mul_assoc, Finset.mul_prod_erase _ (fun c ↦ wedgeCoord (e c) fun i' ↦ a ⟨c, i'⟩)
    (Finset.mem_univ _)]
  rw [Pi.smul_apply, smul_eq_mul, ← Finset.sum_mul]
  rfl

end Columns

end SatoTateGroup
