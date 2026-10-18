/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Concatenating tuples

API to concatenate tuples.

## Main definition
- `Fin.addCasesIter`: concatenates a family of tuples `g : ∀ i, Fin (e i) → α` into a
tuple `Fin (∑ i, e i) → α`
- `indexPairEquiv` : computable bijection between `Fin (∑ i, e i)`, the global index,
  and `Σ (i : Fin r), Fin (e i)`, the pairs of local indices.

## Main results
- `addCasesIter_apply` : describes the evaluation of `Fin.addCasesIter` in terms of the pair of
  local indices.  -/

/-- Form a tuple by concatenating a family of tuples `g` with arities given by `e`. -/
def Fin.addCasesIter {α : Type*} {r : ℕ} (e : Fin r → ℕ) (g : ∀ i, Fin (e i) → α) :
    Fin (∑ i, e i) → α := by
  revert e
  induction r with
  | zero => exact fun e he =>  Fin.elim0
  | succ r hr =>
    intro e g
    exact (Fin.addCases ((hr (fun i => e i.castSucc) (fun i => g i.castSucc)) )
      (g (last r))) ∘ (Fin.cast (Fin.sum_univ_castSucc e))

lemma List.ofFn_addCases {n m} {α} (left : Fin m → α) (right : Fin n → α) :
    List.ofFn (Fin.addCases left right) = List.ofFn left ++ List.ofFn right := by
  simp_rw [List.ofFn_add,  Fin.addCases_right]
  congr
  ext i
  exact Fin.addCases_left i

lemma List.addCases_comp {n m} {α} (f : Fin m → α)  (eq : n = m) :
    List.ofFn (f ∘ (Fin.cast eq))  = List.ofFn f := by
  refine ofFn_inj'.mpr ?_
  ext
  · exact eq
  · exact (Fin.heq_fun_iff eq).mpr (congrFun rfl)

lemma List.ofFn_addCasesIter {α : Type*} {r : ℕ} (e : Fin (r + 1) → ℕ) (g : ∀ i, Fin (e i) → α) :
    List.ofFn (Fin.addCasesIter e g) =
      List.ofFn (Fin.addCasesIter (fun i => e i.castSucc) (fun (i : Fin r) => g i.castSucc))
      ++ List.ofFn (g (Fin.last r)) := by
  match r with
  | 0 =>
    simp [Fin.addCasesIter, Fin.addCases]
    rfl
  | r =>
    unfold Fin.addCasesIter
    simp_rw [List.addCases_comp, List.ofFn_addCases]

/-- Send `j : Fin (∑ i, e i)` to `⟨k, t⟩`, where `k` and `t : Fin (e k)` are
such that `j = t + ∑ i<k, e i` . -/
def indexPair {r : ℕ} (e : Fin r → ℕ) (j : Fin (∑ i, e i)) : Σ (i : Fin r), Fin (e i) := by
  revert e
  induction r with
  | zero =>
    intro e j
    exact ⟨j, IsEmpty.elim (α := Fin 0) (p := fun (i : Fin 0) => Fin (e i)) (Fin.isEmpty') j⟩
  | succ r hr =>
    intro e j
    let e' : Fin r → ℕ := fun i => e i.castSucc
    by_cases h : j < ∑ (i : Fin r), e i.castSucc
    · obtain ⟨i, hi⟩ := hr e' ⟨↑j, h⟩
      exact ⟨i.castSucc, hi⟩
    · let j' := Fin.subNat (∑ (i : Fin r), e i.castSucc) (Fin.cast (show ( ∑ i, e i =
        e (Fin.last r) + ∑ (i : Fin r), e i.castSucc ) by rw [Fin.sum_univ_castSucc, add_comm]) j)
      refine ⟨Fin.last r, ?_⟩
      refine j' ?_
      simp only [Fin.val_cast]
      omega

lemma indexPair_left_aux {r : ℕ} {e : Fin (r + 1) → ℕ} {j : Fin (∑ i, e i)}
    (h : j < ∑ (i : Fin r), e i.castSucc) :
    indexPair e j = ⟨Fin.castSucc (indexPair (fun (i : Fin r) => e i.castSucc) ⟨↑j, h⟩).1,
      (indexPair (fun (i : Fin r) => e i.castSucc) ⟨↑j, h⟩).2 ⟩ := by
  unfold indexPair
  unfold Nat.recAux
  simp only [h, ↓reduceDIte, Fin.val_cast]

lemma indexPair_right_aux {r : ℕ} {e : Fin (r + 1) → ℕ} {j : Fin (∑ i, e i)}
    (h : ¬ j < ∑ (i : Fin r), e i.castSucc) :
    indexPair e j = ⟨Fin.last r, Fin.subNat (∑ (i : Fin r), e i.castSucc)
      (Fin.cast (show ( ∑ i, e i = e (Fin.last r) + ∑ (i : Fin r), e i.castSucc )
        by rw [Fin.sum_univ_castSucc, add_comm]) j) (by simp only [Fin.val_cast] ;  omega)⟩ := by
  unfold indexPair
  unfold Nat.recAux
  simp only [h, ↓reduceDIte]

def indexPair_inv {r : ℕ} (e : Fin r → ℕ) : (Σ (i : Fin r), Fin (e i)) → Fin (∑ i, e i) := by
  intro ⟨i, x⟩
  refine ⟨∑ (j : Fin i.1), e (j.castLE (by omega)) + x.1, ?_⟩
  rw [← Equiv.sum_comp (finCongr (show (i.1 + (r - i.1) = r) by omega)) e, Fin.sum_univ_add]
  refine add_lt_add_of_le_of_lt ?_ ?_
  · refine le_of_eq ?_
    rfl
  · have aux : (r - i.1 - 1) + 1 = r - i.1 := by omega
    rw [← Equiv.sum_comp (finCongr (aux)) _, Fin.sum_univ_succ]
    refine lt_add_of_lt_of_nonneg ?_ ?_
    · show x < e i
      omega
    · exact zero_le

lemma indexPair_left_inverse {r : ℕ} (e : Fin r → ℕ) (j : Fin (∑ i, e i)) :
    indexPair_inv e (indexPair e j) = j := by
  revert e
  induction r with
  | zero =>
    intro e j
    exfalso
    exact Fin.isEmpty.false j
  | succ r hr =>
    intro e x
    by_cases h1 : x < ∑ (i : Fin r), e i.castSucc
    · rw [indexPair_left_aux h1]
      specialize hr (fun i ↦ e i.castSucc) ⟨x, h1⟩
      simp only [← Fin.val_inj] at hr ⊢
      exact hr
    · rw [indexPair_right_aux h1]
      unfold indexPair_inv
      dsimp
      rw [← Fin.val_inj]
      simp
      exact add_tsub_cancel_of_le (not_lt.1 h1)

def indexPairEquiv {r : ℕ} (e : Fin r → ℕ) : Fin (∑ i, e i) ≃  Σ (i : Fin r), Fin (e i) := by
  refine Equiv.ofLeftInverseOfCardLE ?_ (indexPair e) (indexPair_inv e) ?_
  · simp only [Fintype.card_fin, Fintype.card_sigma]
    rfl
  · intro j
    exact indexPair_left_inverse e j

lemma indexPair_right_inverse {r : ℕ} (e : Fin r → ℕ) (i : Fin r) (x : Fin (e i)) :
    indexPair e (indexPair_inv e ⟨i, x⟩) = ⟨i ,x⟩ := by
  show  (indexPairEquiv e ((indexPairEquiv e).symm ⟨i, x⟩)) = ⟨i ,x⟩
  exact Equiv.apply_symm_apply (indexPairEquiv e) ⟨i, x⟩

/-- The evaluation of `Fin.addCasesIter` in terms of the pair of local indices. -/
lemma addCasesIter_apply {α : Type*} {r : ℕ} (e : Fin r → ℕ) (g : ∀ i, Fin (e i) → α)
    (j : Fin (∑ i, e i)) :
    Fin.addCasesIter e g j = g (indexPair e j).1 (indexPair e j).2 := by
  revert e
  induction r with
  | zero =>
    intro e g j
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at j
    exfalso
    exact Fin.isEmpty'.false j
  | succ r hr =>
    intro e g j
    let e' := (fun (i : Fin r) => e i.castSucc)
    let g' := (fun (i : Fin r) => g i.castSucc)
    let f :=  Fin.addCasesIter e' g'
    have : Fin.addCasesIter e g = (Fin.addCases f (g (Fin.last r))) ∘ (Fin.cast (Fin.sum_univ_castSucc e))  := rfl
    rw [this, Function.comp_apply]
    let t := g (Fin.last r)
    by_cases h : j < ∑ (i : Fin r), e i.castSucc
    · have : (Fin.cast (Fin.sum_univ_castSucc e) j) = (Fin.castAdd (e (Fin.last r)) (⟨j, h⟩ )) := by rfl
      rw [this, Fin.addCases_left]
      simp only [hr e' g' ⟨j, h⟩, f, e', g']
      rw [indexPair_left_aux]
    · have : (Fin.cast (Fin.sum_univ_castSucc e) j) =
        (Fin.natAdd (∑ (i : Fin r), e i.castSucc) (Fin.subNat (∑ (i : Fin r), e i.castSucc)
        (Fin.cast (show ( ∑ i, e i = e (Fin.last r) + ∑ (i : Fin r), e i.castSucc )
        by rw [Fin.sum_univ_castSucc, add_comm]) j) (by simp only [Fin.val_cast] ;  omega))) := by
        erw [Fin.natAdd_subNat_cast (i := Fin.cast (Fin.sum_univ_castSucc e) j )]
      rw [this, Fin.addCases_right, indexPair_right_aux h]

section

/-- If the `g i : Fin (e i) → A` are a family of tuples,`f : Fin (∑ i, s i) → List A`, and
if the flattening of `f` restricted to `[sᵢ₋₁, sᵢ)` is contained in `gᵢ`, then the
flattening of `f` is contained in the tuple obtained by concatenating the `gᵢ`. -/
lemma list_flatten_le_list_addCasesIter {A : Type*} {r : ℕ} {e : Fin r → ℕ}
    (g : ∀ (i : Fin r), Fin (e i) → A) {s : Fin r → ℕ} (f : Fin (∑ i, s i) → List A)
    (h : ∀ i : Fin r, List.flatten (List.ofFn (fun (x : Fin (s i)) =>
      f ((indexPair_inv s) ⟨i,x⟩ ))) ⊆ List.ofFn (g i)) :
    List.flatten (List.ofFn f) ⊆ List.ofFn (Fin.addCasesIter e g) := by
  intro x hx
  simp only [List.mem_flatten, List.mem_ofFn, exists_exists_eq_and] at hx ⊢
  obtain ⟨a, ha⟩ := hx
  specialize h (indexPair s a).1
  have : x ∈ List.ofFn (g (indexPair s a).fst) := by
    apply h
    simp only [List.mem_flatten, List.mem_ofFn, exists_exists_eq_and]
    use (indexPair s a).2
    rw [indexPair_left_inverse]
    exact ha
  simp only [List.mem_ofFn] at this
  obtain ⟨j, hj⟩ := this
  use indexPair_inv e ⟨(indexPair s a).fst, j⟩
  rw [addCasesIter_apply, ← hj, indexPair_right_inverse]

/-- If the `g i : Fin (e i) → A` are a family of tuples,`f : Fin (∑ i, s i) → List A`, and
  `gᵢ` is contained in the flattening of `f` restricted to `[sᵢ₋₁, sᵢ)`, then the
the tuple obtained by concatenating the `gᵢ`is contained in the flattening of `f`. -/
lemma list_addCasesIter_le_list_flatten {A : Type*} {r : ℕ} {e : Fin r → ℕ}
    (g : ∀ (i : Fin r), Fin (e i) → A)
    {s : Fin r → ℕ} (f : Fin (∑ i, s i) → List A)
    (h : ∀ i : Fin r,  List.ofFn (g i) ⊆
      List.flatten (List.ofFn (fun (x : Fin (s i)) => f ((indexPair_inv s) ⟨i,x⟩ )))) :
     List.ofFn (Fin.addCasesIter e g) ⊆ List.flatten (List.ofFn f) := by
  intro x hx
  simp only [List.mem_ofFn, List.mem_flatten, exists_exists_eq_and] at hx ⊢
  obtain ⟨i, hi⟩ := hx
  rw [addCasesIter_apply] at hi
  specialize h (indexPair e i).1
  have : x ∈ List.ofFn (g (indexPair e i).fst) := by
    rw [← hi]
    simp only [List.mem_ofFn, exists_apply_eq_apply]
  have aux := h this
  simp only [List.mem_flatten, List.mem_ofFn, exists_exists_eq_and] at aux
  obtain ⟨b, hb⟩ := aux
  use (indexPair_inv s ⟨(indexPair e i).fst, b⟩)

/-- If the `g i : Fin (e i) → A` are a family of tuples,`f : Fin (∑ i, s i) → List A`, and
if the flattening of `f` restricted to `[sᵢ₋₁, sᵢ)` containes the same elements as `gᵢ`, then the
flattening of `f` contains the same elements as the tuple obtained by concatenating the `gᵢ`. -/
lemma list_flatten_eq_list_addCasesIter {A : Type*} {r : ℕ} {e : Fin r → ℕ}
    (g : ∀ (i : Fin r), Fin (e i) → A)
    {s : Fin r → ℕ} (f : Fin (∑ i, s i) → List A)
    (h : ∀ i : Fin r, ∀ x, x ∈ List.flatten (List.ofFn (fun (x : Fin (s i))
      => f ((indexPair_inv s) ⟨i,x⟩ ))) ↔ x ∈ List.ofFn (g i)) (x : A) :
    x ∈ List.flatten (List.ofFn f) ↔ x ∈ List.ofFn (Fin.addCasesIter e g) := by
  constructor
  · intro hx
    refine list_flatten_le_list_addCasesIter g f (fun i x => (h i x).1) hx
  · intro hx
    refine list_addCasesIter_le_list_flatten g f (fun i x => (h i x).2) hx

lemma forall_addCasesIter_prop {A B : Type*} {r : ℕ} {e : Fin r → ℕ}
    (g : ∀ (i : Fin r), Fin (e i) → A) (M : ∀ (i : Fin r), Fin (e i) → B)
    (P : A → B → Prop) (h : ∀ i, ∀ j , P (g i j) (M i j)) :
    ∀ k : Fin (∑ (i : Fin r), e i) , P ((Fin.addCasesIter e g) k) ((Fin.addCasesIter e M) k) := by
  intro k
  rw [addCasesIter_apply, addCasesIter_apply]
  refine h (indexPair e k).1 (indexPair e k).2

end
