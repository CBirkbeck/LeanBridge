import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.OrthogonalInvariants

/-!
# The commutant of `O(d)` on tensor powers

The first fundamental theorem for `O(d)` says that an operator between tensor powers of the standard
representation commuting with `O(d)` is a combination of **Brauer diagrams**
(`SatoTateGroup.brauerMatrix`), the perfect matchings of the slots of the source and of the target
(Brauer, *On algebras which are connected with the semisimple continuous groups*, 1937). A diagram
without an arc inside the source or the target is a permutation of the slots, one with an arc inside
the target has values in the cups (`SatoTateGroup.IsCupAt`), and one with an arc inside the source
has its rows in the cups.

## Main definitions

* `SatoTateGroup.slotRep`: the action of the permutations of the slots on the tensors.
* `SatoTateGroup.IsCupAt`: a tensor which is the Kronecker delta of two slots, times a tensor of
  the others.
* `SatoTateGroup.brauerMatrix`: the operator of a perfect matching of the slots of two tensor
  powers.
* `SatoTateGroup.operatorTensor`: the tensor of an operator between tensor powers.

## Main results

* `SatoTateGroup.eq_sum_smul_brauerMatrix`: an operator commuting with `O(d)` is a combination of
  Brauer diagrams.
-/

open Equiv Matrix TauCeti

universe u

namespace SatoTateGroup

variable (P : Type u) (I : Type*)

/-- The action of the permutations of the slots on the tensors, in coordinates. -/
def slotRep : Representation ℂ (Perm P) ((P → I) → ℂ) where
  toFun σ := LinearMap.funLeft ℂ ℂ fun a ↦ a ∘ σ
  map_one' := rfl
  map_mul' _ _ := rfl

variable {P I}

lemma slotRep_apply (σ : Perm P) (f : (P → I) → ℂ) (a : P → I) : slotRep P I σ f a = f (a ∘ σ) :=
  rfl

/-- `h` is a **cup at the slots `p`, `q`**: a tensor `δ_{a p, a q} h' a`, for a tensor `h'` of the
other slots. -/
def IsCupAt (p q : P) (h : (P → I) → ℂ) : Prop :=
  (∀ a, a p ≠ a q → h a = 0) ∧
    ∀ a a', a p = a q → a' p = a' q → (∀ r, r ≠ p → r ≠ q → a r = a' r) → h a = h a'

lemma apply_eq_of_comp_val_eq {S : Type*} {π : PerfectMatching S} {x y : S} (h : π.val x = y)
    {c : S → I} (hc : c ∘ π.val = c) : c x = c y := by
  have h₁ : c (π.val x) = c x := congrFun hc x
  rw [h] at h₁
  exact h₁.symm

lemma comp_val_eq_of_arc {S : Type*} {π : PerfectMatching S} {x y : S} (h : π.val x = y)
    {c c' : S → I} (hcc : ∀ r, r ≠ x → r ≠ y → c r = c' r) (hc' : c' x = c' y)
    (hc : c ∘ π.val = c) : c' ∘ π.val = c' := by
  have hy : π.val y = x := π.apply_eq_of_apply_eq h
  funext r
  by_cases hr : r = x
  · subst hr
    rw [Function.comp_apply, h]
    exact hc'.symm
  · by_cases hr' : r = y
    · subst hr'
      rw [Function.comp_apply, hy]
      exact hc'
    · have h₁ : π.val r ≠ x := fun h₂ ↦ hr' (by rw [← π.apply_apply r, h₂, h])
      have h₂ : π.val r ≠ y := fun h₃ ↦ hr (by rw [← π.apply_apply r, h₃, hy])
      rw [Function.comp_apply, ← hcc _ h₁ h₂, ← hcc _ hr hr']
      exact congrFun hc r

variable [Fintype P]

variable [DecidableEq P] [Fintype I] in
lemma commute_slotRep_tensorRep (σ : Perm P) (A : Matrix I I ℂ) (f : (P → I) → ℂ) :
    slotRep P I σ (tensorRep A *ᵥ f) = tensorRep A *ᵥ slotRep P I σ f := by
  funext a
  rw [slotRep_apply]
  simp only [mulVec]
  refine ((arrowCongr σ.symm (Equiv.refl I)).sum_comp _).symm.trans
    (Finset.sum_congr rfl fun b _ ↦ ?_)
  have h₁ : (arrowCongr σ.symm (Equiv.refl I)) b = b ∘ σ := rfl
  rw [h₁]
  exact congrArg (· * f (b ∘ σ)) (Equiv.prod_comp σ fun p ↦ A (a p) (b p))

variable [DecidableEq I] {P' : Type u} [Fintype P']

/-- The operator of a perfect matching of the slots of the target and of the source, a
**Brauer diagram**. -/
def brauerMatrix (π : PerfectMatching (P' ⊕ P)) : Matrix (P' → I) (P → I) ℂ :=
  of fun a b ↦ matchingTensor π (Sum.elim a b)

lemma brauerMatrix_row_isCupAt {π : PerfectMatching (P' ⊕ P)} {p q : P}
    (h : π.val (.inr p) = .inr q) (a : P' → I) : IsCupAt p q (brauerMatrix π a) := by
  have hext (x y : P → I) (hxy : ∀ r, r ≠ p → r ≠ q → x r = y r) (r : P' ⊕ P) (hr : r ≠ .inr p)
      (hr' : r ≠ .inr q) : Sum.elim a x r = Sum.elim a y r := by
    rcases r with r | r
    · rfl
    · exact hxy r (fun h₁ ↦ hr (congrArg _ h₁)) fun h₁ ↦ hr' (congrArg _ h₁)
  refine ⟨fun b hb ↦ ite_eq_right fun h₂ ↦ hb (apply_eq_of_comp_val_eq h h₂), fun b b' hb hb' he ↦
    if_congr ⟨comp_val_eq_of_arc h (hext b b' he) hb', comp_val_eq_of_arc h
      (hext b' b fun r h₁ h₂ ↦ (he r h₁ h₂).symm) hb⟩ rfl rfl⟩

variable [DecidableEq P] [Fintype I]

lemma brauerMatrix_mulVec_isCupAt {π : PerfectMatching (P' ⊕ P)} {p q : P'}
    (h : π.val (.inl p) = .inl q) (f : (P → I) → ℂ) : IsCupAt p q (brauerMatrix π *ᵥ f) := by
  refine ⟨fun a ha ↦ Finset.sum_eq_zero fun b _ ↦ ?_, fun a a' ha ha' he ↦
    Finset.sum_congr rfl fun b _ ↦ congrArg (· * f b) ?_⟩
  · have h₁ : matchingTensor π (Sum.elim a b) = 0 :=
      ite_eq_right fun h₂ ↦ ha (apply_eq_of_comp_val_eq h h₂)
    have h₂ : brauerMatrix π a b * f b = matchingTensor π (Sum.elim a b) * f b := rfl
    rw [h₂, h₁, zero_mul]
  · have hext (x y : P' → I) (hxy : ∀ r, r ≠ p → r ≠ q → x r = y r) (r : P' ⊕ P) (hr : r ≠ .inl p)
        (hr' : r ≠ .inl q) : Sum.elim x b r = Sum.elim y b r := by
      rcases r with r | r
      · exact hxy r (fun h₁ ↦ hr (congrArg _ h₁)) fun h₁ ↦ hr' (congrArg _ h₁)
      · rfl
    exact if_congr ⟨comp_val_eq_of_arc h (hext a a' he) ha', comp_val_eq_of_arc h
      (hext a' a fun r h₁ h₂ ↦ (he r h₁ h₂).symm) ha⟩ rfl rfl

lemma exists_brauerMatrix_mulVec_eq {π : PerfectMatching (P ⊕ P)}
    (h : ∀ p, ∃ q, π.val (.inr p) = .inl q) :
    ∃ σ : Perm P, ∀ f : (P → I) → ℂ, brauerMatrix π *ᵥ f = slotRep P I σ f := by
  choose φ hφ using h
  have hinj : Function.Injective φ := fun x y hxy ↦ by
    have h₁ : π.val (.inr x) = π.val (.inr y) := by
      rw [hφ, hφ, hxy]
    exact Sum.inr_injective (π.val.injective h₁)
  let τ : Perm P := ofBijective φ (Finite.injective_iff_bijective.mp hinj)
  have hτ (p : P) : π.val (.inr p) = .inl (τ p) := hφ p
  have hτ' (p : P) : π.val (.inl (τ p)) = .inr p := π.apply_eq_of_apply_eq (hτ p)
  have hδ (a b : P → I) : matchingTensor π (Sum.elim a b) = if a ∘ τ = b then 1 else 0 := by
    refine if_congr ⟨fun h₁ ↦ funext fun p ↦ ?_, fun h₁ ↦ funext fun r ↦ ?_⟩ rfl rfl
    · have h₂ : Sum.elim a b (π.val (.inr p)) = Sum.elim a b (.inr p) := congrFun h₁ _
      rwa [hτ] at h₂
    · subst h₁
      rcases r with q | p
      · have hq : q = τ (τ.symm q) := (τ.apply_symm_apply q).symm
        rw [hq, Function.comp_apply, hτ']
        rfl
      · rw [Function.comp_apply, hτ]
        rfl
  refine ⟨τ, fun f ↦ funext fun a ↦ ?_⟩
  rw [slotRep_apply]
  simp only [mulVec, dotProduct, brauerMatrix, of_apply, hδ, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (a ∘ τ)]
  · rw [ite_eq_left rfl]
  · intro b _ hb
    exact ite_eq_right fun h₁ ↦ hb h₁.symm
  · simp

variable {w d : ℕ} [DecidableEq P']

/-- The tensor of an operator between two tensor powers. -/
def operatorTensor (F : Matrix (P' → Fin d) (P → Fin d) ℂ) (x : P' ⊕ P → Fin d) : ℂ :=
  F (x ∘ .inl) (x ∘ .inr)

lemma tensorRep_mulVec_operatorTensor {A : Matrix (Fin d) (Fin d) ℂ} (hA : A * Aᵀ = 1)
    {F : Matrix (P' → Fin d) (P → Fin d) ℂ} (hF : tensorRep A * F = F * tensorRep A) :
    tensorRep A *ᵥ operatorTensor F = operatorTensor F := by
  have h₁ : (tensorRep A : Matrix (P → Fin d) (P → Fin d) ℂ)ᵀ = tensorRep Aᵀ := by
    ext a b
    simp [tensorRep, kroneckerFamily_apply]
  funext x
  have h₂ : (tensorRep A *ᵥ operatorTensor F) x = (tensorRep A * F * (tensorRep A)ᵀ :
      Matrix (P' → Fin d) (P → Fin d) ℂ) (x ∘ .inl) (x ∘ .inr) := by
    simp only [mulVec, dotProduct, tensorRep, kroneckerFamily_apply, Fintype.prod_sum_type,
      operatorTensor, Matrix.mul_apply, Finset.sum_mul, transpose_apply]
    rw [← (sumArrowEquivProdArrow P' P (Fin d)).symm.sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [Function.comp_apply, sumArrowEquivProdArrow_symm_apply_inl,
      sumArrowEquivProdArrow_symm_apply_inr]
    have h₃ : (sumArrowEquivProdArrow P' P (Fin d)).symm (a, b) ∘ Sum.inl = a := rfl
    have h₄ : (sumArrowEquivProdArrow P' P (Fin d)).symm (a, b) ∘ Sum.inr = b := rfl
    rw [h₃, h₄]
    ring1
  rw [h₂, hF, h₁, Matrix.mul_assoc, ← tensorRep_mul, hA, tensorRep_one, Matrix.mul_one]
  rfl

/-- **An operator between tensor powers commuting with `O(d)` is a combination of Brauer
diagrams.** -/
lemma eq_sum_smul_brauerMatrix (hw : Even w) {F : Matrix (P' → Fin d) (P → Fin d) ℂ}
    (hF : ∀ g : ambientGroup w d, tensorRep (g : Matrix (Fin d) (Fin d) ℂ) * F =
      F * tensorRep (g : Matrix (Fin d) (Fin d) ℂ)) :
    ∃ c : PerfectMatching (P' ⊕ P) → ℂ, F = ∑ π, c π • brauerMatrix π := by
  have h₁ :
      operatorTensor F ∈ Submodule.span ℂ (Set.range (matchingTensor (P := P' ⊕ P) (I := Fin d))) :=
    mem_span_matchingTensor_of_forall_mulVec_eq hw fun g ↦
      tensorRep_mulVec_operatorTensor (mul_transpose_self_ambient hw g) (hF g)
  rcases (Submodule.mem_span_range_iff_exists_fun ℂ).mp h₁ with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  ext a b
  have h₂ : (∑ π, c π • matchingTensor π) (Sum.elim a b) = operatorTensor F (Sum.elim a b) :=
    congrFun hc (Sum.elim a b)
  rw [Matrix.sum_apply]
  simp only [Finset.sum_apply] at h₂
  exact h₂.symm

end SatoTateGroup
