import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.OrthogonalTraceless

/-!
# Weyl's construction does not vanish

Let `μ` be a partition of `m` whose first two columns have lengths `a` and `b`, with `a + b ≤ d`.
Then Weyl's construction for `μ` is nonzero: the Young symmetrizer of `μ` does not kill the
traceless tensors of degree `m` of `ℂ^d` (Fulton and Harris, *Representation Theory*, §19.5).

An explicit traceless tensor is the antisymmetrisation along the columns of the pure tensor with the
vector `v_i` at each slot of the row `i`, where the first `b` vectors `v_i = e_{2i} + 𝕚 e_{2i+1}`
span a totally isotropic subspace, and the next ones `v_i = e_{b+i}` are orthogonal to it. A
contraction of this tensor at two slots of one column vanishes by antisymmetry, and at two slots of
distinct columns because one of the two columns is not the first one, so the two rows give an
orthogonal pair.

## Main definitions

* `SatoTateGroup.pureTensor`: the pure tensor of a family of vectors.
* `SatoTateGroup.weylVector`: Weyl's vectors.
* `SatoTateGroup.weylIndex`: the coordinates dual to them.
* `SatoTateGroup.weylTensor`: the pure tensor of a partition, with the vector of its row at each
  slot.
* `SatoTateGroup.weylTuple`: the index tuple on which that tensor is one.

## Main results

* `SatoTateGroup.columnOp_weylTensor_mem_traceless`: the antisymmetrisation of Weyl's tensor along
  the columns is traceless.
* `SatoTateGroup.youngOp_columnOp_weylTensor_ne_zero`: the Young symmetrizer does not kill it.
-/

open Equiv Function TauCeti YoungDiagram YoungTableau

namespace SatoTateGroup

variable {P I : Type*} [Fintype P] {m : ℕ} (μ : m.Partition) {d : ℕ} (b : ℕ)

/-- The pure tensor of a family of vectors. -/
def pureTensor (u : P → I → ℂ) (a : P → I) : ℂ :=
  ∏ r, u r (a r)

lemma slotRep_pureTensor (τ : Perm P) (u : P → I → ℂ) :
    slotRep P I τ (pureTensor u) = pureTensor fun r ↦ u (τ⁻¹ r) := by
  funext a
  rw [slotRep_apply, pureTensor, pureTensor, ← Equiv.prod_comp τ fun s ↦ u (τ⁻¹ s) (a s)]
  simp

variable [DecidableEq P] [Fintype I]

lemma sum_pureTensor_update {p q : P} (hpq : p ≠ q) (u : P → I → ℂ) (a : P → I)
    (h : ∑ c, u p c * u q c = 0) : ∑ c, pureTensor u (update (update a p c) q c) = 0 := by
  have h₁ (c : I) : pureTensor u (update (update a p c) q c) =
      u p c * u q c * ∏ r : {r : P // r ≠ p ∧ r ≠ q}, u r (a r) := by
    rw [pureTensor, prod_eq_mul_mul_prod_subtype hpq, update_of_ne hpq, update_self, update_self,
      mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun r _ ↦ ?_
    rw [update_of_ne r.2.2, update_of_ne r.2.1]
  simp only [h₁]
  rw [← Finset.sum_mul, h, zero_mul]

/-- **Weyl's vectors** attached to a number `b` of isotropic ones: the vectors `e_{2i} + 𝕚 e_{2i+1}`
for `i < b`, and the vectors `e_{b+i}` for `i ≥ b`. The first `b` of them span a totally isotropic
subspace orthogonal to all the others, for the standard symmetric bilinear form. -/
noncomputable def weylVector (i : ℕ) (c : Fin d) : ℂ :=
  if i < b then if (c : ℕ) = 2 * i then 1 else if (c : ℕ) = 2 * i + 1 then Complex.I else 0
  else if (c : ℕ) = b + i then 1 else 0

/-- The coordinate dual to a Weyl's vector. -/
def weylIndex (i : ℕ) : ℕ :=
  if i < b then 2 * i else b + i

lemma weylVector_of_val_eq {i : ℕ} (j : ℕ) {c : Fin d} (hc : (c : ℕ) = weylIndex b i) :
    weylVector b j c = if i = j then 1 else 0 := by
  rw [weylVector, hc, weylIndex]
  split_ifs <;> first | omega | rfl

lemma sum_weylVector_mul_weylVector (i : ℕ) {j : ℕ} (hj : j < b) (hd : 2 * b ≤ d) :
    ∑ c : Fin d, weylVector b i c * weylVector b j c = 0 := by
  have h₁ : 2 * j < d := by
    omega
  have h₂ : 2 * j + 1 < d := by
    omega
  have h₃ (c : Fin d) : weylVector b j c = (if c = ⟨2 * j, h₁⟩ then 1 else 0) +
      if c = ⟨2 * j + 1, h₂⟩ then Complex.I else 0 := by
    simp only [weylVector, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  simp only [h₃, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ]
  rw [weylVector, weylVector]
  dsimp only
  split_ifs <;> first | omega | simp

lemma colLen_one_le_colLen_zero : (ofPartition μ).colLen 1 ≤ (ofPartition μ).colLen 0 :=
  (ofPartition μ).colLen_anti _ _ (Nat.zero_le _)

lemma partitionRow_lt_colLen_zero (x : Fin m) : partitionRow μ x < (ofPartition μ).colLen 0 :=
  rowIndex_lt_colLen_zero _ _

variable {μ} in
lemma partitionRow_lt_colLen_one {x : Fin m} (hx : (partitionCol μ x : ℕ) ≠ 0) :
    partitionRow μ x < (ofPartition μ).colLen 1 :=
  (mem_iff_lt_colLen.mp (rowIndex_colIndex_mem (partitionTableau μ) _)).trans_le
    ((ofPartition μ).colLen_anti _ _ (Nat.one_le_iff_ne_zero.mpr hx))

variable {μ} in
lemma eq_of_partitionRow_eq_of_partitionCol_eq {x y : Fin m}
    (h₁ : partitionRow μ x = partitionRow μ y) (h₂ : partitionCol μ x = partitionCol μ y) : x = y :=
  (partitionLabel μ).symm.injective (rowIndex_colIndex_injective (partitionTableau μ)
    (Prod.ext h₁ (Fin.ext_iff.mp h₂)))

variable (d) in
/-- **Weyl's tensor** of a partition: the pure tensor with Weyl's vector of its row at each slot. -/
noncomputable def weylTensor : (Fin m → Fin d) → ℂ :=
  pureTensor fun r ↦ weylVector ((ofPartition μ).colLen 1) (partitionRow μ r)

lemma columnOp_apply_update {p q : Fin m} (hc : partitionCol μ p = partitionCol μ q) (hpq : p ≠ q)
    (f : (Fin m → Fin d) → ℂ) (a : Fin m → Fin d) (c : Fin d) :
    columnOp (slotRep (Fin m) (Fin d)) (partitionCol μ) f (update (update a p c) q c) = 0 := by
  let F : (Fin m → Fin d) → ℂ := columnOp (slotRep (Fin m) (Fin d)) (partitionCol μ) f
  let a' : Fin m → Fin d := update (update a p c) q c
  have h₁ : Equiv.swap p q ∈ fiberSubgroup (partitionCol μ) := swap_mem_fiberSubgroup hc
  have h₂ :
      slotRep (Fin m) (Fin d) (Equiv.swap p q) F = ((Perm.sign (Equiv.swap p q) : ℤ) : ℂ) • F :=
    LinearMap.congr_fun (mul_columnOp_of_mem (slotRep (Fin m) (Fin d)) h₁) f
  rw [Perm.sign_swap hpq] at h₂
  have h₃ : a' ∘ Equiv.swap p q = a' := by
    funext r
    by_cases hp : r = p
    · subst hp
      simp [a', update_of_ne hpq]
    · by_cases hq : r = q
      · subst hq
        simp [a', update_of_ne hpq]
      · simp [Equiv.swap_apply_of_ne_of_ne hp hq]
  have h₄ : F a' = -F a' := by
    have h₅ : F (a' ∘ Equiv.swap p q) = (((-1 : ℤˣ) : ℤ) : ℂ) * F a' := congrFun h₂ a'
    rw [h₃] at h₅
    simpa using h₅
  exact CharZero.eq_neg_self_iff.mp h₄

/-- **The antisymmetrisation of Weyl's tensor along the columns is traceless**, when the first two
columns are short enough. -/
lemma columnOp_weylTensor_mem_traceless
    (hd : (ofPartition μ).colLen 0 + (ofPartition μ).colLen 1 ≤ d) :
    columnOp (slotRep (Fin m) (Fin d)) (partitionCol μ) (weylTensor μ d) ∈
      traceless (Fin m) (Fin d) := by
  refine fun p q hpq a ↦ ?_
  have hb : 2 * (ofPartition μ).colLen 1 ≤ d := by
    have h₁ : (ofPartition μ).colLen 1 ≤ (ofPartition μ).colLen 0 := colLen_one_le_colLen_zero μ
    omega
  by_cases hc : partitionCol μ p = partitionCol μ q
  · exact Finset.sum_eq_zero fun c _ ↦ columnOp_apply_update μ hc hpq _ a c
  · have h₁ (c : Fin d) : columnOp (slotRep (Fin m) (Fin d)) (partitionCol μ) (weylTensor μ d)
        (update (update a p c) q c) = ∑ τ : fiberSubgroup (partitionCol μ),
          ((Perm.sign (τ : Perm (Fin m)) : ℤ) : ℂ) * slotRep (Fin m) (Fin d) τ (weylTensor μ d)
            (update (update a p c) q c) := by
      rw [columnOp_eq_sum, LinearMap.sum_apply, Finset.sum_apply]
      rfl
    simp only [h₁]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun τ _ ↦ ?_
    rw [← Finset.mul_sum, weylTensor, slotRep_pureTensor, sum_pureTensor_update hpq, mul_zero]
    have hτ (x : Fin m) : partitionCol μ ((τ : Perm (Fin m))⁻¹ x) = partitionCol μ x :=
      (fiberSubgroup (partitionCol μ)).inv_mem τ.2 x
    rcases eq_or_ne (partitionCol μ q : ℕ) 0 with hq | hq
    · have hp : (partitionCol μ p : ℕ) ≠ 0 := fun hp ↦ hc (Fin.ext (hp.trans hq.symm))
      rw [← hτ p] at hp
      exact (Finset.sum_congr rfl fun c _ ↦ mul_comm _ _).trans
        (sum_weylVector_mul_weylVector _ _ (partitionRow_lt_colLen_one hp) hb)
    · rw [← hτ q] at hq
      exact sum_weylVector_mul_weylVector _ _ (partitionRow_lt_colLen_one hq) hb

lemma weylIndex_lt (hd : (ofPartition μ).colLen 0 + (ofPartition μ).colLen 1 ≤ d) (r : Fin m) :
    weylIndex ((ofPartition μ).colLen 1) (partitionRow μ r) < d := by
  have h₁ : partitionRow μ r < (ofPartition μ).colLen 0 := partitionRow_lt_colLen_zero μ r
  have h₂ : (ofPartition μ).colLen 1 ≤ (ofPartition μ).colLen 0 := colLen_one_le_colLen_zero μ
  rw [weylIndex]
  split_ifs <;> omega

/-- The index tuple on which Weyl's tensor is one. -/
noncomputable def weylTuple (hd : (ofPartition μ).colLen 0 + (ofPartition μ).colLen 1 ≤ d)
    (r : Fin m) : Fin d :=
  ⟨weylIndex ((ofPartition μ).colLen 1) (partitionRow μ r), weylIndex_lt μ hd r⟩

lemma weylTensor_weylTuple_comp (hd : (ofPartition μ).colLen 0 + (ofPartition μ).colLen 1 ≤ d)
    (q : Perm (Fin m)) : weylTensor μ d (weylTuple μ hd ∘ q) =
      ∏ r, if partitionRow μ (q r) = partitionRow μ r then 1 else 0 := by
  rw [weylTensor, pureTensor]
  exact Finset.prod_congr rfl fun r _ ↦ weylVector_of_val_eq _ _ rfl

lemma columnOp_weylTensor_weylTuple (hd : (ofPartition μ).colLen 0 + (ofPartition μ).colLen 1 ≤ d) :
    columnOp (slotRep (Fin m) (Fin d)) (partitionCol μ) (weylTensor μ d) (weylTuple μ hd) = 1 := by
  rw [columnOp_eq_sum, LinearMap.sum_apply, Finset.sum_apply,
    Finset.sum_eq_single (1 : fiberSubgroup (partitionCol μ))]
  · have h₁ : weylTensor μ d (weylTuple μ hd ∘ (1 : Perm (Fin m))) =
        ∏ r, if partitionRow μ ((1 : Perm (Fin m)) r) = partitionRow μ r then 1 else 0 :=
      weylTensor_weylTuple_comp μ hd 1
    simp only [Perm.coe_one] at h₁
    simpa using h₁
  · intro q _ hq
    have h₁ : ∃ r, (q : Perm (Fin m)) r ≠ r := by
      by_contra h₂
      push Not at h₂
      exact hq (Subtype.ext (Equiv.ext h₂))
    rcases h₁ with ⟨r, hr⟩
    have h₂ : weylTensor μ d (weylTuple μ hd ∘ (q : Perm (Fin m))) = 0 := by
      rw [weylTensor_weylTuple_comp]
      refine Finset.prod_eq_zero (Finset.mem_univ r) (ite_eq_right fun h₃ ↦ hr ?_)
      exact eq_of_partitionRow_eq_of_partitionCol_eq h₃ (q.2 r)
    have h₃ : (((Perm.sign (q : Perm (Fin m)) : ℤ) : ℂ) •
        slotRep (Fin m) (Fin d) (q : Perm (Fin m))) (weylTensor μ d) (weylTuple μ hd) =
          ((Perm.sign (q : Perm (Fin m)) : ℤ) : ℂ) *
            weylTensor μ d (weylTuple μ hd ∘ (q : Perm (Fin m))) :=
      rfl
    rw [h₃, h₂, mul_zero]
  · simp

lemma rowOp_apply_weylTuple (hd : (ofPartition μ).colLen 0 + (ofPartition μ).colLen 1 ≤ d)
    (f : (Fin m → Fin d) → ℂ) :
    rowOp (slotRep (Fin m) (Fin d)) (partitionRow μ) f (weylTuple μ hd) =
      (Fintype.card (fiberSubgroup (partitionRow μ)) : ℂ) * f (weylTuple μ hd) := by
  have h₁ (p : fiberSubgroup (partitionRow μ)) :
      slotRep (Fin m) (Fin d) (p : Perm (Fin m)) f (weylTuple μ hd) = f (weylTuple μ hd) := by
    rw [slotRep_apply]
    refine congrArg f (funext fun r ↦ Fin.ext ?_)
    have h₂ : partitionRow μ ((p : Perm (Fin m)) r) = partitionRow μ r := p.2 r
    simp only [Function.comp_apply, weylTuple, h₂]
  rw [rowOp_eq_sum, LinearMap.sum_apply, Finset.sum_apply]
  simp only [h₁]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The Young symmetrizer of a partition with `λ'₁ + λ'₂ ≤ d` does not vanish on the traceless
tensors**: it does not kill the antisymmetrisation of Weyl's tensor along the columns. -/
lemma youngOp_columnOp_weylTensor_ne_zero
    (hd : (ofPartition μ).colLen 0 + (ofPartition μ).colLen 1 ≤ d) :
    youngOp d μ (columnOp (slotRep (Fin m) (Fin d)) (partitionCol μ) (weylTensor μ d)) ≠ 0 := by
  intro h₀
  have h₁ : youngOp d μ (columnOp (slotRep (Fin m) (Fin d)) (partitionCol μ) (weylTensor μ d))
      (weylTuple μ hd) = 0 :=
    congrFun h₀ (weylTuple μ hd)
  have h₂ : columnOp (slotRep (Fin m) (Fin d)) (partitionCol μ)
      (columnOp (slotRep (Fin m) (Fin d)) (partitionCol μ) (weylTensor μ d)) =
        (Fintype.card (fiberSubgroup (partitionCol μ)) : ℂ) •
          columnOp (slotRep (Fin m) (Fin d)) (partitionCol μ) (weylTensor μ d) :=
    LinearMap.congr_fun (columnOp_mul_self (slotRep (Fin m) (Fin d)) (partitionCol μ)) _
  rw [youngOp_apply, rowOp_apply_weylTuple, h₂, Pi.smul_apply, columnOp_weylTensor_weylTuple,
    smul_eq_mul, mul_one] at h₁
  exact mul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) h₁

end SatoTateGroup
