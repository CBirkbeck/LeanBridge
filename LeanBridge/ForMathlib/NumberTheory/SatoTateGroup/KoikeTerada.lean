import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.MomentMatrix

/-!
# The Koike–Terada determinant is Weyl's character formula for `USp(2g)`

Let `λ` be a partition with at most `g` parts, `λ'` its conjugate, and let `e_k` be the elementary
symmetric functions of `x₁^{±1}, …, x_g^{±1}`. This file proves the identity
`det(e_{λ'ᵢ - i + j} - e_{λ'ᵢ - i - j}) · det(x_j^{g - i + 1} - x_j^{-(g - i + 1)}) =
det(x_j^{λᵢ + g - i + 1} - x_j^{-(λᵢ + g - i + 1)})`
(`SatoTateGroup.symplecticSchur_mul_det`) of Koike and Terada: the symplectic Schur function
`SatoTateGroup.symplecticSchur` is the quotient in Weyl's character formula for `USp(2g)`.

The proof is linear algebra. With `ẽ_m = e_{g + m}`, the semi-infinite symmetric matrix
`B_{a, b} = ẽ_{a - b} - ẽ_{a + b}`, `a, b ≥ 1`, has `(-1)^b (x_k^b - x_k^{-b})` in its kernel for
every `k`, because `-x_k^{±1}` are the roots of `∑ e_{2g - k} Tᵏ`; its row `a` vanishes after the
column `a + g`, where it has the entry `1`. The determinant of Koike and Terada is the minor of `B`
on the rows `{g + i - λ'ᵢ}` and the first `λ₁` columns, and the set `{g + i - λ'ᵢ}` is the
complement in `{1, …, g + λ₁}` of the set of exponents `{λᵢ + g - i + 1}` of Weyl's numerator. So
the identity is the relation between the maximal minors of a matrix and of its kernel
(`SatoTateGroup.det_submatrix_mul_det_submatrix_of_mul_eq_zero`).

## Main definitions

* `SatoTateGroup.torusEigenvalues`: the multiset `x₁^{±1}, …, x_g^{±1}`.

## Main results

* `SatoTateGroup.det_submatrix_mul_det_submatrix_of_mul_eq_zero`: the maximal minors of a matrix and
  of its kernel.
* `SatoTateGroup.esymm_torusEigenvalues_eq`: the elementary symmetric functions of
  `x₁^{±1}, …, x_g^{±1}` are palindromic.
* `SatoTateGroup.symplecticSchur_mul_det`: **the identity of Koike and Terada.**
-/

open Equiv Finset Matrix Polynomial

namespace SatoTateGroup

section Minors

variable {R : Type*} [CommRing R] {g l : ℕ}

/-- **The maximal minors of a matrix and of its kernel**: if `P Q = 0` for matrices `P` of size
`l × (g + l)` and `Q` of size `(g + l) × g`, the minor of `Q` on the rows `π(1), …, π(g)` and the
minor of `P` on the columns `π(g + 1), …, π(g + l)` are proportional, up to the sign of `π`, with a
factor independent of `π`. -/
lemma det_submatrix_mul_det_submatrix_of_mul_eq_zero (Q : Matrix (Fin (g + l)) (Fin g) R)
    (P : Matrix (Fin l) (Fin (g + l)) R) (hPQ : P * Q = 0) (π : Equiv.Perm (Fin (g + l))) :
    (Q.submatrix (π ∘ Fin.castAdd l) id).det * (P.submatrix id (Fin.natAdd g)).det =
      (Perm.sign π : ℤ) * (Q.submatrix (Fin.castAdd l) id).det *
        (P.submatrix id (π ∘ Fin.natAdd g)).det := by
  let Y : Matrix (Fin g ⊕ Fin l) (Fin (g + l)) R := of fun r p ↦
    Sum.elim (fun j ↦ if p = Fin.castAdd l j then 1 else 0) (fun i ↦ P i p) r
  let X : Matrix (Fin (g + l)) (Fin g ⊕ Fin l) R := of fun p c ↦
    Sum.elim (fun k ↦ Q p k) (fun i ↦ if p = π (Fin.natAdd g i) then 1 else 0) c
  have hne (j : Fin g) (i : Fin l) : Fin.castAdd l j ≠ Fin.natAdd g i := fun h ↦ by
    have h₁ : (j : ℕ) = g + i := by
      simpa using congrArg Fin.val h
    omega
  have hYX : (Y * X).det =
      (Q.submatrix (Fin.castAdd l) id).det * (P.submatrix id (π ∘ Fin.natAdd g)).det := by
    have h : Y * X = fromBlocks (Q.submatrix (Fin.castAdd l) id)
        (of fun j i ↦ if Fin.castAdd l j = π (Fin.natAdd g i) then 1 else 0) 0
        (P.submatrix id (π ∘ Fin.natAdd g)) := by
      ext (j | i) (k | i')
      · simp [Y, X, Matrix.mul_apply]
      · simp [Y, X, Matrix.mul_apply, eq_comm]
      · simpa [Y, X, Matrix.mul_apply] using congrFun (congrFun hPQ i) k
      · simp [Y, X, Matrix.mul_apply]
    rw [h, det_fromBlocks_zero₂₁]
  have hY : (Y.submatrix id finSumFinEquiv).det = (P.submatrix id (Fin.natAdd g)).det := by
    have h : Y.submatrix id finSumFinEquiv = fromBlocks 1 0 (P.submatrix id (Fin.castAdd l))
        (P.submatrix id (Fin.natAdd g)) := by
      ext (j | i) (k | i')
      · simp [Y, Matrix.one_apply, eq_comm]
      · simp [Y, (hne _ _).symm]
      · simp [Y]
      · simp [Y]
    rw [h, det_fromBlocks_zero₁₂, det_one, one_mul]
  let σ : Equiv.Perm (Fin g ⊕ Fin l) := finSumFinEquiv.symm.permCongr π
  have hσ (r : Fin g ⊕ Fin l) : finSumFinEquiv (σ r) = π (finSumFinEquiv r) := by
    simp [σ]
  have hX : ((X.submatrix finSumFinEquiv id).submatrix σ id).det =
      (Q.submatrix (π ∘ Fin.castAdd l) id).det := by
    have h : (X.submatrix finSumFinEquiv id).submatrix σ id =
        fromBlocks (Q.submatrix (π ∘ Fin.castAdd l) id) 0
          (Q.submatrix (π ∘ Fin.natAdd g) id) 1 := by
      ext (j | i) (k | i') <;> simp [X, hσ, Matrix.one_apply, hne]
    rw [h, det_fromBlocks_zero₁₂, det_one, mul_one]
  have hmul : Y * X = Y.submatrix id finSumFinEquiv * X.submatrix finSumFinEquiv id := by
    rw [submatrix_mul_equiv, submatrix_id_id]
  rw [det_permute, Perm.sign_permCongr] at hX
  rw [hmul, det_mul, hY] at hYX
  rw [← hX]
  linear_combination ((Perm.sign π : ℤ) : R) * hYX

lemma sign_eq_prod_of_strictMono {t : Fin g → Fin (g + l)} {s : Fin l → Fin (g + l)}
    (ht : StrictMono t) (hs : StrictMono s) (π : Equiv.Perm (Fin (g + l)))
    (hπt : ∀ j, π (Fin.castAdd l j) = t j) (hπs : ∀ i, π (Fin.natAdd g i) = s i) :
    Perm.sign π = ∏ j, ∏ i, if t j < s i then 1 else -1 := by
  have hIoi (i : Fin (g + l)) (F : Fin (g + l) → ℤˣ) :
      ∏ j ∈ Finset.Ioi i, F j = ∏ j, if i < j then F j else 1 := by
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  rw [π.sign_eq_prod_prod_Ioi]
  simp_rw [hIoi]
  rw [Fin.prod_univ_add]
  have h₂ : ∏ c : Fin l, ∏ j : Fin (g + l), (if Fin.natAdd g c < j then
      (if π (Fin.natAdd g c) < π j then (1 : ℤˣ) else -1) else 1) = 1 := by
    refine Finset.prod_eq_one fun c _ ↦ ?_
    rw [Fin.prod_univ_add]
    have h₃ : ∏ j : Fin g, (if Fin.natAdd g c < Fin.castAdd l j then
        (if π (Fin.natAdd g c) < π (Fin.castAdd l j) then (1 : ℤˣ) else -1) else 1) = 1 := by
      refine Finset.prod_eq_one fun j _ ↦ ite_eq_right fun h ↦ ?_
      have h₄ : g + (c : ℕ) < j := by
        simpa only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] using h
      have h₅ : (j : ℕ) < g := j.2
      omega
    have h₄ : ∏ c' : Fin l, (if Fin.natAdd g c < Fin.natAdd g c' then
        (if π (Fin.natAdd g c) < π (Fin.natAdd g c') then (1 : ℤˣ) else -1) else 1) = 1 := by
      refine Finset.prod_eq_one fun c' _ ↦ ?_
      by_cases h : Fin.natAdd g c < Fin.natAdd g c'
      · have hcc : c < c' := by
          simpa only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left] using h
        rw [ite_eq_left h, hπs, hπs, ite_eq_left (hs hcc)]
      · rw [ite_eq_right h]
    rw [h₃, h₄, one_mul]
  rw [h₂, mul_one]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [Fin.prod_univ_add]
  have h₃ : ∏ b : Fin g, (if Fin.castAdd l j < Fin.castAdd l b then
      (if π (Fin.castAdd l j) < π (Fin.castAdd l b) then (1 : ℤˣ) else -1) else 1) = 1 := by
    refine Finset.prod_eq_one fun b _ ↦ ?_
    by_cases h : Fin.castAdd l j < Fin.castAdd l b
    · have hjb : j < b := by
        simpa only [Fin.lt_def, Fin.val_castAdd] using h
      rw [ite_eq_left h, hπt, hπt, ite_eq_left (ht hjb)]
    · rw [ite_eq_right h]
  rw [h₃, one_mul]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have h₄ : Fin.castAdd l j < Fin.natAdd g i := by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  rw [ite_eq_left h₄, hπt, hπs]

end Minors

section Eigenvalues

variable {g : ℕ} (x : Fin g → ℂ)

/-- The multiset `x₁, x₁⁻¹, …, x_g, x_g⁻¹` of the eigenvalues of a diagonal matrix of `USp(2g)`. -/
noncomputable def torusEigenvalues : Multiset ℂ :=
  univ.val.map x + univ.val.map fun j ↦ (x j)⁻¹

lemma card_torusEigenvalues : Multiset.card (torusEigenvalues x) = g + g := by
  simp [torusEigenvalues]

/-- The factor `(T + x_j) (T + x_j⁻¹)` of the polynomial with coefficients the `e_k`. -/
noncomputable def torusFactor (j : Fin g) : ℂ[X] :=
  (X + C (x j)) * (X + C (x j)⁻¹)

lemma map_prod_torusEigenvalues :
    ((torusEigenvalues x).map fun r ↦ X + C r).prod = ∏ j, torusFactor x j := by
  simp only [torusEigenvalues, torusFactor, Multiset.map_add, Multiset.prod_add, Multiset.map_map,
    Function.comp_def, Finset.prod_eq_multiset_prod, Multiset.prod_map_mul]

lemma natDegree_torusFactor_le (j : Fin g) : (torusFactor x j).natDegree ≤ 2 := by
  have h : (torusFactor x j).natDegree ≤ (X + C (x j)).natDegree + (X + C (x j)⁻¹).natDegree :=
    natDegree_mul_le
  rwa [natDegree_X_add_C, natDegree_X_add_C] at h

lemma reflect_torusFactor {j : Fin g} (hx : x j ≠ 0) :
    reflect (1 + 1) (torusFactor x j) = torusFactor x j := by
  have hC : C (x j) * C (x j)⁻¹ = (1 : ℂ[X]) := by
    rw [← C_mul, mul_inv_cancel₀ hx, C_1]
  have h₁ (a : ℂ) : reflect 1 (X + C a) = 1 + C a * X := by
    rw [reflect_add, reflect_one_X, reflect_C, pow_one]
  rw [torusFactor, reflect_mul _ _ (natDegree_X_add_C _).le (natDegree_X_add_C _).le, h₁, h₁]
  linear_combination (X ^ 2 - 1) * hC

lemma natDegree_prod_torusFactor_le (S : Finset (Fin g)) :
    (∏ j ∈ S, torusFactor x j).natDegree ≤ (1 + 1) * #S := by
  refine (natDegree_prod_le _ _).trans ?_
  rw [mul_comm, ← smul_eq_mul]
  exact Finset.sum_le_card_nsmul _ _ _ fun j _ ↦ natDegree_torusFactor_le x j

variable {x}

lemma reflect_prod_torusFactor (hx : ∀ j, x j ≠ 0) (S : Finset (Fin g)) :
    reflect ((1 + 1) * #S) (∏ j ∈ S, torusFactor x j) = ∏ j ∈ S, torusFactor x j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj, mul_add, mul_one, add_comm,
      reflect_mul _ _ (natDegree_torusFactor_le x j) (natDegree_prod_torusFactor_le x S),
      reflect_torusFactor x (hx j), ih]

/-- **The elementary symmetric functions of `x₁^{±1}, …, x_g^{±1}` are palindromic.** -/
lemma esymm_torusEigenvalues_eq (hx : ∀ j, x j ≠ 0) {k : ℕ} (hk : k ≤ g + g) :
    (torusEigenvalues x).esymm (g + g - k) = (torusEigenvalues x).esymm k := by
  have hcard : Multiset.card (torusEigenvalues x) = g + g := card_torusEigenvalues x
  have h₁ : (∏ j, torusFactor x j).coeff k = (torusEigenvalues x).esymm (g + g - k) := by
    rw [← map_prod_torusEigenvalues, Multiset.prod_X_add_C_coeff _ (hcard ▸ hk), hcard]
  have h₂ : (∏ j, torusFactor x j).coeff (g + g - k) = (torusEigenvalues x).esymm k := by
    rw [← map_prod_torusEigenvalues, Multiset.prod_X_add_C_coeff _ (by omega), hcard,
      Nat.sub_sub_self hk]
  have h₃ : reflect (g + g) (∏ j, torusFactor x j) = ∏ j, torusFactor x j := by
    have h₄ : (1 + 1) * #(univ : Finset (Fin g)) = g + g := by
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    rw [← h₄]
    exact reflect_prod_torusFactor hx univ
  rw [← h₁, ← h₂]
  conv_lhs => rw [← h₃, coeff_reflect, revAt_le hk]

variable (x) in
/-- The elementary symmetric function `ẽ_m = e_{g + m}` of `x₁^{±1}, …, x_g^{±1}`, for an integer
`m`, zero for `|m| > g`. -/
noncomputable def shiftedEsymm (m : ℤ) : ℂ :=
  esymmOfInt (torusEigenvalues x) (g + m)

lemma shiftedEsymm_of_lt {m : ℤ} (hm : m < -g) : shiftedEsymm x m = 0 :=
  ite_eq_right fun h ↦ absurd h (by omega)

lemma shiftedEsymm_of_gt {m : ℤ} (hm : (g : ℤ) < m) : shiftedEsymm x m = 0 := by
  have h : 0 ≤ (g : ℤ) + m := by
    omega
  rw [shiftedEsymm, esymmOfInt, ite_eq_left h, Multiset.esymm,
    Multiset.powersetCard_eq_empty _ (by rw [card_torusEigenvalues]; omega)]
  simp

lemma shiftedEsymm_neg_natCast : shiftedEsymm x (-g) = 1 := by
  simp [shiftedEsymm, esymmOfInt]

lemma shiftedEsymm_neg (hx : ∀ j, x j ≠ 0) (m : ℤ) : shiftedEsymm x (-m) = shiftedEsymm x m := by
  by_cases h₁ : m < -g
  · rw [shiftedEsymm_of_lt h₁, shiftedEsymm_of_gt (by omega)]
  by_cases h₂ : (g : ℤ) < m
  · rw [shiftedEsymm_of_gt h₂, shiftedEsymm_of_lt (by omega)]
  have h₃ : 0 ≤ (g : ℤ) + m := by
    omega
  have h₄ : 0 ≤ (g : ℤ) + -m := by
    omega
  rw [shiftedEsymm, shiftedEsymm, esymmOfInt, esymmOfInt, ite_eq_left h₃, ite_eq_left h₄]
  have h₅ : ((g : ℤ) + -m).toNat = g + g - ((g : ℤ) + m).toNat := by
    omega
  rw [h₅, esymm_torusEigenvalues_eq hx (by omega)]

lemma sum_Icc_eq_add_sum_range (F : ℤ → ℂ) (N : ℕ) :
    ∑ b ∈ Finset.Icc (-(N : ℤ)) N, F b = F 0 + ∑ b ∈ range N, (F (b + 1) + F (-(b + 1))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert ((N : ℤ) + 1) (insert (-((N : ℤ) + 1)) (Finset.Icc (-(N : ℤ)) N)) := by
      ext b
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [h, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), ih,
      Finset.sum_range_succ]
    ring1

lemma eval_prod_torusFactor {y : ℂ} :
    (∏ j, torusFactor x j).eval y = ∑ k ∈ range (g + g + 1), shiftedEsymm x (g - k) * y ^ k := by
  have hdeg : (∏ j, torusFactor x j).natDegree < g + g + 1 := by
    have h : (∏ j, torusFactor x j).natDegree ≤ (1 + 1) * #(univ : Finset (Fin g)) :=
      natDegree_prod_torusFactor_le x univ
    rw [Finset.card_univ, Fintype.card_fin] at h
    omega
  rw [eval_eq_sum_range' hdeg]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k ≤ g + g := by
    simpa using hk
  rw [← map_prod_torusEigenvalues,
    Multiset.prod_X_add_C_coeff _ (by rw [card_torusEigenvalues]; exact hk'), card_torusEigenvalues,
    shiftedEsymm, esymmOfInt, ite_eq_left (by omega)]
  congr 2
  omega

lemma sum_Icc_shiftedEsymm_mul_zpow {y : ℂ} (hy : y ≠ 0) (hroot : (∏ j, torusFactor x j).eval y = 0)
    (a : ℤ) {N : ℕ} (ha : |a| + g ≤ N) :
    ∑ b ∈ Finset.Icc (-(N : ℤ)) N, shiftedEsymm x (a - b) * y ^ b = 0 := by
  have ha₁ : a + g ≤ N := by
    have h : a ≤ |a| := le_abs_self a
    omega
  have ha₂ : -(N : ℤ) ≤ a - g := by
    have h : -a ≤ |a| := neg_le_abs a
    omega
  have hsub : Finset.Icc (a - g) (a + g) ⊆ Finset.Icc (-(N : ℤ)) N :=
    Finset.Icc_subset_Icc ha₂ ha₁
  rw [← Finset.sum_subset hsub fun b _ hb ↦ ?_]
  · have himage : Finset.Icc (a - g) (a + g) = (range (g + g + 1)).image fun k : ℕ ↦ a - g + k := by
      ext b
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨(b - (a - g)).toNat, by omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩
        omega
    rw [himage, Finset.sum_image fun k₁ _ k₂ _ h ↦ by omega]
    have h₁ : ∀ k ∈ range (g + g + 1), shiftedEsymm x (a - (a - g + k)) * y ^ (a - g + k) =
        y ^ (a - g) * (shiftedEsymm x (g - k) * y ^ k) := fun k _ ↦ by
      rw [zpow_add₀ hy, zpow_natCast, show a - (a - g + k) = g - k by ring1]
      ring1
    rw [Finset.sum_congr rfl h₁, ← Finset.mul_sum, ← eval_prod_torusFactor, hroot, mul_zero]
  · simp only [Finset.mem_Icc, not_and_or] at hb
    rcases hb with h | h
    · rw [shiftedEsymm_of_gt (by omega), zero_mul]
    · rw [shiftedEsymm_of_lt (by omega), zero_mul]

lemma sum_range_shiftedEsymm_mul_sub {y : ℂ} (hy : y ≠ 0)
    (hroot : (∏ j, torusFactor x j).eval y = 0) (hroot' : (∏ j, torusFactor x j).eval y⁻¹ = 0)
    (a : ℤ) {N : ℕ} (ha : |a| + g ≤ N) : ∑ b ∈ range N,
      (shiftedEsymm x (a - (b + 1)) - shiftedEsymm x (a + (b + 1))) *
        (y ^ (b + 1) - y⁻¹ ^ (b + 1)) = 0 := by
  have h₁ : ∑ b ∈ Finset.Icc (-(N : ℤ)) N, shiftedEsymm x (a - b) * (y ^ b - y⁻¹ ^ b) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [sum_Icc_shiftedEsymm_mul_zpow hy hroot a ha,
      sum_Icc_shiftedEsymm_mul_zpow (inv_ne_zero hy) hroot' a ha, sub_zero]
  rw [sum_Icc_eq_add_sum_range] at h₁
  simp only [zpow_zero, sub_self, mul_zero, zero_add] at h₁
  rw [← h₁]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  have h₂ : y ^ (-((b : ℤ) + 1)) = y⁻¹ ^ (b + 1) := by
    rw [zpow_neg, inv_pow]
    norm_cast
  have h₃ : y⁻¹ ^ (-((b : ℤ) + 1)) = y ^ (b + 1) := by
    rw [zpow_neg, inv_zpow, inv_inv]
    norm_cast
  have h₄ : y ^ ((b : ℤ) + 1) = y ^ (b + 1) := by
    norm_cast
  have h₅ : y⁻¹ ^ ((b : ℤ) + 1) = y⁻¹ ^ (b + 1) := by
    norm_cast
  rw [h₂, h₃, h₄, h₅, sub_neg_eq_add]
  ring1

end Eigenvalues

section Partition

variable {g : ℕ} (c : Fin g → ℕ)

lemma highestWeight_antitone : Antitone (highestWeight c) := fun _ _ hij ↦
  Finset.sum_le_sum_of_subset (Finset.Ici_subset_Ici.mpr hij)

lemma highestWeight_le (i : Fin g) : highestWeight c i ≤ ∑ k, c k :=
  Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma lt_conjugateHighestWeight_iff (m : ℕ) (j : Fin g) :
    (j : ℕ) < conjugateHighestWeight c m ↔ m ≤ highestWeight c j := by
  constructor
  · intro h
    by_contra hm
    have hsub : ({i | m ≤ highestWeight c i} : Finset (Fin g)) ⊆ Finset.Iio j := fun i hi ↦ by
      rw [Finset.mem_Iio]
      by_contra hij
      exact hm ((Finset.mem_filter.mp hi).2.trans (highestWeight_antitone c (not_lt.mp hij)))
    have h₁ : conjugateHighestWeight c m ≤ #(Finset.Iio j) := Finset.card_le_card hsub
    rw [Fin.card_Iio] at h₁
    exact absurd h (not_lt.mpr h₁)
  · intro hm
    have hsub : Finset.Iic j ⊆ ({i | m ≤ highestWeight c i} : Finset (Fin g)) := fun i hi ↦
      Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        hm.trans (highestWeight_antitone c (Finset.mem_Iic.mp hi))⟩
    have h₁ : #(Finset.Iic j) ≤ conjugateHighestWeight c m := Finset.card_le_card hsub
    rw [Fin.card_Iic] at h₁
    omega

lemma conjugateHighestWeight_le (m : ℕ) : conjugateHighestWeight c m ≤ g :=
  (Finset.card_le_univ _).trans_eq (Fintype.card_fin g)

lemma conjugateHighestWeight_anti {m m' : ℕ} (h : m ≤ m') :
    conjugateHighestWeight c m' ≤ conjugateHighestWeight c m :=
  Finset.card_le_card fun i hi ↦ Finset.mem_filter.mpr
    ⟨Finset.mem_univ i, h.trans (Finset.mem_filter.mp hi).2⟩

lemma one_le_conjugateHighestWeight (i : Fin (∑ k, c k)) :
    1 ≤ conjugateHighestWeight c (i + 1) := by
  have hg : 0 < g := by
    rcases Nat.eq_zero_or_pos g with rfl | h
    · exact absurd i.2 (by simp)
    · exact h
  have h₁ : highestWeight c ⟨0, hg⟩ = ∑ k, c k := by
    refine Finset.sum_congr (Finset.eq_univ_of_forall fun k ↦ Finset.mem_Ici.mpr ?_) fun _ _ ↦ rfl
    exact Nat.zero_le k
  have h₂ : ((⟨0, hg⟩ : Fin g) : ℕ) < conjugateHighestWeight c (i + 1) :=
    (lt_conjugateHighestWeight_iff c _ _).mpr (by rw [h₁]; exact i.2)
  exact h₂

/-- The position `λ_{g - 1 - j} + j` in `{0, …, g + λ₀ - 1}`, for `j < g`, one less than the
exponent `λ_{g - 1 - j} + j + 1` of Weyl's numerator: these are increasing in `j`. -/
def weylPosition (j : Fin g) : Fin (g + ∑ k, c k) :=
  ⟨highestWeight c (Fin.rev j) + j, by
    have h₁ : highestWeight c (Fin.rev j) ≤ ∑ k, c k := highestWeight_le c _
    have h₂ : (j : ℕ) < g := j.2
    omega⟩

/-- The position `g + i - λ'_{i + 1}` in `{0, …, g + λ₀ - 1}`, for `i < λ₀`: the rows of the
determinant of Koike and Terada. -/
def conjugatePosition (i : Fin (∑ k, c k)) : Fin (g + ∑ k, c k) :=
  ⟨g + i - conjugateHighestWeight c (i + 1), by
    have h₁ : 1 ≤ conjugateHighestWeight c (i + 1) := one_le_conjugateHighestWeight c i
    have h₂ : (i : ℕ) < ∑ k, c k := i.2
    omega⟩

lemma strictMono_weylPosition : StrictMono (weylPosition c) := fun j j' h ↦ by
  have h₁ : highestWeight c (Fin.rev j) ≤ highestWeight c (Fin.rev j') :=
    highestWeight_antitone c (Fin.rev_le_rev.mpr h.le)
  simp only [weylPosition, Fin.mk_lt_mk]
  omega

lemma strictMono_conjugatePosition : StrictMono (conjugatePosition c) := fun i i' h ↦ by
  have h₁ : conjugateHighestWeight c (i' + 1) ≤ conjugateHighestWeight c (i + 1) :=
    conjugateHighestWeight_anti c (by have h₂ : (i : ℕ) < i' := h; omega)
  have h₂ : conjugateHighestWeight c (i + 1) ≤ g := conjugateHighestWeight_le c _
  simp only [conjugatePosition, Fin.mk_lt_mk]
  omega

lemma conjugatePosition_lt_weylPosition_iff (i : Fin (∑ k, c k)) (j : Fin g) :
    conjugatePosition c i < weylPosition c j ↔ (i : ℕ) + 1 ≤ highestWeight c (Fin.rev j) := by
  have h₁ : ((Fin.rev j : Fin g) : ℕ) < conjugateHighestWeight c (i + 1) ↔
      (i : ℕ) + 1 ≤ highestWeight c (Fin.rev j) := lt_conjugateHighestWeight_iff c _ _
  have h₂ : ((Fin.rev j : Fin g) : ℕ) = g - (j + 1) := Fin.val_rev j
  simp only [conjugatePosition, weylPosition, Fin.mk_lt_mk]
  omega

lemma conjugatePosition_ne_weylPosition (i : Fin (∑ k, c k)) (j : Fin g) :
    conjugatePosition c i ≠ weylPosition c j := by
  have h₁ : ((Fin.rev j : Fin g) : ℕ) < conjugateHighestWeight c (i + 1) ↔
      (i : ℕ) + 1 ≤ highestWeight c (Fin.rev j) := lt_conjugateHighestWeight_iff c _ _
  have h₂ : ((Fin.rev j : Fin g) : ℕ) = g - (j + 1) := Fin.val_rev j
  simp only [conjugatePosition, weylPosition, ne_eq, Fin.mk.injEq]
  omega

/-- The map with values the `weylPosition` on the first `g` positions and the `conjugatePosition` on
the others. -/
def positionMap : Fin (g + ∑ k, c k) → Fin (g + ∑ k, c k) :=
  Fin.addCases (motive := fun _ ↦ Fin (g + ∑ k, c k)) (weylPosition c) (conjugatePosition c)

lemma positionMap_castAdd (j : Fin g) : positionMap c (Fin.castAdd _ j) = weylPosition c j :=
  Fin.addCases_left j

lemma positionMap_natAdd (i : Fin (∑ k, c k)) :
    positionMap c (Fin.natAdd g i) = conjugatePosition c i :=
  Fin.addCases_right i

lemma injective_positionMap : Function.Injective (positionMap c) := by
  intro p q
  induction p using Fin.addCases with
  | left j =>
    induction q using Fin.addCases with
    | left j' =>
      intro h
      rw [positionMap_castAdd, positionMap_castAdd] at h
      rw [(strictMono_weylPosition c).injective h]
    | right i =>
      intro h
      rw [positionMap_castAdd, positionMap_natAdd] at h
      exact absurd h.symm (conjugatePosition_ne_weylPosition c i j)
  | right i =>
    induction q using Fin.addCases with
    | left j =>
      intro h
      rw [positionMap_natAdd, positionMap_castAdd] at h
      exact absurd h (conjugatePosition_ne_weylPosition c i j)
    | right i' =>
      intro h
      rw [positionMap_natAdd, positionMap_natAdd] at h
      rw [(strictMono_conjugatePosition c).injective h]

/-- The permutation `positionMap` of `{0, …, g + λ₀ - 1}`. -/
noncomputable def positionPerm : Equiv.Perm (Fin (g + ∑ k, c k)) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (injective_positionMap c))

lemma positionPerm_castAdd (j : Fin g) : positionPerm c (Fin.castAdd _ j) = weylPosition c j :=
  positionMap_castAdd c j

lemma positionPerm_natAdd (i : Fin (∑ k, c k)) :
    positionPerm c (Fin.natAdd g i) = conjugatePosition c i :=
  positionMap_natAdd c i

lemma sign_positionPerm :
    Perm.sign (positionPerm c) = ∏ i : Fin (∑ k, c k), (-1) ^ conjugateHighestWeight c (i + 1) := by
  rw [sign_eq_prod_of_strictMono (strictMono_weylPosition c) (strictMono_conjugatePosition c) _
    (positionPerm_castAdd c) (positionPerm_natAdd c), Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have h₁ (j : Fin g) : (if weylPosition c j < conjugatePosition c i then (1 : ℤˣ) else -1) =
      if (i : ℕ) + 1 ≤ highestWeight c (Fin.rev j) then -1 else 1 := by
    have h₀ :
        conjugatePosition c i < weylPosition c j ↔ (i : ℕ) + 1 ≤ highestWeight c (Fin.rev j) :=
      conjugatePosition_lt_weylPosition_iff c i j
    by_cases h : (i : ℕ) + 1 ≤ highestWeight c (Fin.rev j)
    · rw [ite_eq_right (h₀.mpr h).not_gt, ite_eq_left h]
    · have h₂ : weylPosition c j < conjugatePosition c i :=
        lt_of_le_of_ne (not_lt.mp (mt h₀.mp h)) (conjugatePosition_ne_weylPosition c i j).symm
      rw [ite_eq_left h₂, ite_eq_right h]
  simp_rw [h₁]
  have h₂ : ∏ j : Fin g, (if (i : ℕ) + 1 ≤ highestWeight c (Fin.revPerm j) then (-1 : ℤˣ) else 1) =
      ∏ j : Fin g, if (i : ℕ) + 1 ≤ highestWeight c j then (-1 : ℤˣ) else 1 :=
    Equiv.prod_comp Fin.revPerm fun j ↦ if (i : ℕ) + 1 ≤ highestWeight c j then (-1 : ℤˣ) else 1
  simp only [Fin.revPerm_apply] at h₂
  rw [h₂, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  rfl

end Partition

section Main

variable {g : ℕ} (c : Fin g → ℕ) {x : Fin g → ℂ}

variable (x) in
/-- The value `x_k ^ n - x_k ^ (-n)`. -/
noncomputable def weylEntry (k : Fin g) (n : ℕ) : ℂ :=
  x k ^ n - (x k)⁻¹ ^ n

variable (x) in
/-- The matrix `(x_k ^ (p + 1) - x_k ^ (-(p + 1)))`, of size `(g + λ₀) × g`. -/
noncomputable def weylColumns : Matrix (Fin (g + ∑ k, c k)) (Fin g) ℂ :=
  of fun p k ↦ weylEntry x k (p + 1)

variable (x) in
/-- The first `λ₀` rows of the matrix `(-1) ^ b (ẽ_{a - b} - ẽ_{a + b})`, with `a = i + 1` and
`b = p + 1`. -/
noncomputable def kernelRows : Matrix (Fin (∑ k, c k)) (Fin (g + ∑ k, c k)) ℂ :=
  of fun i p ↦ (-1) ^ ((p : ℕ) + 1) * (shiftedEsymm x ((i + 1 : ℤ) - ((p : ℕ) + 1 : ℤ)) -
    shiftedEsymm x ((i + 1 : ℤ) + ((p : ℕ) + 1 : ℤ)))

lemma kernelRows_mul_weylColumns (hx : ∀ j, x j ≠ 0) : kernelRows c x * weylColumns c x = 0 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.zero_apply]
  simp only [kernelRows, weylColumns, of_apply]
  have hy : -x k ≠ 0 := neg_ne_zero.mpr (hx k)
  have hroot : (∏ j, torusFactor x j).eval (-x k) = 0 := by
    rw [eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    simp [torusFactor]
  have hroot' : (∏ j, torusFactor x j).eval (-x k)⁻¹ = 0 := by
    rw [eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    simp [torusFactor]
  have hsum : ∑ b ∈ range (g + ∑ k, c k), (shiftedEsymm x ((i : ℤ) + 1 - ((b : ℤ) + 1)) -
      shiftedEsymm x ((i : ℤ) + 1 + ((b : ℤ) + 1))) * ((-x k) ^ (b + 1) - (-x k)⁻¹ ^ (b + 1)) = 0 :=
    sum_range_shiftedEsymm_mul_sub hy hroot hroot' ((i : ℤ) + 1) (by
      rw [abs_of_nonneg (by omega)]
      omega)
  rw [← Fin.sum_univ_eq_sum_range (fun b ↦ (shiftedEsymm x ((i : ℤ) + 1 - ((b : ℤ) + 1)) -
    shiftedEsymm x ((i : ℤ) + 1 + ((b : ℤ) + 1))) *
      ((-x k) ^ (b + 1) - (-x k)⁻¹ ^ (b + 1)))] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have h₂ : (-x k) ^ ((p : ℕ) + 1) - (-x k)⁻¹ ^ ((p : ℕ) + 1) =
      (-1) ^ ((p : ℕ) + 1) * weylEntry x k (p + 1) := by
    rw [weylEntry, inv_neg, neg_pow (x k), neg_pow (x k)⁻¹]
    ring1
  rw [h₂]
  ring1

lemma det_kernelRows_natAdd : ((kernelRows c x).submatrix id (Fin.natAdd g)).det =
    ∏ i : Fin (∑ k, c k), (-1 : ℂ) ^ (g + (i : ℕ) + 1) := by
  rw [det_of_isLowerTriangular]
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    have h₁ : ((i : ℤ) + 1) - (((Fin.natAdd g i : Fin (g + ∑ k, c k)) : ℕ) + 1 : ℤ) = -g := by
      simp only [Fin.val_natAdd]
      push_cast
      ring1
    simp only [submatrix_apply, id, kernelRows, of_apply]
    rw [h₁, shiftedEsymm_neg_natCast,
      shiftedEsymm_of_gt (by simp only [Fin.val_natAdd]; push_cast; omega), sub_zero, mul_one,
      Fin.val_natAdd]
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    simp only [submatrix_apply, id, kernelRows, of_apply]
    rw [shiftedEsymm_of_lt (by simp only [Fin.val_natAdd]; push_cast; omega),
      shiftedEsymm_of_gt (by simp only [Fin.val_natAdd]; push_cast; omega), sub_zero, mul_zero]

variable (x) in
/-- The matrix of Koike and Terada, whose determinant is `SatoTateGroup.symplecticSchur`. -/
noncomputable def koikeTeradaMatrix : Matrix (Fin (∑ k, c k)) (Fin (∑ k, c k)) ℂ :=
  of fun i j ↦ esymmOfInt (torusEigenvalues x) (conjugateHighestWeight c (i + 1) - i + j) -
    esymmOfInt (torusEigenvalues x) (conjugateHighestWeight c (i + 1) - i - j - 2)

lemma kernelRows_submatrix_positionPerm (hx : ∀ j, x j ≠ 0) :
    (kernelRows c x).submatrix id (positionPerm c ∘ Fin.natAdd g) =
      of fun i i' ↦ (-1) ^ ((conjugatePosition c i' : ℕ) + 1) * (koikeTeradaMatrix c x)ᵀ i i' := by
  ext i i'
  have hpos : (((conjugatePosition c i' : Fin _) : ℕ) : ℤ) =
      g + i' - conjugateHighestWeight c (i' + 1) := by
    have h₁ : conjugateHighestWeight c (i' + 1) ≤ g := conjugateHighestWeight_le c _
    simp only [conjugatePosition]
    omega
  simp only [submatrix_apply, id, Function.comp_apply, positionPerm_natAdd, kernelRows, of_apply]
  rw [← shiftedEsymm_neg hx ((i : ℤ) + 1 + (((conjugatePosition c i' : Fin _) : ℕ) + 1)),
    shiftedEsymm, shiftedEsymm, hpos]
  congr 3 <;> ring1

lemma det_kernelRows_positionPerm (hx : ∀ j, x j ≠ 0) :
    ((kernelRows c x).submatrix id (positionPerm c ∘ Fin.natAdd g)).det =
      (∏ i : Fin (∑ k, c k), (-1 : ℂ) ^ ((conjugatePosition c i : ℕ) + 1)) *
        symplecticSchur c (torusEigenvalues x) := by
  rw [kernelRows_submatrix_positionPerm c hx, det_mul_row, det_transpose]
  rfl

lemma prod_neg_one_pow_add_one : ∏ i : Fin (∑ k, c k), (-1 : ℂ) ^ (g + (i : ℕ) + 1) =
    ((Perm.sign (positionPerm c) : ℤ) : ℂ) *
      ∏ i : Fin (∑ k, c k), (-1 : ℂ) ^ ((conjugatePosition c i : ℕ) + 1) := by
  have h₁ : ((Perm.sign (positionPerm c) : ℤ) : ℂ) =
      ∏ i : Fin (∑ k, c k), (-1 : ℂ) ^ conjugateHighestWeight c (i + 1) := by
    rw [sign_positionPerm]
    simp
  rw [h₁, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← pow_add]
  congr 1
  have h₂ : conjugateHighestWeight c (i + 1) ≤ g := conjugateHighestWeight_le c _
  simp only [conjugatePosition]
  omega

/-- **The identity of Koike and Terada**: the symplectic Schur function of `x₁^{±1}, …, x_g^{±1}`
is the quotient in Weyl's character formula for `USp(2g)`, for the dominant weight with exponent
vector `c`, that is,
`sp_λ · det(x_j^{g - i} - x_j^{-(g - i)}) = det(x_j^{λᵢ + g - i} - x_j^{-(λᵢ + g - i)})`
with `0`-based indices `i`. -/
lemma symplecticSchur_mul_det (hx : ∀ j, x j ≠ 0) :
    symplecticSchur c (torusEigenvalues x) * (of fun i j : Fin g ↦ weylEntry x j (g - i)).det =
      (of fun i j : Fin g ↦ weylEntry x j (highestWeight c i + g - i)).det := by
  have h₁ : ((weylColumns c x).submatrix (positionPerm c ∘ Fin.castAdd _) id).det *
      ((kernelRows c x).submatrix id (Fin.natAdd g)).det =
        (Perm.sign (positionPerm c) : ℤ) *
          ((weylColumns c x).submatrix (Fin.castAdd _) id).det *
            ((kernelRows c x).submatrix id (positionPerm c ∘ Fin.natAdd g)).det :=
    det_submatrix_mul_det_submatrix_of_mul_eq_zero (weylColumns c x) (kernelRows c x)
      (kernelRows_mul_weylColumns c hx) (positionPerm c)
  have hnum : (weylColumns c x).submatrix (positionPerm c ∘ Fin.castAdd _) id =
      (of fun i j : Fin g ↦
        weylEntry x j (highestWeight c i + g - i)).submatrix Fin.revPerm id := by
    ext j k
    simp only [submatrix_apply, Function.comp_apply, positionPerm_castAdd, weylColumns, of_apply,
      Fin.revPerm_apply]
    congr 1
    have h₂ : ((Fin.rev j : Fin g) : ℕ) = g - (j + 1) := Fin.val_rev j
    have h₃ : (j : ℕ) < g := j.2
    simp only [weylPosition]
    omega
  have hden : (weylColumns c x).submatrix (Fin.castAdd _) id =
      (of fun i j : Fin g ↦ weylEntry x j (g - i)).submatrix Fin.revPerm id := by
    ext j k
    simp only [submatrix_apply, weylColumns, of_apply, Fin.revPerm_apply, Fin.val_castAdd]
    congr 1
    have h₂ : ((Fin.rev j : Fin g) : ℕ) = g - (j + 1) := Fin.val_rev j
    omega
  rw [hnum, hden, det_permute, det_permute, det_kernelRows_natAdd, det_kernelRows_positionPerm c hx,
    prod_neg_one_pow_add_one] at h₁
  have hne : ((Perm.sign (Fin.revPerm (n := g)) : ℤ) : ℂ) *
      (((Perm.sign (positionPerm c) : ℤ) : ℂ) *
        ∏ i : Fin (∑ k, c k), (-1 : ℂ) ^ ((conjugatePosition c i : ℕ) + 1)) ≠ 0 := by
    refine mul_ne_zero (Int.cast_ne_zero.mpr (Units.ne_zero _)) (mul_ne_zero
      (Int.cast_ne_zero.mpr (Units.ne_zero _)) (Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_))
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  refine mul_left_cancel₀ hne ?_
  linear_combination -h₁

end Main

end SatoTateGroup
