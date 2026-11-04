import LeanBridge.ForMathlib.Data.Matrix.Block
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.HeckeRing
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParabolicDecomposition
import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# The Iwasawa decomposition of the Hecke monoid of `Sp(2g, ℤ)`

Every rational symplectic similitude `x` with positive multiplier is `γ⁻¹ b` with `γ ∈ Sp(2g, ℤ)`
and `b` in the Borel subgroup `B` of the block upper triangular similitudes `(A, B; 0, D)` with `A`
upper triangular. The proof clears the columns of the left half of `x` one at a time by left
multiplication with integral symplectic matrices: in the `j`-th column, the integral `SL(2)`s on
the coordinate pairs `(e_c, f_c)`, `c ≥ j`, clear the `f`-part, the entries `f_c`, `c < j`, being
already zero by the symplectic relations with the earlier columns; then a rotation
`(U, 0; 0, U⁻ᵀ)`, `U ∈ SL(g, ℤ)` fixing `e_0, …, e_{j-1}`, clears the entries `e_c`, `c > j`.

So every right coset `Γx` of `Γ = Sp(2g, ℤ)` in the Hecke monoid `S` meets `B`, the fact behind the
Satake map of the local Hecke algebra of `Sp(2g, ℤ)` (Andrianov, *Quadratic forms and Hecke
operators*, Lemma 3.3.1 and §3.3.3, with the opposite Borel subgroup).

## Main definitions

* `SiegelUpperHalfSpace.siegelBorel`: the Borel subgroup `B` of `GSp(2g, ℚ)⁺`.
* `SiegelUpperHalfSpace.borelDiag`: the diagonal entries of the upper left block of `b ∈ B`.

## Main results

* `SiegelUpperHalfSpace.exists_mem_heckeGamma_mul_mem_siegelBorel`: every `x ∈ GSp(2g, ℚ)⁺` has
  `γx ∈ B` for some `γ ∈ Sp(2g, ℤ)`.
-/

open Matrix

open scoped MatrixGroups

namespace SiegelUpperHalfSpace

variable {n : ℕ}

/-! ### The integral `SL(2)` on a pair of coordinates -/

section Pair

variable {j i c : Fin n} (hji : j ≠ i) (M : SL(2, ℤ)) (b : Fin n → ℚ)

/-- `Fin n` as the pair of indices `j, i` together with the other indices. -/
private def pairEquiv : Fin 2 ⊕ {c : Fin n // c ≠ j ∧ c ≠ i} ≃ Fin n where
  toFun := Sum.elim ![j, i] Subtype.val
  invFun c := if hj : c = j then .inl 0 else if hi : c = i then .inl 1 else .inr ⟨c, hj, hi⟩
  left_inv := by
    rintro (a | ⟨c, hcj, hci⟩)
    · fin_cases a <;> simp [hji.symm]
    · simp [hcj, hci]
  right_inv c := by
    by_cases hj : c = j
    · simp [hj]
    · by_cases hi : c = i <;> simp [hj, hi, hji.symm]

/-- The element of `SL(n, ℤ)` acting by `M ∈ SL(2, ℤ)` on the coordinates `j, i` and trivially on
the others. -/
private def pairEmbed : SL(n, ℤ) :=
  ⟨reindex (pairEquiv hji) (pairEquiv hji) (fromBlocks (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 1), by
    rw [det_reindex_self, det_fromBlocks_zero₂₁, det_one, mul_one, M.2]⟩

private lemma pairEquiv_symm_left : (pairEquiv hji).symm j = .inl 0 := by
  simp [pairEquiv]

private lemma pairEquiv_symm_right : (pairEquiv hji).symm i = .inl 1 := by
  simp [pairEquiv, hji.symm]

private lemma pairEquiv_symm_other (hcj : c ≠ j) (hci : c ≠ i) :
    (pairEquiv hji).symm c = .inr ⟨c, hcj, hci⟩ := by
  simp [pairEquiv, hcj, hci]

private lemma pairEmbed_apply_other (hcj : c ≠ j) (hci : c ≠ i) (a : Fin n) :
    (pairEmbed hji M : Matrix (Fin n) (Fin n) ℤ) a c = if a = c then 1 else 0 := by
  by_cases haj : a = j
  · subst haj
    simp [pairEmbed, pairEquiv_symm_left, pairEquiv_symm_other hji hcj hci, Ne.symm hcj]
  · by_cases hai : a = i
    · subst hai
      simp [pairEmbed, pairEquiv_symm_right, pairEquiv_symm_other hji hcj hci, Ne.symm hci]
    · simp [pairEmbed, pairEquiv_symm_other hji haj hai, pairEquiv_symm_other hji hcj hci,
        one_apply]

private lemma pairEmbed_apply_pairEquiv (a : Fin n) (x : Fin 2 ⊕ {c : Fin n // c ≠ j ∧ c ≠ i}) :
    (pairEmbed hji M : Matrix (Fin n) (Fin n) ℤ) a (pairEquiv hji x) =
      fromBlocks (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 1 ((pairEquiv hji).symm a) x := by
  simp [pairEmbed]

private lemma sum_pairEmbed_right :
    ∑ m, ((pairEmbed hji M : Matrix (Fin n) (Fin n) ℤ) i m : ℚ) * b m =
      (M 1 0 : ℚ) * b j + (M 1 1 : ℚ) * b i := by
  rw [← (pairEquiv hji).sum_comp, Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [pairEmbed_apply_pairEquiv, pairEquiv_symm_right]
  simp [pairEquiv]

private lemma sum_pairEmbed_other (hcj : c ≠ j) (hci : c ≠ i) :
    ∑ m, ((pairEmbed hji M : Matrix (Fin n) (Fin n) ℤ) c m : ℚ) * b m = b c := by
  rw [← (pairEquiv hji).sum_comp, Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [pairEmbed_apply_pairEquiv, pairEquiv_symm_other hji hcj hci]
  simp [pairEquiv, one_apply]

end Pair

variable (U : SL(n, ℤ)) (a : Fin n → ℚ)

private lemma sum_mul_SL_apply (P : SL(n, ℤ)) (c : Fin n) :
    ∑ m, (((P * U : SL(n, ℤ)) : Matrix (Fin n) (Fin n) ℤ) c m : ℚ) * a m =
      ∑ l, ((P : Matrix (Fin n) (Fin n) ℤ) c l : ℚ) *
        ∑ m, ((U : Matrix (Fin n) (Fin n) ℤ) l m : ℚ) * a m := by
  simp only [SpecialLinearGroup.coe_mul, mul_apply, Int.cast_sum, Int.cast_mul, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

private lemma exists_SL_fix_mulVec_eq_zero (j : Fin n) : ∃ U : SL(n, ℤ),
    (∀ k : Fin n, k < j → ∀ c, (U : Matrix (Fin n) (Fin n) ℤ) c k = if c = k then 1 else 0) ∧
      ∀ c : Fin n, j < c → ∑ m, ((U : Matrix (Fin n) (Fin n) ℤ) c m : ℚ) * a m = 0 := by
  suffices h : ∀ t : ℕ, ∃ U : SL(n, ℤ),
      (∀ k : Fin n, k < j → ∀ c, (U : Matrix (Fin n) (Fin n) ℤ) c k = if c = k then 1 else 0) ∧
        ∀ c : Fin n, j < c → (c : ℕ) < t →
          ∑ m, ((U : Matrix (Fin n) (Fin n) ℤ) c m : ℚ) * a m = 0 by
    rcases h n with ⟨U, hU, hUa⟩
    exact ⟨U, hU, fun c hc ↦ hUa c hc c.2⟩
  intro t
  induction t with
  | zero => exact ⟨1, fun k _ c ↦ by simp [one_apply], fun c _ hc ↦ absurd hc (Nat.not_lt_zero _)⟩
  | succ t ih =>
    rcases ih with ⟨U, hU, hUa⟩
    by_cases ht : ∃ h : t < n, j < ⟨t, h⟩
    · rcases ht with ⟨htn, hjt⟩
      have hji : j ≠ ⟨t, htn⟩ := hjt.ne
      rcases SymplecticGroup.exists_SL2Z (∑ m, ((U : Matrix (Fin n) (Fin n) ℤ) j m : ℚ) * a m)
        (∑ m, ((U : Matrix (Fin n) (Fin n) ℤ) ⟨t, htn⟩ m : ℚ) * a m) with ⟨M, hM⟩
      refine ⟨pairEmbed hji M * U, fun k hk c ↦ ?_, fun c hjc hct ↦ ?_⟩
      · rw [SpecialLinearGroup.coe_mul, mul_apply, Finset.sum_eq_single k, hU k hk k,
          ite_eq_left rfl, mul_one, pairEmbed_apply_other hji M hk.ne (hk.trans hjt).ne]
        · intro m _ hmk
          rw [hU k hk m, ite_eq_right hmk, mul_zero]
        · simp
      · rw [sum_mul_SL_apply]
        by_cases hc : c = ⟨t, htn⟩
        · subst hc
          rw [sum_pairEmbed_right hji M _, hM]
        · rw [sum_pairEmbed_other hji M _ hjc.ne' hc]
          exact hUa c hjc <| lt_of_le_of_ne (Nat.lt_succ_iff.mp hct) fun h ↦ hc (Fin.ext h)
    · refine ⟨U, hU, fun c hjc hct ↦ hUa c hjc <| lt_of_le_of_ne (Nat.lt_succ_iff.mp hct) ?_⟩
      rintro rfl
      exact ht ⟨c.2, hjc⟩

/-! ### Two families of integral symplectic matrices -/

variable (N : Fin n → SL(2, ℤ))

/-- The integral symplectic matrix acting by `N c ∈ SL(2, ℤ)` on each coordinate pair
`(e_c, f_c)`. -/
private def diagSL : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ :=
  fromBlocks (diagonal fun c ↦ (N c : Matrix (Fin 2) (Fin 2) ℤ) 0 0)
    (diagonal fun c ↦ (N c : Matrix (Fin 2) (Fin 2) ℤ) 0 1)
    (diagonal fun c ↦ (N c : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (diagonal fun c ↦ (N c : Matrix (Fin 2) (Fin 2) ℤ) 1 1)

private lemma diagSL_mem : diagSL N ∈ symplecticGroup (Fin n) ℤ := by
  refine SymplecticGroup.fromBlocks_mem_iff.mpr ⟨?_, ?_, ?_⟩
  on_goal 3 =>
    rw [diagonal_transpose, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal,
      diagonal_sub, ← diagonal_one]
    exact congrArg diagonal <| funext fun c ↦ by
      have h : (N c : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := (N c).2
      rw [det_fin_two] at h
      linear_combination h
  all_goals simp only [diagonal_transpose, diagonal_mul_diagonal, mul_comm]

/-- The integral symplectic matrix `(U, 0; 0, U⁻ᵀ)` of `U ∈ SL(n, ℤ)`. -/
private def rotSL : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ :=
  fromBlocks (U : Matrix (Fin n) (Fin n) ℤ) 0 0 ((U⁻¹ : SL(n, ℤ)) : Matrix (Fin n) (Fin n) ℤ)ᵀ

private lemma rotSL_mem : rotSL U ∈ symplecticGroup (Fin n) ℤ := by
  refine SymplecticGroup.fromBlocks_mem_iff.mpr ⟨?_, ?_, ?_⟩
  on_goal 3 =>
    rw [transpose_zero, Matrix.zero_mul, sub_zero, ← transpose_mul, ← SpecialLinearGroup.coe_mul,
      inv_mul_cancel, SpecialLinearGroup.coe_one, transpose_one]
  all_goals simp

/-! ### Clearing the columns one at a time -/

section Columns

variable (y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) (s : Fin n ⊕ Fin n)

private lemma diagSL_mul_apply_inl (c : Fin n) :
    ((diagSL N).map (Int.castRingHom ℚ) * y) (.inl c) s =
      ((N c : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℚ) * y (.inl c) s +
        ((N c : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℚ) * y (.inr c) s := by
  simp [diagSL, mul_apply, diagonal_apply]

private lemma diagSL_mul_apply_inr (c : Fin n) :
    ((diagSL N).map (Int.castRingHom ℚ) * y) (.inr c) s =
      ((N c : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℚ) * y (.inl c) s +
        ((N c : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℚ) * y (.inr c) s := by
  simp [diagSL, mul_apply, diagonal_apply]

private lemma rotSL_mul_apply_inl (c : Fin n) : ((rotSL U).map (Int.castRingHom ℚ) * y) (.inl c) s =
    ∑ m, ((U : Matrix (Fin n) (Fin n) ℤ) c m : ℚ) * y (.inl m) s := by
  simp [rotSL, mul_apply]

private lemma rotSL_mul_apply_inr (c : Fin n) : ((rotSL U).map (Int.castRingHom ℚ) * y) (.inr c) s =
    ∑ m, ((U⁻¹ : SL(n, ℤ)) m c : ℚ) * y (.inr m) s := by
  simp [rotSL, mul_apply]

private lemma transpose_mul_J_mul_apply (q : Fin n ⊕ Fin n) : (yᵀ * J (Fin n) ℚ * y) q s =
    ∑ c, (y (.inr c) q * y (.inl c) s - y (.inl c) q * y (.inr c) s) := by
  simp [J, mul_apply, one_apply]
  exact (sub_eq_add_neg _ _).symm

/-- The columns `e_k`, `k < j`, of the left half of `y` are those of an element of the Borel
subgroup: `y e_k ∈ span(e_0, …, e_k)`. -/
private def IsBorelPrefix (j : ℕ) : Prop :=
  ∀ k : Fin n, (k : ℕ) < j → (∀ c, y (.inr c) (.inl k) = 0) ∧ ∀ c, k < c → y (.inl c) (.inl k) = 0

variable {y} {j : ℕ} {r : ℚ}

private lemma transpose_mul_J_mul_apply_inl (hp : IsBorelPrefix y j) {k : Fin n}
    (hk : (k : ℕ) < j) :
    (yᵀ * J (Fin n) ℚ * y) (.inl k) s = -∑ c, y (.inl c) (.inl k) * y (.inr c) s := by
  rw [transpose_mul_J_mul_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun c _ ↦ by rw [(hp k hk).1 c, zero_mul, zero_sub]

private lemma inr_eq_zero_of_isBorelPrefix (hp : IsBorelPrefix y j) {m : ℕ} (hm : m ≤ j)
    (hdiag : ∀ k : Fin n, (k : ℕ) < m → y (.inl k) (.inl k) ≠ 0)
    (hs : ∀ k : Fin n, (k : ℕ) < m → (yᵀ * J (Fin n) ℚ * y) (.inl k) s = 0) :
    ∀ k : Fin n, (k : ℕ) < m → y (.inr k) s = 0 := by
  suffices h : ∀ k : ℕ, ∀ hkn : k < n, k < m → y (.inr ⟨k, hkn⟩) s = 0 from
    fun k hk ↦ h k k.2 hk
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkn hk
    have h : (yᵀ * J (Fin n) ℚ * y) (.inl ⟨k, hkn⟩) s = 0 := hs ⟨k, hkn⟩ hk
    rw [transpose_mul_J_mul_apply_inl s hp (hk.trans_le hm), neg_eq_zero,
      Finset.sum_eq_single ⟨k, hkn⟩] at h
    · exact (mul_eq_zero.mp h).resolve_left (hdiag _ hk)
    · intro c _ hck
      rcases lt_or_gt_of_ne hck with hck | hck
      · have hck' : (c : ℕ) < k := hck
        rw [ih c hck' c.2 (hck'.trans hk), mul_zero]
      · rw [(hp ⟨k, hkn⟩ (hk.trans_le hm)).2 c hck, zero_mul]
    · simp

private lemma diag_ne_zero_of_isBorelPrefix (hy : yᵀ * J (Fin n) ℚ * y = r • J (Fin n) ℚ)
    (hr : r ≠ 0) (hp : IsBorelPrefix y j) : ∀ k : Fin n, (k : ℕ) < j → y (.inl k) (.inl k) ≠ 0 := by
  have hJ (a c : Fin n) :
      (yᵀ * J (Fin n) ℚ * y) (.inl a) (.inr c) = -(r * if a = c then 1 else 0) := by
    rw [hy]
    simp [J, one_apply]
  suffices h : ∀ k : ℕ, ∀ hkn : k < n, k < j → y (.inl ⟨k, hkn⟩) (.inl ⟨k, hkn⟩) ≠ 0 from
    fun k hk ↦ h k k.2 hk
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkn hk h0
    have hz : ∀ c : Fin n, (c : ℕ) < k → y (.inr c) (.inr ⟨k, hkn⟩) = 0 :=
      inr_eq_zero_of_isBorelPrefix (.inr ⟨k, hkn⟩) hp hk.le
        (fun k' hk' ↦ ih k' hk' k'.2 (hk'.trans hk)) fun k' hk' ↦ by
          rw [hJ, ite_eq_right fun h ↦ hk'.ne (congrArg Fin.val h), mul_zero, neg_zero]
    have h : (yᵀ * J (Fin n) ℚ * y) (.inl ⟨k, hkn⟩) (.inr ⟨k, hkn⟩) =
        -(r * if (⟨k, hkn⟩ : Fin n) = ⟨k, hkn⟩ then 1 else 0) :=
      hJ ⟨k, hkn⟩ ⟨k, hkn⟩
    rw [transpose_mul_J_mul_apply_inl _ hp hk, Finset.sum_eq_single ⟨k, hkn⟩, h0, zero_mul,
      neg_zero, ite_eq_left rfl, mul_one, zero_eq_neg] at h
    · exact hr h
    · intro c _ hck
      rcases lt_or_gt_of_ne hck with hck | hck
      · rw [hz c hck, mul_zero]
      · rw [(hp ⟨k, hkn⟩ hk).2 c hck, zero_mul]
    · simp

private lemma exists_isBorelPrefix_succ (hy : yᵀ * J (Fin n) ℚ * y = r • J (Fin n) ℚ) (hr : r ≠ 0)
    (hp : IsBorelPrefix y j) (hjn : j < n) :
    ∃ g ∈ symplecticGroup (Fin n) ℤ, IsBorelPrefix (g.map (Int.castRingHom ℚ) * y) (j + 1) := by
  have hw : ∀ k : Fin n, (k : ℕ) < j → y (.inr k) (.inl ⟨j, hjn⟩) = 0 :=
    inr_eq_zero_of_isBorelPrefix _ hp le_rfl (diag_ne_zero_of_isBorelPrefix hy hr hp) fun k hk ↦ by
      rw [hy]
      simp [J]
  choose M hM using fun c : Fin n ↦
    SymplecticGroup.exists_SL2Z (y (.inl c) (.inl ⟨j, hjn⟩)) (y (.inr c) (.inl ⟨j, hjn⟩))
  let N : Fin n → SL(2, ℤ) := fun c ↦ if (c : ℕ) < j then 1 else M c
  have hN₁ (c : Fin n) (hc : (c : ℕ) < j) : N c = 1 := ite_eq_left hc
  have hN₂ (c : Fin n) (hc : ¬(c : ℕ) < j) : N c = M c := ite_eq_right hc
  have h₁ : IsBorelPrefix ((diagSL N).map (Int.castRingHom ℚ) * y) j := fun k hk ↦ by
    refine ⟨fun c ↦ ?_, fun c hkc ↦ ?_⟩
    · rw [diagSL_mul_apply_inr, (hp k hk).1 c, mul_zero, add_zero]
      by_cases hc : (c : ℕ) < j
      · simp [hN₁ c hc]
      · rw [(hp k hk).2 c (Fin.lt_def.mpr (hk.trans_le (not_lt.mp hc))), mul_zero]
    · rw [diagSL_mul_apply_inl, (hp k hk).1 c, (hp k hk).2 c hkc, mul_zero, mul_zero, add_zero]
  have h₁w (c : Fin n) : ((diagSL N).map (Int.castRingHom ℚ) * y) (.inr c) (.inl ⟨j, hjn⟩) = 0 := by
    rw [diagSL_mul_apply_inr]
    by_cases hc : (c : ℕ) < j
    · simp [hN₁ c hc, hw c hc]
    · rw [hN₂ c hc, hM c]
  rcases exists_SL_fix_mulVec_eq_zero
    (fun c ↦ ((diagSL N).map (Int.castRingHom ℚ) * y) (.inl c) (.inl ⟨j, hjn⟩)) ⟨j, hjn⟩ with
    ⟨U, hU, hUa⟩
  refine ⟨rotSL U * diagSL N, mul_mem (rotSL_mem U) (diagSL_mem N), fun k hk ↦ ?_⟩
  rw [Matrix.map_mul, Matrix.mul_assoc]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
  · refine ⟨fun c ↦ ?_, fun c hkc ↦ ?_⟩
    · rw [rotSL_mul_apply_inr]
      exact Finset.sum_eq_zero fun m _ ↦ by rw [(h₁ k hk).1 m, mul_zero]
    · rw [rotSL_mul_apply_inl]
      refine Finset.sum_eq_zero fun m _ ↦ ?_
      rcases le_or_gt m k with hmk | hmk
      · rw [hU m (lt_of_le_of_lt hmk hk) c, ite_eq_right fun h ↦ (h ▸ hkc).not_ge hmk,
          Int.cast_zero, zero_mul]
      · rw [(h₁ k hk).2 m hmk, mul_zero]
  · have hk' : k = ⟨j, hjn⟩ := Fin.ext hk
    subst hk'
    refine ⟨fun c ↦ ?_, fun c hkc ↦ ?_⟩
    · rw [rotSL_mul_apply_inr]
      exact Finset.sum_eq_zero fun m _ ↦ by rw [h₁w m, mul_zero]
    · rw [rotSL_mul_apply_inl]
      exact hUa c hkc

variable (j) in
private lemma exists_isBorelPrefix (hy : yᵀ * J (Fin n) ℚ * y = r • J (Fin n) ℚ) (hr : r ≠ 0)
    (hj : j ≤ n) :
    ∃ g ∈ symplecticGroup (Fin n) ℤ, IsBorelPrefix (g.map (Int.castRingHom ℚ) * y) j := by
  induction j with
  | zero => exact ⟨1, one_mem _, fun k hk ↦ absurd hk (Nat.not_lt_zero _)⟩
  | succ j ih =>
    rcases ih (Nat.le_of_succ_le hj) with ⟨g, hg, hp⟩
    have hgJ : (g.map (Int.castRingHom ℚ))ᵀ * J (Fin n) ℚ * g.map (Int.castRingHom ℚ) =
        J (Fin n) ℚ :=
      SymplecticGroup.mem_iff'.mp (SymplecticGroup.map_mem hg (Int.castRingHom ℚ))
    have hy' : (g.map (Int.castRingHom ℚ) * y)ᵀ * J (Fin n) ℚ * (g.map (Int.castRingHom ℚ) * y) =
        r • J (Fin n) ℚ := by
      have e : (g.map (Int.castRingHom ℚ) * y)ᵀ * J (Fin n) ℚ * (g.map (Int.castRingHom ℚ) * y) =
          yᵀ * ((g.map (Int.castRingHom ℚ))ᵀ * J (Fin n) ℚ * g.map (Int.castRingHom ℚ)) * y := by
        simp only [transpose_mul, Matrix.mul_assoc]
      rw [e, hgJ, hy]
    rcases exists_isBorelPrefix_succ hy' hr hp hj with ⟨g', hg', hp'⟩
    refine ⟨g' * g, mul_mem hg' hg, ?_⟩
    rwa [Matrix.map_mul, Matrix.mul_assoc]

end Columns

/-! ### The Borel subgroup -/

variable {x : GL (Fin n ⊕ Fin n) ℚ}

variable (n) in
/-- The **Borel subgroup** `B` of `GSp(2g, ℚ)⁺` (Andrianov, §3.3.3, with the opposite Borel): the
symplectic similitudes `(A, B; 0, D)` with positive multiplier `r` and `A` upper triangular, so that
`D = r A⁻ᵀ` is lower triangular. -/
def siegelBorel : Subgroup (GL (Fin n ⊕ Fin n) ℚ) where
  carrier := {x | x ∈ gspPlusGL (Fin n) ∧
    (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ).toBlocks₂₁ = 0 ∧
      (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ).toBlocks₁₁.IsUpperTriangular}
  mul_mem' {x y} hx hy := by
    refine ⟨mul_mem hx.1 hy.1, ?_, ?_⟩
    · rw [Units.val_mul, toBlocks₂₁_mul, hx.2.1, hy.2.1, Matrix.zero_mul, Matrix.mul_zero,
        add_zero]
    · rw [Units.val_mul, toBlocks₁₁_mul, hy.2.1, Matrix.mul_zero, add_zero]
      exact hx.2.2.mul hy.2.2
  one_mem' := by
    refine ⟨one_mem _, ?_, ?_⟩
    · rw [Units.val_one, ← fromBlocks_one, toBlocks_fromBlocks₂₁]
    · rw [Units.val_one, ← fromBlocks_one, toBlocks_fromBlocks₁₁]
      exact blockTriangular_one
  inv_mem' {x} hx := by
    have h₁ : ((x⁻¹ : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) *
        (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) = 1 :=
      Units.inv_mul x
    have h₂₁ :
        ((x⁻¹ : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ).toBlocks₂₁ *
          (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ).toBlocks₁₁ = 0 := by
      simpa only [toBlocks₂₁_mul, hx.2.1, Matrix.mul_zero, add_zero, ← fromBlocks_one,
        toBlocks_fromBlocks₂₁] using congrArg toBlocks₂₁ h₁
    have h₁₁ :
        ((x⁻¹ : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ).toBlocks₁₁ *
          (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ).toBlocks₁₁ = 1 := by
      simpa only [toBlocks₁₁_mul, hx.2.1, Matrix.mul_zero, add_zero, ← fromBlocks_one,
        toBlocks_fromBlocks₁₁] using congrArg toBlocks₁₁ h₁
    have : Invertible (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ).toBlocks₁₁ :=
      invertibleOfLeftInverse _ _ h₁₁
    refine ⟨(gspPlusGroup (Fin n)).inv_mem hx.1, ?_, ?_⟩
    · rw [← Matrix.mul_one (toBlocks₂₁ _), ← mul_invOf_self
        (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ).toBlocks₁₁, ← Matrix.mul_assoc, h₂₁,
        Matrix.zero_mul]
    · rw [← inv_eq_left_inv h₁₁]
      exact blockTriangular_inv_of_blockTriangular hx.2.2

variable (b b' : siegelBorel n) (j : Fin n)

/-- The `j`-th diagonal entry `A_jj` of the upper left block `A` of `b ∈ B`. -/
def borelDiag : ℚ :=
  ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) (.inl j) (.inl j)

lemma borelDiag_mul : borelDiag (b * b') j = borelDiag b j * borelDiag b' j :=
  (congrFun (congrFun (toBlocks₁₁_mul _ _) j) j).trans <| by
    rw [b'.2.2.1, Matrix.mul_zero, add_zero, mul_apply_diag_of_isUpperTriangular b.2.2.2 b'.2.2.2]
    rfl

lemma borelDiag_one : borelDiag (1 : siegelBorel n) j = 1 :=
  one_apply_eq _

lemma borelDiag_ne_zero : borelDiag b j ≠ 0 := by
  have h : borelDiag (b⁻¹ * b) j = borelDiag b⁻¹ j * borelDiag b j := borelDiag_mul b⁻¹ b j
  rw [inv_mul_cancel, borelDiag_one] at h
  exact right_ne_zero_of_mul (h ▸ one_ne_zero)

/-- **The Iwasawa decomposition of `GSp(2g, ℚ)⁺`**: for every `x ∈ GSp(2g, ℚ)⁺` there is
`γ ∈ Sp(2g, ℤ)` with `γx` in the Borel subgroup `B`; so every right coset `Γx` of `Γ = Sp(2g, ℤ)`
in the Hecke monoid meets `B`. -/
lemma exists_mem_heckeGamma_mul_mem_siegelBorel (hx : x ∈ gspPlusGL (Fin n)) :
    ∃ γ ∈ heckeGamma (Fin n), γ * x ∈ siegelBorel n := by
  rcases hx with ⟨r, hr, h⟩
  rcases exists_isBorelPrefix n h hr.ne' le_rfl with ⟨g, hg, hp⟩
  have hγ : spToGL (Fin n) ⟨g, hg⟩ ∈ heckeGamma (Fin n) := ⟨⟨g, hg⟩, trivial, rfl⟩
  refine ⟨_, hγ, mul_mem (heckeMonoid_le_gspPlusGL (heckeGamma_le_heckeMonoid hγ)) ⟨r, hr, h⟩,
    ?_, fun c k hkc ↦ (hp k k.2).2 c hkc⟩
  ext c k
  exact (hp k k.2).1 c

end SiegelUpperHalfSpace
