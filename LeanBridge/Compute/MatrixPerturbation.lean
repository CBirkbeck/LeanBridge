import Mathlib

section

open Matrix

lemma isClosed_unitary {R : Type*} [Monoid R] [StarMul R] [TopologicalSpace R] [T1Space R]
    [ContinuousStar R] [ContinuousMul R] :
    IsClosed (unitary R : Set R) := by
  let f : R → R × R := fun u ↦ (star u * u, u * star u)
  have : IsClosed (f ⁻¹' {(1, 1)}) := IsClosed.preimage (by fun_prop) isClosed_singleton
  convert this
  ext u
  simp [f, unitary.mem_iff]

lemma isCompact_unitaryGroup {n : Type*} [DecidableEq n] [Fintype n] :
    IsCompact (unitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
  open Norms.Elementwise in
  apply IsCompact.of_isClosed_subset (ProperSpace.isCompact_closedBall 0 1) isClosed_unitary
  simp +contextual [Set.subset_def, entrywise_sup_norm_bound_of_unitary]

instance {n : Type*} [DecidableEq n] [Fintype n] :
    CompactSpace (unitaryGroup n ℂ : Set (Matrix n n ℂ)) :=
  isCompact_iff_compactSpace.1 isCompact_unitaryGroup

end

open Fintype (card)
open WithLp Finset Matrix Norms.L2Operator

variable {n m : Type*} [Fintype n] [Fintype m]

section

variable {K : Type*} [RCLike K] {A : Matrix n n K}

lemma conjTranspose_mul_self_diag_eq_norm_sq (i : n) :
    (Aᴴ * A) i i = ‖toLp 2 (A.col i)‖ ^ 2 := by
  calc
    (Aᴴ * A) i i = ∑ x, ‖A x i‖ ^ 2 := by simp [Matrix.mul_apply, RCLike.conj_mul]
    _ = (‖toLp 2 (A.col i)‖ ^ 2 : ℝ) := by rw [PiLp.norm_sq_eq_of_L2]; simp
    _ = ‖toLp 2 (A.col i)‖ ^ 2 := by simp

variable [DecidableEq n]

theorem hadamard_aux (hA : ∀ i, ‖toLp 2 (A.col i)‖ = 1) :
    ‖A.det‖ ≤ 1 := by
  obtain hn | hn := isEmpty_or_nonempty n
  · simp
  let B : Matrix n n K := Aᴴ * A
  suffices ‖B.det‖ ≤ 1 by
    rw [← abs_of_nonneg (a := ‖A.det‖) (by simp), abs_le_one_iff_mul_self_le_one]
    simpa [B] using this
  have hB : B.IsHermitian := Matrix.isHermitian_transpose_mul_self _
  have (i : n) : B i i = 1 := by simp [B, conjTranspose_mul_self_diag_eq_norm_sq, hA]
  let N : ℕ := card n
  have hN : 0 < N := by simp [N, Fintype.card_pos]
  have : B.trace = N := by simp [Matrix.trace, this, N]
  have : ∑ i, hB.eigenvalues i = N := by
    simpa [← RCLike.ofReal_inj (K := K), ← hB.trace_eq_sum_eigenvalues]
  rw [← Real.rpow_le_rpow_iff (z := N⁻¹) (by simp) (by simp) (by positivity), Real.one_rpow]
  calc
    ‖B.det‖ ^ (N⁻¹ : ℝ) ≤ (∏ i : n, (|hB.eigenvalues i|) ^ 1) ^ ((∑ i : n, 1)⁻¹ : ℝ) := by
        simp [hB.det_eq_prod_eigenvalues, N]
    _ ≤ (∑ i, 1 * (fun x ↦ |hB.eigenvalues x|) i) / ∑ i, 1 :=
        Real.geom_mean_le_arith_mean _ _ (|hB.eigenvalues ·|) (by simp) (by simpa) (by simp)
    _ = (∑ i, |hB.eigenvalues i|) / N := by simp [N]
    _ = (∑ i, hB.eigenvalues i) / N := by
        congr! 2;
        simp +contextual [A.eigenvalues_conjTranspose_mul_self_nonneg]
    _ = _ := by simp [this]

theorem hadamard : ‖A.det‖ ≤ ∏ i : n, ‖toLp 2 (A.col i)‖ := by
  obtain hA | hA := eq_or_ne A.det 0
  · simp [hA, norm_zero, prod_nonneg]
  have hPos (i : n) : 0 < ‖toLp 2 (A.col i)‖ := by
    simp only [norm_pos_iff, ne_eq, toLp_eq_zero]
    intro h
    apply hA (Matrix.det_eq_zero_of_column_eq_zero i _)
    intro j
    simpa using congr($h j)
  let B : Matrix n n K := of fun i j : n => ‖toLp 2 (A.col j)‖⁻¹ * A i j
  have hB' (i : n) : B.col i = ‖toLp 2 (A.col i)‖⁻¹ • A.col i := by
    ext j
    simp [Matrix.col, B, Algebra.smul_def]
  have hB (i : n) : ‖toLp 2 (B.col i)‖ = 1 := by simp [hB', toLp_smul, norm_smul, (hPos i).ne']
  have hAB : B.det = (↑(∏ i, ‖toLp 2 (A.col i)‖))⁻¹ * A.det := by
    rw [Matrix.det_mul_row]
    simp
  replace hAB : (∏ i, ‖toLp 2 (A.col i)‖) * B.det = A.det := by
    rw [hAB, mul_inv_cancel_left₀]
    simp [prod_eq_zero_iff, hPos, ne_of_gt]
  simp only [← hAB, norm_mul]
  grw [hadamard_aux hB]
  simp

lemma toLp_col_le_opNorm (i : n) : ‖toLp 2 (A.col i)‖ ≤ ‖A‖ := by calc
  ‖toLp 2 (A.col i)‖ ≤ ‖(EuclideanSpace.equiv n K).symm (A.mulVec (Pi.single i 1))‖ := by simp
  _ ≤ ‖A‖ * ‖EuclideanSpace.single i 1‖ := Matrix.l2_opNorm_mulVec _ _
  _ ≤ ‖A‖ := by simp

theorem lem_2_5 : ∏ i : n, ‖toLp 2 (A.col i)‖ ≤ ‖A‖ ^ card n := by calc
  _ ≤ ∏ i, ‖A‖ := prod_le_prod (by simp) fun i hi ↦ toLp_col_le_opNorm i
  _ = ‖A‖ ^ card n := by simp

lemma norm_det_le_opNorm_pow : ‖A.det‖ ≤ ‖A‖ ^ card n := hadamard.trans lem_2_5

lemma l2_opNorm_sq_le_frobenius (A : Matrix m n K) : ‖A‖ ≤ √(∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by simp) ?_
  intro x
  cases x using WithLp.rec with | toLp x =>
  simp only [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap', toEuclideanLin_toLp,
    toLin'_apply]
  have (i : m) : ‖toLp 2 (A *ᵥ x) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ ^ 2) * ‖toLp 2 x‖ ^ 2 := by calc
    ‖toLp 2 (A *ᵥ x) i‖ ^ 2 = ‖∑ j, x j * A i j‖ ^ 2 := by simp [Matrix.mulVec_eq_sum]
    _ ≤ (∑ j, ‖x j‖ * ‖A i j‖) ^ 2 := by grw [norm_sum_le]; simp
    _ ≤ (∑ j, ‖x j‖ ^ 2) * ∑ j, ‖A i j‖ ^ 2 := by grw [Finset.sum_mul_sq_le_sq_mul_sq]
    _ = (∑ j, ‖A i j‖ ^ 2) * ‖toLp 2 x‖ ^ 2 := by rw [mul_comm, PiLp.norm_sq_eq_of_L2]; simp
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by positivity), mul_pow,
    Real.sq_sqrt (by positivity), sum_mul]
  exact sum_le_sum fun i _ ↦ this i

lemma l2_opNorm_isEmpty [IsEmpty n] {A : Matrix m n K} : ‖A‖ = 0 := by
  refine le_antisymm ?_ (by simp)
  refine ContinuousLinearMap.opNorm_le_bound _ (by simp) ?_
  intro x
  have : x = 0 := Subsingleton.elim _ _
  simp [this]

lemma l2_opNorm_diagonal (d : n → K) :
    ‖diagonal d‖ = ‖d‖ := by
  apply ContinuousLinearMap.opNorm_eq_of_bounds (by simp)
  · intro x
    cases x using WithLp.rec with | toLp x =>
    calc
      _ = ‖toLp 2 (diagonal d *ᵥ x)‖ := by simp
      _ = √(∑ i, ‖x i‖ ^ 2 * ‖d i‖ ^ 2) := by
        simp [mulVec_eq_sum, PiLp.norm_eq_of_L2, diagonal_apply, norm_mul, mul_pow]
      _ ≤ √(∑ i, ‖x i‖ ^ 2 * ‖d‖ ^ 2) := by
        gcongr with i hi
        apply norm_le_pi_norm
      _ = √(∑ i, ‖x i‖ ^ 2) * ‖d‖ := by
        rw [← sum_mul, Real.sqrt_mul (by positivity), Real.sqrt_sq (by simp)]
      _ = ‖d‖ * ‖toLp 2 x‖ := by simp [PiLp.norm_eq_of_L2, mul_comm]
  · intro N hN hx
    rw [pi_norm_le_iff_of_nonneg hN]
    intro i
    simpa [Matrix.toEuclideanLin_apply] using hx (EuclideanSpace.single i 1)

lemma norm_extend {α β : Type*} [Fintype α] [Fintype β] {x : α → K} {f : α → β}
    (hf : Function.Injective f) {p : ENNReal} :
    ‖toLp p (f.extend x 0)‖ = ‖toLp p x‖ := by
  cases p using ENNReal.recTopCoe with
  | top =>
    simp only [PiLp.norm_eq_ciSup, PiLp.toLp_apply]
    apply le_antisymm
    · apply Real.iSup_le _ (Real.iSup_nonneg (by simp))
      · intro i
        by_cases hj : ∃ j, f j = i
        · obtain ⟨j, hj⟩ := hj
          rw [← hj, hf.extend_apply]
          exact le_ciSup (f := fun i ↦ ‖x i‖) (by simp) j
        · simp only [Function.extend_apply' _ _ _ hj, Pi.zero_apply, norm_zero]
          apply Real.iSup_nonneg (by simp)
    · apply Real.iSup_le _ (Real.iSup_nonneg (by simp))
      intro i
      apply le_ciSup_of_le (by simp) (f i)
      rw [hf.extend_apply]
  | coe p =>
    obtain h₁ | h₁ := lt_or_ge 0 p.toReal
    · rw [PiLp.norm_eq_sum (by positivity), PiLp.norm_eq_sum (by positivity)]
      simp only [PiLp.toLp_apply, ENNReal.coe_toReal]
      rw [← Finset.sum_of_injOn (s := Finset.univ) f hf.injOn (by simp)]
      · rintro j - hj
        rw [Function.extend_apply']
        · simp [h₁.ne']
        grind only [= Set.mem_image, = mem_coe, mem_univ]
      simp [hf.extend_apply]
    · have : p = 0 := by
        rw [← le_zero_iff]
        norm_cast at h₁
      rw [this]
      simp only [ENNReal.coe_zero, PiLp.norm_eq_card]
      simp only [PiLp.toLp_apply, ne_eq, norm_eq_zero, Set.Finite.toFinset_setOf, Nat.cast_inj]
      apply (Finset.card_nbij f _ hf.injOn _).symm
      · simp [Set.MapsTo, hf.extend_apply]
      · simp only [Set.SurjOn, coe_filter, mem_univ, true_and, Set.subset_def, Set.mem_setOf_eq,
          Set.mem_image]
        intro i hi
        by_cases hj : ∃ j, f j = i
        · obtain ⟨j, hj⟩ := hj
          rw [← hj, hf.extend_apply] at hi
          exact ⟨j, hi, hj⟩
        · simp [Function.extend_apply' _ _ _ hj] at hi

lemma l2_opNorm_submatrix_le_of_injective [DecidableEq m] {n' m' : Type*}
    [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m']
    {fm : m' → m} {fn : n' → n} (hfn : fn.Injective) (hfm : fm.Injective) (A : Matrix m n K) :
    ‖A.submatrix fm fn‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by simp) ?_
  intro x
  cases x using WithLp.rec with | toLp x =>
  dsimp at x
  suffices ‖toLp 2 (A.submatrix fm fn *ᵥ x)‖ ≤ ‖A‖ * ‖toLp 2 x‖ by simpa
  let y : n → K := Function.extend fn x 0
  have h₁ : A *ᵥ y = A.submatrix id fn *ᵥ x := by
    ext i
    simp only [mulVec_eq_sum, op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply,
      smul_eq_mul, y, submatrix_apply, id_eq]
    rw [← Finset.sum_of_injOn (s := Finset.univ) fn hfn.injOn (by simp)]
    · rintro j - hj
      rw [Function.extend_apply' _ _ _ (by grind)]
      simp
    · simp [hfn.extend_apply]
  have h₂ : ‖toLp 2 (A.submatrix fm fn *ᵥ x)‖ ≤ ‖toLp 2 (A.submatrix id fn *ᵥ x)‖ := by
    suffices √(∑ i, ‖∑ j, x j * A (fm i) (fn j)‖ ^ 2) ≤ √(∑ i, ‖∑ j, x j * A i (fn j)‖ ^ 2) by
      simpa [PiLp.norm_eq_of_L2, mulVec_eq_sum] using this
    apply Real.sqrt_le_sqrt
    rw [← Finset.sum_image hfm.injOn (f := fun i ↦ ‖∑ j, x j * A i (fn j)‖ ^ 2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) (by simp)
  have h₃ : ‖toLp 2 (A *ᵥ y)‖ ≤ ‖A‖ * ‖toLp 2 y‖ := Matrix.l2_opNorm_mulVec A y
  have h₄ : ‖toLp 2 y‖ = ‖toLp 2 x‖ := norm_extend hfn
  grw [h₂, ← h₁, h₃, h₄]

lemma l2_opNorm_reindex [DecidableEq m] {n' m' : Type*}
    [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m']
    {em : m ≃ m'} {en : n ≃ n'} (A : Matrix m n K) :
    ‖A.reindex em en‖ = ‖A‖ := by
  refine le_antisymm ?_ ?_
  · exact l2_opNorm_submatrix_le_of_injective en.symm.injective em.symm.injective _
  · simpa using l2_opNorm_submatrix_le_of_injective en.injective em.injective (A.reindex em en)

end

variable {A E F : Matrix n n ℂ}

theorem lem_2_1 {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {j : Fin (n + 1)} {t : ℂ} :
    (A + single j j t).det = A.det + t * (A.submatrix (Fin.succAbove j) (Fin.succAbove j)).det := by
  rw [det_succ_column _ j]
  rw [det_succ_column A j]
  have (x : Fin (n + 1)) : (single j j t).submatrix x.succAbove j.succAbove = 0 := by
    ext a b
    simp
  simp only [add_apply, submatrix_add, Pi.add_apply, this, add_zero, add_mul, mul_add,
    Finset.sum_add_distrib, add_right_inj]
  rw [Finset.sum_eq_single_of_mem j (by simp)]
  · simp
  intro b _ hb
  simp [single_apply_of_row_ne hb.symm]

theorem lem_2_1' {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {t : ℂ} :
    (A + single 0 0 t).det = A.det + t * (A.submatrix Fin.succ Fin.succ).det := by
  simp [lem_2_1]

lemma single_same_eq_diagonal_single {n α : Type*} [DecidableEq n] [Zero α] {i : n} {a : α} :
    single i i a = diagonal (Pi.single i a) := by
  ext j k
  simp [diagonal_apply, Pi.single_apply, single]
  grind

theorem main_result_diag_fin_aux {n : ℕ} (d : Fin (n + 1) → ℂ)
    (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ‖(diagonal d + F).det - (diagonal d).det‖ ≤
      (n + 1) * ‖F‖ * (max ‖diagonal d‖ ‖diagonal d + F‖) ^ n := by
  induction n with
  | zero => simpa using norm_det_le_opNorm_pow (A := F)
  | succ n ih =>
    let d1 : Fin (n + 1) → ℂ := Matrix.vecTail d
    let d'1 : Fin (n + 2) → ℂ := Matrix.vecCons 0 d1
    let F1 := F.submatrix Fin.succ Fin.succ
    set z := (diagonal d + F).det - (diagonal d).det
    set z1 := (diagonal d1 + F1).det - (diagonal d1).det
    have hd'1 : (diagonal d'1).submatrix Fin.succ Fin.succ = diagonal d1 := by
      rw [submatrix_diagonal _ _ (Fin.succ_injective _)]
      rfl
    have hd1 : (diagonal d).submatrix Fin.succ Fin.succ = diagonal d1 := by
      rw [submatrix_diagonal _ _ (Fin.succ_injective _)]
      rfl
    have hd : (diagonal d).det = d 0 * (diagonal d1).det := by
      simp [Fin.prod_univ_succ (n := n + 1), d1, Matrix.vecTail]
    have hd' : diagonal d'1 + single 0 0 (d 0) = diagonal d := by
      rw [single_same_eq_diagonal_single, diagonal_add]
      congr! 2 with i
      cases i using Fin.cases with simp [d'1, d1, vecTail]
    have lem : z = d 0 * z1 + (diagonal d'1 + F).det := by
      replace hd' : diagonal d + F = diagonal d'1 + F + single 0 0 (d 0) := by
        simp only [← hd', add_right_comm]
      simp only [z, z1, hd, lem_2_1', submatrix_add, Pi.add_apply, hd'1, hd', F1]
      ring
    replace ih : ‖z1‖ ≤ (n + 1) * ‖F‖ * max ‖diagonal d‖ ‖diagonal d + F‖ ^ n := by calc
      ‖z1‖ ≤ (n + 1) * ‖F1‖ * max ‖diagonal d1‖ ‖diagonal d1 + F1‖ ^ n := ih d1 F1
      _ ≤ (n + 1) * ‖F‖ * max ‖diagonal d‖ ‖diagonal d1 + F1‖ ^ n := by
        rw [← hd1]
        gcongr <;> apply l2_opNorm_submatrix_le_of_injective <;> exact Fin.succ_injective _
      _ = (n + 1) * ‖F‖ * max ‖diagonal d‖ ‖(diagonal d + F).submatrix Fin.succ Fin.succ‖ ^ n := by
        simp [submatrix_add, hd1, F1]
      _ ≤ (n + 1) * ‖F‖ * max ‖diagonal d‖ ‖diagonal d + F‖ ^ n := by
        gcongr
        apply l2_opNorm_submatrix_le_of_injective <;> exact Fin.succ_injective _
    have h : ‖(diagonal d'1 + F).det‖ ≤ ‖F‖ * ‖diagonal d + F‖ ^ (n + 1) := by calc
      ‖(diagonal d'1 + F).det‖ ≤ ∏ i, ‖toLp 2 ((diagonal d'1 + F).col i)‖ := hadamard
      _ = ‖toLp 2 ((diagonal d'1).col 0 + F.col 0)‖ *
          ∏ i, ‖toLp 2 ((diagonal d'1 + F).col (Fin.succ i))‖ := by
        rw [Fin.prod_univ_succ]
        rfl
      _ = ‖toLp 2 (F.col 0)‖ * ∏ i, ‖toLp 2 ((diagonal d'1 + F).col (Fin.succ i))‖ := by simp [d'1]
      _ = ‖toLp 2 (F.col 0)‖ * ∏ i, ‖toLp 2 ((diagonal d + F).col (Fin.succ i))‖ := by
        rw [← hd']
        congr! 4 with i hi
        ext j
        simp [ne_comm]
      _ ≤ ‖F‖ * ∏ i : Fin (n + 1), ‖diagonal d + F‖ := by gcongr <;> apply toLp_col_le_opNorm
      _ = _ := by simp
    calc
      ‖z‖ = ‖d 0 * z1 + (diagonal d'1 + F).det‖ := by rw [lem]
      _ ≤ ‖d 0‖ * ‖z1‖ + ‖(diagonal d'1 + F).det‖ := by grw [norm_add_le, norm_mul]
      _ ≤ ‖diagonal d‖ * ‖z1‖ + ‖(diagonal d'1 + F).det‖ := by
        grw [norm_le_pi_norm, ← l2_opNorm_diagonal]
      _ ≤ max ‖diagonal d‖ ‖diagonal d + F‖ * ‖z1‖ + ‖(diagonal d'1 + F).det‖ := by
        gcongr
        exact le_max_left ‖diagonal d‖ ‖diagonal d + F‖
      _ ≤ max ‖diagonal d‖ ‖diagonal d + F‖ * ‖z1‖ +
          ‖F‖ * (max ‖diagonal d‖ ‖diagonal d + F‖) ^ (n + 1) := by
        grw [h]
        gcongr
        apply le_max_right
      _ ≤ (n + 2) * ‖F‖ * max ‖diagonal d‖ ‖diagonal d + F‖ ^ (n + 1) := by
        grw [ih]
        linear_combination
      _ = _ := by congr! 2; norm_cast

theorem main_result_diag_fin {n : ℕ} (d : Fin n → ℂ) (E : Matrix (Fin n) (Fin n) ℂ) :
    ‖(diagonal d + E).det - (diagonal d).det‖ ≤
      n * ‖E‖ * max ‖diagonal d‖ ‖diagonal d + E‖ ^ (n - 1) := by
  cases n with
  | zero => simp
  | succ n => simpa using main_result_diag_fin_aux d E

lemma reindex_diagonal {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (e : n ≃ m) (d : n → ℂ) :
    (diagonal d).reindex e e = diagonal (d ∘ e.symm) := by
  ext i j
  simp [diagonal_apply, reindex_apply]

theorem main_result_diag [DecidableEq n] (d : n → ℂ) (E : Matrix n n ℂ) :
    ‖(diagonal d + E).det - (diagonal d).det‖ ≤
      card n * ‖E‖ * (max ‖diagonal d‖ ‖diagonal d + E‖) ^ (card n - 1) := by
  let e : n ≃ Fin (card n) := Fintype.equivFin n
  have h := main_result_diag_fin (d ∘ e.symm) (E.reindex e e)
  have : reindex e e (diagonal d) + reindex e e E = reindex e e (diagonal d + E) := rfl
  rw [← reindex_diagonal e d, this, l2_opNorm_reindex, l2_opNorm_reindex, l2_opNorm_reindex,
    det_reindex_self, det_reindex_self] at h
  exact h

lemma charpoly_ne_zero {n R : Type*} [CommRing R] [Nontrivial R] [Fintype n] [DecidableEq n]
    {A : Matrix n n R} : A.charpoly ≠ 0 := by
  rw [ne_eq, ← Polynomial.degree_eq_bot, Matrix.charpoly_degree_eq_dim]
  simp

lemma Set.Finite.dense_compl {α : Type*} [TopologicalSpace α] [T1Space α] [PerfectSpace α]
    {s : Set α} (hs : s.Finite) : Dense (sᶜ : Set α) := by
  rw [Set.compl_eq_univ_diff]
  exact Dense.diff_finite (by simp) hs

open Filter Topology
theorem approximate_matrix [DecidableEq n] (A : Matrix n n ℂ) :
    ∃ B : ℕ → Matrix n n ℂ, (∀ i, (B i).det ≠ 0) ∧ Filter.Tendsto B Filter.atTop (𝓝 A) := by
  let s : Set ℂ := {x | x ∈ A.charpoly.roots}
  have : 0 ∈ closure sᶜ := (Multiset.finite_toSet _).dense_compl _
  obtain ⟨u, hu, hu'⟩ := mem_closure_iff_seq_limit.1 this
  replace hu : ∀ i : ℕ, Matrix.det (A - scalar n (u i)) ≠ 0 := by
    intro i
    have : A.charpoly.eval (u i) ≠ 0 := by simpa [charpoly_ne_zero, s] using hu i
    contrapose! this
    rw [Matrix.eval_charpoly, ← neg_sub, det_neg, this, mul_zero]
  refine ⟨fun i ↦ A - scalar n (u i), hu, ?_⟩
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  simp only [scalar_apply, sub_apply, diagonal_apply]
  split
  case isFalse => simp
  convert Tendsto.const_sub _ hu'
  simp

open ComplexOrder
theorem exists_svd_nonsingular {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.det ≠ 0) :
    ∃ U ∈ unitaryGroup n ℂ, ∃ V ∈ unitaryGroup n ℂ, ∃ d : n → ℂ, A = U * diagonal d * Vᴴ := by
  let S : Matrix n n ℂ := Aᴴ * A
  have hS : S.IsHermitian := Matrix.isHermitian_transpose_mul_self _
  have hS' : S.PosDef := Matrix.PosDef.conjTranspose_mul_self _ <|
    Matrix.mulVec_injective_of_isUnit <| (Matrix.isUnit_iff_isUnit_det _).2 hA.isUnit
  have hpos (i : n) : (0 : ℝ) < hS.eigenvalues i := hS'.eigenvalues_pos _
  let V : Matrix n n ℂ := hS.eigenvectorUnitary
  let Λ : Matrix n n ℂ := diagonal (fun i ↦ hS.eigenvalues i)
  let D : Matrix n n ℂ := diagonal fun i ↦ Real.sqrt (hS.eigenvalues i)
  have hDΛ : Dᴴ * D = Λ := by
    simp only [D, Λ, diagonal_conjTranspose, diagonal_mul_diagonal, Pi.star_apply, RCLike.star_def,
      Complex.conj_ofReal, diagonal_eq_diagonal_iff]
    intro i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hpos i).le]
  have hD : Dᴴ = D := by simp [D]
  have spec : Vᴴ * S * V = Λ := hS.star_mul_self_mul_eq_diagonal
  have : D.det ≠ 0 := by simp [D, prod_eq_zero_iff, Real.sqrt_ne_zero', hpos]
  have : Invertible D := Matrix.invertibleOfIsUnitDet _ this.isUnit
  let U := A * V * D⁻¹
  have hU : U ∈ unitaryGroup n ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    calc
      star U * U = D⁻¹ᴴ * Vᴴ * S * V * D⁻¹ := by simp [S, U, star_eq_conjTranspose, mul_assoc]
      _ = D⁻¹ᴴ * Λ * D⁻¹ := by simp only [spec, mul_assoc]
      _ = 1 := by simp [← hDΛ, conjTranspose_nonsing_inv, hD]
  have : A = U * D * Vᴴ := by simp [U, mul_assoc, ← star_eq_conjTranspose, V]
  exact ⟨U, hU, V, by simp [V], _, this⟩

lemma tendsto_diagonal_iff {ι n R : Type*} [DecidableEq n] [TopologicalSpace R] [Zero R]
    {l : Filter ι} {x : n → R} {f : ι → n → R} :
    Tendsto (fun i => diagonal (f i)) l (𝓝 (diagonal x)) ↔ Tendsto f l (𝓝 x) := by
  rw [tendsto_pi_nhds]
  simp only [tendsto_pi_nhds, diagonal_apply]
  constructor
  · intro h i
    simpa using h i i
  · intro h i j
    obtain rfl | hij := eq_or_ne i j
    · simpa using h i
    · simp [hij, tendsto_const_nhds]

theorem exists_svd_square {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    ∃ U ∈ unitaryGroup n ℂ, ∃ V ∈ unitaryGroup n ℂ, ∃ d : n → ℂ, A = U * diagonal d * Vᴴ := by
  obtain ⟨B, hBdet, hBlim⟩ := approximate_matrix A
  have (i : ℕ) := exists_svd_nonsingular (B i) (hBdet i)
  choose U_ hU_ V_ hV_ d_ h using this
  let UV : ℕ → Matrix n n ℂ × Matrix n n ℂ := fun i ↦ (U_ i, V_ i)
  have hUV (i : ℕ) : UV i ∈ (unitaryGroup n ℂ : Set _) ×ˢ (unitaryGroup n ℂ) := by
    simp [UV, Set.mem_prod, hU_, hV_]
  obtain ⟨⟨U, V⟩, ⟨hU : U ∈ _, hV : V ∈ _⟩, φ, hφ, hlim⟩ :=
    (isCompact_unitaryGroup.prod isCompact_unitaryGroup).isSeqCompact hUV
  obtain ⟨hUφ, hVφ⟩ : Tendsto (U_ ∘ φ) atTop (𝓝 U) ∧ Tendsto (V_ ∘ φ) atTop (𝓝 V) := by
    rwa [Prod.tendsto_iff] at hlim
  have h_eq : Tendsto (fun i => B (φ i)) atTop (𝓝 A) := hBlim.comp hφ.tendsto_atTop;
  obtain ⟨d, hd⟩ : ∃ d : n → ℂ, Tendsto (d_ ∘ φ) atTop (𝓝 d) := by
    have h_lim : Tendsto (fun i ↦ U_ (φ i) * diagonal (d_ (φ i)) * (V_ (φ i))ᴴ) atTop (𝓝 A) := by
      simpa only [← h] using h_eq
    have h_lim' : Tendsto (fun i ↦ diagonal (d_ (φ i))) atTop (𝓝 (Uᴴ * A * V)) := by
      refine ((hUφ.star.mul h_lim).mul hVφ).congr fun i ↦ ?_
      simp only [Function.comp_apply, mul_assoc, ← star_eq_conjTranspose, (hV_ (φ i)).1]
      simp [(hU_ (φ i)).1, ← mul_assoc]
    use Matrix.diag (Uᴴ * A * V)
    rw [tendsto_pi_nhds]
    intro i
    simpa using tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h_lim' i) i
  refine ⟨U, hU, V, hV, d, ?_⟩
  have h_cont : Tendsto (fun i ↦ U_ (φ i) * diagonal (d_ (φ i)) * (V_ (φ i))ᴴ) atTop
      (𝓝 (U * diagonal d * Vᴴ)) := by
    refine (hUφ.mul ?_).mul hVφ.star
    simpa [tendsto_diagonal_iff] using hd
  exact tendsto_nhds_unique h_eq (by simpa only [h] using h_cont)

lemma norm_mul_mem_unitaryGroup [DecidableEq n] {U : Matrix n n ℂ} (A : Matrix n n ℂ)
    (hU : U ∈ unitaryGroup n ℂ) :
    ‖A * U‖ = ‖A‖ :=
  CStarRing.norm_mul_mem_unitary _ hU

lemma norm_mem_unitaryGroup_mul [DecidableEq n] {U : Matrix n n ℂ} (A : Matrix n n ℂ)
    (hU : U ∈ unitaryGroup n ℂ) :
    ‖U * A‖ = ‖A‖ :=
  CStarRing.norm_mem_unitary_mul _ hU

lemma norm_of_mem_unitaryGroup [DecidableEq n] [Nonempty n] {U : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) : ‖U‖ = 1 :=
  CStarRing.norm_of_mem_unitary hU

theorem main_result [DecidableEq n] :
    ‖(A + E).det - A.det‖ ≤ card n * ‖E‖ * (max ‖A‖ ‖A + E‖) ^ (card n - 1) := by
  obtain ⟨U, hU, V, hV, d, h⟩ := exists_svd_square A
  let F := Uᴴ * E * V
  have hAE : U * (diagonal d + F) * Vᴴ = A + E := by calc
    _ = A + U * F * Vᴴ := by simp [h, add_mul, mul_add]
    _ = A + (U * Uᴴ) * E * (V * Vᴴ) := by simp [F, mul_assoc]
    _ = A + E := by simp [← star_eq_conjTranspose, hU.2, hV.2]
  have det₁ : (U * Vᴴ).det * (diagonal d + F).det = (A + E).det := by calc
    (U * Vᴴ).det * (diagonal d + F).det = U.det * (diagonal d + F).det * (Vᴴ).det := by
      rw [det_mul]
      ring
    _ = (U * (diagonal d + F) * Vᴴ).det := by simp [det_mul]
    _ = (A + E).det := by rw [hAE]
  have det₂ : (U * Vᴴ).det * (diagonal d).det = A.det := by calc
    (U * Vᴴ).det * (diagonal d).det = U.det * (diagonal d).det * (Vᴴ).det := by
      rw [det_mul];
      ring
    _ = (U * diagonal d * Vᴴ).det := by simp [det_mul]
    _ = A.det := by simp [h]
  let z := (diagonal d + F).det - (diagonal d).det
  have hd : ‖diagonal d‖ = ‖A‖ := by
    rw [h, norm_mul_mem_unitaryGroup, norm_mem_unitaryGroup_mul _ hU]
    exact unitary.star_mem hV
  have hF : ‖F‖ = ‖E‖ := by
    rw [norm_mul_mem_unitaryGroup _ hV, norm_mem_unitaryGroup_mul]
    exact unitary.star_mem hU
  have hdF : ‖diagonal d + F‖ = ‖A + E‖ := by
    rw [← hAE, norm_mul_mem_unitaryGroup, norm_mem_unitaryGroup_mul _ hU]
    exact unitary.star_mem hV
  have : ‖z‖ ≤ _ := main_result_diag d F
  calc
    ‖(A + E).det - A.det‖ = ‖(U * Vᴴ).det‖ * ‖z‖ := by
      rw [← det₁, ← det₂, ← norm_mul, mul_sub]
    _ = ‖z‖ := by
      rw [CStarRing.norm_of_mem_unitary, one_mul]
      exact Matrix.det_of_mem_unitary (mul_mem hU (unitary.star_mem hV))
    _ ≤ card n * ‖F‖ * max ‖diagonal d‖ ‖diagonal d + F‖ ^ (card n - 1) := main_result_diag d F
    _ = card n * ‖E‖ * max ‖A‖ ‖A + E‖ ^ (card n - 1) := by
      simp only [hd, hF, hdF]

def myMat : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0.237543147066448,  -1.53145788325137;
     0.0972878195053468,   2.14502930109795]

lemma myMat_det : myMat.det = 0.658529208858350261945890006716 := by
  norm_num [myMat, det_fin_two]
