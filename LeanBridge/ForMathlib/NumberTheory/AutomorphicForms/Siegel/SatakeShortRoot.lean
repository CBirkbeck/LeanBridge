import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SatakeRankOne
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SatakeUniversal

/-!
# The Weyl invariance of the Satake map under the transpositions

Let `k, k' = k + 1` be two consecutive coordinates. The parabolic subgroup `P ⊇ B` of the
`(A, B; 0, D)` with `A` upper triangular but for the entry `(k', k)` has the Levi factor `GL(2)` on
`(e_k, e_{k'})`, and the embedded `SL(2, ℤ)` on these coordinates (`(U, 0; 0, U⁻ᵀ)`,
`SiegelUpperHalfSpace.shortEmbed`) acts on the right cosets `Γx` of a double coset `D` by right
multiplication. Each right coset has a representative `b` in `B`; the `2 × 2` block of `A` at
`(k, k')`, `(A_kk, A_kk'; 0, A_k'k')`, changes under the action by right multiplication up to
`GL(2, ℤ)` on the left (`SiegelUpperHalfSpace.exists_borelRep_smul_eq`), while the valuations at the
other coordinates do not change. So the rank-one reduction `SiegelUpperHalfSpace.sum_mul_hnfData_eq`
applies, the shift `p^{-(g-k)}` and `p^{-(g-k')}` differing by one power of `p`: the universal
Satake map of every double coset is invariant under the transposition of `x_k` and `x_{k'}`.

## Main definitions

* `SiegelUpperHalfSpace.pairBlock`: the matrix acting by a `2 × 2` matrix on two coordinates.
* `SiegelUpperHalfSpace.shortEmbed`: `SL(2, ℤ)` embedded in `Sp(2g, ℤ)` on `(e_k, e_{k'})`.
* `SiegelUpperHalfSpace.IsShortParabolic`: the parabolic subgroup of the transposition.
* `SiegelUpperHalfSpace.shortBlock`: its `2 × 2` block at `(k, k')`.

## Main results

* `SiegelUpperHalfSpace.exists_borelRep_smul_eq`: the representatives in the Borel subgroup of the
  right cosets moved by an element of `Γ`.
* `SiegelUpperHalfSpace.domCongr_weylPerm_swap_satakeMapUniv`: the universal Satake map of a
  double coset is invariant under the transposition of two consecutive coordinates.
-/

open Matrix DoubleCoset MonoidAlgebra

open scoped MatrixGroups

open HeckeCosetModule (single)

namespace SiegelUpperHalfSpace

variable {n : ℕ}

attribute [local instance] Fintype.ofFinite

/-! ### The action of `Γ` on the representatives in the Borel subgroup -/

/-- **The representatives in the Borel subgroup of the right cosets moved by `Γ`** (LMFDB
`mf.siegel.lift`, through the Weyl invariance of the Satake map): if `γ ∈ Γ` moves the right coset
`v` of a double coset `D` to `γ • v`, the representative in the Borel subgroup of `γ • v` is
`c b γ⁻¹` for some `c ∈ Γ`, `b` being that of `v`. -/
lemma exists_borelRep_smul_eq (p : ℕ)
    (D : HeckeCoset (heckeMonoidAt (Fin n) p) (heckeGamma (Fin n)) (heckeGamma (Fin n)))
    (γ : heckeGamma (Fin n)) (v : DecompQuotient (heckeGamma (Fin n)) (heckeGamma (Fin n))
      (D.out : GL (Fin n ⊕ Fin n) ℚ)⁻¹) :
    ∃ c ∈ heckeGamma (Fin n), (borelRep (rightCosetRep_mem_gspPlusGL p D (γ • v)) :
      GL (Fin n ⊕ Fin n) ℚ) = c * (borelRep (rightCosetRep_mem_gspPlusGL p D v) :
        GL (Fin n ⊕ Fin n) ℚ) * (γ : GL (Fin n ⊕ Fin n) ℚ)⁻¹ := by
  rcases exists_mem_rightCosetRep_mul_eq_mul_rightCosetRep D v (inv_mem γ.2) with ⟨γ₁, hγ₁, h₁⟩
  have hv : (⟨(γ : GL (Fin n ⊕ Fin n) ℚ)⁻¹, inv_mem γ.2⟩ : heckeGamma (Fin n))⁻¹ • v = γ • v := by
    congr 1
  rw [hv] at h₁
  rcases exists_borelRep_eq (rightCosetRep_mem_gspPlusGL p D (γ • v)) with ⟨γ₂, hγ₂, h₂⟩
  rcases exists_borelRep_eq (rightCosetRep_mem_gspPlusGL p D v) with ⟨γ₃, hγ₃, h₃⟩
  refine ⟨γ₂ * γ₁⁻¹ * γ₃⁻¹, mul_mem (mul_mem hγ₂ (inv_mem hγ₁)) (inv_mem hγ₃), ?_⟩
  rw [h₂, h₃, eq_inv_mul_of_mul_eq h₁.symm]
  group

/-! ### Diagonal entries of the Borel subgroup -/

lemma coe_inv_apply_inl_inl (b : siegelBorel n) (a c : Fin n) :
    (((b⁻¹ : siegelBorel n) : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)
      (.inl a) (.inl c) = (borelMultiplier b)⁻¹ *
        ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) (.inr c)
          (.inr a) := by
  have hb : ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ *
      J (Fin n) ℚ * ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) =
        borelMultiplier b • J (Fin n) ℚ :=
    transpose_mul_J_mul (⟨((b : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ), b.2.1⟩ : gspPlus (Fin n))
  have hr : borelMultiplier b ≠ 0 := (borelMultiplier_pos b).ne'
  have hleft : ((borelMultiplier b)⁻¹ • -(J (Fin n) ℚ *
      ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ * J (Fin n) ℚ)) *
        ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) = 1 := by
    rw [Matrix.smul_mul, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ _
      ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ), hb,
      Matrix.mul_smul, J_squared, smul_neg, smul_smul, inv_mul_cancel₀ hr, one_smul, neg_neg]
  have hinv : (((b⁻¹ : siegelBorel n) : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) = (borelMultiplier b)⁻¹ • -(J (Fin n) ℚ *
        ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ *
          J (Fin n) ℚ) := by
    rw [Subgroup.coe_inv, coe_units_inv, inv_eq_left_inv hleft]
  rw [hinv]
  simp [J, Matrix.mul_apply, one_apply]

lemma borelDiag_mul_apply_inr (b : siegelBorel n) (j : Fin n) :
    borelDiag b j * ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)
      (.inr j) (.inr j) = borelMultiplier b := by
  have hr : borelMultiplier b ≠ 0 := (borelMultiplier_pos b).ne'
  have hdiag : borelDiag b⁻¹ j * borelDiag b j = 1 := by
    rw [← borelDiag_mul, inv_mul_cancel, borelDiag_one]
  rw [borelDiag, coe_inv_apply_inl_inl] at hdiag
  field_simp at hdiag
  linear_combination hdiag

lemma apply_inr_inr_eq_zero (b : siegelBorel n) {a c : Fin n} (hac : a < c) :
    ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) (.inr a) (.inr c) =
      0 := by
  have h : (((b⁻¹ : siegelBorel n) : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) (.inl c) (.inl a) = 0 :=
    (b⁻¹).2.2.2 hac
  rw [coe_inv_apply_inl_inl] at h
  exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (borelMultiplier_pos b).ne')

lemma borelRep_mem_heckeMonoidAt {p : ℕ} {x : GL (Fin n ⊕ Fin n) ℚ}
    (hx : x ∈ heckeMonoidAt (Fin n) p) (hx' : x ∈ gspPlusGL (Fin n)) :
    (borelRep hx' : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p := by
  rcases exists_borelRep_eq hx' with ⟨γ, hγ, h⟩
  rw [h]
  exact mul_mem (heckeGamma_le_heckeMonoidAt p hγ) hx

lemma exists_natAbs_num_borelDiag [NeZero n] {p : ℕ} [Fact p.Prime] {b : siegelBorel n}
    (hb : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p) (j : Fin n) :
    ∃ a : ℕ, ((borelDiag b j).num.natAbs = p ^ a ∧ ((borelDiag b j).num : ℚ) = borelDiag b j) := by
  rcases hb with ⟨⟨-, M, hM⟩, δ, hδ⟩
  have hr : borelMultiplier b = (p : ℚ) ^ δ := multiplier_eq _ hδ
  have hM' (i i' : Fin n ⊕ Fin n) : ((b : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) i i' = M i i' :=
    (congrFun (congrFun hM i) i').symm
  have h : borelDiag b j * ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)
      (.inr j) (.inr j) = borelMultiplier b :=
    borelDiag_mul_apply_inr b j
  rw [borelDiag, hM', hM', hr] at h
  have hz : M (.inl j) (.inl j) * M (.inr j) (.inr j) = (p : ℤ) ^ δ := by
    exact_mod_cast h
  have hdvd : (M (.inl j) (.inl j)).natAbs ∣ p ^ δ := by
    rw [← Int.natAbs_natCast (p ^ δ), Nat.cast_pow, ← hz]
    exact Int.natAbs_dvd_natAbs.mpr (dvd_mul_right _ _)
  rcases (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd with ⟨a, -, ha⟩
  refine ⟨a, ?_, ?_⟩ <;> rw [borelDiag, hM', Rat.num_intCast]
  exact ha

/-! ### `2 × 2` matrices on two coordinates -/

section Pair

variable {k k' : Fin n} (hkk' : k ≠ k') {R : Type*} [CommRing R]

/-- **`Fin n` as the two coordinates `k, k'` together with the others** (LMFDB `mf.siegel.lift`,
through the Weyl invariance of the Satake map). -/
def twoEquiv : Fin 2 ⊕ {c : Fin n // c ≠ k ∧ c ≠ k'} ≃ Fin n where
  toFun := Sum.elim ![k, k'] Subtype.val
  invFun c := if hk : c = k then .inl 0 else if hk' : c = k' then .inl 1 else .inr ⟨c, hk, hk'⟩
  left_inv := by
    rintro (a | ⟨c, hck, hck'⟩)
    · fin_cases a <;> simp [hkk'.symm]
    · simp [hck, hck']
  right_inv c := by
    by_cases hk : c = k
    · simp [hk]
    · by_cases hk' : c = k' <;> simp [hk, hk', hkk'.symm]

/-- The **matrix acting by `h` on the coordinates `(k, k')`** and by the identity on the others
(LMFDB `mf.siegel.lift`, through the Weyl invariance of the Satake map). -/
def pairBlock (h : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin n) (Fin n) R :=
  reindex (twoEquiv hkk') (twoEquiv hkk') (fromBlocks h 0 0 1)

lemma twoEquiv_symm_left : (twoEquiv hkk').symm k = .inl 0 := by
  simp [twoEquiv]

lemma twoEquiv_symm_right : (twoEquiv hkk').symm k' = .inl 1 := by
  simp [twoEquiv, hkk'.symm]

lemma twoEquiv_symm_other {c : Fin n} (hck : c ≠ k) (hck' : c ≠ k') :
    (twoEquiv hkk').symm c = .inr ⟨c, hck, hck'⟩ := by
  simp [twoEquiv, hck, hck']

variable (h h' : Matrix (Fin 2) (Fin 2) R)

lemma pairBlock_apply_twoEquiv (i j : Fin 2) :
    pairBlock hkk' h (![k, k'] i) (![k, k'] j) = h i j := by
  fin_cases i <;> fin_cases j <;>
    simp [pairBlock, twoEquiv_symm_left, twoEquiv_symm_right]

lemma pairBlock_apply_of_ne_left {a : Fin n} (hak : a ≠ k) (hak' : a ≠ k') (b : Fin n) :
    pairBlock hkk' h a b = if a = b then 1 else 0 := by
  rw [pairBlock, reindex_apply, submatrix_apply, twoEquiv_symm_other hkk' hak hak']
  by_cases hbk : b = k
  · rw [hbk, twoEquiv_symm_left]
    simp [hak]
  · by_cases hbk' : b = k'
    · rw [hbk', twoEquiv_symm_right]
      simp [hak']
    · simp [twoEquiv_symm_other hkk' hbk hbk', one_apply]

lemma pairBlock_apply_of_ne_right {b : Fin n} (hbk : b ≠ k) (hbk' : b ≠ k') (a : Fin n) :
    pairBlock hkk' h a b = if a = b then 1 else 0 := by
  rw [pairBlock, reindex_apply, submatrix_apply, twoEquiv_symm_other hkk' hbk hbk']
  by_cases hak : a = k
  · rw [hak, twoEquiv_symm_left]
    simp [Ne.symm hbk]
  · by_cases hak' : a = k'
    · rw [hak', twoEquiv_symm_right]
      simp [Ne.symm hbk']
    · simp [twoEquiv_symm_other hkk' hak hak', one_apply]

lemma pairBlock_mul : pairBlock hkk' (h * h') = pairBlock hkk' h * pairBlock hkk' h' := by
  rw [pairBlock, pairBlock, pairBlock, reindex_apply, reindex_apply, reindex_apply,
    submatrix_mul_equiv, fromBlocks_multiply]
  simp

lemma pairBlock_one : pairBlock hkk' (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  rw [pairBlock, fromBlocks_one, reindex_apply, submatrix_one_equiv]

lemma pairBlock_map {S : Type*} [CommRing S] (f : R →+* S) :
    (pairBlock hkk' h).map f = pairBlock hkk' (h.map f) := by
  rw [pairBlock, pairBlock, reindex_apply, reindex_apply, ← submatrix_map, fromBlocks_map,
    Matrix.map_zero _ (map_zero f), Matrix.map_zero _ (map_zero f),
    Matrix.map_one _ (map_zero f) (map_one f)]

/-- The **integral symplectic matrix `(U, 0; 0, U⁻ᵀ)`**, `U` acting by `h ∈ SL(2, ℤ)` on the
coordinates `(e_k, e_{k'})` (LMFDB `mf.siegel.lift`, through the Weyl invariance of the Satake
map). -/
def shortEmbedSp : SL(2, ℤ) →* symplecticGroup (Fin n) ℤ where
  toFun h := ⟨fromBlocks (pairBlock hkk' (h : Matrix (Fin 2) (Fin 2) ℤ)) 0 0
    (pairBlock hkk' ((h⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))ᵀ, by
      refine SymplecticGroup.fromBlocks_mem_iff.mpr ⟨by simp, by simp, ?_⟩
      rw [transpose_zero, Matrix.zero_mul, sub_zero, ← transpose_mul, ← pairBlock_mul,
        ← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one, pairBlock_one,
        transpose_one]⟩
  map_one' := Subtype.ext <| by simp [pairBlock_one]
  map_mul' h h' := Subtype.ext <| by
    simp only [Submonoid.coe_mul, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add, mul_inv_rev h h', SpecialLinearGroup.coe_mul, pairBlock_mul, transpose_mul]

/-- `SL(2, ℤ)` **embedded in `Γ = Sp(2g, ℤ)` on the coordinates `(e_k, e_{k'})`** (LMFDB
`mf.siegel.lift`, through the Weyl invariance of the Satake map), by `h ↦ (U, 0; 0, U⁻ᵀ)`, `U`
acting by `h` on `(e_k, e_{k'})` and by the identity on the other `e_c`. -/
def shortEmbed : SL(2, ℤ) →* heckeGamma (Fin n) :=
  ((spToGL (Fin n)).comp (shortEmbedSp hkk')).codRestrict (heckeGamma (Fin n))
    fun h ↦ ⟨shortEmbedSp hkk' h, trivial, rfl⟩

lemma coe_shortEmbed (u : SL(2, ℤ)) : (((shortEmbed hkk' u : heckeGamma (Fin n)) :
    GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) =
      (fromBlocks (pairBlock hkk' (u : Matrix (Fin 2) (Fin 2) ℤ)) 0 0
        (pairBlock hkk' ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))ᵀ).map (Int.castRingHom ℚ) :=
  rfl

variable (u : SL(2, ℤ)) (y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) {a : Fin n}

lemma shortEmbed_mul_apply (hak : a ≠ k) (hak' : a ≠ k') :
    ((((shortEmbed hkk' u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) * y) (.inl a) (.inl a) = y (.inl a) (.inl a) := by
  rw [coe_shortEmbed, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [pairBlock_apply_of_ne_left hkk' _ hak hak']

lemma mul_shortEmbed_apply (hak : a ≠ k) (hak' : a ≠ k') :
    (y * (((shortEmbed hkk' u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)) (.inl a) (.inl a) = y (.inl a) (.inl a) := by
  rw [coe_shortEmbed, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [pairBlock_apply_of_ne_right hkk' _ hak hak']

end Pair

/-! ### The parabolic subgroup of a transposition -/

section Parabolic

variable (k k' : Fin n)

/-- The **parabolic subgroup of the transposition of `k` and `k'`** (LMFDB `mf.siegel.lift`,
through the Weyl invariance of the Satake map): the `(A, B; 0, D)` whose block `A` is upper
triangular but for its entry `(k', k)`. -/
def IsShortParabolic (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) : Prop :=
  x.toBlocks₂₁ = 0 ∧ x.toBlocks₁₁.BlockTriangular fun a ↦ if a = k' then k else a

/-- The **`2 × 2` block at the coordinates `(k, k')`** of the upper left block of a matrix (LMFDB
`mf.siegel.lift`, through the Weyl invariance of the Satake map). -/
def shortBlock (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  of fun i j ↦ x (.inl (![k, k'] i)) (.inl (![k, k'] j))

variable {k k'} {x y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ} {a b : Fin n}

lemma lt_of_short_lt (hk : (k' : ℕ) = k + 1)
    (h : (if b = k' then k else b) < if a = k' then k else a) : b < a := by
  rw [Fin.lt_def] at h ⊢
  split_ifs at h with h₁ h₂ h₂ <;> subst_vars <;> omega

lemma short_lt_of_lt (hk : (k' : ℕ) = k + 1) (hba : b < a) (hne : ¬(a = k' ∧ b = k)) :
    (if b = k' then k else b) < if a = k' then k else a := by
  rw [Fin.lt_def] at hba ⊢
  have hne' : ¬((a : ℕ) = k' ∧ (b : ℕ) = k) := fun h ↦ hne ⟨Fin.ext h.1, Fin.ext h.2⟩
  split_ifs with h₁ h₂ h₂ <;> subst_vars <;> omega

lemma ne_of_short (hk : (k' : ℕ) = k + 1) : k ≠ k' :=
  fun h ↦ by rw [h] at hk; omega

lemma isShortParabolic_of_mem (hk : (k' : ℕ) = k + 1) {x : GL (Fin n ⊕ Fin n) ℚ}
    (hx : x ∈ siegelBorel n) :
    IsShortParabolic k k' (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) :=
  ⟨hx.2.1, fun _ _ hij ↦ hx.2.2 (lt_of_short_lt hk hij)⟩

lemma IsShortParabolic.mul (hx : IsShortParabolic k k' x) (hy : IsShortParabolic k k' y) :
    IsShortParabolic k k' (x * y) := by
  refine ⟨?_, ?_⟩
  · rw [toBlocks₂₁_mul, hx.1, hy.1, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  · rw [toBlocks₁₁_mul, hy.1, Matrix.mul_zero, add_zero]
    exact hx.2.mul hy.2

lemma isShortParabolic_shortEmbed (hkk' : k ≠ k') (u : SL(2, ℤ)) :
    IsShortParabolic k k' (((shortEmbed hkk' u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) := by
  refine ⟨?_, fun a b hab ↦ ?_⟩
  · rw [coe_shortEmbed, fromBlocks_map, toBlocks_fromBlocks₂₁]
    exact Matrix.map_zero _ (map_zero _)
  · rw [coe_shortEmbed, fromBlocks_map, toBlocks_fromBlocks₁₁, map_apply]
    have hab' : a ≠ b := fun h ↦ by rw [h] at hab; exact lt_irrefl _ hab
    by_cases ha : a = k ∨ a = k'
    · have hb : b ≠ k ∧ b ≠ k' := by
        constructor <;> rintro rfl <;> rcases ha with rfl | rfl <;> simp at hab
      rw [pairBlock_apply_of_ne_right hkk' _ hb.1 hb.2, ite_eq_right hab', map_zero]
    · rw [pairBlock_apply_of_ne_left hkk' _ (fun h ↦ ha (.inl h)) (fun h ↦ ha (.inr h)),
        ite_eq_right hab', map_zero]

lemma mem_siegelBorel_of_isShortParabolic (hk : (k' : ℕ) = k + 1) {x : GL (Fin n ⊕ Fin n) ℚ}
    (hx : x ∈ gspPlusGL (Fin n))
    (hP : IsShortParabolic k k' (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ))
    (h₀ : (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) (.inl k') (.inl k) = 0) :
    x ∈ siegelBorel n := by
  refine ⟨hx, hP.1, fun i j hij ↦ ?_⟩
  by_cases hne : i = k' ∧ j = k
  · rcases hne with ⟨rfl, rfl⟩
    exact h₀
  · exact hP.2 (short_lt_of_lt hk hij hne)

lemma shortBlock_mul (hk : (k' : ℕ) = k + 1) (hx : IsShortParabolic k k' x)
    (hy : IsShortParabolic k k' y) :
    shortBlock k k' (x * y) = shortBlock k k' x * shortBlock k k' y := by
  have hβ (i : Fin 2) : (if ![k, k'] i = k' then k else ![k, k'] i) = k := by
    fin_cases i <;> simp [ne_of_short hk]
  ext i j
  have h₂ : ∑ c, x (.inl (![k, k'] i)) (.inr c) * y (.inr c) (.inl (![k, k'] j)) = 0 :=
    Finset.sum_eq_zero fun c _ ↦ by
      rw [show y (.inr c) (.inl (![k, k'] j)) = 0 from congrFun (congrFun hy.1 c) _, mul_zero]
  simp only [shortBlock, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sum_type, h₂]
  rw [Fintype.sum_eq_add k k' (ne_of_short hk) fun c hc ↦ ?_]
  · simp
  · rcases lt_or_gt_of_ne hc.1 with hck | hck
    · rw [show x (.inl (![k, k'] i)) (.inl c) = 0 from hx.2 (by
        dsimp only
        rw [hβ, ite_eq_right hc.2]
        exact hck), zero_mul]
    · rw [show y (.inl c) (.inl (![k, k'] j)) = 0 from hy.2 (by
        dsimp only
        rw [hβ, ite_eq_right hc.2]
        exact hck), mul_zero]

lemma shortBlock_shortEmbed (hkk' : k ≠ k') (u : SL(2, ℤ)) :
    shortBlock k k' (((shortEmbed hkk' u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) =
        (u : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := by
  ext i j
  rw [shortBlock, Matrix.of_apply, coe_shortEmbed, map_apply, fromBlocks_apply₁₁,
    pairBlock_apply_twoEquiv,
    map_apply]

lemma shortBlock_one (hkk' : k ≠ k') : shortBlock k k' 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shortBlock, one_apply, hkk', hkk'.symm]

variable (k k') in
/-- The **integral `2 × 2` block at `(k, k')`** of an integral matrix (LMFDB `mf.siegel.lift`,
through the Weyl invariance of the Satake map). -/
def shortBlockZ (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) : Matrix (Fin 2) (Fin 2) ℤ :=
  (shortBlock k k' x).map Rat.num

lemma map_shortBlockZ (hx : x ∈ (Int.castRingHom ℚ).mapMatrix.range) :
    (shortBlockZ k k' x).map (Int.castRingHom ℚ) = shortBlock k k' x := by
  rcases hx with ⟨M, rfl⟩
  ext i j
  simp [shortBlockZ, shortBlock]

variable (k k') in
/-- The **outer weight**, `(δ; d)` with `d_k` and `d_{k'}` replaced by `δ` (LMFDB
`mf.siegel.lift`, through the Weyl invariance of the Satake map): the part of the valuation of a
representative in the Borel subgroup that the embedded `SL(2, ℤ)` does not change. -/
def shortOutWeight (μ : SatakeWeight n) : SatakeWeight n :=
  .ofAdd (μ.toAdd.1, fun j ↦ if j = k ∨ j = k' then μ.toAdd.1 else μ.toAdd.2 j)

variable (k k') in
/-- The **block weight** `(0; d)` with `d_k = -e₁`, `d_{k'} = -e₂` and `d_j = 0` otherwise (LMFDB
`mf.siegel.lift`, through the Weyl invariance of the Satake map). -/
def shortBlockWeight (e₁ e₂ : ℕ) : SatakeWeight n :=
  .ofAdd (0, Pi.single k (-(e₁ : ℤ)) + Pi.single k' (-(e₂ : ℤ)))

lemma weylPerm_swap_shortOutWeight (μ : SatakeWeight n) :
    weylPerm (Equiv.swap k k') (shortOutWeight k k' μ) = shortOutWeight k k' μ := by
  simp only [weylPerm, shortOutWeight, MulEquiv.coe_mk, Equiv.coe_fn_mk, toAdd_ofAdd,
    Equiv.symm_swap]
  congr 2
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = k ∨ j = k'
  · rcases hj with rfl | rfl <;> simp
  · rw [Equiv.swap_apply_of_ne_of_ne (fun h ↦ hj (.inl h)) fun h ↦ hj (.inr h)]

lemma weylPerm_swap_shortBlockWeight (hkk' : k ≠ k') (e₁ e₂ : ℕ) :
    weylPerm (Equiv.swap k k') (shortBlockWeight k k' e₁ e₂) = shortBlockWeight k k' e₂ e₁ := by
  simp only [weylPerm, shortBlockWeight, MulEquiv.coe_mk, Equiv.coe_fn_mk]
  congr 2
  funext j
  simp only [Pi.add_apply]
  by_cases hjk : j = k
  · subst hjk
    simp [hkk']
  · by_cases hjk' : j = k'
    · subst hjk'
      simp [hkk']
    · simp [Equiv.swap_apply_of_ne_of_ne hjk hjk', hjk, hjk']

end Parabolic

/-! ### The reduction to `GL(2)` -/

section Reduction

variable (p : ℕ)
  (D : HeckeCoset (heckeMonoidAt (Fin n) p) (heckeGamma (Fin n)) (heckeGamma (Fin n)))
  {k k' : Fin n}

lemma mem_range_of_mem_heckeMonoidAt {x : GL (Fin n ⊕ Fin n) ℚ} (hx : x ∈ heckeMonoidAt (Fin n) p) :
    (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) ∈ (Int.castRingHom ℚ).mapMatrix.range :=
  hx.1.2

lemma rightCosetRep_mem_heckeMonoidAt (v : DecompQuotient (heckeGamma (Fin n)) (heckeGamma (Fin n))
    (D.out : GL (Fin n ⊕ Fin n) ℚ)⁻¹) : rightCosetRep D v ∈ heckeMonoidAt (Fin n) p :=
  rightCosetRep_mem D D.out.2 (IsHeckeTriple.right_le (H₁ := heckeGamma (Fin n))) v

lemma transpose_mul_J_mul_of_mem_heckeGamma {γ : GL (Fin n ⊕ Fin n) ℚ}
    (hγ : γ ∈ heckeGamma (Fin n)) : (γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ * J (Fin n) ℚ *
      (γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) = J (Fin n) ℚ := by
  rcases hγ with ⟨γ', -, rfl⟩
  exact SymplecticGroup.mem_iff'.mp (SymplecticGroup.map_mem γ'.2 (Int.castRingHom ℚ))

lemma mem_gspPlusGL_of_mem_heckeGamma {γ : GL (Fin n ⊕ Fin n) ℚ} (hγ : γ ∈ heckeGamma (Fin n)) :
    γ ∈ gspPlusGL (Fin n) :=
  heckeMonoid_le_gspPlusGL (heckeGamma_le_heckeMonoid hγ)

lemma borelMultiplier_eq_of_mul [NeZero n] {b b' : siegelBorel n} {γ γ' : GL (Fin n ⊕ Fin n) ℚ}
    (hγ : γ ∈ heckeGamma (Fin n)) (hγ' : γ' ∈ heckeGamma (Fin n))
    (h : (b' : GL (Fin n ⊕ Fin n) ℚ) = γ * b * γ') : borelMultiplier b' = borelMultiplier b := by
  refine multiplier_eq _ ?_
  have hb : ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ *
      J (Fin n) ℚ * ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) =
        borelMultiplier b • J (Fin n) ℚ :=
    transpose_mul_J_mul (⟨((b : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ), b.2.1⟩ : gspPlus (Fin n))
  have e : (((b' : GL (Fin n ⊕ Fin n) ℚ)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ *
      J (Fin n) ℚ * ((b' : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) =
        (γ' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ *
          (((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ *
            ((γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ * J (Fin n) ℚ *
              (γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)) *
            ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)) *
          (γ' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) := by
    rw [h]
    simp only [Units.val_mul, transpose_mul, Matrix.mul_assoc]
  rw [e, transpose_mul_J_mul_of_mem_heckeGamma hγ, hb, Matrix.mul_smul, Matrix.smul_mul,
    transpose_mul_J_mul_of_mem_heckeGamma hγ']

lemma coe_shortEmbed_inv (hkk' : k ≠ k') (u : SL(2, ℤ)) :
    ((shortEmbed hkk' u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ)⁻¹ =
      ((shortEmbed hkk' u⁻¹ : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) := by
  rw [map_inv, Subgroup.coe_inv]

lemma exists_shortEmbed_mul_mem (hk : (k' : ℕ) = k + 1) {b : GL (Fin n ⊕ Fin n) ℚ}
    (hb : b ∈ siegelBorel n) (hbZ : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) ∈
      (Int.castRingHom ℚ).mapMatrix.range) (h : SL(2, ℤ)) :
    ∃ u : SL(2, ℤ), ((shortEmbed (ne_of_short hk) u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) *
      b * ((shortEmbed (ne_of_short hk) h : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ)⁻¹ ∈
        siegelBorel n := by
  have hkk' : k ≠ k' := ne_of_short hk
  have hyP : IsShortParabolic k k' ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) *
      (((shortEmbed hkk' h⁻¹ : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)) :=
    (isShortParabolic_of_mem hk hb).mul (isShortParabolic_shortEmbed hkk' _)
  have hyZ : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) *
      (((shortEmbed hkk' h⁻¹ : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) ∈ (Int.castRingHom ℚ).mapMatrix.range :=
    mul_mem hbZ (mem_range_of_mem_heckeMonoidAt 1
      (heckeGamma_le_heckeMonoidAt 1 (shortEmbed hkk' h⁻¹).2))
  rcases SymplecticGroup.exists_SL2Z_eq_gcd
    (shortBlockZ k k' ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) *
      (((shortEmbed hkk' h⁻¹ : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)) 0 0)
    (shortBlockZ k k' ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) *
      (((shortEmbed hkk' h⁻¹ : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)) 1 0) with ⟨u, -, hu⟩
  refine ⟨u, mem_siegelBorel_of_isShortParabolic hk (mul_mem (mul_mem
    (mem_gspPlusGL_of_mem_heckeGamma (shortEmbed hkk' u).2) hb.1)
      (mem_gspPlusGL_of_mem_heckeGamma (inv_mem (shortEmbed hkk' h).2))) ?_ ?_⟩
  · rw [coe_shortEmbed_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc]
    exact (isShortParabolic_shortEmbed hkk' u).mul hyP
  · rw [coe_shortEmbed_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc]
    exact (congrFun (congrFun (shortBlock_mul hk (isShortParabolic_shortEmbed hkk' u) hyP) 1)
      0).trans (by rw [shortBlock_shortEmbed, ← map_shortBlockZ hyZ, ← Matrix.map_mul, map_apply,
        Matrix.mul_apply, Fin.sum_univ_two, hu, map_zero])

lemma exists_short_decomp (hk : (k' : ℕ) = k + 1) {b b' c₁ : GL (Fin n ⊕ Fin n) ℚ}
    (hb : b ∈ siegelBorel n) (hbZ : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) ∈
      (Int.castRingHom ℚ).mapMatrix.range) (hb' : b' ∈ siegelBorel n)
    (hc₁ : c₁ ∈ heckeGamma (Fin n)) (h : SL(2, ℤ))
    (he : b' = c₁ * b * ((shortEmbed (ne_of_short hk) h : heckeGamma (Fin n)) :
      GL (Fin n ⊕ Fin n) ℚ)⁻¹) :
    ∃ (u : SL(2, ℤ)) (c : GL (Fin n ⊕ Fin n) ℚ), c ∈ heckeGamma (Fin n) ∧ c ∈ siegelBorel n ∧
      ((shortEmbed (ne_of_short hk) u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) * b *
        ((shortEmbed (ne_of_short hk) h : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ)⁻¹ ∈
          siegelBorel n ∧
      b' = c * (((shortEmbed (ne_of_short hk) u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) * b *
        ((shortEmbed (ne_of_short hk) h : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ)⁻¹) := by
  rcases exists_shortEmbed_mul_mem hk hb hbZ h with ⟨u, hy⟩
  have he' : b' = c₁ * ((shortEmbed (ne_of_short hk) u : heckeGamma (Fin n)) :
      GL (Fin n ⊕ Fin n) ℚ)⁻¹ * (((shortEmbed (ne_of_short hk) u : heckeGamma (Fin n)) :
        GL (Fin n ⊕ Fin n) ℚ) * b * ((shortEmbed (ne_of_short hk) h : heckeGamma (Fin n)) :
          GL (Fin n ⊕ Fin n) ℚ)⁻¹) := by
    rw [he]
    group
  refine ⟨u, _, mul_mem hc₁ (inv_mem (shortEmbed (ne_of_short hk) u).2), ?_, hy, he'⟩
  rw [eq_mul_inv_of_mul_eq he'.symm]
  exact mul_mem hb' (inv_mem hy)

lemma isUnit_shortBlockZ (hk : (k' : ℕ) = k + 1) {c : GL (Fin n ⊕ Fin n) ℚ}
    (hc : c ∈ heckeGamma (Fin n)) (hcB : c ∈ siegelBorel n) :
    shortBlockZ k k' (c : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) *
      shortBlockZ k k' ((c⁻¹ : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) =
        1 := by
  have hc' : c⁻¹ ∈ heckeGamma (Fin n) := inv_mem hc
  refine Matrix.map_injective (RingHom.injective_int (Int.castRingHom ℚ)) ?_
  dsimp only
  rw [Matrix.map_mul, map_shortBlockZ (mem_range_of_mem_heckeMonoidAt 1
    (heckeGamma_le_heckeMonoidAt 1 hc)), map_shortBlockZ (mem_range_of_mem_heckeMonoidAt 1
      (heckeGamma_le_heckeMonoidAt 1 hc')), ← shortBlock_mul hk
        (isShortParabolic_of_mem hk hcB) (isShortParabolic_of_mem hk (inv_mem hcB)),
    ← Units.val_mul, mul_inv_cancel, Units.val_one, shortBlock_one (ne_of_short hk),
    Matrix.map_one _ (map_zero _) (map_one _)]

lemma isUnit_shortBlockZ' (hk : (k' : ℕ) = k + 1) {c : GL (Fin n ⊕ Fin n) ℚ}
    (hc : c ∈ heckeGamma (Fin n)) (hcB : c ∈ siegelBorel n) :
    shortBlockZ k k' ((c⁻¹ : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) *
      shortBlockZ k k' (c : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) = 1 := by
  simpa using isUnit_shortBlockZ hk (inv_mem hc) (inv_mem hcB)

lemma exists_shortBlockZ_eq (hk : (k' : ℕ) = k + 1) {b b' c₁ : GL (Fin n ⊕ Fin n) ℚ}
    (hb : b ∈ siegelBorel n) (hbZ : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) ∈
      (Int.castRingHom ℚ).mapMatrix.range) (hb' : b' ∈ siegelBorel n)
    (hb'Z : (b' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) ∈ (Int.castRingHom ℚ).mapMatrix.range)
    (hc₁ : c₁ ∈ heckeGamma (Fin n)) (h : SL(2, ℤ))
    (he : b' = c₁ * b * ((shortEmbed (ne_of_short hk) h : heckeGamma (Fin n)) :
      GL (Fin n ⊕ Fin n) ℚ)⁻¹) :
    ∃ U : GL (Fin 2) ℤ, shortBlockZ k k' (b' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) =
      U * shortBlockZ k k' (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) *
        ((h⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hkk' : k ≠ k' := ne_of_short hk
  rcases exists_short_decomp hk hb hbZ hb' hc₁ h he with ⟨u, c, hc, hcB, hy, rfl⟩
  have hcZ : (c : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) ∈ (Int.castRingHom ℚ).mapMatrix.range :=
    mem_range_of_mem_heckeMonoidAt 1 (heckeGamma_le_heckeMonoidAt 1 hc)
  have hU : ((⟨_, _, isUnit_shortBlockZ hk hc hcB, isUnit_shortBlockZ' hk hc hcB⟩ * u.toGL :
      GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
        shortBlockZ k k' (c : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) * u := by
    rw [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix]
  refine ⟨⟨_, _, isUnit_shortBlockZ hk hc hcB, isUnit_shortBlockZ' hk hc hcB⟩ * u.toGL, ?_⟩
  rw [hU]
  refine Matrix.map_injective (RingHom.injective_int (Int.castRingHom ℚ)) ?_
  dsimp only
  rw [map_shortBlockZ hb'Z, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, map_shortBlockZ hcZ,
    map_shortBlockZ hbZ, Units.val_mul,
    shortBlock_mul hk (isShortParabolic_of_mem hk hcB) (isShortParabolic_of_mem hk hy),
    coe_shortEmbed_inv, Units.val_mul, Units.val_mul,
    shortBlock_mul hk ((isShortParabolic_shortEmbed hkk' u).mul (isShortParabolic_of_mem hk hb))
      (isShortParabolic_shortEmbed hkk' _),
    shortBlock_mul hk (isShortParabolic_shortEmbed hkk' u) (isShortParabolic_of_mem hk hb),
    shortBlock_shortEmbed, shortBlock_shortEmbed]
  simp only [Matrix.mul_assoc]

variable [Fact p.Prime]

lemma coe_satakeCharacterUniv_shortBlockWeight (hk : (k' : ℕ) = k + 1) (e₁ e₂ : ℕ) :
    (satakeCharacterUniv p (shortBlockWeight k k' e₁ e₂) : SatakeLaurent n) =
      single (shortBlockWeight k k' e₁ e₂)
        ((p : ℂ) ^ ((n - (k : ℕ)) * e₁ + (n - (k' : ℕ)) * e₂)) := by
  have hkk' : k ≠ k' := ne_of_short hk
  rw [coe_satakeCharacterUniv]
  congr 1
  simp only [weightCharacter, shortBlockWeight, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    (one_zpow : ∀ m : ℤ, (1 : ℂˣ) ^ m = 1), one_mul]
  rw [Fintype.prod_eq_mul k k' hkk' fun i hi ↦ by simp [hi.1, hi.2]]
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hkk',
    Pi.single_eq_of_ne hkk'.symm, add_zero, zero_add, Units.val_mul, Units.val_zpow_eq_zpow_val,
    Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, primeUnit, Units.val_mk0]
  rw [zpow_neg ((p : ℂ)⁻¹ ^ (n - (k : ℕ))), zpow_neg ((p : ℂ)⁻¹ ^ (n - (k' : ℕ))), zpow_natCast,
    zpow_natCast, ← pow_mul, ← pow_mul, inv_pow, inv_pow, inv_inv, inv_inv, pow_add]

lemma domCongr_weylPerm_swap_shortBlockWeight (hk : (k' : ℕ) = k + 1) (e₁ e₂ : ℕ) :
    domCongr ℂ ℂ (weylPerm (Equiv.swap k k'))
        (satakeCharacterUniv p (shortBlockWeight k k' e₁ e₂) : SatakeLaurent n) =
      ((p : ℂ) ^ (e₁ : ℤ) * (p : ℂ) ^ (-(e₂ : ℤ))) •
        (satakeCharacterUniv p (shortBlockWeight k k' e₂ e₁) : SatakeLaurent n) := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hn : n - (k : ℕ) = n - (k' : ℕ) + 1 := by
    have hk' : (k' : ℕ) < n := k'.isLt
    omega
  rw [coe_satakeCharacterUniv_shortBlockWeight p hk, coe_satakeCharacterUniv_shortBlockWeight p hk,
    domCongr_single, weylPerm_swap_shortBlockWeight (ne_of_short hk), MonoidAlgebra.smul_single,
    smul_eq_mul, hn]
  congr 1
  rw [← zpow_natCast, ← zpow_natCast (p : ℂ) ((n - (k' : ℕ) + 1) * e₂ + (n - (k' : ℕ)) * e₁),
    ← zpow_add₀ hp, ← zpow_add₀ hp]
  congr 1
  push_cast
  ring1

variable [NeZero n]

lemma shortOutWeight_satakeValuation_eq (hk : (k' : ℕ) = k + 1) {b b' c₁ : GL (Fin n ⊕ Fin n) ℚ}
    (hb : b ∈ siegelBorel n) (hbZ : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) ∈
      (Int.castRingHom ℚ).mapMatrix.range) (hb' : b' ∈ siegelBorel n)
    (hc₁ : c₁ ∈ heckeGamma (Fin n)) (h : SL(2, ℤ))
    (he : b' = c₁ * b * ((shortEmbed (ne_of_short hk) h : heckeGamma (Fin n)) :
      GL (Fin n ⊕ Fin n) ℚ)⁻¹) :
    shortOutWeight k k' (satakeValuation p ⟨b', hb'⟩) =
      shortOutWeight k k' (satakeValuation p ⟨b, hb⟩) := by
  have hkk' : k ≠ k' := ne_of_short hk
  rcases exists_short_decomp hk hb hbZ hb' hc₁ h he with ⟨u, c, hc, hcB, hy, rfl⟩
  have hsplit : (⟨_, hb'⟩ : siegelBorel n) = ⟨c, hcB⟩ * ⟨_, hy⟩ := rfl
  have hr : borelMultiplier ⟨_, hy⟩ = borelMultiplier ⟨b, hb⟩ :=
    borelMultiplier_eq_of_mul (shortEmbed hkk' u).2 (inv_mem (shortEmbed hkk' h).2) rfl
  have hd (j : Fin n) (hj : ¬(j = k ∨ j = k')) : borelDiag ⟨_, hy⟩ j = borelDiag ⟨b, hb⟩ j := by
    simp only [borelDiag]
    rw [coe_shortEmbed_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc,
      shortEmbed_mul_apply hkk' u _ (fun h ↦ hj (.inl h)) fun h ↦ hj (.inr h),
      mul_shortEmbed_apply hkk' _ _ (fun h ↦ hj (.inl h)) fun h ↦ hj (.inr h)]
  rw [hsplit, map_mul, satakeValuation_eq_one p hc, one_mul]
  simp only [shortOutWeight, satakeValuation, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, hr]
  congr 2
  funext j
  split_ifs with hj
  · rfl
  · rw [hd j hj]

lemma satakeValuation_eq_shortOutWeight_mul (hk : (k' : ℕ) = k + 1) {b : siegelBorel n}
    (hb : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p) :
    satakeValuation p b = shortOutWeight k k' (satakeValuation p b) * shortBlockWeight k k'
      (hnfData p (shortBlockZ k k' ((b : GL (Fin n ⊕ Fin n) ℚ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ))).1
      (hnfData p (shortBlockZ k k' ((b : GL (Fin n ⊕ Fin n) ℚ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ))).2.1 := by
  have hkk'lt : k < k' := Fin.lt_def.mpr (by omega)
  have hval (j : Fin n) : padicValRat p (((b : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) (.inl j) (.inl j)) =
        padicValNat p (((b : GL (Fin n ⊕ Fin n) ℚ) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) (.inl j) (.inl j)).num.natAbs := by
    rcases exists_natAbs_num_borelDiag hb j with ⟨-, -, hj⟩
    have h :
        padicValRat p ((borelDiag b j).num : ℚ) = padicValNat p (borelDiag b j).num.natAbs := by
      rw [padicValRat.of_int]
      rfl
    rwa [hj] at h
  rcases exists_natAbs_num_borelDiag hb k with ⟨a, ha, -⟩
  have h0 : ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)
      (.inl k') (.inl k) = 0 :=
    b.2.2.2 hkk'lt
  have h10 : shortBlockZ k k' ((b : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) 1 0 = 0 := by
    simp [shortBlockZ, shortBlock, h0]
  have hdet : (shortBlockZ k k' ((b : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)).det ≠ 0 := by
    rcases exists_natAbs_num_borelDiag hb k' with ⟨a', ha', -⟩
    rw [det_fin_two, h10, mul_zero, sub_zero]
    refine mul_ne_zero (fun h ↦ ?_) fun h ↦ ?_
    · have h' : (borelDiag b k).num = 0 := h
      rw [h', Int.natAbs_zero] at ha
      exact pow_ne_zero a (Fact.out : p.Prime).ne_zero ha.symm
    · have h' : (borelDiag b k').num = 0 := h
      rw [h', Int.natAbs_zero] at ha'
      exact pow_ne_zero a' (Fact.out : p.Prime).ne_zero ha'.symm
  rw [hnfData_eq_upperData p h10 hdet]
  simp only [shortOutWeight, shortBlockWeight, satakeValuation, MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  refine Prod.ext (add_zero _).symm (funext fun j ↦ ?_)
  by_cases hjk : j = k
  · subst hjk
    simp [ne_of_short hk, upperData, shortBlockZ, shortBlock, borelDiag, hval, sub_eq_add_neg]
  · by_cases hjk' : j = k'
    · subst hjk'
      simp [(ne_of_short hk).symm, upperData, shortBlockZ, shortBlock, borelDiag, hval,
        sub_eq_add_neg]
    · simp [hjk, hjk']

lemma exists_natAbs_det_shortBlockZ (hk : (k' : ℕ) = k + 1) {b : siegelBorel n}
    (hb : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p) : ∃ K : ℕ, (shortBlockZ k k'
      ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)).det.natAbs =
        p ^ K := by
  rcases exists_natAbs_num_borelDiag hb k with ⟨a, ha, -⟩
  rcases exists_natAbs_num_borelDiag hb k' with ⟨a', ha', -⟩
  have hkk'lt : k < k' := Fin.lt_def.mpr (by omega)
  have h0 : ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)
      (.inl k') (.inl k) = 0 :=
    b.2.2.2 hkk'lt
  refine ⟨a + a', ?_⟩
  rw [det_fin_two, show shortBlockZ k k' ((b : GL (Fin n ⊕ Fin n) ℚ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) 1 0 = 0 by simp [shortBlockZ, shortBlock, h0],
    mul_zero, sub_zero, Int.natAbs_mul, pow_add]
  exact congrArg₂ (· * ·) ha ha'

/-- **The universal Satake map is invariant under the transposition of two consecutive
coordinates** (LMFDB `mf.siegel.lift`, through the Weyl invariance of the Satake map): for
`k' = k + 1`, the universal Satake map `Ω(ΓαΓ)` of every double coset of the local Hecke algebra of
`Sp(2g, ℤ)` at `p` is fixed by the exchange of `x_k` and `x_{k'}`. The embedded `SL(2, ℤ)` on
`(e_k, e_{k'})` acts on the right cosets; the representatives in the Borel subgroup change by right
multiplication of their block at `(k, k')` up to `GL(2, ℤ)` on the left, their other valuations do
not change, and the rank-one count `SiegelUpperHalfSpace.sum_mul_hnfData_eq` applies, the shifts
`p^{-(g-k)}` and `p^{-(g-k')}` differing by one power of `p`. -/
lemma domCongr_weylPerm_swap_satakeMapUniv (hk : (k' : ℕ) = k + 1) :
    domCongr ℂ ℂ (weylPerm (Equiv.swap k k')) (satakeMapUniv p (single ℂ D 1)) =
      satakeMapUniv p (single ℂ D 1) := by
  have hkk' : k ≠ k' := ne_of_short hk
  have hmem (v : DecompQuotient (heckeGamma (Fin n)) (heckeGamma (Fin n))
      (D.out : GL (Fin n ⊕ Fin n) ℚ)⁻¹) : ((borelRep (rightCosetRep_mem_gspPlusGL p D v) :
        siegelBorel n) : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p :=
    borelRep_mem_heckeMonoidAt (rightCosetRep_mem_heckeMonoidAt p D v) _
  have hval (b : siegelBorel n) (hb : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p) :
      (satakeCharacterUniv p (satakeValuation p b) : SatakeLaurent n) =
        (satakeCharacterUniv p (shortOutWeight k k' (satakeValuation p b)) : SatakeLaurent n) *
          (satakeCharacterUniv p (shortBlockWeight k k'
            (hnfData p (shortBlockZ k k' ((b : GL (Fin n ⊕ Fin n) ℚ) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ))).1
            (hnfData p (shortBlockZ k k' ((b : GL (Fin n ⊕ Fin n) ℚ) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ))).2.1) : SatakeLaurent n) := by
    rw [← Units.val_mul, ← map_mul, ← satakeValuation_eq_shortOutWeight_mul p hk hb]
  have hval' (b : siegelBorel n) (hb : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p) :
      domCongr ℂ ℂ (weylPerm (Equiv.swap k k'))
          (satakeCharacterUniv p (satakeValuation p b) : SatakeLaurent n) =
        (satakeCharacterUniv p (shortOutWeight k k' (satakeValuation p b)) : SatakeLaurent n) *
          domCongr ℂ ℂ (weylPerm (Equiv.swap k k')) (satakeCharacterUniv p (shortBlockWeight k k'
            (hnfData p (shortBlockZ k k' ((b : GL (Fin n ⊕ Fin n) ℚ) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ))).1
            (hnfData p (shortBlockZ k k' ((b : GL (Fin n ⊕ Fin n) ℚ) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ))).2.1) : SatakeLaurent n) := by
    rw [hval b hb, map_mul, coe_satakeCharacterUniv (shortOutWeight k k' _) p, domCongr_single,
      weylPerm_swap_shortOutWeight]
  rw [satakeMapUniv_single_one, map_sum, Finset.sum_congr rfl fun v _ ↦ hval' _ (hmem v),
    Finset.sum_congr rfl fun v _ ↦ hval _ (hmem v)]
  refine sum_mul_hnfData_eq (hX := MulAction.compHom _ (shortEmbed hkk')) p
    (fun v ↦ shortBlockZ k k' ((borelRep (rightCosetRep_mem_gspPlusGL p D v) :
      GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ))
    (fun v ↦ exists_natAbs_det_shortBlockZ p hk (hmem v)) (fun h v ↦ ?_)
    (fun v ↦ (satakeCharacterUniv p (shortOutWeight k k' (satakeValuation p
      (borelRep (rightCosetRep_mem_gspPlusGL p D v)))) : SatakeLaurent n)) (fun h v ↦ ?_)
    (fun e₁ e₂ ↦ (satakeCharacterUniv p (shortBlockWeight k k' e₁ e₂) : SatakeLaurent n))
    (fun e₁ e₂ ↦ domCongr ℂ ℂ (weylPerm (Equiv.swap k k'))
      (satakeCharacterUniv p (shortBlockWeight k k' e₁ e₂) : SatakeLaurent n))
    fun e₁ e₂ ↦ domCongr_weylPerm_swap_shortBlockWeight p hk e₁ e₂
  · rcases exists_borelRep_smul_eq p D (shortEmbed hkk' h) v with ⟨c, hc, he⟩
    exact exists_shortBlockZ_eq hk (borelRep _).2 (mem_range_of_mem_heckeMonoidAt p (hmem v))
      (borelRep _).2 (mem_range_of_mem_heckeMonoidAt p (hmem _)) hc h he
  · rcases exists_borelRep_smul_eq p D (shortEmbed hkk' h) v with ⟨c, hc, he⟩
    exact congrArg (fun μ ↦ (satakeCharacterUniv p μ : SatakeLaurent n))
      (shortOutWeight_satakeValuation_eq p hk (borelRep _).2
        (mem_range_of_mem_heckeMonoidAt p (hmem v)) (borelRep _).2 hc h he)

end Reduction

end SiegelUpperHalfSpace
