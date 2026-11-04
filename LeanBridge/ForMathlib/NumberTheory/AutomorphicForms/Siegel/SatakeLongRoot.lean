import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SatakeShortRoot

/-!
# The Weyl invariance of the Satake map under the sign change of the last coordinate

Let `j₀ = g - 1` be the last coordinate. The parabolic subgroup `P ⊇ B` of the `(A, B; C, D)` with
`A` upper triangular, `D` lower triangular and `C` zero but for its entry `(j₀, j₀)` has the Levi
factor `GL(2)` on `(e_{j₀}, f_{j₀})`, and the embedded `SL(2, ℤ)` on these coordinates
(`SiegelUpperHalfSpace.longEmbed`) acts on the right cosets of a double coset by right
multiplication. The block `(A_{j₀j₀}, B_{j₀j₀}; C_{j₀j₀}, D_{j₀j₀})` of the representatives in the
Borel subgroup changes by right multiplication up to `GL(2, ℤ)` on the left, and the other
valuations do not change. Its determinant is the multiplier `p^δ`; the valuation at `j₀` is the
exponent `e₂` of `D_{j₀j₀}`, which the sign change exchanges with the exponent `e₁ = δ - e₂` of
`A_{j₀j₀}`, while the shift `p^{-1}` at `j₀` accounts for the factor `p^{e₁ - e₂}`. So the rank-one
count `SiegelUpperHalfSpace.sum_mul_hnfData_eq` applies: the universal Satake map of every double
coset is invariant under the sign change of the last coordinate.

## Main definitions

* `SiegelUpperHalfSpace.longMat`: the matrix acting by a `2 × 2` matrix on `(e_{j₀}, f_{j₀})`.
* `SiegelUpperHalfSpace.longEmbed`: `SL(2, ℤ)` embedded in `Sp(2g, ℤ)` on `(e_{j₀}, f_{j₀})`.
* `SiegelUpperHalfSpace.IsLongParabolic`: the parabolic subgroup of the sign change.
* `SiegelUpperHalfSpace.longBlock`: its `2 × 2` block at `(e_{j₀}, f_{j₀})`.

## Main results

* `SiegelUpperHalfSpace.domCongr_weylSign_last_satakeMapUniv`: the universal Satake map of a
  double coset is invariant under the sign change of the last coordinate.
-/

open Matrix DoubleCoset MonoidAlgebra

open scoped MatrixGroups

open HeckeCosetModule (single)

namespace SiegelUpperHalfSpace

variable {n : ℕ}

attribute [local instance] Fintype.ofFinite

/-! ### `SL(2)` on the last coordinate pair -/

section Embed

variable (j₀ : Fin n) {R : Type*} [CommRing R]

/-- The **matrix acting by `h` on the coordinates `(e_{j₀}, f_{j₀})`** and by the identity on the
others (LMFDB `mf.siegel.lift`, through the Weyl invariance of the Satake map). -/
def longMat (h : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  fromBlocks (diagonal (Function.update 1 j₀ (h 0 0))) (diagonal (Pi.single j₀ (h 0 1)))
    (diagonal (Pi.single j₀ (h 1 0))) (diagonal (Function.update 1 j₀ (h 1 1)))

variable (h h' : Matrix (Fin 2) (Fin 2) R)

lemma longMat_mul : longMat j₀ (h * h') = longMat j₀ h * longMat j₀ h' := by
  rw [longMat, longMat, longMat, fromBlocks_multiply]
  simp only [diagonal_mul_diagonal, diagonal_add]
  congr 1 <;> refine congrArg diagonal (funext fun c ↦ ?_) <;>
    rcases eq_or_ne c j₀ with rfl | hc <;>
      simp [Matrix.mul_apply, *]

lemma longMat_one : longMat j₀ (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  simp [longMat]

lemma longMat_mem (u : SL(2, R)) :
    longMat j₀ (u : Matrix (Fin 2) (Fin 2) R) ∈ symplecticGroup (Fin n) R := by
  refine SymplecticGroup.fromBlocks_mem_iff.mpr ⟨?_, ?_, ?_⟩
  · simp only [diagonal_transpose, diagonal_mul_diagonal, mul_comm]
  · simp only [diagonal_transpose, diagonal_mul_diagonal, mul_comm]
  · rw [diagonal_transpose, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal,
      diagonal_sub, ← diagonal_one]
    refine congrArg diagonal (funext fun c ↦ ?_)
    have hu : (u : Matrix (Fin 2) (Fin 2) R).det = 1 := u.2
    rw [det_fin_two] at hu
    rcases eq_or_ne c j₀ with rfl | hc
    · simp only [Function.update_self, Pi.single_eq_same]
      linear_combination hu
    · simp [Function.update_of_ne hc, Pi.single_eq_of_ne hc]

/-- The **integral symplectic matrix acting by `h ∈ SL(2, ℤ)` on `(e_{j₀}, f_{j₀})`** (LMFDB
`mf.siegel.lift`, through the Weyl invariance of the Satake map). -/
def longEmbedSp : SL(2, ℤ) →* symplecticGroup (Fin n) ℤ where
  toFun u := ⟨longMat j₀ (u : Matrix (Fin 2) (Fin 2) ℤ), longMat_mem j₀ u⟩
  map_one' := Subtype.ext <| by simp [longMat_one]
  map_mul' u u' := Subtype.ext <| by simp [longMat_mul]

/-- `SL(2, ℤ)` **embedded in `Γ = Sp(2g, ℤ)` on the coordinates `(e_{j₀}, f_{j₀})`** (LMFDB
`mf.siegel.lift`, through the Weyl invariance of the Satake map), acting by the identity on the
other coordinates. -/
def longEmbed : SL(2, ℤ) →* heckeGamma (Fin n) :=
  ((spToGL (Fin n)).comp (longEmbedSp j₀)).codRestrict (heckeGamma (Fin n))
    fun u ↦ ⟨longEmbedSp j₀ u, trivial, rfl⟩

lemma coe_longEmbed (u : SL(2, ℤ)) : (((longEmbed j₀ u : heckeGamma (Fin n)) :
    GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) =
      (longMat j₀ (u : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.castRingHom ℚ) :=
  rfl

variable {j₀} (u : SL(2, ℤ)) (y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) {a : Fin n}

lemma longEmbed_mul_apply (ha : a ≠ j₀) :
    ((((longEmbed j₀ u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) * y) (.inl a) (.inl a) = y (.inl a) (.inl a) := by
  rw [coe_longEmbed, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [longMat, diagonal_apply, Function.update_of_ne ha, Pi.single_eq_of_ne ha]

lemma mul_longEmbed_apply (ha : a ≠ j₀) :
    (y * (((longEmbed j₀ u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)) (.inl a) (.inl a) = y (.inl a) (.inl a) := by
  rw [coe_longEmbed, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [longMat, diagonal_apply, Function.update_of_ne ha, Pi.single_eq_of_ne ha]

end Embed

/-! ### The parabolic subgroup of the sign change -/

section Parabolic

variable (j₀ : Fin n)

/-- The **parabolic subgroup of the sign change at `j₀`** (LMFDB `mf.siegel.lift`, through the Weyl
invariance of the Satake map): the `(A, B; C, D)` with `A` upper triangular, `D` lower triangular
and `C` zero but for its entry `(j₀, j₀)`. -/
def IsLongParabolic (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) : Prop :=
  (∀ a c : Fin n, c < a → x (.inl a) (.inl c) = 0) ∧
    (∀ a c : Fin n, a < c → x (.inr a) (.inr c) = 0) ∧
      ∀ a c : Fin n, ¬(a = j₀ ∧ c = j₀) → x (.inr a) (.inl c) = 0

/-- The **`2 × 2` block of a matrix at the coordinates `(e_{j₀}, f_{j₀})`** (LMFDB
`mf.siegel.lift`, through the Weyl invariance of the Satake map). -/
def longBlock (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  of fun i j ↦ x (![.inl j₀, .inr j₀] i) (![.inl j₀, .inr j₀] j)

/-- The **integral `2 × 2` block at `(e_{j₀}, f_{j₀})`** of an integral matrix (LMFDB
`mf.siegel.lift`, through the Weyl invariance of the Satake map). -/
def longBlockZ (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) : Matrix (Fin 2) (Fin 2) ℤ :=
  (longBlock j₀ x).map Rat.num

variable {j₀} {x y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ}

lemma le_of_last (hj₀ : (j₀ : ℕ) + 1 = n) (c : Fin n) : c ≤ j₀ :=
  Fin.le_def.mpr (by omega)

lemma isLongParabolic_of_mem {b : GL (Fin n ⊕ Fin n) ℚ} (hb : b ∈ siegelBorel n) :
    IsLongParabolic j₀ (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) :=
  ⟨fun _ _ hca ↦ hb.2.2 hca, fun _ _ hac ↦ apply_inr_inr_eq_zero ⟨b, hb⟩ hac,
    fun a c _ ↦ congrFun (congrFun hb.2.1 a) c⟩

lemma IsLongParabolic.mul (hj₀ : (j₀ : ℕ) + 1 = n) (hx : IsLongParabolic j₀ x)
    (hy : IsLongParabolic j₀ y) : IsLongParabolic j₀ (x * y) := by
  refine ⟨fun a c hca ↦ ?_, fun a c hac ↦ ?_, fun a c hac ↦ ?_⟩
  · rw [Matrix.mul_apply, Fintype.sum_sum_type]
    refine (congrArg₂ (· + ·) (Finset.sum_eq_zero fun m _ ↦ ?_)
      (Finset.sum_eq_zero fun m _ ↦ ?_)).trans (add_zero 0)
    · rcases lt_or_ge m a with hma | hma
      · rw [hx.1 a m hma, zero_mul]
      · rw [hy.1 m c (lt_of_lt_of_le hca hma), mul_zero]
    · rw [hy.2.2 m c fun h ↦ (lt_irrefl _ (lt_of_lt_of_le (h.2 ▸ hca) (le_of_last hj₀ a))),
        mul_zero]
  · rw [Matrix.mul_apply, Fintype.sum_sum_type]
    refine (congrArg₂ (· + ·) (Finset.sum_eq_zero fun m _ ↦ ?_)
      (Finset.sum_eq_zero fun m _ ↦ ?_)).trans (add_zero 0)
    · rw [hx.2.2 a m fun h ↦ (lt_irrefl _ (lt_of_lt_of_le (h.1 ▸ hac) (le_of_last hj₀ c))),
        zero_mul]
    · rcases lt_or_ge a m with ham | ham
      · rw [hx.2.1 a m ham, zero_mul]
      · rw [hy.2.1 m c (lt_of_le_of_lt ham hac), mul_zero]
  · rw [Matrix.mul_apply, Fintype.sum_sum_type]
    refine (congrArg₂ (· + ·) (Finset.sum_eq_zero fun m _ ↦ ?_)
      (Finset.sum_eq_zero fun m _ ↦ ?_)).trans (add_zero 0)
    · by_cases hm : a = j₀ ∧ m = j₀
      · rcases hm with ⟨ha, hm⟩
        have hc : c < j₀ := lt_of_le_of_ne (le_of_last hj₀ c) fun h ↦ hac ⟨ha, h⟩
        rw [hm, hy.1 j₀ c hc, mul_zero]
      · rw [hx.2.2 a m hm, zero_mul]
    · by_cases hm : m = j₀ ∧ c = j₀
      · rcases hm with ⟨hm, hc⟩
        have ha : a < j₀ := lt_of_le_of_ne (le_of_last hj₀ a) fun h ↦ hac ⟨h, hc⟩
        rw [hm, hx.2.1 a j₀ ha, zero_mul]
      · rw [hy.2.2 m c hm, mul_zero]

lemma isLongParabolic_longEmbed (u : SL(2, ℤ)) :
    IsLongParabolic j₀ (((longEmbed j₀ u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) := by
  refine ⟨fun a c hca ↦ ?_, fun a c hac ↦ ?_, fun a c hac ↦ ?_⟩ <;>
    simp only [coe_longEmbed, map_apply, longMat, fromBlocks_apply₁₁, fromBlocks_apply₂₂,
      fromBlocks_apply₂₁, diagonal_apply]
  · rw [ite_eq_right hca.ne', map_zero]
  · rw [ite_eq_right hac.ne, map_zero]
  · by_cases h : a = c
    · subst h
      rw [ite_eq_left rfl, Pi.single_eq_of_ne fun h ↦ hac ⟨h, h⟩, map_zero]
    · rw [ite_eq_right h, map_zero]

lemma mem_siegelBorel_of_isLongParabolic {g : GL (Fin n ⊕ Fin n) ℚ} (hg : g ∈ gspPlusGL (Fin n))
    (hP : IsLongParabolic j₀ (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ))
    (h₀ : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) (.inr j₀) (.inl j₀) = 0) :
    g ∈ siegelBorel n := by
  refine ⟨hg, ?_, fun a c hca ↦ hP.1 a c hca⟩
  ext a c
  by_cases h : a = j₀ ∧ c = j₀
  · rcases h with ⟨rfl, rfl⟩
    exact h₀
  · exact hP.2.2 a c h

lemma longBlock_mul (hj₀ : (j₀ : ℕ) + 1 = n) (hx : IsLongParabolic j₀ x)
    (hy : IsLongParabolic j₀ y) : longBlock j₀ (x * y) = longBlock j₀ x * longBlock j₀ y := by
  have hxl (i : Fin 2) (c : Fin n) (hc : c ≠ j₀) : x (![.inl j₀, .inr j₀] i) (.inl c) = 0 := by
    fin_cases i
    · exact hx.1 j₀ c (lt_of_le_of_ne (le_of_last hj₀ c) hc)
    · exact hx.2.2 j₀ c fun h ↦ hc h.2
  have hyr (j : Fin 2) (c : Fin n) (hc : c ≠ j₀) : y (.inr c) (![.inl j₀, .inr j₀] j) = 0 := by
    fin_cases j
    · exact hy.2.2 c j₀ fun h ↦ hc h.1
    · exact hy.2.1 c j₀ (lt_of_le_of_ne (le_of_last hj₀ c) hc)
  ext i j
  simp only [longBlock, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  rw [Fintype.sum_eq_single j₀ fun c hc ↦ by rw [hxl i c hc, zero_mul],
    Fintype.sum_eq_single j₀ fun c hc ↦ by rw [hyr j c hc, mul_zero]]
  rfl

lemma longBlock_longEmbed (u : SL(2, ℤ)) :
    longBlock j₀ (((longEmbed j₀ u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) =
        (u : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [longBlock, coe_longEmbed, longMat]

lemma longBlock_one : longBlock j₀ 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [longBlock, one_apply]

lemma map_longBlockZ (hx : x ∈ (Int.castRingHom ℚ).mapMatrix.range) :
    (longBlockZ j₀ x).map (Int.castRingHom ℚ) = longBlock j₀ x := by
  rcases hx with ⟨M, rfl⟩
  ext i j
  simp [longBlockZ, longBlock]

variable (j₀) in
/-- The **outer weight**, `(δ; d)` with `d_{j₀}` replaced by `0` (LMFDB `mf.siegel.lift`, through
the Weyl invariance of the Satake map): the part of the valuation of a representative in the Borel
subgroup that the embedded `SL(2, ℤ)` does not change. -/
def longOutWeight (μ : SatakeWeight n) : SatakeWeight n :=
  .ofAdd (μ.toAdd.1, Function.update μ.toAdd.2 j₀ 0)

variable (j₀) in
/-- The **block weight** `(0; d)` with `d_{j₀} = e` and `d_j = 0` otherwise (LMFDB
`mf.siegel.lift`, through the Weyl invariance of the Satake map). -/
def longBlockWeight (e : ℕ) : SatakeWeight n :=
  .ofAdd (0, Pi.single j₀ (e : ℤ))

end Parabolic

/-! ### The reduction to `GL(2)` -/

section Reduction

variable (p : ℕ)
  (D : HeckeCoset (heckeMonoidAt (Fin n) p) (heckeGamma (Fin n)) (heckeGamma (Fin n)))
  {j₀ : Fin n}

lemma coe_longEmbed_inv (u : SL(2, ℤ)) :
    ((longEmbed j₀ u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ)⁻¹ =
      ((longEmbed j₀ u⁻¹ : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) := by
  rw [map_inv, Subgroup.coe_inv]

lemma exists_longEmbed_mul_mem (hj₀ : (j₀ : ℕ) + 1 = n) {b : GL (Fin n ⊕ Fin n) ℚ}
    (hb : b ∈ siegelBorel n) (hbZ : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) ∈
      (Int.castRingHom ℚ).mapMatrix.range) (h : SL(2, ℤ)) :
    ∃ u : SL(2, ℤ), ((longEmbed j₀ u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) * b *
      ((longEmbed j₀ h : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ)⁻¹ ∈ siegelBorel n := by
  have hyP : IsLongParabolic j₀ ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) *
      (((longEmbed j₀ h⁻¹ : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)) :=
    (isLongParabolic_of_mem hb).mul hj₀ (isLongParabolic_longEmbed _)
  have hyZ : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) *
      (((longEmbed j₀ h⁻¹ : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) ∈ (Int.castRingHom ℚ).mapMatrix.range :=
    mul_mem hbZ (mem_range_of_mem_heckeMonoidAt 1
      (heckeGamma_le_heckeMonoidAt 1 (longEmbed j₀ h⁻¹).2))
  rcases SymplecticGroup.exists_SL2Z_eq_gcd
    (longBlockZ j₀ ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) *
      (((longEmbed j₀ h⁻¹ : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)) 0 0)
    (longBlockZ j₀ ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) *
      (((longEmbed j₀ h⁻¹ : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)) 1 0) with ⟨u, -, hu⟩
  refine ⟨u, mem_siegelBorel_of_isLongParabolic (j₀ := j₀) (mul_mem (mul_mem
    (mem_gspPlusGL_of_mem_heckeGamma (longEmbed j₀ u).2) hb.1)
      (mem_gspPlusGL_of_mem_heckeGamma (inv_mem (longEmbed j₀ h).2))) ?_ ?_⟩
  · rw [coe_longEmbed_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc]
    exact (isLongParabolic_longEmbed u).mul hj₀ hyP
  · rw [coe_longEmbed_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc]
    exact (congrFun (congrFun (longBlock_mul hj₀ (isLongParabolic_longEmbed u) hyP) 1) 0).trans
      (by rw [longBlock_longEmbed, ← map_longBlockZ hyZ, ← Matrix.map_mul, map_apply,
        Matrix.mul_apply, Fin.sum_univ_two, hu, map_zero])

lemma exists_long_decomp (hj₀ : (j₀ : ℕ) + 1 = n) {b b' c₁ : GL (Fin n ⊕ Fin n) ℚ}
    (hb : b ∈ siegelBorel n) (hbZ : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) ∈
      (Int.castRingHom ℚ).mapMatrix.range) (hb' : b' ∈ siegelBorel n)
    (hc₁ : c₁ ∈ heckeGamma (Fin n)) (h : SL(2, ℤ))
    (he : b' = c₁ * b * ((longEmbed j₀ h : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ)⁻¹) :
    ∃ (u : SL(2, ℤ)) (c : GL (Fin n ⊕ Fin n) ℚ), c ∈ heckeGamma (Fin n) ∧ c ∈ siegelBorel n ∧
      ((longEmbed j₀ u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) * b *
        ((longEmbed j₀ h : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ)⁻¹ ∈ siegelBorel n ∧
      b' = c * (((longEmbed j₀ u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) * b *
        ((longEmbed j₀ h : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ)⁻¹) := by
  rcases exists_longEmbed_mul_mem hj₀ hb hbZ h with ⟨u, hy⟩
  have he' : b' = c₁ * ((longEmbed j₀ u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ)⁻¹ *
      (((longEmbed j₀ u : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ) * b *
        ((longEmbed j₀ h : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ)⁻¹) := by
    rw [he]
    group
  refine ⟨u, _, mul_mem hc₁ (inv_mem (longEmbed j₀ u).2), ?_, hy, he'⟩
  rw [eq_mul_inv_of_mul_eq he'.symm]
  exact mul_mem hb' (inv_mem hy)

lemma isUnit_longBlockZ (hj₀ : (j₀ : ℕ) + 1 = n) {c : GL (Fin n ⊕ Fin n) ℚ}
    (hc : c ∈ heckeGamma (Fin n)) (hcB : c ∈ siegelBorel n) :
    longBlockZ j₀ (c : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) *
      longBlockZ j₀ ((c⁻¹ : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) =
        1 := by
  have hc' : c⁻¹ ∈ heckeGamma (Fin n) := inv_mem hc
  refine Matrix.map_injective (RingHom.injective_int (Int.castRingHom ℚ)) ?_
  dsimp only
  rw [Matrix.map_mul, map_longBlockZ (mem_range_of_mem_heckeMonoidAt 1
    (heckeGamma_le_heckeMonoidAt 1 hc)), map_longBlockZ (mem_range_of_mem_heckeMonoidAt 1
      (heckeGamma_le_heckeMonoidAt 1 hc')), ← longBlock_mul hj₀
        (isLongParabolic_of_mem hcB) (isLongParabolic_of_mem (inv_mem hcB)), ← Units.val_mul,
    mul_inv_cancel, Units.val_one, longBlock_one, Matrix.map_one _ (map_zero _) (map_one _)]

lemma isUnit_longBlockZ' (hj₀ : (j₀ : ℕ) + 1 = n) {c : GL (Fin n ⊕ Fin n) ℚ}
    (hc : c ∈ heckeGamma (Fin n)) (hcB : c ∈ siegelBorel n) :
    longBlockZ j₀ ((c⁻¹ : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) *
      longBlockZ j₀ (c : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) = 1 := by
  simpa using isUnit_longBlockZ hj₀ (inv_mem hc) (inv_mem hcB)

lemma exists_longBlockZ_eq (hj₀ : (j₀ : ℕ) + 1 = n) {b b' c₁ : GL (Fin n ⊕ Fin n) ℚ}
    (hb : b ∈ siegelBorel n) (hbZ : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) ∈
      (Int.castRingHom ℚ).mapMatrix.range) (hb' : b' ∈ siegelBorel n)
    (hb'Z : (b' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) ∈ (Int.castRingHom ℚ).mapMatrix.range)
    (hc₁ : c₁ ∈ heckeGamma (Fin n)) (h : SL(2, ℤ))
    (he : b' = c₁ * b * ((longEmbed j₀ h : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ)⁻¹) :
    ∃ U : GL (Fin 2) ℤ, longBlockZ j₀ (b' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) =
      U * longBlockZ j₀ (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) *
        ((h⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
  rcases exists_long_decomp hj₀ hb hbZ hb' hc₁ h he with ⟨u, c, hc, hcB, hy, rfl⟩
  have hcZ : (c : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) ∈ (Int.castRingHom ℚ).mapMatrix.range :=
    mem_range_of_mem_heckeMonoidAt 1 (heckeGamma_le_heckeMonoidAt 1 hc)
  have hU : ((⟨_, _, isUnit_longBlockZ hj₀ hc hcB, isUnit_longBlockZ' hj₀ hc hcB⟩ * u.toGL :
      GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
        longBlockZ j₀ (c : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) * u := by
    rw [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix]
  refine ⟨⟨_, _, isUnit_longBlockZ hj₀ hc hcB, isUnit_longBlockZ' hj₀ hc hcB⟩ * u.toGL, ?_⟩
  rw [hU]
  refine Matrix.map_injective (RingHom.injective_int (Int.castRingHom ℚ)) ?_
  dsimp only
  rw [map_longBlockZ hb'Z, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, map_longBlockZ hcZ,
    map_longBlockZ hbZ, Units.val_mul,
    longBlock_mul hj₀ (isLongParabolic_of_mem hcB) (isLongParabolic_of_mem hy),
    coe_longEmbed_inv, Units.val_mul, Units.val_mul,
    longBlock_mul hj₀ ((isLongParabolic_longEmbed u).mul hj₀ (isLongParabolic_of_mem hb))
      (isLongParabolic_longEmbed _),
    longBlock_mul hj₀ (isLongParabolic_longEmbed u) (isLongParabolic_of_mem hb),
    longBlock_longEmbed, longBlock_longEmbed]
  simp only [Matrix.mul_assoc]

variable [Fact p.Prime]

lemma coe_weightCharacter_longBlockWeight (hj₀ : (j₀ : ℕ) + 1 = n) (e : ℕ) :
    (weightCharacter 1 (fun i : Fin n ↦ (primeUnit p)⁻¹ ^ (n - (i : ℕ))) (longBlockWeight j₀ e) :
      ℂ) = (p : ℂ) ^ (-(e : ℤ)) := by
  simp only [weightCharacter, longBlockWeight, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    (one_zpow : ∀ m : ℤ, (1 : ℂˣ) ^ m = 1), one_mul]
  rw [Fintype.prod_eq_single j₀ fun i hi ↦ by simp [hi]]
  simp only [Pi.single_eq_same, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, primeUnit,
    Units.val_mk0, Nat.sub_eq_of_eq_add' hj₀.symm, pow_one, zpow_natCast]
  rw [inv_pow, zpow_neg (p : ℂ), zpow_natCast]

lemma coe_satakeCharacterUniv_longBlockWeight (hj₀ : (j₀ : ℕ) + 1 = n) (e : ℕ) :
    (satakeCharacterUniv p (longBlockWeight j₀ e) : SatakeLaurent n) =
      single (longBlockWeight j₀ e) ((p : ℂ) ^ (-(e : ℤ))) := by
  rw [coe_satakeCharacterUniv, coe_weightCharacter_longBlockWeight p hj₀]

lemma single_longBlockWeight_eq (hj₀ : (j₀ : ℕ) + 1 = n) (e₁ e₂ : ℕ) :
    single (longBlockWeight j₀ e₁) ((p : ℂ) ^ (-(e₂ : ℤ))) =
      ((p : ℂ) ^ (e₁ : ℤ) * (p : ℂ) ^ (-(e₂ : ℤ))) •
        (satakeCharacterUniv p (longBlockWeight j₀ e₁) : SatakeLaurent n) := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [coe_satakeCharacterUniv_longBlockWeight p hj₀, MonoidAlgebra.smul_single, smul_eq_mul,
    mul_right_comm, ← zpow_add₀ hp, add_neg_cancel, zpow_zero, one_mul]

lemma longBlockZ_one_zero (b : siegelBorel n) :
    longBlockZ j₀ ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) 1 0 =
      0 := by
  have h0 : ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)
      (.inr j₀) (.inl j₀) = 0 :=
    congrFun (congrFun b.2.2.1 j₀) j₀
  simp [longBlockZ, longBlock, h0]

variable [NeZero n]

lemma exists_natAbs_num_apply_inr {b : siegelBorel n}
    (hb : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p) (j : Fin n) :
    ∃ a : ℕ, ((((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)
      (.inr j) (.inr j)).num.natAbs = p ^ a ∧ (((((b : GL (Fin n ⊕ Fin n) ℚ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) (.inr j) (.inr j)).num : ℚ) =
          ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)
            (.inr j) (.inr j))) := by
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
  have hdvd : (M (.inr j) (.inr j)).natAbs ∣ p ^ δ := by
    rw [← Int.natAbs_natCast (p ^ δ), Nat.cast_pow, ← hz]
    exact Int.natAbs_dvd_natAbs.mpr (dvd_mul_left _ _)
  rcases (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd with ⟨a, -, ha⟩
  refine ⟨a, ?_, ?_⟩ <;> rw [hM', Rat.num_intCast]
  exact ha

lemma exists_natAbs_det_longBlockZ {b : siegelBorel n}
    (hb : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p) : ∃ K : ℕ, (longBlockZ j₀
      ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)).det.natAbs =
        p ^ K := by
  rcases exists_natAbs_num_borelDiag hb j₀ with ⟨a, ha, -⟩
  rcases exists_natAbs_num_apply_inr p hb j₀ with ⟨a', ha', -⟩
  refine ⟨a + a', ?_⟩
  rw [det_fin_two, longBlockZ_one_zero, mul_zero, sub_zero, Int.natAbs_mul, pow_add]
  exact congrArg₂ (· * ·) ha ha'

lemma padicValRat_borelMultiplier_eq {b : siegelBorel n}
    (hb : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p) :
    padicValRat p (borelMultiplier b) = padicValNat p (borelDiag b j₀).num.natAbs +
      padicValNat p (((b : GL (Fin n ⊕ Fin n) ℚ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) (.inr j₀) (.inr j₀)).num.natAbs := by
  rcases exists_natAbs_num_borelDiag hb j₀ with ⟨a, ha, hA⟩
  rcases exists_natAbs_num_apply_inr p hb j₀ with ⟨a', ha', hD⟩
  have hA₀ : (borelDiag b j₀).num ≠ 0 :=
    fun h ↦ pow_ne_zero a (Fact.out : p.Prime).ne_zero (by rw [← ha, h, Int.natAbs_zero])
  have hD₀ : (((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)
      (.inr j₀) (.inr j₀)).num ≠ 0 :=
    fun h ↦ pow_ne_zero a' (Fact.out : p.Prime).ne_zero (by rw [← ha', h, Int.natAbs_zero])
  rw [← borelDiag_mul_apply_inr, ← hA, ← hD, ← Int.cast_mul, padicValRat.of_int,
    padicValInt.mul hA₀ hD₀]
  rfl

lemma padicValRat_borelDiag_eq_padicValNat {b : siegelBorel n}
    (hb : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p) (j : Fin n) :
    padicValRat p (((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)
      (.inl j) (.inl j)) = padicValNat p ((((b : GL (Fin n ⊕ Fin n) ℚ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) (.inl j) (.inl j)).num.natAbs) := by
  rcases exists_natAbs_num_borelDiag hb j with ⟨-, -, hj⟩
  have h :
      padicValRat p ((borelDiag b j).num : ℚ) = padicValNat p (borelDiag b j).num.natAbs := by
    rw [padicValRat.of_int]
    rfl
  rwa [hj] at h

lemma longOutWeight_satakeValuation_eq (hj₀ : (j₀ : ℕ) + 1 = n) {b b' c₁ : GL (Fin n ⊕ Fin n) ℚ}
    (hb : b ∈ siegelBorel n) (hbZ : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) ∈
      (Int.castRingHom ℚ).mapMatrix.range) (hb' : b' ∈ siegelBorel n)
    (hc₁ : c₁ ∈ heckeGamma (Fin n)) (h : SL(2, ℤ))
    (he : b' = c₁ * b * ((longEmbed j₀ h : heckeGamma (Fin n)) : GL (Fin n ⊕ Fin n) ℚ)⁻¹) :
    longOutWeight j₀ (satakeValuation p ⟨b', hb'⟩) =
      longOutWeight j₀ (satakeValuation p ⟨b, hb⟩) := by
  rcases exists_long_decomp hj₀ hb hbZ hb' hc₁ h he with ⟨u, c, hc, hcB, hy, rfl⟩
  have hsplit : (⟨_, hb'⟩ : siegelBorel n) = ⟨c, hcB⟩ * ⟨_, hy⟩ := rfl
  have hr : borelMultiplier ⟨_, hy⟩ = borelMultiplier ⟨b, hb⟩ :=
    borelMultiplier_eq_of_mul (longEmbed j₀ u).2 (inv_mem (longEmbed j₀ h).2) rfl
  have hd (j : Fin n) (hj : j ≠ j₀) : borelDiag ⟨_, hy⟩ j = borelDiag ⟨b, hb⟩ j := by
    simp only [borelDiag]
    rw [coe_longEmbed_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc,
      longEmbed_mul_apply u _ hj, mul_longEmbed_apply _ _ hj]
  rw [hsplit, map_mul, satakeValuation_eq_one p hc, one_mul]
  simp only [longOutWeight, satakeValuation, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, hr]
  congr 2
  funext j
  rcases eq_or_ne j j₀ with rfl | hj
  · simp
  · rw [Function.update_of_ne hj, Function.update_of_ne hj, hd j hj]

lemma satakeValuation_eq_longOutWeight_mul (hj₀ : (j₀ : ℕ) + 1 = n) {b : siegelBorel n}
    (hb : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p) :
    satakeValuation p b = longOutWeight j₀ (satakeValuation p b) * longBlockWeight j₀
      (hnfData p (longBlockZ j₀ ((b : GL (Fin n ⊕ Fin n) ℚ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ))).2.1 := by
  rcases exists_natAbs_det_longBlockZ p (j₀ := j₀) hb with ⟨K, hK⟩
  rw [hnfData_eq_upperData p (longBlockZ_one_zero b) (det_ne_zero_of_natAbs_eq p hK)]
  simp only [longOutWeight, longBlockWeight, satakeValuation, MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  refine Prod.ext (add_zero _).symm (funext fun j ↦ ?_)
  rcases eq_or_ne j j₀ with rfl | hj
  · simp [upperData, longBlockZ, longBlock, borelDiag,
      padicValRat_borelMultiplier_eq p (j₀ := j) hb, padicValRat_borelDiag_eq_padicValNat p hb j]
  · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]

lemma weylSign_satakeValuation (hj₀ : (j₀ : ℕ) + 1 = n) {b : siegelBorel n}
    (hb : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p) :
    weylSign j₀ (satakeValuation p b) = longOutWeight j₀ (satakeValuation p b) * longBlockWeight j₀
      (hnfData p (longBlockZ j₀ ((b : GL (Fin n ⊕ Fin n) ℚ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ))).1 := by
  rcases exists_natAbs_det_longBlockZ p (j₀ := j₀) hb with ⟨K, hK⟩
  rw [hnfData_eq_upperData p (longBlockZ_one_zero b) (det_ne_zero_of_natAbs_eq p hK)]
  simp only [weylSign, longOutWeight, longBlockWeight, satakeValuation, MulEquiv.coe_mk,
    Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  refine Prod.ext (add_zero _).symm (funext fun j ↦ ?_)
  rcases eq_or_ne j j₀ with rfl | hj
  · simp [upperData, longBlockZ, longBlock, padicValRat_borelDiag_eq_padicValNat p hb j, borelDiag]
  · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]

/-- **The universal Satake map is invariant under the sign change of the last coordinate**
(LMFDB `mf.siegel.lift`, through the Weyl invariance of the Satake map): for `j₀ = g - 1`, the
universal Satake map `Ω(ΓαΓ)` of every double coset of the local Hecke algebra of `Sp(2g, ℤ)` at
`p` is fixed by `x₀ ↦ x₀ x_{j₀}`, `x_{j₀} ↦ x_{j₀}⁻¹`. The embedded `SL(2, ℤ)` on
`(e_{j₀}, f_{j₀})` acts on the right cosets; the representatives in the Borel subgroup change by
right multiplication of their block at `(e_{j₀}, f_{j₀})` up to `GL(2, ℤ)` on the left, the
exponents `e₁` of `A_{j₀j₀}` and `e₂` of `D_{j₀j₀}` being exchanged by the sign change, and the
rank-one count `SiegelUpperHalfSpace.sum_mul_hnfData_eq` applies. -/
lemma domCongr_weylSign_last_satakeMapUniv (hj₀ : (j₀ : ℕ) + 1 = n) :
    domCongr ℂ ℂ (weylSign j₀) (satakeMapUniv p (single ℂ D 1)) =
      satakeMapUniv p (single ℂ D 1) := by
  have hmem (v : DecompQuotient (heckeGamma (Fin n)) (heckeGamma (Fin n))
      (D.out : GL (Fin n ⊕ Fin n) ℚ)⁻¹) : ((borelRep (rightCosetRep_mem_gspPlusGL p D v) :
        siegelBorel n) : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p :=
    borelRep_mem_heckeMonoidAt (rightCosetRep_mem_heckeMonoidAt p D v) _
  have hval (b : siegelBorel n) (hb : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p) :
      (satakeCharacterUniv p (satakeValuation p b) : SatakeLaurent n) =
        (satakeCharacterUniv p (longOutWeight j₀ (satakeValuation p b)) : SatakeLaurent n) *
          (satakeCharacterUniv p (longBlockWeight j₀
            (hnfData p (longBlockZ j₀ ((b : GL (Fin n ⊕ Fin n) ℚ) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ))).2.1) : SatakeLaurent n) := by
    rw [← Units.val_mul, ← map_mul, ← satakeValuation_eq_longOutWeight_mul p hj₀ hb]
  have hval' (b : siegelBorel n) (hb : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p) :
      domCongr ℂ ℂ (weylSign j₀) (satakeCharacterUniv p (satakeValuation p b) : SatakeLaurent n) =
        (satakeCharacterUniv p (longOutWeight j₀ (satakeValuation p b)) : SatakeLaurent n) *
          single (longBlockWeight j₀ (hnfData p (longBlockZ j₀ ((b : GL (Fin n ⊕ Fin n) ℚ) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ))).1)
              ((p : ℂ) ^ (-((hnfData p (longBlockZ j₀ ((b : GL (Fin n ⊕ Fin n) ℚ) :
                Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ))).2.1 : ℤ))) := by
    have hshift : (weightCharacter 1 (fun i : Fin n ↦ (primeUnit p)⁻¹ ^ (n - (i : ℕ)))
        (satakeValuation p b) : ℂ) = (weightCharacter 1 (fun i : Fin n ↦
          (primeUnit p)⁻¹ ^ (n - (i : ℕ))) (longOutWeight j₀ (satakeValuation p b)) : ℂ) *
            (p : ℂ) ^ (-((hnfData p (longBlockZ j₀ ((b : GL (Fin n ⊕ Fin n) ℚ) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ))).2.1 : ℤ)) := by
      rw [← coe_weightCharacter_longBlockWeight p hj₀, ← Units.val_mul, ← map_mul,
        ← satakeValuation_eq_longOutWeight_mul p hj₀ hb]
    rw [coe_satakeCharacterUniv (satakeValuation p b) p, domCongr_single,
      weylSign_satakeValuation p hj₀ hb, hshift, ← single_mul_single,
      ← coe_satakeCharacterUniv (longOutWeight j₀ (satakeValuation p b)) p]
  rw [satakeMapUniv_single_one, map_sum, Finset.sum_congr rfl fun v _ ↦ hval' _ (hmem v),
    Finset.sum_congr rfl fun v _ ↦ hval _ (hmem v)]
  refine sum_mul_hnfData_eq (hX := MulAction.compHom _ (longEmbed j₀)) p
    (fun v ↦ longBlockZ j₀ ((borelRep (rightCosetRep_mem_gspPlusGL p D v) :
      GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ))
    (fun v ↦ exists_natAbs_det_longBlockZ p (hmem v)) (fun h v ↦ ?_)
    (fun v ↦ (satakeCharacterUniv p (longOutWeight j₀ (satakeValuation p
      (borelRep (rightCosetRep_mem_gspPlusGL p D v)))) : SatakeLaurent n)) (fun h v ↦ ?_)
    (fun _ e₂ ↦ (satakeCharacterUniv p (longBlockWeight j₀ e₂) : SatakeLaurent n))
    (fun e₁ e₂ ↦ single (longBlockWeight j₀ e₁) ((p : ℂ) ^ (-(e₂ : ℤ))))
    fun e₁ e₂ ↦ single_longBlockWeight_eq p hj₀ e₁ e₂
  · rcases exists_borelRep_smul_eq p D (longEmbed j₀ h) v with ⟨c, hc, he⟩
    exact exists_longBlockZ_eq hj₀ (borelRep _).2 (mem_range_of_mem_heckeMonoidAt p (hmem v))
      (borelRep _).2 (mem_range_of_mem_heckeMonoidAt p (hmem _)) hc h he
  · rcases exists_borelRep_smul_eq p D (longEmbed j₀ h) v with ⟨c, hc, he⟩
    exact congrArg (fun μ ↦ (satakeCharacterUniv p μ : SatakeLaurent n))
      (longOutWeight_satakeValuation_eq p hj₀ (borelRep _).2
        (mem_range_of_mem_heckeMonoidAt p (hmem v)) (borelRep _).2 hc h he)

end Reduction

end SiegelUpperHalfSpace
