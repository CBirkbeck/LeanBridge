import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SatakeShortRoot

/-!
# Symplectic elementary divisors of `Sp(2g, ℤ)`

Let `p` be a prime and `S_p` the semigroup of the integral symplectic similitudes of `Sp(2g, ℤ)`
whose multiplier is a power of `p` (`SiegelUpperHalfSpace.heckeMonoidAt`). Every double coset of
`Γ = Sp(2g, ℤ)` in `S_p` is `Γ diag(p^{a_0}, …, p^{a_{g-1}}, p^{δ-a_0}, …, p^{δ-a_{g-1}}) Γ` with
`a_0 ≤ ⋯ ≤ a_{g-1}` and `2 a_{g-1} ≤ δ`, the coordinates being `(e_0, …, e_{g-1}, f_0, …, f_{g-1})`
(Andrianov, *Quadratic forms and Hecke operators*, §3.3;
`SiegelUpperHalfSpace.exists_eq_elementaryCoset`). So these double cosets span the local Hecke
algebra of `Sp(2g, ℤ)` at `p`, the basis on which the triangularity of the Satake map, and through
it Satake's theorem (LMFDB `mf.siegel.lift`), rests. In degree `2` this is
`SiegelUpperHalfSpace.exists_eq_heckeCosetDiag`.

The proof works with an integral matrix `M` with `Mᵀ J M = p^δ J` and splits off the coordinate
planes `(e_k, f_k)` one at a time, multiplying on both sides by the subgroup `Γ_k` of `Γ` acting by
the identity on the planes `< k` (`SiegelUpperHalfSpace.lowFix`). Through the symplectic adjoint
`M♯ = -J Mᵀ J`, with `M♯ M = M M♯ = p^δ`, a column `c e_i` of `M` forces the row `(p^δ / c) f_iᵀ`
and a row `c e_iᵀ` the column `(p^δ / c) f_i`. At step `k`, an entry of least `p`-adic valuation
`a_k` of the block of `M` on the planes `≥ k` lies in a column `p^{a_k} w` with `w` primitive, its
common divisors dividing `p^{δ - a_k}` through `M♯ M = p^δ`. The group `Γ_k` acts transitively on
the primitive vectors of these planes (`SiegelUpperHalfSpace.exists_mem_lowFix_mulVec_eq_single`:
the `SL(2, ℤ)` on each plane `(e_c, f_c)` clears the coordinates `f_c`, and those on the pairs
`(e_k, e_c)` merge the coordinates `e_c` into `e_k`), which makes the column `e_k` equal to
`p^{a_k} e_k`. A Levi element `(U, 0; 0, U⁻ᵀ)` and a translation `(1, S; 0, 1)` fixing `e_k` clear
the row `e_k`, the divisions by `p^{a_k}` being exact, and the symplectic relations give the column
`p^{δ - a_k} f_k`. The divisibility of the remaining block by `p^{a_k}` gives `a_k ≤ a_{k+1}` and
`2 a_k ≤ δ`.

## Main definitions

* `SiegelUpperHalfSpace.sympAdj`: the symplectic adjoint `M♯ = -J Mᵀ J`.
* `SiegelUpperHalfSpace.plane`: the index of the coordinate plane of a coordinate.
* `SiegelUpperHalfSpace.lowFix`: the subgroup `Γ_k` of `Sp(2g, ℤ)`.
* `SiegelUpperHalfSpace.planeMat`: `SL(2, ℤ)` acting on every coordinate plane.
* `SiegelUpperHalfSpace.IsSplit`: the coordinate planes `< k` are split off.
* `SiegelUpperHalfSpace.elementaryEntries`, `SiegelUpperHalfSpace.elementaryDiag`,
  `SiegelUpperHalfSpace.elementaryCoset`: the entries, the diagonal matrix and the double coset of
  symplectic elementary divisors.

## Main results

* `SiegelUpperHalfSpace.exists_mem_lowFix_mulVec_eq_single`: `Γ_k` acts transitively on the
  primitive vectors of the coordinates of the planes `≥ k`.
* `SiegelUpperHalfSpace.exists_eq_elementaryCoset`: the symplectic elementary divisor theorem.
-/

open Matrix

open scoped MatrixGroups

namespace SiegelUpperHalfSpace

variable {n : ℕ}

/-! ### The symplectic adjoint -/

section Adjoint

variable {R : Type*} [CommRing R] (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)

/-- The **symplectic adjoint** `M♯ = -J Mᵀ J` of a matrix of size `2g` (LMFDB `mf.siegel.lift`,
through the symplectic elementary divisors): `M♯ M = r` for a symplectic similitude `M` of
multiplier `r`, and `M♯ = M⁻¹` on `Sp(2g)`. -/
def sympAdj : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  -J (Fin n) R * Mᵀ * J (Fin n) R

variable (i j : Fin n)

lemma sympAdj_inl_inl : sympAdj M (.inl i) (.inl j) = M (.inr j) (.inr i) := by
  simp [sympAdj, J, Matrix.mul_apply, one_apply]

lemma sympAdj_inl_inr : sympAdj M (.inl i) (.inr j) = -M (.inl j) (.inr i) := by
  simp [sympAdj, J, Matrix.mul_apply, one_apply]

lemma sympAdj_inr_inl : sympAdj M (.inr i) (.inl j) = -M (.inr j) (.inl i) := by
  simp [sympAdj, J, Matrix.mul_apply, one_apply]

lemma sympAdj_inr_inr : sympAdj M (.inr i) (.inr j) = M (.inl j) (.inl i) := by
  simp [sympAdj, J, Matrix.mul_apply, one_apply]

variable {M} {r : R}

lemma sympAdj_mul (hM : Mᵀ * J (Fin n) R * M = r • J (Fin n) R) : sympAdj M * M = r • 1 := by
  rw [sympAdj, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᵀ, hM, Matrix.mul_smul,
    neg_mul, J_squared, neg_neg]

end Adjoint

section Integral

variable {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ} {r c : ℤ} {i : Fin n}

lemma mul_sympAdj (hr : r ≠ 0) (hM : Mᵀ * J (Fin n) ℤ * M = r • J (Fin n) ℤ) :
    M * sympAdj M = r • 1 := by
  have h : sympAdj M * M = r • 1 := sympAdj_mul hM
  have hdet : M.det ≠ 0 := fun h0 ↦ by
    have h' : (sympAdj M * M).det = (r • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)).det :=
      congrArg det h
    rw [det_mul, h0, mul_zero, det_smul, det_one, mul_one] at h'
    exact pow_ne_zero _ hr h'.symm
  have e : (M * sympAdj M - r • 1) * (M * adjugate M) = 0 := by
    rw [sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (sympAdj M), h, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, sub_self]
  rw [mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at e
  exact sub_eq_zero.mp ((smul_eq_zero.mp e).resolve_left hdet)

lemma mul_apply_inr_of_col_inl (hM : sympAdj M * M = r • 1)
    (hc : ∀ m, M m (.inl i) = (Pi.single (.inl i) c : Fin n ⊕ Fin n → ℤ) m) (v : Fin n ⊕ Fin n) :
    c * M (.inr i) v = if v = .inr i then r else 0 := by
  have h (u : Fin n ⊕ Fin n) : sympAdj M u (.inl i) * c = if u = .inl i then r else 0 := by
    have e : (sympAdj M * M) u (.inl i) = (r • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)) u
        (.inl i) := by
      rw [hM]
    simpa [Matrix.mul_apply, hc, Pi.single_apply, one_apply] using e
  rcases v with l | l
  · have e : sympAdj M (.inr l) (.inl i) * c = if (.inr l : Fin n ⊕ Fin n) = .inl i then r else 0 :=
      h (.inr l)
    rw [sympAdj_inr_inl] at e
    simp only [reduceCtorEq, ite_false] at e ⊢
    linear_combination -e
  · have e : sympAdj M (.inl l) (.inl i) * c = if (.inl l : Fin n ⊕ Fin n) = .inl i then r else 0 :=
      h (.inl l)
    rw [sympAdj_inl_inl] at e
    simp only [Sum.inl.injEq, Sum.inr.injEq] at e ⊢
    linear_combination e

lemma mul_apply_inl_of_col_inr (hM : sympAdj M * M = r • 1)
    (hc : ∀ m, M m (.inr i) = (Pi.single (.inr i) c : Fin n ⊕ Fin n → ℤ) m) (v : Fin n ⊕ Fin n) :
    c * M (.inl i) v = if v = .inl i then r else 0 := by
  have h (u : Fin n ⊕ Fin n) : sympAdj M u (.inr i) * c = if u = .inr i then r else 0 := by
    have e : (sympAdj M * M) u (.inr i) = (r • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)) u
        (.inr i) := by
      rw [hM]
    simpa [Matrix.mul_apply, hc, Pi.single_apply, one_apply] using e
  rcases v with l | l
  · have e : sympAdj M (.inr l) (.inr i) * c = if (.inr l : Fin n ⊕ Fin n) = .inr i then r else 0 :=
      h (.inr l)
    rw [sympAdj_inr_inr] at e
    simp only [Sum.inl.injEq, Sum.inr.injEq] at e ⊢
    linear_combination e
  · have e : sympAdj M (.inl l) (.inr i) * c = if (.inl l : Fin n ⊕ Fin n) = .inr i then r else 0 :=
      h (.inl l)
    rw [sympAdj_inl_inr] at e
    simp only [reduceCtorEq, ite_false] at e ⊢
    linear_combination -e

lemma mul_apply_inr_of_row_inl (hM : M * sympAdj M = r • 1)
    (hc : ∀ v, M (.inl i) v = (Pi.single (.inl i) c : Fin n ⊕ Fin n → ℤ) v) (m : Fin n ⊕ Fin n) :
    c * M m (.inr i) = if m = .inr i then r else 0 := by
  have e : (M * sympAdj M) m (.inr i) = (r • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)) m
      (.inr i) := by
    rw [hM]
  rw [Matrix.mul_apply, Fintype.sum_sum_type] at e
  simp only [sympAdj_inl_inr, sympAdj_inr_inr, hc, Pi.single_apply] at e
  simpa [one_apply, mul_comm] using e

end Integral

/-! ### The subgroups `Γ_k` -/

/-- The **index `i` of the coordinate plane `(e_i, f_i)`** of a coordinate `e_i` or `f_i` of
`ℤ^{2g}` (LMFDB `mf.siegel.lift`, through the symplectic elementary divisors). -/
def plane : Fin n ⊕ Fin n → ℕ :=
  Sum.elim (fun i ↦ (i : ℕ)) fun i ↦ (i : ℕ)

@[simp]
lemma plane_inl (i : Fin n) : plane (.inl i) = i :=
  rfl

@[simp]
lemma plane_inr (i : Fin n) : plane (.inr i) = i :=
  rfl

variable (n) in
/-- The subgroup **`Γ_k` of the `γ ∈ Sp(2g, ℤ)` acting by the identity on the coordinates `e_i`,
`f_i`, `i < k`** (LMFDB `mf.siegel.lift`, through the symplectic elementary divisors): the entries
of `γ` in the rows and the columns of these coordinates are those of the identity, so that `γ` also
preserves the span of the other coordinates. -/
def lowFix (k : ℕ) : Subgroup (symplecticGroup (Fin n) ℤ) where
  carrier := {g | ∀ m v, plane m < k ∨ plane v < k →
    (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) m v =
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) m v}
  mul_mem' {g h} hg hh m v hmv := by
    rw [Submonoid.coe_mul, Matrix.mul_apply]
    rcases hmv with hm | hv
    · simp only [hg m _ (.inl hm), one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ]
      exact hh m v (.inl hm)
    · simp only [hh _ v (.inr hv), one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ]
      exact hg m v (.inr hv)
  one_mem' _ _ _ := rfl
  inv_mem' {g} hg m v hmv := by
    rw [SymplecticGroup.coe_inv]
    rcases m with i | i <;> rcases v with j | j <;> simp only [plane_inl, plane_inr] at hmv
    · rw [← sympAdj, sympAdj_inl_inl, hg _ _ (by simpa using hmv.symm)]
      simp [one_apply, eq_comm]
    · rw [← sympAdj, sympAdj_inl_inr, hg _ _ (by simpa using hmv.symm)]
      simp
    · rw [← sympAdj, sympAdj_inr_inl, hg _ _ (by simpa using hmv.symm)]
      simp
    · rw [← sympAdj, sympAdj_inr_inr, hg _ _ (by simpa using hmv.symm)]
      simp [one_apply, eq_comm]

variable {p δ k : ℕ} {a : Fin n → ℕ} {g g' : symplecticGroup (Fin n) ℤ}
  {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ}

lemma apply_of_mem_lowFix (hg : g ∈ lowFix n k) {m v : Fin n ⊕ Fin n}
    (h : plane m < k ∨ plane v < k) : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) m v =
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) m v :=
  hg m v h

lemma le_plane_of_apply_ne_zero_right (hg : g ∈ lowFix n k) {i : ℕ} (hik : i ≤ k)
    {m l : Fin n ⊕ Fin n} (hm : i ≤ plane m)
    (h : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) m l ≠ 0) : i ≤ plane l := by
  by_contra hl
  rw [apply_of_mem_lowFix hg (.inr (lt_of_lt_of_le (not_le.mp hl) hik)), one_apply] at h
  split_ifs at h with hml
  · exact hl (hml ▸ hm)
  · exact h rfl

lemma le_plane_of_apply_ne_zero_left (hg : g ∈ lowFix n k) {i : ℕ} (hik : i ≤ k)
    {l v : Fin n ⊕ Fin n} (hv : i ≤ plane v)
    (h : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) l v ≠ 0) : i ≤ plane l := by
  by_contra hl
  rw [apply_of_mem_lowFix hg (.inl (lt_of_lt_of_le (not_le.mp hl) hik)), one_apply] at h
  split_ifs at h with hlv
  · exact hl (hlv ▸ hv)
  · exact h rfl

lemma dvd_mul_mul_apply (hg : g ∈ lowFix n k) (hg' : g' ∈ lowFix n k) {i : ℕ} (hik : i ≤ k) {d : ℤ}
    (hd : ∀ m v, i ≤ plane m → i ≤ plane v → d ∣ N m v) {m v : Fin n ⊕ Fin n} (hm : i ≤ plane m)
    (hv : i ≤ plane v) : d ∣ ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) * N * g') m v := by
  rw [Matrix.mul_apply]
  refine Finset.dvd_sum fun l' _ ↦ ?_
  by_cases hl' : (g' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) l' v = 0
  · rw [hl', mul_zero]
    exact dvd_zero d
  refine Dvd.dvd.mul_right ?_ _
  rw [Matrix.mul_apply]
  refine Finset.dvd_sum fun l _ ↦ ?_
  by_cases hl : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) m l = 0
  · rw [hl, zero_mul]
    exact dvd_zero d
  exact Dvd.dvd.mul_left (hd l l' (le_plane_of_apply_ne_zero_right hg hik hm hl)
    (le_plane_of_apply_ne_zero_left hg' hik hv hl')) _

lemma mul_mul_apply_of_col (hg : g ∈ lowFix n k) (hg' : g' ∈ lowFix n k) {u : Fin n ⊕ Fin n}
    (hu : plane u < k) {c : ℤ} (hc : ∀ m, N m u = (Pi.single u c : Fin n ⊕ Fin n → ℤ) m)
    (m : Fin n ⊕ Fin n) :
    ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) * N * g') m u =
      (Pi.single u c : Fin n ⊕ Fin n → ℤ) m := by
  rw [Matrix.mul_apply, Finset.sum_eq_single u, apply_of_mem_lowFix hg' (.inr hu), one_apply_eq,
    mul_one, Matrix.mul_apply, Finset.sum_eq_single u, hc, Pi.single_eq_same,
    apply_of_mem_lowFix hg (.inr hu), one_apply, Pi.single_apply]
  · split_ifs <;> simp
  · intro l _ hl
    rw [hc, Pi.single_eq_of_ne hl, mul_zero]
  · simp
  · intro l _ hl
    rw [apply_of_mem_lowFix hg' (.inr hu), one_apply_ne hl, mul_zero]
  · simp

lemma mem_lowFix_of_fromBlocks {A B C D : Matrix (Fin n) (Fin n) ℤ}
    (hg : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) = fromBlocks A B C D)
    (hA : ∀ i j : Fin n, (i : ℕ) < k ∨ (j : ℕ) < k → A i j = (1 : Matrix (Fin n) (Fin n) ℤ) i j)
    (hB : ∀ i j : Fin n, (i : ℕ) < k ∨ (j : ℕ) < k → B i j = 0)
    (hC : ∀ i j : Fin n, (i : ℕ) < k ∨ (j : ℕ) < k → C i j = 0)
    (hD : ∀ i j : Fin n, (i : ℕ) < k ∨ (j : ℕ) < k → D i j = (1 : Matrix (Fin n) (Fin n) ℤ) i j) :
    g ∈ lowFix n k := by
  rintro (i | i) (j | j) hij <;> rw [hg] <;> simp only [plane_inl, plane_inr] at hij
  · simpa [one_apply] using hA i j hij
  · simpa using hB i j hij
  · simpa using hC i j hij
  · simpa [one_apply] using hD i j hij

lemma transpose_mul_J_mul_eq_of_mem {γ γ' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ}
    (hγ : γ ∈ symplecticGroup (Fin n) ℤ) (hγ' : γ' ∈ symplecticGroup (Fin n) ℤ) {r : ℤ}
    (hN : Nᵀ * J (Fin n) ℤ * N = r • J (Fin n) ℤ) :
    (γ * N * γ')ᵀ * J (Fin n) ℤ * (γ * N * γ') = r • J (Fin n) ℤ := by
  have e : (γ * N * γ')ᵀ * J (Fin n) ℤ * (γ * N * γ') =
      γ'ᵀ * (Nᵀ * (γᵀ * J (Fin n) ℤ * γ) * N) * γ' := by
    simp only [transpose_mul, Matrix.mul_assoc]
  rw [e, SymplecticGroup.mem_iff'.mp hγ, hN, Matrix.mul_smul, Matrix.smul_mul,
    SymplecticGroup.mem_iff'.mp hγ']

/-! ### `Γ_k` acts transitively on the primitive vectors of the coordinates `≥ k` -/

/-- The integral symplectic matrix **acting by `V c ∈ SL(2, ℤ)` on every coordinate plane
`(e_c, f_c)`** (LMFDB `mf.siegel.lift`, through the symplectic elementary divisors). -/
def planeMat (V : Fin n → SL(2, ℤ)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ :=
  fromBlocks (diagonal fun c ↦ V c 0 0) (diagonal fun c ↦ V c 0 1) (diagonal fun c ↦ V c 1 0)
    (diagonal fun c ↦ V c 1 1)

variable (V : Fin n → SL(2, ℤ))

lemma planeMat_mem : planeMat V ∈ symplecticGroup (Fin n) ℤ := by
  refine SymplecticGroup.fromBlocks_mem_iff.mpr ⟨?_, ?_, ?_⟩
  on_goal 3 =>
    rw [diagonal_transpose, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal,
      diagonal_sub, ← diagonal_one]
    exact congrArg diagonal <| funext fun c ↦ by
      have h : (V c : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := (V c).2
      rw [det_fin_two] at h
      linear_combination h
  all_goals simp only [diagonal_transpose, diagonal_mul_diagonal, mul_comm]

lemma planeMat_mulVec_inl (w : Fin n ⊕ Fin n → ℤ) (c : Fin n) :
    (planeMat V *ᵥ w) (.inl c) = V c 0 0 * w (.inl c) + V c 0 1 * w (.inr c) := by
  simp [planeMat, fromBlocks_mulVec, mulVec_diagonal]

lemma planeMat_mulVec_inr (w : Fin n ⊕ Fin n → ℤ) (c : Fin n) :
    (planeMat V *ᵥ w) (.inr c) = V c 1 0 * w (.inl c) + V c 1 1 * w (.inr c) := by
  simp [planeMat, fromBlocks_mulVec, mulVec_diagonal]

variable {V} in
lemma planeMat_mem_lowFix (hV : ∀ c : Fin n, (c : ℕ) < k → V c = 1) :
    (⟨planeMat V, planeMat_mem V⟩ : symplecticGroup (Fin n) ℤ) ∈ lowFix n k := by
  refine mem_lowFix_of_fromBlocks rfl ?_ ?_ ?_ ?_ <;> intro i j hij <;>
    rcases eq_or_ne i j with rfl | hne
  · simp [hV i (hij.elim id id)]
  · simp [hne]
  · simp [hV i (hij.elim id id)]
  · simp [hne]
  · simp [hV i (hij.elim id id)]
  · simp [hne]
  · simp [hV i (hij.elim id id)]
  · simp [hne]

lemma shortEmbedSp_mem_lowFix {c₁ c₂ : Fin n} (h : c₁ ≠ c₂) (hc₁ : k ≤ c₁) (hc₂ : k ≤ c₂)
    (u : SL(2, ℤ)) : shortEmbedSp h u ∈ lowFix n k := by
  refine mem_lowFix_of_fromBlocks rfl (fun i j hij ↦ ?_) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
    fun i j hij ↦ ?_
  · rcases hij with hi | hj
    · rw [pairBlock_apply_of_ne_left h _ (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by omega)), one_apply]
    · rw [pairBlock_apply_of_ne_right h _ (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by omega)), one_apply]
  · rw [transpose_apply]
    rcases hij with hi | hj
    · rw [pairBlock_apply_of_ne_right h _ (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by omega))]
      simp [one_apply, eq_comm]
    · rw [pairBlock_apply_of_ne_left h _ (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by omega))]
      simp [one_apply, eq_comm]

lemma exists_mem_lowFix_mulVec_eq_of_inr (hk : k < n) (t : ℕ) (w : Fin n ⊕ Fin n → ℤ)
    (hw : ∀ c, w (.inr c) = 0) (hw' : ∀ c : Fin n, (c : ℕ) < k ∨ t ≤ c → w (.inl c) = 0) :
    ∃ g ∈ lowFix n k, ∃ c : ℤ,
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) *ᵥ w = Pi.single (.inl ⟨k, hk⟩) c := by
  induction t generalizing w with
  | zero =>
    refine ⟨1, one_mem _, 0, funext fun m ↦ ?_⟩
    rcases m with c | c
    · simp [hw' c (.inr (Nat.zero_le _))]
    · simp [hw c]
  | succ t ih =>
    rcases lt_or_ge k t with hkt | htk
    · rcases lt_or_ge t n with htn | htn
      · have hne : (⟨k, hk⟩ : Fin n) ≠ ⟨t, htn⟩ := Fin.ne_of_val_ne hkt.ne
        rcases SymplecticGroup.exists_SL2Z_eq_gcd (w (.inl ⟨k, hk⟩)) (w (.inl ⟨t, htn⟩)) with
          ⟨U, -, hU⟩
        have e₀ (c : Fin n) : ((shortEmbedSp hne U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) *ᵥ
            w) (.inl c) = ∑ l, pairBlock hne (U : Matrix (Fin 2) (Fin 2) ℤ) c l * w (.inl l) := by
          simp [shortEmbedSp, mulVec, dotProduct]
        have e₁ (c : Fin n) : ((shortEmbedSp hne U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) *ᵥ
            w) (.inr c) = 0 := by
          simp [shortEmbedSp, mulVec, dotProduct, hw]
        have e₂ (c : Fin n) (hc₁ : c ≠ ⟨k, hk⟩) (hc₂ : c ≠ ⟨t, htn⟩) :
            ((shortEmbedSp hne U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) *ᵥ w) (.inl c) =
              w (.inl c) := by
          rw [e₀]
          simp [pairBlock_apply_of_ne_left hne _ hc₁ hc₂]
        have e₃ : ((shortEmbedSp hne U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) *ᵥ w)
            (.inl ⟨t, htn⟩) = 0 := by
          rw [e₀, Fintype.sum_eq_add _ _ hne fun l hl ↦ by
            rw [pairBlock_apply_of_ne_right hne _ hl.1 hl.2, ite_eq_right (Ne.symm hl.2),
              zero_mul]]
          have h₁₀ : pairBlock hne (U : Matrix (Fin 2) (Fin 2) ℤ) ⟨t, htn⟩ ⟨k, hk⟩ = U 1 0 :=
            pairBlock_apply_twoEquiv hne _ 1 0
          have h₁₁ : pairBlock hne (U : Matrix (Fin 2) (Fin 2) ℤ) ⟨t, htn⟩ ⟨t, htn⟩ = U 1 1 :=
            pairBlock_apply_twoEquiv hne _ 1 1
          rw [h₁₀, h₁₁, hU]
        have e₄ (c : Fin n) (hc : (c : ℕ) < k ∨ t ≤ c) :
            ((shortEmbedSp hne U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) *ᵥ w) (.inl c) =
              0 := by
          by_cases hct : c = ⟨t, htn⟩
          · rw [hct, e₃]
          · have hck : c ≠ ⟨k, hk⟩ := by
              rintro rfl
              simp only at hc
              omega
            have hct' : (c : ℕ) ≠ t := fun h ↦ hct (Fin.ext h)
            rw [e₂ c hck hct]
            exact hw' c (by omega)
        rcases ih _ e₁ e₄ with ⟨g, hg, c₀, hc₀⟩
        exact ⟨g * shortEmbedSp hne U, mul_mem hg (shortEmbedSp_mem_lowFix hne le_rfl hkt.le U),
          c₀, by rw [Submonoid.coe_mul, ← mulVec_mulVec, hc₀]⟩
      · exact ih w hw fun c hc ↦ hw' c (.inl (hc.resolve_right (not_le.mpr (c.2.trans_le htn))))
    · refine ⟨1, one_mem _, w (.inl ⟨k, hk⟩), funext fun m ↦ ?_⟩
      rcases m with c | c
      · by_cases hc : c = ⟨k, hk⟩
        · subst hc
          simp
        · have hck : (c : ℕ) ≠ k := fun h ↦ hc (Fin.ext h)
          rw [Submonoid.coe_one, one_mulVec, hw' c (by omega),
            Pi.single_eq_of_ne (by simpa using hc)]
      · simp [hw c]

/-- **`Γ_k` acts transitively on the primitive vectors of the coordinates of the planes `≥ k`**:
such a vector is `γ⁻¹ e_k` for some `γ ∈ Γ_k`. -/
lemma exists_mem_lowFix_mulVec_eq_single (hk : k < n) {w : Fin n ⊕ Fin n → ℤ}
    (hw : ∀ m, plane m < k → w m = 0) (hp : ∀ d : ℤ, (∀ m, d ∣ w m) → IsUnit d) :
    ∃ g ∈ lowFix n k,
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) *ᵥ w = Pi.single (.inl ⟨k, hk⟩) 1 := by
  choose M hM using fun c : Fin n ↦ SymplecticGroup.exists_SL2Z_eq_gcd (w (.inl c)) (w (.inr c))
  let S : Fin n → SL(2, ℤ) := fun c ↦ if (c : ℕ) < k then 1 else M c
  have hS (c : Fin n) (hc : (c : ℕ) < k) : S c = 1 := ite_eq_left hc
  have h₁ (c : Fin n) : (planeMat S *ᵥ w) (.inr c) = 0 := by
    rw [planeMat_mulVec_inr]
    by_cases hc : (c : ℕ) < k
    · rw [hS c hc, hw (.inl c) hc, hw (.inr c) hc]
      simp
    · have hSc : S c = M c := ite_eq_right hc
      rw [hSc]
      exact (hM c).2
  have h₂ (c : Fin n) (hc : (c : ℕ) < k) : (planeMat S *ᵥ w) (.inl c) = 0 := by
    rw [planeMat_mulVec_inl, hw (.inl c) hc, hw (.inr c) hc]
    simp
  rcases exists_mem_lowFix_mulVec_eq_of_inr hk n _ h₁
    fun c hc ↦ h₂ c (hc.resolve_right (not_le.mpr c.2)) with ⟨g, hg, c₀, hc₀⟩
  have hdvd (m : Fin n ⊕ Fin n) : c₀ ∣ w m := by
    have e : w = (((g * ⟨planeMat S, planeMat_mem S⟩)⁻¹ : symplecticGroup (Fin n) ℤ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) *ᵥ Pi.single (.inl ⟨k, hk⟩) c₀ := by
      rw [← hc₀, mulVec_mulVec, mulVec_mulVec, ← Submonoid.coe_mul,
        ← Submonoid.coe_mul (symplecticGroup (Fin n) ℤ) _ ⟨planeMat S, planeMat_mem S⟩, mul_assoc,
        inv_mul_cancel, Submonoid.coe_one, one_mulVec]
    rw [e]
    simp [mulVec]
  rcases Int.isUnit_iff.mp (hp c₀ hdvd) with rfl | rfl
  · exact ⟨g * ⟨planeMat S, planeMat_mem S⟩, mul_mem hg (planeMat_mem_lowFix hS), by
      rw [Submonoid.coe_mul, ← mulVec_mulVec, hc₀]⟩
  · let S' : Fin n → SL(2, ℤ) := Function.update 1 ⟨k, hk⟩ (-1)
    have hS' (c : Fin n) (hc : (c : ℕ) < k) : S' c = 1 :=
      Function.update_of_ne (Fin.ne_of_val_ne hc.ne) _ _
    refine ⟨⟨planeMat S', planeMat_mem S'⟩ * (g * ⟨planeMat S, planeMat_mem S⟩),
      mul_mem (planeMat_mem_lowFix hS') (mul_mem hg (planeMat_mem_lowFix hS)), ?_⟩
    rw [Submonoid.coe_mul, ← mulVec_mulVec, Submonoid.coe_mul, ← mulVec_mulVec, hc₀]
    funext m
    rcases m with c | c
    · rw [planeMat_mulVec_inl]
      by_cases hc : c = ⟨k, hk⟩
      · subst hc
        simp [S']
      · simp [S', hc]
    · rw [planeMat_mulVec_inr]
      by_cases hc : c = ⟨k, hk⟩
      · subst hc
        simp [S']
      · simp [S', hc]

/-! ### Splitting off the coordinate planes one at a time -/

variable (p δ k a) in
/-- The integral matrix `M` is **split below `k`** with the exponents `a` (LMFDB
`mf.siegel.lift`, through the symplectic elementary divisors): for `i < k` its columns at `e_i`
and `f_i` are `p^{a_i} e_i` and `p^{δ - a_i} f_i`, and `p^{a_i}` divides its entries in the rows
and the columns of the coordinates of the planes `≥ i`. -/
structure IsSplit (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) : Prop where
  col_inl (i : Fin n) (hi : (i : ℕ) < k) (m : Fin n ⊕ Fin n) :
    M m (.inl i) = (Pi.single (.inl i) ((p : ℤ) ^ a i) : Fin n ⊕ Fin n → ℤ) m
  col_inr (i : Fin n) (hi : (i : ℕ) < k) (m : Fin n ⊕ Fin n) :
    M m (.inr i) = (Pi.single (.inr i) ((p : ℤ) ^ (δ - a i)) : Fin n ⊕ Fin n → ℤ) m
  dvd (i : Fin n) (hi : (i : ℕ) < k) (m v : Fin n ⊕ Fin n) (hm : (i : ℕ) ≤ plane m)
    (hv : (i : ℕ) ≤ plane v) : (p : ℤ) ^ a i ∣ M m v

lemma isSplit_zero : IsSplit p δ 0 a N where
  col_inl _ hi := absurd hi (Nat.not_lt_zero _)
  col_inr _ hi := absurd hi (Nat.not_lt_zero _)
  dvd _ hi := absurd hi (Nat.not_lt_zero _)

lemma IsSplit.mul_mul (hs : IsSplit p δ k a N) (hg : g ∈ lowFix n k) (hg' : g' ∈ lowFix n k) :
    IsSplit p δ k a ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) * N * g') where
  col_inl i hi := mul_mul_apply_of_col hg hg' (u := .inl i) hi (hs.col_inl i hi)
  col_inr i hi := mul_mul_apply_of_col hg hg' (u := .inr i) hi (hs.col_inr i hi)
  dvd i hi _ _ hm hv := dvd_mul_mul_apply hg hg' hi.le (hs.dvd i hi) hm hv

variable (p) [Fact p.Prime] in
lemma cast_prime_pow_ne_zero (e : ℕ) : (p : ℤ) ^ e ≠ 0 :=
  pow_ne_zero _ (Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

variable [Fact p.Prime] in
lemma le_of_pow_dvd_pow {e e' : ℕ} (h : (p : ℤ) ^ e ∣ (p : ℤ) ^ e') : e ≤ e' :=
  (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp (by exact_mod_cast h)

variable [Fact p.Prime] in
lemma IsSplit.apply_eq_zero (hs : IsSplit p δ k a N) (hN : sympAdj N * N = ((p : ℤ) ^ δ) • 1)
    {m v : Fin n ⊕ Fin n} (hm : plane m < k) (hmv : m ≠ v) : N m v = 0 := by
  rcases m with i | i
  · have h : (p : ℤ) ^ (δ - a i) * N (.inl i) v = if v = .inl i then (p : ℤ) ^ δ else 0 :=
      mul_apply_inl_of_col_inr hN (hs.col_inr i hm) v
    rw [ite_eq_right (Ne.symm hmv)] at h
    exact (mul_eq_zero.mp h).resolve_left (cast_prime_pow_ne_zero p _)
  · have h : (p : ℤ) ^ a i * N (.inr i) v = if v = .inr i then (p : ℤ) ^ δ else 0 :=
      mul_apply_inr_of_col_inl hN (hs.col_inl i hm) v
    rw [ite_eq_right (Ne.symm hmv)] at h
    exact (mul_eq_zero.mp h).resolve_left (cast_prime_pow_ne_zero p _)

variable [Fact p.Prime] in
lemma IsSplit.exists_min (hs : IsSplit p δ k a N) (hN : sympAdj N * N = ((p : ℤ) ^ δ) • 1)
    (hk : k < n) : ∃ m₀ v₀ : Fin n ⊕ Fin n, ∃ e : ℕ, k ≤ plane m₀ ∧ k ≤ plane v₀ ∧
      ¬(p : ℤ) ^ (e + 1) ∣ N m₀ v₀ ∧ ∀ m v, k ≤ plane m → k ≤ plane v → (p : ℤ) ^ e ∣ N m v := by
  have hS : (Finset.univ.filter fun mv : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) ↦
      k ≤ plane mv.1 ∧ k ≤ plane mv.2 ∧ N mv.1 mv.2 ≠ 0).Nonempty := by
    have e : ∑ m, sympAdj N (.inl ⟨k, hk⟩) m * N m (.inl ⟨k, hk⟩) = (p : ℤ) ^ δ := by
      rw [← Matrix.mul_apply, hN, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
    rcases Finset.exists_ne_zero_of_sum_ne_zero (e.trans_ne (cast_prime_pow_ne_zero p δ)) with
      ⟨m, -, hm⟩
    refine ⟨(m, .inl ⟨k, hk⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, le_rfl,
      right_ne_zero_of_mul hm⟩⟩
    by_contra h
    exact right_ne_zero_of_mul hm (hs.apply_eq_zero hN (not_le.mp h) fun h' ↦ h (by
      rw [h']
      exact le_rfl))
  rcases Finset.exists_min_image _ (fun mv ↦ padicValInt p (N mv.1 mv.2)) hS with
    ⟨⟨m₀, v₀⟩, h₀, hmin⟩
  rcases Finset.mem_filter.mp h₀ with ⟨-, hm₀, hv₀, hN₀⟩
  refine ⟨m₀, v₀, padicValInt p (N m₀ v₀), hm₀, hv₀, fun h ↦ ?_, fun m v hm hv ↦ ?_⟩
  · rcases (padicValInt_dvd_iff _ _).mp h with h | h
    · exact hN₀ h
    · omega
  · by_cases h0 : N m v = 0
    · rw [h0]
      exact dvd_zero _
    · exact (padicValInt_dvd_iff _ _).mpr (.inr (hmin (m, v)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm, hv, h0⟩)))

variable [Fact p.Prime] in
lemma IsSplit.exists_pivot (hs : IsSplit p δ k a N) (hN : sympAdj N * N = ((p : ℤ) ^ δ) • 1)
    (hk : k < n) : ∃ e : ℕ, (∀ m v, k ≤ plane m → k ≤ plane v → (p : ℤ) ^ e ∣ N m v) ∧
      ∃ g ∈ lowFix n k, ∃ g' ∈ lowFix n k, ∀ m,
        ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) * N * g') m (.inl ⟨k, hk⟩) =
          (Pi.single (.inl ⟨k, hk⟩) ((p : ℤ) ^ e) : Fin n ⊕ Fin n → ℤ) m := by
  rcases hs.exists_min hN hk with ⟨m₀, v₀, e, -, hv₀, hndvd, hdvd⟩
  have hcol (m : Fin n ⊕ Fin n) : (p : ℤ) ^ e ∣ N m v₀ := by
    by_cases hm : k ≤ plane m
    · exact hdvd m v₀ hm hv₀
    · rw [hs.apply_eq_zero hN (not_le.mp hm) fun h ↦ hm (h ▸ hv₀)]
      exact dvd_zero _
  let w : Fin n ⊕ Fin n → ℤ := fun m ↦ N m v₀ / (p : ℤ) ^ e
  have hw (m : Fin n ⊕ Fin n) : N m v₀ = (p : ℤ) ^ e * w m := (Int.mul_ediv_cancel' (hcol m)).symm
  have hwk (m : Fin n ⊕ Fin n) (hm : plane m < k) : w m = 0 := by
    have h : (p : ℤ) ^ e * w m = 0 := by
      rw [← hw, hs.apply_eq_zero hN hm fun h ↦ by rw [h] at hm; omega]
    exact (mul_eq_zero.mp h).resolve_left (cast_prime_pow_ne_zero p e)
  have hprim (d : ℤ) (hd : ∀ m, d ∣ w m) : IsUnit d := by
    have hpm : ¬(p : ℤ) ∣ w m₀ := fun h ↦ hndvd (by
      rw [hw m₀, pow_succ]
      exact mul_dvd_mul_left _ h)
    have hcop : IsCoprime ((p : ℤ) ^ δ) (w m₀) :=
      ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp Fact.out)).mpr hpm).pow_left
    have hsum : (p : ℤ) ^ e * ∑ m, sympAdj N v₀ m * w m = (p : ℤ) ^ δ := by
      have e' : (sympAdj N * N) v₀ v₀ = ((p : ℤ) ^ δ • (1 : Matrix (Fin n ⊕ Fin n)
          (Fin n ⊕ Fin n) ℤ)) v₀ v₀ := by
        rw [hN]
      rw [Matrix.mul_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at e'
      rw [← e', Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ ↦ by
        rw [hw]
        ring1
    exact (hcop.of_isCoprime_of_dvd_left (Dvd.intro_left _ hsum)).isUnit_of_dvd'
      (Finset.dvd_sum fun m _ ↦ (hd m).mul_left _) (hd m₀)
  rcases exists_mem_lowFix_mulVec_eq_single hk hwk hprim with ⟨g, hg, hgw⟩
  rcases exists_mem_lowFix_mulVec_eq_single hk (w := Pi.single v₀ 1)
    (fun m hm ↦ Pi.single_eq_of_ne (fun h ↦ by rw [h] at hm; omega) _)
    (fun d hd ↦ isUnit_of_dvd_one (by simpa using hd v₀)) with ⟨h, hh, hhv⟩
  refine ⟨e, hdvd, g, hg, h⁻¹, inv_mem hh, fun m ↦ ?_⟩
  have e₁ : ((h⁻¹ : symplecticGroup (Fin n) ℤ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) *ᵥ
      Pi.single (.inl ⟨k, hk⟩) 1 = Pi.single v₀ 1 := by
    rw [← hhv, mulVec_mulVec, ← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one, one_mulVec]
  have e₂ : N *ᵥ Pi.single v₀ 1 = (p : ℤ) ^ e • w := by
    funext m
    rw [Pi.smul_apply, smul_eq_mul, ← hw]
    simp [mulVec]
  have e₃ : (((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) * N *
      ((h⁻¹ : symplecticGroup (Fin n) ℤ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)) *ᵥ
        Pi.single (.inl ⟨k, hk⟩) 1) m = ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) * N *
          ((h⁻¹ : symplecticGroup (Fin n) ℤ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)) m
            (.inl ⟨k, hk⟩) := by
    simp [mulVec]
  rw [← e₃, ← mulVec_mulVec, ← mulVec_mulVec, e₁, e₂, mulVec_smul, hgw, ← Pi.single_smul,
    smul_eq_mul, mul_one]

lemma IsSplit.exists_row (hs : IsSplit p δ k a N) (hk : k < n) {e : ℕ}
    (hcol : ∀ m, N m (.inl ⟨k, hk⟩) =
      (Pi.single (.inl ⟨k, hk⟩) ((p : ℤ) ^ e) : Fin n ⊕ Fin n → ℤ) m)
    (hdvd : ∀ m v, k ≤ plane m → k ≤ plane v → (p : ℤ) ^ e ∣ N m v) :
    ∃ g ∈ lowFix n k, (∀ m, (N * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)) m
      (.inl ⟨k, hk⟩) = (Pi.single (.inl ⟨k, hk⟩) ((p : ℤ) ^ e) : Fin n ⊕ Fin n → ℤ) m) ∧
        ∀ v, (N * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)) (.inl ⟨k, hk⟩) v =
          (Pi.single (.inl ⟨k, hk⟩) ((p : ℤ) ^ e) : Fin n ⊕ Fin n → ℤ) v := by
  let A : Matrix (Fin n) (Fin n) ℤ := of fun i j ↦
    if i = ⟨k, hk⟩ ∧ (⟨k, hk⟩ : Fin n) < j then -(N (.inl ⟨k, hk⟩) (.inl j) / (p : ℤ) ^ e) else 0
  have hA (i j : Fin n) (h : ¬(i = ⟨k, hk⟩ ∧ (⟨k, hk⟩ : Fin n) < j)) : A i j = 0 := by
    simp [A, h]
  have hlow (i j : Fin n) (hij : (i : ℕ) < k ∨ (j : ℕ) < k) :
      ¬(i = ⟨k, hk⟩ ∧ (⟨k, hk⟩ : Fin n) < j) := by
    rintro ⟨rfl, h⟩
    simp only [Fin.lt_def] at h hij
    omega
  have hAA : A * A = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ ↦ ?_
    by_cases h : i = ⟨k, hk⟩ ∧ (⟨k, hk⟩ : Fin n) < l
    · rw [hA l j fun h' ↦ lt_irrefl _ (h'.1 ▸ h.2), mul_zero]
    · rw [hA i l h, zero_mul]
  let L : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ := fromBlocks (1 + A) 0 0 (1 - Aᵀ)
  have hL : L ∈ symplecticGroup (Fin n) ℤ := by
    refine SymplecticGroup.fromBlocks_mem_iff.mpr ⟨by simp, by simp, ?_⟩
    have hAA' : Aᵀ * Aᵀ = 0 := by
      rw [← transpose_mul, hAA, transpose_zero]
    rw [transpose_add, transpose_one, transpose_zero, Matrix.zero_mul, sub_zero, add_mul,
      Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hAA', sub_zero, sub_add_cancel]
  have hLk : (⟨L, hL⟩ : symplecticGroup (Fin n) ℤ) ∈ lowFix n k := by
    refine mem_lowFix_of_fromBlocks rfl (fun i j hij ↦ ?_) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
      fun i j hij ↦ ?_
    · rw [Matrix.add_apply, hA i j (hlow i j hij), add_zero]
    · rw [Matrix.sub_apply, transpose_apply, hA j i (hlow j i hij.symm), sub_zero]
  have h₁ (m : Fin n ⊕ Fin n) (j : Fin n) :
      (N * L) m (.inl j) = N m (.inl j) + N m (.inl ⟨k, hk⟩) * A ⟨k, hk⟩ j := by
    have hsum : ∑ l, N m (.inl l) * A l j = N m (.inl ⟨k, hk⟩) * A ⟨k, hk⟩ j :=
      Finset.sum_eq_single _ (fun l _ hl ↦ by rw [hA l j fun h ↦ hl h.1, mul_zero]) (by simp)
    simp [L, Matrix.mul_apply, mul_add, Finset.sum_add_distrib, one_apply, hsum]
  have h₁k (m : Fin n ⊕ Fin n) : (N * L) m (.inl ⟨k, hk⟩) = N m (.inl ⟨k, hk⟩) := by
    rw [h₁, hA _ _ fun h ↦ lt_irrefl _ h.2, mul_zero, add_zero]
  have h₁r (j : Fin n) :
      (N * L) (.inl ⟨k, hk⟩) (.inl j) = (Pi.single ⟨k, hk⟩ ((p : ℤ) ^ e) : Fin n → ℤ) j := by
    rw [h₁, hcol (.inl ⟨k, hk⟩), Pi.single_eq_same]
    rcases lt_trichotomy j ⟨k, hk⟩ with hj | rfl | hj
    · rw [hA _ _ fun h ↦ lt_asymm h.2 hj, mul_zero, add_zero, Pi.single_eq_of_ne hj.ne,
        hs.col_inl j hj (.inl ⟨k, hk⟩), Pi.single_eq_of_ne (by simpa using hj.ne')]
    · rw [hA _ _ fun h ↦ lt_irrefl _ h.2, mul_zero, add_zero, hcol, Pi.single_eq_same,
        Pi.single_eq_same]
    · simp only [A, of_apply, hj, and_self, ite_true]
      rw [Pi.single_eq_of_ne hj.ne', mul_neg,
        Int.mul_ediv_cancel' (hdvd (.inl ⟨k, hk⟩) (.inl j) le_rfl (Fin.lt_def.mp hj).le),
        add_neg_cancel]
  have hs₁ : IsSplit p δ k a (N * L) := by
    simpa using hs.mul_mul (one_mem _) hLk
  have hdvd₁ (m v : Fin n ⊕ Fin n) (hm : k ≤ plane m) (hv : k ≤ plane v) :
      (p : ℤ) ^ e ∣ (N * L) m v := by
    simpa using dvd_mul_mul_apply (one_mem _) hLk le_rfl hdvd hm hv
  let d : Fin n → ℤ := fun j ↦
    if k ≤ (j : ℕ) then -((N * L) (.inl ⟨k, hk⟩) (.inr j) / (p : ℤ) ^ e) else 0
  let B : Matrix (Fin n) (Fin n) ℤ := of fun i j ↦
    if i = ⟨k, hk⟩ then d j else if j = ⟨k, hk⟩ then d i else 0
  have hB : Bᵀ = B := by
    ext i j
    simp only [B, transpose_apply, of_apply]
    by_cases hi : i = ⟨k, hk⟩ <;> by_cases hj : j = ⟨k, hk⟩ <;> simp [hi, hj]
  let T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ := fromBlocks 1 B 0 1
  have hT : T ∈ symplecticGroup (Fin n) ℤ :=
    SymplecticGroup.fromBlocks_mem_iff.mpr ⟨by simp, by simp [hB], by simp⟩
  have hTk : (⟨T, hT⟩ : symplecticGroup (Fin n) ℤ) ∈ lowFix n k := by
    refine mem_lowFix_of_fromBlocks rfl (fun _ _ _ ↦ rfl) (fun i j hij ↦ ?_) (fun _ _ _ ↦ rfl)
      fun _ _ _ ↦ rfl
    simp only [B, of_apply, d]
    rcases hij with hi | hj
    · have hik : i ≠ ⟨k, hk⟩ := fun h ↦ by
        rw [h] at hi
        exact lt_irrefl _ hi
      simp [hik, not_le.mpr hi]
    · have hjk : j ≠ ⟨k, hk⟩ := fun h ↦ by
        rw [h] at hj
        exact lt_irrefl _ hj
      simp [hjk, not_le.mpr hj]
  have h₂ (m : Fin n ⊕ Fin n) (j : Fin n) : (N * (L * T)) m (.inl j) = (N * L) m (.inl j) := by
    rw [← Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [T, one_apply]
  have h₂' (j : Fin n) : (N * (L * T)) (.inl ⟨k, hk⟩) (.inr j) = 0 := by
    have e₁ : (N * (L * T)) (.inl ⟨k, hk⟩) (.inr j) =
        (p : ℤ) ^ e * d j + (N * L) (.inl ⟨k, hk⟩) (.inr j) := by
      rw [← Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type]
      simp only [h₁r]
      rw [Finset.sum_eq_single ⟨k, hk⟩ (fun l _ hl ↦ by rw [Pi.single_eq_of_ne hl, zero_mul])
        (by simp), Pi.single_eq_same]
      simp [T, B, one_apply]
    rw [e₁]
    by_cases hj : k ≤ (j : ℕ)
    · simp only [d, hj, ite_true]
      rw [mul_neg, Int.mul_ediv_cancel' (hdvd₁ (.inl ⟨k, hk⟩) (.inr j) le_rfl hj), neg_add_cancel]
    · simp only [d, hj, ite_false, mul_zero, zero_add]
      rw [hs₁.col_inr j (not_le.mp hj) (.inl ⟨k, hk⟩)]
      simp
  refine ⟨⟨L * T, mul_mem hL hT⟩, mul_mem hLk hTk, fun m ↦ (h₂ m _).trans ((h₁k m).trans
    (hcol m)), fun v ↦ ?_⟩
  rcases v with j | j
  · exact (h₂ _ j).trans ((h₁r j).trans (by simp [Pi.single_apply]))
  · exact (h₂' j).trans (by simp)

/-! ### Integral matrices of `S_p` and double cosets -/

variable (p δ a) in
/-- The **entries `(p^{a_0}, …, p^{a_{g-1}}, p^{δ - a_0}, …, p^{δ - a_{g-1}})`** at the coordinates
`(e_0, …, e_{g-1}, f_0, …, f_{g-1})` of the diagonal matrix of the symplectic elementary divisors of
multiplier `p^δ` (LMFDB `mf.siegel.lift`, through Satake's theorem). -/
def elementaryEntries : Fin n ⊕ Fin n → ℕ :=
  Sum.elim (fun j ↦ p ^ a j) fun j ↦ p ^ (δ - a j)

variable (p) in
lemma elementaryEntries_mul (ha : ∀ j, a j ≤ δ) (j : Fin n) :
    elementaryEntries p δ a (.inl j) * elementaryEntries p δ a (.inr j) = p ^ δ := by
  rw [elementaryEntries, Sum.elim_inl, Sum.elim_inr, ← pow_add, Nat.add_sub_cancel' (ha j)]

lemma exists_intMatrix_of_mem (x : heckeMonoidAt (Fin n) p) :
    ∃ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) (e : ℕ),
      (Int.castRingHom ℚ).mapMatrix M = (x : GL (Fin n ⊕ Fin n) ℚ) ∧
        Mᵀ * J (Fin n) ℤ * M = ((p : ℤ) ^ e) • J (Fin n) ℤ := by
  rcases x.2 with ⟨⟨-, M, hM⟩, e, he⟩
  have hM' : (Int.castRingHom ℚ).mapMatrix M = (x : GL (Fin n ⊕ Fin n) ℚ) :=
    hM
  refine ⟨M, e, hM', Matrix.map_injective (Int.cast_injective (α := ℚ)) ?_⟩
  have h (M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) :
      M'.map (↑) = (Int.castRingHom ℚ).mapMatrix M' :=
    rfl
  have hJ : (((p : ℤ) ^ e) • J (Fin n) ℤ).map (↑) = ((p : ℚ) ^ e) • J (Fin n) ℚ := by
    rw [← map_J (Fin n) (Int.castRingHom ℚ)]
    ext i j
    simp only [map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast, eq_intCast]
  have hT : (Int.castRingHom ℚ).mapMatrix Mᵀ = ((x : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ := by
    rw [← hM', RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, transpose_map]
  have hJ' : (Int.castRingHom ℚ).mapMatrix (J (Fin n) ℤ) = J (Fin n) ℚ := by
    rw [RingHom.mapMatrix_apply, map_J]
  dsimp only
  rw [hJ, h, map_mul, map_mul, hM', hT, hJ', he]

lemma mem_doubleCoset_of_intMatrix {x y : GL (Fin n ⊕ Fin n) ℚ}
    {M γ γ' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ} (hx : (Int.castRingHom ℚ).mapMatrix M = x)
    (hy : (Int.castRingHom ℚ).mapMatrix N = y) (hγ : γ ∈ symplecticGroup (Fin n) ℤ)
    (hγ' : γ' ∈ symplecticGroup (Fin n) ℤ) (h : γ * M * γ' = N) :
    x ∈ DoubleCoset.doubleCoset y (heckeGamma (Fin n) : Set (GL (Fin n ⊕ Fin n) ℚ))
      (heckeGamma (Fin n)) := by
  have e : y = spToGL (Fin n) ⟨γ, hγ⟩ * x * spToGL (Fin n) ⟨γ', hγ'⟩ :=
    Units.ext <| by
      rw [← hy, ← h, map_mul, map_mul, hx]
      rfl
  refine DoubleCoset.mem_doubleCoset.mpr ⟨(spToGL (Fin n) ⟨γ, hγ⟩)⁻¹,
    inv_mem ⟨_, trivial, rfl⟩, (spToGL (Fin n) ⟨γ', hγ'⟩)⁻¹, inv_mem ⟨_, trivial, rfl⟩, ?_⟩
  rw [e]
  group

variable [Fact p.Prime]

lemma IsSplit.succ (hs : IsSplit p δ k a N) (hN : N * sympAdj N = ((p : ℤ) ^ δ) • 1) (hk : k < n)
    {e : ℕ} (hcol : ∀ m, N m (.inl ⟨k, hk⟩) =
      (Pi.single (.inl ⟨k, hk⟩) ((p : ℤ) ^ e) : Fin n ⊕ Fin n → ℤ) m)
    (hrow : ∀ v, N (.inl ⟨k, hk⟩) v =
      (Pi.single (.inl ⟨k, hk⟩) ((p : ℤ) ^ e) : Fin n ⊕ Fin n → ℤ) v)
    (hdvd : ∀ m v, k ≤ plane m → k ≤ plane v → (p : ℤ) ^ e ∣ N m v) :
    IsSplit p δ (k + 1) (Function.update a ⟨k, hk⟩ e) N where
  col_inl i hi m := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · rw [Function.update_of_ne (Fin.ne_of_val_ne hi.ne)]
      exact hs.col_inl i hi m
    · rw [(Fin.ext hi : i = ⟨k, hk⟩), Function.update_self]
      exact hcol m
  col_inr i hi m := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · rw [Function.update_of_ne (Fin.ne_of_val_ne hi.ne)]
      exact hs.col_inr i hi m
    · rw [(Fin.ext hi : i = ⟨k, hk⟩), Function.update_self]
      have h : (p : ℤ) ^ e * N m (.inr ⟨k, hk⟩) = if m = .inr ⟨k, hk⟩ then (p : ℤ) ^ δ else 0 :=
        mul_apply_inr_of_row_inl hN hrow m
      have hδ : (p : ℤ) ^ e * N (.inr ⟨k, hk⟩) (.inr ⟨k, hk⟩) = (p : ℤ) ^ δ := by
        simpa using mul_apply_inr_of_row_inl hN hrow (.inr ⟨k, hk⟩)
      have hle : e ≤ δ := le_of_pow_dvd_pow (Dvd.intro _ hδ)
      rw [Pi.single_apply]
      split_ifs with hm
      · rw [hm]
        refine mul_left_cancel₀ (cast_prime_pow_ne_zero p e) ?_
        rw [hδ, ← pow_add, Nat.add_sub_cancel' hle]
      · rw [ite_eq_right hm] at h
        exact (mul_eq_zero.mp h).resolve_left (cast_prime_pow_ne_zero p e)
  dvd i hi m v hm hv := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · rw [Function.update_of_ne (Fin.ne_of_val_ne hi.ne)]
      exact hs.dvd i hi m v hm hv
    · rw [(Fin.ext hi : i = ⟨k, hk⟩), Function.update_self]
      exact hdvd m v (hi ▸ hm) (hi ▸ hv)

lemma IsSplit.exists_succ (hs : IsSplit p δ k a N)
    (hN : Nᵀ * J (Fin n) ℤ * N = ((p : ℤ) ^ δ) • J (Fin n) ℤ) (hk : k < n) :
    ∃ a' : Fin n → ℕ, ∃ γ ∈ symplecticGroup (Fin n) ℤ, ∃ γ' ∈ symplecticGroup (Fin n) ℤ,
      IsSplit p δ (k + 1) a' (γ * N * γ') := by
  rcases hs.exists_pivot (sympAdj_mul hN) hk with ⟨e, hdvd, g, hg, g', hg', hcol⟩
  rcases (hs.mul_mul hg hg').exists_row hk hcol fun m v hm hv ↦
    dvd_mul_mul_apply hg hg' le_rfl hdvd hm hv with ⟨g'', hg'', hcol', hrow'⟩
  have e₀ : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) * N * g' * g'' = g * N *
      ((g' * g'' : symplecticGroup (Fin n) ℤ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) := by
    rw [Submonoid.coe_mul, Matrix.mul_assoc]
  rw [e₀] at hcol' hrow'
  refine ⟨_, g, g.2, g' * g'', (g' * g'').2, (hs.mul_mul hg (mul_mem hg' hg'')).succ
    (mul_sympAdj (cast_prime_pow_ne_zero p δ) (transpose_mul_J_mul_eq_of_mem g.2 (g' * g'').2 hN))
    hk hcol' hrow' fun m v hm hv ↦ dvd_mul_mul_apply hg (mul_mem hg' hg'') le_rfl hdvd hm hv⟩

lemma exists_isSplit (hM : Nᵀ * J (Fin n) ℤ * N = ((p : ℤ) ^ δ) • J (Fin n) ℤ) (hk : k ≤ n) :
    ∃ a : Fin n → ℕ, ∃ γ ∈ symplecticGroup (Fin n) ℤ, ∃ γ' ∈ symplecticGroup (Fin n) ℤ,
      IsSplit p δ k a (γ * N * γ') := by
  induction k with
  | zero => exact ⟨0, 1, one_mem _, 1, one_mem _, isSplit_zero⟩
  | succ k ih =>
    rcases ih (Nat.le_of_succ_le hk) with ⟨a, γ, hγ, γ', hγ', hs⟩
    rcases hs.exists_succ (transpose_mul_J_mul_eq_of_mem hγ hγ' hM) (Nat.lt_of_succ_le hk) with
      ⟨a', g, hg, g', hg', hs'⟩
    exact ⟨a', g * γ, mul_mem hg hγ, γ' * g', mul_mem hγ' hg', by
      simpa only [Matrix.mul_assoc] using hs'⟩

lemma exists_mul_mul_eq_diagonal_of_mul_J
    (hN : Nᵀ * J (Fin n) ℤ * N = ((p : ℤ) ^ δ) • J (Fin n) ℤ) :
    ∃ b : Fin n → ℕ, Monotone b ∧ (∀ j, 2 * b j ≤ δ) ∧ ∃ γ ∈ symplecticGroup (Fin n) ℤ,
      ∃ γ' ∈ symplecticGroup (Fin n) ℤ,
        γ * N * γ' = diagonal fun i ↦ (elementaryEntries p δ b i : ℤ) := by
  rcases exists_isSplit hN le_rfl with ⟨b, γ, hγ, γ', hγ', hs⟩
  refine ⟨b, fun i j hij ↦ ?_, fun j ↦ ?_, γ, hγ, γ', hγ', ?_⟩
  · have h : (p : ℤ) ^ b i ∣ (γ * N * γ') (.inl j) (.inl j) := hs.dvd i i.2 _ _ hij hij
    rw [hs.col_inl j j.2, Pi.single_eq_same] at h
    exact le_of_pow_dvd_pow h
  · have h : (p : ℤ) ^ b j ∣ (γ * N * γ') (.inr j) (.inr j) := hs.dvd j j.2 _ _ le_rfl le_rfl
    rw [hs.col_inr j j.2, Pi.single_eq_same] at h
    have h' : b j ≤ δ - b j := le_of_pow_dvd_pow h
    omega
  · ext m (i | i)
    · rw [hs.col_inl i i.2, diagonal_apply, Pi.single_apply]
      split_ifs with hm
      · rw [hm]
        simp [elementaryEntries]
      · rfl
    · rw [hs.col_inr i i.2, diagonal_apply, Pi.single_apply]
      split_ifs with hm
      · rw [hm]
        simp [elementaryEntries]
      · rfl

variable (p δ a) in
/-- The **diagonal matrix `diag(p^{a_0}, …, p^{a_{g-1}}, p^{δ - a_0}, …, p^{δ - a_{g-1}})`** of
`S_p`, of multiplier `p^δ` (LMFDB `mf.siegel.lift`, through Satake's theorem), for
`a_0, …, a_{g-1} ≤ δ`; `T(p)` is that of `δ = 1`, `a = 0`. -/
def elementaryDiag (ha : ∀ j, a j ≤ δ) : heckeMonoidAt (Fin n) p :=
  heckeDiagonal (elementaryEntries p δ a) p δ (Fact.out : p.Prime).pos (elementaryEntries_mul p ha)

variable (p δ a) in
/-- The **double coset `Γ diag(p^{a_0}, …, p^{a_{g-1}}, p^{δ - a_0}, …, p^{δ - a_{g-1}}) Γ`** of
`Γ = Sp(2g, ℤ)` in `S_p` (LMFDB `mf.siegel.lift`, through Satake's theorem), for
`a_0, …, a_{g-1} ≤ δ`. By the symplectic elementary divisor theorem
(`SiegelUpperHalfSpace.exists_eq_elementaryCoset`) these are all the double cosets. -/
def elementaryCoset (ha : ∀ j, a j ≤ δ) :
    HeckeCoset (heckeMonoidAt (Fin n) p) (heckeGamma (Fin n)) (heckeGamma (Fin n)) :=
  HeckeCoset.mk _ _ (elementaryDiag p δ a ha)

lemma coe_elementaryDiag (ha : ∀ j, a j ≤ δ) :
    (((elementaryDiag p δ a ha : heckeMonoidAt (Fin n) p) : GL (Fin n ⊕ Fin n) ℚ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) =
        diagonal fun i ↦ (elementaryEntries p δ a i : ℚ) :=
  rfl

lemma mapMatrix_elementaryEntries (ha : ∀ j, a j ≤ δ) :
    (Int.castRingHom ℚ).mapMatrix (diagonal fun i ↦ (elementaryEntries p δ a i : ℤ)) =
      ((elementaryDiag p δ a ha : heckeMonoidAt (Fin n) p) : GL (Fin n ⊕ Fin n) ℚ) := by
  rw [RingHom.mapMatrix_apply, diagonal_map (map_zero _)]
  rfl

/-- **The symplectic elementary divisor theorem** (LMFDB `mf.siegel.lift`, through Satake's
theorem; Andrianov, *Quadratic forms and Hecke operators*, Lemma 3.3.6): every double coset of
`Γ = Sp(2g, ℤ)` in `S_p` is `Γ diag(p^{a_0}, …, p^{a_{g-1}}, p^{δ - a_0}, …, p^{δ - a_{g-1}}) Γ`
with `a_0 ≤ ⋯ ≤ a_{g-1}` and `2 a_j ≤ δ`, `p^δ` being the multiplier. -/
lemma exists_eq_elementaryCoset
    (D : HeckeCoset (heckeMonoidAt (Fin n) p) (heckeGamma (Fin n)) (heckeGamma (Fin n))) :
    ∃ (δ : ℕ) (a : Fin n → ℕ) (ha : ∀ j, a j ≤ δ), Monotone a ∧ (∀ j, 2 * a j ≤ δ) ∧
      D = elementaryCoset p δ a ha := by
  rcases exists_intMatrix_of_mem D.rep with ⟨M, e, hM, hMJ⟩
  rcases exists_mul_mul_eq_diagonal_of_mul_J hMJ with ⟨b, hb, h2b, γ, hγ, γ', hγ', h⟩
  have hle (j : Fin n) : b j ≤ e := by
    have h' : 2 * b j ≤ e := h2b j
    omega
  refine ⟨e, b, hle, hb, h2b, ?_⟩
  rw [← HeckeCoset.mk_rep D]
  exact HeckeCoset.mk_eq_mk_of_mem
    (mem_doubleCoset_of_intMatrix hM (mapMatrix_elementaryEntries hle) hγ hγ' h)

end SiegelUpperHalfSpace
