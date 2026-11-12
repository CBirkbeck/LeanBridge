import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Borel
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.SplitCartan
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Bruhat

/-!
# Borel subgroups of `GL₂` are maximal, and the subgroups of `B` with an element of order `p`

The Borel subgroups of `GL₂(F)` are maximal subgroups (LMFDB `gl2.borel`): a subgroup strictly
containing the upper triangular subgroup `B` contains an element of the big Bruhat cell `B w B`,
hence the Weyl element `w`, and `B` and `w` generate `GL₂(F)`.

The knowl also says that the subgroups of `B` not contained in the diagonal subgroup are precisely
those with an element of order `p`. As written this fails (for `p = 3` the matrix `!![1, 1; 0, 2]`
has order `2`), but it holds up to conjugacy: a subgroup `H` of `B ⊆ GL₂(𝔽_p)` has an element of
order `p` if and only if it lies in no conjugate of the diagonal subgroup. Indeed the diagonal
subgroup has exponent dividing `p - 1`; conversely, if `H` has no element of order `p` it meets the
unipotent radical trivially, so it is abelian, and either all its elements have equal diagonal
entries, and then they are scalar, or one of them has distinct eigenvalues, and the unipotent
matrix diagonalising it diagonalises all of `H`.

## Main results

* `Matrix.GeneralLinearGroup.isCoatom_gl2Borel` (LMFDB `gl2.borel`): the upper triangular subgroup
  of `GL₂(F)` is a maximal subgroup.
* `Matrix.GeneralLinearGroup.IsBorelSubgroup.isCoatom` (LMFDB `gl2.borel`): every Borel subgroup of
  `GL₂(F)` is a maximal subgroup.
* `Matrix.GeneralLinearGroup.exists_orderOf_eq_iff_forall_not_le_map_diagonalTorus` (LMFDB
  `gl2.borel`): a subgroup of the Borel subgroup of `GL₂(𝔽_p)` has an element of order `p` if and
  only if it lies in no conjugate of the diagonal subgroup.
-/

open Matrix TauCeti Subgroup

namespace Matrix.GeneralLinearGroup

section Maximal

variable {F : Type*} [Field F]

/-- **The upper triangular subgroup of `GL₂(F)` is a maximal subgroup** (LMFDB `gl2.borel`): a
subgroup strictly containing it meets the big Bruhat cell, so it contains the Weyl element, and
the two generate `GL₂(F)`. -/
lemma isCoatom_gl2Borel : IsCoatom (GL2Borel F) := by
  refine ⟨GL2Borel.ne_top F, fun H hBH ↦ ?_⟩
  rcases IsConcreteLE.exists_of_lt hBH with ⟨g, hgH, hgB⟩
  rcases DoubleCoset.mem_doubleCoset.mp (GL2Borel.mem_doubleCoset_weyl_of_notMem hgB) with
    ⟨x, hx, y, hy, rfl⟩
  have hw : GL2WeylElement F ∈ H := by
    simpa [mul_assoc] using H.mul_mem (H.mul_mem (H.inv_mem (hBH.le hx)) hgH)
      (H.inv_mem (hBH.le hy))
  rw [eq_top_iff, ← GL2Borel.closure_insert_gl2WeylElement_eq_top F, closure_le]
  exact Set.insert_subset hw hBH.le

/-- **Every Borel subgroup of `GL₂(F)` is a maximal subgroup** (LMFDB `gl2.borel`). -/
lemma IsBorelSubgroup.isCoatom {H : Subgroup (GL (Fin 2) F)} (hH : IsBorelSubgroup H) :
    IsCoatom H := by
  rcases hH with ⟨g, rfl⟩
  exact ((MulAut.conj g).mapSubgroup.isCoatom_iff _).mpr isCoatom_gl2Borel

end Maximal

section OrderP

variable {p : ℕ} [Fact p.Prime] {H : Subgroup (GL (Fin 2) (ZMod p))}

lemma upperRightHom_pow_prime (b : ZMod p) : upperRightHom b ^ p = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
    AddChar.map_zero_eq_one]

lemma orderOf_upperRightHom {b : ZMod p} (hb : b ≠ 0) : orderOf (upperRightHom b) = p :=
  orderOf_eq_prime (upperRightHom_pow_prime b) fun h ↦
    hb (injective_upperRightHom (h.trans (AddChar.map_zero_eq_one _).symm))

lemma eq_upperRightHom {x : GL (Fin 2) (ZMod p)} (h₀₀ : x.1 0 0 = 1)
    (h₁₀ : x.1 1 0 = 0) (h₁₁ : x.1 1 1 = 1) :
    x = upperRightHom (x.1 0 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperRightHom, h₀₀, h₁₀, h₁₁]

lemma eq_one_of_forall_orderOf_ne (hno : ∀ h ∈ H, orderOf h ≠ p) {x : GL (Fin 2) (ZMod p)}
    (hx : x ∈ H) (h₀₀ : x.1 0 0 = 1) (h₁₀ : x.1 1 0 = 0)
    (h₁₁ : x.1 1 1 = 1) : x = 1 := by
  rw [eq_upperRightHom h₀₀ h₁₀ h₁₁] at hx ⊢
  by_cases hb : x.1 0 1 = 0
  · rw [hb, AddChar.map_zero_eq_one]
  · exact absurd (orderOf_upperRightHom hb) (hno _ hx)

lemma commute_of_forall_orderOf_ne (hH : H ≤ GL2Borel (ZMod p)) (hno : ∀ h ∈ H, orderOf h ≠ p)
    {x y : GL (Fin 2) (ZMod p)} (hx : x ∈ H) (hy : y ∈ H) : x * y = y * x := by
  let c : GL2Borel (ZMod p) := ⟨x, hH hx⟩ * ⟨y, hH hy⟩ * (⟨x, hH hx⟩)⁻¹ * (⟨y, hH hy⟩)⁻¹
  have hc : GL2Borel.diag c = 1 := by
    simp only [c, map_mul, map_inv]
    rw [mul_right_comm, mul_inv_cancel_right, mul_inv_cancel]
  have h₁ : (c : GL (Fin 2) (ZMod p)) = 1 := by
    refine eq_one_of_forall_orderOf_ne hno ?_ ?_ (GL2Borel.apply_one_zero c) ?_
    · exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
    · simpa using congrArg (fun q ↦ ((q.1 : (ZMod p)ˣ) : ZMod p)) hc
    · simpa using congrArg (fun q ↦ ((q.2 : (ZMod p)ˣ) : ZMod p)) hc
  simp only [c, Subgroup.coe_mul, Subgroup.coe_inv] at h₁
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h₁
  exact h₁

lemma pow_card_sub_one_mem_diagonalTorus {d : GL (Fin 2) (ZMod p)} (hd : d ∈ diagonalTorus _ 2) :
    d ^ (p - 1) = 1 := by
  rcases mem_diagonalTorus_iff_exists_diagGL.mp hd with ⟨t, rfl⟩
  rw [← map_pow, show t ^ (p - 1) = 1 from funext fun i ↦ ZMod.units_pow_card_sub_one_eq_one p _,
    map_one]

lemma eq_scalar_mul_upperRightHom {x : GL (Fin 2) (ZMod p)} {a : (ZMod p)ˣ}
    (h₀₀ : x.1 0 0 = a) (h₁₀ : x.1 1 0 = 0) (h₁₁ : x.1 1 1 = a) :
    x = scalar (Fin 2) a * upperRightHom ((a⁻¹ : (ZMod p)ˣ) * x.1 0 1) := by
  ext i j
  rw [Units.val_mul, coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [upperRightHom, h₀₀, h₁₀, h₁₁, -Units.val_inv_eq_inv_val]

lemma commute_scalar (a : (ZMod p)ˣ) (g : GL (Fin 2) (ZMod p)) : Commute (scalar (Fin 2) a) g :=
  Units.ext <| by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

/-- **A subgroup of the Borel subgroup of `GL₂(𝔽_p)` has an element of order `p` if and only if it
lies in no conjugate of the diagonal subgroup** (LMFDB `gl2.borel`, corrected: the knowl says
'not contained in the subgroup of diagonal matrices', which is false for `p = 3`). -/
lemma exists_orderOf_eq_iff_forall_not_le_map_diagonalTorus (hH : H ≤ GL2Borel (ZMod p)) :
    (∃ h ∈ H, orderOf h = p) ↔
      ∀ g : GL (Fin 2) (ZMod p), ¬H ≤ (diagonalTorus _ 2).map (MulAut.conj g).toMonoidHom := by
  refine ⟨fun ⟨h, hh, hp⟩ g hle ↦ ?_, fun h ↦ ?_⟩
  · rcases mem_map.mp (hle hh) with ⟨d, hd, rfl⟩
    have h1 : (MulAut.conj g).toMonoidHom d ^ (p - 1) = 1 := by
      rw [← map_pow, pow_card_sub_one_mem_diagonalTorus hd, map_one]
    have h2 : p.Prime := Fact.out
    have h3 := Nat.le_of_dvd (Nat.sub_pos_of_lt h2.one_lt) (hp ▸ orderOf_dvd_of_pow_eq_one h1)
    have h4 := h2.one_lt
    omega
  by_contra hno
  push Not at hno
  by_cases hs : ∃ x ∈ H, x.1 0 0 ≠ x.1 1 1
  · rcases hs with ⟨x, hx, hne⟩
    have hda : x.1 1 1 - x.1 0 0 ≠ 0 := sub_ne_zero.mpr hne.symm
    refine h (upperRightHom (x.1 0 1 / (x.1 1 1 - x.1 0 0))) fun y hy ↦
      mem_map.mpr ⟨_, ?_, (MulAut.conj _).apply_symm_apply y⟩
    have hx10 : x.1 1 0 = 0 := GL2Borel.mem_iff.mp (hH hx)
    have hy10 : y.1 1 0 = 0 := GL2Borel.mem_iff.mp (hH hy)
    have e := congrArg (fun g : GL (Fin 2) (ZMod p) ↦ g.1 0 1)
      (commute_of_forall_orderOf_ne hH hno hx hy)
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at e
    refine mem_diagonalTorus_of_fin_two _ ?_ ?_
    · simp [MulAut.conj_symm_apply, upperRightHom, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.vecMul, dotProduct, hy10]
      field_simp
      linear_combination -e
    · simp [MulAut.conj_symm_apply, upperRightHom, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.vecMul, dotProduct, hy10]
  push Not at hs
  refine h 1 fun y hy ↦ mem_map.mpr ⟨y, ?_, by simp⟩
  have hy10 : y.1 1 0 = 0 := GL2Borel.mem_iff.mp (hH hy)
  let a : (ZMod p)ˣ := (GL2Borel.diag ⟨y, hH hy⟩).1
  have ha : (a : ZMod p) = y.1 0 0 := GL2Borel.diag_fst_val _
  have hy' := eq_scalar_mul_upperRightHom ha.symm hy10 (ha.trans (hs y hy)).symm
  have hpow : y ^ (p - 1) = upperRightHom ((p - 1 : ℕ) • ((a⁻¹ : (ZMod p)ˣ) * y.1 0 1)) := by
    nth_rw 1 [hy']
    rw [(commute_scalar a _).mul_pow, ← map_pow, ZMod.units_pow_card_sub_one_eq_one,
      map_one, one_mul, AddChar.map_nsmul_eq_pow]
  have hz : (a⁻¹ : (ZMod p)ˣ) * y.1 0 1 = 0 := by
    by_contra hz
    refine hno _ (H.pow_mem hy (p - 1)) ?_
    rw [hpow]
    refine orderOf_upperRightHom ?_
    rw [nsmul_eq_mul, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, ZMod.natCast_self,
      Nat.cast_one, zero_sub, neg_one_mul, neg_ne_zero]
    exact hz
  refine mem_diagonalTorus_of_fin_two _ ?_ hy10
  simpa [-Units.val_inv_eq_inv_val] using hz

end OrderP

end Matrix.GeneralLinearGroup
