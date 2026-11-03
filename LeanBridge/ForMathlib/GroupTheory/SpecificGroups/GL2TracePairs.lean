import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.RationalCanonicalFormFinTwo
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# Pairs of `2 × 2` matrices with the same traces are conjugate

Let `F` be a field of characteristic not `2`. Two pairs `(A, B)` and `(A', B')` of `2 × 2` matrices
over `F`, with `A` and `A'` of trace `0` and nonzero determinant, are conjugate under `GL₂(F)` if
they have the same `det A`, `tr B`, `det B`, `tr AB`, and if `AB - BA` is invertible. This is the
form of the Skolem–Noether theorem used to prove that the exceptional subgroups of `GL₂(𝔽_p)` are
determined up to conjugacy by Sutherland's label (Lemma 3.21 of arXiv:1504.07618v7).

After a conjugation, `A' = A`. Then `B = b₀ + b₁ A + w` and `B' = b₀ + b₁ A + w'` with the same
`b₀`, `b₁`, where `w`, `w'` have trace `0` and anticommute with `A`, and `det w = det w' = ν`, which
is not zero. This is Hilbert's Theorem 90 for the algebra `F[A]`: the element `w' w⁻¹` of `F[A]` has
norm `1`, and `g = ν - w' w` satisfies `g A = A g` and `g w = w' g`. If it is not invertible then
`g = 0`, so `w' = -w`, and `A` conjugates `(A, w)` to `(A, w')`.

## Main results

* `Matrix.exists_mul_eq_mul_of_trace_det_eq`: pairs with the same traces and determinants are
  intertwined by an element of `GL₂(F)`.
-/

open Matrix TauCeti

namespace Matrix

variable {F : Type*} [Field F] {A A' B B' X Y : Matrix (Fin 2) (Fin 2) F}

variable (X Y) in
lemma det_add_fin_two : (X + Y).det = X.det + Y.det + X.trace * Y.trace - (X * Y).trace := by
  simp only [det_fin_two, trace_fin_two, add_apply, mul_apply, Fin.sum_univ_two]
  ring1

variable (X) in
lemma det_smul_one_sub (ν : F) : (ν • 1 - X).det = ν * ν - ν * X.trace + X.det := by
  simp only [det_fin_two, trace_fin_two, sub_apply, smul_apply, one_apply_eq,
    one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  ring1

lemma mul_add_mul_eq_of_trace_eq_zero (hX : X.trace = 0) (hY : Y.trace = 0) :
    X * Y + Y * X = (X * Y).trace • 1 := by
  rw [trace_fin_two] at hX hY
  have hX' : X 1 1 = -X 0 0 := by
    linear_combination hX
  have hY' : Y 1 1 = -Y 0 0 := by
    linear_combination hY
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, trace_fin_two, hX', hY'] <;> ring1

lemma exists_mul_eq_companion (h2 : (2 : F) ≠ 0) (hA : A.trace = 0) (hdet : A.det ≠ 0) :
    ∃ Q : GL (Fin 2) F, A * Q.val = Q.val * companionFinTwo 0 A.det := by
  have hns : A ∉ Set.range (scalar (Fin 2)) := by
    rintro ⟨a, rfl⟩
    have h₁ : (2 : F) * a = 0 := by
      simpa using hA
    exact hdet <| by simp [(mul_eq_zero.mp h₁).resolve_left h2]
  rcases exists_det_ne_zero_mul_eq_mul_companionFinTwo hns with ⟨P, hP, h⟩
  exact ⟨GeneralLinearGroup.mkOfDetNeZero P hP, hA ▸ h⟩

lemma exists_mul_eq_mul_of_trace_eq_of_same_left (h2 : (2 : F) ≠ 0) (hA : A.trace = 0)
    (hdet : A.det ≠ 0) (htrB : B.trace = B'.trace) (hdetB : B.det = B'.det)
    (htrAB : (A * B).trace = (A * B').trace) (hκ : (A * B - B * A).det ≠ 0) :
    ∃ g : GL (Fin 2) F, g.val * A = A * g.val ∧ g.val * B = B' * g.val := by
  have hA2 : A * A = -(A.det • 1) := by
    rw [← sq, sq_eq_trace_smul_sub_det_smul_one_fin_two, hA, zero_smul, zero_sub]
  have htrA2 : (A * A).trace = -(2 * A.det) := by
    rw [hA2, trace_neg, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
    push_cast
    ring1
  generalize hb₀ : B.trace / 2 = b₀
  generalize hb₁ : (A * B).trace / (2 * A.det) = b₁
  have hb₀' : B.trace = 2 * b₀ := by
    rw [← hb₀]
    field_simp
  have hb₁' : (A * B).trace = 2 * A.det * b₁ := by
    rw [← hb₁]
    field_simp
  generalize hX : b₀ • (1 : Matrix (Fin 2) (Fin 2) F) - b₁ • A = X
  have hXtr : X.trace = B.trace := by
    rw [← hX, trace_sub, trace_smul, trace_smul, trace_one, hA, Fintype.card_fin, hb₀']
    simp [mul_comm]
  have hXA : X * A = A * X := by
    rw [← hX]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  have hkey {C : Matrix (Fin 2) (Fin 2) F} (hCtr : C.trace = B.trace)
      (hCA : (A * C).trace = (A * B).trace) : (C - X).trace = 0 ∧ (A * (C - X)).trace = 0 ∧
        (C - X) * A = -(A * (C - X)) ∧ (C - X).det = C.det - X.det := by
    have h₁ : (C - X).trace = 0 := by
      rw [trace_sub, hCtr, hXtr, sub_self]
    have h₂ : (A * (C - X)).trace = 0 := by
      rw [Matrix.mul_sub, trace_sub, hCA, ← hX, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
        Matrix.mul_one, trace_sub, trace_smul, trace_smul, hA, htrA2, hb₁']
      simp
      ring1
    have h₃ : (C - X) * A = -(A * (C - X)) := by
      have h₄ : A * (C - X) + (C - X) * A = (A * (C - X)).trace • 1 :=
        mul_add_mul_eq_of_trace_eq_zero hA h₁
      rw [h₂, zero_smul] at h₄
      exact eq_neg_of_add_eq_zero_right h₄
    refine ⟨h₁, h₂, h₃, ?_⟩
    have h₆ : (X * (C - X)).trace = 0 := by
      generalize C - X = Y at h₁ h₂
      rw [← hX, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, trace_sub,
        trace_smul, trace_smul, h₁, h₂]
      simp
    have h₅ : (X + (C - X)).det = X.det + (C - X).det + X.trace * (C - X).trace -
        (X * (C - X)).trace :=
      det_add_fin_two X (C - X)
    rw [add_sub_cancel, h₁, mul_zero, add_zero, h₆, sub_zero] at h₅
    rw [h₅]
    ring1
  rcases hkey rfl rfl with ⟨hw₁, hw₂, hw₃, hw₄⟩
  rcases hkey htrB.symm htrAB.symm with ⟨hw'₁, hw'₂, hw'₃, hw'₄⟩
  generalize hw : B - X = w at hw₁ hw₂ hw₃ hw₄
  generalize hw' : B' - X = w' at hw'₁ hw'₂ hw'₃ hw'₄
  have hBX : B = X + w := by
    rw [← hw, add_sub_cancel]
  have hB'X : B' = X + w' := by
    rw [← hw', add_sub_cancel]
  have hνν : w'.det = w.det := by
    rw [hw₄, hw'₄, hdetB]
  have hκ' : A * B - B * A = (2 : F) • (A * w) := by
    rw [hBX, Matrix.mul_add, Matrix.add_mul, hXA, hw₃, two_smul]
    abel
  have hν : w.det ≠ 0 := fun hν ↦ hκ <| by
    rw [hκ', det_smul, det_mul, hν, mul_zero, mul_zero]
  have hww : w * w = -(w.det • 1) := by
    rw [← sq, sq_eq_trace_smul_sub_det_smul_one_fin_two, hw₁, zero_smul, zero_sub]
  have hw'w' : w' * w' = -(w.det • 1) := by
    rw [← sq, sq_eq_trace_smul_sub_det_smul_one_fin_two, hw'₁, zero_smul, zero_sub, hνν]
  generalize hg : w.det • (1 : Matrix (Fin 2) (Fin 2) F) - w' * w = g
  have hgA : g * A = A * g := by
    rw [← hg]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, hw₃]
    rw [Matrix.mul_neg, ← Matrix.mul_assoc w' A w, hw'₃, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have hgX : g * X = X * g := by
    rw [← hX]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hgA]
  have hgw : g * w = w' * g := by
    rw [← hg]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hww]
    rw [← Matrix.mul_assoc w' w' w, hw'w']
    simp only [Matrix.mul_neg, Matrix.neg_mul]
    abel
  have hgB : g * B = B' * g := by
    rw [hBX, hB'X, Matrix.mul_add, Matrix.add_mul, hgX, hgw]
  by_cases hgdet : g.det = 0
  · have hgtr : g.trace = 0 := by
      have hdetg : g.det = w.det * (w.det * 2 - (w' * w).trace) := by
        rw [← hg, det_smul_one_sub, det_mul, hνν]
        ring1
      have h₁ : w.det * 2 - (w' * w).trace = 0 :=
        (mul_eq_zero.mp (hdetg.symm.trans hgdet)).resolve_left hν
      rw [← hg, trace_sub, trace_smul, trace_one, Fintype.card_fin]
      simp only [smul_eq_mul]
      exact h₁
    have hgg : g * g = 0 := by
      rw [← sq, sq_eq_trace_smul_sub_det_smul_one_fin_two, hgtr, hgdet, zero_smul, zero_smul,
        sub_zero]
    have hg₀ : g = 0 := by
      have h₁ : g * A + A * g = (g * A).trace • 1 := mul_add_mul_eq_of_trace_eq_zero hgtr hA
      rw [← hgA, ← two_smul F (g * A)] at h₁
      have h₂ : (2 : F) • (g * A * A) = (g * A).trace • A := by
        rw [← Matrix.smul_mul, h₁, Matrix.smul_mul, Matrix.one_mul]
      rw [Matrix.mul_assoc, hA2, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one, smul_neg,
        smul_smul, ← neg_smul] at h₂
      have hgt : g = ((-(2 * A.det))⁻¹ * (g * A).trace) • A := by
        have hne : -(2 * A.det) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero h2 hdet)
        rw [mul_smul, ← h₂, smul_smul, inv_mul_cancel₀ hne, one_smul]
      generalize (-(2 * A.det))⁻¹ * (g * A).trace = t at hgt
      rw [hgt, Matrix.smul_mul, Matrix.mul_smul, hA2, smul_neg, smul_neg, smul_smul,
        smul_smul] at hgg
      have ht : t = 0 := by
        have h₃ : (-((t * t * A.det) • (1 : Matrix (Fin 2) (Fin 2) F))) 0 0 = 0 :=
          congrFun (congrFun hgg 0) 0
        simp only [neg_apply, smul_apply, one_apply_eq, smul_eq_mul, mul_one,
          neg_eq_zero] at h₃
        rcases mul_eq_zero.mp h₃ with h₄ | h₄
        · exact mul_self_eq_zero.mp h₄
        · exact absurd h₄ hdet
      rw [hgt, ht, zero_smul]
    have hneg : w' = -w := by
      have h₁ : w' * w = w.det • 1 := (sub_eq_zero.mp (hg.trans hg₀)).symm
      have h₂ : w' * (w * w) = w.det • w := by
        rw [← Matrix.mul_assoc, h₁, Matrix.smul_mul, Matrix.one_mul]
      rw [hww, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one, ← smul_neg] at h₂
      exact neg_eq_iff_eq_neg.mp (smul_right_injective _ hν h₂) |>.symm ▸ rfl
    refine ⟨GeneralLinearGroup.mkOfDetNeZero A hdet, rfl, ?_⟩
    simp only [GeneralLinearGroup.val_mkOfDetNeZero]
    rw [hBX, hB'X, hneg, Matrix.mul_add, Matrix.add_mul, hXA, Matrix.neg_mul, hw₃, neg_neg]
  · exact ⟨GeneralLinearGroup.mkOfDetNeZero g hgdet, hgA, hgB⟩

/-- **Pairs of `2 × 2` matrices with the same traces and determinants are intertwined by an element
of `GL₂(F)`**, for `F` of characteristic not `2`: if `A` and `A'` have trace `0` and the same
nonzero determinant, `B` and `B'` the same trace and determinant, `AB` and `A'B'` the same trace,
and `AB - BA` is invertible, then `g A = A' g` and `g B = B' g` for some `g ∈ GL₂(F)`. This is a
form of the Skolem–Noether theorem for `M₂(F)`, proved directly. -/
lemma exists_mul_eq_mul_of_trace_det_eq (h2 : (2 : F) ≠ 0) (hA : A.trace = 0) (hA' : A'.trace = 0)
    (hdet : A.det = A'.det) (hdet₀ : A.det ≠ 0) (htrB : B.trace = B'.trace) (hdetB : B.det = B'.det)
    (htrAB : (A * B).trace = (A' * B').trace) (hκ : (A * B - B * A).det ≠ 0) :
    ∃ g : GL (Fin 2) F, g.val * A = A' * g.val ∧ g.val * B = B' * g.val := by
  rcases exists_mul_eq_companion h2 hA hdet₀ with ⟨Q, hQ⟩
  rcases exists_mul_eq_companion h2 hA' (hdet ▸ hdet₀) with ⟨Q', hQ'⟩
  rw [← hdet] at hQ'
  have hP : (Q' * Q⁻¹).val * A = A' * (Q' * Q⁻¹).val := by
    have hQQ : Q.val * (Q⁻¹).val = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hQQ' : (Q⁻¹).val * Q.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h₁ : (Q⁻¹).val * A = companionFinTwo 0 A.det * (Q⁻¹).val := by
      rw [← Matrix.mul_one ((Q⁻¹).val * A), ← hQQ, Matrix.mul_assoc, ← Matrix.mul_assoc A, hQ,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul]
    rw [Units.val_mul, Matrix.mul_assoc, h₁, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ']
  generalize Q' * Q⁻¹ = P at hP
  have hP' : A = (P⁻¹).val * (A' * P.val) := by
    rw [← hP, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have htr₁ : B.trace = ((P⁻¹).val * B' * P.val).trace := by
    rw [trace_units_conj']
    exact htrB
  have hdet₁ : B.det = ((P⁻¹).val * B' * P.val).det := by
    rw [det_units_conj']
    exact hdetB
  have htr₂ : (A * B).trace = (A * ((P⁻¹).val * B' * P.val)).trace := by
    have h₁ : A * ((P⁻¹).val * B' * P.val) = (P⁻¹).val * (A' * B') * P.val := by
      rw [hP']
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [h₁, trace_units_conj']
    exact htrAB
  rcases exists_mul_eq_mul_of_trace_eq_of_same_left h2 hA hdet₀ htr₁ hdet₁ htr₂ hκ with
    ⟨g, hg₁, hg₂⟩
  refine ⟨P * g, ?_, ?_⟩
  · rw [Units.val_mul, Matrix.mul_assoc, hg₁, ← Matrix.mul_assoc, hP, Matrix.mul_assoc]
  · rw [Units.val_mul, Matrix.mul_assoc, hg₂, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
      Matrix.mul_assoc]

end Matrix
