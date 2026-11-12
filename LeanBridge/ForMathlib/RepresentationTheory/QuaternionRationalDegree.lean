import LeanBridge.ForMathlib.RepresentationTheory.FaithfulDegreePositive
import LeanBridge.ForMathlib.RepresentationTheory.RationalGroup

/-!
# The rational linear degree of the quaternion group

The linear degree `lin_k(G)` of LMFDB `group.min_faithful_linear` is the least degree of a faithful
matrix representation over `k`, and the knowl notes that it may be larger than the degree of a
minimal faithful `k`-valued character. The quaternion group `Q₈` is an example for `k = ℚ`: its
two-dimensional complex representation `twoDimHom` is faithful, and its character takes rational
values (`QuaternionGroup.isRational_two`), but `Q₈` has no faithful representation of degree at most
`2` over `ℚ`. In degree `0` or `1` the image would be abelian. In degree `2` the image `A` of `a 1`
is a rational matrix with `A⁴ = 1` and `A² ≠ 1`, so `A² = -1`: the square `z = A²` satisfies
`z² = 1` and `det z = (det A)² ≥ 0`, and a `2 × 2` matrix with `z² = 1` and trace `0` has
determinant `-1`, so `z = ±1`. Then the images `A`, `B` of `a 1` and `xa 0` satisfy
`A² = B² = (AB)² = -1`, so `A`, `B` and `AB` have trace `0`, which no rational `2 × 2` matrices
satisfy (`Matrix.false_of_trace_quaternion`).

## Main results

* `QuaternionGroup.injective_twoDimHom` (LMFDB `group.min_faithful_linear`): the two-dimensional
  complex representation of `Q₈` is faithful.
* `QuaternionGroup.three_le_linearDegree_rat` (LMFDB `group.min_faithful_linear`): `Q₈` has no
  faithful representation of degree at most `2` over `ℚ`, so `lin_ℚ(Q₈) ≥ 3`.
-/

open Matrix

namespace Matrix

variable {M A : Matrix (Fin 2) (Fin 2) ℚ}

lemma trace_eq_zero_of_mul_self_eq_neg_one (h : M * M = -1) : M.trace = 0 := by
  have h00 : (M * M) 0 0 = (-1 : Matrix (Fin 2) (Fin 2) ℚ) 0 0 := congrFun (congrFun h 0) 0
  have h01 : (M * M) 0 1 = (-1 : Matrix (Fin 2) (Fin 2) ℚ) 0 1 := congrFun (congrFun h 0) 1
  simp [mul_apply] at h00 h01
  rw [trace_fin_two]
  by_contra hs
  have hb : M 0 1 = 0 :=
    (mul_eq_zero.mp (by linear_combination h01 : M 0 1 * (M 0 0 + M 1 1) = 0)).resolve_right hs
  rw [hb] at h00
  nlinarith [sq_nonneg (M 0 0)]

lemma sq_eq_neg_one_of_pow_four_eq_one (h4 : A ^ 4 = 1) (h2 : A ^ 2 ≠ 1) : A ^ 2 = -1 := by
  have hzz : A ^ 2 * A ^ 2 = 1 := by
    rw [← pow_add]
    exact h4
  have hdet : 0 ≤ (A ^ 2).det := by
    rw [det_pow]
    exact sq_nonneg _
  have e00 : (A ^ 2 * A ^ 2) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℚ) 0 0 :=
    congrFun (congrFun hzz 0) 0
  have e01 : (A ^ 2 * A ^ 2) 0 1 = (1 : Matrix (Fin 2) (Fin 2) ℚ) 0 1 :=
    congrFun (congrFun hzz 0) 1
  have e10 : (A ^ 2 * A ^ 2) 1 0 = (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 0 :=
    congrFun (congrFun hzz 1) 0
  have e11 : (A ^ 2 * A ^ 2) 1 1 = (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 1 :=
    congrFun (congrFun hzz 1) 1
  simp only [mul_apply, Fin.sum_univ_two, one_apply_eq, one_apply_ne zero_ne_one,
    one_apply_ne one_ne_zero] at e00 e01 e10 e11
  rw [det_fin_two] at hdet
  have hs : (A ^ 2) 0 0 + (A ^ 2) 1 1 ≠ 0 := fun hs ↦ by
    nlinarith
  have hq : (A ^ 2) 0 1 = 0 := (mul_eq_zero.mp (by linear_combination e01 :
    (A ^ 2) 0 1 * ((A ^ 2) 0 0 + (A ^ 2) 1 1) = 0)).resolve_right hs
  have hr : (A ^ 2) 1 0 = 0 := (mul_eq_zero.mp (by linear_combination e10 :
    (A ^ 2) 1 0 * ((A ^ 2) 0 0 + (A ^ 2) 1 1) = 0)).resolve_right hs
  simp only [hq, zero_mul, mul_zero, add_zero] at e00 e11
  have hd : (A ^ 2) 0 0 = (A ^ 2) 1 1 := by
    have h' : ((A ^ 2) 0 0 - (A ^ 2) 1 1) * ((A ^ 2) 0 0 + (A ^ 2) 1 1) = 0 := by
      linear_combination e00 - e11
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hs)
  rcases mul_self_eq_one_iff.mp e00 with h1 | h1
  · exact absurd (by ext i j; fin_cases i <;> fin_cases j <;> simp [h1, ← hd, hq, hr]) h2
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, ← hd, hq, hr]

end Matrix

namespace QuaternionGroup

lemma not_injective_rat_two (ρ : QuaternionGroup 2 →* GL (Fin 2) ℚ) : ¬Function.Injective ρ := by
  intro hρ
  have hval (g h : QuaternionGroup 2) : (ρ g : Matrix (Fin 2) (Fin 2) ℚ) * ρ h = ρ (g * h) := by
    rw [map_mul, Units.val_mul]
  have h4 : (ρ (a 1) : Matrix (Fin 2) (Fin 2) ℚ) ^ 4 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, show (a 1 : QuaternionGroup 2) ^ 4 = 1 by decide,
      map_one, Units.val_one]
  have h2 : (ρ (a 1) : Matrix (Fin 2) (Fin 2) ℚ) ^ 2 ≠ 1 := fun h ↦
    (by decide : (a 1 : QuaternionGroup 2) ^ 2 ≠ 1) <| hρ <| Units.ext <| by
      rw [map_pow, Units.val_pow_eq_pow_val, h, map_one, Units.val_one]
  have hA : (ρ (a 1) : Matrix (Fin 2) (Fin 2) ℚ) ^ 2 = -1 :=
    sq_eq_neg_one_of_pow_four_eq_one h4 h2
  rw [pow_two, hval] at hA
  have hB : (ρ (xa 0) : Matrix (Fin 2) (Fin 2) ℚ) * ρ (xa 0) = -1 := by
    rw [hval, show (xa 0 * xa 0 : QuaternionGroup 2) = a 1 * a 1 by decide, hA]
  have hAB : (ρ (a 1) : Matrix (Fin 2) (Fin 2) ℚ) * ρ (xa 0) * (ρ (a 1) * ρ (xa 0)) = -1 := by
    rw [hval, hval, show (a 1 * xa 0 * (a 1 * xa 0) : QuaternionGroup 2) = a 1 * a 1 by
      decide, hA]
  have htr : (-1 : Matrix (Fin 2) (Fin 2) ℚ).trace = -2 := by
    rw [trace_neg, trace_one, Fintype.card_fin]
    norm_num
  rw [← hval] at hA
  exact false_of_trace_quaternion (trace_eq_zero_of_mul_self_eq_neg_one hA)
    (trace_eq_zero_of_mul_self_eq_neg_one hB) (hA ▸ htr) (hB ▸ htr)
    (trace_eq_zero_of_mul_self_eq_neg_one hAB)

lemma not_injective_rat_of_lt_three {n : ℕ} (hn : n < 3) (ρ : QuaternionGroup 2 →* GL (Fin n) ℚ) :
    ¬Function.Injective ρ := fun hρ ↦ by
  interval_cases n
  · exact (by decide : (a 1 : QuaternionGroup 2) ≠ 1) (hρ (Units.ext (Subsingleton.elim _ _)))
  · refine (by decide : (a 1 * xa 0 : QuaternionGroup 2) ≠ xa 0 * a 1) (hρ (Units.ext ?_))
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
    ext i j
    fin_cases i
    fin_cases j
    simp [mul_apply, mul_comm]
  · exact not_injective_rat_two ρ hρ

/-- **`lin_ℚ(Q₈) ≥ 3`** (LMFDB `group.min_faithful_linear`): the quaternion group has no faithful
representation of degree at most `2` over `ℚ`. In degree `2`, the images `A`, `B` of `a 1` and
`xa 0` would satisfy `A² = B² = (AB)² = -1`, as a rational `2 × 2` matrix of order `4` squares to
`± 1`; these traces are impossible over `ℚ`. -/
lemma three_le_linearDegree_rat : 3 ≤ linearDegree ℚ (QuaternionGroup 2) :=
  le_csInf ⟨_, _, toHomUnits_permMatrixHom_comp_injective ℚ (QuaternionGroup 2)⟩ fun n ⟨ρ, hρ⟩ ↦ by
    by_contra hn
    exact not_injective_rat_of_lt_three (by omega) ρ hρ

/-- **The two-dimensional complex representation of `Q₈` is faithful** (LMFDB
`group.min_faithful_linear`): `twoDimHom (a 2) = diag(-1, -1) ≠ 1`, and every element `g ≠ 1` of
`Q₈` has `g = a 2` or `g² = a 2`. -/
lemma injective_twoDimHom : Function.Injective twoDimHom := by
  have h2 : twoDimHom (a 2) ≠ 1 := fun h ↦ by
    have h' :
        (twoDimHom (a 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 :=
      congrArg (fun M : GL (Fin 2) ℂ ↦ (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
    rw [show (a 2 : QuaternionGroup 2) = a 1 ^ 2 by decide, map_pow, twoDimHom_a_one] at h'
    norm_num [matrixI, pow_two] at h'
  rw [injective_iff_map_eq_one]
  intro g hg
  rcases (by decide : ∀ g : QuaternionGroup 2, g = 1 ∨ g = a 2 ∨ g ^ 2 = a 2) g with
    h | rfl | h
  · exact h
  · exact absurd hg h2
  · exact absurd (by rw [← h, map_pow, hg, one_pow]) h2

end QuaternionGroup
