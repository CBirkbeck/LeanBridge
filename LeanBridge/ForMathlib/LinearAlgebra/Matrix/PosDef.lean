import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.Northcott

/-!
# Positive definiteness from finitely many integer points of bounded value

A real symmetric matrix `G` defines the quadratic form `x ↦ xᵀ G x` on `ℝ^ι`. Positivity of this
form on the nonzero integer vectors does not make `G` positive definite: the form
`(x₁ + √2 x₂) ^ 2` is positive on `ℤ ^ 2 ∖ {0}` but vanishes on a line. Finiteness does: if only
finitely many integer vectors `x` satisfy `xᵀ G x ≤ C`, for each `C`, that is, if the form is
Northcott on `ℤ^ι`, then `G` is positive definite. Conversely, the integer points of bounded value
of a positive definite quadratic form are finitely many, which Mathlib proves for integer matrices.

This is how a height pairing that is Northcott on a lattice, such as the Néron–Tate pairing on the
Mordell–Weil lattice `E(K)/E(K)_tors`, is shown to be positive definite on the real span of the
lattice.

## Main results

* `Matrix.IsSymm.posDef_of_northcott`: a real symmetric matrix whose quadratic form is Northcott on
  the integer vectors is positive definite.

## Implementation notes

If `G` is not positive definite, it has a nonzero vector `v` with `vᵀ G v < 0`, if it is not
positive semidefinite, or with `G v = 0` otherwise. In either case the form is bounded above on the
vectors within distance `1` of the line `ℝ v`, in the sup norm, and the integer vectors
`round (t v)`, for `t` real, are infinitely many of these.
-/

namespace Matrix

variable {ι : Type*} [Fintype ι] {G : Matrix ι ι ℝ} (hG : G.IsSymm) {v w : ι → ℝ}
  (hv : v ⬝ᵥ G *ᵥ v < 0 ∨ G *ᵥ v = 0) (hw : ∀ j, |w j| ≤ 1)

include hw in
private lemma abs_dotProduct_le_sum_abs (u : ι → ℝ) : |w ⬝ᵥ u| ≤ ∑ j, |u j| :=
  (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun j _ ↦ by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hw j)

include hw in
private lemma dotProduct_mulVec_le_sum_abs : w ⬝ᵥ G *ᵥ w ≤ ∑ j, ∑ k, |G j k| :=
  (le_abs_self _).trans <| (abs_dotProduct_le_sum_abs hw _).trans <| Finset.sum_le_sum fun j _ ↦ by
    simpa [mulVec, dotProduct_comm] using abs_dotProduct_le_sum_abs hw (G j)

include hG hv in
private lemma exists_dotProduct_add_smul_mulVec_le :
    ∃ C, ∀ (t : ℝ) (w : ι → ℝ), (∀ j, |w j| ≤ 1) → (w + t • v) ⬝ᵥ G *ᵥ (w + t • v) ≤ C := by
  refine ⟨∑ j, ∑ k, |G j k| + (∑ j, |(G *ᵥ v) j|) ^ 2 / -(v ⬝ᵥ G *ᵥ v), fun t w hw ↦ ?_⟩
  have h : (w + t • v) ⬝ᵥ G *ᵥ (w + t • v) = w ⬝ᵥ G *ᵥ w + (2 * t * (w ⬝ᵥ G *ᵥ v) + t ^ 2 *
      (v ⬝ᵥ G *ᵥ v)) := by
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, hG.dotProduct_mulVec_comm]
    ring1
  refine h.trans_le <| add_le_add (dotProduct_mulVec_le_sum_abs hw) ?_
  rcases hv with hv | hv
  · rw [le_div_iff₀ (neg_pos.mpr hv)]
    nlinarith [sq_nonneg (w ⬝ᵥ G *ᵥ v + t * (v ⬝ᵥ G *ᵥ v)), abs_le.mp (abs_dotProduct_le_sum_abs hw
      (G *ᵥ v))]
  · simp [hv]

include hG hv in
private lemma not_northcott (hv0 : v ≠ 0) :
    ¬Northcott fun x : ι → ℤ ↦ (Int.cast ∘ x) ⬝ᵥ G *ᵥ (Int.cast ∘ x) := by
  intro h
  rcases Function.ne_iff.mp hv0 with ⟨i, hi⟩
  rcases exists_dotProduct_add_smul_mulVec_le hG hv with ⟨C, hC⟩
  refine (h.finite_le C).not_infinite <| Set.infinite_of_injective_forall_mem
    (f := fun (n : ℕ) j ↦ round (n / v i * v j)) (fun m n hmn ↦ ?_) fun n ↦ ?_
  · simpa [div_mul_cancel₀ _ hi] using congrFun hmn i
  · rw [Set.mem_ofPred_eq, ← sub_add_cancel (Int.cast ∘ _) ((n / v i : ℝ) • v)]
    exact hC _ _ fun j ↦ by simpa [abs_sub_comm] using (abs_sub_round _).trans (by norm_num)

include hG in
/-- **A real quadratic form with finitely many integer points of bounded value is positive
definite**: if `G` is a real symmetric matrix and only finitely many integer vectors `x` satisfy
`xᵀ G x ≤ C`, for each `C`, then `G` is positive definite. -/
lemma IsSymm.posDef_of_northcott
    (h : Northcott fun x : ι → ℤ ↦ (Int.cast ∘ x) ⬝ᵥ G *ᵥ (Int.cast ∘ x)) : G.PosDef := by
  classical
  by_contra hG'
  by_cases hpsd : G.PosSemidef
  · rcases exists_mulVec_eq_zero_iff.mpr (by simpa [hpsd.posDef_iff_det_ne_zero] using hG') with
      ⟨v, hv0, hv⟩
    exact not_northcott hG (.inr hv) hv0 h
  · rcases (by simpa [posSemidef_iff_dotProduct_mulVec, hG] using hpsd : ∃ v, v ⬝ᵥ G *ᵥ v < 0) with
      ⟨v, hv⟩
    exact not_northcott hG (.inl hv) (by rintro rfl; simp at hv) h

end Matrix
