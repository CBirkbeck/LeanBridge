import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Arithmetic lattices

A lattice in a real inner product space is arithmetic if it is similar to an integral lattice.
Scaling a lattice by `α ≠ 0` multiplies its inner products by `α²`, and an isometry preserves them,
so `L` is arithmetic exactly when `c ⟪x, y⟫ ∈ ℤ` for all `x, y ∈ L` and some real `c > 0`. That
perfect and strongly eutactic lattices are arithmetic is not formalised.

## Main definitions

* `ZLattice.IsArithmetic` (LMFDB `lattice.arithmetic`).
-/

open scoped InnerProductSpace

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : Submodule ℤ E)

/-- A lattice `L` in a real inner product space is **arithmetic** (LMFDB `lattice.arithmetic`) if it
is similar (LMFDB `lattice.similarity`) to an integral lattice (LMFDB `lattice.definition`): the
inner products of the vectors of `L`, multiplied by some real `c > 0` (the square of the scaling
factor of the similarity), are integers. -/
def IsArithmetic : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x ∈ L, ∀ y ∈ L, ∃ n : ℤ, c * ⟪x, y⟫_ℝ = n

variable {L}

lemma IsArithmetic.smul (h : IsArithmetic L) {a : ℝ} (ha : a ≠ 0) :
    IsArithmetic (L.map (LinearMap.lsmul ℝ E a |>.restrictScalars ℤ)) := by
  rcases h with ⟨c, hc, h⟩
  refine ⟨c / a ^ 2, div_pos hc (sq_pos_of_ne_zero ha), ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rcases h x hx y hy with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real, ← hn]
  field_simp

end ZLattice
