import LeanBridge.ForMathlib.Algebra.Module.ZLattice.MinimalVectors
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Perfect lattices

A lattice `L` in `ℝⁿ` is perfect if the matrices `x xᵀ`, for the minimal vectors `x` of `L`, span
the space of real symmetric `n × n` matrices. That perfect lattices are arithmetic and determined
by their minimal vectors, and that there are finitely many similarity classes of perfect lattices
in each dimension (Voronoi), are not formalised.

## Main definitions

* `ZLattice.IsPerfect` (LMFDB `lattice.perfect`).

## Main results

* `ZLattice.IsPerfect.span_minimalVectors`: a perfect lattice is well-rounded: its minimal vectors
  span `ℝⁿ`.
-/

open Matrix
open scoped InnerProductSpace

namespace ZLattice

variable {ι : Type*} [Fintype ι] {L : Submodule ℤ (EuclideanSpace ℝ ι)}

variable (L) in
/-- A lattice `L` in `ℝⁿ = EuclideanSpace ℝ ι` is **perfect** (LMFDB `lattice.perfect`) if every
real symmetric matrix indexed by `ι` is a real linear combination of the matrices `x xᵀ`, where `x`
ranges over the minimal vectors of `L` (`ZLattice.minimalVectors`); the matrices `x xᵀ` are
symmetric, so they then span the space of symmetric matrices. -/
def IsPerfect : Prop :=
  ∀ A : Matrix ι ι ℝ, A.IsSymm → A ∈ Submodule.span ℝ
    ((fun x : EuclideanSpace ℝ ι ↦ vecMulVec x.ofLp x.ofLp) '' minimalVectors L)

/-- **A perfect lattice is well-rounded** (LMFDB `lattice.well_rounded`): its minimal vectors span
`ℝⁿ`. -/
lemma IsPerfect.span_minimalVectors [DecidableEq ι] (h : IsPerfect L) :
    Submodule.span ℝ (minimalVectors L) = ⊤ := by
  refine Submodule.orthogonal_eq_bot_iff.mp <| (Submodule.eq_bot_iff _).mpr fun v hv ↦ ?_
  have h1 : v.ofLp ⬝ᵥ ((1 : Matrix ι ι ℝ) *ᵥ v.ofLp) = 0 := by
    refine Submodule.span_induction ?_ (by simp) (fun A B _ _ hA hB ↦ ?_) (fun c A _ hA ↦ ?_)
      (h 1 isSymm_one)
    · rintro _ ⟨x, hx, rfl⟩
      have hvx : ⟪x, v⟫_ℝ = 0 :=
        Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span hx) hv
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at hvx
      simp [vecMulVec_mulVec, hvx]
    · rw [add_mulVec, dotProduct_add, hA, hB, add_zero]
    · rw [smul_mulVec, dotProduct_smul, hA, smul_zero]
  rw [one_mulVec, dotProduct_self_eq_zero] at h1
  exact WithLp.ofLp_injective 2 h1

end ZLattice
