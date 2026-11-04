import Mathlib.Data.Matrix.Block

/-!
# The blocks of a product of block matrices

For matrices `M` and `N` indexed by sums, the blocks of the product `M N` are given by block
multiplication: its upper left block is `M₁₁ N₁₁ + M₁₂ N₂₁`, its lower left block is
`M₂₁ N₁₁ + M₂₂ N₂₁` and its lower right block is `M₂₁ N₁₂ + M₂₂ N₂₂`.
-/

namespace Matrix

variable {l m n o p q α : Type*} [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α]
  (M : Matrix (n ⊕ o) (l ⊕ m) α) (N : Matrix (l ⊕ m) (p ⊕ q) α)

lemma toBlocks₁₁_mul :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁ := by
  ext i k
  simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, mul_apply]

lemma toBlocks₂₁_mul :
    (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ := by
  ext i k
  simp [toBlocks₂₁, toBlocks₁₁, toBlocks₂₂, mul_apply]

lemma toBlocks₂₂_mul :
    (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  ext i k
  simp [toBlocks₂₂, toBlocks₂₁, toBlocks₁₂, mul_apply]

end Matrix
