import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The lower unipotent matrices of `SL(2, ℤ)`

The matrices `!![1, 0; c, 1]` of `SL(2, ℤ)`, which occur in the traces between levels of modular
forms, and which multiply by adding the entries `c`.

## Main definitions

* `Matrix.SpecialLinearGroup.lowerUnipotent`: the matrix `!![1, 0; c, 1]`.
-/

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

variable (c d : ℤ)

/-- The **lower unipotent matrix** `!![1, 0; c, 1]` of `SL(2, ℤ)`. -/
def lowerUnipotent : SL(2, ℤ) :=
  ⟨!![1, 0; c, 1], by simp⟩

lemma coe_lowerUnipotent : (lowerUnipotent c : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; c, 1] :=
  rfl

lemma lowerUnipotent_add : lowerUnipotent (c + d) = lowerUnipotent c * lowerUnipotent d := by
  ext i j
  rw [coe_mul, coe_lowerUnipotent, coe_lowerUnipotent, coe_lowerUnipotent]
  fin_cases i <;> fin_cases j <;> simp

end Matrix.SpecialLinearGroup
