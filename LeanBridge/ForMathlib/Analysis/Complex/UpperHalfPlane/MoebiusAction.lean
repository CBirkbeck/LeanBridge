import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups

/-!
# The automorphy factor is a cocycle on subgroups of `SL(2, ℝ)`

For `g, h ∈ GL(2, ℝ)`, Mathlib's `UpperHalfPlane.denom_cocycle_σ` says
`j(gh, z) = σ_h(j(g, hz)) j(h, z)`, with `j(g, z) = cz + d` and `σ_h` the identity when `det h > 0`
and complex conjugation otherwise. On a subgroup `Γ` of `GL(2, ℝ)` whose elements have determinant
`1`, such as the image of `SL(2, ℤ)`, `σ` is the identity and `j` is a cocycle:
`j(γδ, z) = j(γ, δz) j(δ, z)`.
-/

open scoped MatrixGroups

namespace UpperHalfPlane

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] (z : ℍ)

lemma denom_coe_mul (γ δ : Γ) :
    denom ↑(γ * δ) z = denom γ ↑((δ : GL (Fin 2) ℝ) • z) * denom δ z := by
  rw [Subgroup.coe_mul, denom_cocycle_σ]
  simp [σ, Subgroup.HasDetOne.det_eq δ.2]

lemma denom_mul_SL (A B : SL(2, ℤ)) :
    denom (A * B : SL(2, ℤ)) z = denom A ↑(B • z) * denom B z := by
  rw [map_mul, map_mul]
  exact denom_coe_mul (Γ := 𝒮ℒ) z ⟨_, A, rfl⟩ ⟨_, B, rfl⟩

end UpperHalfPlane
