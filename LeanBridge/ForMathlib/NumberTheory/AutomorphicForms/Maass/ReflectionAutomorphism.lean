import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.UpperHalfPlane
import LeanBridge.ForMathlib.NumberTheory.ModularForms.LowerUnipotent
import TauCeti.NumberTheory.ModularForms.Conjugate

/-!
# The reflection `z ↦ -z̄` gives an outer automorphism of the modular group

The reflection `z ↦ -z̄` of `ℍ` in the imaginary axis is the action of the matrix
`J = diag(-1, 1)` (`UpperHalfPlane.maassReflection`), which comes from `GL(2, ℤ)`. Conjugation by
`J` negates the off-diagonal entries of a matrix: it is Tau Ceti's automorphism
`Matrix.SpecialLinearGroup.conjJMulAut` of the modular group `SL(2, ℤ)`, of square `1`, and
`J γ J⁻¹` acts on `ℍ` by `z ↦ -conj (γ (-z̄))`. It is not the identity, so it has order two, and it
is outer: no `g ∈ SL(2, ℤ)` has `J γ J⁻¹ = ±g γ g⁻¹` for all `γ` in a congruence subgroup. Indeed
a congruence subgroup contains `(1, N; 0, 1)` and `(1, 0; N, 1)` for some `N ≥ 1`; the equalities
with the sign `+` for both force `g = diag(a, -a)`, of determinant `-a² ≠ 1`, and the equality with
the sign `-` for one of them forces `det g = 0`. So conjugation by `J` gives an outer automorphism
of order two of `SL(2, ℤ)` and of every congruence subgroup that `J` normalises, such as `Γ₀(N)`,
`Γ₁(N)` and `Γ(N)`, and, as the equality fails up to sign too, of their images in `PSL(2, ℤ)`. The
LMFDB says so of every congruence subgroup, but conjugation by `J` does not map every congruence
subgroup to itself.

## Main results

* `UpperHalfPlane.maassReflection_mem_range`: `diag(-1, 1)` comes from `GL(2, ℤ)`.
* `UpperHalfPlane.conjJ_smul` (LMFDB `mf.maass.mwf.symmetry`): `J γ J⁻¹` acts on `ℍ` by
  `z ↦ -conj (γ (-z̄))`.
* `Matrix.SpecialLinearGroup.conjJMulAut_ne_one`: conjugation by `J` is not the identity.
* `Matrix.SpecialLinearGroup.exists_conjJ_ne` (LMFDB `mf.maass.mwf.symmetry`): on a congruence
  subgroup, conjugation by `J` is not conjugation by an element of `SL(2, ℤ)`, not even up to
  sign.
* `Matrix.SpecialLinearGroup.conjJMulAut_ne_conj` (LMFDB `mf.maass.mwf.symmetry`): conjugation by
  `J` is an outer automorphism of `SL(2, ℤ)`.
-/

open Matrix CongruenceSubgroup

open scoped MatrixGroups

namespace UpperHalfPlane

lemma maassReflection_eq_J : maassReflection = J :=
  rfl

/-- **The reflection `diag(-1, 1)` comes from `GL(2, ℤ)`**: it is the image of an integral matrix
of determinant `-1`. -/
lemma maassReflection_mem_range :
    maassReflection ∈ (GeneralLinearGroup.map (Int.castRingHom ℝ)).range := by
  have h : !![-1, 0; 0, 1] * !![-1, 0; 0, 1] = (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    simp [one_fin_two]
  refine ⟨⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], h, h⟩, Units.ext ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [maassReflection]

/-- **Conjugation by the reflection is `conjJ`** (LMFDB `mf.maass.mwf.symmetry`): for
`γ ∈ SL(2, ℤ)`, `conjJ γ = J γ J⁻¹` acts on `ℍ` by `z ↦ -conj (γ (-z̄))`, where `J = diag(-1, 1)`
acts by `z ↦ -z̄`. -/
lemma conjJ_smul (γ : SL(2, ℤ)) (z : ℍ) :
    γ.conjJ • z = maassReflection • γ • maassReflection • z := by
  rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def, maassReflection_eq_J, ← mul_smul,
    ← mul_smul, SpecialLinearGroup.J_mul_mapGL_mul_J]

end UpperHalfPlane

namespace Matrix.SpecialLinearGroup

/-- **Conjugation by `J` is not the identity** of `SL(2, ℤ)`, so the involution `conjJMulAut` has
order two. -/
lemma conjJMulAut_ne_one : (conjJMulAut : MulAut SL(2, ℤ)) ≠ 1 := fun h ↦ by
  simpa using congrFun₂ (congrArg ((↑) : SL(2, ℤ) → Matrix (Fin 2) (Fin 2) ℤ)
    (DFunLike.congr_fun h ModularGroup.T)) 0 1

lemma conjJ_mem_Gamma {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma N) : γ.conjJ ∈ Gamma N := by
  simpa using hγ

/-- **Conjugation by `J` is outer on every congruence subgroup** (LMFDB `mf.maass.mwf.symmetry`):
for a congruence subgroup `Γ` of `SL(2, ℤ)` and `g ∈ SL(2, ℤ)`, some `γ ∈ Γ` has
`conjJ γ ≠ ±g γ g⁻¹`. So on a congruence subgroup that `J` normalises, such as `Γ₀(N)`, `Γ₁(N)`
and `Γ(N)`, and on its image in `PSL(2, ℤ)`, conjugation by `J` is an automorphism that is not
inner. -/
lemma exists_conjJ_ne {Γ : Subgroup SL(2, ℤ)} (hΓ : IsCongruenceSubgroup Γ) (g : SL(2, ℤ)) :
    ∃ γ ∈ Γ, γ.conjJ ≠ g * γ * g⁻¹ ∧ γ.conjJ ≠ -(g * γ * g⁻¹) := by
  rcases hΓ with ⟨N, hN, hΓN⟩
  have hN' : (N : ℤ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hN
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    rw [← det_fin_two]
    exact g.det_coe
  have hu : ModularGroup.T ^ (N : ℤ) ∈ Γ := hΓN <| Gamma_mem.mpr <| by
    simp only [ModularGroup.coe_T_zpow]
    simp
  have hl : lowerUnipotent N ∈ Γ := hΓN <| Gamma_mem.mpr <| by simp [coe_lowerUnipotent]
  by_contra h
  push Not at h
  have key (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) : (γ.conjJ : Matrix (Fin 2) (Fin 2) ℤ) * g = g * γ ∨
      (γ.conjJ : Matrix (Fin 2) (Fin 2) ℤ) * g = -(g * γ) := by
    by_cases h₁ : γ.conjJ = g * γ * g⁻¹
    · refine .inl ?_
      rw [← coe_mul, ← coe_mul, h₁, inv_mul_cancel_right]
    · refine .inr ?_
      rw [← coe_mul, ← coe_mul, ← coe_neg, h γ hγ h₁, neg_mul, inv_mul_cancel_right]
  rcases key _ hu with hu' | hu' <;>
    rw [coe_conjJ, ModularGroup.coe_T_zpow, eta_fin_two (g : Matrix (Fin 2) (Fin 2) ℤ)] at hu' <;>
    simp [hN] at hu'
  · rcases key _ hl with hl' | hl' <;>
      rw [coe_conjJ, coe_lowerUnipotent, eta_fin_two (g : Matrix (Fin 2) (Fin 2) ℤ)] at hl' <;>
      simp [hN] at hl'
    · rcases hu' with ⟨⟨hc, e⟩, -⟩
      rcases hl' with ⟨hb, -, -⟩
      have hd : g 1 1 = -g 0 0 :=
        mul_left_cancel₀ hN' <| by linear_combination -e
      rw [hb, hc, hd] at hdet
      nlinarith [sq_nonneg (g 0 0)]
    · rcases hl' with ⟨⟨e₁, e₂⟩, -, e₃⟩
      have hb : g 0 1 = 0 := by
        linarith
      rw [hb] at e₁ e₃ hdet
      nlinarith
  · rcases hu' with ⟨⟨e₁, -⟩, e₂, e₃⟩
    have hc : g 1 0 = 0 := by
      linarith
    rw [hc] at e₁ e₃ hdet
    nlinarith

/-- **Conjugation by `J` is an outer automorphism of the modular group** `SL(2, ℤ)` (LMFDB
`mf.maass.mwf.symmetry`): it is not conjugation by an element. -/
lemma conjJMulAut_ne_conj (g : SL(2, ℤ)) : (conjJMulAut : MulAut SL(2, ℤ)) ≠ MulAut.conj g :=
  fun h ↦ by
    rcases exists_conjJ_ne ⟨1, one_ne_zero, le_top⟩ g with ⟨γ, -, hγ, -⟩
    exact hγ <| by simpa using DFunLike.congr_fun h γ

end Matrix.SpecialLinearGroup
