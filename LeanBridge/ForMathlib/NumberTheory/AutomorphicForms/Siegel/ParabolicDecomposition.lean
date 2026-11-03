import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.Gamma0Generators
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.Level

/-!
# `Sp(4, ℚ) = Sp(4, ℤ) P(ℚ)`

Every `γ ∈ Sp(4, ℚ)` is the product `gp` of an integral symplectic matrix `g ∈ Sp(4, ℤ)` and an
element `p` of the Siegel parabolic subgroup `P(ℚ) = {(A, B; 0, D)}`: the Siegel modular group has
a single class of rational Lagrangian subspaces (one `0`-dimensional cusp). The lower left block of
`g⁻¹γ` is cleared column by column by left multiplication with integral matrices: the embeddings
of `SL(2, ℤ)` on the two coordinates (`SymplecticGroup.embedFirst`, `SymplecticGroup.embedSecond`)
and the rotations `(U, 0; 0, U⁻ᵀ)`, `U ∈ SL(2, ℤ)`, each chosen with a bottom row `(c, d)` such
that `cx + dy = 0` for the two rational entries `x, y` to combine. The first column becomes
`(x, 0, 0, 0)`, the symplectic relations then force the entry `(3, 2)` to vanish, and one more
embedding of `SL(2, ℤ)` on the second coordinate clears the entry `(4, 2)`.

## Main results

* `SymplecticGroup.exists_mem_integral_inv_mul_mem_siegelParabolic`: `Sp(4, ℚ) = Sp(4, ℤ) P(ℚ)`.
-/

open Matrix

open scoped MatrixGroups

namespace SymplecticGroup

lemma exists_SL2Z_eq_gcd (a b : ℤ) :
    ∃ M : SL(2, ℤ), M 0 0 * a + M 0 1 * b = a.gcd b ∧ M 1 0 * a + M 1 1 * b = 0 := by
  rcases eq_or_ne (a.gcd b) 0 with h | h
  · refine ⟨1, ?_, ?_⟩ <;> simp [Int.gcd_eq_zero_iff.mp h]
  have hg : (a.gcd b : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr h
  rcases Int.gcd_dvd_left a b with ⟨a', ha'⟩
  rcases Int.gcd_dvd_right a b with ⟨b', hb'⟩
  have hab : (a.gcd b : ℤ) = a * a.gcdA b + b * a.gcdB b := Int.gcd_eq_gcd_ab a b
  have hdet : a.gcdA b * a' + a.gcdB b * b' = 1 :=
    mul_left_cancel₀ hg <| by
      linear_combination -a.gcdA b * ha' - a.gcdB b * hb' - hab
  refine ⟨⟨!![a.gcdA b, a.gcdB b; -b', a'], by
    rw [det_fin_two_of]
    linear_combination hdet⟩, ?_, ?_⟩
  · simp only [of_apply, cons_val_zero, cons_val_one]
    linear_combination -hab
  · simp only [of_apply, cons_val_zero, cons_val_one]
    linear_combination -b' * ha' + a' * hb'

lemma exists_SL2Z (x y : ℚ) : ∃ M : SL(2, ℤ), (M 1 0 : ℚ) * x + (M 1 1 : ℚ) * y = 0 := by
  rcases exists_SL2Z_eq_gcd (x.num * y.den) (y.num * x.den) with ⟨M, -, hM⟩
  refine ⟨M, ?_⟩
  have h : ((M 1 0 : ℚ) * x + (M 1 1 : ℚ) * y) * (x.den * y.den) =
      ((M 1 0 * (x.num * y.den) + M 1 1 * (y.num * x.den) : ℤ) : ℚ) := by
    push_cast
    rw [← Rat.mul_den_eq_num x, ← Rat.mul_den_eq_num y]
    ring1
  rw [hM, Int.cast_zero] at h
  exact (mul_eq_zero.mp h).resolve_right (by positivity)

variable (M : SL(2, ℤ)) {γ : symplecticGroup (Fin 2) ℚ}

private lemma embedFirst_map_mem : embedFirst (M.map (Int.castRingHom ℚ)) ∈ integral (Fin 2) := by
  have h : embedFirst (M.map (Int.castRingHom ℚ)) = map (Int.castRingHom ℚ) (embedFirst M) :=
    Subtype.ext <| by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [embedFirst]
  rw [h]
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top _)

private lemma embedSecond_map_mem : embedSecond (M.map (Int.castRingHom ℚ)) ∈ integral (Fin 2) := by
  have h : embedSecond (M.map (Int.castRingHom ℚ)) = map (Int.castRingHom ℚ) (embedSecond M) :=
    Subtype.ext <| by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [embedSecond]
  rw [h]
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top _)

private lemma rotation_map_mem : rotation (M.map (Int.castRingHom ℚ)) ∈ integral (Fin 2) := by
  have h : rotation (M.map (Int.castRingHom ℚ)) = map (Int.castRingHom ℚ) (rotation M) :=
    Subtype.ext <| by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [rotation]
  rw [h]
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top _)

variable (γ) in
private lemma exists_mul_apply_inr_zero :
    ∃ h ∈ integral (Fin 2), (h * γ).1 (.inr 0) (.inl 0) = 0 := by
  rcases exists_SL2Z (γ.1 (.inl 0) (.inl 0)) (γ.1 (.inr 0) (.inl 0)) with ⟨M₁, hM₁⟩
  refine ⟨embedFirst (M₁.map (Int.castRingHom ℚ)), embedFirst_map_mem M₁, ?_⟩
  rw [embedFirst_mul_apply_inr_zero]
  simpa using hM₁

private lemma exists_mul_apply_inr_one (h₀ : γ.1 (.inr 0) (.inl 0) = 0) :
    ∃ h ∈ integral (Fin 2), (h * γ).1 (.inr 0) (.inl 0) = 0 ∧ (h * γ).1 (.inr 1) (.inl 0) = 0 := by
  rcases exists_SL2Z (γ.1 (.inl 1) (.inl 0)) (γ.1 (.inr 1) (.inl 0)) with ⟨M₂, hM₂⟩
  refine ⟨embedSecond (M₂.map (Int.castRingHom ℚ)), embedSecond_map_mem M₂, ?_, ?_⟩
  · rw [embedSecond_mul_apply_inr_zero, h₀]
  · rw [embedSecond_mul_apply_inr_one]
    simpa using hM₂

private lemma exists_mul_apply_inl_one (h₀ : γ.1 (.inr 0) (.inl 0) = 0)
    (h₁ : γ.1 (.inr 1) (.inl 0) = 0) : ∃ h ∈ integral (Fin 2), (h * γ).1 (.inr 0) (.inl 0) = 0 ∧
      (h * γ).1 (.inr 1) (.inl 0) = 0 ∧ (h * γ).1 (.inl 1) (.inl 0) = 0 := by
  rcases exists_SL2Z (γ.1 (.inl 0) (.inl 0)) (γ.1 (.inl 1) (.inl 0)) with ⟨U, hU⟩
  refine ⟨rotation (U.map (Int.castRingHom ℚ)), rotation_map_mem U,
    rotation_mul_apply_inr_of_eq_zero _ _ _ h₀ h₁, rotation_mul_apply_inr_of_eq_zero _ _ _ h₀ h₁,
    ?_⟩
  rw [rotation_mul_apply_inl]
  simpa using hU

private lemma exists_mul_mem_siegelParabolic (h₀ : γ.1 (.inr 0) (.inl 0) = 0)
    (h₁ : γ.1 (.inr 1) (.inl 0) = 0) (h₂ : γ.1 (.inl 1) (.inl 0) = 0) :
    ∃ h ∈ integral (Fin 2), h * γ ∈ siegelParabolic (Fin 2) ℚ := by
  have hx : γ.1 (.inl 0) (.inl 0) * γ.1 (.inr 0) (.inr 0) = 1 := by
    simpa [h₀, h₁, h₂] using mul_apply_inr_inr_zero_zero γ
  have hc : γ.1 (.inr 0) (.inl 1) = 0 := by
    simpa [h₀, h₁, h₂, left_ne_zero_of_mul_eq_one hx] using mul_apply_inr_inl_one_eq γ
  rcases exists_SL2Z (γ.1 (.inl 1) (.inl 1)) (γ.1 (.inr 1) (.inl 1)) with ⟨M₃, hM₃⟩
  refine ⟨embedSecond (M₃.map (Int.castRingHom ℚ)), embedSecond_map_mem M₃, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [toBlocks₂₁] using (embedSecond_mul_apply_inr_zero _ γ _).trans h₀
  · simpa [toBlocks₂₁] using (embedSecond_mul_apply_inr_zero _ γ _).trans hc
  · simpa [toBlocks₂₁] using (embedSecond_mul_apply_inr_one _ γ _).trans <| by
      rw [h₂, h₁, mul_zero, mul_zero, add_zero]
  · simpa [toBlocks₂₁] using (embedSecond_mul_apply_inr_one _ γ _).trans <| by
      simpa using hM₃

variable (γ) in
/-- **`Sp(4, ℚ) = Sp(4, ℤ) P(ℚ)`**: every `γ ∈ Sp(4, ℚ)` is `gp` with `g ∈ Sp(4, ℤ)` and `p` in the
Siegel parabolic subgroup `{(A, B; 0, D)}` of `Sp(4, ℚ)`. The lower left block of `g⁻¹γ` is
cleared by left multiplication with the images of `SL(2, ℤ)` in `Sp(4, ℤ)`. -/
lemma exists_mem_integral_inv_mul_mem_siegelParabolic :
    ∃ g ∈ integral (Fin 2), g⁻¹ * γ ∈ siegelParabolic (Fin 2) ℚ := by
  rcases exists_mul_apply_inr_zero γ with ⟨h₁, hh₁, e₁⟩
  rcases exists_mul_apply_inr_one e₁ with ⟨h₂, hh₂, e₂, e₂'⟩
  rcases exists_mul_apply_inl_one e₂ e₂' with ⟨h₃, hh₃, e₃, e₃', e₃''⟩
  rcases exists_mul_mem_siegelParabolic e₃ e₃' e₃'' with ⟨h₄, hh₄, hp⟩
  refine ⟨(h₄ * (h₃ * (h₂ * h₁)))⁻¹, inv_mem (mul_mem hh₄ (mul_mem hh₃ (mul_mem hh₂ hh₁))), ?_⟩
  simpa [mul_assoc] using hp

end SymplecticGroup
