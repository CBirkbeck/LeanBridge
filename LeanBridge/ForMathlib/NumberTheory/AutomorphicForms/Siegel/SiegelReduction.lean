import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.FourierLevi
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SiegelEisensteinConvergence
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SiegelFundamentalDomain
import Mathlib.NumberTheory.Modular
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# Siegel's reduction theory in degree 2

Every point of the Siegel upper half-space `ℋ₂` is equivalent under `Sp(4, ℤ)` to a point
`Z = X + iY` of the **Siegel set**: `|x_ij| ≤ 1/2`, `2 |y₀₁| ≤ y₀₀ ≤ y₁₁` and `y₀₀ ≥ √3 / 2`. This
is Siegel's reduction, in the form needed to integrate over a fundamental domain.

The proof has three steps. The Plücker comparison `‖p(C, D)‖ ≤ K(Z) |det(CZ + D)|`
(`SiegelUpperHalfSpace.norm_siegelPlucker_le`) leaves finitely many values of `|det(CZ + D)|` below
any bound, so there is a `δ` minimising it, that is maximising `det Im(δZ)`, and then
`|det(CZ' + D)| ≥ 1` for all `(C, D)` at `Z' = δZ`. An element `U` of `GL(2, ℤ)` reduces
`Y' = Im Z'` to `2 |y₀₁| ≤ y₀₀ ≤ y₁₁`, by Gauss's reduction of binary quadratic forms, which is the
reduction of the point `(y₀₁ + i √det Y') / y₀₀` of the upper half-plane under `SL(2, ℤ)`, and an
integral translation reduces `X'`. These do not change `|det(CZ + D)|`, and at the last point the
partial inversion, for which `det(CZ + D) = z₀₀`, gives `|z₀₀| ≥ 1`, so `y₀₀ ≥ √3 / 2`.

## Main definitions

* `SymplecticGroup.symTranslation`: the translation `(1, S; 0, 1)` by a symmetric matrix.
* `SiegelUpperHalfSpace.siegelSet`: the Siegel set of `ℋ₂`.

## Main results

* `SiegelUpperHalfSpace.val_smul_levi`: `(U, 0; 0, U⁻ᵀ)` acts by `Z ↦ U Z Uᵀ`.
* `SiegelUpperHalfSpace.exists_forall_norm_det_denom_le`: there is a `δ ∈ Sp(4, ℤ)` minimising
  `|det(CZ + D)|`.
* `SiegelUpperHalfSpace.exists_levi_reduced`: Gauss's reduction of `Im Z` under `GL(2, ℤ)`.
* `SiegelUpperHalfSpace.exists_smul_mem_siegelSet`: Siegel's reduction theorem.
* `SiegelUpperHalfSpace.isClosed_siegelSet`: the Siegel set is closed.
* `SiegelUpperHalfSpace.exists_smul_mem_siegelSet_transformationGroup`: the same for the
  transformations of `ℋ₂` induced by `Sp(4, ℤ)`.
-/

open Complex Matrix SymplecticGroup

open scoped MatrixGroups UpperHalfPlane

namespace SymplecticGroup

variable {l : Type*} [Fintype l] [DecidableEq l] {R : Type*} [CommRing R]

/-- The **translation** `(1, S; 0, 1)` of `Sp(2g, R)` by a symmetric matrix `S`. -/
def symTranslation (S : Matrix l l R) (hS : Sᵀ = S) : symplecticGroup l R :=
  ⟨fromBlocks 1 S 0 1, fromBlocks_upper_mem hS⟩

lemma coe_symTranslation (S : Matrix l l R) (hS : Sᵀ = S) :
    (symTranslation S hS : Matrix (l ⊕ l) (l ⊕ l) R) = fromBlocks 1 S 0 1 :=
  rfl

end SymplecticGroup

namespace SiegelUpperHalfSpace

section General

variable {l : Type*} [Fintype l] [DecidableEq l] (τ : SiegelUpperHalfSpace l)

lemma denom_symTranslation {S : Matrix l l ℝ} (hS : Sᵀ = S) :
    denom (symTranslation S hS) τ.val = 1 := by
  simp [denom, coe_symTranslation]

lemma val_smul_symTranslation {S : Matrix l l ℝ} (hS : Sᵀ = S) :
    (symTranslation S hS • τ).val = τ.val + S.map ofReal := by
  rw [val_smul, denom_symTranslation, inv_one, Matrix.mul_one, num, coe_symTranslation]
  simp

lemma map_symTranslation {S : Matrix l l ℤ} (hS : Sᵀ = S) :
    SymplecticGroup.map (Int.castRingHom ℝ) (symTranslation S hS) =
      symTranslation (S.map (Int.castRingHom ℝ)) (by rw [← transpose_map, hS]) :=
  Subtype.ext <| by
    rw [SymplecticGroup.coe_map_apply, coe_symTranslation, coe_symTranslation, fromBlocks_map]
    simp

variable (U : GL l ℤ)

private lemma coe_map_levi :
    (SymplecticGroup.map (Int.castRingHom ℝ) (levi l ℤ U) : Matrix (l ⊕ l) (l ⊕ l) ℝ) =
      fromBlocks ((U : Matrix l l ℤ).map (Int.cast : ℤ → ℝ)) 0 0
        (((U⁻¹ : GL l ℤ) : Matrix l l ℤ)ᵀ.map (Int.cast : ℤ → ℝ)) := by
  rw [SymplecticGroup.coe_map_apply, coe_levi, fromBlocks_map]
  simp

lemma denom_map_levi : denom (SymplecticGroup.map (Int.castRingHom ℝ) (levi l ℤ U)) τ.val =
    ((U⁻¹ : GL l ℤ) : Matrix l l ℤ)ᵀ.map (Int.cast : ℤ → ℂ) := by
  rw [denom, coe_map_levi]
  simp [Function.comp_def]

/-- **`(U, 0; 0, U⁻ᵀ)` acts by `Z ↦ U Z Uᵀ`.** -/
lemma val_smul_levi : (SymplecticGroup.map (Int.castRingHom ℝ) (levi l ℤ U) • τ).val =
    (U : Matrix l l ℤ).map (Int.cast : ℤ → ℂ) * τ.val *
      ((U : Matrix l l ℤ).map (Int.cast : ℤ → ℂ))ᵀ := by
  rw [val_smul_of_mem_siegelParabolic τ (toBlocks_fromBlocks₂₁ _ _ _ _)]
  simp [coe_levi, transpose_map]

lemma norm_det_denom_map_levi :
    ‖(denom (SymplecticGroup.map (Int.castRingHom ℝ) (levi l ℤ U)) τ.val).det‖ = 1 := by
  have h : IsUnit ((U⁻¹ : GL l ℤ) : Matrix l l ℤ)ᵀ.det := by
    rw [det_transpose]
    exact (isUnit_iff_isUnit_det _).mp (U⁻¹).isUnit
  have e : (((U⁻¹ : GL l ℤ) : Matrix l l ℤ)ᵀ.map (Int.cast : ℤ → ℂ)).det =
      ((((U⁻¹ : GL l ℤ) : Matrix l l ℤ)ᵀ.det : ℤ) : ℂ) :=
    (RingHom.map_det (Int.castRingHom ℂ) _).symm
  rw [denom_map_levi, e]
  generalize ((U⁻¹ : GL l ℤ) : Matrix l l ℤ)ᵀ.det = d at h
  rcases Int.isUnit_iff.mp h with rfl | rfl <;> simp

end General

variable (Z : SiegelUpperHalfSpace (Fin 2))

/-! ### The determinant-maximal representative -/

lemma det_denom_one (τ : SiegelUpperHalfSpace (Fin 2)) :
    (denom (1 : symplecticGroup (Fin 2) ℝ) τ.val).det = 1 := by
  have h : (denomGL (1 : symplecticGroup (Fin 2) ℝ) τ : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [denomGL_one, Units.val_one]
  rw [← coe_denomGL, h, det_one]

/-- **The determinant-maximal representative**: `|det(CZ + D)|` has a minimum over the bottom rows
`(C, D)` of `Sp(4, ℤ)`, that is `det Im(δZ)` has a maximum: the Plücker vectors of the bottom rows
with `|det(CZ + D)| ≤ 1` are integral and bounded, and they determine `|det(CZ + D)|`. -/
lemma exists_forall_norm_det_denom_le : ∃ δ : symplecticGroup (Fin 2) ℤ, ∀ γ,
    ‖(denom (SymplecticGroup.map (Int.castRingHom ℝ) δ) Z.val).det‖ ≤
      ‖(denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) Z.val).det‖ := by
  let A : Set (symplecticGroup (Fin 2) ℤ) :=
    {γ | ‖(denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) Z.val).det‖ ≤ 1}
  let f : (Fin 5 → ℤ) → ℝ := fun p ↦ ‖(p 0 : ℂ) * (Z.val 0 0 * Z.val 1 1 - Z.val 0 1 ^ 2) +
    p 1 * Z.val 0 0 + 2 * p 2 * Z.val 0 1 - p 3 * Z.val 1 1 + p 4‖
  have hf (γ : symplecticGroup (Fin 2) ℤ) :
      ‖(denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) Z.val).det‖ = f (siegelPlucker γ) := by
    rw [det_denom_eq_siegelPlucker]
  have hK : 0 < siegelK Z.val := siegelK_pos Z
  have hfin : (siegelPlucker '' A).Finite := by
    refine (isCompact_iff_finite.mp
      (isCompact_closedBall (0 : Fin 5 → ℤ) (siegelK Z.val))).subset ?_
    rintro _ ⟨γ, hγ, rfl⟩
    rw [mem_closedBall_zero_iff]
    refine (norm_siegelPlucker_le γ Z).trans ?_
    exact mul_le_of_le_one_right hK.le hγ
  have h₁ : (1 : symplecticGroup (Fin 2) ℤ) ∈ A := by
    rw [Set.mem_ofPred_eq, map_one, det_denom_one, norm_one]
  rcases Set.exists_min_image _ f hfin ⟨_, 1, h₁, rfl⟩ with ⟨_, ⟨δ, hδ, rfl⟩, hmin⟩
  refine ⟨δ, fun γ ↦ ?_⟩
  by_cases hγ : γ ∈ A
  · rw [hf, hf]
    exact hmin _ ⟨γ, hγ, rfl⟩
  · exact (show _ ≤ (1 : ℝ) from hδ).trans (not_le.mp hγ).le

/-! ### Gauss's reduction of binary quadratic forms -/

section Gauss

variable {a b c : ℝ}

private lemma normSq_mul_add {t p q : ℝ} (ha : a ≠ 0) (ht : t ^ 2 = a * c - b ^ 2) :
    a * ((p * (b / a) + q) ^ 2 + (p * (t / a)) ^ 2) = a * q ^ 2 + 2 * b * q * p + c * p ^ 2 := by
  field_simp
  linear_combination p ^ 2 * ht

private lemma re_mul_conj {t p q r s : ℝ} (ha : a ≠ 0) (ht : t ^ 2 = a * c - b ^ 2) :
    a * ((p * (b / a) + q) * (r * (b / a) + s) + p * (t / a) * (r * (t / a))) = a * s * q +
      b * (s * p + r * q) + c * r * p := by
  field_simp
  linear_combination p * r * ht

private lemma exists_gauss_reduced (ha : 0 < a) (hD : 0 < a * c - b ^ 2) : ∃ p q r s : ℤ,
    s * p - r * q = 1 ∧ 2 * |a * s * q + b * (s * p + r * q) + c * r * p| ≤
      a * s ^ 2 + 2 * b * s * r + c * r ^ 2 ∧ a * s ^ 2 + 2 * b * s * r + c * r ^ 2 ≤
        a * q ^ 2 + 2 * b * q * p + c * p ^ 2 := by
  have ht : (√(a * c - b ^ 2)) ^ 2 = a * c - b ^ 2 := Real.sq_sqrt hD.le
  have ht₀ : 0 < √(a * c - b ^ 2) := Real.sqrt_pos.mpr hD
  generalize √(a * c - b ^ 2) = t at ht ht₀
  have hy : 0 < t / a := div_pos ht₀ ha
  let τ : ℍ := ⟨((b / a : ℝ) : ℂ) + ((t / a : ℝ) : ℂ) * I, by
    simpa using hy⟩
  have hτre : τ.re = b / a := by
    simp [τ]
  have hτim : τ.im = t / a := by
    simp [τ]
  rcases ModularGroup.exists_smul_mem_fd τ with ⟨g, hg₁, hg₂⟩
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h : (g : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := g.det_coe
    rwa [det_fin_two] at h
  have hsmul : ((g • τ : ℍ) : ℂ) = (((g 0 0 : ℝ) : ℂ) * τ + ((g 0 1 : ℝ) : ℂ)) /
      (((g 1 0 : ℝ) : ℂ) * τ + ((g 1 1 : ℝ) : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp
  have hg₁' : 1 ≤ normSq ((g • τ : ℍ) : ℂ) := hg₁
  have hg₂' : |((g • τ : ℍ) : ℂ).re| ≤ 1 / 2 := hg₂
  rw [hsmul] at hg₁' hg₂'
  have hw (u v : ℝ) :
      ((u : ℂ) * τ + (v : ℂ)).re = u * (b / a) + v ∧ ((u : ℂ) * τ + (v : ℂ)).im = u * (t / a) := by
    simp [hτre, hτim]
  have hnorm (u v : ℝ) :
      a * normSq ((u : ℂ) * τ + (v : ℂ)) = a * v ^ 2 + 2 * b * v * u + c * u ^ 2 := by
    rw [normSq_apply, (hw u v).1, (hw u v).2, ← pow_two, ← pow_two]
    exact normSq_mul_add ha.ne' ht
  have hN₂ : 0 < normSq (((g 1 0 : ℝ) : ℂ) * τ + ((g 1 1 : ℝ) : ℂ)) := by
    refine normSq_pos.mpr fun h ↦ ?_
    have h₃ : (((g 1 0 : ℝ) : ℂ) * τ + ((g 1 1 : ℝ) : ℂ)).im = (g 1 0 : ℝ) * (t / a) :=
      (hw (g 1 0) (g 1 1)).2
    have h₄ :
        (((g 1 0 : ℝ) : ℂ) * τ + ((g 1 1 : ℝ) : ℂ)).re = (g 1 0 : ℝ) * (b / a) + (g 1 1 : ℝ) :=
      (hw (g 1 0) (g 1 1)).1
    rw [h, zero_im] at h₃
    rw [h, zero_re] at h₄
    have e₀ : ((g 1 0 : ℤ) : ℝ) = 0 := (mul_eq_zero.mp h₃.symm).resolve_right hy.ne'
    rw [e₀, zero_mul, zero_add] at h₄
    have e₀' : g 1 0 = 0 := by
      exact_mod_cast e₀
    have e₁' : g 1 1 = 0 := by
      exact_mod_cast h₄.symm
    rw [e₀', e₁'] at hdet
    simp at hdet
  refine ⟨g 0 0, g 0 1, g 1 0, g 1 1, ?_, ?_, ?_⟩
  · linear_combination hdet
  · rw [div_re, (hw _ _).1, (hw _ _).2, (hw _ _).1, (hw _ _).2, ← add_div, abs_div, abs_of_pos hN₂,
      div_le_iff₀ hN₂] at hg₂'
    rw [← re_mul_conj (p := (g 0 0 : ℝ)) (q := (g 0 1 : ℝ)) (r := (g 1 0 : ℝ)) (s := (g 1 1 : ℝ))
      ha.ne' ht, ← hnorm, abs_mul, abs_of_pos ha]
    nlinarith [mul_le_mul_of_nonneg_left hg₂' ha.le]
  · rw [normSq_div, le_div_iff₀ hN₂, one_mul] at hg₁'
    rw [← hnorm, ← hnorm]
    exact mul_le_mul_of_nonneg_left hg₁' ha.le

end Gauss

lemma im_val_smul_levi (U : GL (Fin 2) ℤ) (i j : Fin 2) :
    ((SymplecticGroup.map (Int.castRingHom ℝ) (levi (Fin 2) ℤ U) • Z).val i j).im =
      ((U : Matrix (Fin 2) (Fin 2) ℤ) i 0 : ℝ) * (U : Matrix (Fin 2) (Fin 2) ℤ) j 0 *
          (Z.val 0 0).im +
        (((U : Matrix (Fin 2) (Fin 2) ℤ) i 0 : ℝ) * (U : Matrix (Fin 2) (Fin 2) ℤ) j 1 +
          ((U : Matrix (Fin 2) (Fin 2) ℤ) i 1 : ℝ) * (U : Matrix (Fin 2) (Fin 2) ℤ) j 0) *
            (Z.val 0 1).im +
        ((U : Matrix (Fin 2) (Fin 2) ℤ) i 1 : ℝ) * (U : Matrix (Fin 2) (Fin 2) ℤ) j 1 *
          (Z.val 1 1).im := by
  have hZ : Z.val 1 0 = Z.val 0 1 := congrFun (congrFun Z.transpose_val 0) 1
  rw [val_smul_levi]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, transpose_apply, map_apply, hZ, add_im, mul_im,
    intCast_re, intCast_im]
  ring1

lemma im_mul_im_sub_sq_pos : 0 < (Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im ^ 2 := by
  have h₁ : 0 < (Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im * (Z.val 1 0).im := det_im_pos Z
  have hZ : Z.val 1 0 = Z.val 0 1 := congrFun (congrFun Z.transpose_val 0) 1
  rwa [hZ, ← sq] at h₁

/-- **Gauss's reduction of binary quadratic forms**: for `Z ∈ ℋ₂` there is `U ∈ GL(2, ℤ)` such that
`Y = Im(U Z Uᵀ)` has `2 |y₀₁| ≤ y₀₀ ≤ y₁₁`. -/
lemma exists_levi_reduced : ∃ U : GL (Fin 2) ℤ,
    2 * |((SymplecticGroup.map (Int.castRingHom ℝ) (levi (Fin 2) ℤ U) • Z).val 0 1).im| ≤
      ((SymplecticGroup.map (Int.castRingHom ℝ) (levi (Fin 2) ℤ U) • Z).val 0 0).im ∧
    ((SymplecticGroup.map (Int.castRingHom ℝ) (levi (Fin 2) ℤ U) • Z).val 0 0).im ≤
      ((SymplecticGroup.map (Int.castRingHom ℝ) (levi (Fin 2) ℤ U) • Z).val 1 1).im := by
  rcases exists_gauss_reduced (im_zero_zero_pos Z) (im_mul_im_sub_sq_pos Z) with
    ⟨p, q, r, s, hdet, h₁, h₂⟩
  let U : GL (Fin 2) ℤ := ⟨!![s, r; q, p], !![p, -r; -q, s], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;>
      first | ring1 | linear_combination hdet, by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;>
      first | ring1 | linear_combination hdet⟩
  have hU : (U : Matrix (Fin 2) (Fin 2) ℤ) = !![s, r; q, p] := rfl
  refine ⟨U, ?_, ?_⟩
  · rw [im_val_smul_levi, im_val_smul_levi, hU]
    simp only [of_apply, cons_val_zero, cons_val_one]
    convert h₁ using 1
    · congr 2
      ring1
    · ring1
  · rw [im_val_smul_levi, im_val_smul_levi, hU]
    simp only [of_apply, cons_val_zero, cons_val_one]
    convert h₂ using 1 <;> ring1

/-! ### The Siegel set -/

/-- The **Siegel set** of `ℋ₂`: the points `Z = X + iY` with `|x_ij| ≤ 1/2`, with `Y` reduced in the
sense of Gauss, `2 |y₀₁| ≤ y₀₀ ≤ y₁₁`, and with `y₀₀ ≥ √3 / 2`. Every point of `ℋ₂` is equivalent to
one of its points under `Sp(4, ℤ)` (`SiegelUpperHalfSpace.exists_smul_mem_siegelSet`). -/
def siegelSet : Set (SiegelUpperHalfSpace (Fin 2)) :=
  {Z | (∀ i j, |(Z.val i j).re| ≤ 1 / 2) ∧ 2 * |(Z.val 0 1).im| ≤ (Z.val 0 0).im ∧
    (Z.val 0 0).im ≤ (Z.val 1 1).im ∧ √3 / 2 ≤ (Z.val 0 0).im}

/-- **The Siegel set is closed.** -/
lemma isClosed_siegelSet : IsClosed siegelSet := by
  have h₁ : IsClosed {Z : SiegelUpperHalfSpace (Fin 2) | ∀ i j, |(Z.val i j).re| ≤ 1 / 2} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
      isClosed_le (continuous_re_apply i j).abs continuous_const
  have h₂ : IsClosed {Z : SiegelUpperHalfSpace (Fin 2) | 2 * |(Z.val 0 1).im| ≤ (Z.val 0 0).im} :=
    isClosed_le (continuous_const.mul (continuous_im_apply 0 1).abs) (continuous_im_apply 0 0)
  have h₃ : IsClosed {Z : SiegelUpperHalfSpace (Fin 2) | (Z.val 0 0).im ≤ (Z.val 1 1).im} :=
    isClosed_le (continuous_im_apply 0 0) (continuous_im_apply 1 1)
  have h₄ : IsClosed {Z : SiegelUpperHalfSpace (Fin 2) | √3 / 2 ≤ (Z.val 0 0).im} :=
    isClosed_le continuous_const (continuous_im_apply 0 0)
  exact h₁.inter (h₂.inter (h₃.inter h₄))

lemma measurableSet_siegelSet : MeasurableSet siegelSet :=
  isClosed_siegelSet.measurableSet

/-- **Siegel's reduction theorem in degree 2**: every point of `ℋ₂` is equivalent under `Sp(4, ℤ)`
to a point of the Siegel set. Take `δ` maximising `det Im(δZ)`, then reduce the imaginary part by
`GL(2, ℤ)` and the real part by an integral translation, which keeps `det Im` maximal; the partial
inversion then gives `|z₀₀| ≥ 1`. -/
lemma exists_smul_mem_siegelSet :
    ∃ γ : symplecticGroup (Fin 2) ℤ, SymplecticGroup.map (Int.castRingHom ℝ) γ • Z ∈ siegelSet := by
  rcases exists_forall_norm_det_denom_le Z with ⟨δ, hδ⟩
  let φ : symplecticGroup (Fin 2) ℤ →* symplecticGroup (Fin 2) ℝ :=
    SymplecticGroup.map (Int.castRingHom ℝ)
  have hZ₁ (γ : symplecticGroup (Fin 2) ℤ) : 1 ≤ ‖(denom (φ γ) (φ δ • Z).val).det‖ := by
    have h₁ : (denom (φ (γ * δ)) Z.val).det = (denom (φ γ) (φ δ • Z).val).det *
        (denom (φ δ) Z.val).det := by
      rw [map_mul, denom_mul, det_mul]
    have h₂ : ‖(denom (φ δ) Z.val).det‖ ≤ ‖(denom (φ (γ * δ)) Z.val).det‖ := hδ (γ * δ)
    have hpos : 0 < ‖(denom (φ δ) Z.val).det‖ :=
      norm_pos_iff.mpr (isUnit_det_denom _ Z).ne_zero
    rw [h₁, norm_mul] at h₂
    exact le_of_mul_le_mul_right (by simpa using h₂) hpos
  rcases exists_levi_reduced (φ δ • Z) with ⟨U, hU₁, hU₂⟩
  have hLδ : ‖(denom (φ (levi (Fin 2) ℤ U)) (φ δ • Z).val).det‖ = 1 :=
    norm_det_denom_map_levi _ U
  generalize hZ₂ : φ (levi (Fin 2) ℤ U) • φ δ • Z = Z₂ at hU₁ hU₂
  have hZ₂s : Z₂.val 1 0 = Z₂.val 0 1 := congrFun (congrFun Z₂.transpose_val 0) 1
  let S : Matrix (Fin 2) (Fin 2) ℤ := !![-round (Z₂.val 0 0).re, -round (Z₂.val 0 1).re;
    -round (Z₂.val 0 1).re, -round (Z₂.val 1 1).re]
  have hS : Sᵀ = S := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hZ₃ (i j : Fin 2) :
      (φ (symTranslation S hS) • Z₂).val i j = Z₂.val i j + ((S i j : ℝ) : ℂ) := by
    have e : φ (symTranslation S hS) = symTranslation (S.map (Int.castRingHom ℝ))
        (by rw [← transpose_map, hS]) := map_symTranslation hS
    rw [e, val_smul_symTranslation]
    simp
  have hT (W : SiegelUpperHalfSpace (Fin 2)) : (denom (φ (symTranslation S hS)) W.val).det = 1 := by
    have e : φ (symTranslation S hS) = symTranslation (S.map (Int.castRingHom ℝ))
        (by rw [← transpose_map, hS]) := map_symTranslation hS
    rw [e, denom_symTranslation, det_one]
  have hZ₄ (γ : symplecticGroup (Fin 2) ℤ) :
      1 ≤ ‖(denom (φ γ) (φ (symTranslation S hS) • Z₂).val).det‖ := by
    have h₁ : 1 ≤ ‖(denom (φ (γ * symTranslation S hS * levi (Fin 2) ℤ U)) (φ δ • Z).val).det‖ :=
      hZ₁ (γ * symTranslation S hS * levi (Fin 2) ℤ U)
    rw [map_mul, map_mul, denom_mul, hZ₂, denom_mul, det_mul, det_mul, hT, mul_one, norm_mul, hLδ,
      mul_one] at h₁
    exact h₁
  have hpi : 1 ≤ ‖(denom (φ partialInversion) (φ (symTranslation S hS) • Z₂).val).det‖ :=
    hZ₄ partialInversion
  rw [det_denom_partialInversion, hZ₃] at hpi
  refine ⟨symTranslation S hS * levi (Fin 2) ℤ U * δ, ?_⟩
  have hsmul :
      SymplecticGroup.map (Int.castRingHom ℝ) (symTranslation S hS * levi (Fin 2) ℤ U * δ) • Z =
        φ (symTranslation S hS) • Z₂ := by
    rw [← hZ₂, ← mul_smul, ← mul_smul, ← map_mul, ← map_mul]
  rw [hsmul]
  have him (i j : Fin 2) : ((φ (symTranslation S hS) • Z₂).val i j).im = (Z₂.val i j).im := by
    rw [hZ₃]
    simp
  have hre (i j : Fin 2) :
      ((φ (symTranslation S hS) • Z₂).val i j).re = (Z₂.val i j).re + (S i j : ℝ) := by
    rw [hZ₃]
    simp
  have hx₀₀ : |(Z₂.val 0 0).re + (S 0 0 : ℝ)| ≤ 1 / 2 := by
    simpa [S, sub_eq_add_neg] using abs_sub_round (Z₂.val 0 0).re
  refine ⟨fun i j ↦ ?_, ?_, ?_, ?_⟩
  · rw [hre]
    fin_cases i <;> fin_cases j
    · exact hx₀₀
    · simpa [S, sub_eq_add_neg] using abs_sub_round (Z₂.val 0 1).re
    · simpa [S, sub_eq_add_neg, hZ₂s] using abs_sub_round (Z₂.val 0 1).re
    · simpa [S, sub_eq_add_neg] using abs_sub_round (Z₂.val 1 1).re
  · rw [him, him]
    exact hU₁
  · rw [him, him]
    exact hU₂
  · rw [him]
    have hy : 0 < (Z₂.val 0 0).im := im_zero_zero_pos Z₂
    have hn : 1 ≤ normSq (Z₂.val 0 0 + ((S 0 0 : ℝ) : ℂ)) := by
      rw [normSq_eq_norm_sq]
      nlinarith [norm_nonneg (Z₂.val 0 0 + ((S 0 0 : ℝ) : ℂ))]
    rw [normSq_apply] at hn
    have hre₀ : (Z₂.val 0 0 + ((S 0 0 : ℝ) : ℂ)).re = (Z₂.val 0 0).re + (S 0 0 : ℝ) := by
      simp
    have him₀ : (Z₂.val 0 0 + ((S 0 0 : ℝ) : ℂ)).im = (Z₂.val 0 0).im := by
      simp
    rw [hre₀, him₀] at hn
    have hx : -(1 / 2) ≤ (Z₂.val 0 0).re + (S 0 0 : ℝ) ∧ (Z₂.val 0 0).re + (S 0 0 : ℝ) ≤ 1 / 2 :=
      abs_le.mp hx₀₀
    have h₃ : √3 ≤ 2 * (Z₂.val 0 0).im :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
    linarith

/-- **Siegel's reduction theorem for the transformations of `ℋ₂`** induced by `Sp(4, ℤ)`: every
orbit meets the Siegel set. -/
lemma exists_smul_mem_siegelSet_transformationGroup :
    ∃ g : transformationGroup (integral (Fin 2)), g • Z ∈ siegelSet := by
  rcases exists_smul_mem_siegelSet Z with ⟨γ, hγ⟩
  refine ⟨⟨_, SymplecticGroup.map (Int.castRingHom ℚ) γ, ⟨γ, trivial, rfl⟩, rfl⟩, ?_⟩
  have e : SymplecticGroup.map (algebraMap ℚ ℝ) (SymplecticGroup.map (Int.castRingHom ℚ) γ) =
      SymplecticGroup.map (Int.castRingHom ℝ) γ :=
    Subtype.ext <| by
      ext a b
      simp
  have e₁ : (⟨_, SymplecticGroup.map (Int.castRingHom ℚ) γ, ⟨γ, trivial, rfl⟩, rfl⟩ :
      transformationGroup (integral (Fin 2))) • Z =
        SymplecticGroup.map (algebraMap ℚ ℝ) (SymplecticGroup.map (Int.castRingHom ℚ) γ) • Z :=
    rfl
  rw [e₁, e]
  exact hγ

end SiegelUpperHalfSpace
