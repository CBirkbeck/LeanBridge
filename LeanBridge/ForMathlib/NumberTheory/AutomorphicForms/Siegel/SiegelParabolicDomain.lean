import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PeterssonUnfolding
import TauCeti.Algebra.Group.Units.Countable

/-!
# A fundamental domain of the Siegel parabolic subgroup of `Sp(4, ℤ)`

The Siegel parabolic subgroup `P` of `Sp(4, ℤ)` acts on `ℋ₂` by `Z ↦ U Z Uᵀ + S`, for `U ∈ GL(2, ℤ)`
and `S` integral symmetric. It has a fundamental domain which is a product in the coordinates
`Z = X + iY`: `X` runs over a box of volume `1`, and `Y` over the points of its `GL(2, ℤ)`-orbit at
which the linear form `tr(W Y)` is strictly minimal, for `W = (3, 1; 1, 4)`. The minimum is
attained, as `tr(W U Y Uᵀ)` is a positive definite quadratic form in the entries of `U`, and it is
attained once for almost every `Y`, since the only elements of `GL(2, ℤ)` with `Uᵀ W U = W` are
`±1`, so that `tr(W U Y Uᵀ) = tr(W Y)` cuts out a proper hyperplane for `U ≠ ±1`.

The box can be translated freely, so the translation `T_u : Z ↦ Z + u E₁₁` maps this domain to a
fundamental domain of `P` for every `u`, although `T_u` does not normalise `P`.

## Main definitions

* `SiegelUpperHalfSpace.parabolicWeight`: the linear form `tr(W Y)`.
* `SiegelUpperHalfSpace.parabolicDomain`: the fundamental domain.

## Main results

* `SiegelUpperHalfSpace.exists_eq_symTranslation_mul_levi`: an element of `P` is `(1, S; 0, 1)`
  times `(U, 0; 0, U⁻ᵀ)`.
* `SiegelUpperHalfSpace.isFundamentalDomain_parabolicDomain`: `parabolicDomain` is a fundamental
  domain of `P`.
* `SiegelUpperHalfSpace.cornerTranslation_smul_parabolicDomain`: `T_u` translates the box.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open Complex MeasureTheory Module Real Set SymplecticGroup

open scoped Pointwise

namespace SiegelUpperHalfSpace

/-! ### The Siegel parabolic subgroup -/

/-- **An element of the Siegel parabolic subgroup of `Sp(4, ℤ)` is
`(1, S; 0, 1) (U, 0; 0, U⁻ᵀ)`.** -/
lemma exists_eq_symTranslation_mul_levi {p : symplecticGroup (Fin 2) ℤ}
    (hp : p ∈ siegelParabolic (Fin 2) ℤ) : ∃ (S : Matrix (Fin 2) (Fin 2) ℤ) (hS : Sᵀ = S)
      (U : GL (Fin 2) ℤ), p = symTranslation S hS * levi (Fin 2) ℤ U := by
  have hS : (p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ)ᵀ = p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ := by
    rw [transpose_mul, transpose_transpose, toBlocks₁₂_mul_transpose_toBlocks₁₁ hp]
  refine ⟨_, hS, siegelParabolicBlock ⟨p, hp⟩, Subtype.ext ?_⟩
  have hinv : ((siegelParabolicBlock ⟨p, hp⟩)⁻¹ : GL (Fin 2) ℤ).1ᵀ = p.1.toBlocks₂₂ := by
    have h : ((siegelParabolicBlock ⟨p, hp⟩)⁻¹ : GL (Fin 2) ℤ).1 = p.1.toBlocks₂₂ᵀ := rfl
    rw [h, transpose_transpose]
  have hval :
      ((siegelParabolicBlock ⟨p, hp⟩ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = p.1.toBlocks₁₁ :=
    rfl
  have h₁ : p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ * p.1.toBlocks₂₂ = p.1.toBlocks₁₂ := by
    rw [Matrix.mul_assoc, transpose_toBlocks₁₁_mul_toBlocks₂₂ hp, Matrix.mul_one]
  rw [Submonoid.coe_mul, coe_symTranslation, coe_levi, fromBlocks_multiply, hinv, hval, h₁]
  simpa using eq_fromBlocks_of_mem_siegelParabolic hp

/-! ### The weight -/

variable (U V : GL (Fin 2) ℤ) (Z Z' : SiegelUpperHalfSpace (Fin 2))

/-- The linear form `tr(W Y) = 3 y₀₀ + 2 y₀₁ + 4 y₁₁` on `Z = X + iY`, for `W = (3, 1; 1, 4)`. Its
minimum on the `GL(2, ℤ)`-orbit of `Y` selects the fundamental domain of the Siegel parabolic
subgroup (`SiegelUpperHalfSpace.parabolicDomain`). -/
noncomputable def parabolicWeight : ℝ :=
  3 * (Z.val 0 0).im + 2 * (Z.val 0 1).im + 4 * (Z.val 1 1).im

/-- The action `Z ↦ U Z Uᵀ` of `U ∈ GL(2, ℤ)`. -/
private noncomputable abbrev leviR : symplecticGroup (Fin 2) ℝ :=
  SymplecticGroup.map (Int.castRingHom ℝ) (levi (Fin 2) ℤ U)

private lemma leviR_mul : leviR (U * V) = leviR U * leviR V := by
  simp only [leviR, map_mul]

private lemma leviR_one : leviR 1 = 1 := by
  simp only [leviR, map_one]

private lemma parabolicWeight_leviR_smul : parabolicWeight (leviR U • Z) =
    ((3 * U.1 0 0 ^ 2 + 2 * U.1 0 0 * U.1 1 0 + 4 * U.1 1 0 ^ 2 : ℤ) : ℝ) * (Z.val 0 0).im +
      ((6 * U.1 0 0 * U.1 0 1 + 2 * (U.1 0 0 * U.1 1 1 + U.1 0 1 * U.1 1 0) +
        8 * U.1 1 0 * U.1 1 1 : ℤ) : ℝ) * (Z.val 0 1).im +
      ((3 * U.1 0 1 ^ 2 + 2 * U.1 0 1 * U.1 1 1 + 4 * U.1 1 1 ^ 2 : ℤ) : ℝ) * (Z.val 1 1).im := by
  rw [parabolicWeight, im_val_smul_levi, im_val_smul_levi, im_val_smul_levi]
  push_cast
  ring1

variable {Z Z'}

private lemma parabolicWeight_congr (h : ∀ i j, (Z.val i j).im = (Z'.val i j).im) :
    parabolicWeight Z = parabolicWeight Z' := by
  simp only [parabolicWeight, h]

private lemma parabolicWeight_leviR_smul_congr (h : ∀ i j, (Z.val i j).im = (Z'.val i j).im) :
    parabolicWeight (leviR U • Z) = parabolicWeight (leviR U • Z') := by
  simp only [parabolicWeight_leviR_smul, h]

private lemma int_aut {p q r s : ℤ} (hA : 3 * p ^ 2 + 2 * p * r + 4 * r ^ 2 = 3)
    (hC : 3 * q ^ 2 + 2 * q * s + 4 * s ^ 2 = 4)
    (hB : 6 * p * q + 2 * (p * s + q * r) + 8 * r * s = 2) :
    (p = 1 ∧ q = 0 ∧ r = 0 ∧ s = 1) ∨ (p = -1 ∧ q = 0 ∧ r = 0 ∧ s = -1) := by
  have hp₁ : p ≤ 1 := by nlinarith [sq_nonneg (p + r), sq_nonneg r, sq_nonneg (p - 1)]
  have hp₂ : -1 ≤ p := by nlinarith [sq_nonneg (p + r), sq_nonneg r, sq_nonneg (p + 1)]
  have hr₁ : r ≤ 1 := by nlinarith [sq_nonneg (p + r), sq_nonneg p, sq_nonneg (r - 1)]
  have hr₂ : -1 ≤ r := by nlinarith [sq_nonneg (p + r), sq_nonneg p, sq_nonneg (r + 1)]
  have hq₁ : q ≤ 1 := by nlinarith [sq_nonneg (q + s), sq_nonneg s, sq_nonneg (q - 1)]
  have hq₂ : -1 ≤ q := by nlinarith [sq_nonneg (q + s), sq_nonneg s, sq_nonneg (q + 1)]
  have hs₁ : s ≤ 1 := by nlinarith [sq_nonneg (q + s), sq_nonneg q, sq_nonneg (s - 1)]
  have hs₂ : -1 ≤ s := by nlinarith [sq_nonneg (q + s), sq_nonneg q, sq_nonneg (s + 1)]
  interval_cases p <;> interval_cases r <;> interval_cases q <;> interval_cases s <;> omega

private lemma eq_one_or_eq_neg_one
    (hA : 3 * U.1 0 0 ^ 2 + 2 * U.1 0 0 * U.1 1 0 + 4 * U.1 1 0 ^ 2 = 3)
    (hB : 6 * U.1 0 0 * U.1 0 1 + 2 * (U.1 0 0 * U.1 1 1 + U.1 0 1 * U.1 1 0) +
      8 * U.1 1 0 * U.1 1 1 = 2)
    (hC : 3 * U.1 0 1 ^ 2 + 2 * U.1 0 1 * U.1 1 1 + 4 * U.1 1 1 ^ 2 = 4) : U = 1 ∨ U = -1 := by
  rcases int_aut hA hC hB with ⟨h₀, h₁, h₂, h₃⟩ | ⟨h₀, h₁, h₂, h₃⟩
  · refine .inl (Units.ext ?_)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h₀, h₁, h₂, h₃]
  · refine .inr (Units.ext ?_)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h₀, h₁, h₂, h₃]

/-! ### Null sets -/

private lemma invariantMeasure_setOf_linear_eq_zero {a b c : ℝ} (h : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    invariantMeasure (Fin 2) {Z | a * (Z.val 0 0).im + b * (Z.val 0 1).im + c * (Z.val 1 1).im =
      0} = 0 := by
  let p : MvPolynomial (Sym2 (Fin 2) ⊕ Sym2 (Fin 2)) ℝ :=
    MvPolynomial.C a * MvPolynomial.X (.inr s(0, 0)) +
      MvPolynomial.C b * MvPolynomial.X (.inr s(0, 1)) +
        MvPolynomial.C c * MvPolynomial.X (.inr s(1, 1))
  have hev (x : Sym2 (Fin 2) ⊕ Sym2 (Fin 2) → ℝ) : MvPolynomial.eval x p = a * x (.inr s(0, 0)) +
      b * x (.inr s(0, 1)) + c * x (.inr s(1, 1)) := by
    simp [p]
  have hp : p ≠ 0 := by
    intro h₀
    have hv (x : Sym2 (Fin 2) ⊕ Sym2 (Fin 2) → ℝ) :
        a * x (.inr s(0, 0)) + b * x (.inr s(0, 1)) + c * x (.inr s(1, 1)) = 0 := by
      rw [← hev, h₀, map_zero]
    refine h ⟨?_, ?_, ?_⟩
    · simpa using hv (Pi.single (.inr s(0, 0)) 1)
    · simpa using hv (Pi.single (.inr s(0, 1)) 1)
    · simpa using hv (Pi.single (.inr s(1, 1)) 1)
  refine measure_mono_null (fun Z hZ ↦ ?_) (invariantMeasure_setOf_eval_eq_zero hp)
  rw [mem_ofPred_eq, hev]
  simpa [toCoords_apply] using hZ

private lemma invariantMeasure_setOf_parabolicWeight_eq {U : GL (Fin 2) ℤ} (h₁ : U ≠ 1)
    (h₂ : U ≠ -1) :
    invariantMeasure (Fin 2) {Z | parabolicWeight (leviR U • Z) = parabolicWeight Z} = 0 := by
  have hne : ¬(((3 * U.1 0 0 ^ 2 + 2 * U.1 0 0 * U.1 1 0 + 4 * U.1 1 0 ^ 2 : ℤ) : ℝ) - 3 = 0 ∧
      ((6 * U.1 0 0 * U.1 0 1 + 2 * (U.1 0 0 * U.1 1 1 + U.1 0 1 * U.1 1 0) +
        8 * U.1 1 0 * U.1 1 1 : ℤ) : ℝ) - 2 = 0 ∧
      ((3 * U.1 0 1 ^ 2 + 2 * U.1 0 1 * U.1 1 1 + 4 * U.1 1 1 ^ 2 : ℤ) : ℝ) - 4 = 0) := by
    rintro ⟨e₁, e₂, e₃⟩
    rcases eq_one_or_eq_neg_one U (by exact_mod_cast sub_eq_zero.mp e₁)
      (by exact_mod_cast sub_eq_zero.mp e₂) (by exact_mod_cast sub_eq_zero.mp e₃) with h | h
    · exact h₁ h
    · exact h₂ h
  refine measure_mono_null (fun Z hZ ↦ ?_) (invariantMeasure_setOf_linear_eq_zero hne)
  rw [mem_ofPred_eq] at hZ ⊢
  rw [parabolicWeight_leviR_smul, parabolicWeight] at hZ
  linarith

private lemma ae_parabolicWeight_ne : ∀ᵐ Z ∂invariantMeasure (Fin 2), ∀ U V : GL (Fin 2) ℤ, U ≠ 1 →
    U ≠ -1 → parabolicWeight (leviR U • leviR V • Z) ≠ parabolicWeight (leviR V • Z) := by
  simp only [ae_all_iff]
  intro U V h₁ h₂
  have h₃ : invariantMeasure (Fin 2) ((fun Z ↦ leviR V • Z) ⁻¹'
      {Z | parabolicWeight (leviR U • Z) = parabolicWeight Z}) =
        invariantMeasure (Fin 2) {Z | parabolicWeight (leviR U • Z) = parabolicWeight Z} :=
    measure_preimage_smul (invariantMeasure (Fin 2)) (leviR V) _
  rw [invariantMeasure_setOf_parabolicWeight_eq h₁ h₂] at h₃
  rw [ae_iff]
  simpa using h₃

/-! ### The minimum on an orbit -/

private lemma le_parabolicWeight_leviR_smul (Z : SiegelUpperHalfSpace (Fin 2)) :
    ((Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im ^ 2) / ((Z.val 0 0).im + (Z.val 1 1).im) *
      (((U.1 0 0 : ℝ)) ^ 2 + (U.1 0 1 : ℝ) ^ 2 + (U.1 1 0 : ℝ) ^ 2 + (U.1 1 1 : ℝ) ^ 2) ≤
        parabolicWeight (leviR U • Z) := by
  have hT : 0 < (Z.val 0 0).im + (Z.val 1 1).im := add_pos (im_zero_zero_pos Z) (im_one_one_pos Z)
  rw [div_mul_eq_mul_div, div_le_iff₀ hT, parabolicWeight_leviR_smul]
  push_cast
  generalize (U.1 0 0 : ℝ) = p
  generalize (U.1 0 1 : ℝ) = q
  generalize (U.1 1 0 : ℝ) = r
  generalize (U.1 1 1 : ℝ) = s
  have ha : 0 < (Z.val 0 0).im := im_zero_zero_pos Z
  have he : 0 < (Z.val 1 1).im := im_one_one_pos Z
  have hD : 0 < (Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im ^ 2 := im_mul_im_sub_sq_pos Z
  generalize (Z.val 0 0).im = a at ha hD hT ⊢
  generalize (Z.val 0 1).im = b at hD ⊢
  generalize (Z.val 1 1).im = e at he hD hT ⊢
  -- the quadratic form `q(x, y) = a x² + 2 b x y + e y²` dominates `det / tr (x² + y²)`
  have hq (x y : ℝ) :
      (a * e - b ^ 2) * (x ^ 2 + y ^ 2) ≤ (a + e) * (a * x ^ 2 + 2 * b * x * y + e * y ^ 2) := by
    nlinarith [sq_nonneg (a * x + b * y), sq_nonneg (b * x + e * y)]
  have hq₀ (x y : ℝ) : 0 ≤ a * x ^ 2 + 2 * b * x * y + e * y ^ 2 := by
    have h₂ : 0 ≤ (a * e - b ^ 2) * (x ^ 2 + y ^ 2) := by
      positivity
    exact nonneg_of_mul_nonneg_right (h₂.trans (hq x y)) hT
  nlinarith [hq p q, hq r s, mul_nonneg hT.le (hq₀ (p + r) (q + s)), mul_nonneg hT.le (hq₀ p q),
    mul_nonneg hT.le (hq₀ r s)]

private lemma finite_setOf_parabolicWeight_le (Z : SiegelUpperHalfSpace (Fin 2)) (c : ℝ) :
    {U : GL (Fin 2) ℤ | parabolicWeight (leviR U • Z) ≤ c}.Finite := by
  have hT : 0 < (Z.val 0 0).im + (Z.val 1 1).im := add_pos (im_zero_zero_pos Z) (im_one_one_pos Z)
  generalize hm : ((Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im ^ 2) /
    ((Z.val 0 0).im + (Z.val 1 1).im) = m
  have hm₀ : 0 < m := hm ▸ div_pos (im_mul_im_sub_sq_pos Z) hT
  have hfin : (Metric.closedBall (0 : Fin 2 → Fin 2 → ℤ) √(c / m)).Finite :=
    isCompact_iff_finite.mp (isCompact_closedBall (0 : Fin 2 → Fin 2 → ℤ) √(c / m))
  refine Finite.of_finite_image (f := fun (U : GL (Fin 2) ℤ) (i j : Fin 2) ↦ U.1 i j)
    (hfin.subset ?_) (fun _ _ _ _ h ↦ Units.ext (Matrix.ext fun i j ↦ congrFun (congrFun h i) j))
  rintro _ ⟨U, hU, rfl⟩
  have h₂ :
      m * ((U.1 0 0 : ℝ) ^ 2 + (U.1 0 1 : ℝ) ^ 2 + (U.1 1 0 : ℝ) ^ 2 + (U.1 1 1 : ℝ) ^ 2) ≤ c := by
    rw [← hm]
    exact (le_parabolicWeight_leviR_smul U Z).trans hU
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i ↦
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j ↦ ?_
  rw [Int.norm_eq_abs]
  refine Real.abs_le_sqrt ?_
  rw [le_div_iff₀ hm₀]
  have hsq (x : Fin 2) (y : Fin 2) : (0 : ℝ) ≤ (U.1 x y : ℝ) ^ 2 := sq_nonneg _
  have h₃ : (U.1 i j : ℝ) ^ 2 ≤ (U.1 0 0 : ℝ) ^ 2 + (U.1 0 1 : ℝ) ^ 2 + (U.1 1 0 : ℝ) ^ 2 +
      (U.1 1 1 : ℝ) ^ 2 := by
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one] <;>
      linarith [hsq 0 0, hsq 0 1, hsq 1 0, hsq 1 1]
  nlinarith [mul_le_mul_of_nonneg_left h₃ hm₀.le]

private lemma exists_forall_parabolicWeight_le (Z : SiegelUpperHalfSpace (Fin 2)) :
    ∃ V : GL (Fin 2) ℤ, ∀ U : GL (Fin 2) ℤ, parabolicWeight (leviR V • Z) ≤
      parabolicWeight (leviR U • Z) := by
  have h₁ : (1 : GL (Fin 2) ℤ) ∈ {U | parabolicWeight (leviR U • Z) ≤ parabolicWeight Z} := by
    simp [leviR_one]
  rcases Set.exists_min_image _ (fun U : GL (Fin 2) ℤ ↦ parabolicWeight (leviR U • Z))
    (finite_setOf_parabolicWeight_le Z _) ⟨1, h₁⟩ with ⟨V, hV, hmin⟩
  refine ⟨V, fun U ↦ ?_⟩
  by_cases hU : parabolicWeight (leviR U • Z) ≤ parabolicWeight Z
  · exact hmin U hU
  · exact (show parabolicWeight (leviR V • Z) ≤ parabolicWeight Z from hV).trans (not_le.mp hU).le

/-! ### The fundamental domain -/

/-- A **fundamental domain of the Siegel parabolic subgroup of `Sp(4, ℤ)`** acting on `ℋ₂`, with
parameter `t`: the points `Z = X + iY` with `x₀₀, x₀₁, x₁₁ - t ∈ [0, 1)` at which the linear form
`SiegelUpperHalfSpace.parabolicWeight` is strictly smaller than at the translates `U Z Uᵀ`, for
`U ≠ ±1` in `GL(2, ℤ)`. -/
def parabolicDomain (t : ℝ) : Set (SiegelUpperHalfSpace (Fin 2)) :=
  {Z | (Z.val 0 0).re ∈ Ico (0 : ℝ) 1 ∧ (Z.val 0 1).re ∈ Ico (0 : ℝ) 1 ∧
    (Z.val 1 1).re - t ∈ Ico (0 : ℝ) 1 ∧ ∀ U : GL (Fin 2) ℤ, U ≠ 1 → U ≠ -1 →
      parabolicWeight Z < parabolicWeight (SymplecticGroup.map (Int.castRingHom ℝ)
        (levi (Fin 2) ℤ U) • Z)}

private lemma continuous_parabolicWeight :
    Continuous (parabolicWeight : SiegelUpperHalfSpace (Fin 2) → ℝ) :=
  ((continuous_const.mul (continuous_im_apply 0 0)).add
    (continuous_const.mul (continuous_im_apply 0 1))).add
      (continuous_const.mul (continuous_im_apply 1 1))

lemma measurableSet_parabolicDomain (t : ℝ) : MeasurableSet (parabolicDomain t) := by
  have h₀ : MeasurableSet {Z : SiegelUpperHalfSpace (Fin 2) | (Z.val 0 0).re ∈ Ico (0 : ℝ) 1} :=
    (continuous_re_apply 0 0).measurable measurableSet_Ico
  have h₁ : MeasurableSet {Z : SiegelUpperHalfSpace (Fin 2) | (Z.val 0 1).re ∈ Ico (0 : ℝ) 1} :=
    (continuous_re_apply 0 1).measurable measurableSet_Ico
  have h₂ : MeasurableSet {Z : SiegelUpperHalfSpace (Fin 2) | (Z.val 1 1).re - t ∈ Ico (0 : ℝ) 1} :=
    ((continuous_re_apply 1 1).sub continuous_const).measurable measurableSet_Ico
  have h₃ : MeasurableSet {Z : SiegelUpperHalfSpace (Fin 2) | ∀ U : GL (Fin 2) ℤ, U ≠ 1 → U ≠ -1 →
      parabolicWeight Z < parabolicWeight (leviR U • Z)} := by
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun U ↦ MeasurableSet.iInter fun _ ↦ MeasurableSet.iInter fun _ ↦ ?_
    exact measurableSet_lt continuous_parabolicWeight.measurable
      (continuous_parabolicWeight.comp (continuous_const_smul (leviR U))).measurable
  exact h₀.inter (h₁.inter (h₂.inter h₃))

variable (S : Matrix (Fin 2) (Fin 2) ℤ) (hS : Sᵀ = S)

private lemma val_map_symTranslation_smul (i j : Fin 2) :
    (SymplecticGroup.map (Int.castRingHom ℝ) (symTranslation S hS) • Z).val i j = Z.val i j +
      ((S i j : ℝ) : ℂ) := by
  rw [map_symTranslation hS, val_smul_symTranslation]
  simp

private lemma im_map_symTranslation_smul (i j : Fin 2) :
    ((SymplecticGroup.map (Int.castRingHom ℝ) (symTranslation S hS) • Z).val i j).im =
      (Z.val i j).im := by
  rw [val_map_symTranslation_smul]
  simp

private lemma re_map_symTranslation_smul (i j : Fin 2) :
    ((SymplecticGroup.map (Int.castRingHom ℝ) (symTranslation S hS) • Z).val i j).re =
      (Z.val i j).re + S i j := by
  rw [val_map_symTranslation_smul]
  simp

private lemma symTranslation_mul_levi_mem (U : GL (Fin 2) ℤ) :
    symTranslation S hS * levi (Fin 2) ℤ U ∈ siegelParabolic (Fin 2) ℤ :=
  Subgroup.mul_mem _ (toBlocks_fromBlocks₂₁ _ _ _ _) (toBlocks_fromBlocks₂₁ _ _ _ _)

private lemma leviR_smul_of_eq_one_or (hU : U = 1 ∨ U = -1) (τ : SiegelUpperHalfSpace (Fin 2)) :
    leviR U • τ = τ := by
  refine SiegelUpperHalfSpace.ext ?_
  rw [val_smul_levi]
  rcases hU with rfl | rfl
  · simp
  · have e : ((((-1 : GL (Fin 2) ℤ) : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)).map
        (Int.cast : ℤ → ℂ) = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [e]
    simp

private lemma eq_zero_of_mem_Ico {x : ℝ} {n : ℤ} (h₁ : x ∈ Ico (0 : ℝ) 1)
    (h₂ : x + n ∈ Ico (0 : ℝ) 1) : n = 0 := by
  have h₃ : (n : ℝ) < 1 := by
    linarith [h₁.1, h₂.2]
  have h₄ : (-1 : ℝ) < n := by
    linarith [h₁.2, h₂.1]
  have h₅ : n < 1 := by
    exact_mod_cast h₃
  have h₆ : -1 < n := by
    exact_mod_cast h₄
  omega

private lemma eq_one_of_smul_mem_parabolicDomain {t : ℝ}
    (h : (siegelParabolic (Fin 2) ℤ).map integralTransformation) {a : SiegelUpperHalfSpace (Fin 2)}
    (ha : a ∈ parabolicDomain t) (hb : h • a ∈ parabolicDomain t) : h = 1 := by
  rcases h with ⟨_, p, hp, rfl⟩
  rcases exists_eq_symTranslation_mul_levi hp with ⟨S, hS, U, rfl⟩
  have e (τ : SiegelUpperHalfSpace (Fin 2)) :
      integralTransformation (symTranslation S hS * levi (Fin 2) ℤ U) • τ =
        SymplecticGroup.map (Int.castRingHom ℝ) (symTranslation S hS) • leviR U • τ := by
    rw [integralTransformation_smul, map_mul, mul_smul]
  have hb' : SymplecticGroup.map (Int.castRingHom ℝ) (symTranslation S hS) • leviR U • a ∈
      parabolicDomain t := by
    rw [← e]
    exact hb
  by_cases hU : U = 1 ∨ U = -1
  · rw [leviR_smul_of_eq_one_or U hU] at hb'
    have h₀ : S 0 0 = 0 := by
      refine eq_zero_of_mem_Ico ha.1 ?_
      rw [← re_map_symTranslation_smul S hS]
      exact hb'.1
    have h₁ : S 0 1 = 0 := by
      refine eq_zero_of_mem_Ico ha.2.1 ?_
      rw [← re_map_symTranslation_smul S hS]
      exact hb'.2.1
    have h₂ : S 1 1 = 0 := by
      refine eq_zero_of_mem_Ico ha.2.2.1 ?_
      have h₃ : ((SymplecticGroup.map (Int.castRingHom ℝ) (symTranslation S hS) • a).val 1 1).re -
          t ∈ Ico (0 : ℝ) 1 :=
        hb'.2.2.1
      rw [re_map_symTranslation_smul] at h₃
      convert h₃ using 1
      ring1
    have h₃ : S 1 0 = S 0 1 := congrFun (congrFun hS 0) 1
    refine Subtype.ext (Subtype.ext (Equiv.ext fun τ ↦ ?_))
    refine (e τ).trans ?_
    rw [leviR_smul_of_eq_one_or U hU]
    refine SiegelUpperHalfSpace.ext ?_
    ext i j
    rw [val_map_symTranslation_smul]
    fin_cases i <;> fin_cases j <;> simp [h₀, h₁, h₂, h₃]
  · rw [not_or] at hU
    have h₁ : parabolicWeight a < parabolicWeight (leviR U • a) := ha.2.2.2 U hU.1 hU.2
    have h₂ : parabolicWeight (SymplecticGroup.map (Int.castRingHom ℝ) (symTranslation S hS) •
        leviR U • a) < parabolicWeight (leviR U⁻¹ • SymplecticGroup.map (Int.castRingHom ℝ)
          (symTranslation S hS) • leviR U • a) :=
      hb'.2.2.2 U⁻¹ (fun h ↦ hU.1 (inv_eq_one.mp h)) fun h ↦ hU.2 (by
        rw [← inv_inv U, h, inv_neg, inv_one])
    have h₃ : parabolicWeight (SymplecticGroup.map (Int.castRingHom ℝ) (symTranslation S hS) •
        leviR U • a) = parabolicWeight (leviR U • a) :=
      parabolicWeight_congr (im_map_symTranslation_smul S hS)
    have h₄ : parabolicWeight (SymplecticGroup.map (Int.castRingHom ℝ) (levi (Fin 2) ℤ U⁻¹) •
        SymplecticGroup.map (Int.castRingHom ℝ) (symTranslation S hS) • leviR U • a) =
          parabolicWeight (leviR U⁻¹ • leviR U • a) :=
      parabolicWeight_leviR_smul_congr U⁻¹ (im_map_symTranslation_smul S hS)
    have h₅ : leviR U⁻¹ • leviR U • a = a := by
      rw [← mul_smul, ← leviR_mul, inv_mul_cancel, leviR_one, one_smul]
    rw [h₃, h₄, h₅] at h₂
    exact absurd h₁ (not_lt.mpr h₂.le)

/-- **`parabolicDomain t` is a fundamental domain of the Siegel parabolic subgroup of `Sp(4, ℤ)`**,
acting on `ℋ₂`, for every `t`. -/
lemma isFundamentalDomain_parabolicDomain (t : ℝ) :
    IsFundamentalDomain ((siegelParabolic (Fin 2) ℤ).map integralTransformation)
      (parabolicDomain t) (invariantMeasure (Fin 2)) where
  nullMeasurableSet := (measurableSet_parabolicDomain t).nullMeasurableSet
  ae_covers := by
    filter_upwards [ae_parabolicWeight_ne] with Z hZ
    rcases exists_forall_parabolicWeight_le Z with ⟨V, hV⟩
    have hZ₁ (U : GL (Fin 2) ℤ) (h₁ : U ≠ 1) (h₂ : U ≠ -1) :
        parabolicWeight (leviR V • Z) < parabolicWeight (leviR U • leviR V • Z) := by
      refine lt_of_le_of_ne ?_ (hZ U V h₁ h₂).symm
      have h₃ : parabolicWeight (leviR V • Z) ≤ parabolicWeight (leviR (U * V) • Z) := hV (U * V)
      rwa [leviR_mul, mul_smul] at h₃
    generalize hZ₂ : leviR V • Z = Z₁ at hZ₁
    let S : Matrix (Fin 2) (Fin 2) ℤ := !![-⌊(Z₁.val 0 0).re⌋, -⌊(Z₁.val 0 1).re⌋;
      -⌊(Z₁.val 0 1).re⌋, -⌊(Z₁.val 1 1).re - t⌋]
    have hS : Sᵀ = S := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    refine ⟨⟨_, _, symTranslation_mul_levi_mem S hS V, rfl⟩, ?_⟩
    have e : (⟨_, _, symTranslation_mul_levi_mem S hS V, rfl⟩ :
        (siegelParabolic (Fin 2) ℤ).map integralTransformation) • Z =
          SymplecticGroup.map (Int.castRingHom ℝ) (symTranslation S hS) • Z₁ := by
      rw [← hZ₂, ← mul_smul, ← map_mul]
      rfl
    rw [e]
    have hfract (x : ℝ) : x + ((-⌊x⌋ : ℤ) : ℝ) ∈ Ico (0 : ℝ) 1 := by
      have h₁ : x + ((-⌊x⌋ : ℤ) : ℝ) = Int.fract x := by
        rw [Int.cast_neg, Int.fract, sub_eq_add_neg]
      rw [h₁]
      exact ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
    refine ⟨?_, ?_, ?_, fun U h₁ h₂ ↦ ?_⟩
    · rw [re_map_symTranslation_smul]
      exact hfract _
    · rw [re_map_symTranslation_smul]
      exact hfract _
    · rw [re_map_symTranslation_smul]
      convert hfract ((Z₁.val 1 1).re - t) using 1
      simp only [S, of_apply, cons_val_one, cons_val_fin_one]
      ring1
    · rw [parabolicWeight_congr (im_map_symTranslation_smul S hS),
        parabolicWeight_leviR_smul_congr U (im_map_symTranslation_smul S hS)]
      exact hZ₁ U h₁ h₂
  aedisjoint g₁ g₂ hne := by
    refine Disjoint.aedisjoint (Set.disjoint_left.mpr ?_)
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hba : (g₂⁻¹ * g₁) • a = b := by
      rw [mul_smul, inv_smul_eq_iff]
      exact hab.symm
    refine hne ?_
    have h₁ : g₂⁻¹ * g₁ = 1 := eq_one_of_smul_mem_parabolicDomain (g₂⁻¹ * g₁) ha (hba ▸ hb)
    rwa [inv_mul_eq_one, eq_comm] at h₁

/-- **The translation `T_u` translates the box of `parabolicDomain`**, so that `T_u` maps
`parabolicDomain 0` to a fundamental domain of the Siegel parabolic subgroup. -/
lemma cornerTranslation_smul_parabolicDomain (u : ℝ) :
    cornerTranslation u • parabolicDomain 0 = parabolicDomain u := by
  have hweight (τ : SiegelUpperHalfSpace (Fin 2)) (v : ℝ) (U : GL (Fin 2) ℤ) :
      parabolicWeight (leviR U • cornerTranslation v • τ) = parabolicWeight (leviR U • τ) :=
    parabolicWeight_leviR_smul_congr U (im_cornerTranslation_smul v τ)
  have hweight₀ (τ : SiegelUpperHalfSpace (Fin 2)) (v : ℝ) :
      parabolicWeight (cornerTranslation v • τ) = parabolicWeight τ :=
    parabolicWeight_congr (im_cornerTranslation_smul v τ)
  have hre (τ : SiegelUpperHalfSpace (Fin 2)) (v : ℝ) (i j : Fin 2) :
      ((cornerTranslation v • τ).val i j).re = (τ.val i j).re + if i = 1 ∧ j = 1 then v else 0 := by
    rw [val_cornerTranslation_smul]
    split_ifs <;> simp
  ext Z
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨?_, ?_, ?_, fun U h₁ h₂ ↦ ?_⟩
    · simpa [hre] using ha.1
    · simpa [hre] using ha.2.1
    · simpa [hre] using ha.2.2.1
    · rw [hweight₀]
      exact (ha.2.2.2 U h₁ h₂).trans_eq (hweight a u U).symm
  · intro hZ
    have hinv : cornerTranslation u • cornerTranslation (-u) • Z = Z := by
      refine SiegelUpperHalfSpace.ext ?_
      ext i j
      rw [val_cornerTranslation_smul, val_cornerTranslation_smul]
      split_ifs <;> simp
    refine ⟨cornerTranslation (-u) • Z, ⟨?_, ?_, ?_, fun U h₁ h₂ ↦ ?_⟩, hinv⟩
    · simpa [hre] using hZ.1
    · simpa [hre] using hZ.2.1
    · have h₁ := hZ.2.2.1
      simp only [hre]
      simpa [sub_eq_add_neg] using h₁
    · rw [hweight₀]
      exact (hZ.2.2.2 U h₁ h₂).trans_eq (hweight Z (-u) U).symm

end SiegelUpperHalfSpace
