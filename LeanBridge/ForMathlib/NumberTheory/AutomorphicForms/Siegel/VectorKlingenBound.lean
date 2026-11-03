import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.VectorKlingenTerm
import Mathlib.Algebra.Module.ZLattice.Summable

/-!
# The estimates for the vector-valued Klingen–Eisenstein series of degree 2

Let `f` be a function on the upper half-plane with `|f(τ)| ≤ C (Im τ)^(-(k + j) / 2)`, such as a
cusp form of weight `k + j` on `SL(2, ℤ)`, `δ = (A, B; C, D) ∈ Sp(4, ℤ)` and `M = CZ + D` for
`Z ∈ ℋ₂`. The first column of `M⁻¹` is `s / det M` for `s = (M₁₁, -M₁₀)`, and
`Im (δZ)₀₀ = sᴴ (Im Z) s / |det M|²`. So the term `f((δZ)₀₀) ρ_{k,j}(M)⁻¹ e₁^j` of the
Klingen–Eisenstein series is, through a linear form `φ` on `Sym^j(ℂ²)`, at most
`C C_φ r^(-(k + j)) ‖s‖^j` for `r = √(sᴴ (Im Z) s)`, the powers of `|det M|` cancelling. With
`λ = √(det Im Z / tr Im Z)`, `λ ‖s‖ ≤ r`, so this is at most `C C_φ λ^(-j) r^(-k)`. Since
`(M₁₀, M₁₁)` is `cZ + d` for the last row `(c, d)` of `δ`, whose imaginary part determines `c` and
then whose real part determines `d`, `‖(c, d)‖ ≤ K ‖s‖` for an explicit `K`, which gives the
estimate `C C_φ λ^(-j) (K / λ)^k ‖(c, d)‖^(-k)` by the last row, whose sum over `ℤ⁴` converges for
`k > 4`.

## Main definitions

* `SiegelUpperHalfSpace.hermForm`: the Hermitian form `sᴴ Y s` of a real symmetric matrix `Y`.
* `SiegelUpperHalfSpace.klingenVec`: the vector `s = (M₁₁, -M₁₀)`.
* `SiegelUpperHalfSpace.dualBound`: the constant `C_φ`, with `|φ(u^j)| ≤ C_φ ‖u‖^j`.
* `SiegelUpperHalfSpace.imLam`, `SiegelUpperHalfSpace.imK`: the constants `λ` and `K`.
* `SiegelUpperHalfSpace.klingenRadius`: the number `r = √(sᴴ (Im Z) s)`.
* `SiegelUpperHalfSpace.klingenConst`: the constant `λ^(-j) (K / λ)^k`.

## Main results

* `SiegelUpperHalfSpace.det_div_trace_mul_le_hermForm`: the lower bound of a positive definite form.
* `SiegelUpperHalfSpace.im_topLeft_smul_mul_normSq`: `Im (gZ)₀₀ |det M|² = sᴴ (Im Z) s`.
* `SiegelUpperHalfSpace.imLam_mul_norm_le_sqrt_hermForm`: `λ ‖s‖ ≤ r`.
* `SiegelUpperHalfSpace.norm_bottomRow_le`: `‖(c, d)‖ ≤ K ‖s‖`.
* `SiegelUpperHalfSpace.norm_dual_vectorKlingenTerm_le_radius`,
  `SiegelUpperHalfSpace.norm_dual_vectorKlingenTerm_le`: the estimates of the terms.
* `SiegelUpperHalfSpace.summable_norm_rpow_int`: `∑_{x ∈ ℤ^ι} ‖x‖^r` converges for `r < -|ι|`.
-/

open Complex Module

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open scoped MatrixGroups TensorProduct UpperHalfPlane

namespace SiegelUpperHalfSpace

open SymplecticGroup

variable (Y : Matrix (Fin 2) (Fin 2) ℝ) (s : Fin 2 → ℂ)

/-- The Hermitian form `sᴴ Y s` of a real symmetric `2 × 2` matrix `Y`. -/
noncomputable def hermForm : ℝ :=
  Y 0 0 * normSq (s 0) + Y 1 1 * normSq (s 1) +
    2 * Y 0 1 * ((s 0).re * (s 1).re + (s 0).im * (s 1).im)

lemma hermForm_smul (c : ℂ) : hermForm Y (c • s) = normSq c * hermForm Y s := by
  simp only [hermForm, Pi.smul_apply, smul_eq_mul, mul_re, mul_im, normSq_apply]
  ring1

lemma star_dotProduct_mulVec_eq_hermForm (hY : Y 1 0 = Y 0 1) :
    star s ⬝ᵥ (Y.map ofReal *ᵥ s) = (hermForm Y s : ℂ) := by
  apply Complex.ext
  · simp only [dotProduct, mulVec, Fin.sum_univ_two, map_apply, hY, hermForm, normSq_apply]
    simp
    ring1
  · simp only [dotProduct, mulVec, Fin.sum_univ_two, map_apply, hY]
    simp
    ring1

variable {Y}

/-- **The lower bound of a positive definite form**:
`(det Y / tr Y) (|s₀|² + |s₁|²) ≤ sᴴ Y s`, since
`(tr Y) sᴴ Y s - (det Y) sᴴ s = ‖Y Re s‖² + ‖Y Im s‖²`. -/
lemma det_div_trace_mul_le_hermForm (h₀ : 0 < Y 0 0 + Y 1 1) (hY : Y 1 0 = Y 0 1) :
    (Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0) / (Y 0 0 + Y 1 1) * (normSq (s 0) + normSq (s 1)) ≤
      hermForm Y s := by
  rw [div_mul_eq_mul_div, div_le_iff₀ h₀]
  simp only [hermForm, normSq_apply, hY]
  nlinarith [sq_nonneg (Y 0 0 * (s 0).re + Y 0 1 * (s 1).re),
    sq_nonneg (Y 0 1 * (s 0).re + Y 1 1 * (s 1).re),
    sq_nonneg (Y 0 0 * (s 0).im + Y 0 1 * (s 1).im),
    sq_nonneg (Y 0 1 * (s 0).im + Y 1 1 * (s 1).im)]

variable (Z : SiegelUpperHalfSpace (Fin 2)) (g : symplecticGroup (Fin 2) ℝ)

private lemma sub_conjTranspose_eq {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : Mᵀ = M) :
    M - Mᴴ = (2 * I) • (M.map im).map ofReal := by
  ext i j
  have h : M j i = M i j := by rw [← transpose_apply M i j, hM]
  simp only [Matrix.sub_apply, conjTranspose_apply, h, Matrix.smul_apply, map_apply]
  rw [star_def, sub_conj]
  push_cast
  ring1

private lemma map_im_smul : ((g • Z).val.map im).map ofReal =
    (denom g Z.val)⁻¹ᴴ * (Z.val.map im).map ofReal * (denom g Z.val)⁻¹ := by
  have e : (denom g Z.val)⁻¹ᴴ * (denom g Z.val)ᴴ = 1 := by
    rw [← conjTranspose_mul, mul_nonsing_inv _ (isUnit_det_denom g Z), conjTranspose_one]
  have h : (2 * I) • ((g • Z).val.map im).map ofReal =
      (2 * I) • ((denom g Z.val)⁻¹ᴴ * (Z.val.map im).map ofReal * (denom g Z.val)⁻¹) := by
    rw [← sub_conjTranspose_eq (g • Z).transpose_val, val_smul, ← Matrix.smul_mul,
      ← Matrix.mul_smul, ← sub_conjTranspose_eq Z.transpose_val,
      ← conjTranspose_denom_mul_num_sub g Z.val]
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, e, Matrix.one_mul,
      mul_nonsing_inv_cancel_right _ _ (isUnit_det_denom g Z), conjTranspose_mul]
  exact smul_right_injective _ (by simp) h

/-- The vector `s = (M₁₁, -M₁₀)`, for `M = CZ + D`, the numerator of the first column
`(CZ + D)⁻¹ e₁ = s / det(CZ + D)`. -/
noncomputable def klingenVec : Fin 2 → ℂ :=
  ![denom g Z.val 1 1, -denom g Z.val 1 0]

lemma inv_denom_mulVec_single : (denom g Z.val)⁻¹ *ᵥ (Pi.single 0 1 : Fin 2 → ℂ) =
    ((denom g Z.val).det)⁻¹ • klingenVec Z g := by
  rw [Matrix.inv_def, adjugate_fin_two, Ring.inverse_eq_inv']
  ext i
  fin_cases i <;> simp [klingenVec, mulVec, dotProduct]

private lemma transpose_im_eq : (Z.val.map im) 1 0 = (Z.val.map im) 0 1 := by
  have h : Z.val 1 0 = Z.val 0 1 :=
    congrFun (congrFun Z.transpose_val 0) 1
  simp [h]

/-- The imaginary part of the upper-left entry of `gZ`:
`Im (gZ)₀₀ |det(CZ + D)|² = sᴴ (Im Z) s`, for `s = (M₁₁, -M₁₀)` and `M = CZ + D`. -/
lemma im_topLeft_smul_mul_normSq : (topLeft (g • Z)).im * normSq (denom g Z.val).det =
    hermForm (Z.val.map im) (klingenVec Z g) := by
  have hD : normSq (denom g Z.val).det ≠ 0 :=
    normSq_eq_zero.not.mpr (isUnit_det_denom g Z).ne_zero
  have h₀ : (((g • Z).val.map im).map ofReal) 0 0 =
      ((denom g Z.val)⁻¹ᴴ * (Z.val.map im).map ofReal * (denom g Z.val)⁻¹) 0 0 :=
    congrFun (congrFun (map_im_smul Z g) 0) 0
  have h₁ : ((denom g Z.val)⁻¹ᴴ * (Z.val.map im).map ofReal * (denom g Z.val)⁻¹) 0 0 =
      star ((denom g Z.val)⁻¹ *ᵥ (Pi.single 0 1 : Fin 2 → ℂ)) ⬝ᵥ
        ((Z.val.map im).map ofReal *ᵥ ((denom g Z.val)⁻¹ *ᵥ (Pi.single 0 1 : Fin 2 → ℂ))) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply, dotProduct, mulVec,
      Pi.star_apply, Pi.single_eq_same, Pi.single_eq_of_ne, ne_eq, one_ne_zero, not_false_eq_true,
      mul_one, mul_zero, add_zero]
    ring1
  rw [h₁, star_dotProduct_mulVec_eq_hermForm _ _ (transpose_im_eq Z), inv_denom_mulVec_single,
    hermForm_smul, map_inv₀] at h₀
  have h₂ : (topLeft (g • Z)).im = (normSq (denom g Z.val).det)⁻¹ *
      hermForm (Z.val.map im) (klingenVec Z g) :=
    ofReal_injective h₀
  rw [h₂, mul_comm, ← mul_assoc, mul_inv_cancel₀ hD, one_mul]

variable {j : ℕ} (φ : Dual ℂ (Sym[ℂ]^j (Fin 2 → ℂ)))

/-- The constant `C_φ = ∑_r |φ(e_{r₁} ⋯ e_{r_j})|`, with `|φ(u^j)| ≤ C_φ ‖u‖^j`. -/
noncomputable def dualBound : ℝ :=
  ∑ r : Fin j → Fin 2, ‖φ (⨂ₛ[ℂ] i, Pi.single (r i) 1)‖

lemma dualBound_nonneg : 0 ≤ dualBound φ :=
  Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

lemma norm_dual_tprod_le (u : Fin 2 → ℂ) : ‖φ (⨂ₛ[ℂ] _ : Fin j, u)‖ ≤ dualBound φ * ‖u‖ ^ j := by
  have h : φ (⨂ₛ[ℂ] _ : Fin j, 1 *ᵥ u) = ∑ r : Fin j → Fin 2, (∏ i, (1 *ᵥ u) (r i)) *
      φ (⨂ₛ[ℂ] i, Pi.single (r i) 1) :=
    dual_tprod_mulVec φ 1 (fun _ : Fin j ↦ u)
  simp only [one_mulVec] at h
  rw [h, dualBound, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ ↦ ?_)
  rw [norm_mul, norm_prod, mul_comm]
  refine mul_le_mul_of_nonneg_left ((Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
    fun i _ ↦ norm_le_pi_norm u (r i)).trans_eq ?_) (norm_nonneg _)
  simp

/-- The constant `√(det Im Z / tr Im Z)`, with `(√(det Im Z / tr Im Z) ‖s‖)² ≤ sᴴ (Im Z) s`. -/
noncomputable def imLam (W : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  √(((W 0 0).im * (W 1 1).im - (W 0 1).im * (W 1 0).im) / ((W 0 0).im + (W 1 1).im))

/-- The constant `K` with `‖(c, d)‖ ≤ K ‖cW + d‖` for real row vectors `c`, `d`, in terms of the
entries of the real and imaginary parts of `W`. -/
noncomputable def imK (W : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  1 + (1 + (|(W 0 0).re| + |(W 0 1).re| + |(W 1 1).re|)) *
    ((|(W 0 0).im| + |(W 0 1).im| + |(W 1 1).im|) /
      ((W 0 0).im * (W 1 1).im - (W 0 1).im * (W 1 0).im))

lemma det_im_pos : 0 < (Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im * (Z.val 1 0).im := by
  simpa [det_fin_two] using Z.posDef_im.det_pos

lemma imLam_pos : 0 < imLam Z.val :=
  Real.sqrt_pos.mpr (div_pos (det_im_pos Z) (add_pos (im_zero_zero_pos Z) (im_one_one_pos Z)))

lemma imK_pos : 0 < imK Z.val :=
  add_pos_of_pos_of_nonneg one_pos (mul_nonneg (by positivity)
    (div_nonneg (by positivity) (det_im_pos Z).le))

/-- **`λ ‖s‖ ≤ √(sᴴ (Im Z) s)`** for `λ = √(det Im Z / tr Im Z)`. -/
lemma imLam_mul_norm_le_sqrt_hermForm : imLam Z.val * ‖s‖ ≤ √(hermForm (Z.val.map im) s) := by
  have h₀ : 0 < (Z.val 0 0).im + (Z.val 1 1).im :=
    add_pos (im_zero_zero_pos Z) (im_one_one_pos Z)
  have h₁ : _ ≤ hermForm (Z.val.map im) s :=
    det_div_trace_mul_le_hermForm s (by simpa using h₀) (transpose_im_eq Z)
  have hs : ‖s‖ ^ 2 ≤ normSq (s 0) + normSq (s 1) := by
    have h₂ : ‖s‖ ≤ √(normSq (s 0) + normSq (s 1)) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i ↦ ?_
      refine Real.le_sqrt_of_sq_le ?_
      rw [Complex.sq_norm]
      fin_cases i
      · exact le_add_of_nonneg_right (normSq_nonneg _)
      · exact le_add_of_nonneg_left (normSq_nonneg _)
    exact (Real.le_sqrt (norm_nonneg _) (add_nonneg (normSq_nonneg _) (normSq_nonneg _))).mp h₂
  refine Real.le_sqrt_of_sq_le ?_
  rw [mul_pow, imLam, Real.sq_sqrt (div_nonneg (det_im_pos Z).le h₀.le)]
  refine (mul_le_mul_of_nonneg_left hs (div_nonneg (det_im_pos Z).le h₀.le)).trans ?_
  simpa using h₁

private lemma abs_le_div_mul_of_mul_eq {t u v p q d μ A : ℝ} (hd : 0 < d) (hμ : 0 ≤ μ)
    (ht : t * d = p * u - q * v) (hu : |u| ≤ μ) (hv : |v| ≤ μ) (hA : |p| + |q| ≤ A) :
    |t| ≤ A / d * μ := by
  rw [div_mul_eq_mul_div, le_div_iff₀ hd]
  have h : |t| * d = |p * u - q * v| := by
    rw [← ht, abs_mul, abs_of_pos hd]
  rw [h]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul]
  nlinarith [abs_nonneg p, abs_nonneg q, mul_le_mul_of_nonneg_left hu (abs_nonneg p),
    mul_le_mul_of_nonneg_left hv (abs_nonneg q)]

private lemma abs_coord_le {c₀ c₁ d₀ d₁ : ℝ} {z₀₀ z₀₁ z₁₁ : ℂ} {μ : ℝ}
    (h₀ : ‖(c₀ : ℂ) * z₀₀ + c₁ * z₀₁ + d₀‖ ≤ μ) (h₁ : ‖(c₀ : ℂ) * z₀₁ + c₁ * z₁₁ + d₁‖ ≤ μ)
    (hd : 0 < z₀₀.im * z₁₁.im - z₀₁.im * z₀₁.im) {t : ℝ} (ht : t ∈ ({c₀, c₁, d₀, d₁} : Set ℝ)) :
    |t| ≤ (1 + (1 + (|z₀₀.re| + |z₀₁.re| + |z₁₁.re|)) *
      ((|z₀₀.im| + |z₀₁.im| + |z₁₁.im|) / (z₀₀.im * z₁₁.im - z₀₁.im * z₀₁.im))) * μ := by
  have hμ : 0 ≤ μ := (norm_nonneg _).trans h₀
  have him₀ : |c₀ * z₀₀.im + c₁ * z₀₁.im| ≤ μ := by
    refine le_trans (le_of_eq ?_) ((abs_im_le_norm _).trans h₀)
    simp
  have him₁ : |c₀ * z₀₁.im + c₁ * z₁₁.im| ≤ μ := by
    refine le_trans (le_of_eq ?_) ((abs_im_le_norm _).trans h₁)
    simp
  have hre₀ : |c₀ * z₀₀.re + c₁ * z₀₁.re + d₀| ≤ μ := by
    refine le_trans (le_of_eq ?_) ((abs_re_le_norm _).trans h₀)
    simp
  have hre₁ : |c₀ * z₀₁.re + c₁ * z₁₁.re + d₁| ≤ μ := by
    refine le_trans (le_of_eq ?_) ((abs_re_le_norm _).trans h₁)
    simp
  have hc₀ : |c₀| ≤ (|z₀₀.im| + |z₀₁.im| + |z₁₁.im|) / (z₀₀.im * z₁₁.im - z₀₁.im * z₀₁.im) * μ :=
    abs_le_div_mul_of_mul_eq hd hμ (p := z₁₁.im) (q := z₀₁.im) (by ring1) him₀ him₁ <| by
      linarith [abs_nonneg z₀₀.im]
  have hc₁ : |c₁| ≤ (|z₀₀.im| + |z₀₁.im| + |z₁₁.im|) / (z₀₀.im * z₁₁.im - z₀₁.im * z₀₁.im) * μ :=
    abs_le_div_mul_of_mul_eq hd hμ (p := z₀₀.im) (q := z₀₁.im) (by ring1) him₁ him₀ <| by
      linarith [abs_nonneg z₁₁.im]
  generalize (|z₀₀.im| + |z₀₁.im| + |z₁₁.im|) / (z₀₀.im * z₁₁.im - z₀₁.im * z₀₁.im) = T at hc₀ hc₁ ⊢
  have hTμ : 0 ≤ T * μ := (abs_nonneg _).trans hc₀
  have hS : 0 ≤ |z₀₀.re| + |z₀₁.re| + |z₁₁.re| := by positivity
  have hx₀ : |c₀ * z₀₀.re| ≤ T * μ * |z₀₀.re| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hc₀ (abs_nonneg _)
  have hx₁ : |c₁ * z₀₁.re| ≤ T * μ * |z₀₁.re| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hc₁ (abs_nonneg _)
  have hx₂ : |c₀ * z₀₁.re| ≤ T * μ * |z₀₁.re| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hc₀ (abs_nonneg _)
  have hx₃ : |c₁ * z₁₁.re| ≤ T * μ * |z₁₁.re| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hc₁ (abs_nonneg _)
  have hK : (1 + (1 + (|z₀₀.re| + |z₀₁.re| + |z₁₁.re|)) * T) * μ =
      μ + T * μ + T * μ * (|z₀₀.re| + |z₀₁.re| + |z₁₁.re|) := by
    ring1
  rw [hK]
  rcases ht with rfl | rfl | rfl | rfl
  · nlinarith [mul_nonneg hTμ hS]
  · nlinarith [mul_nonneg hTμ hS]
  · rw [abs_le] at hre₀ hx₀ hx₁ ⊢
    constructor <;> nlinarith [mul_nonneg hTμ (abs_nonneg z₀₀.re),
      mul_nonneg hTμ (abs_nonneg z₀₁.re), mul_nonneg hTμ (abs_nonneg z₁₁.re)]
  · rw [abs_le] at hre₁ hx₂ hx₃ ⊢
    constructor <;> nlinarith [mul_nonneg hTμ (abs_nonneg z₀₀.re),
      mul_nonneg hTμ (abs_nonneg z₀₁.re), mul_nonneg hTμ (abs_nonneg z₁₁.re)]

/-- **The last row of `δ` is bounded by `s = (M₁₁, -M₁₀)`**, for `M = CZ + D`: `‖(c, d)‖ ≤ K ‖s‖`,
the imaginary part of `cZ + d` determining `c` and then its real part `d`. -/
lemma norm_bottomRow_le (δ : symplecticGroup (Fin 2) ℤ) :
    ‖bottomRow δ‖ ≤ imK Z.val * ‖klingenVec Z (SymplecticGroup.map (Int.castRingHom ℝ) δ)‖ := by
  have hZ : Z.val 1 0 = Z.val 0 1 :=
    congrFun (congrFun Z.transpose_val 0) 1
  have h₀ : denom (SymplecticGroup.map (Int.castRingHom ℝ) δ) Z.val 1 0 =
      ((δ.1 (.inr 1) (.inl 0) : ℝ) : ℂ) * Z.val 0 0 +
        ((δ.1 (.inr 1) (.inl 1) : ℝ) : ℂ) * Z.val 0 1 + ((δ.1 (.inr 1) (.inr 0) : ℝ) : ℂ) := by
    simp [denom, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, hZ]
  have h₁ : denom (SymplecticGroup.map (Int.castRingHom ℝ) δ) Z.val 1 1 =
      ((δ.1 (.inr 1) (.inl 0) : ℝ) : ℂ) * Z.val 0 1 +
        ((δ.1 (.inr 1) (.inl 1) : ℝ) : ℂ) * Z.val 1 1 + ((δ.1 (.inr 1) (.inr 1) : ℝ) : ℂ) := by
    simp [denom, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply]
  have hn₀ : ‖denom (SymplecticGroup.map (Int.castRingHom ℝ) δ) Z.val 1 0‖ ≤
      ‖klingenVec Z (SymplecticGroup.map (Int.castRingHom ℝ) δ)‖ := by
    simpa [klingenVec] using
      norm_le_pi_norm (klingenVec Z (SymplecticGroup.map (Int.castRingHom ℝ) δ)) 1
  have hn₁ : ‖denom (SymplecticGroup.map (Int.castRingHom ℝ) δ) Z.val 1 1‖ ≤
      ‖klingenVec Z (SymplecticGroup.map (Int.castRingHom ℝ) δ)‖ := by
    simpa [klingenVec] using
      norm_le_pi_norm (klingenVec Z (SymplecticGroup.map (Int.castRingHom ℝ) δ)) 0
  have hd : 0 < (Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im * (Z.val 0 1).im := by
    simpa [hZ] using det_im_pos Z
  rw [h₀] at hn₀
  rw [h₁] at hn₁
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (imK_pos Z).le (norm_nonneg _))).mpr fun i ↦ ?_
  have hi : |((bottomRow δ i : ℤ) : ℝ)| ≤ imK Z.val *
      ‖klingenVec Z (SymplecticGroup.map (Int.castRingHom ℝ) δ)‖ := by
    rw [imK, hZ]
    refine abs_coord_le hn₀ hn₁ hd ?_
    rcases i with i | i <;> fin_cases i <;> simp [bottomRow]
  simpa [Int.norm_eq_abs] using hi

private lemma bound_aux {C D A r L n : ℝ} (hA : 0 < A) (hr : 0 < r) (hL : 0 < L) (hn : 0 ≤ n)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hnr : L * n ≤ r) (k : ℤ) :
    C / (r / A) ^ (k + j) * (A ^ (-k) * (A⁻¹ ^ j * (D * n ^ j))) ≤
      C * D * L ^ (-(j : ℤ)) * r ^ (-k) := by
  have hn' : n ^ j ≤ (r / L) ^ j :=
    pow_le_pow_left₀ hn ((le_div_iff₀ hL).mpr (by linarith)) j
  have e : C / (r / A) ^ (k + j) * (A ^ (-k) * (A⁻¹ ^ j * (D * (r / L) ^ j))) =
      C * D * L ^ (-(j : ℤ)) * r ^ (-k) := by
    rw [div_zpow, zpow_add₀ hr.ne', zpow_add₀ hA.ne', zpow_natCast, zpow_natCast, div_pow,
      zpow_neg A, zpow_neg r, zpow_neg L, zpow_natCast, inv_pow]
    field_simp
  rw [← e]
  gcongr

variable (k : ℤ) (f : ℍ → ℂ) (δ : symplecticGroup (Fin 2) ℤ)

/-- The number `√(sᴴ (Im Z) s)` for `s = (M₁₁, -M₁₀)`, `M = CZ + D`, in terms of which the terms of
the Klingen–Eisenstein series are estimated. -/
noncomputable def klingenRadius : ℝ :=
  √(hermForm (Z.val.map im) (klingenVec Z (SymplecticGroup.map (Int.castRingHom ℝ) δ)))

lemma sqrt_im_topLeft_smul : √(topLeft (g • Z)).im =
    √(hermForm (Z.val.map im) (klingenVec Z g)) / ‖(denom g Z.val).det‖ := by
  have hD : 0 < ‖(denom g Z.val).det‖ :=
    norm_pos_iff.mpr (isUnit_det_denom g Z).ne_zero
  rw [← im_topLeft_smul_mul_normSq, Real.sqrt_mul (topLeft (g • Z)).im_pos.le, normSq_eq_norm_sq,
    Real.sqrt_sq hD.le, mul_div_cancel_right₀ _ hD.ne']

lemma hermForm_klingenVec_pos : 0 < hermForm (Z.val.map im) (klingenVec Z g) := by
  rw [← im_topLeft_smul_mul_normSq]
  exact mul_pos (topLeft (g • Z)).im_pos (normSq_pos.mpr (isUnit_det_denom g Z).ne_zero)

lemma klingenRadius_pos : 0 < klingenRadius Z δ :=
  Real.sqrt_pos.mpr (hermForm_klingenVec_pos Z _)

variable {C : ℝ} {k f}

/-- **The estimate of the terms of the Klingen–Eisenstein series**: if
`|f(τ)| ≤ C (Im τ)^(-(k + j) / 2)`, then for every linear form `φ` on `Sym^j(ℂ²)`,
`|φ(t_δ(Z))| ≤ C C_φ λ^(-j) r^(-k)`, for `r = √(sᴴ (Im Z) s)`, `s = (M₁₁, -M₁₀)`, `M = CZ + D`, and
`λ = √(det Im Z / tr Im Z)`. -/
lemma norm_dual_vectorKlingenTerm_le_radius (hC : 0 ≤ C)
    (hf : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((k + j : ℤ) : ℝ) / 2)) : ‖φ (vectorKlingenTerm Z k j f δ)‖ ≤
    C * dualBound φ * imLam Z.val ^ (-(j : ℤ)) * klingenRadius Z δ ^ (-k) := by
  have hA : 0 < ‖(denom (SymplecticGroup.map (Int.castRingHom ℝ) δ) Z.val).det‖ :=
    norm_pos_iff.mpr (isUnit_det_denom _ Z).ne_zero
  have hy : 0 < (topLeft (SymplecticGroup.map (Int.castRingHom ℝ) δ • Z)).im :=
    (topLeft (SymplecticGroup.map (Int.castRingHom ℝ) δ • Z)).im_pos
  have hf₁ : ‖f (topLeft (SymplecticGroup.map (Int.castRingHom ℝ) δ • Z))‖ ≤ _ :=
    hf (topLeft (SymplecticGroup.map (Int.castRingHom ℝ) δ • Z))
  rw [Real.rpow_div_two_eq_sqrt _ hy.le, Real.rpow_intCast, sqrt_im_topLeft_smul] at hf₁
  have ht : φ (vectorKlingenTerm Z k j f δ) =
      f (topLeft (SymplecticGroup.map (Int.castRingHom ℝ) δ • Z)) *
        ((denom (SymplecticGroup.map (Int.castRingHom ℝ) δ) Z.val).det ^ (-k) *
          (((denom (SymplecticGroup.map (Int.castRingHom ℝ) δ) Z.val).det)⁻¹ ^ j *
            φ (⨂ₛ[ℂ] _ : Fin j, klingenVec Z (SymplecticGroup.map (Int.castRingHom ℝ) δ)))) := by
    rw [vectorKlingenTerm, rhoKJ_denomGL_inv_tprod, inv_denom_mulVec_single, tprod_smul, map_smul,
      map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  rw [ht, norm_mul, norm_mul, norm_mul, norm_zpow, norm_pow, norm_inv]
  refine (mul_le_mul hf₁ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (norm_dual_tprod_le φ _) (by positivity)) (by positivity)) (by positivity)
    (div_nonneg hC (zpow_nonneg (div_nonneg (Real.sqrt_nonneg _) hA.le) _))).trans ?_
  exact bound_aux hA (klingenRadius_pos Z δ) (imLam_pos Z) (norm_nonneg _) hC (dualBound_nonneg φ)
    (imLam_mul_norm_le_sqrt_hermForm _ Z) k

variable (k j) in
/-- The constant `λ^(-j) (K / λ)^k` of the estimate of the terms of the Klingen–Eisenstein
series. -/
noncomputable def klingenConst (W : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  imLam W ^ (-(j : ℤ)) * (imK W / imLam W) ^ k

lemma bottomRow_ne_zero : SymplecticGroup.bottomRow δ ≠ 0 := by
  intro h
  have e : (δ * δ⁻¹).1 (.inr 1) (.inr 1) = 1 := by
    rw [mul_inv_cancel]
    simp
  rw [Submonoid.coe_mul, Matrix.mul_apply] at e
  have h₀ (a : Fin 2 ⊕ Fin 2) : δ.1 (.inr 1) a = 0 :=
    congrFun h a
  simp [h₀] at e

lemma klingenRadius_zpow_le (hk : 0 < k) : klingenRadius Z δ ^ (-k) ≤
    (imK Z.val / imLam Z.val) ^ k * ‖SymplecticGroup.bottomRow δ‖ ^ (-k) := by
  have hL : 0 < imLam Z.val :=
    imLam_pos Z
  have hK : 0 < imK Z.val :=
    imK_pos Z
  have hℓ : 0 < ‖SymplecticGroup.bottomRow δ‖ :=
    norm_pos_iff.mpr (bottomRow_ne_zero δ)
  have h₁ : imLam Z.val * ‖SymplecticGroup.bottomRow δ‖ / imK Z.val ≤ klingenRadius Z δ := by
    rw [div_le_iff₀ hK]
    have h₂ : ‖SymplecticGroup.bottomRow δ‖ ≤
        imK Z.val * ‖klingenVec Z (SymplecticGroup.map (Int.castRingHom ℝ) δ)‖ :=
      norm_bottomRow_le Z δ
    have h₃ : imLam Z.val * ‖klingenVec Z (SymplecticGroup.map (Int.castRingHom ℝ) δ)‖ ≤
        klingenRadius Z δ :=
      imLam_mul_norm_le_sqrt_hermForm _ Z
    nlinarith
  have h₄ : (0 : ℝ) < imLam Z.val * ‖SymplecticGroup.bottomRow δ‖ / imK Z.val := by
    positivity
  have h₅ : (imLam Z.val * ‖SymplecticGroup.bottomRow δ‖ / imK Z.val) ^ k ≤ klingenRadius Z δ ^ k :=
    zpow_le_zpow_left₀ hk.le h₄.le h₁
  have h₆ : (klingenRadius Z δ ^ k)⁻¹ ≤
      ((imLam Z.val * ‖SymplecticGroup.bottomRow δ‖ / imK Z.val) ^ k)⁻¹ :=
    inv_anti₀ (zpow_pos h₄ k) h₅
  have e : (imLam Z.val * ‖SymplecticGroup.bottomRow δ‖ / imK Z.val)⁻¹ =
      imK Z.val / imLam Z.val * ‖SymplecticGroup.bottomRow δ‖⁻¹ := by
    field_simp
  rw [zpow_neg, zpow_neg, ← inv_zpow ‖SymplecticGroup.bottomRow δ‖, ← mul_zpow, ← e, inv_zpow]
  exact h₆

/-- **The estimate of the terms of the Klingen–Eisenstein series by the last row**:
`|φ(t_δ(Z))| ≤ C C_φ λ^(-j) (K / λ)^k ‖(c, d)‖^(-k)`, for `(c, d)` the last row of `δ`. -/
lemma norm_dual_vectorKlingenTerm_le (hC : 0 ≤ C)
    (hf : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((k + j : ℤ) : ℝ) / 2)) (hk : 0 < k) :
    ‖φ (vectorKlingenTerm Z k j f δ)‖ ≤ C * dualBound φ * klingenConst j k Z.val *
      ‖SymplecticGroup.bottomRow δ‖ ^ (-k) := by
  refine (norm_dual_vectorKlingenTerm_le_radius Z φ δ hC hf).trans ?_
  have h₁ : 0 ≤ C * dualBound φ * imLam Z.val ^ (-(j : ℤ)) :=
    mul_nonneg (mul_nonneg hC (dualBound_nonneg φ)) (zpow_nonneg (imLam_pos Z).le _)
  refine (mul_le_mul_of_nonneg_left (klingenRadius_zpow_le Z δ hk) h₁).trans_eq ?_
  rw [klingenConst]
  ring1

/-- **The lattice sum**: `∑_{x ∈ ℤ^ι} ‖x‖^r` converges for `r < -|ι|`. -/
lemma summable_norm_rpow_int {ι : Type*} [Fintype ι] {r : ℝ} (hr : r < -(Fintype.card ι : ℝ)) :
    Summable fun x : ι → ℤ ↦ ‖x‖ ^ r := by
  let L : Submodule ℤ (ι → ℝ) := Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))
  have hL : Module.finrank ℤ L = Fintype.card ι := by
    rw [ZLattice.rank ℝ L, Module.finrank_fintype_fun_eq_card]
  have hmem (x : ι → ℤ) : (fun i ↦ (x i : ℝ)) ∈ L := by
    refine ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ _).mpr fun i ↦ ?_
    simp
  have hs : Summable fun z : L ↦ ‖z‖ ^ r :=
    ZLattice.summable_norm_rpow L r (by rwa [hL])
  have hinj : Function.Injective fun x : ι → ℤ ↦ (⟨_, hmem x⟩ : L) := fun x y h ↦ funext fun i ↦
    Int.cast_injective (congrFun (congrArg Subtype.val h) i)
  refine (hs.comp_injective hinj).congr fun x ↦ ?_
  have hn : ‖(fun i ↦ (x i : ℝ) : ι → ℝ)‖ = ‖x‖ := by
    simp only [Pi.norm_def]
    exact congrArg _ (Finset.sup_congr rfl fun b _ ↦ NNReal.eq (Int.norm_cast_real (x b)))
  exact congrArg (· ^ r) hn

end SiegelUpperHalfSpace
