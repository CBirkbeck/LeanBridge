import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PluckerQuadricSum
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.VectorKlingenEisenstein

/-!
# Convergence of the Siegel Eisenstein series of degree 2

The Siegel Eisenstein series `ψ_k(Z) = ∑_{(C, D)} det(CZ + D)^{-k}` of degree `2`
(`SiegelUpperHalfSpace.siegelEisensteinSeries`, LMFDB `mf.siegel.eisenstein_series`) converges
absolutely for `k > 3`, the bound of the knowl, and it is a Siegel modular form of weight `k` on
`Sp(4, ℤ)`, with constant term `1`, for even `k`.

The bottom row `(C, D)` has the Plücker vector `p = (det C, c₁ ∧ d₂, c₂ ∧ d₂, c₂ ∧ d₁, det D) ∈ ℤ⁵`,
the remaining minor being `c₁ ∧ d₁ = -c₂ ∧ d₂`, as `C Dᵀ` is symmetric. The determinant is linear
in `p`: `det(CZ + D) = p₀ det Z + p₁ z₀₀ + 2 p₂ z₀₁ - p₃ z₁₁ + p₄`. For `Z = X + iY`, the matrix
`R = adj(CX + D) C` is symmetric, and the Plücker relation gives
`|det(CZ + D)|² = det(CX + D)² + det(C)² det(Y)² + tr((RY)²)`. The three terms bound the coordinates
of `p`, which gives `‖p‖ ≤ K(Z) |det(CZ + D)|`, with `K` continuous. The Plücker vector determines
the coset `P (C, D)`: for `(C', D')` with the same vector, `det(C'Z + D') = det(CZ + D)` for all
`Z`, so the bottom row `(E, F)` of the quotient has `det(EZ + F) = 1` for all `Z`, which forces
`E = 0`. So the series is dominated by the sum of `‖p‖^{-k}` over the quadric
`p₀ p₄ + p₂² + p₁ p₃ = 0` (`SiegelUpperHalfSpace.summable_norm_zpow_quadric`), locally uniformly in
`Z`.

## Main definitions

* `SiegelUpperHalfSpace.siegelPlucker`: the Plücker vector of the bottom row of `δ ∈ Sp(4, ℤ)`.
* `SiegelUpperHalfSpace.siegelK`: the constant `K(Z)`.
* `SiegelUpperHalfSpace.siegelCosetsMul`: the right translation of the cosets of the Siegel
  parabolic subgroup.
* `SiegelUpperHalfSpace.siegelEisensteinKJ`: `ψ_k`, with values in `Sym⁰(ℂ²)`.
* `SiegelUpperHalfSpace.scalarPoint`: the point `diag(is, is)` of `ℋ₂`.

## Main results

* `SiegelUpperHalfSpace.det_denom_eq_siegelPlucker`: `det(CZ + D)` in terms of the Plücker vector.
* `SiegelUpperHalfSpace.norm_siegelPlucker_le`: `‖p(C, D)‖ ≤ K(Z) |det(CZ + D)|`.
* `SiegelUpperHalfSpace.siegelPlucker_out_injective`: the Plücker vector determines the coset.
* `SiegelUpperHalfSpace.summable_siegelEisensteinTerm`: the series converges for `k > 3`.
* `SiegelUpperHalfSpace.siegelEisensteinSeries_smul`: the transformation law of `ψ_k`.
* `SiegelUpperHalfSpace.isHolomorphic_siegelEisensteinSeries`: `ψ_k` is holomorphic.
* `SiegelUpperHalfSpace.siegelEisensteinKJ_mem_modularFormsKJ`: `ψ_k` is a Siegel modular form.
* `SiegelUpperHalfSpace.isVectorSiegelEisensteinSeries_siegelEisensteinKJ`: `ψ_k` is the
  vector-valued Siegel Eisenstein series of the generator of `Sym⁰(ℂ²)`.
* `SiegelUpperHalfSpace.tendsto_siegelEisensteinSeries_scalarPoint`: the constant term of `ψ_k` is
  `1`.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open Complex Filter Metric Module Real SymplecticGroup Topology

open scoped TensorProduct

namespace SiegelUpperHalfSpace

/-! ### The real inequality -/

section Real

variable {p q r s t x₀₀ x₀₁ x₁₁ a b e : ℝ}

private lemma sq_add_sq_eq (hQ : p * t + r ^ 2 + q * s = 0) :
    (p * (x₀₀ * x₁₁ - x₀₁ ^ 2 - (a * e - b ^ 2)) + q * x₀₀ + 2 * r * x₀₁ - s * x₁₁ + t) ^ 2 +
      (p * (x₀₀ * e + a * x₁₁ - 2 * x₀₁ * b) + q * a + 2 * r * b - s * e) ^ 2 =
    (p * (x₀₀ * x₁₁ - x₀₁ ^ 2) + q * x₀₀ + 2 * r * x₀₁ - s * x₁₁ + t) ^ 2 +
      p ^ 2 * (a * e - b ^ 2) ^ 2 + (((x₁₁ * p + q) * a + (r - x₀₁ * p) * b) ^ 2 +
        (((r - x₀₁ * p) * b + (x₀₀ * p - s) * e)) ^ 2 +
          2 * ((x₁₁ * p + q) * b + (r - x₀₁ * p) * e) *
            ((r - x₀₁ * p) * a + (x₀₀ * p - s) * b)) := by
  linear_combination (-2 * (a * e - b ^ 2)) * hQ

variable (a b e) (u v w : ℝ)

/-- The form `tr((RY)²)` for `R = (u, v; v, w)` and `Y = (a, b; b, e)`. -/
private def traceForm : ℝ :=
  (u * a + v * b) ^ 2 + (v * b + w * e) ^ 2 + 2 * (u * b + v * e) * (v * a + w * b)

private lemma mul_traceForm_right : a ^ 2 * traceForm a b e u v w =
    (a * (u * a + v * b) + b * (v * a + w * b)) ^ 2 + 2 * (a * e - b ^ 2) * (v * a + w * b) ^ 2 +
      (a * e - b ^ 2) ^ 2 * w ^ 2 := by
  simp only [traceForm]
  ring1

private lemma mul_traceForm_left : e ^ 2 * traceForm a b e u v w =
    (e * (w * e + v * b) + b * (v * e + u * b)) ^ 2 + 2 * (a * e - b ^ 2) * (v * e + u * b) ^ 2 +
      (a * e - b ^ 2) ^ 2 * u ^ 2 := by
  simp only [traceForm]
  ring1

variable {a b e u v w} {N : ℝ}

private lemma traceForm_nonneg (ha : 0 < a) (hD : 0 < a * e - b ^ 2) :
    0 ≤ traceForm a b e u v w := by
  have h : 0 ≤ a ^ 2 * traceForm a b e u v w := by
    rw [mul_traceForm_right]
    positivity
  exact nonneg_of_mul_nonneg_right h (by positivity)

private lemma abs_right_le (ha : 0 < a) (hD : 0 < a * e - b ^ 2) (hN : 0 ≤ N)
    (hT : traceForm a b e u v w ≤ N ^ 2) : |w| ≤ a / (a * e - b ^ 2) * N := by
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  have h₁ : a ^ 2 * traceForm a b e u v w = _ := mul_traceForm_right a b e u v w
  have h₂ : (a * e - b ^ 2) ^ 2 * w ^ 2 ≤ a ^ 2 * N ^ 2 := by
    have h₃ : a ^ 2 * traceForm a b e u v w ≤ a ^ 2 * N ^ 2 :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    have h₄ : 0 ≤ (a * (u * a + v * b) + b * (v * a + w * b)) ^ 2 +
        2 * (a * e - b ^ 2) * (v * a + w * b) ^ 2 := by
      positivity
    linarith
  rw [div_mul_eq_mul_div, div_pow, le_div_iff₀ (by positivity), mul_comm, mul_pow]
  exact h₂

private lemma abs_left_le (he : 0 < e) (hD : 0 < a * e - b ^ 2) (hN : 0 ≤ N)
    (hT : traceForm a b e u v w ≤ N ^ 2) : |u| ≤ e / (a * e - b ^ 2) * N := by
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  have h₁ : e ^ 2 * traceForm a b e u v w = _ := mul_traceForm_left a b e u v w
  have h₂ : (a * e - b ^ 2) ^ 2 * u ^ 2 ≤ e ^ 2 * N ^ 2 := by
    have h₃ : e ^ 2 * traceForm a b e u v w ≤ e ^ 2 * N ^ 2 :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    have h₄ : 0 ≤ (e * (w * e + v * b) + b * (v * e + u * b)) ^ 2 +
        2 * (a * e - b ^ 2) * (v * e + u * b) ^ 2 := by
      positivity
    linarith
  rw [div_mul_eq_mul_div, div_pow, le_div_iff₀ (by positivity), mul_comm, mul_pow]
  exact h₂

private lemma abs_mid_le (ha : 0 < a) (hD : 0 < a * e - b ^ 2) (hN : 0 ≤ N)
    (hT : traceForm a b e u v w ≤ N ^ 2) :
    |v| ≤ (1 + 1 / (a * e - b ^ 2) + |b| / (a * e - b ^ 2)) * N := by
  have h₁ : a ^ 2 * traceForm a b e u v w = _ := mul_traceForm_right a b e u v w
  have hw : |v * a + w * b| ≤ a * ((1 + 1 / (a * e - b ^ 2)) * N) := by
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    have h₂ : 2 * (a * e - b ^ 2) * (v * a + w * b) ^ 2 ≤ a ^ 2 * N ^ 2 := by
      have h₃ : a ^ 2 * traceForm a b e u v w ≤ a ^ 2 * N ^ 2 :=
        mul_le_mul_of_nonneg_left hT (by positivity)
      have h₄ :
          0 ≤ (a * (u * a + v * b) + b * (v * a + w * b)) ^ 2 + (a * e - b ^ 2) ^ 2 * w ^ 2 := by
        positivity
      linarith
    have h₅ : 1 / (2 * (a * e - b ^ 2)) ≤ (1 + 1 / (a * e - b ^ 2)) ^ 2 := by
      have h₆ : 0 < 1 / (a * e - b ^ 2) := by
        positivity
      have h₇ : 1 / (2 * (a * e - b ^ 2)) = 1 / 2 * (1 / (a * e - b ^ 2)) := by
        field_simp
      rw [h₇]
      nlinarith
    have h₈ : (v * a + w * b) ^ 2 ≤ 1 / (2 * (a * e - b ^ 2)) * (a ^ 2 * N ^ 2) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity), mul_comm]
      exact h₂
    exact h₈.trans ((mul_le_mul_of_nonneg_right h₅ (by positivity)).trans_eq (by ring1))
  have hb : |w| * |b| ≤ a / (a * e - b ^ 2) * N * |b| :=
    mul_le_mul_of_nonneg_right (abs_right_le ha hD hN hT) (abs_nonneg b)
  have h₉ : |v| * a ≤ a * ((1 + 1 / (a * e - b ^ 2)) * N) + a / (a * e - b ^ 2) * N * |b| := by
    have e₁ : |v| * a = |(v * a + w * b) - w * b| := by
      rw [add_sub_cancel_right, abs_mul, abs_of_pos ha]
    rw [e₁]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    exact add_le_add hw hb
  refine le_of_mul_le_mul_right (h₉.trans_eq ?_) ha
  field_simp

end Real

/-! ### The Plücker vector of the bottom row -/

variable (δ : symplecticGroup (Fin 2) ℤ) (Z : SiegelUpperHalfSpace (Fin 2))

/-- The **Plücker vector** `(det C, c₁ ∧ d₂, c₂ ∧ d₂, c₂ ∧ d₁, det D)` of the bottom row `(C, D)` of
`δ ∈ Sp(4, ℤ)`, where `c₁, c₂` and `d₁, d₂` are the columns of `C` and `D`. The remaining minor is
`c₁ ∧ d₁ = -c₂ ∧ d₂`, as `C Dᵀ` is symmetric. -/
def siegelPlucker : Fin 5 → ℤ :=
  ![δ.1 (.inr 0) (.inl 0) * δ.1 (.inr 1) (.inl 1) - δ.1 (.inr 0) (.inl 1) * δ.1 (.inr 1) (.inl 0),
    δ.1 (.inr 0) (.inl 0) * δ.1 (.inr 1) (.inr 1) - δ.1 (.inr 0) (.inr 1) * δ.1 (.inr 1) (.inl 0),
    δ.1 (.inr 0) (.inl 1) * δ.1 (.inr 1) (.inr 1) - δ.1 (.inr 0) (.inr 1) * δ.1 (.inr 1) (.inl 1),
    δ.1 (.inr 0) (.inl 1) * δ.1 (.inr 1) (.inr 0) - δ.1 (.inr 0) (.inr 0) * δ.1 (.inr 1) (.inl 1),
    δ.1 (.inr 0) (.inr 0) * δ.1 (.inr 1) (.inr 1) - δ.1 (.inr 0) (.inr 1) * δ.1 (.inr 1) (.inr 0)]

private lemma isotropic_bottomRow : δ.1 (.inr 0) (.inl 0) * δ.1 (.inr 1) (.inr 0) -
    δ.1 (.inr 0) (.inr 0) * δ.1 (.inr 1) (.inl 0) + (δ.1 (.inr 0) (.inl 1) * δ.1 (.inr 1) (.inr 1) -
      δ.1 (.inr 0) (.inr 1) * δ.1 (.inr 1) (.inl 1)) = 0 := by
  have h : ((δ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) * J (Fin 2) ℤ *
      (δ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)ᵀ) (.inr 0) (.inr 1) =
        J (Fin 2) ℤ (.inr 0) (.inr 1) :=
    congrFun (congrFun (SymplecticGroup.mem_iff.mp δ.2) (.inr 0)) (.inr 1)
  simp [Matrix.mul_apply, J] at h
  linarith

private lemma siegelPlucker_quadric : (siegelPlucker δ 0 : ℝ) * siegelPlucker δ 4 +
    (siegelPlucker δ 2 : ℝ) ^ 2 + siegelPlucker δ 1 * siegelPlucker δ 3 = 0 := by
  have h : ((δ.1 (.inr 0) (.inl 0) * δ.1 (.inr 1) (.inr 0) -
      δ.1 (.inr 0) (.inr 0) * δ.1 (.inr 1) (.inl 0) +
        (δ.1 (.inr 0) (.inl 1) * δ.1 (.inr 1) (.inr 1) -
          δ.1 (.inr 0) (.inr 1) * δ.1 (.inr 1) (.inl 1)) : ℤ) : ℝ) = 0 := by
    rw [isotropic_bottomRow, Int.cast_zero]
  simp only [siegelPlucker]
  push_cast at h ⊢
  linear_combination ((δ.1 (.inr 0) (.inl 1) : ℝ) * δ.1 (.inr 1) (.inr 1) -
    δ.1 (.inr 0) (.inr 1) * δ.1 (.inr 1) (.inl 1)) * h

/-- **The determinant `det(CZ + D)` in terms of the Plücker vector**: it is
`p₀ det Z + p₁ z₀₀ + 2 p₂ z₀₁ - p₃ z₁₁ + p₄`. -/
lemma det_denom_eq_siegelPlucker : (denom (map (Int.castRingHom ℝ) δ) Z.val).det =
    (siegelPlucker δ 0 : ℂ) * (Z.val 0 0 * Z.val 1 1 - Z.val 0 1 ^ 2) +
      siegelPlucker δ 1 * Z.val 0 0 + 2 * siegelPlucker δ 2 * Z.val 0 1 -
        siegelPlucker δ 3 * Z.val 1 1 + siegelPlucker δ 4 := by
  have hZ : Z.val 1 0 = Z.val 0 1 := Z.val_one_zero
  have h : ((δ.1 (.inr 0) (.inl 0) * δ.1 (.inr 1) (.inr 0) -
      δ.1 (.inr 0) (.inr 0) * δ.1 (.inr 1) (.inl 0) +
        (δ.1 (.inr 0) (.inl 1) * δ.1 (.inr 1) (.inr 1) -
          δ.1 (.inr 0) (.inr 1) * δ.1 (.inr 1) (.inl 1)) : ℤ) : ℂ) = 0 := by
    rw [isotropic_bottomRow, Int.cast_zero]
  simp only [det_fin_two, denom, toBlocks₂₁, toBlocks₂₂, Matrix.add_apply, Matrix.mul_apply,
    Fin.sum_univ_two, map_apply, of_apply, siegelPlucker, hZ, SymplecticGroup.coe_map_apply]
  push_cast at h ⊢
  linear_combination (-(Z.val 0 1)) * h

private lemma abs_le_of_abs_mul_add_le {c p y K A : ℝ} (hA : 1 + |c| ≤ A) (hK : 0 ≤ K)
    (hp : |p| ≤ K) (h : |c * p + y| ≤ K) : |y| ≤ A * K := by
  have e : y = c * p + y - c * p := by
    ring1
  rw [e]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul]
  have h₁ : |c| * |p| ≤ |c| * K := mul_le_mul_of_nonneg_left hp (abs_nonneg c)
  nlinarith [mul_le_mul_of_nonneg_right hA hK]

/-- The constant `K(Z)` of the comparison `‖p(C, D)‖ ≤ K(Z) |det(CZ + D)|`, for `Z = X + iY`. -/
noncomputable def siegelK (W : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  4 * (1 + |(W 0 0).re| + |(W 0 1).re| + |(W 1 1).re|) ^ 2 *
    (1 + (1 + (W 0 0).im + (W 1 1).im + |(W 0 1).im|) /
      ((W 0 0).im * (W 1 1).im - (W 0 1).im ^ 2))

private lemma det_im_eq : (Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im ^ 2 =
    (Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im * (Z.val 1 0).im := by
  have hZ : Z.val 1 0 = Z.val 0 1 := Z.val_one_zero
  rw [hZ]
  ring1

lemma siegelK_pos : 0 < siegelK Z.val := by
  have hD : 0 < (Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im ^ 2 := by
    rw [det_im_eq]
    exact det_im_pos Z
  have ha : 0 < (Z.val 0 0).im := im_zero_zero_pos Z
  have he : 0 < (Z.val 1 1).im := im_one_one_pos Z
  rw [siegelK]
  positivity

private lemma mul_add_sq_le {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    u * w + v ^ 2 ≤ (1 + u + v + w) ^ 2 := by
  have h : 0 ≤ 1 + u ^ 2 + w ^ 2 + 2 * u + 2 * v + 2 * w + 2 * u * v + 2 * v * w + u * w := by
    positivity
  linarith

private lemma abs_coords_le {p q r s t x₀ x₁ x₂ a b e N : ℝ} (hQ : p * t + r ^ 2 + q * s = 0)
    (ha : 0 < a) (he : 0 < e) (hD : 0 < a * e - b ^ 2) (hN₀ : 0 ≤ N)
    (hnorm : (p * (x₀ * x₂ - x₁ ^ 2 - (a * e - b ^ 2)) + q * x₀ + 2 * r * x₁ - s * x₂ + t) ^ 2 +
      (p * (x₀ * e + a * x₂ - 2 * x₁ * b) + q * a + 2 * r * b - s * e) ^ 2 = N ^ 2) (i : Fin 5) :
    |![p, q, r, s, t] i| ≤ 4 * (1 + |x₀| + |x₁| + |x₂|) ^ 2 *
      (1 + (1 + a + e + |b|) / (a * e - b ^ 2)) * N := by
  have hsum : (p * (x₀ * x₂ - x₁ ^ 2 - (a * e - b ^ 2)) + q * x₀ + 2 * r * x₁ - s * x₂ + t) ^ 2 +
      (p * (x₀ * e + a * x₂ - 2 * x₁ * b) + q * a + 2 * r * b - s * e) ^ 2 = _ :=
    sq_add_sq_eq hQ
  rw [hnorm] at hsum
  have hE : N ^ 2 = (p * (x₀ * x₂ - x₁ ^ 2) + q * x₀ + 2 * r * x₁ - s * x₂ + t) ^ 2 +
      p ^ 2 * (a * e - b ^ 2) ^ 2 + traceForm a b e (x₂ * p + q) (r - x₁ * p) (x₀ * p - s) :=
    hsum
  have hT₀ : 0 ≤ traceForm a b e (x₂ * p + q) (r - x₁ * p) (x₀ * p - s) :=
    traceForm_nonneg ha hD
  have hT : traceForm a b e (x₂ * p + q) (r - x₁ * p) (x₀ * p - s) ≤ N ^ 2 := by
    have h₁ : 0 ≤ (p * (x₀ * x₂ - x₁ ^ 2) + q * x₀ + 2 * r * x₁ - s * x₂ + t) ^ 2 +
        p ^ 2 * (a * e - b ^ 2) ^ 2 := by
      positivity
    linarith
  have hdP : |p * (x₀ * x₂ - x₁ ^ 2) + q * x₀ + 2 * r * x₁ - s * x₂ + t| ≤ N := by
    refine abs_le_of_sq_le_sq ?_ hN₀
    have h₁ : 0 ≤ p ^ 2 * (a * e - b ^ 2) ^ 2 := by
      positivity
    linarith
  have hpD : |p * (a * e - b ^ 2)| ≤ N := by
    refine abs_le_of_sq_le_sq ?_ hN₀
    have h₁ : 0 ≤ (p * (x₀ * x₂ - x₁ ^ 2) + q * x₀ + 2 * r * x₁ - s * x₂ + t) ^ 2 := by
      positivity
    rw [mul_pow]
    linarith
  generalize hB : 1 + (1 + a + e + |b|) / (a * e - b ^ 2) = B
  generalize hA : 1 + |x₀| + |x₁| + |x₂| = A
  have hsplit : (1 + a + e + |b|) / (a * e - b ^ 2) =
      1 / (a * e - b ^ 2) + a / (a * e - b ^ 2) + e / (a * e - b ^ 2) + |b| / (a * e - b ^ 2) := by
    ring1
  have hi₁ : 0 ≤ 1 / (a * e - b ^ 2) := by
    positivity
  have hi₂ : 0 ≤ a / (a * e - b ^ 2) := by
    positivity
  have hi₃ : 0 ≤ e / (a * e - b ^ 2) := by
    positivity
  have hi₄ : 0 ≤ |b| / (a * e - b ^ 2) := by
    positivity
  have hB₁ : 1 ≤ B := by
    rw [← hB, hsplit]
    linarith
  have hA₁ : 1 ≤ A := by
    rw [← hA]
    linarith [abs_nonneg x₀, abs_nonneg x₁, abs_nonneg x₂]
  have hK₁ : 0 ≤ B * N := by
    positivity
  have hle (y : ℝ) (hy : y ≤ B) : y * N ≤ B * N :=
    mul_le_mul_of_nonneg_right hy hN₀
  have hp' : |p| ≤ B * N := by
    have h₁ : |p| * (a * e - b ^ 2) ≤ N := by
      rwa [abs_mul, abs_of_pos hD] at hpD
    have h₂ : |p| ≤ 1 / (a * e - b ^ 2) * N := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hD]
      exact h₁
    refine h₂.trans (hle _ ?_)
    rw [← hB, hsplit]
    linarith
  have hu : |x₂ * p + q| ≤ B * N := by
    refine (abs_left_le he hD hN₀ hT).trans (hle _ ?_)
    rw [← hB, hsplit]
    linarith
  have hw : |x₀ * p - s| ≤ B * N := by
    refine (abs_right_le ha hD hN₀ hT).trans (hle _ ?_)
    rw [← hB, hsplit]
    linarith
  have hv : |r - x₁ * p| ≤ B * N := by
    refine (abs_mid_le ha hD hN₀ hT).trans (hle _ ?_)
    rw [← hB, hsplit]
    linarith
  have hq' : |q| ≤ A * (B * N) :=
    abs_le_of_abs_mul_add_le (by rw [← hA]; linarith [abs_nonneg x₀, abs_nonneg x₁]) hK₁ hp' hu
  have hr' : |r| ≤ A * (B * N) := by
    refine abs_le_of_abs_mul_add_le (c := -x₁) (by
      rw [← hA, abs_neg]
      linarith [abs_nonneg x₀, abs_nonneg x₂]) hK₁ hp' ?_
    have e₁ : -x₁ * p + r = r - x₁ * p := by
      ring1
    rwa [e₁]
  have hs' : |s| ≤ A * (B * N) := by
    refine abs_le_of_abs_mul_add_le (c := -x₀) (by
      rw [← hA, abs_neg]
      linarith [abs_nonneg x₁, abs_nonneg x₂]) hK₁ hp' ?_
    have e₁ : -x₀ * p + s = -(x₀ * p - s) := by
      ring1
    rwa [e₁, abs_neg]
  have hA₂ : A ≤ A ^ 2 := le_self_pow₀ hA₁ two_ne_zero
  have hA₃ : 1 ≤ A ^ 2 := hA₁.trans hA₂
  have hc₁ : B * N ≤ A ^ 2 * (B * N) := le_mul_of_one_le_left hK₁ hA₃
  have hc₂ : A * (B * N) ≤ A ^ 2 * (B * N) := mul_le_mul_of_nonneg_right hA₂ hK₁
  have hc₃ : 0 ≤ A ^ 2 * (B * N) := by
    positivity
  have ht' : |t| ≤ 4 * A ^ 2 * B * N := by
    have ht₁ : |(x₀ * x₂ - x₁ ^ 2) * p| ≤ A ^ 2 * (B * N) := by
      rw [abs_mul]
      refine mul_le_mul ?_ hp' (abs_nonneg p) (by positivity)
      have h₁ : |x₀ * x₂ - x₁ ^ 2| ≤ |x₀| * |x₂| + |x₁| ^ 2 := by
        have h₂ : |x₀ * x₂ - x₁ ^ 2| ≤ |x₀ * x₂| + |x₁ ^ 2| := abs_sub _ _
        rwa [abs_mul, abs_pow] at h₂
      rw [← hA]
      exact h₁.trans (mul_add_sq_le (abs_nonneg x₀) (abs_nonneg x₁) (abs_nonneg x₂))
    have ht₂ : |q * x₀| ≤ |x₀| * (A * (B * N)) := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left hq' (abs_nonneg _)
    have ht₃ : |2 * r * x₁| ≤ 2 * |x₁| * (A * (B * N)) := by
      rw [abs_mul, abs_mul, abs_two, mul_comm, ← mul_assoc, mul_comm |x₁|]
      exact mul_le_mul_of_nonneg_left hr' (by positivity)
    have ht₄ : |s * x₂| ≤ |x₂| * (A * (B * N)) := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left hs' (abs_nonneg _)
    have ht₅ : (|x₀| + 2 * |x₁| + |x₂|) * (A * (B * N)) ≤ 2 * A * (A * (B * N)) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [← hA]
      linarith [abs_nonneg x₀, abs_nonneg x₁, abs_nonneg x₂]
    have ht₆ : |p * (x₀ * x₂ - x₁ ^ 2) + q * x₀ + 2 * r * x₁ - s * x₂ + t| ≤ B * N :=
      hdP.trans (le_mul_of_one_le_left hN₀ hB₁)
    have e₁ : p * (x₀ * x₂ - x₁ ^ 2) = (x₀ * x₂ - x₁ ^ 2) * p := by
      ring1
    rw [e₁] at ht₆
    have ht₇ : 4 * A ^ 2 * B * N = 4 * (A ^ 2 * (B * N)) := by
      ring1
    have ht₈ : 2 * A * (A * (B * N)) = 2 * (A ^ 2 * (B * N)) := by
      ring1
    rw [ht₇]
    rw [abs_le] at ht₁ ht₂ ht₃ ht₄ ht₆ ⊢
    constructor <;> linarith
  fin_cases i
  · have h₁ : |p| ≤ 4 * A ^ 2 * B * N := by
      linarith
    simpa using h₁
  · have h₁ : |q| ≤ 4 * A ^ 2 * B * N := by
      linarith
    simpa using h₁
  · have h₁ : |r| ≤ 4 * A ^ 2 * B * N := by
      linarith
    simpa using h₁
  · have h₁ : |s| ≤ 4 * A ^ 2 * B * N := by
      linarith
    simpa using h₁
  · simpa using ht'

/-- **The comparison of `det(CZ + D)` with the Plücker vector**: `‖p(C, D)‖ ≤ K(Z) |det(CZ + D)|`
for the bottom row `(C, D)` of `δ ∈ Sp(4, ℤ)`. For `Z = X + iY`, `R = adj(CX + D) C` is symmetric
and `|det(CZ + D)|² = det(CX + D)² + det(C)² det(Y)² + tr((RY)²)`, whose terms bound the coordinates
of `p(C, D)`. -/
lemma norm_siegelPlucker_le :
    ‖siegelPlucker δ‖ ≤ siegelK Z.val * ‖(denom (map (Int.castRingHom ℝ) δ) Z.val).det‖ := by
  generalize hN : ‖(denom (map (Int.castRingHom ℝ) δ) Z.val).det‖ = N
  have hN₀ : 0 ≤ N := hN ▸ norm_nonneg _
  generalize hp : (siegelPlucker δ 0 : ℝ) = p
  generalize hq : (siegelPlucker δ 1 : ℝ) = q
  generalize hr : (siegelPlucker δ 2 : ℝ) = r
  generalize hs : (siegelPlucker δ 3 : ℝ) = s
  generalize ht : (siegelPlucker δ 4 : ℝ) = t
  have hQ : p * t + r ^ 2 + q * s = 0 := by
    rw [← hp, ← hq, ← hr, ← hs, ← ht]
    exact siegelPlucker_quadric δ
  have ha : 0 < (Z.val 0 0).im := im_zero_zero_pos Z
  have he : 0 < (Z.val 1 1).im := im_one_one_pos Z
  have hD : 0 < (Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im ^ 2 := by
    rw [det_im_eq]
    exact det_im_pos Z
  have hnorm : ((p * ((Z.val 0 0).re * (Z.val 1 1).re - (Z.val 0 1).re ^ 2 -
      ((Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im ^ 2)) + q * (Z.val 0 0).re +
        2 * r * (Z.val 0 1).re - s * (Z.val 1 1).re + t)) ^ 2 +
      (p * ((Z.val 0 0).re * (Z.val 1 1).im + (Z.val 0 0).im * (Z.val 1 1).re -
        2 * (Z.val 0 1).re * (Z.val 0 1).im) + q * (Z.val 0 0).im + 2 * r * (Z.val 0 1).im -
          s * (Z.val 1 1).im) ^ 2 = N ^ 2 := by
    rw [← hN, ← normSq_eq_norm_sq, det_denom_eq_siegelPlucker, normSq_apply, ← pow_two, ← pow_two]
    have e₁ (n : ℤ) : (n : ℂ) = ((n : ℝ) : ℂ) := by
      simp
    simp only [e₁, hp, hq, hr, hs, ht]
    simp [pow_two]
    ring1
  have hK : siegelK Z.val = 4 * (1 + |(Z.val 0 0).re| + |(Z.val 0 1).re| + |(Z.val 1 1).re|) ^ 2 *
      (1 + (1 + (Z.val 0 0).im + (Z.val 1 1).im + |(Z.val 0 1).im|) /
        ((Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im ^ 2)) :=
    rfl
  have hb (i : Fin 5) : |![p, q, r, s, t] i| ≤ siegelK Z.val * N :=
    hK ▸ abs_coords_le hQ ha he hD hN₀ hnorm i
  have hKN : 0 ≤ siegelK Z.val * N := mul_nonneg (siegelK_pos Z).le hN₀
  refine (pi_norm_le_iff_of_nonneg hKN).mpr fun i ↦ ?_
  have h₁ : |![p, q, r, s, t] i| ≤ siegelK Z.val * N := hb i
  have h₂ : ‖siegelPlucker δ i‖ = |((siegelPlucker δ i : ℤ) : ℝ)| := by
    rw [Int.norm_eq_abs]
  rw [h₂]
  fin_cases i
  · simpa [hp] using h₁
  · simpa [hq] using h₁
  · simpa [hr] using h₁
  · simpa [hs] using h₁
  · simpa [ht] using h₁

/-- The point `diag(i, i)` of `ℋ₂`. -/
private def baseDiag : SiegelUpperHalfSpace (Fin 2) :=
  diagPoint UpperHalfPlane.I ⟨1, Set.mem_Ioi.mpr one_pos⟩

lemma siegelPlucker_ne_zero : siegelPlucker δ ≠ 0 := by
  intro h
  have h₁ : (denom (map (Int.castRingHom ℝ) δ) baseDiag.val).det ≠ 0 :=
    (isUnit_det_denom (map (Int.castRingHom ℝ) δ) baseDiag).ne_zero
  refine h₁ ?_
  rw [det_denom_eq_siegelPlucker, h]
  simp

private lemma mem_siegelParabolic_of_siegelPlucker (h₀ : siegelPlucker δ 0 = 0)
    (h₁ : siegelPlucker δ 1 = 0) (h₂ : siegelPlucker δ 2 = 0) (h₃ : siegelPlucker δ 3 = 0) :
    δ ∈ siegelParabolic (Fin 2) ℤ := by
  have ht : siegelPlucker δ 4 ≠ 0 := fun ht ↦ siegelPlucker_ne_zero δ <| by
    ext i
    fin_cases i <;> assumption
  have hiso : δ.1 (.inr 0) (.inl 0) * δ.1 (.inr 1) (.inr 0) -
      δ.1 (.inr 0) (.inr 0) * δ.1 (.inr 1) (.inl 0) +
        (δ.1 (.inr 0) (.inl 1) * δ.1 (.inr 1) (.inr 1) -
          δ.1 (.inr 0) (.inr 1) * δ.1 (.inr 1) (.inl 1)) = 0 :=
    isotropic_bottomRow δ
  simp only [siegelPlucker, Matrix.cons_val] at h₀ h₁ h₂ h₃ ht
  have e₁ : δ.1 (.inr 0) (.inl 0) * δ.1 (.inr 1) (.inr 0) -
      δ.1 (.inr 0) (.inr 0) * δ.1 (.inr 1) (.inl 0) = 0 := by
    linarith
  have hC : ∀ i j : Fin 2, δ.1 (.inr i) (.inl j) = 0 := by
    refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
      Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩ <;> refine (mul_eq_zero.mp ?_).resolve_left ht
    · linear_combination (δ.1 (.inr 0) (.inr 0)) * h₁ - (δ.1 (.inr 0) (.inr 1)) * e₁
    · linear_combination (δ.1 (.inr 0) (.inr 0)) * h₂ - (δ.1 (.inr 0) (.inr 1)) * h₃
    · linear_combination (δ.1 (.inr 1) (.inr 0)) * h₁ - (δ.1 (.inr 1) (.inr 1)) * e₁
    · linear_combination (δ.1 (.inr 1) (.inr 0)) * h₂ - (δ.1 (.inr 1) (.inr 1)) * h₃
  ext i j
  exact hC i j

/-- The point `(i, 1; 1, 2i)` of `ℋ₂`. -/
private noncomputable def testPoint : SiegelUpperHalfSpace (Fin 2) where
  val := !![I, 1; 1, 2 * I]
  transpose_val := by
    ext a c
    fin_cases a <;> fin_cases c <;> rfl
  posDef_im := by
    have h : (!![I, 1; 1, 2 * I] : Matrix (Fin 2) (Fin 2) ℂ).map Complex.im = diagonal ![1, 2] := by
      ext a c
      fin_cases a <;> fin_cases c <;> simp
    rw [h, Matrix.posDef_diagonal_iff]
    intro a
    fin_cases a <;> simp

/-- The point `diag(2i, i)` of `ℋ₂`. -/
private def testDiag : SiegelUpperHalfSpace (Fin 2) :=
  diagPoint ⟨2 * I, by simp⟩ ⟨1, Set.mem_Ioi.mpr one_pos⟩

private lemma siegelPlucker_eq_of_forall_det
    (h : ∀ W : SiegelUpperHalfSpace (Fin 2), (denom (map (Int.castRingHom ℝ) δ) W.val).det = 1)
    (i : Fin 4) : siegelPlucker δ i.castSucc = 0 := by
  have h₁ : (denom (map (Int.castRingHom ℝ) δ) baseDiag.val).det = 1 := h baseDiag
  have h₂ : (denom (map (Int.castRingHom ℝ) δ) testDiag.val).det = 1 := h testDiag
  have h₃ : (denom (map (Int.castRingHom ℝ) δ) testPoint.val).det = 1 := h testPoint
  rw [det_denom_eq_siegelPlucker] at h₁ h₂ h₃
  generalize siegelPlucker δ = v at h₁ h₂ h₃ ⊢
  have a₁ : Complex.re _ = Complex.re 1 := congrArg Complex.re h₁
  have b₁ : Complex.im _ = Complex.im 1 := congrArg Complex.im h₁
  have a₂ : Complex.re _ = Complex.re 1 := congrArg Complex.re h₂
  have b₂ : Complex.im _ = Complex.im 1 := congrArg Complex.im h₂
  have a₃ : Complex.re _ = Complex.re 1 := congrArg Complex.re h₃
  simp [baseDiag, testDiag, diagPoint, testPoint] at a₁ b₁ a₂ b₂ a₃
  have e₀ : (v 0 : ℝ) = 0 := by
    linarith
  have e₁ : (v 1 : ℝ) = 0 := by
    linarith
  have e₂ : (v 2 : ℝ) = 0 := by
    linarith
  have e₃ : (v 3 : ℝ) = 0 := by
    linarith
  fin_cases i
  · exact_mod_cast e₀
  · exact_mod_cast e₁
  · exact_mod_cast e₂
  · exact_mod_cast e₃

variable {δ} in
private lemma mul_inv_mem_of_siegelPlucker_eq {δ' : symplecticGroup (Fin 2) ℤ}
    (h : siegelPlucker δ' = siegelPlucker δ) : δ' * δ⁻¹ ∈ siegelParabolic (Fin 2) ℤ := by
  have hdet (W : SiegelUpperHalfSpace (Fin 2)) :
      (denom (map (Int.castRingHom ℝ) (δ' * δ⁻¹)) W.val).det = 1 := by
    have e : W = map (Int.castRingHom ℝ) δ • map (Int.castRingHom ℝ) δ⁻¹ • W := by
      rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    have h₁ : denom (map (Int.castRingHom ℝ) (δ' * δ⁻¹) * map (Int.castRingHom ℝ) δ)
        (map (Int.castRingHom ℝ) δ⁻¹ • W).val = denom (map (Int.castRingHom ℝ) (δ' * δ⁻¹))
          (map (Int.castRingHom ℝ) δ • map (Int.castRingHom ℝ) δ⁻¹ • W).val *
            denom (map (Int.castRingHom ℝ) δ) (map (Int.castRingHom ℝ) δ⁻¹ • W).val :=
      denom_mul _ _ _
    rw [← e, ← map_mul, inv_mul_cancel_right] at h₁
    have h₂ : (denom (map (Int.castRingHom ℝ) δ') (map (Int.castRingHom ℝ) δ⁻¹ • W).val).det =
        (denom (map (Int.castRingHom ℝ) (δ' * δ⁻¹)) W.val *
          denom (map (Int.castRingHom ℝ) δ) (map (Int.castRingHom ℝ) δ⁻¹ • W).val).det :=
      congrArg Matrix.det h₁
    rw [det_mul, det_denom_eq_siegelPlucker δ', det_denom_eq_siegelPlucker δ, h] at h₂
    have h₃ : (siegelPlucker δ 0 : ℂ) * ((map (Int.castRingHom ℝ) δ⁻¹ • W).val 0 0 *
        (map (Int.castRingHom ℝ) δ⁻¹ • W).val 1 1 - (map (Int.castRingHom ℝ) δ⁻¹ • W).val 0 1 ^ 2) +
          siegelPlucker δ 1 * (map (Int.castRingHom ℝ) δ⁻¹ • W).val 0 0 +
            2 * siegelPlucker δ 2 * (map (Int.castRingHom ℝ) δ⁻¹ • W).val 0 1 -
              siegelPlucker δ 3 * (map (Int.castRingHom ℝ) δ⁻¹ • W).val 1 1 +
                siegelPlucker δ 4 ≠ 0 := by
      rw [← det_denom_eq_siegelPlucker]
      exact (isUnit_det_denom _ _).ne_zero
    exact (mul_eq_right₀ h₃).mp h₂.symm
  have hv (i : Fin 4) : siegelPlucker (δ' * δ⁻¹) i.castSucc = 0 :=
    siegelPlucker_eq_of_forall_det (δ' * δ⁻¹) hdet i
  exact mem_siegelParabolic_of_siegelPlucker _ (hv 0) (hv 1) (hv 2) (hv 3)

/-- **The Plücker vector determines the coset of the Siegel parabolic subgroup**: if `(C, D)` and
`(C', D')` have the same Plücker vector, then `det(C'Z + D') = det(CZ + D)` for all `Z`, so the
bottom row `(E, F)` of `δ' δ⁻¹` has `det(EZ + F) = 1` for all `Z`, which forces `E = 0`. -/
lemma siegelPlucker_out_injective :
    Function.Injective fun x : SiegelParabolicCosets (Fin 2) ↦ siegelPlucker x.out := by
  intro x y h
  rw [← Quotient.out_eq x, ← Quotient.out_eq y]
  refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
  exact mul_inv_mem_of_siegelPlucker_eq (h : siegelPlucker x.out = siegelPlucker y.out).symm

variable {k : ℤ} (β : symplecticGroup (Fin 2) ℤ)

lemma summable_norm_siegelPlucker_zpow (hk : 3 < k) :
    Summable fun x : SiegelParabolicCosets (Fin 2) ↦ ‖siegelPlucker x.out‖ ^ (-k) := by
  have hQ (γ : symplecticGroup (Fin 2) ℤ) : siegelPlucker γ 0 * siegelPlucker γ 4 +
      siegelPlucker γ 2 ^ 2 + siegelPlucker γ 1 * siegelPlucker γ 3 = 0 := by
    exact_mod_cast siegelPlucker_quadric γ
  exact summable_norm_zpow_quadric hk siegelPlucker_out_injective
    (fun x ↦ siegelPlucker_ne_zero x.out) fun x ↦ hQ x.out

lemma norm_siegelEisensteinTerm_le (hk : 0 < k) :
    ‖siegelEisensteinTerm k Z δ‖ ≤ siegelK Z.val ^ k * ‖siegelPlucker δ‖ ^ (-k) := by
  have hv : 0 < ‖siegelPlucker δ‖ := norm_pos_iff.mpr (siegelPlucker_ne_zero δ)
  have hK : 0 < siegelK Z.val := siegelK_pos Z
  have hd : 0 < ‖(denom (map (Int.castRingHom ℝ) δ) Z.val).det‖ :=
    norm_pos_iff.mpr (isUnit_det_denom _ _).ne_zero
  have h₁ : ‖siegelPlucker δ‖ ^ k ≤
      (siegelK Z.val * ‖(denom (map (Int.castRingHom ℝ) δ) Z.val).det‖) ^ k :=
    zpow_le_zpow_left₀ hk.le hv.le (norm_siegelPlucker_le δ Z)
  rw [mul_zpow] at h₁
  rw [siegelEisensteinTerm, norm_zpow, zpow_neg, zpow_neg, ← div_eq_mul_inv,
    le_div_iff₀ (zpow_pos hv k), inv_mul_le_iff₀ (zpow_pos hd k), mul_comm]
  exact h₁

/-- **The Siegel Eisenstein series of degree `2` converges absolutely** for `k > 3`, by comparison
with the sum of `‖p‖^{-k}` over the quadric of Plücker vectors. -/
lemma summable_siegelEisensteinTerm (hk : 3 < k) :
    Summable fun x : SiegelParabolicCosets (Fin 2) ↦ siegelEisensteinTerm k Z x.out :=
  ((summable_norm_siegelPlucker_zpow hk).mul_left (siegelK Z.val ^ k)).of_norm_bounded fun x ↦
    norm_siegelEisensteinTerm_le x.out Z (by linarith)

/-- The right translation `P δ ↦ P δ β` of the cosets of the Siegel parabolic subgroup. -/
noncomputable def siegelCosetsMul : Equiv.Perm (SiegelParabolicCosets (Fin 2)) :=
  Quotient.congr (Equiv.mulRight β) fun a b ↦ by
    simp [QuotientGroup.rightRel_apply]

private lemma siegelEisensteinTerm_smul : siegelEisensteinTerm k (map (Int.castRingHom ℝ) β • Z) δ =
    (denom (map (Int.castRingHom ℝ) β) Z.val).det ^ k * siegelEisensteinTerm k Z (δ * β) := by
  have h₀ : (denom (map (Int.castRingHom ℝ) β) Z.val).det ≠ 0 := (isUnit_det_denom _ _).ne_zero
  rw [siegelEisensteinTerm, siegelEisensteinTerm, map_mul, denom_mul, det_mul, mul_zpow,
    zpow_neg (denom (map (Int.castRingHom ℝ) β) Z.val).det, mul_left_comm,
    mul_inv_cancel₀ (zpow_ne_zero _ h₀), mul_one]

/-- **The transformation law of the Siegel Eisenstein series** `ψ_k`, for even `k`:
`ψ_k(βZ) = det(C_β Z + D_β)^k ψ_k(Z)`. -/
lemma siegelEisensteinSeries_smul (hk' : Even k) :
    siegelEisensteinSeries k (map (Int.castRingHom ℝ) β • Z) =
      (denom (map (Int.castRingHom ℝ) β) Z.val).det ^ k * siegelEisensteinSeries k Z := by
  have e (x : SiegelParabolicCosets (Fin 2)) : siegelEisensteinTerm k Z (x.out * β) =
      siegelEisensteinTerm k Z (siegelCosetsMul β x).out := by
    have e₁ : siegelCosetsMul β x = ⟦x.out * β⟧ := by
      conv_lhs => rw [← Quotient.out_eq x]
      rfl
    rw [e₁, siegelEisensteinTerm_out k Z _ hk']
  rw [siegelEisensteinSeries, siegelEisensteinSeries, ← tsum_mul_left,
    ← (siegelCosetsMul β).tsum_eq fun x ↦ _ * siegelEisensteinTerm k Z x.out]
  exact tsum_congr fun x ↦ (siegelEisensteinTerm_smul _ Z β).trans (by rw [e])

private lemma continuousAt_siegelK {Z₀ : Fin 2 → Fin 2 → ℂ}
    (hZ₀ : Z₀ ∈ symmetrizePreimage (Fin 2)) :
    ContinuousAt (fun Z : Fin 2 → Fin 2 → ℂ ↦ siegelK (symmetrize Z)) Z₀ := by
  have hy (a b : Fin 2) : Continuous fun Z : Fin 2 → Fin 2 → ℂ ↦ (symmetrize Z a b).im := by
    fun_prop
  have hx (a b : Fin 2) : Continuous fun Z : Fin 2 → Fin 2 → ℂ ↦ (symmetrize Z a b).re := by
    fun_prop
  have hdet : (symmetrize Z₀ 0 0).im * (symmetrize Z₀ 1 1).im - (symmetrize Z₀ 0 1).im ^ 2 ≠ 0 := by
    have h₁ : (symmetrize Z₀ 0 0).im * (symmetrize Z₀ 1 1).im - (symmetrize Z₀ 0 1).im ^ 2 =
        (symmetrize Z₀ 0 0).im * (symmetrize Z₀ 1 1).im -
          (symmetrize Z₀ 0 1).im * (symmetrize Z₀ 1 0).im :=
      det_im_eq ⟨symmetrize Z₀, transpose_symmetrize Z₀, hZ₀⟩
    have h₂ : 0 < (symmetrize Z₀ 0 0).im * (symmetrize Z₀ 1 1).im -
        (symmetrize Z₀ 0 1).im * (symmetrize Z₀ 1 0).im :=
      det_im_pos ⟨symmetrize Z₀, transpose_symmetrize Z₀, hZ₀⟩
    exact (h₁.trans_gt h₂).ne'
  have c₁ : Continuous fun Z : Fin 2 → Fin 2 → ℂ ↦ 4 * (1 + |(symmetrize Z 0 0).re| +
      |(symmetrize Z 0 1).re| + |(symmetrize Z 1 1).re|) ^ 2 :=
    continuous_const.mul ((((continuous_const.add (hx 0 0).abs).add (hx 0 1).abs).add
      (hx 1 1).abs).pow 2)
  have c₂ : Continuous fun Z : Fin 2 → Fin 2 → ℂ ↦ 1 + (symmetrize Z 0 0).im +
      (symmetrize Z 1 1).im + |(symmetrize Z 0 1).im| :=
    ((continuous_const.add (hy 0 0)).add (hy 1 1)).add (hy 0 1).abs
  have c₃ : Continuous fun Z : Fin 2 → Fin 2 → ℂ ↦ (symmetrize Z 0 0).im * (symmetrize Z 1 1).im -
      (symmetrize Z 0 1).im ^ 2 :=
    ((hy 0 0).mul (hy 1 1)).sub ((hy 0 1).pow 2)
  exact c₁.continuousAt.mul (continuousAt_const.add (c₂.continuousAt.div c₃.continuousAt hdet))

/-- **The Siegel Eisenstein series `ψ_k` of degree `2` is holomorphic** for `k > 3`: around each
point the terms are bounded by a summable family, locally uniformly. -/
lemma isHolomorphic_siegelEisensteinSeries (hk : 3 < k) :
    IsHolomorphic fun Z : SiegelUpperHalfSpace (Fin 2) ↦ siegelEisensteinSeries k Z := by
  rw [isHolomorphic_iff_differentiableOn]
  intro Z₀ hZ₀
  have hP : ∀ᶠ Z in 𝓝 Z₀, Z ∈ symmetrizePreimage (Fin 2) :=
    isOpen_symmetrizePreimage.eventually_mem hZ₀
  have hU : ∀ᶠ Z in 𝓝 Z₀, Z ∈ symmetrizePreimage (Fin 2) ∧
      siegelK (symmetrize Z) < siegelK (symmetrize Z₀) + 1 :=
    hP.and <| (continuousAt_siegelK hZ₀).eventually_lt continuousAt_const (by linarith)
  rcases eventually_nhds_iff_ball.mp hU with ⟨r, hr, hball⟩
  have hd (x : SiegelParabolicCosets (Fin 2)) : DifferentiableOn ℂ
      (extend fun τ ↦ siegelEisensteinTerm k τ x.out) (ball Z₀ (3 * (r / 3))) := by
    refine (isHolomorphic_iff_differentiableOn.mp
      (isHolomorphic_det_denom_zpow (map (Int.castRingHom ℝ) x.out) (-k))).mono fun Z hZ ↦
        (hball Z ?_).1
    rwa [mul_div_cancel₀ _ three_ne_zero] at hZ
  have hK₀ : 0 < siegelK (symmetrize Z₀) :=
    siegelK_pos ⟨symmetrize Z₀, transpose_symmetrize Z₀, hZ₀⟩
  have hb (x : SiegelParabolicCosets (Fin 2)) (Z : Fin 2 → Fin 2 → ℂ)
      (hZ : Z ∈ ball Z₀ (3 * (r / 3))) : ‖extend (fun τ ↦ siegelEisensteinTerm k τ x.out) Z‖ ≤
        (siegelK (symmetrize Z₀) + 1) ^ k * ‖siegelPlucker x.out‖ ^ (-k) := by
    have hZ' : Z ∈ ball Z₀ r := by
      rwa [mul_div_cancel₀ _ three_ne_zero] at hZ
    rw [extend_of_mem _ (hball Z hZ').1]
    refine (norm_siegelEisensteinTerm_le x.out _ (by linarith)).trans ?_
    refine mul_le_mul_of_nonneg_right (zpow_le_zpow_left₀ (by linarith)
      (siegelK_pos ⟨symmetrize Z, transpose_symmetrize Z, (hball Z hZ').1⟩).le (hball Z hZ').2.le)
      (zpow_nonneg (norm_nonneg _) _)
  refine ((differentiableAt_tsum_of_bound ((summable_norm_siegelPlucker_zpow hk).mul_left _)
    (div_pos hr three_pos) hd hb).congr_of_eventuallyEq ?_).differentiableWithinAt
  refine hP.mono fun Z hZ ↦ ?_
  rw [extend_of_mem _ hZ, siegelEisensteinSeries]
  exact tsum_congr fun x ↦ (extend_of_mem (fun τ ↦ siegelEisensteinTerm k τ x.out) hZ).symm

/-! ### The Siegel Eisenstein series in `M_{k,0}(Sp(4, ℤ))` -/

lemma symPowerRep_zero (g : GL (Fin 2) ℂ) (v : Sym[ℂ]^0 (Fin 2 → ℂ)) :
    TauCeti.symPowerRep ℂ 2 0 g v = v := by
  have hv : v ∈ Submodule.span ℂ (Set.range (SymmetricPower.tprod ℂ)) := by
    rw [SymmetricPower.span_tprod_eq_top]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨m, rfl⟩
    exact (Representation.symmetricPower_apply_tprod _ _ _ _).trans
      (congrArg _ (Subsingleton.elim _ _))
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, hx, hy]
  | smul a x _ hx =>
    rw [map_smul, hx]

variable (k) in
/-- The Siegel Eisenstein series `ψ_k` as a function with values in `Sym⁰(ℂ²) ≅ ℂ`, the space of
`ρ_{k,0} = det^k`. -/
noncomputable def siegelEisensteinKJ : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^0 (Fin 2 → ℂ) :=
  fun W ↦ siegelEisensteinSeries k W • ⨂ₛ[ℂ] _ : Fin 0, (Pi.single 0 1 : Fin 2 → ℂ)

private lemma slash_siegelEisensteinKJ (hk' : Even k) :
    slash (rhoKJ k 0) (map (Int.castRingHom ℝ) β) (siegelEisensteinKJ k) =
      siegelEisensteinKJ k := by
  funext W
  have h₀ : (denom (map (Int.castRingHom ℝ) β) W.val).det ≠ 0 := (isUnit_det_denom _ _).ne_zero
  rw [slash_apply, rhoKJ_denomGL_inv_apply, symPowerRep_zero, siegelEisensteinKJ,
    siegelEisensteinSeries_smul W β hk', siegelEisensteinKJ, smul_smul, zpow_neg,
    inv_mul_cancel_left₀ (zpow_ne_zero _ h₀)]

private lemma isHolomorphic_siegelEisensteinKJ (hk : 3 < k) :
    IsHolomorphic (siegelEisensteinKJ k) := by
  intro φ
  refine ((isHolomorphic_iff_differentiableOn.mp
    (isHolomorphic_siegelEisensteinSeries hk)).mul_const
      (φ (⨂ₛ[ℂ] _ : Fin 0, Pi.single 0 1))).congr fun Z hZ ↦ ?_
  rw [extend_of_mem _ hZ, extend_of_mem _ hZ]
  simp [siegelEisensteinKJ]

/-- **The Siegel Eisenstein series `ψ_k` of degree `2` is a Siegel modular form** of weight `k` on
`Sp(4, ℤ)`, for even `k > 3`. -/
lemma siegelEisensteinKJ_mem_modularFormsKJ (hk : 3 < k) (hk' : Even k) :
    siegelEisensteinKJ k ∈ modularFormsKJ k 0 (integral (Fin 2)) :=
  mem_modularFormsKJ_of_slash_eq k (isHolomorphic_siegelEisensteinKJ hk)
    fun β _ ↦ slash_siegelEisensteinKJ β hk'

private lemma isGLIntInvariant_tprod (hk' : Even k) :
    IsGLIntInvariant (rhoKJ k 0) (⨂ₛ[ℂ] _ : Fin 0, (Pi.single 0 1 : Fin 2 → ℂ)) := by
  intro D
  have hD : IsUnit (D : Matrix (Fin 2) (Fin 2) ℤ).det := (isUnit_iff_isUnit_det _).mp D.isUnit
  have hm : ((GeneralLinearGroup.map (Int.castRingHom ℂ) D : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = (Int.castRingHom ℂ).mapMatrix (D : Matrix (Fin 2) (Fin 2) ℤ) :=
    rfl
  have e : rhoKJ k 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) D)
      (⨂ₛ[ℂ] _ : Fin 0, (Pi.single 0 1 : Fin 2 → ℂ)) =
        (((GeneralLinearGroup.map (Int.castRingHom ℂ) D).det ^ k : ℂˣ) : ℂ) •
          TauCeti.symPowerRep ℂ 2 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) D)
            (⨂ₛ[ℂ] _ : Fin 0, (Pi.single 0 1 : Fin 2 → ℂ)) :=
    rfl
  rw [e, symPowerRep_zero, Units.val_zpow_eq_zpow_val, GeneralLinearGroup.val_det_apply, hm,
    ← RingHom.map_det]
  rcases Int.isUnit_iff.mp hD with h | h <;> simp [h, hk'.neg_one_zpow]

/-- **`ψ_k` is the vector-valued Siegel Eisenstein series of the generator of `Sym⁰(ℂ²)`**, for
`k > 3`, so it lies in the space `E_{k,0}(Sp(4, ℤ))` for even `k`. -/
lemma isVectorSiegelEisensteinSeries_siegelEisensteinKJ (hk : 3 < k) :
    IsVectorSiegelEisensteinSeries (rhoKJ k 0) (⨂ₛ[ℂ] _ : Fin 0, Pi.single 0 1)
      (siegelEisensteinKJ k) := by
  intro Z φ
  have h : HasSum (fun x : SiegelParabolicCosets (Fin 2) ↦ siegelEisensteinTerm k Z x.out *
      φ (⨂ₛ[ℂ] _ : Fin 0, Pi.single 0 1)) ((∑' x : SiegelParabolicCosets (Fin 2),
        siegelEisensteinTerm k Z x.out) * φ (⨂ₛ[ℂ] _ : Fin 0, Pi.single 0 1)) :=
    (summable_siegelEisensteinTerm Z hk).hasSum.mul_right _
  have e : φ (siegelEisensteinKJ k Z) = (∑' x : SiegelParabolicCosets (Fin 2),
      siegelEisensteinTerm k Z x.out) * φ (⨂ₛ[ℂ] _ : Fin 0, Pi.single 0 1) := by
    rw [siegelEisensteinKJ, map_smul, smul_eq_mul, siegelEisensteinSeries]
  rw [e]
  refine h.congr_fun fun x ↦ ?_
  rw [vectorSiegelEisensteinTerm, rhoKJ_denomGL_inv_apply, symPowerRep_zero, map_smul, smul_eq_mul,
    siegelEisensteinTerm]

lemma siegelEisensteinKJ_mem_siegelEisensteinSubspaceKJ (hk : 3 < k) (hk' : Even k) :
    siegelEisensteinKJ k ∈ siegelEisensteinSubspaceKJ k 0 :=
  Submodule.subset_span ⟨_, isGLIntInvariant_tprod hk',
    isVectorSiegelEisensteinSeries_siegelEisensteinKJ hk⟩

/-! ### The constant term -/

/-- The point `diag(is, is)` of `ℋ₂`. -/
def scalarPoint (s : Set.Ioi (0 : ℝ)) : SiegelUpperHalfSpace (Fin 2) :=
  diagPoint ⟨(s : ℝ) * I, by
    have h : (0 : ℝ) < s := s.2
    simpa using h⟩ s

variable {s : Set.Ioi (0 : ℝ)}

variable (s) in
private lemma normSq_det_scalarPoint :
    ‖(denom (map (Int.castRingHom ℝ) δ) (scalarPoint s).val).det‖ ^ 2 =
      (siegelPlucker δ 4 : ℝ) ^ 2 + (siegelPlucker δ 0 : ℝ) ^ 2 * (s : ℝ) ^ 4 + (s : ℝ) ^ 2 *
        ((siegelPlucker δ 1 : ℝ) ^ 2 + (siegelPlucker δ 3 : ℝ) ^ 2 +
          2 * (siegelPlucker δ 2 : ℝ) ^ 2) := by
  have hQ : (siegelPlucker δ 0 : ℝ) * siegelPlucker δ 4 + (siegelPlucker δ 2 : ℝ) ^ 2 +
      siegelPlucker δ 1 * siegelPlucker δ 3 = 0 :=
    siegelPlucker_quadric δ
  rw [← normSq_eq_norm_sq, det_denom_eq_siegelPlucker, normSq_apply]
  simp [scalarPoint, diagPoint]
  linear_combination (-2 * (s : ℝ) ^ 2) * hQ

private lemma one_le_sq_intCast {x : ℤ} (hx : x ≠ 0) : (1 : ℝ) ≤ (x : ℝ) ^ 2 := by
  have h : 0 < x ^ 2 := by
    positivity
  have h₁ : (1 : ℤ) ≤ x ^ 2 := by
    omega
  exact_mod_cast h₁

private lemma le_norm_det_scalarPoint (hs : (1 : ℝ) ≤ s)
    (h : ¬(siegelPlucker δ 0 = 0 ∧ siegelPlucker δ 1 = 0 ∧ siegelPlucker δ 2 = 0 ∧
      siegelPlucker δ 3 = 0)) :
    (s : ℝ) ≤ ‖(denom (map (Int.castRingHom ℝ) δ) (scalarPoint s).val).det‖ := by
  have hs₀ : (0 : ℝ) < s := s.2
  have hs₂ : (s : ℝ) ^ 2 ≤ (s : ℝ) ^ 4 := pow_le_pow_right₀ hs (by norm_num)
  have hsq : (s : ℝ) ^ 2 ≤ ‖(denom (map (Int.castRingHom ℝ) δ) (scalarPoint s).val).det‖ ^ 2 := by
    rw [normSq_det_scalarPoint]
    have h₄ : 0 ≤ (siegelPlucker δ 4 : ℝ) ^ 2 := sq_nonneg _
    have h₀ : 0 ≤ (siegelPlucker δ 0 : ℝ) ^ 2 := sq_nonneg _
    have h₁ : 0 ≤ (siegelPlucker δ 1 : ℝ) ^ 2 := sq_nonneg _
    have h₂ : 0 ≤ (siegelPlucker δ 2 : ℝ) ^ 2 := sq_nonneg _
    have h₃ : 0 ≤ (siegelPlucker δ 3 : ℝ) ^ 2 := sq_nonneg _
    have hA : 0 ≤ (s : ℝ) ^ 2 * ((siegelPlucker δ 1 : ℝ) ^ 2 + (siegelPlucker δ 3 : ℝ) ^ 2 +
        2 * (siegelPlucker δ 2 : ℝ) ^ 2) := by
      positivity
    have hB : 0 ≤ (siegelPlucker δ 0 : ℝ) ^ 2 * (s : ℝ) ^ 4 := by
      positivity
    by_cases e₀ : siegelPlucker δ 0 = 0
    · refine le_add_of_nonneg_of_le (by positivity) ?_
      refine le_mul_of_one_le_right (by positivity) ?_
      by_cases e₁ : siegelPlucker δ 1 = 0
      · by_cases e₂ : siegelPlucker δ 2 = 0
        · have e₃ : siegelPlucker δ 3 ≠ 0 := fun e₃ ↦ h ⟨e₀, e₁, e₂, e₃⟩
          linarith [one_le_sq_intCast e₃]
        · linarith [one_le_sq_intCast e₂]
      · linarith [one_le_sq_intCast e₁]
    · have h₅ : (s : ℝ) ^ 4 ≤ (siegelPlucker δ 0 : ℝ) ^ 2 * (s : ℝ) ^ 4 :=
        le_mul_of_one_le_left (by positivity) (one_le_sq_intCast e₀)
      linarith
  exact (pow_le_pow_iff_left₀ hs₀.le (norm_nonneg _) two_ne_zero).mp hsq

private lemma siegelK_scalarPoint_le (hs : (1 : ℝ) ≤ s) : siegelK (scalarPoint s).val ≤ 16 := by
  have hs₀ : (0 : ℝ) < s := s.2
  have e : siegelK (scalarPoint s).val = 4 * (1 + (1 + (s : ℝ) + s) / (s * s)) := by
    simp [siegelK, scalarPoint, diagPoint]
  rw [e]
  have h : (1 + (s : ℝ) + s) / (s * s) ≤ 3 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

private lemma norm_siegelEisensteinTerm_scalarPoint_le (hk : 0 < k) (hs : (1 : ℝ) ≤ s) :
    ‖siegelEisensteinTerm k (scalarPoint s) δ‖ ≤ (16 : ℝ) ^ k * ‖siegelPlucker δ‖ ^ (-k) :=
  (norm_siegelEisensteinTerm_le δ _ hk).trans (mul_le_mul_of_nonneg_right (zpow_le_zpow_left₀ hk.le
    (siegelK_pos _).le (siegelK_scalarPoint_le hs)) (zpow_nonneg (norm_nonneg _) _))

private lemma siegelEisensteinTerm_one : siegelEisensteinTerm k Z 1 = 1 := by
  have h : denom (map (Int.castRingHom ℝ) (1 : symplecticGroup (Fin 2) ℤ)) Z.val = 1 := by
    rw [map_one, ← coe_denomGL, denomGL_one, Units.val_one]
  rw [siegelEisensteinTerm, h, det_one]
  simp

private lemma tendsto_siegelEisensteinTerm_scalarPoint (hk : 0 < k)
    {x : SiegelParabolicCosets (Fin 2)} (hx : x ≠ ⟦1⟧) : Tendsto
      (fun s : Set.Ioi (0 : ℝ) ↦ siegelEisensteinTerm k (scalarPoint s) x.out) atTop (𝓝 0) := by
  have hne : ¬(siegelPlucker x.out 0 = 0 ∧ siegelPlucker x.out 1 = 0 ∧ siegelPlucker x.out 2 = 0 ∧
      siegelPlucker x.out 3 = 0) := fun h ↦ hx <| by
    have hmem : x.out ∈ siegelParabolic (Fin 2) ℤ :=
      mem_siegelParabolic_of_siegelPlucker _ h.1 h.2.1 h.2.2.1 h.2.2.2
    rw [← Quotient.out_eq x]
    refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
    simpa using inv_mem hmem
  have ht : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ (t : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have h₁ : Tendsto (fun s : Set.Ioi (0 : ℝ) ↦ (s : ℝ) ^ (-k)) atTop (𝓝 0) :=
    (tendsto_zpow_atTop_zero (by linarith)).comp ht
  refine squeeze_zero_norm' ?_ h₁
  filter_upwards [ht.eventually_ge_atTop 1] with s hs
  have hs₀ : (0 : ℝ) < s := s.2
  rw [siegelEisensteinTerm, norm_zpow, zpow_neg, zpow_neg]
  exact inv_anti₀ (zpow_pos hs₀ k) (zpow_le_zpow_left₀ hk.le hs₀.le
    (le_norm_det_scalarPoint x.out hs hne))

/-- **The constant term of the Siegel Eisenstein series**: `ψ_k(diag(is, is)) → 1` as `s → ∞`, for
even `k > 3`: the term of the trivial coset is `1`, and the others tend to `0`, as
`|det(C(is) + D)| ≥ s` for `C ≠ 0`, dominated by `16^k ‖p(C, D)‖^{-k}`. -/
lemma tendsto_siegelEisensteinSeries_scalarPoint (hk : 3 < k) (hk' : Even k) :
    Tendsto (fun s : Set.Ioi (0 : ℝ) ↦ siegelEisensteinSeries k (scalarPoint s)) atTop (𝓝 1) := by
  classical
  have hk₀ : 0 < k := by
    linarith
  have ht : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ (t : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have hlim (x : SiegelParabolicCosets (Fin 2)) : Tendsto
      (fun s : Set.Ioi (0 : ℝ) ↦ siegelEisensteinTerm k (scalarPoint s) x.out) atTop
      (𝓝 (if x = ⟦1⟧ then 1 else 0)) := by
    split_ifs with hx
    · subst hx
      refine tendsto_const_nhds.congr fun s ↦ ?_
      rw [siegelEisensteinTerm_out _ _ _ hk', siegelEisensteinTerm_one]
    · exact tendsto_siegelEisensteinTerm_scalarPoint hk₀ hx
  have hb : ∀ᶠ s : Set.Ioi (0 : ℝ) in atTop, ∀ x : SiegelParabolicCosets (Fin 2),
      ‖siegelEisensteinTerm k (scalarPoint s) x.out‖ ≤
        (16 : ℝ) ^ k * ‖siegelPlucker x.out‖ ^ (-k) := by
    filter_upwards [ht.eventually_ge_atTop 1] with s hs x
    exact norm_siegelEisensteinTerm_scalarPoint_le x.out hk₀ hs
  have key : Tendsto (fun s : Set.Ioi (0 : ℝ) ↦ ∑' x : SiegelParabolicCosets (Fin 2),
      siegelEisensteinTerm k (scalarPoint s) x.out) atTop
      (𝓝 (∑' x : SiegelParabolicCosets (Fin 2), if x = ⟦1⟧ then 1 else 0)) :=
    tendsto_tsum_of_dominated_convergence ((summable_norm_siegelPlucker_zpow hk).mul_left _) hlim hb
  rwa [tsum_ite_eq] at key

end SiegelUpperHalfSpace
