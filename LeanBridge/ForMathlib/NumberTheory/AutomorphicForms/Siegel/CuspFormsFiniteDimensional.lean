import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PeterssonUnfolding
import Mathlib.Algebra.Order.Chebyshev

/-!
# The cusp forms of degree 2 and weight `ρ_{k,j}` on `Sp(4, ℤ)` are finite-dimensional

The invariant function `c(ρ(Y) F(Z), F(Z))` of a cusp form `F`, for `Y = Im Z` and the Hermitian
form `c = symHermitianForm`, is bounded, by the decay of `F` on the Siegel set. Its values at a
point `Z₀` of the Siegel set and at the shifted points `Z₀ + (x - i / 5) 1` are comparable, up to a
constant depending only on `k` and `j`. If the Fourier coefficients `a(n)` of `F` vanish for
`tr n < R`, then the Fourier series in `x` of `F(Z₀ + (x - i / 5) 1)`, whose frequencies are the
traces `tr n`, shows that the value at `Z₀` is at most `θ_R` times the supremum of the invariant
function, with `θ_R → 0` as `R → ∞`. So `F = 0` for `R` large, and `F` is determined by the finitely
many coefficients `a(n)` with `n` positive semidefinite and `tr n < R`. No maximum principle is
needed: the coefficient of each frequency is bounded by the supremum of the series.

This is the finiteness behind the decomposition `M_{j,k}(Γ₂) = S_{j,k}(Γ₂) ⊕ N_{j,k}(Γ₂)` of LMFDB
`mf.siegel.subspace.degree.two`.

## Main results

* `SiegelUpperHalfSpace.norm_tsum_mul_pow_le`: a Fourier series with large frequencies is small
  inside the disc.
* `SiegelUpperHalfSpace.finiteDimensional_cuspFormsKJ`: the space `S_{j,k}(Γ₂)` is
  finite-dimensional.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_mul zpow_neg one_zpow

open Complex MeasureTheory Module Real Set SymplecticGroup

open scoped ComplexConjugate ComplexOrder TensorProduct

namespace SiegelUpperHalfSpace

/-! ### Fourier series with large frequencies -/

variable {ι : Type*} [Countable ι] {c : ι → ℂ} {m : ι → ℕ} {R : ℕ} {l B : ℝ}

private lemma norm_tsum_ite_le (hc : Summable fun n ↦ ‖c n‖)
    (hB : ∀ x ∈ Icc (0 : ℝ) 1, ‖∑' n, c n * cexp (2 * π * I * ((m n : ℂ) * x))‖ ≤ B) (k : ℕ) :
    ‖∑' n, if m n = k then c n else 0‖ ≤ B := by
  have hnorm (n : ι) (x : ℝ) :
      ‖c n * cexp (2 * π * I * (((m n : ℤ) - (k : ℤ) : ℤ) * x))‖ = ‖c n‖ := by
    have e : 2 * π * I * ((((m n : ℤ) - (k : ℤ) : ℤ) : ℂ) * x) =
        ((2 * π * (((m n : ℤ) - (k : ℤ) : ℤ) : ℝ) * x : ℝ) : ℂ) * I := by
      push_cast
      ring1
    rw [norm_mul, e, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hcont (n : ι) :
      Continuous fun x : ℝ ↦ c n * cexp (2 * π * I * (((m n : ℤ) - (k : ℤ) : ℤ) * x)) := by
    fun_prop
  have hint (n : ι) : Integrable (fun x : ℝ ↦
      c n * cexp (2 * π * I * (((m n : ℤ) - (k : ℤ) : ℤ) * x))) (volume.restrict (Icc (0 : ℝ) 1)) :=
    (hcont n).integrableOn_Icc
  have hsum : Summable fun n ↦ ∫ x in Icc (0 : ℝ) 1,
      ‖c n * cexp (2 * π * I * (((m n : ℤ) - (k : ℤ) : ℤ) * x))‖ := by
    simp only [hnorm]
    simpa using hc
  have hval (n : ι) : ∫ x in Icc (0 : ℝ) 1,
      c n * cexp (2 * π * I * (((m n : ℤ) - (k : ℤ) : ℤ) * x)) = if m n = k then c n else 0 := by
    split_ifs with hn
    · simp [hn]
    · rw [integral_const_mul, integral_cexp_int_eq_zero (by omega), mul_zero]
  have h₁ : ∑' n, (∫ x in Icc (0 : ℝ) 1, c n * cexp (2 * π * I * (((m n : ℤ) - (k : ℤ) : ℤ) * x))) =
      ∫ x in Icc (0 : ℝ) 1, ∑' n, c n * cexp (2 * π * I * (((m n : ℤ) - (k : ℤ) : ℤ) * x)) :=
    integral_tsum_of_summable_integral_norm hint hsum
  simp only [hval] at h₁
  rw [h₁]
  have hfun (x : ℝ) : ∑' n, c n * cexp (2 * π * I * (((m n : ℤ) - (k : ℤ) : ℤ) * x)) =
      (∑' n, c n * cexp (2 * π * I * ((m n : ℂ) * x))) * cexp (-(2 * π * I * ((k : ℂ) * x))) := by
    rw [← tsum_mul_right]
    refine tsum_congr fun n ↦ ?_
    rw [mul_assoc (c n), ← Complex.exp_add]
    congr 2
    push_cast
    ring1
  simp only [hfun]
  simpa using norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (0 : ℝ) 1) (C := B)
    (f := fun x : ℝ ↦ (∑' n, c n * cexp (2 * π * I * ((m n : ℂ) * x))) *
      cexp (-(2 * π * I * ((k : ℂ) * x)))) (by simp) fun x hx ↦ by
      have e : -(2 * π * I * ((k : ℂ) * x)) = ((-(2 * π * k * x) : ℝ) : ℂ) * I := by
        push_cast
        ring1
      rw [norm_mul, e, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hB x hx

/-- **A Fourier series with large frequencies is small inside the disc**: if
`∑ c_n e^{2πi m_n x}`, with absolutely summable `c_n` and `m_n ≥ R` for `c_n ≠ 0`, is bounded by
`B`, then `|∑ c_n l^{m_n}| ≤ B l^R / (1 - l)` for `0 ≤ l < 1`: the coefficient of each frequency is
bounded by `B`. -/
lemma norm_tsum_mul_pow_le (hc : Summable fun n ↦ ‖c n‖) (hR : ∀ n, c n ≠ 0 → R ≤ m n) (hl₀ : 0 ≤ l)
    (hl₁ : l < 1) (hB : ∀ x ∈ Icc (0 : ℝ) 1, ‖∑' n, c n * cexp (2 * π * I * ((m n : ℂ) * x))‖ ≤ B) :
    ‖∑' n, c n * (l : ℂ) ^ m n‖ ≤ B * (l ^ R / (1 - l)) := by
  have hs : Summable fun n ↦ c n * (l : ℂ) ^ m n := by
    refine Summable.of_norm_bounded hc fun n ↦ ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hl₀]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hl₀ hl₁.le)
  have h₁ :
      HasSum (fun k : ℕ ↦ ∑' b : m ⁻¹' {k}, c b * (l : ℂ) ^ m b) (∑' n, c n * (l : ℂ) ^ m n) :=
    hs.hasSum.tsum_fiberwise m
  have hin (k : ℕ) :
      ∑' b : m ⁻¹' {k}, c b * (l : ℂ) ^ m b = (l : ℂ) ^ k * ∑' n, if m n = k then c n else 0 := by
    have e (b : m ⁻¹' {k}) : c b * (l : ℂ) ^ m b = (l : ℂ) ^ k * c b := by
      have h₂ : m b = k := b.2
      rw [h₂, mul_comm]
    rw [tsum_congr e, tsum_mul_left, tsum_subtype (m ⁻¹' {k}) c]
    refine congrArg (_ * ·) (tsum_congr fun n ↦ ?_)
    by_cases hn : m n = k
    · rw [Set.indicator_of_mem (by exact hn), ite_eq_left_iff.mpr fun h ↦ absurd hn h]
    · rw [Set.indicator_of_notMem (by exact hn), ite_eq_right_iff.mpr fun h ↦ absurd h hn]
  simp only [hin] at h₁
  have hg : HasSum (fun k : ℕ ↦ if R ≤ k then B * l ^ k else 0) (B * (l ^ R / (1 - l))) := by
    refine (hasSum_nat_add_iff' R).mp ?_
    have e : ∑ i ∈ Finset.range R, (if R ≤ i then B * l ^ i else 0) = 0 :=
      Finset.sum_eq_zero fun i hi ↦ ite_eq_right_iff.mpr fun h ↦
        absurd h (not_le.mpr (Finset.mem_range.mp hi))
    rw [e, sub_zero]
    convert (hasSum_geometric_of_lt_one hl₀ hl₁).mul_left (B * l ^ R) using 1
    · funext i
      rw [ite_eq_left_iff.mpr fun h ↦ absurd (Nat.le_add_left R i) h, pow_add]
      ring1
    · ring1
  refine h₁.norm_le_of_bounded hg fun k ↦ ?_
  split_ifs with hk
  · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hl₀, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_tsum_ite_le hc hB k) (pow_nonneg hl₀ k)
  · have h₂ : (∑' n, if m n = k then c n else 0) = 0 := by
      refine (tsum_congr fun n ↦ ?_).trans tsum_zero
      split_ifs with hn
      · by_contra hc₀
        exact hk (hn ▸ hR n hc₀)
      · rfl
    rw [h₂, mul_zero, norm_zero]

/-! ### A shift of a point of the Siegel set -/

private lemma posDef_of_fin_two {Y : Matrix (Fin 2) (Fin 2) ℝ} (hs : Y 1 0 = Y 0 1) (h₀ : 0 < Y 0 0)
    (hd : 0 < Y 0 0 * Y 1 1 - Y 0 1 ^ 2) : Y.PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun v hv ↦ ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hs]
  · simp only [dotProduct, mulVec, Fin.sum_univ_two, hs]
    have h₁ :
        0 < Y 0 0 * (v 0 * (Y 0 0 * v 0 + Y 0 1 * v 1) + v 1 * (Y 0 1 * v 0 + Y 1 1 * v 1)) := by
      have e : Y 0 0 * (v 0 * (Y 0 0 * v 0 + Y 0 1 * v 1) + v 1 * (Y 0 1 * v 0 + Y 1 1 * v 1)) =
          (Y 0 0 * v 0 + Y 0 1 * v 1) ^ 2 + (Y 0 0 * Y 1 1 - Y 0 1 ^ 2) * v 1 ^ 2 := by
        ring1
      rw [e]
      by_cases h₄ : v 1 = 0
      · have h₅ : v 0 ≠ 0 := fun h₅ ↦ hv <| by
          ext i
          fin_cases i <;> simp [h₄, h₅]
        have h₂ : 0 < (Y 0 0 * v 0) ^ 2 := by
          positivity
        simpa [h₄] using h₂
      · have h₂ : 0 < (Y 0 0 * Y 1 1 - Y 0 1 ^ 2) * v 1 ^ 2 := mul_pos hd (by positivity)
        linarith [sq_nonneg (Y 0 0 * v 0 + Y 0 1 * v 1)]
    exact (mul_pos_iff_of_pos_left h₀).mp h₁

variable {Z₀ : SiegelUpperHalfSpace (Fin 2)}

private lemma det_map_im_eq (Z : SiegelUpperHalfSpace (Fin 2)) :
    (Z.val.map im).det = (Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im ^ 2 := by
  have hZs : Z.val 1 0 = Z.val 0 1 := congrFun (congrFun Z.transpose_val 0) 1
  simp [det_fin_two, hZs, pow_two]

private lemma mul_le_im_mul_im_sub_sq (hZ₀ : Z₀ ∈ siegelSet) :
    3 / 4 * ((Z₀.val 0 0).im * (Z₀.val 1 1).im) ≤ (Z₀.val 0 0).im * (Z₀.val 1 1).im -
      (Z₀.val 0 1).im ^ 2 :=
  det_map_im_eq Z₀ ▸ mul_le_det_im hZ₀

private lemma sub_mul_sub_sub_sq_pos (hZ₀ : Z₀ ∈ siegelSet) :
    0 < ((Z₀.val 0 0).im - 1 / 5) * ((Z₀.val 1 1).im - 1 / 5) - (Z₀.val 0 1).im ^ 2 := by
  have h₀ : 4 / 5 ≤ (Z₀.val 0 0).im := four_fifths_le_im_zero_zero hZ₀
  have h₁ : 4 / 5 ≤ (Z₀.val 1 1).im := four_fifths_le_im_one_one hZ₀
  have h₂ : 3 / 4 * ((Z₀.val 0 0).im * (Z₀.val 1 1).im) ≤ (Z₀.val 0 0).im * (Z₀.val 1 1).im -
      (Z₀.val 0 1).im ^ 2 :=
    mul_le_im_mul_im_sub_sq hZ₀
  nlinarith

variable (hZ₀ : Z₀ ∈ siegelSet) (x : ℝ)

/-- The point `Z₀ + (x - i / 5) 1` of `ℋ₂`, for `Z₀` in the Siegel set. -/
private noncomputable def shiftedPoint : SiegelUpperHalfSpace (Fin 2) where
  val := Z₀.val + (((x : ℂ) - I / 5)) • 1
  transpose_val := by
    rw [transpose_add, Z₀.transpose_val, transpose_smul, transpose_one]
  posDef_im := by
    have hZs : Z₀.val 1 0 = Z₀.val 0 1 := congrFun (congrFun Z₀.transpose_val 0) 1
    have h₀ : 4 / 5 ≤ (Z₀.val 0 0).im := four_fifths_le_im_zero_zero hZ₀
    have hD : 0 < ((Z₀.val 0 0).im - 1 / 5) * ((Z₀.val 1 1).im - 1 / 5) - (Z₀.val 0 1).im ^ 2 :=
      sub_mul_sub_sub_sq_pos hZ₀
    refine posDef_of_fin_two ?_ ?_ ?_
    · simp [hZs]
    · simp
      linarith
    · simp
      nlinarith

private lemma im_shiftedPoint (i k : Fin 2) :
    ((shiftedPoint hZ₀ x).val i k).im = (Z₀.val i k).im - if i = k then 1 / 5 else 0 := by
  by_cases h : i = k
  · simp [shiftedPoint, h]
    ring1
  · simp [shiftedPoint, h]

variable {M L : GL (Fin 2) ℂ}

private lemma trace_star_mul_self_eq (hM : imGL Z₀ = star M * M) {Z₁ : SiegelUpperHalfSpace (Fin 2)}
    (hL : imGL Z₁ = star L * L) : trace ((star (M * L⁻¹) * (M * L⁻¹) : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = trace ((imGL Z₀ * (imGL Z₁)⁻¹ : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) := by
  have h₁ : star (M * L⁻¹) * (M * L⁻¹) = star L⁻¹ * (imGL Z₀ * L⁻¹) := by
    rw [hM, star_mul]
    simp only [mul_assoc]
  have h₂ : imGL Z₀ * (imGL Z₁)⁻¹ = imGL Z₀ * L⁻¹ * star L⁻¹ := by
    rw [hL, mul_inv_rev, star_inv, mul_assoc]
  rw [h₁, h₂, Units.val_mul, Units.val_mul, trace_mul_comm, Units.val_mul, Units.val_mul]

private lemma trace_imGL_mul_inv_le :
    (trace ((imGL Z₀ * (imGL (shiftedPoint hZ₀ x))⁻¹ : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ)).re ≤ 4 := by
  have hZs : Z₀.val 1 0 = Z₀.val 0 1 := congrFun (congrFun Z₀.transpose_val 0) 1
  have h₀ : 4 / 5 ≤ (Z₀.val 0 0).im := four_fifths_le_im_zero_zero hZ₀
  have h₁ : 4 / 5 ≤ (Z₀.val 1 1).im := four_fifths_le_im_one_one hZ₀
  have h₂ : 3 / 4 * ((Z₀.val 0 0).im * (Z₀.val 1 1).im) ≤ (Z₀.val 0 0).im * (Z₀.val 1 1).im -
      (Z₀.val 0 1).im ^ 2 :=
    mul_le_im_mul_im_sub_sq hZ₀
  have hD : 0 < ((Z₀.val 0 0).im - 1 / 5) * ((Z₀.val 1 1).im - 1 / 5) - (Z₀.val 0 1).im ^ 2 :=
    sub_mul_sub_sub_sq_pos hZ₀
  have hY₀ : ((imGL Z₀ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Z₀.val 0 0).im : ℂ), (Z₀.val 0 1).im; (Z₀.val 0 1).im, (Z₀.val 1 1).im] := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [hZs]
  have hY₁ : ((imGL (shiftedPoint hZ₀ x) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(((Z₀.val 0 0).im - 1 / 5 : ℝ) : ℂ), (Z₀.val 0 1).im;
        (Z₀.val 0 1).im, (((Z₀.val 1 1).im - 1 / 5 : ℝ) : ℂ)] := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [im_shiftedPoint, hZs]
  generalize (Z₀.val 0 0).im = a at *
  generalize (Z₀.val 0 1).im = b at *
  generalize (Z₀.val 1 1).im = e at *
  have htr : trace ((imGL Z₀ * (imGL (shiftedPoint hZ₀ x))⁻¹ : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = (((((a - 1 / 5) * (e - 1 / 5) - b ^ 2)⁻¹ *
        (a * (e - 1 / 5) - 2 * b ^ 2 + e * (a - 1 / 5)) : ℝ)) : ℂ) := by
    rw [Units.val_mul, coe_units_inv, hY₀, hY₁, Matrix.inv_def, adjugate_fin_two_of,
      det_fin_two_of, Ring.inverse_eq_inv', Matrix.mul_smul, trace_smul, mul_fin_two,
      trace_fin_two_of, smul_eq_mul]
    push_cast
    ring1
  rw [htr, ofReal_re, inv_mul_le_iff₀ hD]
  nlinarith

private lemma norm_apply_le_two (hM : imGL Z₀ = star M * M)
    (hL : imGL (shiftedPoint hZ₀ x) = star L * L) (a b : Fin 2) :
    ‖((M * L⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) a b‖ ≤ 2 := by
  have h₁ : (trace ((imGL Z₀ * (imGL (shiftedPoint hZ₀ x))⁻¹ : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ)).re ≤ 4 :=
    trace_imGL_mul_inv_le hZ₀ x
  rw [← trace_star_mul_self_eq hM hL] at h₁
  generalize M * L⁻¹ = A at h₁
  have h₂ : trace ((star A * A : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((∑ c, ∑ d, ‖(A : Matrix (Fin 2) (Fin 2) ℂ) d c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Units.val_mul, Units.coe_star, star_eq_conjTranspose]
    simp only [trace, diag_apply, Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
    rw [← Complex.conj_mul']
    rfl
  rw [h₂, ofReal_re] at h₁
  have h₃ : ‖(A : Matrix (Fin 2) (Fin 2) ℂ) a b‖ ^ 2 ≤
      ∑ c, ∑ d, ‖(A : Matrix (Fin 2) (Fin 2) ℂ) d c‖ ^ 2 := by
    have h₄ :
        ‖(A : Matrix (Fin 2) (Fin 2) ℂ) a b‖ ^ 2 ≤ ∑ d, ‖(A : Matrix (Fin 2) (Fin 2) ℂ) d b‖ ^ 2 :=
      Finset.single_le_sum (f := fun d ↦ ‖(A : Matrix (Fin 2) (Fin 2) ℂ) d b‖ ^ 2)
        (fun d _ ↦ sq_nonneg _) (Finset.mem_univ a)
    exact h₄.trans (Finset.single_le_sum
      (f := fun c ↦ ∑ d, ‖(A : Matrix (Fin 2) (Fin 2) ℂ) d c‖ ^ 2)
        (fun c _ ↦ Finset.sum_nonneg fun d _ ↦ sq_nonneg _) (Finset.mem_univ b))
  exact abs_le_of_sq_le_sq' (by linarith) (by norm_num) |>.2

private lemma norm_det_sq {τ : SiegelUpperHalfSpace (Fin 2)} (hM : imGL τ = star M * M) :
    ‖(M : Matrix (Fin 2) (Fin 2) ℂ).det‖ ^ 2 = (τ.val.map im).det := by
  have h₁ : ((imGL τ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det =
      ((star M * M : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det := by
    rw [hM]
  simp only [coe_imGL, Units.val_mul, Units.coe_star, det_mul, star_eq_conjTranspose,
    det_conjTranspose, det_map_ofReal] at h₁
  have h₂ : star (M : Matrix (Fin 2) (Fin 2) ℂ).det * (M : Matrix (Fin 2) (Fin 2) ℂ).det =
      ((‖(M : Matrix (Fin 2) (Fin 2) ℂ).det‖ ^ 2 : ℝ) : ℂ) := by
    rw [ofReal_pow]
    exact Complex.conj_mul' _
  rw [h₂, ofReal_inj] at h₁
  exact h₁.symm

private lemma norm_det_mul_inv_sq_eq (hM : imGL Z₀ = star M * M) {Z₁ : SiegelUpperHalfSpace (Fin 2)}
    (hL : imGL Z₁ = star L * L) : ‖((M * L⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖ ^ 2 =
      (Z₀.val.map im).det / (Z₁.val.map im).det := by
  rw [← norm_det_sq hM, ← norm_det_sq hL, Units.val_mul, det_mul, coe_units_inv, det_nonsing_inv,
    Ring.inverse_eq_inv', norm_mul, norm_inv, mul_pow, inv_pow, div_eq_mul_inv]

private lemma det_map_im_shiftedPoint : ((shiftedPoint hZ₀ x).val.map im).det =
    ((Z₀.val 0 0).im - 1 / 5) * ((Z₀.val 1 1).im - 1 / 5) - (Z₀.val 0 1).im ^ 2 := by
  have hZs : Z₀.val 1 0 = Z₀.val 0 1 := congrFun (congrFun Z₀.transpose_val 0) 1
  simp [det_fin_two, im_shiftedPoint, hZs, pow_two]

private lemma one_le_norm_det_mul_inv_sq (hM : imGL Z₀ = star M * M)
    (hL : imGL (shiftedPoint hZ₀ x) = star L * L) :
    1 ≤ ‖((M * L⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖ ^ 2 := by
  have h₀ : 4 / 5 ≤ (Z₀.val 0 0).im := four_fifths_le_im_zero_zero hZ₀
  have h₁ : 4 / 5 ≤ (Z₀.val 1 1).im := four_fifths_le_im_one_one hZ₀
  rw [norm_det_mul_inv_sq_eq hM hL, det_map_im_shiftedPoint, det_map_im_eq,
    one_le_div (sub_mul_sub_sub_sq_pos hZ₀)]
  nlinarith

private lemma norm_det_mul_inv_sq_le_four (hM : imGL Z₀ = star M * M)
    (hL : imGL (shiftedPoint hZ₀ x) = star L * L) :
    ‖((M * L⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖ ^ 2 ≤ 4 := by
  have h₀ : 4 / 5 ≤ (Z₀.val 0 0).im := four_fifths_le_im_zero_zero hZ₀
  have h₁ : 4 / 5 ≤ (Z₀.val 1 1).im := four_fifths_le_im_one_one hZ₀
  have h₂ : 3 / 4 * ((Z₀.val 0 0).im * (Z₀.val 1 1).im) ≤ (Z₀.val 0 0).im * (Z₀.val 1 1).im -
      (Z₀.val 0 1).im ^ 2 :=
    mul_le_im_mul_im_sub_sq hZ₀
  rw [norm_det_mul_inv_sq_eq hM hL, det_map_im_shiftedPoint, det_map_im_eq,
    div_le_iff₀ (sub_mul_sub_sub_sq_pos hZ₀)]
  nlinarith [mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr h₁)]

/-! ### The norm on `Sym^j(ℂ²)` -/

variable {k : ℤ} {j : ℕ} (u : Sym[ℂ]^j (Fin 2 → ℂ))

/-- The squared norm `c(u, u)` of `u ∈ Sym^j(ℂ²)`, for the form `symHermitianForm`. -/
private noncomputable def symNormSq : ℝ :=
  ∑ r, ‖symCoord r u‖ ^ 2

private lemma symHermitianForm_self : symHermitianForm j u u = (symNormSq u : ℂ) := by
  rw [symHermitianForm_apply, symNormSq]
  push_cast
  exact Finset.sum_congr rfl fun r _ ↦ Complex.mul_conj' _

private lemma symNormSq_nonneg : 0 ≤ symNormSq u :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

private lemma norm_symCoord_sq_le (r : Fin j → Fin 2) : ‖symCoord r u‖ ^ 2 ≤ symNormSq u :=
  Finset.single_le_sum (f := fun s ↦ ‖symCoord s u‖ ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ r)

private lemma symNormSq_smul (s : ℂ) : symNormSq (s • u) = ‖s‖ ^ 2 * symNormSq u := by
  simp [symNormSq, mul_pow, Finset.mul_sum]

private lemma symNormSq_symPowerRep_le {A : GL (Fin 2) ℂ}
    (hA : ∀ a b, ‖(A : Matrix (Fin 2) (Fin 2) ℂ) a b‖ ≤ 2) :
    symNormSq (TauCeti.symPowerRep ℂ 2 j A u) ≤ 16 ^ j * symNormSq u := by
  have hS : (∑ s : Fin j → Fin 2, ‖symCoord s u‖) ^ 2 ≤ 2 ^ j * symNormSq u := by
    simpa [symNormSq] using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin j → Fin 2)))
      (f := fun s ↦ ‖symCoord s u‖)
  have h (r : Fin j → Fin 2) :
      ‖symCoord r (TauCeti.symPowerRep ℂ 2 j A u)‖ ^ 2 ≤ 8 ^ j * symNormSq u := by
    have h₁ : ‖symCoord r (TauCeti.symPowerRep ℂ 2 j A u)‖ ≤ 2 ^ j * ∑ s, ‖symCoord s u‖ := by
      rw [symCoord_symPowerRep, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ ↦ ?_)
      rw [norm_mul, norm_prod]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      simpa using Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin j)))
        (f := fun i ↦ ‖(A : Matrix (Fin 2) (Fin 2) ℂ) (r i) (s i)‖) (g := fun _ ↦ (2 : ℝ))
        (fun i _ ↦ norm_nonneg _) fun i _ ↦ hA _ _
    have h₃ :
        ‖symCoord r (TauCeti.symPowerRep ℂ 2 j A u)‖ ^ 2 ≤ (2 ^ j * ∑ s, ‖symCoord s u‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h₁ 2
    rw [mul_pow] at h₃
    refine h₃.trans ?_
    have e : (8 : ℝ) ^ j = (2 ^ j) ^ 2 * 2 ^ j := by
      rw [← pow_mul, ← pow_add, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
      congr 1
      ring1
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_left hS (by positivity)
  have h₄ : ∑ r : Fin j → Fin 2, ‖symCoord r (TauCeti.symPowerRep ℂ 2 j A u)‖ ^ 2 ≤
      ∑ _r : Fin j → Fin 2, 8 ^ j * symNormSq u :=
    Finset.sum_le_sum fun r _ ↦ h r
  have e : (16 : ℝ) ^ j = 2 ^ j * 8 ^ j := by
    rw [← mul_pow]
    norm_num
  simp only [Finset.sum_const, Finset.card_univ] at h₄
  rw [symNormSq, e, mul_assoc]
  simpa using h₄

private lemma symNormSq_rhoKJ_le_shift (hM : imGL Z₀ = star M * M)
    (hL : imGL (shiftedPoint hZ₀ x) = star L * L) :
    symNormSq (rhoKJ k j M u) ≤ max (4 ^ k) 1 * 16 ^ j * symNormSq (rhoKJ k j L u) := by
  have e : rhoKJ k j M u = rhoKJ k j (M * L⁻¹) (rhoKJ k j L u) := by
    rw [← End.mul_apply, ← map_mul, inv_mul_cancel_right]
  rw [e, rhoKJ_apply, symNormSq_smul]
  have hn : ‖(((M * L⁻¹).det ^ k : ℂˣ) : ℂ)‖ ^ 2 ≤ max (4 ^ k) 1 := by
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, GeneralLinearGroup.val_det_apply]
    rcases le_total 0 k with hk | hk
    · exact le_max_of_le_left (zpow_le_zpow_left₀ hk (by positivity)
        (norm_det_mul_inv_sq_le_four hZ₀ x hM hL))
    · exact le_max_of_le_right (zpow_le_one_of_nonpos₀
        (one_le_norm_det_mul_inv_sq hZ₀ x hM hL) hk)
  rw [mul_assoc]
  exact mul_le_mul hn (symNormSq_symPowerRep_le _ (norm_apply_le_two hZ₀ x hM hL))
    (symNormSq_nonneg _) (by positivity)

/-! ### Fourier expansions at the shifted point -/

private lemma exp_neg_two_pi_div_five_lt_one : rexp (-(2 * π / 5)) < 1 := by
  rw [Real.exp_lt_one_iff]
  linarith [Real.pi_pos]

variable (n : dualLattice (integral (Fin 2)))

private lemma fourierExp_shiftedPoint : fourierExp n (shiftedPoint hZ₀ x) = fourierExp n Z₀ *
    cexp (2 * π * I * (((x : ℂ) - I / 5) * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℂ) +
      ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℂ)))) := by
  rw [fourierExp, fourierExp, ← Complex.exp_add]
  congr 1
  have e : (shiftedPoint hZ₀ x).val = Z₀.val + (((x : ℂ) - I / 5)) • 1 := rfl
  have hT : ((n : Matrix (Fin 2) (Fin 2) ℚ).map ((↑) : ℚ → ℂ)).trace =
      ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℂ) + ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℂ) := by
    simp [trace_fin_two]
  rw [e, Matrix.mul_add, trace_add, Matrix.mul_smul, Matrix.mul_one, trace_smul, hT, smul_eq_mul]
  ring1

/-- The trace of an element of the dual lattice, as a natural number. -/
private noncomputable def traceNat : ℕ :=
  ⌊(n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 + (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1⌋₊

variable {n} in
private lemma cast_traceNat (hn : (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) :
    ((traceNat n : ℕ) : ℚ) = (n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 +
      (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 := by
  rcases exists_intCast_eq_apply n 0 with ⟨z₀, hz₀⟩
  rcases exists_intCast_eq_apply n 1 with ⟨z₁, hz₁⟩
  have h₀ : (0 : ℚ) ≤ (n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 := hn.diag_nonneg
  have h₁ : (0 : ℚ) ≤ (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 := hn.diag_nonneg
  rw [hz₀] at h₀
  rw [hz₁] at h₁
  have h₀' : 0 ≤ z₀ := by
    exact_mod_cast h₀
  have h₁' : 0 ≤ z₁ := by
    exact_mod_cast h₁
  rcases Int.eq_ofNat_of_zero_le h₀' with ⟨N₀, rfl⟩
  rcases Int.eq_ofNat_of_zero_le h₁' with ⟨N₁, rfl⟩
  have e : (n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 + (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 =
      ((N₀ + N₁ : ℕ) : ℚ) := by
    rw [hz₀, hz₁]
    push_cast
    rfl
  rw [traceNat, e, Nat.floor_natCast]

variable {n} in
private lemma natCast_traceNat (hn : (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) :
    ((traceNat n : ℕ) : ℂ) = ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℂ) +
      ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℂ) := by
  exact_mod_cast congrArg (fun q : ℚ ↦ (q : ℂ)) (cast_traceNat hn)

section Expansion

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {f : SiegelUpperHalfSpace (Fin 2) → V}
    {a : dualLattice (integral (Fin 2)) → V}

private lemma norm_dual_le_of_forall_shiftedPoint
    (ha : HasSiegelFourierExpansion (integral (Fin 2)) f a)
    (hpsd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef)
    (hR : ∀ n, a n ≠ 0 → R ≤ traceNat n) (ψ : Dual ℂ V)
    (hB : ∀ x ∈ Icc (0 : ℝ) 1, ‖ψ (f (shiftedPoint hZ₀ x))‖ ≤ B) :
    ‖ψ (f Z₀)‖ ≤ B * (rexp (-(2 * π / 5)) ^ R / (1 - rexp (-(2 * π / 5)))) := by
  have hc : Summable fun n ↦ ‖fourierExp n (shiftedPoint hZ₀ 0) * ψ (a n)‖ :=
    (ha _ ψ).summable.norm
  have hterm (n : dualLattice (integral (Fin 2))) (x : ℝ) :
      fourierExp n (shiftedPoint hZ₀ 0) * ψ (a n) * cexp (2 * π * I * ((traceNat n : ℂ) * x)) =
        fourierExp n (shiftedPoint hZ₀ x) * ψ (a n) := by
    by_cases hn : a n = 0
    · simp [hn]
    rw [fourierExp_shiftedPoint, fourierExp_shiftedPoint, ← natCast_traceNat (hpsd n hn),
      mul_right_comm]
    congr 1
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring1
  have hterm₀ (n : dualLattice (integral (Fin 2))) :
      fourierExp n (shiftedPoint hZ₀ 0) * ψ (a n) * ((rexp (-(2 * π / 5)) : ℝ) : ℂ) ^ traceNat n =
        fourierExp n Z₀ * ψ (a n) := by
    by_cases hn : a n = 0
    · simp [hn]
    have e :
        ((rexp (-(2 * π / 5)) : ℝ) : ℂ) ^ traceNat n = cexp (-(2 * π / 5) * (traceNat n : ℂ)) := by
      rw [ofReal_exp, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring1
    have e₁ : 2 * (π : ℂ) * I * ((((0 : ℝ) : ℂ) - I / 5) * (traceNat n : ℂ)) +
        -(2 * π / 5) * (traceNat n : ℂ) = 0 := by
      push_cast
      linear_combination (-(2 * π / 5) * (traceNat n : ℂ) : ℂ) * I_mul_I
    rw [fourierExp_shiftedPoint, ← natCast_traceNat (hpsd n hn), e, mul_right_comm,
      mul_assoc (fourierExp n Z₀), mul_assoc (fourierExp n Z₀), ← Complex.exp_add, e₁,
      Complex.exp_zero, one_mul]
  have h₁ : ‖∑' n, fourierExp n (shiftedPoint hZ₀ 0) * ψ (a n) *
      ((rexp (-(2 * π / 5)) : ℝ) : ℂ) ^ traceNat n‖ ≤
        B * (rexp (-(2 * π / 5)) ^ R / (1 - rexp (-(2 * π / 5)))) :=
    norm_tsum_mul_pow_le hc (fun n hn ↦ hR n (fun h ↦ hn (by simp [h]))) (Real.exp_nonneg _)
      exp_neg_two_pi_div_five_lt_one fun x hx ↦ by
        simp only [hterm]
        rw [(ha _ ψ).tsum_eq]
        exact hB x hx
  simp only [hterm₀] at h₁
  rwa [(ha _ ψ).tsum_eq] at h₁

end Expansion

/-! ### The vanishing of cusp forms with only large frequencies -/

section Vanishing

variable {F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)}
    {a : dualLattice (integral (Fin 2)) → Sym[ℂ]^j (Fin 2 → ℂ)}

variable (k F) in
/-- The invariant function `c(ρ(Y) F(Z), F(Z))`. -/
private noncomputable def normFn (Z : SiegelUpperHalfSpace (Fin 2)) : ℝ :=
  (peterssonIntegrand (rhoKJ k j) (symHermitianForm j) F F Z).re

private lemma normFn_eq {Z : SiegelUpperHalfSpace (Fin 2)} (hM : imGL Z = star M * M) :
    normFn k F Z = symNormSq (rhoKJ k j M (F Z)) := by
  have h : peterssonIntegrand (rhoKJ k j) (symHermitianForm j) F F Z =
      (symNormSq (rhoKJ k j M (F Z)) : ℂ) := by
    have h₁ : symHermitianForm j (rhoKJ k j (star M) (rhoKJ k j M (F Z))) (F Z) =
        symHermitianForm j (rhoKJ k j M (F Z)) (rhoKJ k j (star (star M)) (F Z)) :=
      isAdmissibleForm_symHermitianForm k (star M) (rhoKJ k j M (F Z)) (F Z)
    rw [star_star] at h₁
    rw [peterssonIntegrand_apply, hM, map_mul, End.mul_apply, h₁, symHermitianForm_self]
  rw [normFn, h, ofReal_re]

private lemma normFn_nonneg (Z : SiegelUpperHalfSpace (Fin 2)) : 0 ≤ normFn k F Z := by
  rcases exists_star_mul_eq_imGL Z with ⟨M, hM⟩
  rw [normFn_eq hM]
  exact symNormSq_nonneg _

private lemma normFn_smul (hF : F ∈ modularForms (rhoKJ k j) (integral (Fin 2)) 1)
    (γ : transformationGroup (integral (Fin 2))) (Z : SiegelUpperHalfSpace (Fin 2)) :
    normFn k F (γ • Z) = normFn k F Z := by
  rw [normFn, normFn, peterssonIntegrand_map_smul (isAdmissibleForm_symHermitianForm k) hF hF]

private lemma exists_normFn_le (hF : F ∈ cuspForms (rhoKJ k j) (integral (Fin 2)) 1) :
    ∃ Λ, ∀ Z ∈ siegelSet, normFn k F Z ≤ Λ := by
  rcases exists_norm_peterssonIntegrand_le (f := F) (g := F)
    (A := fun τ ↦ rexp (-π * ((τ.val 0 0).im + (τ.val 1 1).im))) (isModerateForm_rhoKJ k _)
      (fun φ ψ ↦ by
        rcases exists_norm_dual_le_of_mem_modularForms hF.1 φ with ⟨C₁, hC₁, h₁⟩
        rcases exists_norm_dual_le_of_mem_cuspForms hF ψ with ⟨C₂, hC₂, h₂⟩
        refine ⟨C₁ * C₂, fun τ hτ ↦ ?_⟩
        rw [mul_assoc]
        exact mul_le_mul (h₁ τ hτ) (h₂ τ hτ) (norm_nonneg _) hC₁) with ⟨C, N, hC⟩
  refine ⟨|C| * (N.factorial / (π / 2) ^ N * rexp (π / 2)), fun Z hZ ↦ ?_⟩
  refine (Complex.re_le_norm _).trans ((hC Z hZ).trans ?_)
  have hT : 0 ≤ (Z.val 0 0).im + (Z.val 1 1).im :=
    add_nonneg (by linarith [four_fifths_le_im_zero_zero hZ])
      (by linarith [four_fifths_le_im_one_one hZ])
  rw [add_assoc]
  refine (mul_rexp_mul_pow_le C N Real.pi_pos hT).trans <|
    mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_)
  nlinarith [Real.pi_pos]

private lemma bddAbove_range_normFn (hF : F ∈ cuspForms (rhoKJ k j) (integral (Fin 2)) 1) :
    BddAbove (Set.range (normFn k F)) := by
  rcases exists_normFn_le (k := k) hF with ⟨Λ, hΛ⟩
  refine ⟨Λ, ?_⟩
  rintro _ ⟨Z, rfl⟩
  rcases exists_smul_mem_siegelSet_transformationGroup Z with ⟨γ, hγ⟩
  rw [← normFn_smul hF.1 γ]
  exact hΛ _ hγ

private lemma imGL_shiftedPoint : imGL (shiftedPoint hZ₀ x) = imGL (shiftedPoint hZ₀ 0) :=
  Units.ext <| by
    rw [coe_imGL, coe_imGL]
    ext i i'
    simp [im_shiftedPoint]

private lemma normFn_le_of_forall_le (ha : HasSiegelFourierExpansion (integral (Fin 2)) F a)
    (hpsd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef)
    (hR : ∀ n, a n ≠ 0 → R ≤ traceNat n) (hZ : Z₀ ∈ siegelSet) {Λ : ℝ}
    (hΛ : ∀ Z, normFn k F Z ≤ Λ) : normFn k F Z₀ ≤ 2 ^ j * (max (4 ^ k) 1 * 16 ^ j * Λ) *
      (rexp (-(2 * π / 5)) ^ R / (1 - rexp (-(2 * π / 5)))) ^ 2 := by
  rcases exists_star_mul_eq_imGL Z₀ with ⟨M, hM⟩
  rcases exists_star_mul_eq_imGL (shiftedPoint hZ 0) with ⟨L, hL⟩
  have hL' (x : ℝ) : imGL (shiftedPoint hZ x) = star L * L := by
    rw [imGL_shiftedPoint, hL]
  generalize hK : max ((4 : ℝ) ^ k) 1 * 16 ^ j * Λ = K
  have hK₀ : 0 ≤ K := by
    rw [← hK]
    have h₁ : 0 ≤ Λ := (normFn_nonneg Z₀).trans (hΛ Z₀)
    positivity
  generalize hq : rexp (-(2 * π / 5)) ^ R / (1 - rexp (-(2 * π / 5))) = q
  have hq₀ : 0 ≤ q := by
    rw [← hq]
    exact div_nonneg (by positivity) (by linarith [exp_neg_two_pi_div_five_lt_one])
  have hcoord (r : Fin j → Fin 2) : ‖symCoord r (rhoKJ k j M (F Z₀))‖ ^ 2 ≤ K * q ^ 2 := by
    have h₁ : ‖symCoord r (rhoKJ k j M (F Z₀))‖ ≤
        √K * (rexp (-(2 * π / 5)) ^ R / (1 - rexp (-(2 * π / 5)))) :=
      norm_dual_le_of_forall_shiftedPoint hZ ha hpsd hR (symCoord r ∘ₗ rhoKJ k j M) fun x _ ↦ by
        refine Real.le_sqrt_of_sq_le ?_
        refine (norm_symCoord_sq_le _ r).trans ?_
        refine (symNormSq_rhoKJ_le_shift hZ x _ hM (hL' x)).trans ?_
        rw [← normFn_eq (hL' x), ← hK]
        exact mul_le_mul_of_nonneg_left (hΛ _) (by positivity)
    rw [hq] at h₁
    have h₂ : ‖symCoord r (rhoKJ k j M (F Z₀))‖ ^ 2 ≤ (√K * q) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h₁ 2
    rwa [mul_pow, Real.sq_sqrt hK₀] at h₂
  rw [normFn_eq hM, symNormSq]
  refine (Finset.sum_le_sum fun r _ ↦ hcoord r).trans_eq ?_
  simp
  ring1

variable (k j) in
private lemma exists_frequency_bound : ∃ R : ℕ, 2 ^ j * (max ((4 : ℝ) ^ k) 1 * 16 ^ j) *
    (rexp (-(2 * π / 5)) ^ R / (1 - rexp (-(2 * π / 5)))) ^ 2 < 1 := by
  have h₁ : Filter.Tendsto (fun R : ℕ ↦ 2 ^ j * (max ((4 : ℝ) ^ k) 1 * 16 ^ j) *
      (rexp (-(2 * π / 5)) ^ R / (1 - rexp (-(2 * π / 5)))) ^ 2) Filter.atTop (nhds 0) := by
    simpa using (((tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_nonneg _)
      exp_neg_two_pi_div_five_lt_one).div_const (1 - rexp (-(2 * π / 5)))).pow 2).const_mul
        (2 ^ j * (max ((4 : ℝ) ^ k) 1 * 16 ^ j))
  exact (h₁.eventually (gt_mem_nhds zero_lt_one)).exists

private lemma eq_zero_of_forall_traceNat_le (hθ : 2 ^ j * (max ((4 : ℝ) ^ k) 1 * 16 ^ j) *
    (rexp (-(2 * π / 5)) ^ R / (1 - rexp (-(2 * π / 5)))) ^ 2 < 1)
    (hF : F ∈ cuspForms (rhoKJ k j) (integral (Fin 2)) 1)
    (ha : HasSiegelFourierExpansion (integral (Fin 2)) F a) (hR : ∀ n, a n ≠ 0 → R ≤ traceNat n) :
    F = 0 := by
  have hb : BddAbove (Set.range (normFn k F)) := bddAbove_range_normFn hF
  have hpsd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef :=
    koecherPrinciple (rhoKJ k j) (isArithmetic_integral (Fin 2)) (by simp) F hF.1 a ha
  generalize hθ' : 2 ^ j * (max ((4 : ℝ) ^ k) 1 * 16 ^ j) *
    (rexp (-(2 * π / 5)) ^ R / (1 - rexp (-(2 * π / 5)))) ^ 2 = θ at hθ
  have : Nonempty (SiegelUpperHalfSpace (Fin 2)) := ⟨scalarPoint tOne⟩
  have hle : ⨆ Z, normFn k F Z ≤ θ * ⨆ Z, normFn k F Z := by
    refine ciSup_le fun Z ↦ ?_
    rcases exists_smul_mem_siegelSet_transformationGroup Z with ⟨γ, hγ⟩
    rw [← normFn_smul hF.1 γ]
    refine (normFn_le_of_forall_le ha hpsd hR hγ (Λ := ⨆ Z, normFn k F Z)
      fun Z ↦ le_ciSup hb Z).trans_eq ?_
    rw [← hθ']
    ring1
  have hΛ : ⨆ Z, normFn k F Z ≤ 0 := by
    nlinarith [hle, le_ciSup hb (scalarPoint tOne),
      normFn_nonneg (k := k) (F := F) (scalarPoint tOne)]
  funext Z
  by_contra hne
  rcases exists_star_mul_eq_imGL Z with ⟨M, hM⟩
  have hv : rhoKJ k j M (F Z) ≠ 0 := fun h ↦ hne <| by
    have h₁ : rhoKJ k j M⁻¹ (rhoKJ k j M (F Z)) = F Z := (rhoKJ k j).inv_self_apply M (F Z)
    rw [h, map_zero] at h₁
    exact h₁.symm
  have h₁ : 0 < symHermitianForm j (rhoKJ k j M (F Z)) (rhoKJ k j M (F Z)) :=
    symHermitianForm_pos hv
  rw [symHermitianForm_self, zero_lt_real, ← normFn_eq hM] at h₁
  linarith [le_ciSup hb Z]

end Vanishing

/-! ### Finite dimension -/

/-- The coordinates `(n₀₀, 2 n₀₁, n₁₁)` of an element of the dual lattice of `Sp(4, ℤ)`. -/
private noncomputable def dualCoords : ℤ × ℤ × ℤ :=
  (⌊(n : Matrix (Fin 2) (Fin 2) ℚ) 0 0⌋, ⌊2 * (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1⌋,
    ⌊(n : Matrix (Fin 2) (Fin 2) ℚ) 1 1⌋)

private lemma dual_apply_one_zero :
    (n : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 :=
  congrFun (congrFun n.2.1 0) 1

private lemma exists_intCast_eq_two_mul : ∃ w : ℤ, 2 * (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = w := by
  rcases n.2.2 _ (vecMulVec_mem_translationLattice ![1, 1]) with ⟨z, hz⟩
  rcases exists_intCast_eq_apply n 0 with ⟨z₀, hz₀⟩
  rcases exists_intCast_eq_apply n 1 with ⟨z₁, hz₁⟩
  refine ⟨z - z₀ - z₁, ?_⟩
  push_cast
  rw [← hz, ← hz₀, ← hz₁]
  simp [trace, Matrix.mul_apply, dual_apply_one_zero n]
  ring1

private lemma dualCoords_injective : Function.Injective dualCoords := by
  intro n n' h
  rcases exists_intCast_eq_apply n 0 with ⟨z₀, hz₀⟩
  rcases exists_intCast_eq_apply n 1 with ⟨z₁, hz₁⟩
  rcases exists_intCast_eq_two_mul n with ⟨w, hw⟩
  rcases exists_intCast_eq_apply n' 0 with ⟨z₀', hz₀'⟩
  rcases exists_intCast_eq_apply n' 1 with ⟨z₁', hz₁'⟩
  rcases exists_intCast_eq_two_mul n' with ⟨w', hw'⟩
  simp only [dualCoords, hz₀, hz₁, hw, hz₀', hz₁', hw'] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  have h₁ : (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = (n' : Matrix (Fin 2) (Fin 2) ℚ) 0 1 := by
    linarith
  refine Subtype.ext ?_
  ext i k
  fin_cases i <;> fin_cases k
  · exact hz₀.trans hz₀'.symm
  · exact h₁
  · exact (dual_apply_one_zero n).trans (h₁.trans (dual_apply_one_zero n').symm)
  · exact hz₁.trans hz₁'.symm

variable (R) in
private lemma finite_setOf_traceNat_lt : {n : dualLattice (integral (Fin 2)) |
    (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef ∧ traceNat n < R}.Finite := by
  refine ((Set.finite_Icc ((0 : ℤ), -(2 * (R : ℤ)), (0 : ℤ))
    ((R : ℤ), 2 * (R : ℤ), (R : ℤ))).preimage dualCoords_injective.injOn).subset ?_
  rintro n ⟨hn, hR⟩
  have hR' : (n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 + (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 < R := by
    rw [← cast_traceNat hn]
    exact_mod_cast hR
  have h₀ : (0 : ℚ) ≤ (n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 := hn.diag_nonneg
  have h₁ : (0 : ℚ) ≤ (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 := hn.diag_nonneg
  have h₂ : (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 ^ 2 ≤
      (n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 * (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 :=
    sq_apply_le_of_posSemidef hn
  have h₃ : |(n : Matrix (Fin 2) (Fin 2) ℚ) 0 1| ≤ R := by
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    nlinarith
  have h₄ :
      -(R : ℚ) ≤ (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 ∧ (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 ≤ R :=
    abs_le.mp h₃
  have hup {q : ℚ} {N : ℤ} (h : q ≤ N) : ⌊q⌋ ≤ N := by
    simpa using Int.floor_mono h
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact Int.floor_nonneg.mpr h₀
  · refine Int.le_floor.mpr ?_
    push_cast
    linarith
  · exact Int.floor_nonneg.mpr h₁
  · refine hup ?_
    push_cast
    linarith
  · refine hup ?_
    push_cast
    linarith
  · refine hup ?_
    push_cast
    linarith

/-- A choice of Fourier coefficients of a cusp form. -/
private noncomputable def cuspCoeff (F : cuspFormsKJ k j (integral (Fin 2))) :
    dualLattice (integral (Fin 2)) → Sym[ℂ]^j (Fin 2 → ℂ) :=
  (exists_hasSiegelFourierExpansion (rhoKJ k j) (isArithmetic_integral (Fin 2)) F.2.1).choose

private lemma hasSiegelFourierExpansion_cuspCoeff (F : cuspFormsKJ k j (integral (Fin 2))) :
    HasSiegelFourierExpansion (integral (Fin 2))
      (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) (cuspCoeff F) :=
  (exists_hasSiegelFourierExpansion (rhoKJ k j) (isArithmetic_integral (Fin 2)) F.2.1).choose_spec

variable (R k j) in
/-- The Fourier coefficients of a cusp form at the finitely many `n` positive semidefinite with
`tr n < R`, as a linear map. -/
private noncomputable def cuspCoeffMap : cuspFormsKJ k j (integral (Fin 2)) →ₗ[ℂ]
    ({n : dualLattice (integral (Fin 2)) | (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef ∧ traceNat n <
      R} → Sym[ℂ]^j (Fin 2 → ℂ)) where
  toFun F n := cuspCoeff F n
  map_add' F G := by
    funext n
    exact (congrFun (((hasSiegelFourierExpansion_cuspCoeff F).add _
      (hasSiegelFourierExpansion_cuspCoeff G)).unique_of_isArithmetic
        (isArithmetic_integral (Fin 2)) (hasSiegelFourierExpansion_cuspCoeff (F + G))) n).symm
  map_smul' c F := by
    funext n
    exact (congrFun (((hasSiegelFourierExpansion_cuspCoeff F).const_smul _ c).unique_of_isArithmetic
      (isArithmetic_integral (Fin 2)) (hasSiegelFourierExpansion_cuspCoeff (c • F))) n).symm

variable (k j) in
/-- **The space `S_{j,k}(Γ₂)` is finite-dimensional.** A cusp form `F` is determined by its Fourier
coefficients `a(n)` with `tr n < R`, for `R` large enough: the invariant function
`c(ρ(Y) F(Z), F(Z))` is bounded, and if `a(n) = 0` for `tr n < R`, then at a point `Z₀` of the
Siegel set, by the Fourier series in `x` of `F(Z₀ + (x - i / 5) 1)`, its value is at most `θ_R`
times its supremum, with `θ_R → 0` as `R → ∞`. -/
lemma finiteDimensional_cuspFormsKJ : FiniteDimensional ℂ (cuspFormsKJ k j (integral (Fin 2))) := by
  rcases exists_frequency_bound k j with ⟨R, hR⟩
  have : Finite {n : dualLattice (integral (Fin 2)) | (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef ∧
      traceNat n < R} :=
    (finite_setOf_traceNat_lt R).to_subtype
  refine FiniteDimensional.of_injective (cuspCoeffMap R k j) ((injective_iff_map_eq_zero _).mpr
    fun F hF ↦ Subtype.ext ?_)
  refine eq_zero_of_forall_traceNat_le hR F.2 (hasSiegelFourierExpansion_cuspCoeff F) fun n hn ↦ ?_
  by_contra hlt
  exact hn (congrFun hF ⟨n, koecherPrinciple (rhoKJ k j) (isArithmetic_integral (Fin 2)) (by simp)
    _ F.2.1 _ (hasSiegelFourierExpansion_cuspCoeff F) n hn, not_le.mp hlt⟩)

end SiegelUpperHalfSpace
