import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Jacobi.FourierCoefficients
import Mathlib.NumberTheory.Modular

/-!
# Growth of the Fourier coefficients of Jacobi forms of index 1

The Fourier coefficients `c(n, r)` of a Jacobi form `φ ∈ J_{k,1}` grow polynomially:
`|c(n, r)| ≤ C (1 + |n|)^k`, and `J_{k,1} = 0` for `k ≤ 0`. The proof is Hecke's argument, carried
out with the transformation laws of `φ`:

* on the region `Im τ ≥ 1/2`, `|Im z| ≤ Im τ / 2`, the Fourier series of `φ` is dominated by
  `∑ |c(n, r)| (e^{-π(n + r/2)} + e^{-π(n - r/2)})`, since `n - |r|/2 ≥ 0` on the support
  `4n ≥ r²`, so `|φ| ≤ C₀` there;
* for `τ ∈ ℍ` and real `u` there is `γ = (a, b; c, d) ∈ SL(2, ℤ)` with `Im γτ ≥ 1/2` and
  `|cτ + d| ≤ 1`; with `λ = -round(cu)` the point `(γτ, u/(cτ + d) - λγτ)` lies in that region,
  and the transformation laws give `|φ(τ, u)| |cτ + d|^k ≤ C₀`, the factor
  `e^{-2π Im(γτ) (cu + λ)²} ≤ 1` being what is left of the exponentials. As `|cτ + d| ≥ Im τ`
  when `Im τ ≤ 1`, this gives `|φ(τ, u)| ≤ C₀ (Im τ)^{-k}` for `k ≥ 0`, and `|φ(τ, u)| ≤ C₀` for
  `k ≤ 0`;
* the coefficient `c(n, r) e^{-2πny}` is the Fourier coefficient of `(x, u) ↦ φ(x + iy, u)` on
  the torus `(ℝ / ℤ)²`, so it is bounded by the supremum `C₀ y^{-k}`; take `y = 1/(1 + |n|)`.
  For `k ≤ 0`, Bessel's inequality on the torus, applied to the `N` coefficients
  `c(n + λr + λ², r + 2λ) = c(n, r)`, `0 ≤ λ < N`, gives `N |c(n, r)|² ≤ C₀² e^{4π}` for every
  `N`, so `c(n, r) = 0`.

The polynomial bound is the hypothesis of
`SiegelUpperHalfSpace.maassLift_mem_scalarModularForms_of_norm_jacobiCoeff_le`.

## Main definitions

* `ModularForm.jacobiSupBound`: the constant `∑ |c(n, r)| (e^{-π(n + r/2)} + e^{-π(n - r/2)})`.

## Main results

* `UnitAddTorus.norm_le_of_norm_tsum_mFourier_le`: the coefficients of an absolutely convergent
  Fourier series on the torus are bounded by the supremum of its sum.
* `UnitAddTorus.sum_norm_sq_le_of_norm_tsum_mFourier_le`: Bessel's inequality for such series.
* `ModularForm.norm_jacobiCoeff_le_of_mem_jacobiFormSpace_one`: the Fourier coefficients of a
  Jacobi form of weight `k` and index `1` satisfy `|c(n, r)| ≤ C (1 + |n|)^k`.
* `ModularForm.eq_zero_of_mem_jacobiFormSpace_one_of_nonpos`: `J_{k,1} = 0` for `k ≤ 0`.
-/

open Complex MeasureTheory Real UnitAddTorus

open UpperHalfPlane hiding I

open scoped MatrixGroups

attribute [local instance] unitAddCircleHaarMeasureSpace

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι] {c : (ι → ℤ) → ℂ} {B : ℝ} (m : ι → ℤ)

private lemma summable_smul_mFourier (hc : Summable c) : Summable fun k ↦ c k • mFourier k :=
  .of_norm <| by simpa [norm_smul, mFourier_norm] using hc.norm

private lemma eq_inner_toLp (hc : Summable c) :
    c m = inner ℂ (mFourierLp 2 m) (ContinuousMap.toLp 2 volume ℂ (∑' k, c k • mFourier k)) := by
  have hm : HasSum (fun k ↦ if k = m then c k else 0) (inner ℂ (mFourierLp 2 m)
      (ContinuousMap.toLp 2 volume ℂ (∑' k, c k • mFourier k))) := by
    simpa only [ContinuousLinearMap.comp_apply, map_smul, innerSL_apply_apply,
      orthonormal_iff_ite.mp orthonormal_mFourier m, smul_eq_mul, mul_ite, mul_one, mul_zero,
      eq_comm (a := m)] using ((innerSL ℂ (mFourierLp 2 m)).comp
        (ContinuousMap.toLp 2 volume ℂ)).hasSum (summable_smul_mFourier hc).hasSum
  exact (hasSum_ite_eq m (c m)).unique (hm.congr_fun fun b ↦ by
    split_ifs with hb
    · rw [hb]
    · rfl)

private lemma norm_toLp_le (hc : Summable c) (h : ∀ x, ‖∑' k, c k * mFourier k x‖ ≤ B) :
    ‖ContinuousMap.toLp 2 volume ℂ (∑' k, c k • mFourier k)‖ ≤ B := by
  have hG : ‖∑' k, c k • mFourier k‖ ≤ B :=
    (ContinuousMap.norm_le _ ((norm_nonneg _).trans (h 0))).mpr fun x ↦ by
      rw [← ContinuousMap.tsum_apply (summable_smul_mFourier hc)]
      simpa using h x
  refine (((ContinuousMap.toLp 2 volume ℂ).le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) ?_)).trans hG
  refine (ContinuousMap.toLp_norm_le volume).trans ?_
  simp [measureUnivNNReal]

/-- **The coefficients of a Fourier series on the torus are bounded by its supremum**: if
`∑ c(k) e^{2πi k·x}` converges absolutely and its sum is bounded by `B` on `(ℝ / ℤ)^ι`, then
`|c(k)| ≤ B` for every `k`. -/
lemma norm_le_of_norm_tsum_mFourier_le (hc : Summable c)
    (h : ∀ x, ‖∑' k, c k * mFourier k x‖ ≤ B) : ‖c m‖ ≤ B := by
  rw [eq_inner_toLp m hc]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [orthonormal_mFourier.1 m, one_mul]
  exact norm_toLp_le hc h

/-- **Bessel's inequality for Fourier series on the torus**: if `∑ c(k) e^{2πi k·x}` converges
absolutely and its sum is bounded by `B` on `(ℝ / ℤ)^ι`, then `∑_{k ∈ s} |c(k)|² ≤ B²` for every
finite set `s` of frequencies. -/
lemma sum_norm_sq_le_of_norm_tsum_mFourier_le (hc : Summable c)
    (h : ∀ x, ‖∑' k, c k * mFourier k x‖ ≤ B) (s : Finset (ι → ℤ)) :
    ∑ m ∈ s, ‖c m‖ ^ 2 ≤ B ^ 2 := by
  have h1 : ∑ m ∈ s, ‖c m‖ ^ 2 = ∑ m ∈ s, ‖inner ℂ (mFourierLp 2 m)
      (ContinuousMap.toLp 2 volume ℂ (∑' k, c k • mFourier k))‖ ^ 2 :=
    Finset.sum_congr rfl fun m _ ↦ by
      rw [← eq_inner_toLp m hc]
  rw [h1]
  exact (orthonormal_mFourier.sum_inner_products_le _).trans
    (pow_le_pow_left₀ (norm_nonneg _) (norm_toLp_le hc h) 2)

end UnitAddTorus

namespace ModularForm

variable {k : ℤ} {φ : ℍ × ℂ → ℂ}

/-- The constant `∑_{n, r} |c(n, r)| (e^{-π(n + r/2)} + e^{-π(n - r/2)})` attached to
`f : ℍ × ℂ → ℂ` with Fourier coefficients `c(n, r)`. For a Jacobi form of index `1` the series
converges, and its sum bounds `|f(τ, z)|` on the region `Im τ ≥ 1/2`, `|Im z| ≤ Im τ / 2`, which
meets every orbit of the Jacobi group `SL(2, ℤ) ⋉ ℤ²`. -/
noncomputable def jacobiSupBound (f : ℍ × ℂ → ℂ) : ℝ :=
  ∑' p : ℤ × ℤ, ‖jacobiCoeff f p‖ *
    (rexp (-(π * ((p.1 : ℝ) + p.2 / 2))) + rexp (-(π * ((p.1 : ℝ) - p.2 / 2))))

private lemma norm_jacobiFourierExp (p : ℤ × ℤ) (x : ℍ × ℂ) :
    ‖jacobiFourierExp p x‖ = rexp (-(2 * π * (p.1 * x.1.im + p.2 * x.2.im))) := by
  rw [jacobiFourierExp, Complex.norm_exp]
  congr 1
  simp

/-- The point `(i/2, si/4)` of `ℍ × ℂ`. -/
private noncomputable def basePoint (s : ℝ) : ℍ × ℂ :=
  (mk (I / 2) (by simp), s * I / 4)

private lemma summable_mul_rexp (hφ : φ ∈ jacobiFormSpace k 1) (s : ℝ) :
    Summable fun p : ℤ × ℤ ↦ ‖jacobiCoeff φ p‖ * rexp (-(π * ((p.1 : ℝ) + s * p.2 / 2))) :=
  (summable_norm_iff.mpr ((hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ)
    (basePoint s)).summable).congr fun p ↦ by
      rw [norm_mul, norm_jacobiFourierExp]
      congr 2
      simp [basePoint]
      ring1

lemma summable_jacobiSupBound (hφ : φ ∈ jacobiFormSpace k 1) : Summable fun p : ℤ × ℤ ↦
    ‖jacobiCoeff φ p‖ *
        (rexp (-(π * ((p.1 : ℝ) + p.2 / 2))) + rexp (-(π * ((p.1 : ℝ) - p.2 / 2)))) :=
  ((summable_mul_rexp hφ 1).add (summable_mul_rexp hφ (-1))).congr fun p ↦ by
    rw [one_mul, neg_one_mul, neg_div, ← sub_eq_add_neg, ← mul_add]

private lemma rexp_le_add_rexp {n r y v : ℝ} (hn : |r| ≤ 2 * n) (hy : 1 / 2 ≤ y)
    (hv : |v| ≤ y / 2) :
    rexp (-(2 * π * (n * y + r * v))) ≤ rexp (-(π * (n + r / 2))) + rexp (-(π * (n - r / 2))) := by
  rcases le_total 0 r with hr | hr
  · refine (Real.exp_le_exp.mpr ?_).trans (le_add_of_nonneg_left (Real.exp_pos _).le)
    rw [abs_of_nonneg hr] at hn
    nlinarith [Real.pi_pos, abs_le.mp hv, mul_nonneg (by linarith : 0 ≤ y - 1 / 2)
      (by linarith : 0 ≤ n - r / 2), mul_nonneg hr (by linarith [(abs_le.mp hv).1] : 0 ≤ v + y / 2)]
  · refine (Real.exp_le_exp.mpr ?_).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
    rw [abs_of_nonpos hr] at hn
    nlinarith [Real.pi_pos, abs_le.mp hv, mul_nonneg (by linarith : 0 ≤ y - 1 / 2)
      (by linarith : 0 ≤ n + r / 2), mul_nonneg (neg_nonneg.mpr hr)
      (by linarith [(abs_le.mp hv).2] : 0 ≤ y / 2 - v)]

private lemma abs_le_two_mul {n r : ℤ} (hn : 0 ≤ n) (hr : r ^ 2 ≤ 4 * n) : |r| ≤ 2 * n := by
  by_contra h
  have h' : 2 * n + 1 ≤ |r| := by omega
  nlinarith [sq_abs r, abs_nonneg r]

variable (τ : ℍ) (u : ℝ) (γ : SL(2, ℤ))

variable {τ} in
lemma norm_le_jacobiSupBound (hφ : φ ∈ jacobiFormSpace k 1) {z : ℂ} (hτ : 1 / 2 ≤ τ.im)
    (hz : |z.im| ≤ τ.im / 2) : ‖φ (τ, z)‖ ≤ jacobiSupBound φ := by
  have hc : HasJacobiFourierExpansion φ (jacobiCoeff φ) :=
    hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ
  have hs : Summable fun p ↦ ‖jacobiCoeff φ p * jacobiFourierExp p (τ, z)‖ :=
    summable_norm_iff.mpr (hc (τ, z)).summable
  rw [← (hc (τ, z)).tsum_eq]
  refine (norm_tsum_le_tsum_norm hs).trans <| hs.tsum_le_tsum (fun p ↦ ?_) <|
    summable_jacobiSupBound hφ
  rw [norm_mul, norm_jacobiFourierExp]
  by_cases hp : jacobiCoeff φ p = 0
  · rw [hp, norm_zero, zero_mul, zero_mul]
  have hS : 0 ≤ p.1 ∧ p.2 ^ 2 ≤ 4 * p.1 * ((1 : ℕ) : ℤ) := by
    by_contra h
    exact hp <| jacobiCoeff_eq_zero_of_mem_jacobiFourierSupported hφ.2.2 h
  have hr : |(p.2 : ℝ)| ≤ 2 * p.1 := by
    exact_mod_cast abs_le_two_mul hS.1 (by simpa using hS.2)
  exact mul_le_mul_of_nonneg_left (rexp_le_add_rexp hr hτ hz) (norm_nonneg _)

private lemma im_div_denom : ((u : ℂ) / denom γ τ).im = -((γ 1 0 : ℝ) * u * (γ • τ).im) := by
  rw [ModularGroup.im_smul_eq_div_normSq, Complex.div_im, ModularGroup.denom_apply]
  simp
  ring1

variable {τ u} in
private lemma norm_mul_norm_zpow_le_of_eq (hφ : φ ∈ jacobiFormSpace k 1) {τ' : ℍ} {t : ℝ} {w : ℂ}
    (hτ' : 1 / 2 ≤ τ'.im) (hw : ((u : ℂ) / w).im = -(t * τ'.im))
    (h : φ (τ', u / w) = w ^ k * cexp (2 * π * I * t * (u / w)) * φ (τ, u)) :
    ‖φ (τ, u)‖ * ‖w‖ ^ k ≤ jacobiSupBound φ := by
  have hz : |((u : ℂ) / w + round t * (τ' : ℂ)).im| ≤ τ'.im / 2 := by
    have h1 : |t - round t| ≤ 1 / 2 := abs_sub_round t
    have he : ((u : ℂ) / w + round t * (τ' : ℂ)).im = -((t - round t) * τ'.im) := by
      rw [add_im, hw]
      simp
      ring1
    rw [he, abs_neg, abs_mul, abs_of_pos τ'.im_pos]
    nlinarith [τ'.im_pos]
  have h2 : φ (τ', (u : ℂ) / w + round t * (τ' : ℂ) + ((-round t : ℤ) : ℂ) * τ') =
      cexp (-2 * π * I * ((1 : ℕ) : ℂ) * (((-round t : ℤ) : ℂ) ^ 2 * τ' +
        2 * ((-round t : ℤ) : ℂ) * ((u : ℂ) / w + round t * (τ' : ℂ)))) *
          φ (τ', (u : ℂ) / w + round t * (τ' : ℂ)) :=
    apply_add_mul_of_mem_jacobiFormSpace τ' _ (-round t) hφ
  have h3 : (u : ℂ) / w + round t * (τ' : ℂ) + ((-round t : ℤ) : ℂ) * τ' = u / w := by
    push_cast
    ring1
  rw [h3, h] at h2
  have hb : ‖φ (τ', (u : ℂ) / w + round t * (τ' : ℂ))‖ ≤ jacobiSupBound φ :=
    norm_le_jacobiSupBound hφ hτ' hz
  generalize (u : ℂ) / w = X at h2 hw hb
  have hE : ‖cexp (-2 * π * I * ((1 : ℕ) : ℂ) *
      (((-round t : ℤ) : ℂ) ^ 2 * τ' + 2 * ((-round t : ℤ) : ℂ) * (X + round t * τ')))‖ ≤
        ‖cexp (2 * π * I * t * X)‖ := by
    rw [Complex.norm_exp, Complex.norm_exp, Real.exp_le_exp]
    simp [hw, sq]
    nlinarith [mul_nonneg Real.pi_pos.le (mul_nonneg τ'.im_pos.le (sq_nonneg (t - round t)))]
  have hE₂ : 0 < ‖cexp (2 * π * I * t * X)‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hn : ‖w‖ ^ k * ‖cexp (2 * π * I * t * X)‖ * ‖φ (τ, u)‖ = ‖cexp (-2 * π * I * ((1 : ℕ) : ℂ) *
      (((-round t : ℤ) : ℂ) ^ 2 * τ' + 2 * ((-round t : ℤ) : ℂ) * (X + round t * τ')))‖ *
        ‖φ (τ', X + round t * τ')‖ := by
    rw [← norm_zpow, ← norm_mul, ← norm_mul, ← norm_mul, h2]
  nlinarith [mul_le_mul hE hb (norm_nonneg _) hE₂.le, norm_nonneg (φ (τ, u))]

variable {γ} in
private lemma norm_mul_norm_denom_zpow_le (hφ : φ ∈ jacobiFormSpace k 1) (hγ : 1 / 2 ≤ (γ • τ).im) :
    ‖φ (τ, u)‖ * ‖denom γ τ‖ ^ k ≤ jacobiSupBound φ :=
  norm_mul_norm_zpow_le_of_eq hφ hγ (im_div_denom τ u γ) <| by
    rw [hφ.2.1 γ (τ, u), jacobiFactor]
    congr 3
    push_cast
    ring1

variable {τ} in
private lemma im_le_norm_denom (hτ : τ.im ≤ 1) : τ.im ≤ ‖denom γ τ‖ := by
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · have hdet : γ 1 1 * γ 0 0 = 1 := by
      have h : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.det_coe
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero, mul_comm] at h
      exact h
    rw [ModularGroup.denom_apply, hc]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with hd | hd <;> simpa [hd] using hτ
  · have h1 : (1 : ℝ) ≤ |(γ 1 0 : ℝ)| := by exact_mod_cast Int.one_le_abs hc
    refine le_trans ?_ (abs_im_le_norm _)
    rw [ModularGroup.denom_apply]
    simp [abs_of_pos τ.im_pos]
    nlinarith [τ.im_pos]

private lemma norm_le_jacobiSupBound_of_nonpos (hφ : φ ∈ jacobiFormSpace k 1) (hk : k ≤ 0) :
    ‖φ (τ, u)‖ ≤ jacobiSupBound φ := by
  rcases ModularGroup.exists_one_half_le_im_smul_and_norm_denom_le τ with ⟨γ, hγ, hd⟩
  exact (le_mul_of_one_le_right (norm_nonneg _) (one_le_zpow_of_nonpos₀
    (norm_pos_iff.mpr (denom_ne_zero γ τ)) hd hk)).trans (norm_mul_norm_denom_zpow_le τ u hφ hγ)

private lemma norm_mul_im_pow_le (hφ : φ ∈ jacobiFormSpace k 1) (hτ : τ.im ≤ 1) :
    ‖φ (τ, u)‖ * τ.im ^ k.toNat ≤ jacobiSupBound φ := by
  rcases le_or_gt 0 k with hk | hk
  · rcases ModularGroup.exists_one_half_le_im_smul_and_norm_denom_le τ with ⟨γ, hγ, -⟩
    refine (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)).trans
      (norm_mul_norm_denom_zpow_le τ u hφ hγ)
    rw [← Int.toNat_of_nonneg hk, zpow_natCast, Int.toNat_natCast]
    exact pow_le_pow_left₀ τ.im_pos.le (im_le_norm_denom γ hτ) _
  · rw [Int.toNat_of_nonpos hk.le, pow_zero, mul_one]
    exact norm_le_jacobiSupBound_of_nonpos τ u hφ hk.le

variable {y B : ℝ} (v : Fin 2 → ℝ)

/-- The point `(v₀ + yi, v₁)` of `ℍ × ℂ`, for real `v₀, v₁` and `y > 0`. -/
private noncomputable def heightPoint (hy : 0 < y) : ℍ × ℂ :=
  (mk (v 0 + y * I) (by simpa using hy), (v 1 : ℂ))

private lemma jacobiFourierExp_heightPoint (hy : 0 < y) (p : Fin 2 → ℤ) :
    jacobiFourierExp (p 0, p 1) (heightPoint v hy) =
      cexp (-2 * π * p 0 * y) * mFourier p fun i ↦ (v i : UnitAddCircle) := by
  simp only [jacobiFourierExp, heightPoint, mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, Fin.prod_univ_two, ← Complex.exp_add]
  congr 1
  linear_combination (2 * π * p 0 * y : ℂ) * I_sq

private lemma hasSum_heightPoint (hφ : φ ∈ jacobiFormSpace k 1) (hy : 0 < y) :
    HasSum (fun p : Fin 2 → ℤ ↦ jacobiCoeff φ (p 0, p 1) * cexp (-2 * π * p 0 * y) *
      mFourier p fun i ↦ (v i : UnitAddCircle)) (φ (heightPoint v hy)) :=
  ((finTwoArrowEquiv ℤ).hasSum_iff.mpr
    (hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ (heightPoint v hy))).congr_fun
      fun p ↦ by
        rw [mul_assoc, ← jacobiFourierExp_heightPoint]
        rfl

private lemma summable_heightCoeff (hφ : φ ∈ jacobiFormSpace k 1) (hy : 0 < y) :
    Summable fun p : Fin 2 → ℤ ↦ jacobiCoeff φ (p 0, p 1) * cexp (-2 * π * p 0 * y) :=
  (hasSum_heightPoint 0 hφ hy).summable.congr fun p ↦ by
    simp [mFourier]

private lemma norm_tsum_heightCoeff_le (hφ : φ ∈ jacobiFormSpace k 1) (hy : 0 < y)
    (hB : ∀ (τ : ℍ) (u : ℝ), τ.im = y → ‖φ (τ, u)‖ ≤ B) (x : UnitAddTorus (Fin 2)) :
    ‖∑' p, jacobiCoeff φ (p 0, p 1) * cexp (-2 * π * p 0 * y) * mFourier p x‖ ≤ B := by
  choose v hv using fun i ↦ QuotientAddGroup.mk_surjective (x i)
  rw [← (funext hv : (fun i ↦ (v i : UnitAddCircle)) = x), (hasSum_heightPoint v hφ hy).tsum_eq]
  exact hB _ _ (by simp)

variable (n r : ℤ)

private lemma norm_jacobiCoeff_mul_rexp_le (hφ : φ ∈ jacobiFormSpace k 1) (hy : 0 < y)
    (hB : ∀ (τ : ℍ) (u : ℝ), τ.im = y → ‖φ (τ, u)‖ ≤ B) :
    ‖jacobiCoeff φ (n, r)‖ * rexp (-(2 * π * n * y)) ≤ B := by
  have h : ‖jacobiCoeff φ (![n, r] 0, ![n, r] 1) * cexp (-2 * π * (![n, r] 0 : ℤ) * y)‖ ≤ B :=
    norm_le_of_norm_tsum_mFourier_le ![n, r] (summable_heightCoeff hφ hy)
      (norm_tsum_heightCoeff_le hφ hy hB)
  simpa [Complex.norm_exp] using h

/-- **The Fourier coefficients of a Jacobi form of index `1` grow polynomially** (Hecke's
bound): for `φ ∈ J_{k,1}`, `|c(n, r)| ≤ C e^{2π} (1 + |n|)^k` if `k ≥ 0`, and `|c(n, r)| ≤ C e^{2π}`
if `k < 0`, where `C = jacobiSupBound φ`. The coefficient `c(n, r) e^{-2πny}` is bounded by the
supremum of `|φ(x + iy, u)|` over real `x, u`, which is at most `C y^{-k}` for `y ≤ 1` by the
transformation laws of `φ`; take `y = 1/(1 + |n|)`. -/
lemma norm_jacobiCoeff_le_of_mem_jacobiFormSpace_one (hφ : φ ∈ jacobiFormSpace k 1) :
    ‖jacobiCoeff φ (n, r)‖ ≤ jacobiSupBound φ * rexp (2 * π) * (1 + |(n : ℝ)|) ^ k.toNat := by
  have hn : 0 < 1 + |(n : ℝ)| := by positivity
  have hy1 : (1 + |(n : ℝ)|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [abs_nonneg (n : ℝ)])
  have hB (τ : ℍ) (u : ℝ) (hτ : τ.im = (1 + |(n : ℝ)|)⁻¹) :
      ‖φ (τ, u)‖ ≤ jacobiSupBound φ * (1 + |(n : ℝ)|) ^ k.toNat := by
    have h : ‖φ (τ, u)‖ * τ.im ^ k.toNat ≤ jacobiSupBound φ :=
      norm_mul_im_pow_le τ u hφ (hτ ▸ hy1)
    rwa [hτ, inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)] at h
  have h : ‖jacobiCoeff φ (n, r)‖ * rexp (-(2 * π * n * (1 + |(n : ℝ)|)⁻¹)) ≤
      jacobiSupBound φ * (1 + |(n : ℝ)|) ^ k.toNat :=
    norm_jacobiCoeff_mul_rexp_le n r hφ (inv_pos.mpr hn) hB
  have hS : 0 ≤ jacobiSupBound φ := tsum_nonneg fun p ↦ by positivity
  have he : rexp (2 * π * n * (1 + |(n : ℝ)|)⁻¹) ≤ rexp (2 * π) := by
    have h1 : (n : ℝ) * (1 + |(n : ℝ)|)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hn]
      linarith [le_abs_self (n : ℝ)]
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos]
  have h' : ‖jacobiCoeff φ (n, r)‖ * rexp (-(2 * π * n * (1 + |(n : ℝ)|)⁻¹)) *
      rexp (2 * π * n * (1 + |(n : ℝ)|)⁻¹) ≤ jacobiSupBound φ * (1 + |(n : ℝ)|) ^ k.toNat *
        rexp (2 * π * n * (1 + |(n : ℝ)|)⁻¹) :=
    mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h'
  nlinarith [mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ jacobiSupBound φ *
    (1 + |(n : ℝ)|) ^ k.toNat)]

private lemma natCast_mul_le_jacobiSupBound_sq (hφ : φ ∈ jacobiFormSpace k 1) (hk : k ≤ 0) {N : ℕ}
    (hN : 1 ≤ N) :
    N * (‖jacobiCoeff φ (n, r)‖ ^ 2 * rexp (-(2 * π)) ^ 2) ≤ jacobiSupBound φ ^ 2 := by
  have hK : 0 < ((|n| + |r| + 1 : ℤ) : ℝ) * N ^ 2 := by
    positivity
  have hy : 0 < (((|n| + |r| + 1 : ℤ) : ℝ) * N ^ 2)⁻¹ := inv_pos.mpr hK
  have hinj : Function.Injective fun l : ℕ ↦ ![n + l * r + l ^ 2, r + 2 * l] := fun l l' h ↦ by
    simpa using congrFun h 1
  have h : ∑ p ∈ (Finset.range N).image (fun l : ℕ ↦ ![n + l * r + l ^ 2, r + 2 * l]),
      ‖jacobiCoeff φ (p 0, p 1) * cexp (-2 * π * p 0 * (((|n| + |r| + 1 : ℤ) : ℝ) * N ^ 2)⁻¹)‖ ^ 2 ≤
        jacobiSupBound φ ^ 2 :=
    sum_norm_sq_le_of_norm_tsum_mFourier_le (summable_heightCoeff hφ hy)
      (norm_tsum_heightCoeff_le hφ hy fun τ u _ ↦ norm_le_jacobiSupBound_of_nonpos τ u hφ hk) _
  have hN' : (N : ℝ) * (‖jacobiCoeff φ (n, r)‖ ^ 2 * rexp (-(2 * π)) ^ 2) =
      ((Finset.range N).image fun l : ℕ ↦ ![n + l * r + l ^ 2, r + 2 * l]).card •
        (‖jacobiCoeff φ (n, r)‖ ^ 2 * rexp (-(2 * π)) ^ 2) := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range, nsmul_eq_mul]
  rw [hN']
  refine (Finset.card_nsmul_le_sum _ _ _ fun p hp ↦ ?_).trans h
  rcases Finset.mem_image.mp hp with ⟨l, hl, rfl⟩
  have hl : (l : ℝ) ≤ N := by
    exact_mod_cast (Finset.mem_range.mp hl).le
  have hc : jacobiCoeff φ (n + l * r + l ^ 2, r + 2 * l) = jacobiCoeff φ (n, r) := by
    simpa using jacobiCoeff_add_of_mem_jacobiFormSpace l n r hφ
  have hnl : ((n + l * r + l ^ 2 : ℤ) : ℝ) * (((|n| + |r| + 1 : ℤ) : ℝ) * N ^ 2)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hK]
    push_cast
    have h1 : (1 : ℝ) ≤ N := by
      exact_mod_cast hN
    have hN2 : (N : ℝ) ≤ N ^ 2 := by
      nlinarith
    have hlr : (l : ℝ) * r ≤ |(r : ℝ)| * N ^ 2 :=
      (mul_le_mul_of_nonneg_left (le_abs_self (r : ℝ)) (Nat.cast_nonneg l)).trans <| by
        nlinarith [abs_nonneg (r : ℝ)]
    nlinarith [le_abs_self (n : ℝ), abs_nonneg (n : ℝ),
      mul_le_mul hl hl (Nat.cast_nonneg l) (Nat.cast_nonneg N)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hc, norm_mul, Complex.norm_exp, mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le ?_ 2) (by positivity)
  generalize (((|n| + |r| + 1 : ℤ) : ℝ) * N ^ 2)⁻¹ = y at hnl ⊢
  generalize n + l * r + l ^ 2 = a at hnl ⊢
  rw [Real.exp_le_exp]
  simp
  nlinarith [mul_le_mul_of_nonneg_left hnl Real.pi_pos.le]

lemma eq_zero_of_jacobiCoeff_eq_zero (hφ : φ ∈ jacobiFormSpace k 1) (hc : jacobiCoeff φ = 0) :
    φ = 0 :=
  funext fun x ↦ (hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ x).unique <| by
    simp [hc]

/-- **There are no nonzero Jacobi forms of weight `k ≤ 0` and index `1`**: for `k ≤ 0` the
transformation laws give `|φ(τ, u)| ≤ C` for all `τ` and real `u`, so by Bessel's inequality on
the torus at height `y`, `∑ |c(n_λ, r_λ)|² e^{-4πn_λ y} ≤ C²` over the `N` pairs
`(n_λ, r_λ) = (n + λr + λ², r + 2λ)`, `0 ≤ λ < N`, which carry the coefficient `c(n, r)`; with
`y = 1/((|n| + |r| + 1) N²)` this gives `N |c(n, r)|² e^{-4π} ≤ C²` for every `N ≥ 1`. -/
lemma eq_zero_of_mem_jacobiFormSpace_one_of_nonpos (hφ : φ ∈ jacobiFormSpace k 1) (hk : k ≤ 0) :
    φ = 0 := by
  refine eq_zero_of_jacobiCoeff_eq_zero hφ <| funext fun p ↦ ?_
  rcases p with ⟨n, r⟩
  rw [Pi.zero_apply, ← norm_eq_zero]
  by_contra hne
  have ha : 0 < ‖jacobiCoeff φ (n, r)‖ ^ 2 * rexp (-(2 * π)) ^ 2 := by
    have h0 : 0 < ‖jacobiCoeff φ (n, r)‖ := (norm_nonneg _).lt_of_ne' hne
    positivity
  rcases exists_nat_gt (jacobiSupBound φ ^ 2 /
    (‖jacobiCoeff φ (n, r)‖ ^ 2 * rexp (-(2 * π)) ^ 2)) with ⟨N, hN⟩
  have hN1 : 1 ≤ N := by
    have h0 : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    exact_mod_cast h0
  rw [div_lt_iff₀ ha] at hN
  linarith [natCast_mul_le_jacobiSupBound_sq n r hφ hk hN1]

end ModularForm
