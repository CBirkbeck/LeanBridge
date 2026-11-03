import LeanBridge.ForMathlib.Analysis.Fourier.TubeFourierSeries
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Jacobi.CoefficientGrowthIndex
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.GritsenkoLift
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ThetaTransformation

/-!
# Absolute convergence and holomorphy of the Gritsenko lift

The Gritsenko lift `Grit(φ)(Z) = ∑ a(n, r, m) e^{2πi(nτ + rz + Nmω)}` of a Jacobi cusp form
`φ ∈ J_{k,N}^cusp`, `N ≥ 1` (`SiegelUpperHalfSpace.gritsenkoLift`, LMFDB `mf.siegel.lift.gritsenko`)
is defined as a sum of series, with the junk value `0` where a series diverges. This file proves
that the series converges absolutely at every point of `ℋ₂`, so that the `tsum` means what it says.
The coefficients vanish unless `T = (n, r/2; r/2, Nm)` is positive definite, and then `|r| ≤ n + Nm`
and `tr(T Im Z) ≥ ε(n + Nm)` with `ε = det(Im Z) / tr(Im Z)`; by Hecke's bound
`|c(n, r)| ≤ C (1 + |n|)^k` for index `N`
(`ModularForm.norm_jacobiCoeff_le_of_mem_jacobiFormSpace`), the divisor sums satisfy
`|a(n, r, m)| ≤ C' (1 + n + Nm)^{k + 2k}`. The same estimates make the lift holomorphic.

The two general lemmas of this file, on series `∑ b(n, r, m) e^{2πi(nτ + rz + Nmω)}` with `b`
supported on the positive semidefinite `T`, are those proved for the Maass lift `N = 1` in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.MaassLiftHolomorphic`, where they are
private and specific to its coefficients.

## Main results

* `SiegelUpperHalfSpace.summable_mul_liftExp_of_norm_le`: a series with polynomially bounded
  coefficients supported on the positive semidefinite `T` converges absolutely on `ℋ₂`.
* `SiegelUpperHalfSpace.isHolomorphic_tsum_mul_liftExp`: such a series is holomorphic as soon as it
  converges absolutely on `ℋ₂`.
* `SiegelUpperHalfSpace.gritsenkoCoeff_eq_zero`: `a(n, r, m) = 0` unless `T` is positive definite.
* `SiegelUpperHalfSpace.summable_gritsenkoLift`: the series of the Gritsenko lift converges
  absolutely.
* `SiegelUpperHalfSpace.isHolomorphic_gritsenkoLift`: the Gritsenko lift is holomorphic.
-/

open Complex ModularForm Real

open scoped UpperHalfPlane

namespace SiegelUpperHalfSpace

variable {N : ℕ} {b : ℤ × ℤ × ℤ → ℂ} (p : ℤ × ℤ × ℤ) (Ω : SiegelUpperHalfSpace (Fin 2))
    (W : Fin 2 → Fin 2 → ℂ) {C ε : ℝ} {B : ℕ}

private lemma abs_le_add_of_le {n r M : ℝ} (hn : 0 ≤ n) (hM : 0 ≤ M) (hr : r ^ 2 ≤ 4 * n * M) :
    |r| ≤ n + M :=
  abs_le.mpr <| abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg (n - M)]) <| by positivity

private lemma add_mul_add_nonneg {n r M a e c : ℝ} (hn : 0 ≤ n) (hM : 0 ≤ M)
    (hr : r ^ 2 ≤ 4 * n * M) (ha : 0 ≤ a) (hc : 0 ≤ c) (he : e ^ 2 ≤ a * c) :
    0 ≤ n * a + r * e + M * c := by
  have h1 : r ^ 2 * e ^ 2 ≤ 4 * n * M * (a * c) :=
    mul_le_mul hr he (sq_nonneg e) (by positivity)
  nlinarith [sq_nonneg (n * a - M * c), mul_nonneg hn ha, mul_nonneg hM hc]

private lemma decay_mul_add_le_of_le {n r M : ℝ} (hn : 0 ≤ n) (hM : 0 ≤ M)
    (hr : r ^ 2 ≤ 4 * n * M) :
    decay Ω * (n + M) ≤ n * (Ω.val 0 0).im + r * (Ω.val 0 1).im + M * (Ω.val 1 1).im := by
  have ha : 0 < (Ω.val 0 0).im := by simpa using Ω.posDef_im.diag_pos
  have hc : 0 < (Ω.val 1 1).im := by simpa using Ω.posDef_im.diag_pos
  have key : 0 ≤ n * ((Ω.val 0 0).im ^ 2 + (Ω.val 0 1).im ^ 2) +
      r * ((Ω.val 0 1).im * ((Ω.val 0 0).im + (Ω.val 1 1).im)) +
        M * ((Ω.val 0 1).im ^ 2 + (Ω.val 1 1).im ^ 2) :=
    add_mul_add_nonneg hn hM hr (by positivity) (by positivity) <| by
      nlinarith [sq_nonneg ((Ω.val 0 0).im * (Ω.val 1 1).im - (Ω.val 0 1).im ^ 2)]
  rw [decay, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [key]

variable (N) in
/-- The triple `p = (n, r, m)` has `T = (n, r/2; r/2, Nm)` positive semidefinite. -/
def IsLiftSupport : Prop :=
  0 ≤ p.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 ^ 2 ≤ 4 * p.1 * (N * p.2.2)

variable {p}

private lemma IsLiftSupport.cast_fst (hp : IsLiftSupport N p) : (0 : ℝ) ≤ p.1 := by
  exact_mod_cast hp.1

private lemma IsLiftSupport.cast_mul (hp : IsLiftSupport N p) : (0 : ℝ) ≤ N * p.2.2 :=
  mul_nonneg (Nat.cast_nonneg N) (by exact_mod_cast hp.2.1)

private lemma IsLiftSupport.cast_sq (hp : IsLiftSupport N p) :
    (p.2.1 : ℝ) ^ 2 ≤ 4 * p.1 * (N * p.2.2) := by
  exact_mod_cast hp.2.2

variable (p)

/-- **A series with polynomially bounded coefficients supported on the positive semidefinite
`T = (n, r/2; r/2, Nm)` converges absolutely on `ℋ₂`**: for `N ≥ 1`, if `b(n, r, m) = 0` unless `T`
is positive semidefinite and `|b(n, r, m)| ≤ C (1 + n + Nm)^B`, then
`∑ b(n, r, m) e^{2πi(nτ + rz + Nmω)}` converges absolutely, since
`|e^{2πi(nτ + rz + Nmω)}| ≤ e^{-2πε(n + Nm)}` with `ε = det(Im Z) / tr(Im Z)` and `|r| ≤ n + Nm`. -/
lemma summable_mul_liftExp_of_norm_le (hN : 0 < N) (hC : 0 ≤ C)
    (hb₀ : ∀ p, ¬IsLiftSupport N p → b p = 0)
    (hb : ∀ p, IsLiftSupport N p → ‖b p‖ ≤ C * (1 + (p.1 + N * p.2.2 : ℝ)) ^ B) :
    Summable fun p : ℤ × ℤ × ℤ ↦ b p * liftExp N p.1 p.2.1 p.2.2 Ω := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hε : 0 < decay Ω := decay_pos Ω
  have hc : Summable fun t : ℤ ↦ rexp (-(π * decay Ω / 2 * |(t : ℝ)|)) :=
    summable_rexp_neg_mul_abs_int (by positivity)
  have hg : Summable fun p : ℤ × ℤ × ℤ ↦ rexp (-(π * decay Ω / 2 * |(p.1 : ℝ)|)) *
      (rexp (-(π * decay Ω / 2 * |(p.2.1 : ℝ)|)) *
        rexp (-(π * decay Ω / 2 * |(p.2.2 : ℝ)|))) :=
    hc.mul_of_nonneg (hc.mul_of_nonneg hc (fun _ ↦ Real.exp_nonneg _) fun _ ↦ Real.exp_nonneg _)
      (fun _ ↦ Real.exp_nonneg _) fun _ ↦ by positivity
  refine (hg.mul_left (C * (B.factorial / (π * decay Ω) ^ B) * rexp (π * decay Ω))).of_norm_bounded
    fun p ↦ ?_
  by_cases hp : IsLiftSupport N p
  · have hn : (0 : ℝ) ≤ p.1 := hp.cast_fst
    have hM : (0 : ℝ) ≤ N * p.2.2 := hp.cast_mul
    have hr : (p.2.1 : ℝ) ^ 2 ≤ 4 * p.1 * (N * p.2.2) := hp.cast_sq
    have hrb : |(p.2.1 : ℝ)| ≤ p.1 + N * p.2.2 := abs_le_add_of_le hn hM hr
    have hm : (0 : ℝ) ≤ p.2.2 := by exact_mod_cast hp.2.1
    have hmN : (p.2.2 : ℝ) ≤ N * p.2.2 := le_mul_of_one_le_left hm hN'
    have hexp :
        ‖liftExp N p.1 p.2.1 p.2.2 Ω‖ ≤ rexp (-(2 * π * (decay Ω * (p.1 + N * p.2.2)))) := by
      have h : decay Ω * (p.1 + N * p.2.2) ≤
          p.1 * (Ω.val 0 0).im + p.2.1 * (Ω.val 0 1).im + (N * p.2.2) * (Ω.val 1 1).im :=
        decay_mul_add_le_of_le Ω hn hM hr
      rw [liftExp, Complex.norm_exp, Real.exp_le_exp]
      simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat, add_im,
        intCast_re, intCast_im, natCast_re, natCast_im]
      nlinarith [Real.pi_pos]
    have hpow : (1 + (p.1 + N * p.2.2 : ℝ)) ^ B ≤ B.factorial / (π * decay Ω) ^ B *
        rexp (π * decay Ω * (1 + (p.1 + N * p.2.2))) :=
      one_add_pow_le_mul_rexp B (by positivity) (by positivity)
    have hsplit : rexp (π * decay Ω * (1 + (p.1 + N * p.2.2))) *
        rexp (-(2 * π * (decay Ω * (p.1 + N * p.2.2)))) ≤ rexp (π * decay Ω) *
          (rexp (-(π * decay Ω / 2 * |(p.1 : ℝ)|)) *
            (rexp (-(π * decay Ω / 2 * |(p.2.1 : ℝ)|)) *
              rexp (-(π * decay Ω / 2 * |(p.2.2 : ℝ)|)))) := by
      simp only [← Real.exp_add, Real.exp_le_exp]
      rw [abs_of_nonneg hn, abs_of_nonneg hm]
      nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hrb (by positivity : (0 : ℝ) ≤ π * decay Ω),
        mul_le_mul_of_nonneg_left hmN (by positivity : (0 : ℝ) ≤ π * decay Ω)]
    rw [norm_mul]
    refine ((mul_le_mul (hb p hp) hexp (norm_nonneg _) (by positivity)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC)
        (Real.exp_nonneg _))).trans ?_
    have h2 : C * (B.factorial / (π * decay Ω) ^ B *
        rexp (π * decay Ω * (1 + (p.1 + N * p.2.2)))) *
          rexp (-(2 * π * (decay Ω * (p.1 + N * p.2.2)))) =
        C * (B.factorial / (π * decay Ω) ^ B) * (rexp (π * decay Ω * (1 + (p.1 + N * p.2.2))) *
          rexp (-(2 * π * (decay Ω * (p.1 + N * p.2.2))))) := by
      ring1
    rw [h2]
    refine (mul_le_mul_of_nonneg_left hsplit (by positivity)).trans (le_of_eq ?_)
    ring1
  · rw [hb₀ p hp, zero_mul, norm_zero]
    positivity

variable (N) in
/-- The linear form `W ↦ nW₀₀ + r(W₀₁ + W₁₀)/2 + NmW₁₁` on the square matrices given by their
entries, for `p = (n, r, m)`. -/
private noncomputable def liftFormLevel : (Fin 2 → Fin 2 → ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun W ↦ p.1 * W 0 0 + p.2.1 * ((W 0 1 + W 1 0) / 2) + N * p.2.2 * W 1 1
      map_add' := fun W W' ↦ by
        simp only [Pi.add_apply]
        ring1
      map_smul' := fun c W ↦ by
        simp only [Pi.smul_apply, RingHom.id_apply]
        ring1 }
    (|(p.1 : ℝ)| + |(p.2.1 : ℝ)| + |(N * p.2.2 : ℝ)|) fun W ↦ by
      have h (i j : Fin 2) : ‖W i j‖ ≤ ‖W‖ :=
        (norm_le_pi_norm (W i) j).trans (norm_le_pi_norm W i)
      have h2 : ‖W 0 1 + W 1 0‖ ≤ 2 * ‖W‖ := (norm_add_le _ _).trans (by linarith [h 0 1, h 1 0])
      simp only [LinearMap.coe_mk]
      refine (norm_add₃_le).trans ?_
      simp only [norm_mul, Complex.norm_intCast, norm_div, Complex.norm_ofNat, Complex.norm_natCast,
        abs_mul, Nat.abs_cast]
      nlinarith [mul_le_mul_of_nonneg_left (h 0 0) (abs_nonneg (p.1 : ℝ)),
        mul_le_mul_of_nonneg_left h2 (abs_nonneg (p.2.1 : ℝ)),
        mul_le_mul_of_nonneg_left (h 1 1)
          (mul_nonneg (Nat.cast_nonneg N) (abs_nonneg (p.2.2 : ℝ)))]

private lemma liftFormLevel_apply : liftFormLevel N p W = p.1 * symmetrize W 0 0 +
    p.2.1 * symmetrize W 0 1 + N * p.2.2 * symmetrize W 1 1 := by
  simp only [liftFormLevel, symmetrize]
  simp
  ring1

variable (N b) in
/-- The term `b(n, r, m) e^{2πi(nW₀₀ + r(W₀₁ + W₁₀)/2 + NmW₁₁)}`, as a function of a square matrix
`W` given by its entries. -/
private noncomputable def liftTermLevel : ℂ :=
  b p * cexp (2 * π * I * liftFormLevel N p W)

private lemma hasFDerivAt_liftTermLevel : HasFDerivAt (liftTermLevel N b p)
    (b p • cexp (2 * π * I * liftFormLevel N p W) • (2 * π * I) • liftFormLevel N p) W :=
  (((liftFormLevel N p).hasFDerivAt.const_mul (2 * π * I)).cexp).const_mul _

variable {W₀ : Fin 2 → Fin 2 → ℂ}

private lemma im_liftFormLevel_ge (hW₀ : W₀ ∈ symmetrizePreimage (Fin 2)) (hp : IsLiftSupport N p)
    (hW : ‖W - W₀‖ < decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ / 4) :
    decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ / 2 * (p.1 + N * p.2.2) ≤
      (liftFormLevel N p W).im := by
  have hn : (0 : ℝ) ≤ p.1 := hp.cast_fst
  have hM : (0 : ℝ) ≤ N * p.2.2 := hp.cast_mul
  have hr : (p.2.1 : ℝ) ^ 2 ≤ 4 * p.1 * (N * p.2.2) := hp.cast_sq
  have hrb : |(p.2.1 : ℝ)| ≤ p.1 + N * p.2.2 := abs_le_add_of_le hn hM hr
  have h1 : decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ * (p.1 + N * p.2.2) ≤
      (liftFormLevel N p W₀).im := by
    rw [liftFormLevel_apply]
    simpa using decay_mul_add_le_of_le ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ hn hM hr
  have h2 : |(liftFormLevel N p (W - W₀)).im| ≤ (|(p.1 : ℝ)| + |(p.2.1 : ℝ)| + |(N * p.2.2 : ℝ)|) *
      (decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ / 4) :=
    (abs_im_le_norm _).trans <| ((liftFormLevel N p).le_opNorm _).trans <| mul_le_mul
      (LinearMap.mkContinuous_norm_le _ (by positivity) _) hW.le (norm_nonneg _) (by positivity)
  have h3 :
      (liftFormLevel N p W).im = (liftFormLevel N p W₀).im + (liftFormLevel N p (W - W₀)).im := by
    rw [map_sub, sub_im, add_sub_cancel]
  rw [abs_of_nonneg hn, abs_of_nonneg hM] at h2
  nlinarith [abs_le.mp h2, decay_pos ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩]

private lemma norm_fderiv_liftTermLevel_le (hb₀ : ∀ p, ¬IsLiftSupport N p → b p = 0)
    (hW₀ : W₀ ∈ symmetrizePreimage (Fin 2))
    (hW : ‖W - W₀‖ < decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ / 4) :
    ‖b p • cexp (2 * π * I * liftFormLevel N p W) • (2 * π * I) • liftFormLevel N p‖ ≤ ‖b p‖ *
      (8 / decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ *
        rexp (-(π * (decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ / 4) *
          (2 * (p.1 + N * p.2.2))))) := by
  by_cases hp : IsLiftSupport N p
  · have hn : (0 : ℝ) ≤ p.1 := hp.cast_fst
    have hM : (0 : ℝ) ≤ N * p.2.2 := hp.cast_mul
    have hr : (p.2.1 : ℝ) ^ 2 ≤ 4 * p.1 * (N * p.2.2) := hp.cast_sq
    have hrb : |(p.2.1 : ℝ)| ≤ p.1 + N * p.2.2 := abs_le_add_of_le hn hM hr
    have hexp : ‖cexp (2 * π * I * liftFormLevel N p W)‖ ≤
        rexp (-(π * (decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ / 2) *
          (2 * (p.1 + N * p.2.2)))) := by
      have h : decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ / 2 * (p.1 + N * p.2.2) ≤
          (liftFormLevel N p W).im :=
        im_liftFormLevel_ge p W hW₀ hp hW
      rw [Complex.norm_exp, Real.exp_le_exp]
      simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
      nlinarith [Real.pi_pos]
    have hL : ‖(2 * π * I : ℂ) • liftFormLevel N p‖ ≤ π * (2 * (2 * (p.1 + N * p.2.2))) := by
      rw [norm_smul]
      have h2 : ‖(2 * π * I : ℂ)‖ = 2 * π := by
        simp
      rw [h2]
      have h3 : ‖liftFormLevel N p‖ ≤ |(p.1 : ℝ)| + |(p.2.1 : ℝ)| + |(N * p.2.2 : ℝ)| :=
        LinearMap.mkContinuous_norm_le _ (by positivity) _
      rw [abs_of_nonneg hn, abs_of_nonneg hM] at h3
      nlinarith [Real.pi_pos]
    rw [norm_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left ((mul_le_mul hexp hL (norm_nonneg _)
      (Real.exp_nonneg _)).trans (rexp_neg_mul_mul_le (decay_pos _))) (norm_nonneg _)
  · rw [hb₀ p hp, norm_smul, norm_zero, zero_mul, zero_mul]

private lemma summable_norm_mul_rexp (hs : ∀ Z : SiegelUpperHalfSpace (Fin 2),
    Summable fun p : ℤ × ℤ × ℤ ↦ b p * liftExp N p.1 p.2.1 p.2.2 Z) (hε : 0 < ε) :
    Summable fun p : ℤ × ℤ × ℤ ↦ ‖b p‖ * rexp (-(π * ε * (2 * (p.1 + N * p.2.2)))) := by
  refine (summable_norm_iff.mpr (hs (diagPoint (UpperHalfPlane.mk (ε * I) (by simpa using hε))
    ⟨ε, hε⟩))).congr fun p ↦ ?_
  rw [norm_mul, liftExp, Complex.norm_exp]
  congr 2
  simp [diagPoint]
  ring1

private lemma hasFDerivAt_tsum_liftTermLevel (hb₀ : ∀ p, ¬IsLiftSupport N p → b p = 0)
    (hs : ∀ Z : SiegelUpperHalfSpace (Fin 2), Summable fun p : ℤ × ℤ × ℤ ↦ b p *
      liftExp N p.1 p.2.1 p.2.2 Z) (hW₀ : W₀ ∈ symmetrizePreimage (Fin 2)) : HasFDerivAt
    (fun W ↦ ∑' p, liftTermLevel N b p W) (∑' p, b p •
      cexp (2 * π * I * liftFormLevel N p W₀) • (2 * π * I) • liftFormLevel N p) W₀ := by
  have hε : 0 < decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ := decay_pos _
  have hε4 : 0 < decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ / 4 := by
    positivity
  refine hasFDerivAt_tsum_of_isPreconnected (((summable_norm_mul_rexp hs hε4).mul_left
    (8 / decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩)).congr fun p ↦ ?_)
    Metric.isOpen_ball (convex_ball _ _).isPreconnected (fun p W _ ↦ hasFDerivAt_liftTermLevel p W)
    (fun p W hW ↦ norm_fderiv_liftTermLevel_le p W hb₀ hW₀ ?_) (Metric.mem_ball_self hε4)
    ((hs ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩).congr fun p ↦ ?_)
    (Metric.mem_ball_self hε4)
  · ring1
  · rwa [Metric.mem_ball, dist_eq_norm] at hW
  · rw [liftTermLevel, liftFormLevel_apply, liftExp]

/-- **A series `∑ b(n, r, m) e^{2πi(nτ + rz + Nmω)}` with coefficients supported on the positive
semidefinite `T = (n, r/2; r/2, Nm)` is holomorphic** as soon as it converges absolutely on `ℋ₂`: on
a ball around a point the series of the derivatives of the terms is dominated by the series at a
point `(iε/2) 1`. -/
lemma isHolomorphic_tsum_mul_liftExp (hb₀ : ∀ p, ¬IsLiftSupport N p → b p = 0)
    (hs : ∀ Z : SiegelUpperHalfSpace (Fin 2), Summable fun p : ℤ × ℤ × ℤ ↦ b p *
      liftExp N p.1 p.2.1 p.2.2 Z) :
    IsHolomorphic fun Z ↦ ∑' p : ℤ × ℤ × ℤ, b p * liftExp N p.1 p.2.1 p.2.2 Z := by
  refine isHolomorphic_iff_differentiableOn.mpr <| DifferentiableOn.congr (fun W₀ hW₀ ↦
    (hasFDerivAt_tsum_liftTermLevel hb₀ hs hW₀).differentiableAt.differentiableWithinAt)
      fun W hW ↦ ?_
  rw [extend_of_mem _ hW]
  refine tsum_congr fun p ↦ ?_
  rw [liftTermLevel, liftFormLevel_apply, liftExp]

variable {k : ℤ} {φ : ℍ × ℂ → ℂ} {n r m : ℤ} {d : ℕ}

private lemma sq_mul_disc_level (hd : d ∈ ((n.gcd r : ℤ).gcd m).divisors) :
    (d : ℤ) ^ 2 * (4 * (n * m / (d : ℤ) ^ 2) * N - (r / d) ^ 2) = 4 * n * m * N - r ^ 2 := by
  have hd0 : (d : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
  have hg : (d : ℤ) ∣ ((n.gcd r : ℤ).gcd m : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mem_divisors hd)
  have hg' : (d : ℤ) ∣ (n.gcd r : ℤ) := hg.trans (Int.gcd_dvd_left _ _)
  rcases hg'.trans (Int.gcd_dvd_left _ _) with ⟨n₁, hn₁⟩
  rcases hg'.trans (Int.gcd_dvd_right _ _) with ⟨r₁, hr₁⟩
  rcases hg.trans (Int.gcd_dvd_right _ _) with ⟨m₁, hm₁⟩
  rw [hn₁, hr₁, hm₁]
  have h₁ : (d : ℤ) * n₁ * (d * m₁) / d ^ 2 = n₁ * m₁ :=
    Int.ediv_eq_of_eq_mul_right (pow_ne_zero 2 hd0) (by ring1)
  rw [h₁, Int.mul_ediv_cancel_left _ hd0]
  ring1

variable (n r m) in
/-- **The coefficients of the Gritsenko lift of a Jacobi cusp form are supported on the positive
definite `T = (n, r/2; r/2, Nm)`**: `a(n, r, m) = 0` unless `n, m > 0` and `4nNm > r²`, as
`a(n, r, m)` is a sum of coefficients `c(nm/d², r/d)` of discriminants `(4nmN - r²)/d²`. -/
lemma gritsenkoCoeff_eq_zero (hφ : φ ∈ jacobiCuspFormSpace k N)
    (h : ¬(0 < n ∧ 0 < m ∧ r ^ 2 < 4 * n * (N * m))) :
    gritsenkoCoeff k (jacobiCoeff φ) n r m = 0 := by
  rw [gritsenkoCoeff]
  split_ifs with hm
  · refine Finset.sum_eq_zero fun d hd ↦ ?_
    rw [jacobiCoeff_eq_zero_of_mem_jacobiFourierSupported hφ.2, mul_zero]
    intro hlt
    have hr : r ^ 2 < 4 * n * (N * m) := by
      have h₁ : 0 < (d : ℤ) ^ 2 * (4 * (n * m / (d : ℤ) ^ 2) * N - (r / d) ^ 2) :=
        mul_pos (pow_pos (Nat.cast_pos.mpr (Nat.pos_of_mem_divisors hd)) 2) (sub_pos.mpr hlt)
      rw [sq_mul_disc_level hd] at h₁
      linarith
    refine h ⟨?_, hm, hr⟩
    by_contra hn
    have hN₀ : (0 : ℤ) ≤ N := Int.natCast_nonneg N
    nlinarith [sq_nonneg r, mul_nonneg hN₀ hm.le, mul_nonneg (not_lt.mp hn |> neg_nonneg.mpr)
      (mul_nonneg hN₀ hm.le)]
  · rfl

variable {p} in
private lemma isLiftSupport_of_gritsenkoCoeff_ne_zero (hφ : φ ∈ jacobiCuspFormSpace k N)
    (hp : gritsenkoCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 ≠ 0) : IsLiftSupport N p := by
  have h : 0 < p.1 ∧ 0 < p.2.2 ∧ p.2.1 ^ 2 < 4 * p.1 * (N * p.2.2) :=
    not_not.mp fun h ↦ hp (gritsenkoCoeff_eq_zero _ _ _ hφ h)
  exact ⟨h.1.le, h.2.1.le, h.2.2.le⟩

variable {p} in
private lemma norm_gritsenkoCoeff_le (hN : 0 < N) (hk : 1 ≤ k) {A : ℕ} (hC : 0 ≤ C)
    (hc : ∀ n r : ℤ, ‖jacobiCoeff φ (n, r)‖ ≤ C * (1 + |(n : ℝ)|) ^ A) (hp : IsLiftSupport N p) :
    ‖gritsenkoCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2‖ ≤ C *
      (1 + (p.1 + N * p.2.2 : ℝ)) ^ ((k - 1).toNat + 1 + 2 * A) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ) ≤ p.1 := by exact_mod_cast hp.1
  have hm : (0 : ℝ) ≤ p.2.2 := by exact_mod_cast hp.2.1
  have hmN : (p.2.2 : ℝ) ≤ N * p.2.2 := le_mul_of_one_le_left hm hN'
  rw [gritsenkoCoeff]
  split_ifs with hm₀
  swap
  · rw [norm_zero]
    positivity
  rw [liftDivisorSum]
  have hm₀' : (1 : ℝ) ≤ p.2.2 := by exact_mod_cast hm₀
  have hg : (((p.1.gcd p.2.1 : ℤ).gcd p.2.2 : ℕ) : ℤ) ≤ p.2.2 :=
    Int.le_of_dvd hm₀ (Int.gcd_dvd_right _ _)
  have hg'' : (((p.1.gcd p.2.1 : ℤ).gcd p.2.2 : ℕ) : ℝ) ≤ p.2.2 := by
    exact_mod_cast hg
  have hg' : (((p.1.gcd p.2.1 : ℤ).gcd p.2.2 : ℕ) : ℝ) ≤ p.1 + N * p.2.2 := by
    linarith
  have hterm (d : ℕ) (hd : d ∈ ((p.1.gcd p.2.1 : ℤ).gcd p.2.2).divisors) :
      ‖(d : ℂ) ^ (k - 1) * jacobiCoeff φ (p.1 * p.2.2 / (d : ℤ) ^ 2, p.2.1 / d)‖ ≤
        C * (1 + (p.1 + N * p.2.2 : ℝ)) ^ ((k - 1).toNat + 2 * A) := by
    have hdg : (d : ℝ) ≤ p.1 + N * p.2.2 :=
      (Nat.cast_le.mpr (Nat.divisor_le hd)).trans hg'
    have hk' : k - 1 = ((k - 1).toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
    have hdiv : |((p.1 * p.2.2 / (d : ℤ) ^ 2 : ℤ) : ℝ)| ≤ p.1 * p.2.2 := by
      have h2 : 0 ≤ p.1 * p.2.2 / (d : ℤ) ^ 2 :=
        Int.ediv_nonneg (mul_nonneg hp.1 hp.2.1) (by positivity)
      have h3 : p.1 * p.2.2 / (d : ℤ) ^ 2 ≤ p.1 * p.2.2 :=
        Int.ediv_le_self _ (mul_nonneg hp.1 hp.2.1)
      rw [abs_of_nonneg (by exact_mod_cast h2)]
      exact_mod_cast h3
    rw [norm_mul, norm_zpow, Complex.norm_natCast, hk', zpow_natCast, pow_add, mul_comm C,
      mul_assoc]
    refine mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) _) ((hc _ _).trans ?_)
      (norm_nonneg _) (by positivity)
    rw [pow_mul, mul_comm C]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ _) hC
    nlinarith
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (((p.1.gcd p.2.1 : ℤ).gcd p.2.2).divisors.card : ℝ) ≤ 1 + (p.1 + N * p.2.2 : ℝ) :=
    (Nat.cast_le.mpr (Nat.card_divisors_le_self _)).trans (by linarith)
  have hpow : (1 + (p.1 + N * p.2.2 : ℝ)) ^ ((k - 1).toNat + 1 + 2 * A) =
      (1 + (p.1 + N * p.2.2 : ℝ)) * (1 + (p.1 + N * p.2.2 : ℝ)) ^ ((k - 1).toNat + 2 * A) := by
    ring1
  rw [hpow, mul_left_comm C]
  exact mul_le_mul_of_nonneg_right hcard (by positivity)

variable (k n r m) in
lemma gritsenkoCoeff_jacobiCoeff_zero :
    gritsenkoCoeff k (jacobiCoeff (0 : ℍ × ℂ → ℂ)) n r m = 0 := by
  rw [hasJacobiFourierExpansion_zero.jacobiCoeff_eq]
  simp [gritsenkoCoeff, liftDivisorSum]

/-- **The series of the Gritsenko lift converges absolutely** at every point of `ℋ₂` (LMFDB
`mf.siegel.lift.gritsenko`), for every Jacobi cusp form `φ ∈ J_{k,N}^cusp`, `N ≥ 1`: the Fourier
coefficients of `φ` grow polynomially, `|c(n, r)| ≤ C (1 + |n|)^k`, so that
`|a(n, r, m)| ≤ C (1 + n + Nm)^{k + 2k}` on the positive semidefinite `T = (n, r/2; r/2, Nm)`, which
carry the coefficients; and `φ = 0` for `k ≤ 0`. -/
lemma summable_gritsenkoLift (hN : 0 < N) (hφ : φ ∈ jacobiCuspFormSpace k N) :
    Summable fun p : ℤ × ℤ × ℤ ↦ gritsenkoCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 *
      liftExp N p.1 p.2.1 p.2.2 Ω := by
  rcases le_or_gt k 0 with hk | hk
  · rw [eq_zero_of_mem_jacobiFormSpace_of_nonpos hN hφ.1 hk]
    simp [gritsenkoCoeff_jacobiCoeff_zero]
  · have hC : 0 ≤ jacobiSupBound φ * rexp (2 * π) :=
      mul_nonneg jacobiSupBound_nonneg (Real.exp_nonneg _)
    exact summable_mul_liftExp_of_norm_le Ω hN hC
      (fun _ hp ↦ not_not.mp fun h ↦ hp (isLiftSupport_of_gritsenkoCoeff_ne_zero hφ h))
      fun _ hp ↦ norm_gritsenkoCoeff_le hN (by omega) hC
        (fun n r ↦ norm_jacobiCoeff_le_of_mem_jacobiFormSpace n r hN hφ.1) hp

/-- **The Gritsenko lift of a Jacobi cusp form is holomorphic** on `ℋ₂` (LMFDB
`mf.siegel.lift.gritsenko`). -/
lemma isHolomorphic_gritsenkoLift (hN : 0 < N) (hφ : φ ∈ jacobiCuspFormSpace k N) :
    IsHolomorphic (gritsenkoLift k N φ) :=
  isHolomorphic_tsum_mul_liftExp
    (fun _ hp ↦ not_not.mp fun h ↦ hp (isLiftSupport_of_gritsenkoCoeff_ne_zero hφ h))
    fun Z ↦ summable_gritsenkoLift Z hN hφ

end SiegelUpperHalfSpace
