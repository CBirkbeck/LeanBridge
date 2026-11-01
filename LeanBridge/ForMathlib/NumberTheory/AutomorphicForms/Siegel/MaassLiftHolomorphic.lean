import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.MaassLiftIndexRaising

/-!
# Holomorphy of the Maass lift

The Maass lift `F(Z) = ∑ a(n, r, m) e^{2πi(nτ + rz + mω)}` of a Jacobi form `φ ∈ J_{k,1}`
(`SiegelUpperHalfSpace.maassLift`, LMFDB `mf.siegel.lift.maass`) is holomorphic on `ℋ₂` as soon as
its series converges absolutely at every point. The coefficients vanish unless
`T = (n, r/2; r/2, m)` is positive semidefinite, and then `|r| ≤ n + m` and
`tr(T Im Z) ≥ ε(n + m)` with `ε = det(Im Z) / tr(Im Z)`. On a ball of radius `ε/4` around a point
the terms are then dominated by `|a(n, r, m)| e^{-πε(n + m)}` and their derivatives by
`8/ε |a(n, r, m)| e^{-πε(n + m)/2}`, the absolute values of the terms of the series at the point
`(iε/4) 1`, so the series can be differentiated term by term (as for the theta constants in
`SiegelUpperHalfSpace.isHolomorphic_thetaConstant`). With the reduction of the theorem of Maass to
convergence and holomorphy, the Maass lift of `φ ∈ J_{k,1}`, `k ≥ 3`, is a Siegel modular form of
weight `k` on `Sp(4, ℤ)` as soon as its series converges absolutely on `ℋ₂`. The series converges
absolutely if the Fourier coefficients of `φ` grow polynomially, `‖c(n, r)‖ ≤ C (1 + |n|)^A`: the
divisor sums then satisfy `|a(n, r, m)| ≤ C' (1 + n + m)^{k + 2A}`, and the terms are dominated by
`e^{-πε(|n| + |r| + |m|)/2}` up to a constant. That bound on `c(n, r)` (a Hecke-type estimate for
Jacobi forms) is proved in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Jacobi.CoefficientGrowth`.

## Main results

* `SiegelUpperHalfSpace.isHolomorphic_maassLift`: the Maass lift is holomorphic if its series
  converges absolutely on `ℋ₂`.
* `SiegelUpperHalfSpace.maassLift_mem_scalarModularForms_of_forall_summable`: for `φ ∈ J_{k,1}`
  with `k ≥ 3`, the Maass lift is a Siegel modular form of weight `k` on `Sp(4, ℤ)` if its series
  converges absolutely on `ℋ₂`.
* `SiegelUpperHalfSpace.summable_maassLift_of_norm_jacobiCoeff_le`: the series of the Maass lift
  converges absolutely if the Fourier coefficients of `φ` grow polynomially.
* `SiegelUpperHalfSpace.maassLift_mem_scalarModularForms_of_norm_jacobiCoeff_le`: for
  `φ ∈ J_{k,1}` with `k ≥ 3` and polynomially bounded Fourier coefficients, the Maass lift is a
  Siegel modular form of weight `k` on `Sp(4, ℤ)`.
-/

open Complex ModularForm Real SymplecticGroup

open scoped UpperHalfPlane

namespace SiegelUpperHalfSpace

variable {k : ℤ} {φ : ℍ × ℂ → ℂ} (p : ℤ × ℤ × ℤ) (Ω : SiegelUpperHalfSpace (Fin 2))
    (W : Fin 2 → Fin 2 → ℂ) {C ε : ℝ} {A B : ℕ}

private lemma abs_le_add_of_posSemidef (hp : 0 ≤ p.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 ^ 2 ≤ 4 * p.1 * p.2.2) :
    |(p.2.1 : ℝ)| ≤ p.1 + p.2.2 := by
  have hn : (0 : ℝ) ≤ p.1 := by exact_mod_cast hp.1
  have hm : (0 : ℝ) ≤ p.2.2 := by exact_mod_cast hp.2.1
  have h : (p.2.1 : ℝ) ^ 2 ≤ 4 * p.1 * p.2.2 := by exact_mod_cast hp.2.2
  exact abs_le.mpr <| abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg ((p.1 : ℝ) - p.2.2)]) <| by
    positivity

private lemma add_mul_add_nonneg {n r m a b c : ℝ} (hn : 0 ≤ n) (hm : 0 ≤ m)
    (hr : r ^ 2 ≤ 4 * n * m) (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : b ^ 2 ≤ a * c) :
    0 ≤ n * a + r * b + m * c := by
  have h1 : r ^ 2 * b ^ 2 ≤ 4 * n * m * (a * c) :=
    mul_le_mul hr hb (sq_nonneg b) (by positivity)
  nlinarith [sq_nonneg (n * a - m * c), mul_nonneg hn ha, mul_nonneg hm hc]

private lemma decay_mul_add_le (hp : 0 ≤ p.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 ^ 2 ≤ 4 * p.1 * p.2.2) :
    decay Ω * (p.1 + p.2.2) ≤ p.1 * (Ω.val 0 0).im + p.2.1 * (Ω.val 0 1).im +
      p.2.2 * (Ω.val 1 1).im := by
  have ha : 0 < (Ω.val 0 0).im := by simpa using Ω.posDef_im.diag_pos (i := 0)
  have hc : 0 < (Ω.val 1 1).im := by simpa using Ω.posDef_im.diag_pos (i := 1)
  have hn : (0 : ℝ) ≤ p.1 := by exact_mod_cast hp.1
  have hm : (0 : ℝ) ≤ p.2.2 := by exact_mod_cast hp.2.1
  have hr : (p.2.1 : ℝ) ^ 2 ≤ 4 * p.1 * p.2.2 := by exact_mod_cast hp.2.2
  have key : 0 ≤ p.1 * ((Ω.val 0 0).im ^ 2 + (Ω.val 0 1).im ^ 2) +
      p.2.1 * ((Ω.val 0 1).im * ((Ω.val 0 0).im + (Ω.val 1 1).im)) +
        p.2.2 * ((Ω.val 0 1).im ^ 2 + (Ω.val 1 1).im ^ 2) :=
    add_mul_add_nonneg hn hm hr (by positivity) (by positivity) <| by
      nlinarith [sq_nonneg ((Ω.val 0 0).im * (Ω.val 1 1).im - (Ω.val 0 1).im ^ 2)]
  rw [decay, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [key]

/-- The linear form `W ↦ nW₀₀ + r(W₀₁ + W₁₀)/2 + mW₁₁` on the square matrices given by their
entries, for `p = (n, r, m)`. -/
private noncomputable def liftForm : (Fin 2 → Fin 2 → ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun W ↦ p.1 * W 0 0 + p.2.1 * ((W 0 1 + W 1 0) / 2) + p.2.2 * W 1 1
      map_add' := fun W W' ↦ by
        simp only [Pi.add_apply]
        ring1
      map_smul' := fun c W ↦ by
        simp only [Pi.smul_apply, RingHom.id_apply]
        ring1 }
    (|(p.1 : ℝ)| + |(p.2.1 : ℝ)| + |(p.2.2 : ℝ)|) fun W ↦ by
      have h (i j : Fin 2) : ‖W i j‖ ≤ ‖W‖ :=
        (norm_le_pi_norm (W i) j).trans (norm_le_pi_norm W i)
      have h2 : ‖W 0 1 + W 1 0‖ ≤ 2 * ‖W‖ := (norm_add_le _ _).trans (by linarith [h 0 1, h 1 0])
      simp only [LinearMap.coe_mk]
      refine (norm_add₃_le).trans ?_
      simp only [norm_mul, Complex.norm_intCast, norm_div, Complex.norm_ofNat]
      nlinarith [mul_le_mul_of_nonneg_left (h 0 0) (abs_nonneg (p.1 : ℝ)),
        mul_le_mul_of_nonneg_left h2 (abs_nonneg (p.2.1 : ℝ)),
        mul_le_mul_of_nonneg_left (h 1 1) (abs_nonneg (p.2.2 : ℝ))]

private lemma liftForm_apply : liftForm p W =
    p.1 * symmetrize W 0 0 + p.2.1 * symmetrize W 0 1 + p.2.2 * symmetrize W 1 1 := by
  simp only [liftForm, LinearMap.mkContinuous_apply, symmetrize]
  simp
  ring1

variable (k φ) in
/-- The term `a(n, r, m) e^{2πi(nW₀₀ + r(W₀₁ + W₁₀)/2 + mW₁₁)}` of the Maass lift, as a function of
a square matrix `W` given by its entries. -/
private noncomputable def liftTerm : ℂ :=
  maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * cexp (2 * π * I * liftForm p W)

private lemma hasFDerivAt_liftTerm : HasFDerivAt (liftTerm k φ p)
    (maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 •
      cexp (2 * π * I * liftForm p W) • (2 * π * I) • liftForm p) W :=
  (((liftForm p).hasFDerivAt.const_mul (2 * π * I)).cexp).const_mul _

variable {W₀ : Fin 2 → Fin 2 → ℂ}

private lemma im_liftForm_ge (hW₀ : W₀ ∈ symmetrizePreimage (Fin 2))
    (hp : 0 ≤ p.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 ^ 2 ≤ 4 * p.1 * p.2.2)
    (hW : ‖W - W₀‖ < decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ / 4) :
    decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ / 2 * (p.1 + p.2.2) ≤
      (liftForm p W).im := by
  have hn : (0 : ℝ) ≤ p.1 := by exact_mod_cast hp.1
  have hm : (0 : ℝ) ≤ p.2.2 := by exact_mod_cast hp.2.1
  have hr : |(p.2.1 : ℝ)| ≤ p.1 + p.2.2 := abs_le_add_of_posSemidef p hp
  have h1 :
      decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ * (p.1 + p.2.2) ≤ (liftForm p W₀).im := by
    rw [liftForm_apply]
    simpa using decay_mul_add_le p ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ hp
  have h2 : |(liftForm p (W - W₀)).im| ≤ (|(p.1 : ℝ)| + |(p.2.1 : ℝ)| + |(p.2.2 : ℝ)|) *
      (decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ / 4) :=
    (abs_im_le_norm _).trans <| ((liftForm p).le_opNorm _).trans <| mul_le_mul
      (LinearMap.mkContinuous_norm_le _ (by positivity) _) hW.le (norm_nonneg _) (by positivity)
  have h3 : (liftForm p W).im = (liftForm p W₀).im + (liftForm p (W - W₀)).im := by
    rw [map_sub, sub_im, add_sub_cancel]
  rw [abs_of_nonneg hn, abs_of_nonneg hm] at h2
  nlinarith [abs_le.mp h2, decay_pos ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩]

private lemma norm_fderiv_liftTerm_le (hφ : φ ∈ jacobiFormSpace k 1)
    (hW₀ : W₀ ∈ symmetrizePreimage (Fin 2))
    (hW : ‖W - W₀‖ < decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ / 4) :
    ‖maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 •
      cexp (2 * π * I * liftForm p W) • (2 * π * I) • liftForm p‖ ≤
        ‖maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2‖ *
          (8 / decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ *
            rexp (-(π * (decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ / 4) *
              (2 * (p.1 + p.2.2))))) := by
  by_cases hp : 0 ≤ p.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 ^ 2 ≤ 4 * p.1 * p.2.2
  · have hn : (0 : ℝ) ≤ p.1 := by exact_mod_cast hp.1
    have hm : (0 : ℝ) ≤ p.2.2 := by exact_mod_cast hp.2.1
    have hr : |(p.2.1 : ℝ)| ≤ p.1 + p.2.2 := abs_le_add_of_posSemidef p hp
    have hexp : ‖cexp (2 * π * I * liftForm p W)‖ ≤
        rexp (-(π * (decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ / 2) *
          (2 * (p.1 + p.2.2)))) := by
      have h : decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ / 2 * (p.1 + p.2.2) ≤
          (liftForm p W).im :=
        im_liftForm_ge p W hW₀ hp hW
      rw [Complex.norm_exp, Real.exp_le_exp]
      simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
      nlinarith [Real.pi_pos]
    have hL : ‖(2 * π * I : ℂ) • liftForm p‖ ≤ π * (2 * (2 * (p.1 + p.2.2))) := by
      rw [norm_smul]
      have h2 : ‖(2 * π * I : ℂ)‖ = 2 * π := by
        simp
      rw [h2]
      have h3 : ‖liftForm p‖ ≤ |(p.1 : ℝ)| + |(p.2.1 : ℝ)| + |(p.2.2 : ℝ)| :=
        LinearMap.mkContinuous_norm_le _ (by positivity) _
      rw [abs_of_nonneg hn, abs_of_nonneg hm] at h3
      nlinarith [Real.pi_pos]
    rw [norm_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left ((mul_le_mul hexp hL (norm_nonneg _)
      (Real.exp_pos _).le).trans (rexp_neg_mul_mul_le (decay_pos _))) (norm_nonneg _)
  · rw [maassCoeff_eq_zero_of_not_posSemidef _ _ _ hφ hp, norm_smul, norm_zero, zero_mul, zero_mul]

private lemma summable_norm_maassCoeff_mul_rexp
    (hs : ∀ Z : SiegelUpperHalfSpace (Fin 2), Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z)
    (hε : 0 < ε) : Summable fun p : ℤ × ℤ × ℤ ↦
      ‖maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2‖ * rexp (-(π * ε * (2 * (p.1 + p.2.2)))) := by
  refine (summable_norm_iff.mpr (hs (diagPoint (UpperHalfPlane.mk (ε * I) (by simpa using hε))
    ⟨ε, hε⟩))).congr fun p ↦ ?_
  rw [norm_mul, liftExp, Complex.norm_exp]
  congr 2
  simp [diagPoint]
  ring1

private lemma hasFDerivAt_tsum_liftTerm (hφ : φ ∈ jacobiFormSpace k 1)
    (hs : ∀ Z : SiegelUpperHalfSpace (Fin 2), Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z)
    (hW₀ : W₀ ∈ symmetrizePreimage (Fin 2)) : HasFDerivAt (fun W ↦ ∑' p, liftTerm k φ p W)
      (∑' p, maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 •
        cexp (2 * π * I * liftForm p W₀) • (2 * π * I) • liftForm p) W₀ := by
  have hε : 0 < decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ := decay_pos _
  have hε4 : 0 < decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩ / 4 := by
    positivity
  refine hasFDerivAt_tsum_of_isPreconnected (((summable_norm_maassCoeff_mul_rexp hs hε4).mul_left
    (8 / decay ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩)).congr fun p ↦ ?_)
    Metric.isOpen_ball (convex_ball _ _).isPreconnected (fun p W _ ↦ hasFDerivAt_liftTerm p W)
    (fun p W hW ↦ norm_fderiv_liftTerm_le p W hφ hW₀ ?_) (Metric.mem_ball_self hε4)
    ((hs ⟨symmetrize W₀, transpose_symmetrize W₀, hW₀⟩).congr fun p ↦ ?_)
    (Metric.mem_ball_self hε4)
  · ring1
  · rwa [Metric.mem_ball, dist_eq_norm] at hW
  · rw [liftTerm, liftForm_apply, liftExp]
    simp

/-- **The Maass lift is holomorphic** as soon as its series converges absolutely on `ℋ₂`, for a
Jacobi form `φ ∈ J_{k,1}`: the coefficients `a(n, r, m)` vanish unless `T = (n, r/2; r/2, m)` is
positive semidefinite, and then `tr(TY) ≥ ε(n + m)` and `|r| ≤ n + m` for `Y = Im Z` near a point
with `det(Y) / tr(Y) ≥ 2ε`, so the series of the derivatives of the terms is dominated by
`8/ε ∑ |a(n, r, m)| e^{-πε(n + m)}`, the series of the lift at `(iε/2) 1`. -/
lemma isHolomorphic_maassLift (hφ : φ ∈ jacobiFormSpace k 1)
    (hs : ∀ Z : SiegelUpperHalfSpace (Fin 2), Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z) :
    IsHolomorphic (maassLift k φ) := by
  refine isHolomorphic_iff_differentiableOn.mpr <| DifferentiableOn.congr (fun W₀ hW₀ ↦
    (hasFDerivAt_tsum_liftTerm hφ hs hW₀).differentiableAt.differentiableWithinAt) fun W hW ↦ ?_
  rw [extend_of_mem _ hW, maassLift]
  refine tsum_congr fun p ↦ ?_
  rw [liftTerm, liftForm_apply, liftExp]
  simp

private lemma summable_rexp_neg_mul_abs (hε : 0 < ε) :
    Summable fun t : ℤ ↦ rexp (-(ε * |(t : ℝ)|)) := by
  have h : Summable fun n : ℕ ↦ rexp (n * -ε) := Real.summable_exp_nat_mul_iff.mpr (by linarith)
  refine Summable.of_nat_of_neg (h.congr fun n ↦ ?_) (h.congr fun n ↦ ?_)
  · rw [Int.cast_natCast, Nat.abs_cast]
    congr 1
    ring1
  · rw [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]
    congr 1
    ring1

variable (B) in
private lemma pow_le_mul_rexp {x : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) :
    (1 + x) ^ B ≤ B.factorial / ε ^ B * rexp (ε * (1 + x)) := by
  have h : (ε * (1 + x)) ^ B / B.factorial ≤ rexp (ε * (1 + x)) :=
    Real.pow_div_factorial_le_exp _ (by positivity) B
  rw [div_le_iff₀ (by positivity), mul_pow] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

private lemma summable_of_norm_maassCoeff_le (hφ : φ ∈ jacobiFormSpace k 1) (hC : 0 ≤ C)
    (ha : ∀ p : ℤ × ℤ × ℤ, 0 ≤ p.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 ^ 2 ≤ 4 * p.1 * p.2.2 →
      ‖maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2‖ ≤ C * (1 + (p.1 + p.2.2 : ℝ)) ^ B) :
    Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Ω := by
  have hε : 0 < decay Ω := decay_pos Ω
  have hc : 0 < π * decay Ω / 2 := by positivity
  have hg : Summable fun p : ℤ × ℤ × ℤ ↦ rexp (-(π * decay Ω / 2 * |(p.1 : ℝ)|)) *
      (rexp (-(π * decay Ω / 2 * |(p.2.1 : ℝ)|)) *
        rexp (-(π * decay Ω / 2 * |(p.2.2 : ℝ)|))) :=
    (summable_rexp_neg_mul_abs hc).mul_of_nonneg ((summable_rexp_neg_mul_abs hc).mul_of_nonneg
      (summable_rexp_neg_mul_abs hc) (fun _ ↦ (Real.exp_pos _).le)
        fun _ ↦ (Real.exp_pos _).le) (fun _ ↦ (Real.exp_pos _).le) fun _ ↦ by positivity
  refine Summable.of_norm_bounded (hg.mul_left (C * (B.factorial / (π * decay Ω) ^ B) *
    rexp (π * decay Ω))) fun p ↦ ?_
  by_cases hp : 0 ≤ p.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 ^ 2 ≤ 4 * p.1 * p.2.2
  · have hn : (0 : ℝ) ≤ p.1 := by exact_mod_cast hp.1
    have hm : (0 : ℝ) ≤ p.2.2 := by exact_mod_cast hp.2.1
    have hr : |(p.2.1 : ℝ)| ≤ p.1 + p.2.2 := abs_le_add_of_posSemidef p hp
    have hexp : ‖liftExp 1 p.1 p.2.1 p.2.2 Ω‖ ≤ rexp (-(2 * π * (decay Ω * (p.1 + p.2.2)))) := by
      have h : decay Ω * (p.1 + p.2.2) ≤
          p.1 * (Ω.val 0 0).im + p.2.1 * (Ω.val 0 1).im + p.2.2 * (Ω.val 1 1).im :=
        decay_mul_add_le p Ω hp
      rw [liftExp, Complex.norm_exp, Real.exp_le_exp]
      simp only [Nat.cast_one, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat,
        im_ofNat, add_im, intCast_re, intCast_im, one_re, one_im]
      nlinarith [Real.pi_pos]
    have hpow : (1 + (p.1 + p.2.2 : ℝ)) ^ B ≤ B.factorial / (π * decay Ω) ^ B *
        rexp (π * decay Ω * (1 + (p.1 + p.2.2))) :=
      pow_le_mul_rexp B (by positivity) (by positivity)
    have hsplit : rexp (π * decay Ω * (1 + (p.1 + p.2.2))) *
        rexp (-(2 * π * (decay Ω * (p.1 + p.2.2)))) ≤ rexp (π * decay Ω) *
          (rexp (-(π * decay Ω / 2 * |(p.1 : ℝ)|)) *
            (rexp (-(π * decay Ω / 2 * |(p.2.1 : ℝ)|)) *
              rexp (-(π * decay Ω / 2 * |(p.2.2 : ℝ)|)))) := by
      simp only [← Real.exp_add, Real.exp_le_exp]
      rw [abs_of_nonneg hn, abs_of_nonneg hm]
      nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ π * decay Ω)]
    rw [norm_mul]
    refine ((mul_le_mul (ha p hp) hexp (norm_nonneg _) (by positivity)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC)
        (Real.exp_pos _).le)).trans ?_
    have h2 : C * (B.factorial / (π * decay Ω) ^ B *
        rexp (π * decay Ω * (1 + (p.1 + p.2.2)))) *
          rexp (-(2 * π * (decay Ω * (p.1 + p.2.2)))) =
        C * (B.factorial / (π * decay Ω) ^ B) * (rexp (π * decay Ω * (1 + (p.1 + p.2.2))) *
          rexp (-(2 * π * (decay Ω * (p.1 + p.2.2))))) := by
      ring1
    rw [h2]
    refine (mul_le_mul_of_nonneg_left hsplit (by positivity)).trans (le_of_eq ?_)
    ring1
  · rw [maassCoeff_eq_zero_of_not_posSemidef _ _ _ hφ hp, zero_mul, norm_zero]
    positivity

private lemma norm_maassCoeff_le (hk : 1 ≤ k) (hC : 0 ≤ C)
    (hc : ∀ n r : ℤ, ‖jacobiCoeff φ (n, r)‖ ≤ C * (1 + |(n : ℝ)|) ^ A)
    (hp : 0 ≤ p.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 ^ 2 ≤ 4 * p.1 * p.2.2) :
    ‖maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2‖ ≤ (‖maassCoeff k (jacobiCoeff φ) 0 0 0‖ + C) *
      (1 + (p.1 + p.2.2 : ℝ)) ^ ((k - 1).toNat + 1 + 2 * A) := by
  have hn : (0 : ℝ) ≤ p.1 := by exact_mod_cast hp.1
  have hm : (0 : ℝ) ≤ p.2.2 := by exact_mod_cast hp.2.1
  have h1 : (1 : ℝ) ≤ (1 + (p.1 + p.2.2 : ℝ)) ^ ((k - 1).toNat + 1 + 2 * A) :=
    one_le_pow₀ (by linarith)
  by_cases h0 : p.1 = 0 ∧ p.2.1 = 0 ∧ p.2.2 = 0
  · rw [h0.1, h0.2.1, h0.2.2, Int.cast_zero, add_zero, add_zero, one_pow, mul_one]
    linarith
  rw [maassCoeff, ite_eq_right h0, ite_eq_left ⟨hp.1, hp.2.1⟩, liftDivisorSum]
  have hnm : 0 < p.1 + p.2.2 := by
    by_contra h
    have hr : p.2.1 ^ 2 ≤ 0 := by nlinarith [hp.2.2]
    exact h0 ⟨by omega, pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (le_antisymm hr (sq_nonneg _)),
      by omega⟩
  have hg : (((p.1.gcd p.2.1 : ℤ).gcd p.2.2 : ℕ) : ℤ) ≤ p.1 + p.2.2 :=
    Int.le_of_dvd hnm <| dvd_add ((Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _))
      (Int.gcd_dvd_right _ _)
  have hg' : (((p.1.gcd p.2.1 : ℤ).gcd p.2.2 : ℕ) : ℝ) ≤ p.1 + p.2.2 := by exact_mod_cast hg
  have hterm (d : ℕ) (hd : d ∈ ((p.1.gcd p.2.1 : ℤ).gcd p.2.2).divisors) :
      ‖(d : ℂ) ^ (k - 1) * jacobiCoeff φ (p.1 * p.2.2 / (d : ℤ) ^ 2, p.2.1 / d)‖ ≤
        C * (1 + (p.1 + p.2.2 : ℝ)) ^ ((k - 1).toNat + 2 * A) := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hdg : (d : ℝ) ≤ p.1 + p.2.2 :=
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
  have hcard : (((p.1.gcd p.2.1 : ℤ).gcd p.2.2).divisors.card : ℝ) ≤ 1 + (p.1 + p.2.2 : ℝ) :=
    (Nat.cast_le.mpr (Nat.card_divisors_le_self _)).trans (by linarith)
  have hpow : (1 + (p.1 + p.2.2 : ℝ)) ^ ((k - 1).toNat + 1 + 2 * A) =
      (1 + (p.1 + p.2.2 : ℝ)) * (1 + (p.1 + p.2.2 : ℝ)) ^ ((k - 1).toNat + 2 * A) := by
    ring1
  rw [hpow]
  nlinarith [mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤
    C * (1 + (p.1 + p.2.2 : ℝ)) ^ ((k - 1).toNat + 2 * A)),
    norm_nonneg (maassCoeff k (jacobiCoeff φ) 0 0 0),
    pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + (p.1 + p.2.2 : ℝ)) ((k - 1).toNat + 2 * A)]

/-- **The theorem of Maass, reduced to the convergence of the series** (LMFDB
`mf.siegel.lift.maass`): for a Jacobi form `φ ∈ J_{k,1}` of weight `k ≥ 3`, if the series of the
Maass lift converges absolutely at every point of `ℋ₂`, then the Maass lift is a Siegel modular
form of weight `k` on `Sp(4, ℤ)`: it is then holomorphic (`isHolomorphic_maassLift`). -/
lemma maassLift_mem_scalarModularForms_of_forall_summable (hφ : φ ∈ jacobiFormSpace k 1)
    (hk : 3 ≤ k) (hs : ∀ Z : SiegelUpperHalfSpace (Fin 2), Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z) :
    maassLift k φ ∈ scalarModularForms k (integral (Fin 2)) := by
  lift k to ℕ using by omega
  exact maassLift_mem_scalarModularForms_of_summable_of_isHolomorphic hφ (by exact_mod_cast hk) hs
    (isHolomorphic_maassLift hφ hs)

/-- **The series of the Maass lift converges absolutely** on `ℋ₂` if the Fourier coefficients of
the Jacobi form `φ ∈ J_{k,1}`, `k ≥ 1`, grow polynomially: `‖c(n, r)‖ ≤ C (1 + |n|)^A` (as follows
from a bound `C (1 + 4n - r²)^A` on the support `4n ≥ r²`). Then
`|a(n, r, m)| ≤ C' (1 + n + m)^{k + 2A}` on the positive semidefinite `(n, r/2; r/2, m)`, which
carry the coefficients, while `|e^{2πi(nτ + rz + mω)}| ≤ e^{-2πε(n + m)}` with
`ε = det(Im Z) / tr(Im Z)` and `|r| ≤ n + m`. -/
lemma summable_maassLift_of_norm_jacobiCoeff_le (hφ : φ ∈ jacobiFormSpace k 1) (hk : 1 ≤ k)
    (hc : ∀ n r : ℤ, ‖jacobiCoeff φ (n, r)‖ ≤ C * (1 + |(n : ℝ)|) ^ A) :
    Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Ω := by
  have hC : 0 ≤ C := by
    simpa using (norm_nonneg _).trans (hc 0 0)
  exact summable_of_norm_maassCoeff_le Ω hφ (by positivity) fun p hp ↦
    norm_maassCoeff_le p hk hC hc hp

/-- **The theorem of Maass, reduced to a polynomial bound for the Fourier coefficients of `φ`**
(LMFDB `mf.siegel.lift.maass`): for a Jacobi form `φ ∈ J_{k,1}` of weight `k ≥ 3` whose Fourier
coefficients satisfy `‖c(n, r)‖ ≤ C (1 + |n|)^A`, the Maass lift is a Siegel modular form of weight
`k` on `Sp(4, ℤ)`. Every Jacobi form satisfies such a bound
(`ModularForm.norm_jacobiCoeff_le_of_mem_jacobiFormSpace_one`), so this gives the
`mem_modularForms` part of `MaassLiftTheorem` for `k ≥ 3`. -/
lemma maassLift_mem_scalarModularForms_of_norm_jacobiCoeff_le (hφ : φ ∈ jacobiFormSpace k 1)
    (hk : 3 ≤ k) (hc : ∀ n r : ℤ, ‖jacobiCoeff φ (n, r)‖ ≤ C * (1 + |(n : ℝ)|) ^ A) :
    maassLift k φ ∈ scalarModularForms k (integral (Fin 2)) :=
  maassLift_mem_scalarModularForms_of_forall_summable hφ hk fun Z ↦
    summable_maassLift_of_norm_jacobiCoeff_le Z hφ (by omega) hc

end SiegelUpperHalfSpace
