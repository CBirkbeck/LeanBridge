import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.GritsenkoLiftModularity
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.InvariantMeasure

/-!
# Gritsenko's theorem

The Gritsenko lift `F = Grit(φ)` (`SiegelUpperHalfSpace.gritsenkoLift`, LMFDB
`mf.siegel.lift.gritsenko`) of a Jacobi cusp form `φ ∈ J_{k,N}^cusp`, `N ≥ 1`, is a paramodular cusp
form: `F ∈ S_k(K(N))`. The paramodular group has many cusps in general, and the argument here does
not classify them. It rests on a bound for `F` in the invariant norm. The function
`|φ(τ, z)| v^{k/2} e^{-2πN y²/v}` is bounded for a cusp form
(`ModularForm.exists_jacobiNorm_mul_sqrt_zpow_le`), `τ = u + iv`, `z = x + iy`, and the Hecke sum
`φ ∣ V_m` then satisfies
`|(φ ∣ V_m)(τ, z)| v^{k/2} ≤ C m³ m^{k/2} e^{2πNm y²/v}`. In the Fourier–Jacobi expansion
`F(Z) = ∑_{m ≥ 1} (φ ∣ V_m)(τ, z) e^{2πiNmω}`, `ω = u' + it`, this gives
`|F(Z)| det(Y)^{k/2} ≤ C' D^{k/2} ∑_m m³ m^{k/2} e^{-2πNmD}` with `D = t - y²/v = det(Y)/v`, which
is bounded on `D ≥ D₀`, for every `D₀ > 0`.

Now take `γ ∈ Sp(4, ℚ)`. As `F` is invariant under `K(N)`, the embedding of `SL(2, ℤ)` on the second
coordinate lets us assume that the entry `(4, 2)` of `γ` vanishes
(`SiegelUpperHalfSpace.exists_mem_paramodularLevel_mul_apply_eq_zero`). For `W = γ diag(τ', it)` the
quantity `D(W)` is then bounded below as `t → ∞`, from `Im(γZ) = (CZ + D)⁻ᴴ Y (CZ + D)⁻¹`, so that
`|(F ∣ γ)(diag(τ', it))| = |F(W)| det(Im W)^{k/2} (v' t)^{-k/2}` tends to `0` when `k ≥ 1`. For
`k ≤ 0`, `J_{k,N} = 0`.

## Main results

* `SiegelUpperHalfSpace.exists_norm_gritsenkoLift_mul_sqrt_pow_le`: the bound for the Gritsenko lift
  in the invariant norm on `D ≥ D₀`.
* `SiegelUpperHalfSpace.isCuspForm_gritsenkoLift`: the Gritsenko lift of a Jacobi cusp form is a
  cusp form.
* `SiegelUpperHalfSpace.gritsenkoLift_mem_cuspForms`: `Grit(φ) ∈ S_k(K(N))`.
* `SiegelUpperHalfSpace.gritsenkoLiftTheorem`: Gritsenko's theorem.
* `SiegelUpperHalfSpace.eq_zero_of_hasSum_mul_liftExp`: the coefficients of the series of the lift
  are determined by its sum.
* `SiegelUpperHalfSpace.gritsenkoFourierJacobi_one`: the first Fourier–Jacobi coefficient of
  `Grit(φ)` is `φ`.
* `SiegelUpperHalfSpace.gritsenkoLift_ne_zero`: `Grit(φ) ≠ 0` for `φ ≠ 0`.
-/

open Complex Filter Matrix ModularForm Module Real SymplecticGroup Topology UnitAddTorus

open scoped MatrixGroups UpperHalfPlane

namespace SiegelUpperHalfSpace

variable {K N m : ℕ} {φ : ℍ × ℂ → ℂ} {C : ℝ} (x : ℍ × ℂ) (t : ℕ × ℕ × ℕ)

private lemma card_cosetReps_le (hm : 0 < m) : ((cosetReps m).card : ℝ) ≤ 8 * m ^ 3 := by
  have h : (cosetReps m).card ≤ (m + 1) * ((m + 1) * (m + 1)) := by
    refine (Finset.card_filter_le _ _).trans ?_
    simp
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h' : ((cosetReps m).card : ℝ) ≤ ((m : ℝ) + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 1)) := by
    exact_mod_cast h
  refine h'.trans ?_
  have h₂ : (m : ℝ) + 1 ≤ 2 * m := by linarith
  have h₃ : ((m : ℝ) + 1) * ((m : ℝ) + 1) ≤ 2 * m * (2 * m) :=
    mul_le_mul h₂ h₂ (by positivity) (by positivity)
  have h₄ : ((m : ℝ) + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 1)) ≤ 2 * m * (2 * m * (2 * m)) :=
    mul_le_mul h₂ h₃ (by positivity) (by positivity)
  nlinarith

private lemma norm_cosetTerm_mul_le (hφ : ∀ (τ : ℍ) (z : ℂ), jacobiNorm N φ (τ, z) * √τ.im ^ K ≤ C)
    (hm : 0 < m) (ht : t ∈ cosetReps m) : ‖cosetTerm (K : ℤ) φ t x‖ * √x.1.im ^ K ≤ √(m : ℝ) ^ K *
    C * rexp (2 * π * N * m * x.2.im ^ 2 / x.1.im) := by
  rw [mem_cosetReps hm] at ht
  rcases ht with ⟨hmt, hbd⟩
  have ha : 0 < t.1 := Nat.pos_of_ne_zero fun h ↦ hm.ne <| by rw [← hmt, h, zero_mul]
  have hd : 0 < t.2.2 := Nat.pos_of_ne_zero fun h ↦ hm.ne <| by rw [← hmt, h, mul_zero]
  have ha' : (0 : ℝ) < t.1 := by exact_mod_cast ha
  have hd' : (0 : ℝ) < t.2.2 := by exact_mod_cast hd
  have hv : 0 < x.1.im := x.1.im_pos
  have hm' : (m : ℝ) = t.1 * t.2.2 := by exact_mod_cast hmt.symm
  have him : (affinePoint t.1 t.2.1 t.2.2 x.1).im = t.1 * x.1.im / t.2.2 := by
    have h : ((affinePoint t.1 t.2.1 t.2.2 x.1 : ℍ) : ℂ) = (t.1 * x.1 + t.2.1) / t.2.2 := by
      simpa using coe_affinePoint (t.2.1 : ℤ) x.1 (p := t.1) (s := t.2.2) (by exact_mod_cast ha)
        (by exact_mod_cast hd)
    rw [← UpperHalfPlane.coe_im, h]
    simp
  have hzim : ((t.1 : ℂ) * x.2).im = t.1 * x.2.im := by
    simp
  have hC : jacobiNorm N φ (affinePoint t.1 t.2.1 t.2.2 x.1, t.1 * x.2) *
      √(affinePoint t.1 t.2.1 t.2.2 x.1).im ^ K ≤ C :=
    hφ (affinePoint t.1 t.2.1 t.2.2 x.1) (t.1 * x.2)
  rw [jacobiNorm] at hC
  dsimp only at hC
  rw [him, hzim] at hC
  have hexp : 2 * π * N * (t.1 * x.2.im) ^ 2 / (t.1 * x.1.im / t.2.2) =
      2 * π * N * m * x.2.im ^ 2 / x.1.im := by
    rw [hm']
    field_simp
  rw [hexp] at hC
  have hsqrt : (t.1 : ℝ) * √x.1.im = √(m : ℝ) * √(t.1 * x.1.im / t.2.2) := by
    rw [← Real.sqrt_mul (by positivity), hm']
    have h : (t.1 : ℝ) * t.2.2 * (t.1 * x.1.im / t.2.2) = (t.1 : ℝ) ^ 2 * x.1.im := by
      field_simp
    rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq ha'.le]
  have hE : 0 < rexp (2 * π * N * m * x.2.im ^ 2 / x.1.im) := Real.exp_pos _
  have hEE : rexp (-(2 * π * N * m * x.2.im ^ 2 / x.1.im)) *
      rexp (2 * π * N * m * x.2.im ^ 2 / x.1.im) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [cosetTerm, norm_mul, norm_zpow, Complex.norm_natCast, zpow_natCast, mul_right_comm, ← mul_pow,
    hsqrt, mul_pow]
  have hkey : ‖φ (affinePoint t.1 t.2.1 t.2.2 x.1, t.1 * x.2)‖ * √(t.1 * x.1.im / t.2.2) ^ K ≤
      C * rexp (2 * π * N * m * x.2.im ^ 2 / x.1.im) := by
    have h₁ : _ * rexp (2 * π * N * m * x.2.im ^ 2 / x.1.im) ≤
        C * rexp (2 * π * N * m * x.2.im ^ 2 / x.1.im) :=
      mul_le_mul_of_nonneg_right hC hE.le
    have h₂ : ‖φ (affinePoint t.1 t.2.1 t.2.2 x.1, t.1 * x.2)‖ *
        rexp (-(2 * π * N * m * x.2.im ^ 2 / x.1.im)) * √(t.1 * x.1.im / t.2.2) ^ K *
          rexp (2 * π * N * m * x.2.im ^ 2 / x.1.im) =
        ‖φ (affinePoint t.1 t.2.1 t.2.2 x.1, t.1 * x.2)‖ * √(t.1 * x.1.im / t.2.2) ^ K := by
      linear_combination (‖φ (affinePoint t.1 t.2.1 t.2.2 x.1, t.1 * x.2)‖ *
        √(t.1 * x.1.im / t.2.2) ^ K) * hEE
    rwa [h₂] at h₁
  have e : √(m : ℝ) ^ K * √(t.1 * x.1.im / t.2.2) ^ K *
      ‖φ (affinePoint t.1 t.2.1 t.2.2 x.1, t.1 * x.2)‖ = √(m : ℝ) ^ K *
        (‖φ (affinePoint t.1 t.2.1 t.2.2 x.1, t.1 * x.2)‖ * √(t.1 * x.1.im / t.2.2) ^ K) := by
    ring1
  rw [e, mul_assoc]
  exact mul_le_mul_of_nonneg_left hkey (pow_nonneg (Real.sqrt_nonneg _) K)

private lemma norm_indexRaising_mul_le
    (hφ : ∀ (τ : ℍ) (z : ℂ), jacobiNorm N φ (τ, z) * √τ.im ^ K ≤ C) (hm : 0 < m) :
    ‖indexRaising (K : ℤ) φ m x‖ * √x.1.im ^ K ≤ 8 * m ^ 3 *
      (√(m : ℝ) ^ K * C * rexp (2 * π * N * m * x.2.im ^ 2 / x.1.im)) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs : 0 ≤ √x.1.im ^ K := pow_nonneg (Real.sqrt_nonneg _) K
  have hC : 0 ≤ C := (mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))
    (pow_nonneg (Real.sqrt_nonneg _) K)).trans (hφ x.1 x.2)
  have hsum : ‖∑ t ∈ cosetReps m, cosetTerm (K : ℤ) φ t x‖ * √x.1.im ^ K ≤
      (cosetReps m).card * (√(m : ℝ) ^ K * C * rexp (2 * π * N * m * x.2.im ^ 2 / x.1.im)) := by
    refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) hs).trans ?_
    rw [Finset.sum_mul, ← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun t ht ↦ norm_cosetTerm_mul_le x t hφ hm ht
  rw [indexRaising, norm_mul, norm_inv, Complex.norm_natCast, mul_assoc]
  refine (mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hm')).trans (hsum.trans ?_)
  exact mul_le_mul_of_nonneg_right (card_cosetReps_le hm) (by positivity)

variable (K) in
private lemma sqrt_pow_mul_rexp_le {ε y : ℝ} (hε : 0 < ε) (hy : 0 ≤ y) :
    √y ^ K * rexp (-(2 * ε * y)) ≤ K.factorial / ε ^ K * rexp ε * rexp (-(ε * y)) := by
  have h₁ : √y ^ K ≤ (1 + y) ^ K :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (by
      nlinarith [Real.sq_sqrt hy, Real.sqrt_nonneg y, sq_nonneg (√y - 1)]) K
  have h₂ : (1 + y) ^ K ≤ K.factorial / ε ^ K * rexp (ε * (1 + y)) :=
    one_add_pow_le_mul_rexp K hε hy
  have h₃ : rexp (ε * (1 + y)) * rexp (-(2 * ε * y)) = rexp ε * rexp (-(ε * y)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring1
  refine (mul_le_mul_of_nonneg_right (h₁.trans h₂) (Real.exp_nonneg _)).trans (le_of_eq ?_)
  rw [mul_assoc, h₃, mul_assoc]

variable (Z : SiegelUpperHalfSpace (Fin 2))

private lemma det_im_eq :
    (Z.val.map im).det = (Z.val 0 0).im * (Z.val 1 1).im - (Z.val 0 1).im ^ 2 := by
  have h : Z.val 1 0 = Z.val 0 1 := congrFun (congrFun Z.transpose_val 0) 1
  rw [det_fin_two]
  simp [h, sq]

private lemma norm_gritsenkoFourierJacobi_mul_le (hφ : φ ∈ jacobiFormSpace (K : ℤ) N)
    (hC : ∀ (τ : ℍ) (z : ℂ), jacobiNorm N φ (τ, z) * √τ.im ^ K ≤ C) (hm : 0 < m) :
    ‖gritsenkoFourierJacobi (K : ℤ) φ (toJacobiPoint Z) m *
      cexp (2 * π * I * (N * m) * Z.val 1 1)‖ * √(Z.val.map im).det ^ K ≤
        8 * m ^ 3 * (C * (√((m : ℝ) * ((Z.val.map im).det / (Z.val 0 0).im)) ^ K *
          rexp (-(2 * (π * N) * ((m : ℝ) * ((Z.val.map im).det / (Z.val 0 0).im)))))) := by
  have hv : 0 < (Z.val 0 0).im := im_zero_zero_pos Z
  have hdet : 0 < (Z.val.map im).det := Z.posDef_im.det_pos
  have hD : 0 < (Z.val.map im).det / (Z.val 0 0).im := div_pos hdet hv
  have hx₁ : (toJacobiPoint Z).1.im = (Z.val 0 0).im := rfl
  have hx₂ : (toJacobiPoint Z).2.im = (Z.val 0 1).im := rfl
  have hI : ‖indexRaising (K : ℤ) φ m (toJacobiPoint Z)‖ * √(toJacobiPoint Z).1.im ^ K ≤
      8 * m ^ 3 * (√(m : ℝ) ^ K * C *
        rexp (2 * π * N * m * (toJacobiPoint Z).2.im ^ 2 / (toJacobiPoint Z).1.im)) :=
    norm_indexRaising_mul_le (toJacobiPoint Z) hC hm
  rw [hx₁, hx₂] at hI
  have hsqrt : √(Z.val.map im).det = √(Z.val 0 0).im * √((Z.val.map im).det / (Z.val 0 0).im) := by
    rw [← Real.sqrt_mul hv.le, mul_div_cancel₀ _ hv.ne']
  have hexp :
      ‖cexp (2 * π * I * (N * m) * Z.val 1 1)‖ = rexp (-(2 * π * N * m * (Z.val 1 1).im)) := by
    rw [Complex.norm_exp]
    congr 1
    have h : 2 * π * I * (N * m) * Z.val 1 1 = ((2 * π * N * m : ℝ) : ℂ) * (I * Z.val 1 1) := by
      push_cast
      ring1
    rw [h, re_ofReal_mul, I_mul_re]
    ring1
  rw [gritsenkoFourierJacobi_eq_indexRaising _ hφ hm, norm_mul, hexp, hsqrt, mul_pow,
    Real.sqrt_mul (Nat.cast_nonneg m), mul_pow]
  have hD' : (Z.val 1 1).im - (Z.val 0 1).im ^ 2 / (Z.val 0 0).im =
      (Z.val.map im).det / (Z.val 0 0).im := by
    rw [det_im_eq]
    field_simp
  have he : rexp (2 * π * N * m * (Z.val 0 1).im ^ 2 / (Z.val 0 0).im) *
      rexp (-(2 * π * N * m * (Z.val 1 1).im)) =
        rexp (-(2 * (π * N) * ((m : ℝ) * ((Z.val.map im).det / (Z.val 0 0).im)))) := by
    rw [← Real.exp_add, ← hD']
    congr 1
    field_simp
    ring1
  have hE : _ * (rexp (-(2 * π * N * m * (Z.val 1 1).im)) *
      √((Z.val.map im).det / (Z.val 0 0).im) ^ K) ≤ _ * (rexp (-(2 * π * N * m * (Z.val 1 1).im)) *
        √((Z.val.map im).det / (Z.val 0 0).im) ^ K) :=
    mul_le_mul_of_nonneg_right hI (mul_nonneg (Real.exp_nonneg _)
      (pow_nonneg (Real.sqrt_nonneg _) K))
  refine (le_of_eq ?_).trans (hE.trans (le_of_eq ?_))
  · ring1
  · rw [← he]
    ring1

private lemma term_mul_le (hφ : φ ∈ jacobiFormSpace (K : ℤ) N) (hN : 0 < N)
    (hC : ∀ (τ : ℍ) (z : ℂ), jacobiNorm N φ (τ, z) * √τ.im ^ K ≤ C) (hC₀ : 0 ≤ C) {D₀ : ℝ}
    (hZ : D₀ ≤ (Z.val.map im).det / (Z.val 0 0).im) (n : ℕ) :
    ‖gritsenkoFourierJacobi (K : ℤ) φ (toJacobiPoint Z) n *
      cexp (2 * π * I * (N * n) * Z.val 1 1)‖ * √(Z.val.map im).det ^ K ≤
        8 * (C * (K.factorial / (π * N) ^ K * rexp (π * N))) *
          ((n : ℝ) ^ 3 * rexp (-(π * N * D₀)) ^ n) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hε : 0 < π * N := by positivity
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : gritsenkoFourierJacobi (K : ℤ) φ (toJacobiPoint Z) ((0 : ℕ) : ℤ) = 0 :=
      gritsenkoFourierJacobi_of_nonpos _ _ (by simp)
    rw [h0]
    simp
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hD : 0 < (Z.val.map im).det / (Z.val 0 0).im :=
    div_pos Z.posDef_im.det_pos (im_zero_zero_pos Z)
  refine (norm_gritsenkoFourierJacobi_mul_le Z hφ hC hn).trans ?_
  generalize (Z.val.map im).det / (Z.val 0 0).im = D at hZ hD
  have h₁ : √((n : ℝ) * D) ^ K * rexp (-(2 * (π * N) * ((n : ℝ) * D))) ≤
      K.factorial / (π * N) ^ K * rexp (π * N) * rexp (-(π * N * ((n : ℝ) * D))) :=
    sqrt_pow_mul_rexp_le K hε (mul_pos hn' hD).le
  have h₂ : rexp (-(π * N * ((n : ℝ) * D))) ≤ rexp (-(π * N * D₀)) ^ n := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    have h₃ : π * N * n * D₀ ≤ π * N * n * D :=
      mul_le_mul_of_nonneg_left hZ (mul_pos hε hn').le
    linarith
  have h₃ : √((n : ℝ) * D) ^ K * rexp (-(2 * (π * N) * ((n : ℝ) * D))) ≤
      K.factorial / (π * N) ^ K * rexp (π * N) * rexp (-(π * N * D₀)) ^ n :=
    h₁.trans (mul_le_mul_of_nonneg_left h₂ (by positivity))
  have h₄ : 8 * (n : ℝ) ^ 3 * C * (√((n : ℝ) * D) ^ K * rexp (-(2 * (π * N) * ((n : ℝ) * D)))) ≤
      8 * (n : ℝ) ^ 3 * C * (K.factorial / (π * N) ^ K * rexp (π * N) * rexp (-(π * N * D₀)) ^ n) :=
    mul_le_mul_of_nonneg_left h₃ (by positivity)
  refine (le_of_eq ?_).trans (h₄.trans (le_of_eq ?_)) <;> ring1

private lemma gritsenkoLift_eq_tsum_nat (hN : 0 < N) (hφ : φ ∈ jacobiCuspFormSpace (K : ℤ) N) :
    gritsenkoLift (K : ℤ) N φ Z = ∑' n : ℕ, gritsenkoFourierJacobi (K : ℤ) φ (toJacobiPoint Z) n *
      cexp (2 * π * I * (N * n) * Z.val 1 1) := by
  rw [gritsenkoLift_eq_tsum_fourierJacobi _ (summable_gritsenkoLift Z hN hφ)]
  have h : Function.support (fun l : ℤ ↦ gritsenkoFourierJacobi (K : ℤ) φ (toJacobiPoint Z) l *
      cexp (2 * π * I * (N * l) * Z.val 1 1)) ⊆ Set.range ((↑) : ℕ → ℤ) := fun l hl ↦ by
    rcases le_or_gt l 0 with h | h
    · refine absurd ?_ hl
      beta_reduce
      rw [gritsenkoFourierJacobi_of_nonpos _ _ h, zero_mul]
    · exact ⟨l.toNat, Int.toNat_of_nonneg h.le⟩
  exact (Nat.cast_injective.tsum_eq h).symm.trans <| tsum_congr fun n ↦ by
    simp only [Int.cast_natCast]

variable (N K) in
/-- **The Gritsenko lift is bounded in the invariant norm away from the boundary**: for
`φ ∈ J_{K,N}^cusp`, `N ≥ 1`, and `D₀ > 0`, there is a constant `A` with `|F(Z)| det(Y)^{K/2} ≤ A`
for all `Z = (τ, z; z, ω)` with `D = det(Y)/Im τ ≥ D₀`. In the Fourier–Jacobi expansion,
`|(φ ∣ V_m)(τ, z) e^{2πiNmω}| det(Y)^{K/2} ≤ C m³ (mD)^{K/2} e^{-2πNmD}`, summable in `m`
uniformly on `D ≥ D₀`. -/
lemma exists_norm_gritsenkoLift_mul_sqrt_pow_le (hN : 0 < N)
    (hφ : φ ∈ jacobiCuspFormSpace (K : ℤ) N) {D₀ : ℝ} (hD₀ : 0 < D₀) : ∃ A,
    ∀ Z : SiegelUpperHalfSpace (Fin 2), D₀ ≤ (Z.val.map im).det / (Z.val 0 0).im →
      ‖gritsenkoLift (K : ℤ) N φ Z‖ * √(Z.val.map im).det ^ K ≤ A := by
  rcases exists_jacobiNorm_mul_sqrt_zpow_le hN hφ with ⟨C, hC'⟩
  have hC (τ : ℍ) (z : ℂ) : jacobiNorm N φ (τ, z) * √τ.im ^ K ≤ C := by
    simpa using hC' τ z
  have hC₀ : 0 ≤ C := (mul_nonneg (mul_nonneg (norm_nonneg (φ (UpperHalfPlane.I, 0)))
    (Real.exp_nonneg _)) (pow_nonneg (Real.sqrt_nonneg _) K)).trans (hC UpperHalfPlane.I 0)
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hε : 0 < π * N := by positivity
  have hr₀ : 0 < rexp (-(π * N * D₀)) := Real.exp_pos _
  have hr₁ : rexp (-(π * N * D₀)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith [mul_pos hε hD₀]
  have hg₀ : Summable fun n : ℕ ↦ (n : ℝ) ^ 3 * rexp (-(π * N * D₀)) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 3 (by rwa [Real.norm_of_nonneg hr₀.le])
  have hg : Summable fun n : ℕ ↦ 8 * (C * (K.factorial / (π * N) ^ K * rexp (π * N))) *
      ((n : ℝ) ^ 3 * rexp (-(π * N * D₀)) ^ n) :=
    hg₀.mul_left _
  refine ⟨∑' n : ℕ, 8 * (C * (K.factorial / (π * N) ^ K * rexp (π * N))) *
    ((n : ℝ) ^ 3 * rexp (-(π * N * D₀)) ^ n), fun Z hZ ↦ ?_⟩
  have hdet : 0 < (Z.val.map im).det := Z.posDef_im.det_pos
  have hs : 0 < √(Z.val.map im).det ^ K := pow_pos (Real.sqrt_pos.mpr hdet) K
  have hF : gritsenkoLift (K : ℤ) N φ Z = ∑' n : ℕ,
      gritsenkoFourierJacobi (K : ℤ) φ (toJacobiPoint Z) n *
        cexp (2 * π * I * (N * n) * Z.val 1 1) :=
    gritsenkoLift_eq_tsum_nat Z hN hφ
  have hterm (n : ℕ) : ‖gritsenkoFourierJacobi (K : ℤ) φ (toJacobiPoint Z) n *
      cexp (2 * π * I * (N * n) * Z.val 1 1)‖ ≤
        8 * (C * (K.factorial / (π * N) ^ K * rexp (π * N))) *
          ((n : ℝ) ^ 3 * rexp (-(π * N * D₀)) ^ n) / √(Z.val.map im).det ^ K :=
    (le_div_iff₀ hs).mpr (term_mul_le Z hφ.1 hN hC hC₀ hZ n)
  have hbound : ‖gritsenkoLift (K : ℤ) N φ Z‖ ≤
      (∑' n : ℕ, 8 * (C * (K.factorial / (π * N) ^ K * rexp (π * N))) *
        ((n : ℝ) ^ 3 * rexp (-(π * N * D₀)) ^ n)) / √(Z.val.map im).det ^ K := by
    rw [hF]
    exact tsum_of_norm_bounded (hg.hasSum.div_const _) hterm
  exact (le_div_iff₀ hs).mp hbound

variable (g : symplecticGroup (Fin 2) ℝ) (τ' : ℍ) (s : Set.Ioi (0 : ℝ))

private lemma map_im_diagPoint : (diagPoint τ' s).val.map im = !![τ'.im, 0; 0, (s : ℝ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagPoint]

private lemma det_im_diagPoint : ((diagPoint τ' s).val.map im).det = τ'.im * s := by
  rw [map_im_diagPoint, det_fin_two_of]
  ring1

private lemma denom_apply_one_zero :
    denom g (diagPoint τ' s).val 1 0 = g.1 (.inr 1) (.inl 0) * τ' + g.1 (.inr 1) (.inr 0) := by
  simp [denom, diagPoint, Matrix.mul_apply, toBlocks₂₁, toBlocks₂₂]

private lemma denom_apply_one_one :
    denom g (diagPoint τ' s).val 1 1 = g.1 (.inr 1) (.inl 1) * (s * I) + g.1 (.inr 1) (.inr 1) := by
  simp [denom, diagPoint, Matrix.mul_apply, toBlocks₂₁, toBlocks₂₂]

private lemma im_smul_diagPoint_zero_zero : ((g • diagPoint τ' s).val 0 0).im =
    (τ'.im * normSq (denom g (diagPoint τ' s).val 1 1) +
      s * normSq (denom g (diagPoint τ' s).val 1 0)) /
        normSq (denom g (diagPoint τ' s).val).det := by
  have hJ : (denom g (diagPoint τ' s).val).det ≠ 0 := (isUnit_det_denom g _).ne_zero
  have h : (((g • diagPoint τ' s).val.map im).map ofReal) 0 0 = _ :=
    congrFun (congrFun (map_im_smul (diagPoint τ' s) g) 0) 0
  rw [map_im_diagPoint] at h
  simp only [map_apply] at h
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two] at h
  simp only [conjTranspose_apply, map_apply, of_apply, cons_val_zero, cons_val_one, ofReal_zero,
    mul_zero, add_zero, zero_add] at h
  rw [Matrix.inv_def, Ring.inverse_eq_inv', adjugate_fin_two] at h
  simp only [Matrix.smul_apply, of_apply, cons_val_zero, cons_val_one, smul_eq_mul] at h
  refine ofReal_injective ?_
  rw [h, ofReal_div, ofReal_add, ofReal_mul, ofReal_mul, normSq_eq_conj_mul_self,
    normSq_eq_conj_mul_self, normSq_eq_conj_mul_self]
  simp only [star_def, map_mul, map_inv₀, map_neg]
  have hJ' : (starRingEnd ℂ) (denom g (diagPoint τ' s).val).det ≠ 0 := by
    simpa using hJ
  field_simp

private lemma det_im_div_im_smul_diagPoint :
    ((g • diagPoint τ' s).val.map im).det / ((g • diagPoint τ' s).val 0 0).im =
      τ'.im * s / (τ'.im * normSq (denom g (diagPoint τ' s).val 1 1) +
        s * normSq (denom g (diagPoint τ' s).val 1 0)) := by
  have hJ : 0 < normSq (denom g (diagPoint τ' s).val).det :=
    normSq_pos.mpr (isUnit_det_denom g _).ne_zero
  rw [det_im_smul, det_im_diagPoint, im_smul_diagPoint_zero_zero]
  field_simp

private lemma exists_le_det_im_div (hg : g.1 (.inr 1) (.inl 1) = 0) : ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ s : Set.Ioi (0 : ℝ), 1 ≤ (s : ℝ) → D₀ ≤
      ((g • diagPoint τ' s).val.map im).det / ((g • diagPoint τ' s).val 0 0).im := by
  have hv : 0 < τ'.im := τ'.im_pos
  have hJ₁ (s : Set.Ioi (0 : ℝ)) : denom g (diagPoint τ' s).val 1 1 = g.1 (.inr 1) (.inr 1) := by
    rw [denom_apply_one_one, hg]
    simp
  have hB₀ : 0 < τ'.im * normSq (g.1 (.inr 1) (.inr 1) : ℂ) +
      normSq (g.1 (.inr 1) (.inl 0) * τ' + g.1 (.inr 1) (.inr 0) : ℂ) := by
    have h : 0 < ((g • diagPoint τ' tOne).val 0 0).im := im_zero_zero_pos _
    rw [im_smul_diagPoint_zero_zero, hJ₁, denom_apply_one_zero] at h
    have hN : 0 < normSq (denom g (diagPoint τ' tOne).val).det :=
      normSq_pos.mpr (isUnit_det_denom g _).ne_zero
    simpa [tOne] using (div_pos_iff_of_pos_right hN).mp h
  refine ⟨τ'.im / (τ'.im * normSq (g.1 (.inr 1) (.inr 1) : ℂ) +
    normSq (g.1 (.inr 1) (.inl 0) * τ' + g.1 (.inr 1) (.inr 0) : ℂ)), by positivity, fun s hs ↦ ?_⟩
  rw [det_im_div_im_smul_diagPoint, hJ₁, denom_apply_one_zero]
  have hA : 0 ≤ normSq (g.1 (.inr 1) (.inl 0) * τ' + g.1 (.inr 1) (.inr 0) : ℂ) := normSq_nonneg _
  have hd : 0 ≤ normSq (g.1 (.inr 1) (.inr 1) : ℂ) := normSq_nonneg _
  have hpos : 0 < τ'.im * normSq (g.1 (.inr 1) (.inr 1) : ℂ) +
      s * normSq (g.1 (.inr 1) (.inl 0) * τ' + g.1 (.inr 1) (.inr 0) : ℂ) := by
    nlinarith [mul_nonneg hv.le hd, mul_le_mul_of_nonneg_right hs hA]
  rw [div_le_div_iff₀ hB₀ hpos]
  nlinarith [mul_nonneg hv.le hd, mul_le_mul_of_nonneg_left hs (mul_nonneg hv.le hd),
    mul_nonneg hv.le hA]

private lemma norm_slash_mul_sqrt_pow (F : SiegelUpperHalfSpace (Fin 2) → ℂ) :
    ‖slash (TauCeti.detPowerRep ℂ 2 (K : ℤ)) g F Z‖ * √(Z.val.map im).det ^ K =
      ‖F (g • Z)‖ * √((g • Z).val.map im).det ^ K := by
  have hJ : 0 < ‖(denom g Z.val).det‖ := norm_pos_iff.mpr (isUnit_det_denom g Z).ne_zero
  have hdet : 0 < (Z.val.map im).det := Z.posDef_im.det_pos
  have hsqrt : √(Z.val.map im).det = √((g • Z).val.map im).det * ‖(denom g Z.val).det‖ := by
    rw [det_im_smul, normSq_eq_norm_sq, Real.sqrt_div hdet.le, Real.sqrt_sq hJ.le,
      div_mul_cancel₀ _ hJ.ne']
  have hy : (denom g Z.val).det ^ (K : ℤ) *
      slash (TauCeti.detPowerRep ℂ 2 (K : ℤ)) g F Z = F (g • Z) := by
    rw [← detPowerRep_denomGL _ g Z, slash_apply, ← End.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, End.one_apply]
  rw [← hy, norm_mul, norm_zpow, zpow_natCast, hsqrt, mul_pow]
  ring1

variable {L : ℕ+}

private lemma tendsto_slash_gritsenkoLift_diagPoint (hK : K ≠ 0)
    (hφ : φ ∈ jacobiCuspFormSpace (K : ℤ) L) (hg : g.1 (.inr 1) (.inl 1) = 0) : Tendsto
    (fun s : Set.Ioi (0 : ℝ) ↦ slash (TauCeti.detPowerRep ℂ 2 (K : ℤ)) g
      (gritsenkoLift (K : ℤ) L φ) (diagPoint τ' s)) atTop (𝓝 0) := by
  rcases exists_le_det_im_div g τ' hg with ⟨D₀, hD₀, hD⟩
  rcases exists_norm_gritsenkoLift_mul_sqrt_pow_le K L L.pos hφ hD₀ with ⟨A, hA⟩
  have ht : Tendsto (fun s : Set.Ioi (0 : ℝ) ↦ (s : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have hv : 0 < τ'.im := τ'.im_pos
  have hlim : Tendsto (fun s : Set.Ioi (0 : ℝ) ↦ A / √(τ'.im * s) ^ K) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop <| (tendsto_pow_atTop hK).comp <|
      Real.tendsto_sqrt_atTop.comp <| ht.const_mul_atTop hv
  refine tendsto_zero_iff_norm_tendsto_zero.mpr <| squeeze_zero' (Eventually.of_forall fun _ ↦
    norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop tOne] with s hs
  have hdet : 0 < τ'.im * s := mul_pos hv s.2
  have h : ‖slash (TauCeti.detPowerRep ℂ 2 (K : ℤ)) g (gritsenkoLift (K : ℤ) L φ)
      (diagPoint τ' s)‖ * √((diagPoint τ' s).val.map im).det ^ K ≤ A :=
    (norm_slash_mul_sqrt_pow (diagPoint τ' s) g (gritsenkoLift (K : ℤ) L φ)).trans_le
      (hA _ (hD s hs))
  rw [det_im_diagPoint] at h
  exact (le_div_iff₀ (pow_pos (Real.sqrt_pos.mpr hdet) K)).mpr h

variable {k : ℤ}

private lemma gritsenkoLift_zero : gritsenkoLift k L (0 : ℍ × ℂ → ℂ) = 0 :=
  funext fun Z ↦ by
    simp [gritsenkoLift, gritsenkoCoeff_jacobiCoeff_zero]

/-- **The Gritsenko lift of a Jacobi cusp form is a cusp form**: for `φ ∈ J_{k,N}^cusp`, `N ≥ 1`,
`Φ(Grit(φ) ∣ γ) = 0` for every `γ ∈ Sp(4, ℚ)`. As `Grit(φ)` is invariant under `K(N)`, one can
assume that the entry `(4, 2)` of `γ` vanishes, and then
`|(F ∣ γ)(diag(τ', it))| = |F(W)| det(Im W)^{k/2} (v' t)^{-k/2} ≤ A (v' t)^{-k/2}` for
`W = γ diag(τ', it)`, `t ≥ 1`, by the bound for `F` in the invariant norm. -/
lemma isCuspForm_gritsenkoLift (hφ : φ ∈ jacobiCuspFormSpace k L) :
    IsCuspForm (TauCeti.detPowerRep ℂ 2 k) (gritsenkoLift k L φ) := by
  rcases le_or_gt k 0 with hk | hk
  · rw [eq_zero_of_mem_jacobiFormSpace_of_nonpos L.pos hφ.1 hk, gritsenkoLift_zero]
    intro γ
    rw [slash_zero]
    exact siegelOperatorVanishes_zero
  lift k to ℕ using hk.le
  have hk' : k ≠ 0 := by
    rintro rfl
    simp at hk
  intro γ τ' ψ
  rcases exists_mem_paramodularLevel_mul_apply_eq_zero L γ with ⟨g, hg, hzero⟩
  have hF : slash (TauCeti.detPowerRep ℂ 2 (k : ℤ)) (map (algebraMap ℚ ℝ) g)
      (gritsenkoLift (k : ℤ) L φ) = gritsenkoLift (k : ℤ) L φ := by
    simpa using ((mem_modularForms_iff_slash _ _ _ _).mp
      (gritsenkoLift_mem_modularForms L hφ)).2 ⟨g, hg⟩
  have he : slash (TauCeti.detPowerRep ℂ 2 (k : ℤ)) (map (algebraMap ℚ ℝ) γ)
      (gritsenkoLift (k : ℤ) L φ) = slash (TauCeti.detPowerRep ℂ 2 (k : ℤ))
        (map (algebraMap ℚ ℝ) (g * γ)) (gritsenkoLift (k : ℤ) L φ) := by
    rw [map_mul, slash_mul, hF]
  have hz : (map (algebraMap ℚ ℝ) (g * γ)).1 (.inr 1) (.inl 1) = 0 := by
    rw [coe_map_apply, Matrix.map_apply, hzero, map_zero]
  rw [he]
  exact (ψ.continuous_of_finiteDimensional.tendsto' 0 0 (map_zero ψ)).comp
    (tendsto_slash_gritsenkoLift_diagPoint _ τ' hk' hφ hz)

/-- **`Grit(φ) ∈ S_k(K(N))`** (LMFDB `mf.siegel.lift.gritsenko`): the Gritsenko lift of a Jacobi
cusp form of weight `k` and index `N ≥ 1` is a paramodular cusp form of weight `k` and level `N`. -/
lemma gritsenkoLift_mem_cuspForms (hφ : φ ∈ jacobiCuspFormSpace k L) :
    gritsenkoLift k L φ ∈ cuspForms (TauCeti.detPowerRep ℂ 2 k) (paramodularLevel L) 1 :=
  ⟨gritsenkoLift_mem_modularForms L hφ, isCuspForm_gritsenkoLift hφ⟩

/-- **Gritsenko's theorem** (LMFDB `mf.siegel.lift.gritsenko`; Gritsenko, *Arithmetical lifting and
its applications*, 1995): for `N ≥ 1` and a Jacobi cusp form `φ ∈ J_{k,N}^cusp`, the series of the
Gritsenko lift converges absolutely on `ℋ₂`, and `Grit(φ)` is a paramodular cusp form of weight `k`
and level `N`: `Grit(φ) ∈ S_k(K(N))`. -/
lemma gritsenkoLiftTheorem : GritsenkoLiftTheorem where
  summable _ N _ hφ Z := summable_gritsenkoLift Z N.pos hφ
  mem_cuspForms _ _ _ hφ := gritsenkoLift_mem_cuspForms hφ

/-! ### The lift is not degenerate -/

variable (L) in
/-- The point `(v₀ + i, v₁; v₁, v₂/N + i)` of `ℋ₂`, for real `v₀, v₁, v₂`. -/
private noncomputable def liftTorusPoint (v : Fin 3 → ℝ) : SiegelUpperHalfSpace (Fin 2) where
  val := !![(v 0 : ℂ) + I, v 1; v 1, (v 2 : ℂ) / L + I]
  transpose_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  posDef_im := by
    have h : (!![(v 0 : ℂ) + I, v 1; v 1, (v 2 : ℂ) / L + I] :
        Matrix (Fin 2) (Fin 2) ℂ).map im = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [h]
    exact PosDef.one

private lemma liftExp_liftTorusPoint (p : Fin 3 → ℤ) (v : Fin 3 → ℝ) :
    liftExp L (p 0) (p 1) (p 2) (liftTorusPoint L v) = cexp (-(2 * π * (p 0 + L * p 2))) *
      mFourier p fun i ↦ (v i : UnitAddCircle) := by
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr L.ne_zero
  rw [mFourier_coe_apply, liftExp, ← Complex.exp_add]
  congr 1
  simp [liftTorusPoint, Fin.sum_univ_three]
  field_simp
  linear_combination (p 0 + L * p 2 : ℂ) * I_sq

/-- The bijection `ℤ³ ≃ ℤ × ℤ × ℤ`. -/
private def tripleEquiv : (Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ where
  toFun q := (q 0, q 1, q 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv q := by
    ext i
    fin_cases i <;> rfl
  right_inv _ := rfl

/-- **The series of the lift determines its coefficients**: if
`∑ b(n, r, m) e^{2πi(nτ + rz + Nmω)} = 0` on `ℋ₂`, `N ≥ 1`, the sum converging unconditionally, then
`b = 0`. On the points `(v₀ + i, v₁; v₁, v₂/N + i)` it is a Fourier series on the torus
`(ℝ / ℤ)³`. -/
lemma eq_zero_of_hasSum_mul_liftExp {b : ℤ × ℤ × ℤ → ℂ}
    (hb : ∀ Z, HasSum (fun p : ℤ × ℤ × ℤ ↦ b p * liftExp L p.1 p.2.1 p.2.2 Z) 0) : b = 0 := by
  have hd (v : Fin 3 → ℝ) : HasSum (fun q : Fin 3 → ℤ ↦ b (tripleEquiv q) *
      cexp (-(2 * π * (q 0 + L * q 2))) * mFourier q fun i ↦ (v i : UnitAddCircle)) 0 :=
    (tripleEquiv.hasSum_iff.mpr (hb (liftTorusPoint L v))).congr_fun fun q ↦ by
      rw [mul_assoc, ← liftExp_liftTorusPoint]
      rfl
  have hs : Summable fun q : Fin 3 → ℤ ↦ b (tripleEquiv q) * cexp (-(2 * π * (q 0 + L * q 2))) :=
    (hd 0).summable.congr fun q ↦ by
      simp [mFourier]
  have h₀ : (fun q : Fin 3 → ℤ ↦ b (tripleEquiv q) * cexp (-(2 * π * (q 0 + L * q 2)))) = 0 :=
    eq_zero_of_hasSum_mFourier hs fun x ↦ by
      choose v hv using fun i ↦ QuotientAddGroup.mk_surjective (x i)
      exact (funext hv : (fun i ↦ (v i : UnitAddCircle)) = x) ▸ hd v
  funext p
  simpa using congrFun h₀ (tripleEquiv.symm p)

variable (c : ℤ × ℤ → ℂ) (n r : ℤ)

lemma gritsenkoCoeff_one : gritsenkoCoeff k c n r 1 = c (n, r) := by
  simp [gritsenkoCoeff, liftDivisorSum]

/-- **The first Fourier–Jacobi coefficient of `Grit(φ)` is `φ`**: for `φ ∈ J_{k,N}`, the coefficient
of `e^{2πiNω}` in `Grit(φ)` is `φ` itself, as `a(n, r, 1) = c(n, r)`, so that the Gritsenko lift is
a section of the first Fourier–Jacobi coefficient (Poor, Shurman, Yuen, *Finding all Borcherds
product paramodular cusp forms of a given weight and level*, §2.3). -/
lemma gritsenkoFourierJacobi_one (hφ : φ ∈ jacobiFormSpace k N) :
    gritsenkoFourierJacobi k φ x 1 = φ x := by
  simpa only [gritsenkoFourierJacobi, gritsenkoCoeff_one] using
    (hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ x).tsum_eq

/-- **The Gritsenko lift of a nonzero Jacobi cusp form is nonzero**: `Grit(φ) = 0` makes all the
coefficients `a(n, r, m)` vanish, and `a(n, r, 1) = c(n, r)`. -/
lemma gritsenkoLift_ne_zero (hφ : φ ∈ jacobiCuspFormSpace k L) (h₀ : φ ≠ 0) :
    gritsenkoLift k L φ ≠ 0 := by
  intro h
  have hb : (fun p : ℤ × ℤ × ℤ ↦ gritsenkoCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2) = 0 :=
    eq_zero_of_hasSum_mul_liftExp fun Z ↦ by
      have hZ : gritsenkoLift k L φ Z = 0 := congrFun h Z
      rw [gritsenkoLift] at hZ
      exact hZ ▸ (summable_gritsenkoLift Z L.pos hφ).hasSum
  have hc : jacobiCoeff φ = 0 := funext fun q ↦ by
    simpa [gritsenkoCoeff_one] using congrFun hb (q.1, q.2, 1)
  exact h₀ <| eq_zero_of_jacobiCoeff_eq_zero hφ.1 hc

end SiegelUpperHalfSpace
