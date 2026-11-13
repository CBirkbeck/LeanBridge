import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoSmallWeight

/-!
# The Witt restriction of Siegel modular forms of degree 2

Let `F ∈ M_{k,j}(Γ₂)` have weight `ρ_{k,j} = det^k ⊗ Sym^j` and Fourier coefficients `a`, and let
`ψ` be the linear form on `Sym^j(ℂ²)` with `ψ(e₁^j) = 1` (`SiegelUpperHalfSpace.symConstCoeff`).
For `τ₁` in the upper half-plane, the restriction `τ₂ ↦ ψ(F(diag(τ₁, τ₂)))` of `F` to the diagonal
(Witt's operator) is a modular form of weight `k` on `SL(2, ℤ)`: the embedding of `SL(2, ℤ)` into
`Sp(4, ℤ)` in the second coordinate acts on `diag(τ₁, τ₂)` through `τ₂`, with automorphy factor
`diag(1, cτ₂ + d)`, on which `ψ ∘ ρ_{k,j}` is multiplication by `(cτ₂ + d)^k`, and the restriction
is the series `∑ ψ(a(n)) e^{2πi(n₀₀ τ₁ + n₁₁ τ₂)}`, holomorphic and bounded at `i∞` in `τ₂`. As
`τ₂ → i∞` it tends to the Siegel operator `Φ(F)(τ₁)`. Hence `Φ(F) = 0` whenever there are no
nonzero modular forms of weight `k` on `SL(2, ℤ)`, for instance for `k = 2` and `k < 0`; as the
Siegel operator is injective on the orthogonal complement `N_{j,k}(Γ₂)` of the cusp forms,
`N_{j,k}(Γ₂) = 0` in these weights, for every `j`. Among them are the weights `(10, 2)` and
`(16, -2)` of the knowl `mf.siegel.subspace.degree.two`, beyond the reach of
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoSmallWeight`; the weight
`k = 0` is treated in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoWeightZero`.

The series are handled at the points `(p, q; q, r)` of `ℋ₂`, where `e^{2πi tr(nZ)}` is
`e^{2πi(n₀₀ p + 2 n₀₁ q + n₁₁ r)}`: for a positive semidefinite `n`, `2|n₀₁| ≤ n₀₀ + n₁₁`, so a
series of Fourier coefficients with a multiplier of linear growth in `n₀₀ + n₁₁` is dominated by
the Fourier series at a point of `ℋ₂` with smaller imaginary part.

## Main definitions

* `SiegelUpperHalfSpace.ofEntries`: the point `(p, q; q, r)` of `ℋ₂`.
* `SiegelUpperHalfSpace.entriesExp`: the exponential `e^{2πi(n₀₀ p + 2 n₀₁ q + n₁₁ r)}`.
* `SiegelUpperHalfSpace.diagSeries`: the series `∑ d(n) m(n) e^{2πi(n₀₀ p + n₁₁ r)}`.
* `SiegelUpperHalfSpace.diagonalPoint`: the point `diag(τ₁, τ₂)` of `ℋ₂`.
* `SiegelUpperHalfSpace.wittForm`: the Witt restriction `τ₂ ↦ ψ(F(diag(τ₁, τ₂)))`, a modular form
  of weight `k` on `SL(2, ℤ)`.

## Main results

* `SiegelUpperHalfSpace.differentiableOn_diagSeries`,
  `SiegelUpperHalfSpace.isBoundedAtImInfty_diagSeries`,
  `SiegelUpperHalfSpace.tendsto_diagSeries_atImInfty`: the series
  `∑ d(n) m(n) e^{2πi(n₀₀ p + n₁₁ r)}` is holomorphic in `r`, bounded at `i∞`, and tends to the sum
  of its terms with `n₁₁ = 0`.
* `SiegelUpperHalfSpace.symConstCoeff_rhoKJ`: `ψ ∘ ρ_{k,j}` on the lower triangular matrices.
* `SiegelUpperHalfSpace.val_smul_embedSecond`: the action of the second embedding of `SL(2, ℤ)`.
* `SiegelUpperHalfSpace.diagSeries_symConstCoeff_smul`: the transformation law of the Witt
  restriction.
* `SiegelUpperHalfSpace.wittForm_apply`: the Witt restriction is `τ₂ ↦ ψ(F(diag(τ₁, τ₂)))`.
* `SiegelUpperHalfSpace.tendsto_wittForm_atImInfty`: the Witt restriction tends to `Φ(F)(τ₁)` as
  `τ₂ → i∞`.
* `SiegelUpperHalfSpace.siegelOperatorSeries_eq_zero_of_subsingleton`: `Φ(F) = 0` if there are no
  nonzero modular forms of weight `k` on `SL(2, ℤ)`.
* `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_eq_bot_of_subsingleton_modularForm_weight`:
  `N_{j,k}(Γ₂) = 0` if there are no nonzero modular forms of weight `k` on `SL(2, ℤ)`.
* `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_two_eq_bot` (LMFDB `mf.siegel.subspace.degree.two`):
  `N_{j,2}(Γ₂) = 0` for every `j`.
* `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_eq_bot_of_neg` (LMFDB
  `mf.siegel.subspace.degree.two`): `N_{j,k}(Γ₂) = 0` for `k < 0` and every `j`.

## References

* E. Witt, *Eine Identität zwischen Modulformen zweiten Grades*, Abh. Math. Sem. Univ. Hamburg 14
  (1941), 323–337.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open Complex Filter Module Polynomial Real SymplecticGroup Topology

open scoped ComplexOrder Manifold MatrixGroups ModularForm TensorProduct UpperHalfPlane

namespace SiegelUpperHalfSpace

/-! ### Points of `ℋ₂` given by their entries -/

section Points

variable (p q r : ℂ) (hp : 0 < p.im) (hq : q.im ^ 2 < p.im * r.im)

/-- The point `(p, q; q, r)` of the Siegel upper half-space `ℋ₂`, for `p, q, r ∈ ℂ` with
`Im p > 0` and `(Im q)² < Im p Im r`. -/
def ofEntries : SiegelUpperHalfSpace (Fin 2) where
  val := !![p, q; q, r]
  transpose_val := by
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  posDef_im := posDef_of_fin_two (by simp) (by simpa using hp) (sub_pos.mpr (by simpa using hq))

lemma ofEntries_val : (ofEntries p q r hp hq).val = !![p, q; q, r] :=
  rfl

end Points

/-! ### Series of Fourier coefficients at the points `(p, q; q, r)` -/

section Series

variable {Γ : Subgroup (symplecticGroup (Fin 2) ℚ)} (d m : dualLattice Γ → ℂ) (n : dualLattice Γ)
  (p q r : ℂ)

/-- The exponential `e^{2πi(n₀₀ p + 2 n₀₁ q + n₁₁ r)}`, the value of `e^{2πi tr(nZ)}` at
`Z = (p, q; q, r)` for the symmetric matrix `n`. -/
noncomputable def entriesExp : ℂ :=
  cexp (2 * π * I * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℂ) * p +
    2 * ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 : ℂ) * q +
      ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℂ) * r))

lemma fourierExp_of_val_eq {Z : SiegelUpperHalfSpace (Fin 2)} (hZ : Z.val = !![p, q; q, r]) :
    fourierExp n Z = entriesExp n p q r := by
  have hn : (n : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 :=
    congrFun (congrFun n.2.1 0) 1
  rw [fourierExp, entriesExp, hZ]
  congr 1
  simp [trace, Matrix.mul_apply, hn]
  ring1

lemma norm_entriesExp : ‖entriesExp n p q r‖ =
    rexp (-(2 * π * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) * p.im +
      2 * ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 : ℝ) * q.im +
        ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) * r.im))) := by
  rw [entriesExp, Complex.norm_exp]
  congr 1
  simp

lemma abs_two_mul_apply_zero_one_le {N : Matrix (Fin 2) (Fin 2) ℚ} (hN : N.PosSemidef) :
    |2 * N 0 1| ≤ N 0 0 + N 1 1 := by
  have hs : N 1 0 = N 0 1 := by
    simpa using congrFun (congrFun hN.1 0) 1
  have h₁ : 0 ≤ star ![(1 : ℚ), 1] ⬝ᵥ (N *ᵥ ![1, 1]) := hN.dotProduct_mulVec_nonneg _
  have h₂ : 0 ≤ star ![(1 : ℚ), -1] ⬝ᵥ (N *ᵥ ![1, -1]) := hN.dotProduct_mulVec_nonneg _
  simp at h₁ h₂
  rw [abs_le]
  constructor <;> linarith

/-- The series `∑ d(n) m(n) e^{2πi(n₀₀ p + n₁₁ r)}` along the diagonal points `diag(p, r)`, for a
family `d` of coefficients and a multiplier `m`. -/
noncomputable def diagSeries : ℂ :=
  ∑' n, d n * m n * entriesExp n p 0 r

variable {d m n p q r} {a b K : ℝ}

lemma norm_entriesExp_le (hn : (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) (ha : a ≤ p.im - |q.im|)
    (hb : b ≤ r.im - |q.im|) : ‖entriesExp n p q r‖ ≤ ‖entriesExp n (a * I) 0 (b * I)‖ := by
  rw [norm_entriesExp, norm_entriesExp]
  have h₀₀ : (0 : ℝ) ≤ ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) := by
    exact_mod_cast hn.diag_nonneg
  have h₁₁ : (0 : ℝ) ≤ ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) := by
    exact_mod_cast hn.diag_nonneg
  have h₀₁ : |2 * ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 : ℝ)| ≤
      ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) + ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) := by
    exact_mod_cast abs_two_mul_apply_zero_one_le hn
  set x₀ : ℝ := ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ)
  set x₁ : ℝ := ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 : ℝ)
  set x₂ : ℝ := ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ)
  have hq : -(|2 * x₁| * |q.im|) ≤ 2 * x₁ * q.im := by
    rw [← abs_mul]
    exact neg_abs_le _
  have key : x₀ * a + x₂ * b ≤ x₀ * p.im + 2 * x₁ * q.im + x₂ * r.im := by
    nlinarith [mul_le_mul_of_nonneg_right h₀₁ (abs_nonneg q.im), mul_le_mul_of_nonneg_left ha h₀₀,
      mul_le_mul_of_nonneg_left hb h₁₁]
  simp only [mul_I_im, zero_im, mul_zero, add_zero]
  exact Real.exp_le_exp.mpr <| neg_le_neg <| mul_le_mul_of_nonneg_left key (by positivity)

private lemma one_add_mul_rexp_le {x E μ : ℝ} (hx : 0 ≤ x) (hμ : 0 < μ) (hE : μ * x ≤ E) :
    (1 + x) * rexp (-(2 * π * E)) ≤ (1 + (π * μ)⁻¹) * rexp (-(π * E)) := by
  have hπμ : 0 < π * μ := mul_pos Real.pi_pos hμ
  have hE₀ : 0 ≤ π * E := mul_nonneg Real.pi_pos.le ((mul_nonneg hμ.le hx).trans hE)
  have hy : 0 < rexp (-(π * E)) := Real.exp_pos _
  have h₁ : rexp (-(2 * π * E)) = rexp (-(π * E)) * rexp (-(π * E)) := by
    rw [← Real.exp_add]
    congr 1
    ring1
  have h₂ : rexp (-(π * E)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h₃ : π * E * rexp (-(π * E)) ≤ 1 := by
    have h₄ : π * E + 1 ≤ rexp (π * E) := Real.add_one_le_exp _
    have h₅ : rexp (π * E) * rexp (-(π * E)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith
  have h₆ : x * rexp (-(π * E)) ≤ (π * μ)⁻¹ := by
    rw [← one_div, le_div_iff₀ hπμ]
    have h₇ : π * (μ * x) ≤ π * E := mul_le_mul_of_nonneg_left hE Real.pi_pos.le
    nlinarith [mul_le_mul_of_nonneg_right h₇ hy.le]
  rw [h₁]
  nlinarith [mul_le_mul_of_nonneg_right h₆ hy.le, mul_le_mul_of_nonneg_right h₂ hy.le]

variable (n) in
private lemma norm_diagSeries_term_le
    (hpsd : ∀ n, d n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef)
    (hm : ∀ n, d n ≠ 0 → ‖m n‖ ≤ K * (1 + ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) +
      ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ))) {v : ℝ} (hv : 0 < v) (hp : 0 < p.im)
    (hr : v ≤ r.im) : ‖d n * m n * entriesExp n p 0 r‖ ≤
      K * (1 + (π * min p.im v)⁻¹) * ‖entriesExp n (p.im / 2 * I) 0 (v / 2 * I) * d n‖ := by
  by_cases hd : d n = 0
  · simp [hd]
  have h₀₀ : (0 : ℝ) ≤ ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) := by
    exact_mod_cast (hpsd n hd).diag_nonneg
  have h₁₁ : (0 : ℝ) ≤ ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) := by
    exact_mod_cast (hpsd n hd).diag_nonneg
  set x₀ : ℝ := ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ)
  set x₁ : ℝ := ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ)
  have hK : 0 ≤ K :=
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hm n hd)) (by linarith)
  have hE : min p.im v * (x₀ + x₁) ≤ x₀ * p.im + x₁ * v := by
    nlinarith [min_le_left p.im v, min_le_right p.im v]
  have h₁ : (1 + (x₀ + x₁)) * rexp (-(2 * π * (x₀ * p.im + x₁ * v))) ≤
      (1 + (π * min p.im v)⁻¹) * rexp (-(π * (x₀ * p.im + x₁ * v))) :=
    one_add_mul_rexp_le (add_nonneg h₀₀ h₁₁) (lt_min hp hv) hE
  have h₂ : ‖entriesExp n p 0 r‖ ≤ rexp (-(2 * π * (x₀ * p.im + x₁ * v))) := by
    rw [norm_entriesExp]
    refine Real.exp_le_exp.mpr ?_
    simp only [zero_im]
    nlinarith [mul_le_mul_of_nonneg_left hr h₁₁, Real.pi_pos]
  have h₃ : ‖entriesExp n (p.im / 2 * I) 0 (v / 2 * I)‖ = rexp (-(π * (x₀ * p.im + x₁ * v))) := by
    rw [norm_entriesExp]
    congr 1
    norm_num
    ring1
  have h₄ : ‖m n‖ * ‖entriesExp n p 0 r‖ ≤
      K * (1 + (π * min p.im v)⁻¹) * rexp (-(π * (x₀ * p.im + x₁ * v))) := by
    linarith [mul_le_mul (hm n hd) h₂ (norm_nonneg _) (mul_nonneg hK (by linarith)),
      mul_le_mul_of_nonneg_left h₁ hK]
  rw [norm_mul, norm_mul, norm_mul, h₃]
  nlinarith [mul_le_mul_of_nonneg_left h₄ (norm_nonneg (d n))]

private lemma summable_bound (hs : ∀ Z, Summable fun n ↦ fourierExp n Z * d n) {v : ℝ} (hv : 0 < v)
    (hp : 0 < p.im) : Summable fun n : dualLattice Γ ↦
      K * (1 + (π * min p.im v)⁻¹) * ‖entriesExp n (p.im / 2 * I) 0 (v / 2 * I) * d n‖ := by
  have hZ : ((0 : ℂ).im) ^ 2 < (p.im / 2 * I).im * (v / 2 * I).im := by
    norm_num
    positivity
  refine ((hs (ofEntries _ _ _ (by simpa using hp) hZ)).norm.congr fun n ↦ ?_).mul_left _
  rw [fourierExp_of_val_eq n _ _ _ (ofEntries_val _ _ _ _ _)]

variable (p)

/-- **The series `∑ d(n) m(n) e^{2πi(n₀₀ p + n₁₁ r)}` is holomorphic in `r` on the upper
half-plane**, for coefficients `d` with summable Fourier series on `ℋ₂`, supported on positive
semidefinite `n`, and a multiplier `m` of linear growth in `n₀₀ + n₁₁`. -/
lemma differentiableOn_diagSeries (hs : ∀ Z, Summable fun n ↦ fourierExp n Z * d n)
    (hpsd : ∀ n, d n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef)
    (hm : ∀ n, d n ≠ 0 → ‖m n‖ ≤ K * (1 + ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) +
      ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ))) (hp : 0 < p.im) :
    DifferentiableOn ℂ (diagSeries d m p) {r | 0 < r.im} := by
  intro r₀ (hr₀ : 0 < r₀.im)
  have hv : 0 < r₀.im / 2 := half_pos hr₀
  have hU : IsOpen {r : ℂ | r₀.im / 2 < r.im} := isOpen_lt continuous_const continuous_im
  have h : DifferentiableOn ℂ (diagSeries d m p) {r : ℂ | r₀.im / 2 < r.im} :=
    differentiableOn_tsum_of_summable_norm (summable_bound hs hv hp)
      (fun n ↦ by
        unfold entriesExp
        fun_prop)
      hU fun n r hr ↦ norm_diagSeries_term_le n hpsd hm hv hp (le_of_lt hr)
  exact (h.differentiableAt (hU.mem_nhds (by simpa using half_lt_self hr₀))).differentiableWithinAt

/-- **The series `∑ d(n) m(n) e^{2πi(n₀₀ p + n₁₁ r)}` is bounded as `r → i∞`.** -/
lemma isBoundedAtImInfty_diagSeries (hs : ∀ Z, Summable fun n ↦ fourierExp n Z * d n)
    (hpsd : ∀ n, d n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef)
    (hm : ∀ n, d n ≠ 0 → ‖m n‖ ≤ K * (1 + ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) +
      ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ))) (hp : 0 < p.im) :
    UpperHalfPlane.IsBoundedAtImInfty fun τ : ℍ ↦ diagSeries d m p τ := by
  have hu : Summable fun n : dualLattice Γ ↦
      K * (1 + (π * min p.im 1)⁻¹) * ‖entriesExp n (p.im / 2 * I) 0 ((1 : ℝ) / 2 * I) * d n‖ :=
    summable_bound hs one_pos hp
  refine UpperHalfPlane.isBoundedAtImInfty_iff.mpr ⟨∑' n, K * (1 + (π * min p.im 1)⁻¹) *
    ‖entriesExp n (p.im / 2 * I) 0 ((1 : ℝ) / 2 * I) * d n‖, 1, fun τ hτ ↦ ?_⟩
  have hle (n : dualLattice Γ) : ‖d n * m n * entriesExp n p 0 τ‖ ≤
      K * (1 + (π * min p.im 1)⁻¹) * ‖entriesExp n (p.im / 2 * I) 0 ((1 : ℝ) / 2 * I) * d n‖ :=
    norm_diagSeries_term_le n hpsd hm one_pos hp hτ
  have hs' : Summable fun n ↦ ‖d n * m n * entriesExp n p 0 τ‖ :=
    hu.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
  exact (norm_tsum_le_tsum_norm hs').trans (hs'.tsum_le_tsum hle hu)

/-- **The series `∑ d(n) m(n) e^{2πi(n₀₀ p + n₁₁ r)}` tends to the sum of its terms with
`n₁₁ = 0` as `r → i∞`**, by dominated convergence. -/
lemma tendsto_diagSeries_atImInfty (hs : ∀ Z, Summable fun n ↦ fourierExp n Z * d n)
    (hpsd : ∀ n, d n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef)
    (hm : ∀ n, d n ≠ 0 → ‖m n‖ ≤ K * (1 + ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) +
      ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ))) (hp : 0 < p.im) :
    Tendsto (fun τ : ℍ ↦ diagSeries d m p τ) UpperHalfPlane.atImInfty
      (𝓝 (∑' n : dualLattice Γ, if (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0 then
        d n * m n * cexp (2 * π * I * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℂ) * p)) else 0)) := by
  have him : Tendsto (fun τ : ℍ ↦ τ.im) UpperHalfPlane.atImInfty atTop := tendsto_comap
  refine tendsto_tsum_of_dominated_convergence (summable_bound (K := K) hs one_pos hp)
    (fun n ↦ ?_) ?_
  · split_ifs with hn
    · refine tendsto_const_nhds.congr fun τ ↦ ?_
      simp [entriesExp, hn]
    by_cases hd : d n = 0
    · simp [hd]
    have hpos : (0 : ℝ) < ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) := by
      exact_mod_cast lt_of_le_of_ne (hpsd n hd).diag_nonneg (Ne.symm hn)
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    simp only [norm_mul, norm_entriesExp, zero_im, mul_zero]
    have h₁ : Tendsto (fun τ : ℍ ↦ rexp (-(2 * π * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) *
        p.im + ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) * (τ : ℂ).im)))) UpperHalfPlane.atImInfty
          (𝓝 0) :=
      Real.tendsto_exp_atBot.comp <| tendsto_neg_atTop_atBot.comp <|
        (tendsto_atTop_add_const_left _ _ (him.const_mul_atTop hpos)).const_mul_atTop two_pi_pos
    simpa using h₁.const_mul (‖d n‖ * ‖m n‖)
  · filter_upwards [him.eventually_ge_atTop 1] with τ hτ n
    exact norm_diagSeries_term_le n hpsd hm one_pos hp hτ

end Series

/-! ### The linear form `ψ` and the second embedding of `SL(2, ℤ)` -/

variable {k : ℤ} {j : ℕ} (u : Fin j → Fin 2 → ℂ) {x w : ℂ} {A : GL (Fin 2) ℂ}

lemma symConstCoeff_tprod : symConstCoeff j (⨂ₛ[ℂ] i, u i) = ∏ i, u i 0 := by
  rw [symConstCoeff, LinearMap.comp_apply, symDehomogenize_tprod]
  simp [eval_prod]

/-- **`ψ ∘ ρ_{k,j}` on the lower triangular matrices**: for `A = (1, 0; x, w)`,
`ψ(ρ_{k,j}(A) v) = w^k ψ(v)`, as `A` fixes the first coordinate of every vector. -/
lemma symConstCoeff_rhoKJ (hA : (A : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; x, w])
    (v : Sym[ℂ]^j (Fin 2 → ℂ)) : symConstCoeff j (rhoKJ k j A v) = w ^ k * symConstCoeff j v := by
  have hv : v ∈ Submodule.span ℂ (Set.range (SymmetricPower.tprod ℂ)) := by
    rw [SymmetricPower.span_tprod_eq_top]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨u', rfl⟩
    rw [rhoKJ_tprod, map_smul, symConstCoeff_tprod, symConstCoeff_tprod, Units.val_zpow_eq_zpow_val,
      GeneralLinearGroup.val_det_apply, hA]
    simp [dotProduct]
  | zero => simp
  | add y y' _ _ hy hy' => rw [map_add, map_add, hy, hy', map_add, mul_add]
  | smul a y _ hy => rw [map_smul, map_smul, hy, map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm]

variable (g : SL(2, ℤ)) (Z : SiegelUpperHalfSpace (Fin 2))

lemma coe_denomGL_embedSecond : (denomGL (SymplecticGroup.map (Int.castRingHom ℝ) (embedSecond g))
    Z : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1, 0; (g 1 0 : ℂ) * Z.val 0 1, (g 1 0 : ℂ) * Z.val 1 1 + g 1 1] := by
  have hZ : Z.val 1 0 = Z.val 0 1 := Z.val_one_zero
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [denom, embedSecond, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, hZ]

/-- **The action of the second embedding of `SL(2, ℤ)` on `ℋ₂`**: for `g = (a, b; c, d)`,
`(τ₁, z; z, τ₂) ↦ (τ₁ - cz² / (cτ₂ + d), z / (cτ₂ + d); z / (cτ₂ + d), (aτ₂ + b) / (cτ₂ + d))`. -/
lemma val_smul_embedSecond : (SymplecticGroup.map (Int.castRingHom ℝ) (embedSecond g) • Z).val =
    !![Z.val 0 0 - (g 1 0 : ℂ) * Z.val 0 1 ^ 2 / ((g 1 0 : ℂ) * Z.val 1 1 + g 1 1),
      Z.val 0 1 / ((g 1 0 : ℂ) * Z.val 1 1 + g 1 1);
      Z.val 0 1 / ((g 1 0 : ℂ) * Z.val 1 1 + g 1 1),
      ((g 0 0 : ℂ) * Z.val 1 1 + g 0 1) / ((g 1 0 : ℂ) * Z.val 1 1 + g 1 1)] := by
  have hZ : Z.val 1 0 = Z.val 0 1 := Z.val_one_zero
  have hw : (g 1 0 : ℂ) * Z.val 1 1 + g 1 1 ≠ 0 := by
    have h : UpperHalfPlane.denom (g : GL (Fin 2) ℝ)
        (UpperHalfPlane.mk (Z.val 1 1) (im_one_one_pos Z)) ≠ 0 :=
      UpperHalfPlane.denom_ne_zero _ _
    simpa [UpperHalfPlane.denom] using h
  have hw' : Z.val 1 1 * g 1 0 + g 1 1 ≠ 0 := by
    rwa [mul_comm]
  have hdet : (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h : (g : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := g.det_coe
    rw [det_fin_two] at h
    exact_mod_cast h
  have hn : num (SymplecticGroup.map (Int.castRingHom ℝ) (embedSecond g)) Z.val =
      !![Z.val 0 0, Z.val 0 1; (g 0 0 : ℂ) * Z.val 0 1, (g 0 0 : ℂ) * Z.val 1 1 + g 0 1] := by
    ext a c
    fin_cases a <;> fin_cases c <;>
      simp [num, embedSecond, toBlocks₁₁, toBlocks₁₂, Matrix.mul_apply, hZ]
  have hi : (!![1, 0; (g 1 0 : ℂ) * Z.val 0 1, (g 1 0 : ℂ) * Z.val 1 1 + g 1 1])⁻¹ =
      !![1, 0; -((g 1 0 : ℂ) * Z.val 0 1) / ((g 1 0 : ℂ) * Z.val 1 1 + g 1 1),
        1 / ((g 1 0 : ℂ) * Z.val 1 1 + g 1 1)] := by
    refine inv_eq_right_inv ?_
    ext a c
    fin_cases a <;> fin_cases c <;> simp <;> field_simp
    ring1
  rw [val_smul, hn, ← coe_denomGL, coe_denomGL_embedSecond, hi]
  ext a c
  fin_cases a <;> fin_cases c <;> simp <;> field_simp
  · ring1
  · linear_combination Z.val 0 1 * hdet

/-! ### The Witt restriction -/

variable {p q r : ℂ} {F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)}
  {b : dualLattice (integral (Fin 2)) → Sym[ℂ]^j (Fin 2 → ℂ)} (n : dualLattice (integral (Fin 2)))
  (τ₁ τ₂ : ℍ)

variable {Z} in
lemma dual_apply_eq_tsum_entriesExp (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b)
    (φ : Dual ℂ (Sym[ℂ]^j (Fin 2 → ℂ))) (hZ : Z.val = !![p, q; q, r]) :
    φ (F Z) = ∑' n, φ (b n) * entriesExp n p q r := by
  rw [← (hb Z φ).tsum_eq]
  exact tsum_congr fun n ↦ by rw [fourierExp_of_val_eq n p q r hZ, mul_comm]

lemma posSemidef_of_dual_apply_ne_zero (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) (φ : Dual ℂ (Sym[ℂ]^j (Fin 2 → ℂ)))
    (hn : φ (b n) ≠ 0) : (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef :=
  posSemidef_of_apply_ne_zero hF hb n fun h ↦ hn (by rw [h, map_zero])

private lemma norm_one_le (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) (hn : symConstCoeff j (b n) ≠ 0) :
    ‖(1 : dualLattice (integral (Fin 2)) → ℂ) n‖ ≤
      1 * (1 + ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) +
        ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ)) := by
  have h₀₀ : (0 : ℝ) ≤ ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) := by
    exact_mod_cast (posSemidef_of_dual_apply_ne_zero n hF hb _ hn).diag_nonneg
  have h₁₁ : (0 : ℝ) ≤ ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) := by
    exact_mod_cast (posSemidef_of_dual_apply_ne_zero n hF hb _ hn).diag_nonneg
  simp only [Pi.one_apply, norm_one]
  linarith

/-- The point `diag(τ₁, τ₂)` of `ℋ₂`, for `τ₁, τ₂` in the upper half-plane. -/
def diagonalPoint : SiegelUpperHalfSpace (Fin 2) :=
  ofEntries τ₁ 0 τ₂ τ₁.im_pos (by simpa using mul_pos τ₁.im_pos τ₂.im_pos)

lemma diagonalPoint_val : (diagonalPoint τ₁ τ₂).val = !![(τ₁ : ℂ), 0; 0, (τ₂ : ℂ)] :=
  rfl

/-- **The transformation law of the Witt restriction**: `ψ(F(diag(τ₁, gτ₂)))` is
`(cτ₂ + d)^k ψ(F(diag(τ₁, τ₂)))` for `g = (a, b; c, d) ∈ SL(2, ℤ)`, from the transformation law of
`F` under the second embedding of `g`, with automorphy factor `diag(1, cτ₂ + d)`. -/
lemma diagSeries_symConstCoeff_smul (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) :
    diagSeries (fun n ↦ symConstCoeff j (b n)) 1 τ₁ (g • τ₂ : ℍ) =
      ((g 1 0 : ℂ) * τ₂ + g 1 1) ^ k * diagSeries (fun n ↦ symConstCoeff j (b n)) 1 τ₁ τ₂ := by
  have hγZ : (SymplecticGroup.map (Int.castRingHom ℝ) (embedSecond g) •
      diagonalPoint τ₁ τ₂).val = !![(τ₁ : ℂ), 0; 0, ((g • τ₂ : ℍ) : ℂ)] := by
    rw [val_smul_embedSecond, diagonalPoint_val, UpperHalfPlane.coe_specialLinearGroup_apply]
    simp
  have hD : (denomGL (SymplecticGroup.map (Int.castRingHom ℝ) (embedSecond g))
      (diagonalPoint τ₁ τ₂) : Matrix (Fin 2) (Fin 2) ℂ) =
        !![1, 0; 0, (g 1 0 : ℂ) * τ₂ + g 1 1] := by
    rw [coe_denomGL_embedSecond, diagonalPoint_val]
    simp
  have hmod : F (SymplecticGroup.map (Int.castRingHom ℝ) (embedSecond g) • diagonalPoint τ₁ τ₂) =
      rhoKJ k j (denomGL (SymplecticGroup.map (Int.castRingHom ℝ) (embedSecond g))
        (diagonalPoint τ₁ τ₂)) (F (diagonalPoint τ₁ τ₂)) := by
    simpa only [map_algebraMap_map_intCast, MonoidHom.one_apply, Units.val_one, one_smul] using
      hF.2 ⟨_, embedSecond g, trivial, rfl⟩ (diagonalPoint τ₁ τ₂)
  simp only [diagSeries, Pi.one_apply, mul_one]
  rw [← dual_apply_eq_tsum_entriesExp hb _ hγZ,
    ← dual_apply_eq_tsum_entriesExp hb _ (diagonalPoint_val τ₁ τ₂), hmod, symConstCoeff_rhoKJ hD]

private lemma slash_diagSeries (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) :
    (fun τ₂ : ℍ ↦ diagSeries (fun n ↦ symConstCoeff j (b n)) 1 τ₁ τ₂) ∣[k] g =
      fun τ₂ : ℍ ↦ diagSeries (fun n ↦ symConstCoeff j (b n)) 1 τ₁ τ₂ := by
  ext τ
  have hw : UpperHalfPlane.denom g τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  have e : UpperHalfPlane.denom g τ = (g 1 0 : ℂ) * τ + (g 1 1 : ℂ) := by
    simp [UpperHalfPlane.denom]
  rw [ModularForm.SL_slash_apply, diagSeries_symConstCoeff_smul g τ₁ τ hF hb, ← e, zpow_neg,
    mul_comm, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hw), one_mul]

private lemma mdifferentiable_diagSeries (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) :
    MDiff fun τ₂ : ℍ ↦ diagSeries (fun n ↦ symConstCoeff j (b n)) 1 τ₁ τ₂ := by
  refine UpperHalfPlane.mdifferentiable_iff.mpr ((differentiableOn_diagSeries (τ₁ : ℂ)
    (fun Z ↦ (hb Z _).summable) (posSemidef_of_dual_apply_ne_zero · hF hb _)
      (norm_one_le · hF hb) τ₁.im_pos).congr fun z hz ↦ ?_)
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-- The **Witt restriction** of `F ∈ M_{k,j}(Γ₂)`, with Fourier coefficients `a`, at `τ₁` in the
upper half-plane: the modular form `τ₂ ↦ ψ(F(diag(τ₁, τ₂))) = ∑ ψ(a(n)) e^{2πi(n₀₀ τ₁ + n₁₁ τ₂)}`
of weight `k` on `SL(2, ℤ)`, for the linear form `ψ` with `ψ(e₁^j) = 1`. -/
noncomputable def wittForm (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) : ModularForm 𝒮ℒ k where
  toFun τ₂ := diagSeries (fun n ↦ symConstCoeff j (b n)) 1 τ₁ τ₂
  slash_action_eq' := fun _ ⟨g', hg'⟩ ↦ hg' ▸ slash_diagSeries g' τ₁ hF hb
  holo' := mdifferentiable_diagSeries τ₁ hF hb
  bdd_at_cusps' hc := (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun g' _ ↦
    (slash_diagSeries g' τ₁ hF hb).symm ▸ isBoundedAtImInfty_diagSeries (τ₁ : ℂ)
      (fun Z ↦ (hb Z _).summable) (posSemidef_of_dual_apply_ne_zero · hF hb _)
        (norm_one_le · hF hb) τ₁.im_pos

lemma coe_wittForm (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) :
    wittForm τ₁ hF hb τ₂ = diagSeries (fun n ↦ symConstCoeff j (b n)) 1 τ₁ τ₂ :=
  rfl

/-- **The Witt restriction is the restriction to the diagonal**: its value at `τ₂` is
`ψ(F(diag(τ₁, τ₂)))`. -/
lemma wittForm_apply (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) :
    wittForm τ₁ hF hb τ₂ = symConstCoeff j (F (diagonalPoint τ₁ τ₂)) := by
  rw [dual_apply_eq_tsum_entriesExp hb (symConstCoeff j) (diagonalPoint_val τ₁ τ₂), coe_wittForm]
  simp [diagSeries]

/-- **The Witt restriction tends to the Siegel operator**: `ψ(F(diag(τ₁, τ₂))) → Φ(F)(τ₁)` as
`τ₂ → i∞`. -/
lemma tendsto_wittForm_atImInfty (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) :
    Tendsto (wittForm τ₁ hF hb) UpperHalfPlane.atImInfty (𝓝 (siegelOperatorSeries b τ₁)) := by
  have e : (∑' n : dualLattice (integral (Fin 2)), if (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0 then
      symConstCoeff j (b n) * (1 : dualLattice (integral (Fin 2)) → ℂ) n *
        cexp (2 * π * I * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℂ) * τ₁)) else 0) =
          siegelOperatorSeries b τ₁ :=
    tsum_congr fun n ↦ by simp [phiTerm, mul_comm]
  exact e ▸ tendsto_diagSeries_atImInfty (τ₁ : ℂ) (fun Z ↦ (hb Z _).summable)
    (posSemidef_of_dual_apply_ne_zero · hF hb _) (norm_one_le · hF hb) τ₁.im_pos

/-- **`Φ(F) = 0` if there are no nonzero modular forms of weight `k` on `SL(2, ℤ)`**: the Witt
restrictions then vanish, and they tend to `Φ(F)`. -/
lemma siegelOperatorSeries_eq_zero_of_subsingleton (hF : F ∈ modularFormsKJ k j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) (hM : Subsingleton (ModularForm 𝒮ℒ k)) :
    siegelOperatorSeries b τ₁ = 0 := by
  have h₁ : Tendsto (wittForm τ₁ hF hb) UpperHalfPlane.atImInfty (𝓝 (siegelOperatorSeries b τ₁)) :=
    tendsto_wittForm_atImInfty τ₁ hF hb
  rw [Subsingleton.elim (wittForm τ₁ hF hb) 0, FunLike.coe_zero] at h₁
  exact tendsto_nhds_unique h₁ tendsto_const_nhds

/-! ### The vanishing of `N_{j,k}(Γ₂)` -/

variable {c : Sym[ℂ]^j (Fin 2 → ℂ) →ₗ[ℂ] Sym[ℂ]^j (Fin 2 → ℂ) →ₗ⋆[ℂ] ℂ}

/-- **`N_{j,k}(Γ₂) = 0` if there are no nonzero modular forms of weight `k` on `SL(2, ℤ)`**, for
every `j` and an admissible positive definite form `c`: the Siegel operator vanishes on
`M_{j,k}(Γ₂)`, and it is injective on `N_{j,k}(Γ₂)`. -/
lemma cuspFormsOrthogonalKJ_eq_bot_of_subsingleton_modularForm_weight
    (hadm : IsAdmissibleForm (rhoKJ k j) c) (hpos : ∀ v, v ≠ 0 → 0 < c v v)
    (hM : Subsingleton (ModularForm 𝒮ℒ k)) :
    cuspFormsOrthogonalKJ (integral (Fin 2)) k j c = ⊥ :=
  cuspFormsOrthogonalKJ_eq_bot_of_forall_siegelOperatorSeries_eq_zero hadm hpos fun _ hG _ ha τ' ↦
    siegelOperatorSeries_eq_zero_of_subsingleton τ' hG ha hM

/-- **`N_{j,2}(Γ₂) = 0`** (LMFDB `mf.siegel.subspace.degree.two`) for every `j`, for an admissible
positive definite form `c`, as there are no nonzero modular forms of weight `2` on `SL(2, ℤ)`. -/
lemma cuspFormsOrthogonalKJ_two_eq_bot (hadm : IsAdmissibleForm (rhoKJ 2 j) c)
    (hpos : ∀ v, v ≠ 0 → 0 < c v v) : cuspFormsOrthogonalKJ (integral (Fin 2)) 2 j c = ⊥ :=
  cuspFormsOrthogonalKJ_eq_bot_of_subsingleton_modularForm_weight hadm hpos
    (rank_zero_iff.mp ModularForm.levelOne_weight_two_rank_zero)

/-- **`N_{j,k}(Γ₂) = 0` for `k < 0`** (LMFDB `mf.siegel.subspace.degree.two`) and every `j`, for an
admissible positive definite form `c`, as there are no nonzero modular forms of negative weight on
`SL(2, ℤ)`. -/
lemma cuspFormsOrthogonalKJ_eq_bot_of_neg (hadm : IsAdmissibleForm (rhoKJ k j) c)
    (hpos : ∀ v, v ≠ 0 → 0 < c v v) (hk : k < 0) :
    cuspFormsOrthogonalKJ (integral (Fin 2)) k j c = ⊥ :=
  cuspFormsOrthogonalKJ_eq_bot_of_subsingleton_modularForm_weight hadm hpos
    (rank_zero_iff.mp (ModularForm.levelOne_neg_weight_rank_zero hk))

end SiegelUpperHalfSpace
