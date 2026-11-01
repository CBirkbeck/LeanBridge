import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.WhittakerHarmonic

/-!
# The radial equations of a harmonic Fourier mode

A **Fourier mode** of frequency `μ ∈ ℂ` and weight `k` on `ℋ₃` is a function `F(x, y) = ψ(μx) φ(y)`,
where `ψ(z) = e^{2πi(z + z̄)}` and `φ : (0, ∞) → ℂ^{k+1}` (`bianchiFourierMode`): the Fourier
coefficients of a Bianchi modular form of weight `k` are of this form, and so are the terms
`y W_k(u, 4π|μ|y) ψ(μx)` of its Fourier–Bessel expansion (`bianchiWhittakerFunction`). Write
`R_j(y) = y^k φ_j(y)` (`fourierModeRadial`). Pairing the lift `Φ_F` of `F` to `SL(2, ℂ)` with
`(C(k, i) w₁^{k-i} w₂^i)_i` gives the generating function `∑_j C(k, j) Q^j P^{k-j} R_j(y) e^θ` of
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.WhittakerHarmonic`, where
`g = (a, b; c, d)`, `Q = c w₁ + d w₂`, `P = d̄ w₁ - c̄ w₂`, `y = 1 / (|c|² + |d|²)` and `θ` is the
phase of `ψ(μx)` at `g j = (x, y)` (the functions of the namespace
`HyperbolicThreeSpace.WhittakerCasimir`). The computation of the Casimir operator `Ψ` made there
for the `K`-Bessel functions holds for all radial functions of class `C²`: `Ψ - (k² - 4) / 8` maps
the generating function to `∑_j C(k, j) Q^j P^{k-j} e^θ D_j(y)`, where
`D_j = j(j + 2)/2 R_j - (j + 1/2) y R_j' + y²/2 R_j'' - 8π²|μ|²y² R_j - (k² - 4)/8 R_j +
4πiμ(k - j) y R_{j+1}` (`bianchiRadialOperator`). At `g = diag(√y, 1/√y)`, the polynomial
`Q^j P^{k-j}` is a multiple of `w₁^{k-j} w₂^j`, so the first Casimir equation of `F` gives the
**radial equations** `D_j = 0`, `0 ≤ j ≤ k`. Complex conjugation of `SL(2, ℂ)` turns the second
Casimir equation into the first one for the frequency `μ̄` and the radial functions
`(-1)^j R_{k-j}`, so it gives the radial equations of these.

## Main definitions

* `HyperbolicThreeSpace.bianchiFourierMode` (LMFDB `mf.bianchi.spaces`): the function `ψ(μx) φ(y)`.
* `HyperbolicThreeSpace.fourierModeRadial`: its radial functions `R_j(y) = y^k φ_j(y)`.
* `HyperbolicThreeSpace.bianchiRadialOperator`: the radial operator `D_j`.

## Main results

* `HyperbolicThreeSpace.bianchiRadialOperator_eq_zero_of_casimirOne`: the first Casimir equation of
  a Fourier mode gives the radial equations of its radial functions.
* `HyperbolicThreeSpace.bianchiRadialOperator_eq_zero_of_casimirTwo`: the second Casimir equation
  gives the radial equations of the reflected radial functions `(-1)^j R_{k-j}`, for `μ̄`.
-/

open Complex Matrix

open scoped ComplexConjugate MatrixGroups Real

namespace HyperbolicThreeSpace

open WhittakerCasimir

variable {f₂ : SL(2, ℂ) → ℂ} (w₁ w₂ μ : ℂ) (k : ℕ) {ρ : ℝ → ℂ} {s : ℝ}

private lemma hasDerivAt_of_contDiffOn_Ioi (hρ : ContDiffOn ℝ 2 ρ (Set.Ioi 0)) (hs : 0 < s) :
    HasDerivAt ρ (deriv ρ s) s :=
  ((hρ.contDiffAt (Ioi_mem_nhds hs)).differentiableAt two_ne_zero).hasDerivAt

private lemma hasDerivAt_deriv_of_contDiffOn_Ioi (hρ : ContDiffOn ℝ 2 ρ (Set.Ioi 0)) (hs : 0 < s) :
    HasDerivAt (deriv ρ) (deriv (deriv ρ) s) s :=
  (((hρ.deriv_of_isOpen isOpen_Ioi (m := 1) le_rfl).contDiffAt (Ioi_mem_nhds hs)).differentiableAt
    one_ne_zero).hasDerivAt

private lemma casimirOne_comp_fYr (hρ : ContDiffOn ℝ 2 ρ (Set.Ioi 0)) (g : SL(2, ℂ)) :
    casimirOne (ρ ∘ fYr) g = deriv ρ (fYr g) * (-(1 / 2) * fY g) +
      2⁻¹ * (deriv (deriv ρ) (fYr g) * fY g ^ 2) := by
  have h : IsLieSmooth fun g ↦ (fYr g : ℂ) := by
    rw [ofReal_fYr]
    exact isLieSmooth_fY
  rw [casimirOne_comp_real (fun g ↦ hasDerivAt_of_contDiffOn_Ioi hρ (fYr_pos g))
    (fun g ↦ hasDerivAt_deriv_of_contDiffOn_Ioi hρ (fYr_pos g)) h, ofReal_fYr, casimirOne_fY]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
    casimirOneBracket_fY_fY]

variable (f₂) in
private lemma casimirOneBracket_comp_fYr (hρ : ContDiffOn ℝ 2 ρ (Set.Ioi 0)) (g : SL(2, ℂ)) :
    casimirOneBracket (ρ ∘ fYr) f₂ g = deriv ρ (fYr g) * casimirOneBracket fY f₂ g := by
  have h : IsLieDifferentiable fun g ↦ (fYr g : ℂ) := by
    rw [ofReal_fYr]
    exact isLieSmooth_fY.isLieDifferentiable
  rw [casimirOneBracket_comp_real (fun g ↦ hasDerivAt_of_contDiffOn_Ioi hρ (fYr_pos g)) h,
    ofReal_fYr]
  rfl

variable (ρ) in
/-- The `j`-th term `Q^j ρ(y) e^θ P^{k-j}` of the generating function, for a radial function `ρ`. -/
private noncomputable def radialTerm (j : ℕ) : SL(2, ℂ) → ℂ :=
  (fun z ↦ z ^ j) ∘ fQ w₁ w₂ * ((ρ ∘ fYr) * (cexp ∘ fΘ μ)) * ((fun z ↦ z ^ (k - j)) ∘ fP w₁ w₂)

private lemma isLieSmooth_radialTerm (hρ : ContDiffOn ℝ 2 ρ (Set.Ioi 0)) (j : ℕ) :
    IsLieSmooth (radialTerm w₁ w₂ μ k ρ j) :=
  ((isLieSmooth_pow_comp j (isLieSmooth_fQ w₁ w₂)).mul
    ((isLieSmooth_comp_fYr hρ).mul ((isLieSmooth_fΘ μ).comp_contDiff contDiff_exp))).mul
    (isLieSmooth_pow_comp (k - j) (isLieSmooth_fP w₁ w₂))

private lemma casimirOne_radialTerm (hρ : ContDiffOn ℝ 2 ρ (Set.Ioi 0)) (j : ℕ) (g : SL(2, ℂ)) :
    casimirOne (radialTerm w₁ w₂ μ k ρ j) g = fP w₁ w₂ g ^ (k - j) * cexp (fΘ μ g) *
      (fQ w₁ w₂ g ^ j * ((j * (j + 2) / 2 : ℂ) * ρ (fYr g) -
        (2⁻¹ : ℂ) * fY g * deriv ρ (fYr g) + (2⁻¹ : ℂ) * fY g ^ 2 * deriv (deriv ρ) (fYr g) -
        8 * π ^ 2 * normSq μ * fY g ^ 2 * ρ (fYr g) - j * fY g * deriv ρ (fYr g)) +
      j * fQ w₁ w₂ g ^ (j - 1) * (4 * π * I * μ * fY g * fP w₁ w₂ g) * ρ (fYr g)) := by
  have hQ : IsLieSmooth ((fun z ↦ z ^ j) ∘ fQ w₁ w₂) :=
    isLieSmooth_pow_comp j (isLieSmooth_fQ w₁ w₂)
  have hR : IsLieSmooth (ρ ∘ fYr) :=
    isLieSmooth_comp_fYr hρ
  have hE : IsLieSmooth (cexp ∘ fΘ μ) :=
    (isLieSmooth_fΘ μ).comp_contDiff contDiff_exp
  rw [radialTerm, casimirOne_mul_of_lieDerivOne_eq_zero (hQ.mul (hR.mul hE))
    (isLieSmooth_pow_comp (k - j) (isLieSmooth_fP w₁ w₂)) fun b ↦ lieDerivOne_fP_pow b _ _ _,
    casimirOne_mul hQ (hR.mul hE), casimirOne_mul hR hE,
    casimirOneBracket_mul_right hR.isLieDifferentiable hE.isLieDifferentiable]
  simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
  rw [casimirOne_fQ_pow, casimirOne_comp_fYr hρ, casimirOne_exp_fΘ,
    casimirOneBracket_comp_fYr _ hρ, casimirOneBracket_comm fY, casimirOneBracket_exp_fΘ,
    casimirOneBracket_comm (fΘ μ), casimirOneBracket_fY_fΘ, casimirOneBracket_fQ_pow,
    casimirOneBracket_fQ_pow, casimirOneBracket_comm (fQ w₁ w₂), casimirOneBracket_exp_fΘ,
    casimirOneBracket_comm (fΘ μ), casimirOneBracket_fQ_fΘ, casimirOneBracket_comm (fQ w₁ w₂),
    casimirOneBracket_comp_fYr _ hρ, casimirOneBracket_fY_fQ]
  rcases j with _ | j
  · ring1
  · simp only [Nat.add_sub_cancel, Nat.cast_add, pow_succ]
    ring1

variable (R : ℕ → ℝ → ℂ)

/-- The generating function `∑_j C(k, j) Q^j P^{k-j} R_j(y) e^θ` of a family `R` of radial
functions. -/
private noncomputable def radialGen : SL(2, ℂ) → ℂ :=
  ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) • radialTerm w₁ w₂ μ k (R j) j

/-- The **radial operator** `D_j = j(j + 2)/2 R_j - (j + 1/2) y R_j' + y²/2 R_j'' - 8π²|μ|²y² R_j -
(k² - 4)/8 R_j + 4πiμ(k - j) y R_{j+1}` at `y`, for a family `R : ℕ → ℝ → ℂ` of radial functions,
the frequency `μ` and the weight `k`: the first Casimir equation of the Fourier mode
`ψ(μx) (y^{-k} R_j(y))_j` is the system of radial equations `D_j = 0`, `0 ≤ j ≤ k`
(`bianchiRadialOperator_eq_zero_of_casimirOne`). -/
noncomputable def bianchiRadialOperator (j : ℕ) (y : ℝ) : ℂ :=
  (j * (j + 2) / 2 : ℂ) * R j y - (2⁻¹ + j) * y * deriv (R j) y +
    2⁻¹ * (y : ℂ) ^ 2 * deriv (deriv (R j)) y - 8 * π ^ 2 * normSq μ * (y : ℂ) ^ 2 * R j y -
      harmonicEigenvalue k * R j y + 4 * π * I * μ * ((k : ℂ) - j) * y * R (j + 1) y

private lemma casimirOne_radialGen (hR : ∀ j, ContDiffOn ℝ 2 (R j) (Set.Ioi 0)) (g : SL(2, ℂ)) :
    casimirOne (radialGen w₁ w₂ μ k R) g - harmonicEigenvalue k * radialGen w₁ w₂ μ k R g =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * fQ w₁ w₂ g ^ j * fP w₁ w₂ g ^ (k - j) *
        cexp (fΘ μ g) * bianchiRadialOperator μ k R j (fYr g) := by
  rw [radialGen, casimirOne_sum _ fun j ↦ (isLieSmooth_radialTerm w₁ w₂ μ k (hR j) j).const_smul _]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hy : fY g = (fYr g : ℂ) := by
    rw [← ofReal_fYr]
  have key (j : ℕ) : casimirOne ((k.choose j : ℂ) • radialTerm w₁ w₂ μ k (R j) j) g -
      harmonicEigenvalue k * ((k.choose j : ℂ) * radialTerm w₁ w₂ μ k (R j) j g) =
        (k.choose j : ℂ) * fQ w₁ w₂ g ^ j * fP w₁ w₂ g ^ (k - j) * cexp (fΘ μ g) *
          bianchiRadialOperator μ k R j (fYr g) - (k.choose j : ℂ) * ((k : ℂ) - j) *
            fQ w₁ w₂ g ^ j * fP w₁ w₂ g ^ (k - j) * cexp (fΘ μ g) *
              (4 * π * I * μ * fY g * R (j + 1) (fYr g)) + (k.choose j : ℂ) * j *
                fQ w₁ w₂ g ^ (j - 1) * fP w₁ w₂ g ^ (k - j) * fP w₁ w₂ g * cexp (fΘ μ g) *
                  (4 * π * I * μ * fY g * R j (fYr g)) := by
    rw [casimirOne_smul _ (isLieSmooth_radialTerm w₁ w₂ μ k (hR j) j), Pi.smul_apply, smul_eq_mul,
      casimirOne_radialTerm w₁ w₂ μ k (hR j) j]
    simp only [radialTerm, bianchiRadialOperator, Pi.mul_apply, Function.comp_apply, hy]
    ring1
  have hXY : ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * ((k : ℂ) - j) * fQ w₁ w₂ g ^ j *
      fP w₁ w₂ g ^ (k - j) * cexp (fΘ μ g) * (4 * π * I * μ * fY g * R (j + 1) (fYr g)) =
        ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * j * fQ w₁ w₂ g ^ (j - 1) *
          fP w₁ w₂ g ^ (k - j) * fP w₁ w₂ g * cexp (fΘ μ g) *
            (4 * π * I * μ * fY g * R j (fYr g)) := by
    refine sum_range_succ_eq_of_shift k _ _ (fun i hi ↦ ?_) (by simp) (by simp)
    have hc :
        ((k.choose (i + 1) : ℕ) : ℂ) * ((i + 1 : ℕ) : ℂ) = (k.choose i : ℂ) * ((k : ℂ) - i) := by
      rw [← Nat.cast_mul, Nat.choose_succ_right_eq, Nat.cast_mul, Nat.cast_sub hi.le]
    have e : k - i = k - (i + 1) + 1 := by
      omega
    rw [e, Nat.add_sub_cancel, pow_succ]
    linear_combination (-(fQ w₁ w₂ g ^ i * fP w₁ w₂ g ^ (k - (i + 1)) * fP w₁ w₂ g *
      cexp (fΘ μ g) * (4 * π * I * μ * fY g * R (i + 1) (fYr g)))) * hc
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun j _ ↦ key j,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, hXY, sub_add_cancel]

/-- The diagonal element `diag(t, 1/t)` of `SL(2, ℂ)`, which maps `j` to `(0, t²)` for `t > 0`. -/
private noncomputable def diagSL (t : ℝ) : SL(2, ℂ) :=
  sl2Exp 0 (Real.log t)

variable {t : ℝ}

private lemma coe_diagSL (ht : 0 < t) :
    (diagSL t : Matrix (Fin 2) (Fin 2) ℂ) = !![(t : ℂ), 0; 0, (t : ℂ)⁻¹] := by
  have h₁ : cexp (Real.log t) = t := by
    rw [← ofReal_exp, Real.exp_log ht]
  have h₂ : cexp (-(Real.log t : ℂ)) = (t : ℂ)⁻¹ := by
    rw [exp_neg, h₁]
  simp only [diagSL, sl2Exp, h₁, h₂]

private lemma fQ_diagSL (ht : 0 < t) : fQ w₁ w₂ (diagSL t) = w₂ * (t : ℂ)⁻¹ := by
  simp [fQ, ent, coe_diagSL ht]

private lemma fP_diagSL (ht : 0 < t) : fP w₁ w₂ (diagSL t) = w₁ * (t : ℂ)⁻¹ := by
  simp [fP, cent, coe_diagSL ht]

private lemma fYr_diagSL (ht : 0 < t) : fYr (diagSL t) = t ^ 2 := by
  simp [fYr, coe_diagSL ht, sq]

private lemma fΘ_diagSL (ht : 0 < t) : fΘ μ (diagSL t) = 0 := by
  simp [fΘ, fV, fU, fUb, ent, cent, coe_diagSL ht]

private lemma bianchiRadialOperator_eq_zero_of_radialGen
    (hR : ∀ j, ContDiffOn ℝ 2 (R j) (Set.Ioi 0)) (h : ∀ w₁ w₂ : ℂ,
      casimirOne (radialGen w₁ w₂ μ k R) = harmonicEigenvalue k • radialGen w₁ w₂ μ k R)
    {j : ℕ} (hj : j ≤ k) {y : ℝ} (hy : 0 < y) : bianchiRadialOperator μ k R j y = 0 := by
  have ht : 0 < √y := Real.sqrt_pos.mpr hy
  have ht' : ((√y : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hY : fYr (diagSL √y) = y := by
    rw [fYr_diagSL ht, Real.sq_sqrt hy.le]
  have hv : (fun i : Fin (k + 1) ↦ ((√y : ℝ) : ℂ)⁻¹ ^ k * bianchiRadialOperator μ k R i y) = 0 := by
    refine eq_zero_of_sum_choose_mul k fun w₁ w₂ ↦ ?_
    have h₀ : casimirOne (radialGen w₁ w₂ μ k R) (diagSL √y) -
        harmonicEigenvalue k * radialGen w₁ w₂ μ k R (diagSL √y) = 0 := by
      rw [h w₁ w₂, Pi.smul_apply, smul_eq_mul, sub_self]
    rw [casimirOne_radialGen w₁ w₂ μ k R hR, fQ_diagSL _ _ ht, fP_diagSL _ _ ht, fΘ_diagSL _ ht,
      hY, exp_zero, ← Fin.sum_univ_eq_sum_range] at h₀
    rw [← h₀]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hp :
        ((√y : ℝ) : ℂ)⁻¹ ^ (i : ℕ) * ((√y : ℝ) : ℂ)⁻¹ ^ (k - i : ℕ) = ((√y : ℝ) : ℂ)⁻¹ ^ k := by
      rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp i.2)]
    rw [mul_pow, mul_pow]
    linear_combination (-((k.choose i : ℂ) * w₂ ^ (i : ℕ) * w₁ ^ (k - i : ℕ) *
      bianchiRadialOperator μ k R i y)) * hp
  have hj' : ((√y : ℝ) : ℂ)⁻¹ ^ k * bianchiRadialOperator μ k R j y = 0 := by
    simpa using congrFun hv ⟨j, Nat.lt_succ_iff.mpr hj⟩
  exact (mul_eq_zero.mp hj').resolve_left (pow_ne_zero k (inv_ne_zero ht'))

variable {k}

variable (φ : ℝ → Fin (k + 1) → ℂ) in
/-- The **Fourier mode** `F(x, y) = ψ(μx) φ(y)` (LMFDB `mf.bianchi.spaces`) of frequency `μ ∈ ℂ` on
`ℋ₃`, with values in `ℂ^{k+1}`, where `ψ(z) = e^{2πi(z + z̄)}` and `φ : (0, ∞) → ℂ^{k+1}`: the
functions transforming under the translations `x ↦ x + t` of `ℋ₃` by the character `ψ(μt)`. The
Fourier coefficients of a Bianchi modular form, and the terms `y W_k(u, 4π|μ|y) ψ(μx)` of its
Fourier–Bessel expansion (`bianchiWhittakerFunction`), are Fourier modes. -/
noncomputable def bianchiFourierMode : HyperbolicThreeSpace → Fin (k + 1) → ℂ :=
  fun z ↦ cexp (2 * π * I * (μ * z.coords.1 + conj (μ * z.coords.1))) • φ z.coords.2

variable (φ : ℝ → Fin (k + 1) → ℂ) in
/-- The **radial functions** `R_j(y) = y^k φ_j(y)` of the Fourier mode `ψ(μx) φ(y)` of weight `k`,
for `j ∈ ℕ` taken modulo `k + 1`: the coefficients of the generating function of its lift to
`SL(2, ℂ)`, which satisfy the radial equations (`bianchiRadialOperator`) when it is harmonic. -/
noncomputable def fourierModeRadial (j : ℕ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ k * φ y (Fin.ofNat (k + 1) j)

variable {φ : ℝ → Fin (k + 1) → ℂ}

lemma contDiffOn_fourierModeRadial (hφ : ContDiffOn ℝ 2 φ (Set.Ioi 0)) (j : ℕ) :
    ContDiffOn ℝ 2 (fourierModeRadial φ j) (Set.Ioi 0) :=
  (contDiff_ofReal.pow k).contDiffOn.mul (contDiffOn_pi.mp hφ _)

private lemma extend_bianchiFourierMode (g : SL(2, ℂ)) :
    extend (bianchiFourierMode μ φ) (moebius g (0, 1)) = cexp (fΘ μ g) • φ (fYr g) := by
  have hpos : 0 < (moebius g (0, 1)).2 := moebius_snd_pos g one_pos
  have hc : coords (.mk (WithLp.toLp 2 (moebius g (0, 1))) hpos) = moebius g (0, 1) :=
    rfl
  have hU : conj (fU g) = fUb g := by
    simp [fU, fUb, ent, cent]
  have hY : conj (fY g) = fY g := by
    rw [← ofReal_fYr, conj_ofReal]
  rw [extend, dite_eq_left hpos]
  simp only [bianchiFourierMode, hc, moebius_snd, moebius_fst]
  congr 2
  simp only [fΘ, fV, Pi.smul_apply, Pi.mul_apply, Pi.add_apply, smul_eq_mul, map_mul, hU, hY]
  ring1

private lemma isLieSmooth_bianchiLift_bianchiFourierMode (hφ : ContDiffOn ℝ 2 φ (Set.Ioi 0)) :
    IsLieSmooth (bianchiLift k (bianchiFourierMode μ φ)) :=
  isLieSmooth_of_contDiff fun γ hγ ↦ by
    have h₁₀ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := hγ 1 0
    have h₁₁ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := hγ 1 1
    have hN (st : ℝ × ℝ) : moebiusDenom (γ st) (0, 1) ≠ 0 :=
      (moebiusDenom_pos (γ st) (p := (0, 1)) one_pos).ne'
    have hD : ContDiff ℝ 2 fun st ↦ moebiusDenom (γ st) (0, 1) := by
      simp only [moebiusDenom]
      fun_prop
    have hΦ : ContDiff ℝ 2 fun st ↦ φ (fYr (γ st)) :=
      hφ.comp_contDiff (contDiff_fYr_comp hγ) fun st ↦ fYr_pos (γ st)
    refine contDiff_pi.2 fun i ↦ ?_
    simp only [Function.comp_def, bianchiLift_apply, extend_bianchiFourierMode, mulVec, dotProduct]
    refine ContDiff.sum fun j _ ↦ ContDiff.mul ?_ ?_
    · simp only [inv_automorphyFactor, symPowMatrix, of_apply, Matrix.smul_apply,
        cons_val_zero, cons_val_one, ← ofReal_inv]
      fun_prop (disch := exact hN _)
    · exact (contDiff_exp.comp (contDiff_fΘ_comp μ hγ)).mul (contDiff_pi.mp hΦ j)

private lemma sum_choose_mul_bianchiLift_bianchiFourierMode (g : SL(2, ℂ)) :
    ∑ i : Fin (k + 1), (k.choose i : ℂ) * w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ) *
      bianchiLift k (bianchiFourierMode μ φ) g i =
        radialGen w₁ w₂ μ k (fourierModeRadial φ) g := by
  have hS : ∑ i : Fin (k + 1), (k.choose i : ℂ) * w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ) *
      bianchiLift k (bianchiFourierMode μ φ) g i = ∑ j : Fin (k + 1),
        (∑ i : Fin (k + 1), (k.choose i : ℂ) * w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ) *
          symPowMatrix k (automorphyFactor g (0, 1))⁻¹ i j) *
            extend (bianchiFourierMode μ φ) (moebius g (0, 1)) j := by
    simp only [bianchiLift_apply, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring1
  have hN : (moebiusDenom g (0, 1) : ℂ) = fN g := by
    rw [fN_apply, moebiusDenom]
    simp only [mul_zero, zero_add, one_pow, mul_one]
    push_cast
    ring1
  have hY : (fN g)⁻¹ = (fYr g : ℂ) :=
    (congrFun ofReal_fYr g).symm
  rw [hS, extend_bianchiFourierMode, radialGen, Finset.sum_apply,
    ← Fin.sum_univ_eq_sum_range (fun j ↦ ((k.choose j : ℂ) •
      radialTerm w₁ w₂ μ k (fourierModeRadial φ j) j) g)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [sum_choose_mul_symPowMatrix, inv_automorphyFactor, hN]
  simp only [radialTerm, fourierModeRadial, Fin.ofNat_val_eq_self, Pi.mul_apply,
    Function.comp_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, of_apply, cons_val_zero,
    cons_val_one, fQ, fP, ent, cent, Pi.add_apply, Pi.sub_apply, hY, mul_zero, zero_add, ofReal_one,
    mul_one]
  have hb₁ : (fYr g : ℂ) * conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) * w₁ +
      (fYr g : ℂ) * -conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) * w₂ = (fYr g : ℂ) *
        (w₁ * conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) -
          w₂ * conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) := by
    ring1
  have hb₂ : (fYr g : ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * w₁ +
      (fYr g : ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * w₂ = (fYr g : ℂ) *
        (w₁ * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 + w₂ * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) := by
    ring1
  have hp : (fYr g : ℂ) ^ (k - j : ℕ) * (fYr g : ℂ) ^ (j : ℕ) = (fYr g : ℂ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp j.2)]
  rw [hb₁, hb₂, mul_pow, mul_pow]
  linear_combination ((k.choose j : ℂ) *
    (w₁ * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 + w₂ * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) ^ (j : ℕ) *
      (w₁ * conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) -
        w₂ * conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) ^ (k - j : ℕ) * cexp (fΘ μ g) *
          φ (fYr g) j) * hp

variable {μ} in
/-- **The first Casimir equation of a Fourier mode gives the radial equations**: if the Casimir
operator `Ψ` acts by `(k² - 4) / 8` on the lift of the Fourier mode `ψ(μx) φ(y)` of weight `k`
(`bianchiFourierMode`), with `φ` of class `C²` on `(0, ∞)`, then its radial functions
`R_j(y) = y^k φ_j(y)` (`fourierModeRadial`) satisfy the radial equations
`j(j + 2)/2 R_j - (j + 1/2) y R_j' + y²/2 R_j'' - 8π²|μ|²y² R_j - (k² - 4)/8 R_j +
4πiμ(k - j) y R_{j+1} = 0` (`bianchiRadialOperator`) for `0 ≤ j ≤ k` and `y > 0`. -/
lemma bianchiRadialOperator_eq_zero_of_casimirOne (hφ : ContDiffOn ℝ 2 φ (Set.Ioi 0))
    (h : casimirOne (bianchiLift k (bianchiFourierMode μ φ)) =
      harmonicEigenvalue k • bianchiLift k (bianchiFourierMode μ φ)) {j : ℕ} (hj : j ≤ k) {y : ℝ}
    (hy : 0 < y) : bianchiRadialOperator μ k (fourierModeRadial φ) j y = 0 := by
  refine bianchiRadialOperator_eq_zero_of_radialGen μ k _ (contDiffOn_fourierModeRadial hφ)
    (fun w₁ w₂ ↦ ?_) hj hy
  let L : (Fin (k + 1) → ℂ) →L[ℂ] ℂ := ∑ i : Fin (k + 1),
    ((k.choose i : ℂ) * w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ)) • ContinuousLinearMap.proj i
  have hL (v : Fin (k + 1) → ℂ) :
      L v = ∑ i : Fin (k + 1), (k.choose i : ℂ) * w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ) * v i := by
    simp [L]
  have h₁ :
      L ∘ bianchiLift k (bianchiFourierMode μ φ) = radialGen w₁ w₂ μ k (fourierModeRadial φ) :=
    funext fun g ↦ by rw [Function.comp_apply, hL, sum_choose_mul_bianchiLift_bianchiFourierMode]
  rw [← h₁, casimirOne_clm_comp L (isLieSmooth_bianchiLift_bianchiFourierMode μ hφ), h]
  funext g
  simp only [Function.comp_apply, Pi.smul_apply, map_smul]

private lemma radialTerm_conjSL (j : ℕ) (g : SL(2, ℂ)) :
    radialTerm w₁ w₂ μ k ρ j (conjSL g) = fP w₂ (-w₁) g ^ j *
      (ρ (fYr g) * cexp (fΘ (conj μ) g)) * (-fQ w₂ (-w₁) g) ^ (k - j) := by
  have hY : fYr (conjSL g) = fYr g := by
    simp [fYr, conjSL_apply]
  have hΘ : fΘ μ (conjSL g) = fΘ (conj μ) g := by
    simp only [fΘ, fY, fV, fN, fU, fUb, ent, cent, Pi.smul_apply, Pi.mul_apply, Pi.add_apply,
      smul_eq_mul, conjSL_apply, conj_conj]
    ring1
  simp only [radialTerm, Pi.mul_apply, Function.comp_apply, hY, hΘ]
  congr 2
  · simp [fQ, fP, ent, cent, conjSL_apply]
    ring1
  · simp [fQ, fP, ent, cent, conjSL_apply]
    ring1

private lemma radialGen_conjSL (g : SL(2, ℂ)) : radialGen w₁ w₂ μ k R (conjSL g) =
    radialGen w₂ (-w₁) (conj μ) k (fun j y ↦ (-1) ^ j * R (k - j) y) g := by
  simp only [radialGen, Finset.sum_apply, Pi.smul_apply, radialTerm_conjSL]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Nat.add_sub_cancel, Nat.sub_sub_self hj', Nat.choose_symm hj']
  simp only [radialTerm, Pi.mul_apply, Function.comp_apply]
  rw [neg_pow (fQ w₂ (-w₁) g)]
  ring1

variable {μ} in
/-- **The second Casimir equation of a Fourier mode gives the reflected radial equations**: if the
Casimir operator `Ψ'` acts by `(k² - 4) / 8` on the lift of the Fourier mode `ψ(μx) φ(y)` of
weight `k` (`bianchiFourierMode`), with `φ` of class `C²` on `(0, ∞)`, then the reflected radial
functions `(-1)^j R_{k-j}`, `R_j(y) = y^k φ_j(y)`, satisfy the radial equations
(`bianchiRadialOperator`) of the frequency `μ̄`, for `0 ≤ j ≤ k` and `y > 0`. Complex conjugation
of `SL(2, ℂ)` exchanges `Ψ` and `Ψ'`. At `j = k` this is the equation
`k(k + 2)/2 R₀ - (k + 1/2) y R₀' + y²/2 R₀'' - 8π²|μ|²y² R₀ - (k² - 4)/8 R₀ = 0`, which only
involves `R₀`. -/
lemma bianchiRadialOperator_eq_zero_of_casimirTwo (hφ : ContDiffOn ℝ 2 φ (Set.Ioi 0))
    (h : casimirTwo (bianchiLift k (bianchiFourierMode μ φ)) =
      harmonicEigenvalue k • bianchiLift k (bianchiFourierMode μ φ)) {j : ℕ} (hj : j ≤ k) {y : ℝ}
    (hy : 0 < y) : bianchiRadialOperator (conj μ) k
      (fun j y ↦ (-1) ^ j * fourierModeRadial φ (k - j) y) j y = 0 := by
  refine bianchiRadialOperator_eq_zero_of_radialGen (conj μ) k _
    (fun j ↦ contDiffOn_const.mul (contDiffOn_fourierModeRadial hφ (k - j))) (fun w₁ w₂ ↦ ?_) hj hy
  let L : (Fin (k + 1) → ℂ) →L[ℂ] ℂ := ∑ i : Fin (k + 1),
    ((k.choose i : ℂ) * (-w₂) ^ (k - i : ℕ) * w₁ ^ (i : ℕ)) • ContinuousLinearMap.proj i
  have hL (v : Fin (k + 1) → ℂ) :
      L v = ∑ i : Fin (k + 1), (k.choose i : ℂ) * (-w₂) ^ (k - i : ℕ) * w₁ ^ (i : ℕ) * v i := by
    simp [L]
  have h₁ : L ∘ (bianchiLift k (bianchiFourierMode μ φ) ∘ conjSL) =
      radialGen w₁ w₂ (conj μ) k (fun j y ↦ (-1) ^ j * fourierModeRadial φ (k - j) y) :=
    funext fun g ↦ by
      rw [Function.comp_apply, Function.comp_apply, hL,
        sum_choose_mul_bianchiLift_bianchiFourierMode, radialGen_conjSL, neg_neg]
  rw [← h₁, casimirOne_clm_comp L (isLieSmooth_bianchiLift_bianchiFourierMode μ hφ).comp_conjSL,
    casimirOne_comp_conjSL, h]
  funext g
  simp only [Function.comp_apply, Pi.smul_apply, map_smul]

end HyperbolicThreeSpace
