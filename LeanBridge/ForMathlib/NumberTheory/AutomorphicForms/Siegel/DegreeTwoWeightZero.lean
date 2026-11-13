import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoWitt
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.QuasiModularDepth
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable

/-!
# The vanishing of `N_{j,0}(Γ₂)` for `j > 0`

Let `F ∈ M_{j,0}(Γ₂)` have weight `Sym^j` (`k = 0`) and Fourier coefficients `a`, and let `ψ₀`,
`ψ₁` be the linear forms on `Sym^j(ℂ²)` reading off the constant and linear coefficients of the
dehomogenisation `u₁ ⋯ u_j ↦ ∏ᵢ (uᵢ₀ + uᵢ₁ X)`. The Witt restriction `τ₂ ↦ ψ₀(F(diag(τ₁, τ₂)))` is
a modular form of weight `0`, hence the constant `Φ(F)(τ₁)`. The derivative
`D(τ₁, τ₂) = ∂_z ψ₁(F(τ₁, z; z, τ₂))` at `z = 0` is the series
`∑ ψ₁(a(n)) 2πi 2n₀₁ e^{2πi(n₀₀ τ₁ + n₁₁ τ₂)}`, holomorphic and bounded at `i∞` in `τ₂`, with
limit `0`; the second embedding of `g = (a, b; c, d) ∈ SL(2, ℤ)` has automorphy factor
`(1, 0; cz, cτ₂ + d)`, on which `ψ₁ ∘ Sym^j` is `jcz ψ₀ + (cτ₂ + d) ψ₁`, and differentiating the
transformation law of `F` in `z` at `z = 0` gives
`D(τ₁, gτ₂) = (cτ₂ + d)² D(τ₁, τ₂) + jc(cτ₂ + d) Φ(F)(τ₁)`. This is the transformation law of a
multiple of `E₂`, which transforms with the correction `-κc(cτ₂ + d)`, `κ = 2πi / 2ζ(2)`, so
`D(τ₁, ·) + (j Φ(F)(τ₁) / κ) E₂` is a modular form of weight `2` on `SL(2, ℤ)`, hence `0`. Its
limit at `i∞` is `j Φ(F)(τ₁) / κ`, so `Φ(F) = 0` for `j > 0`, and `N_{j,0}(Γ₂) = 0`, the Siegel
operator being injective on it.

Together with `LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoWitt` (`k = 2`
and `k < 0`) and the known vanishing for odd `k`, this proves `N_{j,k}(Γ₂) = 0` for every `k < 4`
apart from `(j, k) = (0, 0)`, where `N_{0,0}(Γ₂)` is the space of constants (not proved here). This
is the claim behind the corrected range `k > 4` and `(j, k) = (0, 4)` of the decomposition
`N_{j,k}(Γ₂) = E_{j,k}(Γ₂) ⊕ KE_{j,k}(Γ₂)` of the knowl `mf.siegel.subspace.degree.two`, the
weights `(10, 2)`, `(12, 0)` and `(16, -2)` among them. In these weights `E_{j,k}(Γ₂)` vanishes
for `j > 0` (`SiegelUpperHalfSpace.siegelEisensteinSubspaceKJ_eq_bot`), but `E_{0,k}(Γ₂)` and
`KE_{j,k}(Γ₂)`, spanned by series shown to converge only for `k > 3` and `k > 4`, are not shown to
vanish.

## Main definitions

* `SiegelUpperHalfSpace.symLinearCoeff`: the linear form `ψ₁` on `Sym^j(ℂ²)`.
* `SiegelUpperHalfSpace.offDiagMultiplier`: the multiplier `n ↦ 2πi 2n₀₁`.

## Main results

* `SiegelUpperHalfSpace.symLinearCoeff_rhoKJ`: `ψ₁ ∘ ρ_{k,j}` on the lower triangular matrices.
* `SiegelUpperHalfSpace.hasDerivAt_tsum_entriesExp`: the series of Fourier coefficients along the
  curves `(p + αz², βz; βz, r)` may be differentiated termwise at `z = 0`.
* `SiegelUpperHalfSpace.diagSeries_symLinearCoeff_smul`: the transformation law of `D(τ₁, ·)`.
* `SiegelUpperHalfSpace.siegelOperatorSeries_eq_zero_of_weight_zero`: `Φ(F) = 0` for
  `F ∈ M_{j,0}(Γ₂)`, `j > 0`.
* `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_eq_bot_of_weight_zero` (LMFDB
  `mf.siegel.subspace.degree.two`): `N_{j,0}(Γ₂) = 0` for `j > 0`.
* `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_eq_bot_of_lt_four` (LMFDB
  `mf.siegel.subspace.degree.two`): `N_{j,k}(Γ₂) = 0` for `k < 4` and `(j, k) ≠ (0, 0)`.

## References

* M. Eichler and D. Zagier, *The theory of Jacobi forms*, Progress in Mathematics 55, Birkhäuser
  (1985), §3, for the Taylor expansion of Jacobi forms in `z`.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open Complex EisensteinSeries Filter Module Polynomial Real SymplecticGroup Topology

open scoped ComplexOrder Manifold MatrixGroups ModularForm TensorProduct UpperHalfPlane

namespace SiegelUpperHalfSpace

/-! ### The linear form `ψ₁` -/

variable {k : ℤ} {j : ℕ}

private lemma coeff_one_prod_C_add_C_mul_X {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b : ι → ℂ) :
    (∏ i ∈ s, (C (a i) + C (b i) * X)).coeff 1 = ∑ i ∈ s, b i * ∏ l ∈ s.erase i, a l := by
  induction s using Finset.induction_on with
  | empty => simp [coeff_one]
  | insert i s hi ih =>
    have h₁ : (X * ∏ l ∈ s, (C (a l) + C (b l) * X)).coeff 1 =
        (∏ l ∈ s, (C (a l) + C (b l) * X)).coeff 0 := by
      simp
    have h₀ : (∏ l ∈ s, (C (a l) + C (b l) * X)).coeff 0 = ∏ l ∈ s, a l := by
      rw [coeff_zero_eq_eval_zero, eval_prod]
      simp
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.erase_insert hi, add_mul, coeff_add,
      coeff_C_mul, ih, mul_assoc, coeff_C_mul, h₁, h₀, Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hl hi).symm,
      Finset.prod_insert fun h ↦ hi (Finset.mem_of_mem_erase h)]
    ring1

variable (j) in
/-- The linear form `ψ₁` on `Sym^j(ℂ²)` reading off the coefficient of `X` of the dehomogenisation
`u₁ ⋯ u_j ↦ ∏ᵢ (uᵢ₀ + uᵢ₁ X)`, the coordinate of `e₁^{j-1} e₂` in the basis of monomials. -/
noncomputable def symLinearCoeff : Dual ℂ (Sym[ℂ]^j (Fin 2 → ℂ)) :=
  lcoeff ℂ 1 ∘ₗ symDehomogenize j

lemma symLinearCoeff_tprod (u : Fin j → Fin 2 → ℂ) :
    symLinearCoeff j (⨂ₛ[ℂ] i, u i) = ∑ i, u i 1 * ∏ l ∈ Finset.univ.erase i, u l 0 := by
  rw [symLinearCoeff, LinearMap.comp_apply, symDehomogenize_tprod, lcoeff_apply,
    coeff_one_prod_C_add_C_mul_X]

/-- **`ψ₁ ∘ ρ_{k,j}` on the lower triangular matrices**: for `A = (1, 0; x, w)`,
`ψ₁(ρ_{k,j}(A) v) = w^k (j x ψ₀(v) + w ψ₁(v))`. -/
lemma symLinearCoeff_rhoKJ {x w : ℂ} {A : GL (Fin 2) ℂ}
    (hA : (A : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; x, w]) (v : Sym[ℂ]^j (Fin 2 → ℂ)) :
    symLinearCoeff j (rhoKJ k j A v) =
      w ^ k * (j * x * symConstCoeff j v + w * symLinearCoeff j v) := by
  have hv : v ∈ Submodule.span ℂ (Set.range (SymmetricPower.tprod ℂ)) := by
    rw [SymmetricPower.span_tprod_eq_top]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨m, rfl⟩
    have h₀ (u : Fin 2 → ℂ) : ((A : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ u) 0 = u 0 := by
      simp [hA, dotProduct]
    have h₁ (u : Fin 2 → ℂ) : ((A : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ u) 1 = x * u 0 + w * u 1 := by
      simp [hA, dotProduct]
    have hdet : ((A.det ^ k : ℂˣ) : ℂ) = w ^ k := by
      rw [Units.val_zpow_eq_zpow_val, GeneralLinearGroup.val_det_apply, hA]
      simp
    have hsum : ∑ i : Fin j, m i 0 * ∏ l ∈ Finset.univ.erase i, m l 0 = j * ∏ l, m l 0 := by
      rw [Finset.sum_congr rfl fun i _ ↦ Finset.mul_prod_erase Finset.univ (fun l ↦ m l 0)
        (Finset.mem_univ i), Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have e : ∑ i, (x * m i 0 + w * m i 1) * ∏ l ∈ Finset.univ.erase i, m l 0 =
        x * ∑ i, m i 0 * ∏ l ∈ Finset.univ.erase i, m l 0 +
          w * ∑ i, m i 1 * ∏ l ∈ Finset.univ.erase i, m l 0 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring1
    rw [rhoKJ_tprod, map_smul, symLinearCoeff_tprod, symLinearCoeff_tprod, symConstCoeff_tprod,
      hdet, smul_eq_mul]
    simp only [h₀, h₁]
    rw [e, hsum]
    ring1
  | zero => simp
  | add y y' _ _ hy hy' =>
    rw [map_add, map_add, hy, hy', map_add, map_add]
    ring1
  | smul a y _ hy =>
    rw [map_smul, map_smul, hy, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring1

/-! ### Termwise differentiation in the off-diagonal entry -/

variable {Γ : Subgroup (symplecticGroup (Fin 2) ℚ)} {d : dualLattice Γ → ℂ} (n : dualLattice Γ)
  {p r : ℂ}

/-- The multiplier `n ↦ 2πi · 2n₀₁`, the derivative in `z` at `z = 0` of
`e^{2πi(n₀₀ p + 2n₀₁ z + n₁₁ r)}` divided by its value. -/
noncomputable def offDiagMultiplier : ℂ :=
  2 * π * I * (2 * ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 : ℂ))

/-- **Termwise differentiation along `(p + αz², βz; βz, r)`**: for coefficients `d` with summable
Fourier series on `ℋ₂`, supported on positive semidefinite `n`, the derivative at `z = 0` of
`∑ d(n) e^{2πi(n₀₀ (p + αz²) + 2n₀₁ βz + n₁₁ r)}` is `β ∑ d(n) 2πi 2n₀₁ e^{2πi(n₀₀ p + n₁₁ r)}`. -/
lemma hasDerivAt_tsum_entriesExp (hs : ∀ Z, Summable fun n ↦ fourierExp n Z * d n)
    (hpsd : ∀ n, d n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) (hp : 0 < p.im)
    (hr : 0 < r.im) (α β : ℂ) :
    HasDerivAt (fun z ↦ ∑' n, d n * entriesExp n (p + α * z ^ 2) (β * z) r)
      (β * diagSeries d offDiagMultiplier p r) 0 := by
  set ρ : ℝ := min 1 (min p.im r.im / (2 * (‖α‖ + ‖β‖ + 1)))
  have hρ₀ : 0 < ρ := lt_min one_pos (div_pos (lt_min hp hr) (by positivity))
  have hρ₁ : ρ ≤ 1 := min_le_left _ _
  have hρ₂ : (‖α‖ + ‖β‖ + 1) * ρ ≤ min p.im r.im / 2 := by
    have h : ρ ≤ min p.im r.im / (2 * (‖α‖ + ‖β‖ + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have h0U : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ₀
  have hbound (n : dualLattice Γ) (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) ρ) :
      ‖d n * entriesExp n (p + α * z ^ 2) (β * z) r‖ ≤
        ‖entriesExp n ((p.im / 2 : ℝ) * I) 0 ((r.im / 2 : ℝ) * I) * d n‖ := by
    by_cases hd : d n = 0
    · simp [hd]
    have hz' : ‖z‖ < ρ := by
      simpa using hz
    have hβz : |(β * z).im| ≤ ‖β‖ * ρ :=
      (abs_im_le_norm _).trans (by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hz'.le (norm_nonneg _))
    have hαz : |(α * z ^ 2).im| ≤ ‖α‖ * ρ :=
      (abs_im_le_norm _).trans (by
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg z]) (norm_nonneg _))
    rw [norm_mul, norm_mul, mul_comm ‖d n‖]
    refine mul_le_mul_of_nonneg_right (norm_entriesExp_le (a := p.im / 2) (b := r.im / 2)
      (hpsd n hd) ?_ ?_) (norm_nonneg (d n))
    · rw [add_im]
      nlinarith [(abs_le.mp hαz).1, min_le_left p.im r.im, norm_nonneg α, norm_nonneg β]
    · nlinarith [min_le_right p.im r.im, norm_nonneg α, norm_nonneg β]
  have hsum : Summable fun n : dualLattice Γ ↦
      ‖entriesExp n ((p.im / 2 : ℝ) * I) 0 ((r.im / 2 : ℝ) * I) * d n‖ := by
    have hZ : ((0 : ℂ).im) ^ 2 < (((p.im / 2 : ℝ) : ℂ) * I).im * (((r.im / 2 : ℝ) : ℂ) * I).im := by
      simpa using mul_pos (half_pos hp) (half_pos hr)
    refine (hs (ofEntries _ _ _ (by simpa using half_pos hp) hZ)).norm.congr fun n ↦ ?_
    rw [fourierExp_of_val_eq n _ _ _ (ofEntries_val _ _ _ _ _)]
  have hdiff (n : dualLattice Γ) : DifferentiableOn ℂ
      (fun z ↦ d n * entriesExp n (p + α * z ^ 2) (β * z) r) (Metric.ball 0 ρ) := by
    unfold entriesExp
    fun_prop
  have hderiv (n : dualLattice Γ) :
      HasDerivAt (fun z ↦ d n * entriesExp n (p + α * z ^ 2) (β * z) r)
        (β * (d n * offDiagMultiplier n * entriesExp n p 0 r)) 0 := by
    have hG : HasDerivAt (fun z : ℂ ↦ 2 * π * I * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℂ) *
        (p + α * z ^ 2) + 2 * ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 : ℂ) * (β * z) +
          ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℂ) * r))
            (2 * π * I * (2 * ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 : ℂ) * β)) 0 := by
      convert (((((hasDerivAt_pow 2 (0 : ℂ)).const_mul α).const_add p).const_mul
        ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℂ)).add
          (((hasDerivAt_id (0 : ℂ)).const_mul β).const_mul
            (2 * ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 : ℂ)))).add_const
              (((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℂ) * r) |>.const_mul (2 * π * I) using 1 <;>
        norm_num
    have he : cexp (2 * π * I * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℂ) * (p + α * 0 ^ 2) +
        2 * ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 : ℂ) * (β * 0) +
          ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℂ) * r)) = entriesExp n p 0 r := by
      simp [entriesExp]
    convert hG.cexp.const_mul (d n) using 1
    · rfl
    · rw [he, offDiagMultiplier]
      ring1
  have h₁ : HasSum (fun n ↦ deriv (fun z ↦ d n * entriesExp n (p + α * z ^ 2) (β * z) r) 0)
      (deriv (fun z ↦ ∑' n, d n * entriesExp n (p + α * z ^ 2) (β * z) r) 0) :=
    hasSum_deriv_of_summable_norm hsum hdiff hU hbound h0U
  have h₂ : DifferentiableAt ℂ (fun z ↦ ∑' n, d n * entriesExp n (p + α * z ^ 2) (β * z) r) 0 :=
    (differentiableOn_tsum_of_summable_norm hsum hdiff hU hbound).differentiableAt
      (hU.mem_nhds h0U)
  have h₃ : deriv (fun z ↦ ∑' n, d n * entriesExp n (p + α * z ^ 2) (β * z) r) 0 =
      β * diagSeries d offDiagMultiplier p r := by
    rw [← h₁.tsum_eq, diagSeries, ← tsum_mul_left]
    exact tsum_congr fun n ↦ (hderiv n).deriv
  exact h₃ ▸ h₂.hasDerivAt

private lemma norm_offDiagMultiplier_le
    (hpsd : ∀ n, d n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) (hn : d n ≠ 0) :
    ‖offDiagMultiplier n‖ ≤ 2 * π * (1 + ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) +
      ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ)) := by
  have h : |2 * ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 : ℝ)| ≤
      ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) + ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) := by
    exact_mod_cast abs_two_mul_apply_zero_one_le (hpsd n hn)
  have e : ‖offDiagMultiplier n‖ = 2 * π * |2 * ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 : ℝ)| := by
    simp [offDiagMultiplier]
  rw [e]
  nlinarith [Real.pi_pos]

private lemma offDiagMultiplier_eq_zero
    (hpsd : ∀ n, d n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) (hn : d n ≠ 0)
    (h : (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0) : offDiagMultiplier n = 0 := by
  simp [offDiagMultiplier, apply_zero_one_eq_zero (hpsd n hn) h]

/-! ### The first Taylor coefficient in the off-diagonal entry -/

variable {F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)}
  {b : dualLattice (integral (Fin 2)) → Sym[ℂ]^j (Fin 2 → ℂ)} (g : SL(2, ℤ)) (τ₁ τ₂ : ℍ)

/-- **The transformation law of the first Taylor coefficient**: for `F ∈ M_{j,0}(Γ₂)`, the
derivative `D(τ₁, τ₂)` at `z = 0` of `ψ₁(F(τ₁, z; z, τ₂))` satisfies
`D(τ₁, gτ₂) = (cτ₂ + d)² D(τ₁, τ₂) + jc(cτ₂ + d) ψ₀(F(diag(τ₁, τ₂)))` for
`g = (a, b; c, d) ∈ SL(2, ℤ)`, by differentiating the transformation law of `F` under the second
embedding of `g` in `z` at `z = 0`. -/
lemma diagSeries_symLinearCoeff_smul (hF : F ∈ modularFormsKJ 0 j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) :
    diagSeries (fun n ↦ symLinearCoeff j (b n)) offDiagMultiplier τ₁ (g • τ₂ : ℍ) =
      ((g 1 0 : ℂ) * τ₂ + g 1 1) ^ 2 *
        diagSeries (fun n ↦ symLinearCoeff j (b n)) offDiagMultiplier τ₁ τ₂ +
          j * g 1 0 * ((g 1 0 : ℂ) * τ₂ + g 1 1) *
            diagSeries (fun n ↦ symConstCoeff j (b n)) 1 τ₁ τ₂ := by
  set W : ℂ := (g 1 0 : ℂ) * τ₂ + g 1 1
  have hW₀ : W ≠ 0 := by
    have h : UpperHalfPlane.denom g τ₂ ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ₂
    simpa [UpperHalfPlane.denom] using h
  have hpsd₀ : ∀ n, symConstCoeff j (b n) ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef :=
    (posSemidef_of_dual_apply_ne_zero · hF hb _)
  have hpsd₁ : ∀ n, symLinearCoeff j (b n) ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef :=
    (posSemidef_of_dual_apply_ne_zero · hF hb _)
  have hL : HasDerivAt (fun z ↦ ∑' n, symLinearCoeff j (b n) *
      entriesExp n (τ₁ + -(g 1 0 : ℂ) / W * z ^ 2) (W⁻¹ * z) (g • τ₂ : ℍ))
        (W⁻¹ * diagSeries (fun n ↦ symLinearCoeff j (b n)) offDiagMultiplier τ₁ (g • τ₂ : ℍ)) 0 :=
    hasDerivAt_tsum_entriesExp (fun Z ↦ (hb Z _).summable) hpsd₁ τ₁.im_pos (g • τ₂).im_pos _ _
  have hS₀ : HasDerivAt (fun z ↦ ∑' n, symConstCoeff j (b n) * entriesExp n τ₁ z τ₂)
      (diagSeries (fun n ↦ symConstCoeff j (b n)) offDiagMultiplier τ₁ τ₂) 0 := by
    simpa using hasDerivAt_tsum_entriesExp (fun Z ↦ (hb Z _).summable) hpsd₀ τ₁.im_pos
      τ₂.im_pos 0 1
  have hS₁ : HasDerivAt (fun z ↦ ∑' n, symLinearCoeff j (b n) * entriesExp n τ₁ z τ₂)
      (diagSeries (fun n ↦ symLinearCoeff j (b n)) offDiagMultiplier τ₁ τ₂) 0 := by
    simpa using hasDerivAt_tsum_entriesExp (fun Z ↦ (hb Z _).summable) hpsd₁ τ₁.im_pos
      τ₂.im_pos 0 1
  have hR : HasDerivAt (fun z ↦ j * (g 1 0 * z) * ∑' n, symConstCoeff j (b n) *
      entriesExp n τ₁ z τ₂ + W * ∑' n, symLinearCoeff j (b n) * entriesExp n τ₁ z τ₂)
        (j * g 1 0 * diagSeries (fun n ↦ symConstCoeff j (b n)) 1 τ₁ τ₂ +
          W * diagSeries (fun n ↦ symLinearCoeff j (b n)) offDiagMultiplier τ₁ τ₂) 0 := by
    convert ((((hasDerivAt_id (0 : ℂ)).const_mul (g 1 0 : ℂ)).const_mul (j : ℂ)).mul hS₀).add
      (hS₁.const_mul W) using 1
    · rfl
    · simp [diagSeries]
  have hopen : {z : ℂ | z.im ^ 2 < (τ₁ : ℂ).im * (τ₂ : ℂ).im} ∈ 𝓝 0 :=
    IsOpen.mem_nhds (isOpen_lt (continuous_im.pow 2) continuous_const)
      (by simpa using mul_pos τ₁.im_pos τ₂.im_pos)
  have heq : (fun z ↦ ∑' n, symLinearCoeff j (b n) *
      entriesExp n (τ₁ + -(g 1 0 : ℂ) / W * z ^ 2) (W⁻¹ * z) (g • τ₂ : ℍ)) =ᶠ[𝓝 0]
        fun z ↦ j * (g 1 0 * z) * ∑' n, symConstCoeff j (b n) * entriesExp n τ₁ z τ₂ +
          W * ∑' n, symLinearCoeff j (b n) * entriesExp n τ₁ z τ₂ := by
    filter_upwards [hopen] with z (hz : z.im ^ 2 < (τ₁ : ℂ).im * (τ₂ : ℂ).im)
    have hZ : (ofEntries (τ₁ : ℂ) z τ₂ τ₁.im_pos hz).val = !![(τ₁ : ℂ), z; z, (τ₂ : ℂ)] :=
      ofEntries_val (τ₁ : ℂ) z τ₂ τ₁.im_pos hz
    have hγZ : (SymplecticGroup.map (Int.castRingHom ℝ) (embedSecond g) •
        ofEntries (τ₁ : ℂ) z τ₂ τ₁.im_pos hz).val =
          !![(τ₁ : ℂ) + -(g 1 0 : ℂ) / W * z ^ 2, W⁻¹ * z; W⁻¹ * z, ((g • τ₂ : ℍ) : ℂ)] := by
      rw [val_smul_embedSecond, hZ, UpperHalfPlane.coe_specialLinearGroup_apply]
      ext a c
      fin_cases a <;> fin_cases c <;> simp <;> ring1
    have hD : (denomGL (SymplecticGroup.map (Int.castRingHom ℝ) (embedSecond g))
        (ofEntries (τ₁ : ℂ) z τ₂ τ₁.im_pos hz) : Matrix (Fin 2) (Fin 2) ℂ) =
          !![1, 0; (g 1 0 : ℂ) * z, W] := by
      rw [coe_denomGL_embedSecond, hZ]
      simp
      rfl
    have hmod : F (SymplecticGroup.map (Int.castRingHom ℝ) (embedSecond g) •
        ofEntries (τ₁ : ℂ) z τ₂ τ₁.im_pos hz) = rhoKJ 0 j (denomGL (SymplecticGroup.map
          (Int.castRingHom ℝ) (embedSecond g)) (ofEntries (τ₁ : ℂ) z τ₂ τ₁.im_pos hz))
            (F (ofEntries (τ₁ : ℂ) z τ₂ τ₁.im_pos hz)) := by
      simpa only [map_algebraMap_map_intCast, MonoidHom.one_apply, Units.val_one, one_smul] using
        hF.2 ⟨_, embedSecond g, trivial, rfl⟩ (ofEntries (τ₁ : ℂ) z τ₂ τ₁.im_pos hz)
    rw [← dual_apply_eq_tsum_entriesExp hb (symLinearCoeff j) hγZ, hmod, symLinearCoeff_rhoKJ hD,
      dual_apply_eq_tsum_entriesExp hb (symConstCoeff j) hZ,
      dual_apply_eq_tsum_entriesExp hb (symLinearCoeff j) hZ, zpow_zero, one_mul]
  have key : W⁻¹ * diagSeries (fun n ↦ symLinearCoeff j (b n)) offDiagMultiplier τ₁ (g • τ₂ : ℍ) =
      j * g 1 0 * diagSeries (fun n ↦ symConstCoeff j (b n)) 1 τ₁ τ₂ +
        W * diagSeries (fun n ↦ symLinearCoeff j (b n)) offDiagMultiplier τ₁ τ₂ :=
    hL.unique (hR.congr_of_eventuallyEq heq)
  linear_combination W * key -
    diagSeries (fun n ↦ symLinearCoeff j (b n)) offDiagMultiplier τ₁ (g • τ₂ : ℍ) *
      mul_inv_cancel₀ hW₀

/-! ### The comparison with `E₂` -/

/-- The constant `κ = 6i / π = 2πi / 2ζ(2)` of the transformation law of `E₂`. -/
private noncomputable def e2Correction : ℂ :=
  6 * I / π

private lemma e2Correction_ne_zero : e2Correction ≠ 0 :=
  div_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) (ofReal_ne_zero.mpr Real.pi_ne_zero)

/-- **`Φ(F) = 0` for `F ∈ M_{j,0}(Γ₂)` with `j > 0`**: the Witt restriction `ψ₀(F(diag(τ₁, ·)))`
is a modular form of weight `0`, hence the constant `Φ(F)(τ₁)`, and then
`D(τ₁, ·) + (j Φ(F)(τ₁) / κ) E₂`, `κ = 2πi / 2ζ(2)`, is a modular form of weight `2` on
`SL(2, ℤ)`, hence `0`; its limit `j Φ(F)(τ₁) / κ` at `i∞` vanishes. -/
lemma siegelOperatorSeries_eq_zero_of_weight_zero (hF : F ∈ modularFormsKJ 0 j (integral (Fin 2)))
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) (hj : j ≠ 0) :
    siegelOperatorSeries b τ₁ = 0 := by
  rcases ModularFormClass.levelOne_weight_zero_const (wittForm τ₁ hF hb) with ⟨u, hu⟩
  have hu' : u = siegelOperatorSeries b τ₁ := by
    have h : Tendsto (Function.const ℍ u) UpperHalfPlane.atImInfty
        (𝓝 (siegelOperatorSeries b τ₁)) :=
      hu ▸ tendsto_wittForm_atImInfty τ₁ hF hb
    exact tendsto_nhds_unique tendsto_const_nhds h
  have hX (τ : ℍ) : diagSeries (fun n ↦ symConstCoeff j (b n)) 1 τ₁ τ = u := by
    rw [← coe_wittForm τ₁ τ hF hb, hu, Function.const_apply]
  have hs₁ (Z : SiegelUpperHalfSpace (Fin 2)) :
      Summable fun n ↦ fourierExp n Z * symLinearCoeff j (b n) :=
    (hb Z _).summable
  have hpsd₁ : ∀ n, symLinearCoeff j (b n) ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef :=
    (posSemidef_of_dual_apply_ne_zero · hF hb _)
  have hm₁ : ∀ n, symLinearCoeff j (b n) ≠ 0 → ‖offDiagMultiplier n‖ ≤
      2 * π * (1 + ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) +
        ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ)) :=
    (norm_offDiagMultiplier_le · hpsd₁)
  have hslash (g : SL(2, ℤ)) : (fun τ : ℍ ↦
      diagSeries (fun n ↦ symLinearCoeff j (b n)) offDiagMultiplier τ₁ τ +
        j * u / e2Correction * E2 τ) ∣[(2 : ℤ)] g = fun τ : ℍ ↦
          diagSeries (fun n ↦ symLinearCoeff j (b n)) offDiagMultiplier τ₁ τ +
            j * u / e2Correction * E2 τ := by
    ext τ
    have hw : UpperHalfPlane.denom g τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
    have e : UpperHalfPlane.denom g τ = (g 1 0 : ℂ) * τ + g 1 1 := by
      simp [UpperHalfPlane.denom]
    rw [e] at hw
    rw [ModularForm.SL_slash_apply, ModularForm.E2_smul, e,
      diagSeries_symLinearCoeff_smul g τ₁ τ hF hb, hX, e2Correction]
    field_simp
    ring1
  have hmdiff : MDiff fun τ : ℍ ↦
      diagSeries (fun n ↦ symLinearCoeff j (b n)) offDiagMultiplier τ₁ τ +
        j * u / e2Correction * E2 τ := by
    refine MDifferentiable.add ?_ (mdifferentiable_const.mul E2_mdifferentiable)
    refine UpperHalfPlane.mdifferentiable_iff.mpr ((differentiableOn_diagSeries (τ₁ : ℂ) hs₁ hpsd₁
      hm₁ τ₁.im_pos).congr fun z hz ↦ ?_)
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty fun τ : ℍ ↦
      diagSeries (fun n ↦ symLinearCoeff j (b n)) offDiagMultiplier τ₁ τ +
        j * u / e2Correction * E2 τ :=
    (isBoundedAtImInfty_diagSeries (τ₁ : ℂ) hs₁ hpsd₁ hm₁ τ₁.im_pos).add
      ((const_boundedAtFilter _ _).mul isBoundedAtImInfty_E2)
  let f : ModularForm 𝒮ℒ 2 :=
    { toFun τ := diagSeries (fun n ↦ symLinearCoeff j (b n)) offDiagMultiplier τ₁ τ +
        j * u / e2Correction * E2 τ
      slash_action_eq' := fun _ ⟨g, hg⟩ ↦ hg ▸ hslash g
      holo' := hmdiff
      bdd_at_cusps' := fun hc ↦ (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun g _ ↦
        (hslash g).symm ▸ hbdd }
  have hf : f = 0 := (rank_zero_iff.mp ModularForm.levelOne_weight_two_rank_zero).elim _ _
  have hD : Tendsto (fun τ : ℍ ↦
      diagSeries (fun n ↦ symLinearCoeff j (b n)) offDiagMultiplier τ₁ τ)
        UpperHalfPlane.atImInfty (𝓝 0) := by
    have e : (∑' n : dualLattice (integral (Fin 2)), if (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0 then
        symLinearCoeff j (b n) * offDiagMultiplier n *
          cexp (2 * π * I * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℂ) * τ₁)) else 0) = 0 := by
      refine (tsum_congr fun n ↦ ?_).trans tsum_zero
      split_ifs with h₁₁
      · by_cases hn : symLinearCoeff j (b n) = 0
        · simp [hn]
        · simp [offDiagMultiplier_eq_zero n hpsd₁ hn h₁₁]
      · rfl
    exact e ▸ tendsto_diagSeries_atImInfty (τ₁ : ℂ) hs₁ hpsd₁ hm₁ τ₁.im_pos
  have h₀ : Tendsto (fun τ : ℍ ↦
      diagSeries (fun n ↦ symLinearCoeff j (b n)) offDiagMultiplier τ₁ τ +
        j * u / e2Correction * E2 τ) UpperHalfPlane.atImInfty (𝓝 0) := by
    have e : (fun τ : ℍ ↦ diagSeries (fun n ↦ symLinearCoeff j (b n)) offDiagMultiplier τ₁ τ +
        j * u / e2Correction * E2 τ) = f :=
      rfl
    rw [e, hf]
    exact tendsto_const_nhds
  have h₁ : 0 + j * u / e2Correction * 1 = 0 :=
    tendsto_nhds_unique (hD.add (tendsto_E2_atImInfty.const_mul (j * u / e2Correction))) h₀
  rw [zero_add, mul_one, div_eq_zero_iff, or_iff_left e2Correction_ne_zero, mul_eq_zero,
    or_iff_right (Nat.cast_ne_zero.mpr hj)] at h₁
  rw [← hu', h₁]

/-! ### The vanishing of `N_{j,k}(Γ₂)` -/

variable {c : Sym[ℂ]^j (Fin 2 → ℂ) →ₗ[ℂ] Sym[ℂ]^j (Fin 2 → ℂ) →ₗ⋆[ℂ] ℂ}

/-- **`N_{j,0}(Γ₂) = 0` for `j > 0`** (LMFDB `mf.siegel.subspace.degree.two`), for an admissible
positive definite form `c`: the Siegel operator vanishes on `M_{j,0}(Γ₂)` and is injective on
`N_{j,0}(Γ₂)`. -/
lemma cuspFormsOrthogonalKJ_eq_bot_of_weight_zero (hadm : IsAdmissibleForm (rhoKJ 0 j) c)
    (hpos : ∀ v, v ≠ 0 → 0 < c v v) (hj : j ≠ 0) :
    cuspFormsOrthogonalKJ (integral (Fin 2)) 0 j c = ⊥ :=
  cuspFormsOrthogonalKJ_eq_bot_of_forall_siegelOperatorSeries_eq_zero hadm hpos fun _ hG _ ha τ' ↦
    siegelOperatorSeries_eq_zero_of_weight_zero τ' hG ha hj

/-- **`N_{j,k}(Γ₂) = 0` for `k < 4` and `(j, k) ≠ (0, 0)`** (LMFDB
`mf.siegel.subspace.degree.two`), for an admissible positive definite form `c`: for odd `k`
there are no non-cusp forms, for `k = 2` and `k < 0` the Witt restrictions vanish, and for `k = 0`
the Siegel operator vanishes by the comparison with `E₂`. This is the claim behind the corrected
range `k > 4` and `(j, k) = (0, 4)` of the decomposition
`N_{j,k}(Γ₂) = E_{j,k}(Γ₂) ⊕ KE_{j,k}(Γ₂)`. -/
lemma cuspFormsOrthogonalKJ_eq_bot_of_lt_four (hadm : IsAdmissibleForm (rhoKJ k j) c)
    (hpos : ∀ v, v ≠ 0 → 0 < c v v) (hk : k < 4) (hjk : j ≠ 0 ∨ k ≠ 0) :
    cuspFormsOrthogonalKJ (integral (Fin 2)) k j c = ⊥ := by
  rcases Int.even_or_odd k with hk' | hk'
  · rcases lt_trichotomy k 0 with h | rfl | h
    · exact cuspFormsOrthogonalKJ_eq_bot_of_neg hadm hpos h
    · exact cuspFormsOrthogonalKJ_eq_bot_of_weight_zero hadm hpos (hjk.resolve_right (by simp))
    · have h₂ : k = 2 := by
        rcases hk' with ⟨m, rfl⟩
        omega
      subst h₂
      exact cuspFormsOrthogonalKJ_two_eq_bot hadm hpos
  · exact cuspFormsOrthogonalKJ_eq_bot_of_odd hadm hpos hk'

end SiegelUpperHalfSpace
