import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.PoincareConvergence

/-!
# Poincaré series of every index converge

The `n`-th Poincaré series of weight `k` and multiplier `v` on `G ≤ SL(2, ℤ)` at the cusp
`s = γ_s ∞` of width `w` (LMFDB `specialfunction.poincare`) is
`P(z) = Σ_{g ∈ G_s \ G} conj(v(g)) e^{2πi (n/w) γ_s⁻¹ g z} j(γ_s⁻¹ g, z)^{-k}`
(`ModularForm.poincareSeries`). For `k ≥ 3` it converges absolutely and locally uniformly, and is
holomorphic on `ℍ`, for every `n ∈ ℤ`: `PoincareConvergence.lean` proves this for `n ≥ 0`, where
the exponential factors have modulus at most `1`, and this file for every `n`. For `M ∈ SL(2, ℤ)`
with bottom row `(c, d)`, `Im(M z) = y / |cz + d|²` is `y` when `c = 0` (then `d = ±1`) and at most
`1 / y` otherwise (`|cz + d| ≥ |c| y ≥ y`), so `Im(M z) ≤ y + y⁻¹`, and the exponential factor of
each term has modulus at most `e^{2π |n| (y + y⁻¹) / w}`, a bound uniform on compact sets. The
comparison with the Eisenstein series of weight `k` then goes through as for `n ≥ 0`. So the
series is never a junk value of the unconditional sum, for any index `n`; for `n ≥ 1` it is a cusp
form (`PoincareCuspForm.lean`), for `n = 0` the Eisenstein series at `s`, and for `n < 0` it grows
like `e^{2π |n| y / w}` at `s`.

## Main results

* `ModularForm.summable_norm_poincareTerm_of_three_le`,
  `ModularForm.hasSum_poincareSeries_of_three_le`: for `k ≥ 3` and every `n` the series converges
  absolutely, to `ModularForm.poincareSeries`.
* `ModularForm.tendstoLocallyUniformly_poincareSeries_of_three_le`,
  `ModularForm.mdifferentiable_poincareSeries_of_three_le`: for `k ≥ 3` and every `n` the series
  converges locally uniformly, and is holomorphic on `ℍ`.
-/

open UpperHalfPlane Matrix SpecialLinearGroup EisensteinSeries ModularGroup

open scoped MatrixGroups ComplexConjugate Manifold

namespace ModularGroup

lemma im_smul_le_im_add_inv (M : SL(2, ℤ)) (z : ℍ) : (M • z).im ≤ z.im + z.im⁻¹ := by
  have hy : 0 < z.im := z.im_pos
  rw [im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
  rcases eq_or_ne (M 1 0) 0 with hc | hc
  · have hdet : M 0 0 * M 1 1 = 1 := by
      have hM : (M : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := M.det_coe
      rwa [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hM
    have hd : |(M 1 1 : ℝ)| = 1 := by
      exact_mod_cast Int.isUnit_iff_abs_eq.mp (IsUnit.of_mul_eq_one_right _ hdet)
    have hden : ‖denom M z‖ = 1 := by
      rw [denom_apply, hc]
      simpa using hd
    rw [hden, one_pow, div_one]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hy.le)
  · have hyden : z.im ≤ ‖denom M z‖ := by
      rw [denom_apply]
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      have h1 : (1 : ℝ) ≤ |(M 1 0 : ℝ)| := by exact_mod_cast Int.one_le_abs hc
      simpa [abs_of_pos hy] using le_mul_of_one_le_left hy.le h1
    refine le_trans ?_ (le_add_of_nonneg_left hy.le)
    refine (div_le_div_of_nonneg_left hy.le (pow_pos hy 2)
      (pow_le_pow_left₀ hy.le hyden 2)).trans_eq ?_
    field_simp

end ModularGroup

namespace ModularForm

variable {G : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ)) (v : G →* Circle) {k : ℤ} (n : ℤ) (w : ℕ) (z : ℍ)
    (g : G)

variable {n w} in
lemma norm_exp_le_of_im_le {b : ℝ} (hz : z.im ≤ b) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (n / w) * z)‖ ≤
      Real.exp (2 * Real.pi * (|(n : ℝ)| / w) * b) := by
  have hy : 0 < z.im := z.im_pos
  have h1 : -((n : ℝ) / w) ≤ |(n : ℝ)| / w := by
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (neg_le_abs _) (Nat.cast_nonneg _)
  have h2 : -((n : ℝ) / w) * z.im ≤ |(n : ℝ)| / w * b :=
    (mul_le_mul_of_nonneg_right h1 hy.le).trans (mul_le_mul_of_nonneg_left hz (by positivity))
  have h3 : -(2 * Real.pi * (n / w) * z.im) ≤ 2 * Real.pi * (|(n : ℝ)| / w) * b := by
    linarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  rw [Complex.norm_exp]
  simpa using h3

variable {n w z} in
lemma norm_poincareTerm_le_exp_mul : ‖poincareTerm γ v k n w z g‖ ≤
    Real.exp (2 * Real.pi * (|(n : ℝ)| / w) * (z.im + z.im⁻¹)) *
        ‖eisSummand k ![(γ⁻¹ * (g : SL(2, ℤ))) 1 0, (γ⁻¹ * (g : SL(2, ℤ))) 1 1] z‖ := by
  have hden : denom (γ⁻¹ * (g : SL(2, ℤ))) z ^ (-k) =
      eisSummand k ![(γ⁻¹ * (g : SL(2, ℤ))) 1 0, (γ⁻¹ * (g : SL(2, ℤ))) 1 1] z := by
    rw [← map_mul, ← map_mul, denom_apply]
    simp [eisSummand]
  rw [poincareTerm, norm_mul, norm_mul, Complex.norm_conj, Circle.norm_coe, one_mul, hden]
  exact mul_le_mul_of_nonneg_right (norm_exp_le_of_im_le _ (im_smul_le_im_add_inv _ z))
    (norm_nonneg _)

/-- **Poincaré series of weight `k ≥ 3` converge absolutely for every index `n ∈ ℤ`** (LMFDB
`specialfunction.poincare`), by comparison with the Eisenstein series of weight `k`: the term at
`g` is at most `e^{2π |n| (y + y⁻¹) / w}` times the Eisenstein term of the bottom row of
`γ_s⁻¹ g`, and these rows are distinct over the cosets `G_s g`. -/
lemma summable_norm_poincareTerm_of_three_le (hk : 3 ≤ k) : Summable
    fun q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) ↦
      ‖poincareTerm γ v k n w z q.out‖ :=
  ((summable_norm_eisSummand hk z).comp_injective (injective_poincareBottomRow γ)).mul_left
    (Real.exp (2 * Real.pi * (|(n : ℝ)| / w) * (z.im + z.im⁻¹)))
  |>.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun q ↦ norm_poincareTerm_le_exp_mul γ v q.out

/-- **Poincaré series of weight `k ≥ 3` converge for every index `n ∈ ℤ`** (LMFDB
`specialfunction.poincare`): `ModularForm.poincareSeries` is the sum of its terms, never a junk
value of the unconditional sum. -/
lemma hasSum_poincareSeries_of_three_le (hk : 3 ≤ k) : HasSum
    (fun q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) ↦
      poincareTerm γ v k n w z q.out) (poincareSeries γ v k n w z) :=
  (summable_norm_poincareTerm_of_three_le γ v n w z hk).of_norm.hasSum

/-- **Poincaré series of weight `k ≥ 3` converge locally uniformly on `ℍ` for every index
`n ∈ ℤ`**, by the Weierstrass test: on a compact set `K`, inside a vertical strip
`{|Re z| ≤ A, Im z ≥ B}` with `Im z ≤ Y`, the term at `g` is at most `e^{2π |n| (Y + B⁻¹) / w}`
times the Eisenstein bound `r^{-k} ‖(c, d)‖^{-k}` of the bottom row of `γ_s⁻¹ g`. -/
lemma tendstoLocallyUniformly_poincareSeries_of_three_le (hk : 3 ≤ k) : TendstoLocallyUniformly
    (fun s : Finset (Quotient (QuotientGroup.rightRel (cuspStabilizer G γ))) ↦
      (∑ q ∈ s, poincareTerm γ v k n w · q.out)) (poincareSeries γ v k n w ·) Filter.atTop := by
  have hk' : (2 : ℝ) < k := by
    norm_cast
  have p_sum : Summable fun q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) ↦
      ‖![(γ⁻¹ * (q.out : SL(2, ℤ))) 1 0, (γ⁻¹ * (q.out : SL(2, ℤ))) 1 1]‖ ^ (-k : ℝ) :=
    (summable_one_div_norm_rpow hk').comp_injective (injective_poincareBottomRow γ)
  refine tendstoLocallyUniformly_iff_forall_isCompact.mpr fun K hK ↦ ?_
  rcases subset_verticalStrip_of_isCompact hK with ⟨A, B, hB, HABK⟩
  rcases hK.bddAbove_image continuous_im.continuousOn with ⟨Y, hY⟩
  refine tendstoUniformlyOn_tsum (((p_sum.mul_left (r ⟨⟨A, B⟩, hB⟩ ^ (-k : ℝ))).mul_left
    (Real.exp (2 * Real.pi * (|(n : ℝ)| / w) * (Y + B⁻¹))))) fun q z hz ↦
      (norm_poincareTerm_le_exp_mul γ v q.out).trans ?_
  have hz' : z ∈ verticalStrip A B := HABK hz
  have him : z.im + z.im⁻¹ ≤ Y + B⁻¹ := add_le_add (hY ⟨z, hz, rfl⟩) (inv_anti₀ hB hz'.2)
  refine mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left him (by positivity))) ?_
    (norm_nonneg _) (Real.exp_pos _).le
  simpa only [eisSummand, norm_zpow, ← Real.rpow_intCast, Int.cast_neg] using
    summand_bound_of_mem_verticalStrip (by positivity) _ hB hz'

/-- **Poincaré series of weight `k ≥ 3` are holomorphic on `ℍ` for every index `n ∈ ℤ`** (LMFDB
`specialfunction.poincare`), as locally uniform limits of holomorphic functions. -/
lemma mdifferentiable_poincareSeries_of_three_le (hk : 3 ≤ k) :
    MDiff (poincareSeries γ v k n w) := by
  have h : TendstoLocallyUniformlyOn
      (fun s : Finset (Quotient (QuotientGroup.rightRel (cuspStabilizer G γ))) ↦
        ↑ₕ(fun z : ℍ ↦ ∑ q ∈ s, poincareTerm γ v k n w z q.out))
      (↑ₕ(poincareSeries γ v k n w)) Filter.atTop {z : ℂ | 0 < z.im} := by
    rw [← upperHalfPlaneSet, ← range_coe, ← Set.image_univ]
    exact (tendstoLocallyUniformlyOn_univ.mpr <|
      tendstoLocallyUniformly_poincareSeries_of_three_le γ v n w hk).comp _
        (Set.mapsTo_univ _ _) (OpenPartialHomeomorph.continuousOn_symm _)
  rw [UpperHalfPlane.mdifferentiable_iff]
  exact h.differentiableOn (.of_forall fun s ↦ DifferentiableOn.fun_sum
    fun q _ ↦ UpperHalfPlane.mdifferentiable_iff.mp <|
      mdifferentiable_poincareTerm γ v k n w q.out) isOpen_upperHalfPlaneSet

end ModularForm
