import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.PoincareUnfolding

/-!
# Poincaré series and the choice of the cusp representative

The `n`-th Poincaré series `P(z; γ_s)` of weight `k` and multiplier `v` on `G ≤ SL(2, ℤ)` at the
cusp `s = γ_s ∞` of width `w` (LMFDB `specialfunction.poincare`) is defined through a
representative `s` of the cusp `G s` and a matrix `γ_s ∈ SL(2, ℤ)` mapping `∞` to `s`. The matrices
mapping `∞` to `s` are the `±γ_s T^m`, `m ∈ ℤ`, all with the stabiliser `G_s`: replacing `γ_s` by
`γ_s T^m` multiplies the series by `e^{-2πinm/w}`, and replacing it by `-γ_s` multiplies it by
`(-1)^k`. So the series is determined by `s` up to a factor `(±1)^k e^{-2πinm/w}`, and by `s` alone
for `w ∣ n` and even `k`. Replacing the representative `s` by `g s`, and `γ_s` by `g γ_s`, `g ∈ G`,
multiplies the series by `conj(v(g))` once its terms are constant on the cosets `G_s g`: for a
nontrivial multiplier the series depends on the representative of the cusp. This is the corrected
form of the LMFDB's sentence "The series depends on the choice of `γ_s` up to a factor of
`e^{2πin/w}`, therefore, if `w ∣ n`, it does not depend on the cusp representative".

## Main results

* `ModularForm.poincareSeries_mul_T_zpow`: `P(z; γ_s T^m) = e^{-2πinm/w} P(z; γ_s)`.
* `ModularForm.poincareSeries_neg`: `P(z; -γ_s) = (-1)^k P(z; γ_s)`.
* `ModularForm.exists_poincareSeries_eq_of_smul_infty_eq`: two matrices mapping `∞` to the same
  point give Poincaré series that differ by a factor `(±1)^k e^{-2πinm/w}`.
* `ModularForm.poincareSeries_eq_of_smul_infty_eq`: for `w ∣ n` and even `k` they give the same
  Poincaré series.
* `ModularForm.poincareSeries_coe_mul`: `P(z; g γ_s) = conj(v(g)) P(z; γ_s)` for `g ∈ G`.
-/

open UpperHalfPlane Matrix SpecialLinearGroup ModularGroup OnePoint

open scoped MatrixGroups ComplexConjugate

namespace ModularForm

variable {G : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ)) (v : G →* Circle) (k n : ℤ) (w : ℕ)

/-- **Replacing `γ_s` by `γ_s T^m` multiplies the Poincaré series by `e^{-2πinm/w}`** (LMFDB
`specialfunction.poincare`): the cosets `G_s g` do not change, and every term is multiplied by this
factor. -/
lemma poincareSeries_mul_T_zpow (m : ℤ) : poincareSeries (γ * T ^ m) v k n w =
    Complex.exp (-(2 * Real.pi * Complex.I * (n / w) * m)) • poincareSeries γ v k n w := by
  funext z
  rw [Pi.smul_apply, smul_eq_mul, poincareSeries, poincareSeries, ← tsum_mul_left]
  simp_rw [poincareTerm_mul_T_zpow]
  rw [cuspStabilizer_mul_T_zpow]

/-- **Replacing `γ_s` by `-γ_s` multiplies the Poincaré series by `(-1)^k`** (LMFDB
`specialfunction.poincare`): the cosets `G_s g` do not change, and every term is multiplied by this
factor. -/
lemma poincareSeries_neg :
    poincareSeries (-γ) v k n w = (-1 : ℂ) ^ k • poincareSeries γ v k n w := by
  funext z
  rw [Pi.smul_apply, smul_eq_mul, poincareSeries, poincareSeries, ← tsum_mul_left]
  simp_rw [poincareTerm_neg]
  rw [cuspStabilizer_neg]

/-- **The Poincaré series is determined by the cusp up to a factor `(±1)^k e^{-2πinm/w}`** (LMFDB
`specialfunction.poincare`): if `γ'_s ∞ = γ_s ∞`, then `γ'_s = ±γ_s T^m` for some `m ∈ ℤ`, and the
Poincaré series built with `γ'_s` is `(±1)^k e^{-2πinm/w}` times the one built with `γ_s`. -/
lemma exists_poincareSeries_eq_of_smul_infty_eq {γ' : SL(2, ℤ)}
    (h : mapGL ℝ γ' • (∞ : OnePoint ℝ) = mapGL ℝ γ • ∞) : ∃ ε : ℤˣ, ∃ m : ℤ,
    poincareSeries γ' v k n w = ((ε : ℤ) : ℂ) ^ k •
      Complex.exp (-(2 * Real.pi * Complex.I * (n / w) * m)) • poincareSeries γ v k n w := by
  have hM (M : SL(2, ℤ)) : (mapGL ℝ M : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = (M 1 0 : ℝ) :=
    rfl
  rw [← inv_smul_eq_iff, smul_smul, ← map_inv, ← map_mul, smul_infty_eq_self_iff, hM,
    Int.cast_eq_zero] at h
  have hb : ∃ b : ℤ, γ⁻¹ * γ' = T ^ b ∨ γ⁻¹ * γ' = -T ^ b :=
    ⟨(γ⁻¹ * γ') 0 0 * (γ⁻¹ * γ') 0 1,
      eq_or_eq_neg_of_apply_one_zero_eq_zero h (by simp [coe_T_zpow]) (by simp [coe_T_zpow])⟩
  rcases hb with ⟨b, h' | h'⟩
  · refine ⟨1, b, ?_⟩
    rw [← mul_inv_cancel_left γ γ', h', poincareSeries_mul_T_zpow]
    simp
  · refine ⟨-1, b, ?_⟩
    rw [← mul_inv_cancel_left γ γ', h', mul_neg, poincareSeries_neg, poincareSeries_mul_T_zpow]
    simp

/-- **For `w ∣ n` and even `k` the Poincaré series depends only on the point `s`, not on `γ_s`**
(LMFDB `specialfunction.poincare`): the factor `(±1)^k e^{-2πinm/w}` of
`exists_poincareSeries_eq_of_smul_infty_eq` is then `1`. -/
lemma poincareSeries_eq_of_smul_infty_eq {γ' : SL(2, ℤ)}
    (h : mapGL ℝ γ' • (∞ : OnePoint ℝ) = mapGL ℝ γ • ∞) (hwn : (w : ℤ) ∣ n) (hk : Even k) :
    poincareSeries γ' v k n w = poincareSeries γ v k n w := by
  rcases exists_poincareSeries_eq_of_smul_infty_eq γ v k n w h with ⟨ε, m, h'⟩
  rcases hwn with ⟨j, rfl⟩
  have hexp : Complex.exp (-(2 * Real.pi * Complex.I * (((w * j : ℤ) : ℂ) / w) * m)) = 1 := by
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    · rw [← Complex.exp_int_mul_two_pi_mul_I (-(j * m))]
      congr 1
      push_cast
      field_simp
  rw [h', hexp, one_smul]
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp
  · simp [hk.neg_one_zpow]

/-- **Replacing the cusp representative `s` by `g s`, `g ∈ G`, multiplies the Poincaré series by
`conj(v(g))`** (LMFDB `specialfunction.poincare`), when its terms are constant on the cosets
`G_s h` (`w` divides the translations of the `γ_s⁻¹ h γ_s = ±T^b`, `h ∈ G_s`, and `v(h) = (±1)^k`
on `G_s`): `h ↦ g⁻¹ h` maps the cosets of `G_{g s} = g G_s g⁻¹` onto those of `G_s`, and the term at
`h` for `g γ_s` is `conj(v(g))` times the term at `g⁻¹ h` for `γ_s`. -/
lemma poincareSeries_coe_mul
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k) (g : G) :
    poincareSeries ((g : SL(2, ℤ)) * γ) v k n w = conj (v g : ℂ) • poincareSeries γ v k n w := by
  have hterm (z : ℍ) (h : G) : poincareTerm ((g : SL(2, ℤ)) * γ) v k n w z h =
      conj (v g : ℂ) * poincareTerm γ v k n w z (g⁻¹ * h) := by
    have hmat : ((g : SL(2, ℤ)) * γ)⁻¹ * (h : SL(2, ℤ)) = γ⁻¹ * ((g⁻¹ * h : G) : SL(2, ℤ)) := by
      push_cast
      group
    rw [poincareTerm_eq_denom, poincareTerm_eq_denom, hmat, ← mul_assoc, ← mul_assoc,
      ← map_mul (starRingEnd ℂ), ← Circle.coe_mul, ← map_mul v, mul_inv_cancel_left]
  have hrel (a b : G) : QuotientGroup.rightRel (cuspStabilizer G ((g : SL(2, ℤ)) * γ)) a b ↔
      QuotientGroup.rightRel (cuspStabilizer G γ) (g⁻¹ * a) (g⁻¹ * b) := by
    have hmat : ((g : SL(2, ℤ)) * γ)⁻¹ * ((b * a⁻¹ : G) : SL(2, ℤ)) * ((g : SL(2, ℤ)) * γ) =
        γ⁻¹ * ((g⁻¹ * b * (g⁻¹ * a)⁻¹ : G) : SL(2, ℤ)) * γ := by
      push_cast
      group
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply, mem_cuspStabilizer_iff,
      mem_cuspStabilizer_iff, hmat]
  let e : Quotient (QuotientGroup.rightRel (cuspStabilizer G ((g : SL(2, ℤ)) * γ))) ≃
      Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) :=
    Quotient.congr (Equiv.mulLeft g⁻¹) hrel
  funext z
  rw [Pi.smul_apply, smul_eq_mul, poincareSeries_eq_tsum_of_section γ v k n w z hw hv
    (fun q ↦ g⁻¹ * (e.symm q).out) fun q ↦ (congrArg e (Quotient.out_eq (e.symm q))).trans
      (e.apply_symm_apply q), ← tsum_mul_left, poincareSeries]
  simp_rw [hterm]
  exact (e.symm.tsum_eq fun q ↦ conj (v g : ℂ) * poincareTerm γ v k n w z (g⁻¹ * q.out)).symm

end ModularForm
