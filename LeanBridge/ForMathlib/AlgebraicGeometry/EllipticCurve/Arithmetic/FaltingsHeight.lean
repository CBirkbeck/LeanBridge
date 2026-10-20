import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.ComplexPeriod
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Reduced
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Semistable

/-!
# The Faltings height of an elliptic curve over `ℚ`

The Faltings height of an elliptic curve `E` over `ℚ` (LMFDB `ec.q.faltings_height`) is

`h(E) = -(1/2) log A`,

where `A` is the covolume of the Néron lattice of `E`, the period lattice of the invariant
differential of a global minimal model (LMFDB `ec.q.period_lattice`). Here the global minimal
model is Tau Ceti's reduced minimal model `WeierstrassCurve.reducedMinimalModel`, and the covolume
is `WeierstrassCurve.periodCovolume`, the area of `E(ℂ)` for the form `(i/2) ω ∧ ω̄`. The stable
Faltings height is

`h_stable(E) = (1/12) (log denom(j) - log |Δ|) - (1/2) log A`,

where `j` is the `j`-invariant and `Δ` and `A` are the discriminant and the covolume of the period
lattice of any model of `E`: under a change of variables with scaling factor `u`, `Δ` becomes
`u⁻¹² Δ` and `A` becomes `u² A`, so the stable height does not depend on the model. On the reduced
minimal model it differs from the Faltings height by `(1/12) (log denom(j) - log |Δ_min|)`.

## Main definitions

* `WeierstrassCurve.faltingsHeight`: the Faltings height (LMFDB `ec.q.faltings_height`).
* `WeierstrassCurve.stableFaltingsHeight`: the stable Faltings height
  (LMFDB `ec.q.faltings_height`).

## Main results

* `WeierstrassCurve.faltingsHeight_variableChange`: the Faltings height is an isomorphism
  invariant.
* `WeierstrassCurve.stableFaltingsHeight_variableChange`: the stable Faltings height does not
  depend on the model.
* `WeierstrassCurve.stableFaltingsHeight_eq_faltingsHeight_add`: the stable height is the Faltings
  height plus `(1/12) (log denom(j) - log |Δ_min|)`.
* `WeierstrassCurve.IsSemistable.stableFaltingsHeight_eq`: the two heights agree on a semistable
  curve, for which `denom(j) = |Δ_min|`.
-/

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (C : VariableChange ℚ)

/-- The **Faltings height** `h(E) = -(1/2) log A` (LMFDB `ec.q.faltings_height`) of an elliptic
curve over `ℚ`, where `A` is the covolume of its Néron lattice, the period lattice of the invariant
differential of its reduced minimal model. -/
noncomputable def faltingsHeight : ℝ :=
  -Real.log ((reducedMinimalModel E)⁄ℂ).periodCovolume / 2

/-- The **stable Faltings height** `h_stable(E) = (1/12) (log denom(j) - log |Δ|) - (1/2) log A`
(LMFDB `ec.q.faltings_height`) of an elliptic curve over `ℚ`, where `j` is its `j`-invariant, `Δ`
the discriminant of the equation `E` and `A` the covolume of the period lattice of its invariant
differential. It does not depend on the equation
(`WeierstrassCurve.stableFaltingsHeight_variableChange`). -/
noncomputable def stableFaltingsHeight : ℝ :=
  (Real.log E.j.den - Real.log |(E.Δ : ℝ)|) / 12 - Real.log (E⁄ℂ).periodCovolume / 2

/-- **The Faltings height is an isomorphism invariant**, unchanged by a change of variables. -/
@[simp]
lemma faltingsHeight_variableChange : (C • E).faltingsHeight = E.faltingsHeight := by
  rw [faltingsHeight, faltingsHeight, VariableChange.reducedMinimalModel_smul]

omit [E.IsElliptic] in
lemma periodCovolume_baseChange_variableChange :
    ((C • E)⁄ℂ).periodCovolume = |((C.u : ℚ) : ℝ)| ^ 2 * (E⁄ℂ).periodCovolume := by
  rw [baseChange, baseChange, ← map_variableChange, periodCovolume_variableChange]
  simp

/-- **The stable Faltings height does not depend on the model**: under a change of variables with
scaling factor `u`, `log |Δ|` drops by `12 log |u|` and `log A` grows by `2 log |u|`. -/
@[simp]
lemma stableFaltingsHeight_variableChange :
    (C • E).stableFaltingsHeight = E.stableFaltingsHeight := by
  have hu : |((C.u : ℚ) : ℝ)| ≠ 0 := abs_ne_zero.mpr (Rat.cast_ne_zero.mpr C.u.ne_zero)
  have hΔ : |(E.Δ : ℝ)| ≠ 0 := abs_ne_zero.mpr (Rat.cast_ne_zero.mpr E.isUnit_Δ.ne_zero)
  rw [stableFaltingsHeight, stableFaltingsHeight, variableChange_j, variableChange_Δ,
    periodCovolume_baseChange_variableChange, Rat.cast_mul, Rat.cast_pow, Units.val_inv_eq_inv_val,
    Rat.cast_inv, abs_mul, abs_pow, abs_inv,
    Real.log_mul (pow_ne_zero 2 hu) (E⁄ℂ).periodCovolume_pos.ne',
    Real.log_mul (pow_ne_zero 12 (inv_ne_zero hu)) hΔ, Real.log_pow, Real.log_pow, Real.log_inv]
  ring1

lemma j_reducedMinimalModel : (reducedMinimalModel E).j = E.j := by
  rcases exists_smul_eq_reducedMinimalModel E with ⟨D, hD⟩
  simp only [← hD, variableChange_j]

lemma stableFaltingsHeight_reducedMinimalModel :
    (reducedMinimalModel E).stableFaltingsHeight = E.stableFaltingsHeight := by
  rcases exists_smul_eq_reducedMinimalModel E with ⟨D, hD⟩
  simp only [← hD, stableFaltingsHeight_variableChange]

/-- **The stable Faltings height is the Faltings height plus
`(1/12) (log denom(j) - log |Δ_min|)`**, where `|Δ_min|` is the norm of the minimal discriminant
ideal. -/
lemma stableFaltingsHeight_eq_faltingsHeight_add : E.stableFaltingsHeight = E.faltingsHeight +
    (Real.log E.j.den - Real.log (Ideal.absNorm (minimalDiscriminantIdeal ℤ E))) / 12 := by
  have hΔ :
      (Ideal.absNorm (minimalDiscriminantIdeal ℤ E) : ℝ) = |((reducedMinimalModel E).Δ : ℝ)| :=
    mod_cast E.absNorm_minimalDiscriminantIdeal
  rw [← E.stableFaltingsHeight_reducedMinimalModel, stableFaltingsHeight, faltingsHeight, hΔ,
    j_reducedMinimalModel]
  ring1

private lemma den_intCast_div_intCast {a b : ℤ} (hb : b ≠ 0) (h : IsCoprime a b) :
    ((a : ℚ) / b).den = b.natAbs := by
  have hab : Int.gcd a b = 1 := Int.isCoprime_iff_gcd_eq_one.mp h
  rcases hb.lt_or_gt with hb' | hb'
  · have hdiv : (a : ℚ) / b = ((-a : ℤ) : ℚ) / ((-b : ℤ) : ℚ) := by
      push_cast
      rw [neg_div_neg_eq]
    have hden : ((((-a : ℤ) : ℚ) / ((-b : ℤ) : ℚ)).den : ℤ) = -b :=
      Rat.den_div_eq_of_coprime (neg_pos.mpr hb') (by rwa [Int.natAbs_neg, Int.natAbs_neg])
    rw [hdiv]
    omega
  · have hden : (((a : ℚ) / (b : ℚ)).den : ℤ) = b := Rat.den_div_eq_of_coprime hb' hab
    omega

/-- **The stable and unstable Faltings heights agree on a semistable curve**, for which
`denom(j) = |Δ_min|`: on the reduced minimal model, `c₄` and `Δ` are coprime. -/
lemma IsSemistable.stableFaltingsHeight_eq (h : IsSemistable ℤ E) :
    E.stableFaltingsHeight = E.faltingsHeight := by
  rcases exists_smul_eq_reducedMinimalModel E with ⟨D, hD⟩
  have hmin : IsGlobalMinimal ℤ (reducedMinimalModel E) :=
    (isReducedMinimal_reducedMinimalModel E).isGlobalMinimal
  have : IsIntegral ℤ (reducedMinimalModel E) := hmin.isIntegral
  have hW₀ : (integralModel ℤ (reducedMinimalModel E))⁄ℚ = reducedMinimalModel E :=
    baseChange_integralModel_eq ℤ _
  have hΔ₀ : (integralModel ℤ (reducedMinimalModel E)).Δ ≠ 0 := by
    intro h0
    apply (reducedMinimalModel E).isUnit_Δ.ne_zero
    rw [← algebraMap_Δ_of_baseChange_eq hW₀, h0, map_zero]
  have hR : IsSemistable ℤ (reducedMinimalModel E) := by
    simpa only [← hD, isSemistable_smul] using h
  -- at every prime, the reduction of the minimal model is not additive, so `c₄` and `Δ` are coprime
  have hcop : IsCoprime (integralModel ℤ (reducedMinimalModel E)).c₄
      (integralModel ℤ (reducedMinimalModel E)).Δ := by
    refine isCoprime_of_prime_dvd (fun h0 ↦ hΔ₀ h0.2) fun z hz hc hΔ ↦ ?_
    refine hR (.ofPrime (Ideal.prime_span_singleton_iff.mpr hz)) ?_
    rw [hmin.hasAdditiveReduction_minimal_iff hW₀]
    exact ⟨Ideal.mem_span_singleton.mpr hΔ, Ideal.mem_span_singleton.mpr hc⟩
  have hj : E.j = (((integralModel ℤ (reducedMinimalModel E)).c₄ ^ 3 : ℤ) : ℚ) /
      ((integralModel ℤ (reducedMinimalModel E)).Δ : ℚ) := by
    rw [← j_reducedMinimalModel, j_eq, ← algebraMap_Δ_of_baseChange_eq hW₀,
      ← algebraMap_c₄_of_baseChange_eq hW₀, algebraMap_int_eq, eq_intCast, eq_intCast, Int.cast_pow]
    ring1
  have hnorm : Ideal.absNorm (minimalDiscriminantIdeal ℤ E) =
      (integralModel ℤ (reducedMinimalModel E)).Δ.natAbs := by
    have hq : (Ideal.absNorm (minimalDiscriminantIdeal ℤ E) : ℚ) =
        ((integralModel ℤ (reducedMinimalModel E)).Δ.natAbs : ℚ) := by
      rw [E.absNorm_minimalDiscriminantIdeal, ← algebraMap_Δ_of_baseChange_eq hW₀,
        Nat.cast_natAbs, Int.cast_abs, algebraMap_int_eq, eq_intCast]
    exact_mod_cast hq
  rw [stableFaltingsHeight_eq_faltingsHeight_add, hj, den_intCast_div_intCast hΔ₀ hcop.pow_left,
    hnorm, sub_self, zero_div, add_zero]

end WeierstrassCurve
