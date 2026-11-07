import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.DefectIdeal

/-!
# The minimal discriminant ideal and the discriminant of any Weierstrass model

Let `O` be a Dedekind domain with fraction field `K` and `W` an elliptic Weierstrass equation over
`K`. Tau Ceti's `WeierstrassCurve.minimalDiscriminantIdeal` is the minimal discriminant ideal
`𝔇_{E/K} = ∏ᵥ 𝔭ᵥ ^ v(Δ_min,ᵥ)`, and for an equation with coefficients in `O` its
`WeierstrassCurve.span_Δ_eq_minimalDiscriminantIdeal_mul_weierstrassDefectIdeal_pow_twelve`
gives `(Δ W) = 𝔇_{E/K} · 𝔍_W ^ 12` with the defect ideal `𝔍_W` an ideal of `O`.

The coefficients of a Weierstrass model over `K` need not lie in `O`, and then `(Δ W)` is a
fractional ideal. Any such model is carried to an integral one `C • W` by a change of variables,
which multiplies the discriminant by `C.u⁻¹²`, so
`(Δ W) = 𝔇_{E/K} · (𝔍_(C • W) · (C.u)) ^ 12`
(`WeierstrassCurve.spanSingleton_Δ_eq_of_isIntegral_smul`): the minimal discriminant ideal differs
from the discriminant ideal of every Weierstrass model by the twelfth power of a fractional ideal
(`WeierstrassCurve.exists_spanSingleton_Δ_eq`).

## Main results

* `WeierstrassCurve.spanSingleton_Δ_eq_of_isIntegral_smul`: `(Δ W) = 𝔇_{E/K} · (𝔍_(C • W) ·
  (C.u)) ^ 12` for a change of variables `C` making `W` integral.
* `WeierstrassCurve.exists_spanSingleton_Δ_eq` (LMFDB `ec.minimal_discriminant`): the discriminant
  ideal of any Weierstrass model is `𝔇_{E/K}` times the twelfth power of a fractional ideal.
-/

open scoped nonZeroDivisors

namespace WeierstrassCurve

variable {O : Type*} [CommRing O] [IsDedekindDomain O] {K : Type*} [Field K] [Algebra O K]
  [IsFractionRing O K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The discriminant ideal of a Weierstrass model in terms of an integral model**: if a change of
variables `C` makes `W` integral, then `(Δ W) = 𝔇_{E/K} · (𝔍_(C • W) · (C.u)) ^ 12` as fractional
ideals. -/
lemma spanSingleton_Δ_eq_of_isIntegral_smul (C : VariableChange K) [IsIntegral O (C • W)] :
    FractionalIdeal.spanSingleton O⁰ W.Δ = minimalDiscriminantIdeal O W *
        (weierstrassDefectIdeal O (C • W) * FractionalIdeal.spanSingleton O⁰ (C.u : K)) ^ 12 := by
  rcases Δ_integral_of_isIntegral O (C • W) with ⟨d, hd⟩
  have hΔ : W.Δ = (C.u : K) ^ 12 * (C • W).Δ := by
    rw [variableChange_Δ, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
  rw [hΔ, map_mul, map_pow, ← hd, ← FractionalIdeal.coeIdeal_span_singleton,
    span_Δ_eq_minimalDiscriminantIdeal_mul_weierstrassDefectIdeal_pow_twelve (C • W) hd,
    minimalDiscriminantIdeal_smul, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow,
    mul_pow]
  ring1

/-- **The minimal discriminant ideal differs from the discriminant ideal of any Weierstrass model by
the twelfth power of a fractional ideal** (LMFDB `ec.minimal_discriminant`): for every elliptic
Weierstrass equation `W` over `K`, `(Δ W) = 𝔇_{E/K} · 𝔞 ^ 12` for a fractional ideal `𝔞` of `O`,
an ideal of `O` when `W` is integral (Tau Ceti's defect ideal). -/
lemma exists_spanSingleton_Δ_eq : ∃ 𝔞 : FractionalIdeal O⁰ K,
    FractionalIdeal.spanSingleton O⁰ W.Δ = minimalDiscriminantIdeal O W * 𝔞 ^ 12 := by
  rcases exists_smul_isIntegral O W with ⟨C, hC⟩
  exact ⟨_, spanSingleton_Δ_eq_of_isIntegral_smul W C⟩

end WeierstrassCurve
