import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.ComplexPeriod
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.DiscriminantIdeal
import TauCeti.AlgebraicGeometry.EllipticCurve.RealPeriod

/-!
# The global period of an elliptic curve over a number field

The global period `Ω(E/K)` of an elliptic curve `E` over a number field `K` (LMFDB `ec.period`) is a
product of local factors `Ω_v(E_v)`, one for each infinite place `v` of `K`, where `E_v` is the
Weierstrass equation of `E` with coefficients embedded by `v`, with `ω = dx / (2y + a₁x + a₃)`:

* at a real place, `Ω_v = |∫_{E_v(ℝ)} ω|`, Tau Ceti's real period `WeierstrassCurve.realPeriod`;
* at a complex place, `Ω_v = |∫_{E_v(ℂ)} ω ∧ ω̄|`, the complex period
  `WeierstrassCurve.complexPeriod`, twice the covolume of the period lattice.

For an arbitrary model of `E`, with discriminant `Δ` and minimal discriminant ideal `𝔡`,

`Ω(E/K) = |N(Δ) / N(𝔡)| ^ (1/12) ∏_v Ω_v(E_v)`,

which is the plain product of the local factors on a global minimal model, and does not depend on
the model: a change of variables with scaling factor `u` multiplies `∏_v Ω_v` by `|N(u)|` and `N(Δ)`
by `N(u)⁻¹²`. A complex place is the class of a pair of conjugate embeddings `K → ℂ`; the factor
`Ω_v` is computed with Mathlib's chosen embedding `NumberField.InfinitePlace.embedding`, and does
not depend on that choice.

## Main definitions

* `WeierstrassCurve.localPeriod`: the local factor `Ω_v(E_v)` at an infinite place
  (LMFDB `ec.period`).
* `WeierstrassCurve.globalPeriod`: the global period `Ω(E/K)` (LMFDB `ec.period`).

## Main results

* `WeierstrassCurve.localPeriod_mk_of_isComplex`: at a complex place, the local period may be
  computed with either of its two conjugate embeddings.
* `WeierstrassCurve.localPeriod_variableChange`: a change of variables with scaling factor `u`
  multiplies `Ω_v` by `|u|_v ^ mult v`.
* `WeierstrassCurve.globalPeriod_variableChange`: the global period does not depend on the model.
* `WeierstrassCurve.globalPeriod_eq_prod_of_isGlobalMinimal`: on a global minimal model, the global
  period is the product of the local factors.
* `WeierstrassCurve.globalPeriod_pos`: the global period of an elliptic curve is positive.
-/

open NumberField InfinitePlace

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K) (v : InfinitePlace K) (C : VariableChange K)

open scoped Classical in
/-- The **local period** `Ω_v(E_v)` (LMFDB `ec.period`) of a Weierstrass curve over a number field
at an infinite place `v`: the real period `|∫_{E_v(ℝ)} ω|` of the curve embedded by `v` when `v`
is real, and the complex period `|∫_{E_v(ℂ)} ω ∧ ω̄|` of the curve embedded by Mathlib's chosen
complex embedding of `v` when `v` is complex. -/
noncomputable def localPeriod : ℝ :=
  if hv : v.IsReal then (W.map (embedding_of_isReal hv)).realPeriod
  else (W.map v.embedding).complexPeriod

lemma localPeriod_of_isReal (hv : v.IsReal) :
    W.localPeriod v = (W.map (embedding_of_isReal hv)).realPeriod :=
  dite_eq_left hv

lemma localPeriod_of_isComplex (hv : v.IsComplex) :
    W.localPeriod v = (W.map v.embedding).complexPeriod :=
  dite_eq_right <| not_isReal_iff_isComplex.mpr hv

/-- **At a complex place, the local period may be computed with either conjugate embedding**: for
every embedding `φ : K → ℂ` defining a complex place, the local period at that place is the complex
period of the curve embedded by `φ`. -/
lemma localPeriod_mk_of_isComplex {φ : K →+* ℂ} (hφ : (InfinitePlace.mk φ).IsComplex) :
    W.localPeriod (InfinitePlace.mk φ) = (W.map φ).complexPeriod := by
  rw [W.localPeriod_of_isComplex _ hφ]
  rcases mk_eq_iff.mp (mk_embedding (InfinitePlace.mk φ)).symm with h | h
  · rw [← h]
  · rw [← h, ← complexPeriod_map_conj (W.map φ), map_map]
    rfl

/-- **A change of variables with scaling factor `u` multiplies the local period at `v` by
`|u|_v ^ mult v`**, where `mult v` is `1` at a real place and `2` at a complex place. -/
lemma localPeriod_variableChange :
    (C • W).localPeriod v = v (C.u : K) ^ v.mult * W.localPeriod v := by
  rcases v.isReal_or_isComplex with hv | hv
  · rw [localPeriod_of_isReal _ _ hv, localPeriod_of_isReal _ _ hv, hv.mult_eq_one, pow_one,
      ← map_variableChange, realPeriod_variableChange, ← norm_embedding_of_isReal hv,
      Real.norm_eq_abs]
    simp
  · rw [localPeriod_of_isComplex _ _ hv, localPeriod_of_isComplex _ _ hv, hv.mult_eq_two,
      ← map_variableChange, complexPeriod_variableChange, ← norm_embedding_eq]
    simp

variable [W.IsElliptic]

lemma localPeriod_pos : 0 < W.localPeriod v := by
  rcases v.isReal_or_isComplex with hv | hv
  · rw [W.localPeriod_of_isReal v hv]
    exact realPeriod_pos _
  · rw [W.localPeriod_of_isComplex v hv]
    exact complexPeriod_pos _

variable [NumberField K]

/-- The **global period** `Ω(E/K) = |N(Δ) / N(𝔡)| ^ (1/12) ∏_v Ω_v(E_v)` (LMFDB `ec.period`) of an
elliptic curve over a number field `K`, where `Δ` is the discriminant of the equation `W`, `𝔡` the
minimal discriminant ideal, `N` the norm and the product runs over the infinite places of `K`. On a
global minimal model it is `∏_v Ω_v(E_v)`, and it does not depend on the model. -/
noncomputable def globalPeriod : ℝ :=
  (|(Algebra.norm ℚ W.Δ : ℝ)| / Ideal.absNorm (minimalDiscriminantIdeal (𝓞 K) W)) ^ (12⁻¹ : ℝ) *
    ∏ v : InfinitePlace K, W.localPeriod v

/-- **The global period does not depend on the model**: it is invariant under a change of
variables. -/
@[simp]
lemma globalPeriod_variableChange : (C • W).globalPeriod = W.globalPeriod := by
  rw [globalPeriod, globalPeriod, minimalDiscriminantIdeal_smul]
  simp_rw [localPeriod_variableChange]
  rw [Finset.prod_mul_distrib, prod_eq_abs_norm, variableChange_Δ, map_mul, map_pow, map_units_inv,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_inv, abs_mul, abs_pow, abs_inv, Rat.cast_abs,
    mul_div_assoc, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  norm_num
  field_simp

/-- **On a global minimal model the global period is the product of the local periods**: the norm
of its discriminant is that of the minimal discriminant ideal. -/
lemma globalPeriod_eq_prod_of_isGlobalMinimal (h : IsGlobalMinimal (𝓞 K) W) :
    W.globalPeriod = ∏ v : InfinitePlace K, W.localPeriod v := by
  have : IsIntegral (𝓞 K) W := h.isIntegral
  have hd : algebraMap (𝓞 K) K (integralModel (𝓞 K) W).Δ = W.Δ := integralModel_Δ_eq _ W
  have hd0 : (integralModel (𝓞 K) W).Δ ≠ 0 :=
    fun h0 ↦ W.isUnit_Δ.ne_zero <| by rw [← hd, h0, map_zero]
  have hnorm : Algebra.norm ℚ (algebraMap (𝓞 K) K (integralModel (𝓞 K) W).Δ) =
      (Algebra.norm ℤ (integralModel (𝓞 K) W).Δ : ℚ) :=
    (Algebra.coe_norm_int _).symm
  rw [globalPeriod, minimalDiscriminantIdeal_eq_span_of_isGlobalMinimal h hd,
    Ideal.absNorm_span_singleton, ← hd, hnorm, Rat.cast_intCast, Nat.cast_natAbs, Int.cast_abs,
    div_self (abs_ne_zero.mpr (Int.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hd0))),
    Real.one_rpow, one_mul]

/-- **The global period of an elliptic curve is positive.** -/
lemma globalPeriod_pos : 0 < W.globalPeriod := by
  have hΔ : (Algebra.norm ℚ W.Δ : ℝ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr W.isUnit_Δ.ne_zero)
  have hd : (0 : ℝ) < Ideal.absNorm (minimalDiscriminantIdeal (𝓞 K) W) :=
    Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| Ideal.absNorm_eq_zero_iff.not.mpr <|
      minimalDiscriminantIdeal_ne_bot _ W
  exact mul_pos (Real.rpow_pos_of_pos (div_pos (abs_pos.mpr hΔ) hd) _)
    (Finset.prod_pos fun v _ ↦ W.localPeriod_pos v)

end WeierstrassCurve
