import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.NewformAtkinLehner
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.Weight
import LeanBridge.ForMathlib.NumberTheory.ModularForms.EtaMultiplier
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Gamma1Index
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.PoincareSpanCuspForm
import Mathlib.NumberTheory.ModularForms.Bounds

/-!
# Maass forms of real weight with the eta multiplier

For a real number `k` and a holomorphic function `F` on the upper half-plane `ℍ`, the function
`f(z) = y^(k/2) F(z)`, `y = Im z`, is an eigenfunction of the weight `k` Laplacian
`Δ_k = y² (∂²/∂x² + ∂²/∂y²) - iky ∂/∂x`, with `Δ_k f = (k/2)(k/2 - 1) f`
(`UpperHalfPlane.maassLaplacian_im_rpow_mul`). If `F(γz) = v (cz + d)^k F(z)` for some
`γ = (a, b; c, d)` in `SL(2, ℤ)`, with the principal power, then
`exp(-ik Arg(cz + d)) f(γz) = v f(z)` (`UpperHalfPlane.maassSlash_im_rpow_mul`): the unitary slash
action of weight `k` of the LMFDB (`mf.maass.mwf`) turns the automorphy factor `v (cz + d)^k` of
`F` into the multiplier `v`.

For the powers `η^{2k} = exp(2k log η)` of the Dedekind eta function, whose multiplier is the eta
multiplier `v_η^{2k}` of weight `k` (`ModularForm.etaMultiplier`, LMFDB `mf.maass.mwf.character`),
this gives a Maass form of weight `k` that "transforms according to the eta multiplier", in the
sense of the LMFDB's character column, for every real `k`. For `k ≥ 0` it is `y^(k/2) η(z)^{2k}`,
with eigenvalue `(k/2)(1 - k/2)`: it is smooth and nowhere zero, and it is bounded, as
`y⁶ |Δ(z)|` is for the cusp form `Δ = η²⁴`, hence square-integrable on `SL(2, ℤ) \ ℍ`, which has
finite volume. For `k ≤ 0` it is the complex conjugate of `y^(-k/2) η(z)^{-2k}`, with eigenvalue
`(-k/2)(1 + k/2)`: conjugating a Maass form negates its weight and inverts its multiplier
(`UpperHalfPlane.IsMaassFormOfWeight.conj`).

## Main definitions

* `UpperHalfPlane.etaMaassForm`: the function `y^(k/2) η(z)^{2k}`.

## Main results

* `UpperHalfPlane.etaMaassForm_ne_zero`: `y^(k/2) η^{2k}` has no zero on `ℍ`.
* `UpperHalfPlane.maassSlash_etaMaassForm`: `y^(k/2) η^{2k}` transforms with the eta multiplier
  `v_η^{2k}` under `SL(2, ℤ)`.
* `UpperHalfPlane.isMaassFormOfWeight_etaMaassForm` (LMFDB `mf.maass.mwf.character`): for `k ≥ 0`,
  `y^(k/2) η^{2k}` is a Maass form of weight `k` and multiplier system `v_η^{2k}` on `SL(2, ℤ)`.
* `UpperHalfPlane.isMaassFormOfWeight_conj_etaMaassForm` (LMFDB `mf.maass.mwf.character`): for
  `k ≤ 0`, the conjugate of `y^(-k/2) η^{-2k}` is a Maass form of weight `k` and multiplier system
  `v_η^{2k}` on `SL(2, ℤ)`.
-/

open Complex MeasureTheory ModularForm CongruenceSubgroup Matrix SpecialLinearGroup

open scoped ComplexConjugate ContDiff MatrixGroups

namespace UpperHalfPlane

variable (k : ℝ) (γ : SL(2, ℤ)) (z : ℍ) {w : ℂ}

/-- The **eta Maass form** `y^(k/2) η(z)^{2k}` of real weight `k`, as a function on `ℂ`
(only its values on the upper half-plane matter), where `η^{2k} = exp(2k log η)` is the power
`ModularForm.etaPow` of the Dedekind eta function. For `k ≥ 0` it is a Maass form of weight `k` on
`SL(2, ℤ)` with the eta multiplier `v_η^{2k}` (`isMaassFormOfWeight_etaMaassForm`). -/
noncomputable def etaMaassForm (u : ℂ) : ℂ :=
  (u.im ^ (k / 2) : ℝ) * etaPow (2 * k) u

/-- **`y^(k/2) η(z)^{2k}` has no zero on the upper half-plane**, for every real `k`: the Maass
forms of `isMaassFormOfWeight_etaMaassForm` and `isMaassFormOfWeight_conj_etaMaassForm` are not
zero, although the zero function is a Maass form for every multiplier. -/
lemma etaMaassForm_ne_zero (hw : 0 < w.im) : etaMaassForm k w ≠ 0 :=
  mul_ne_zero (ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hw _).ne') (etaPow_ne_zero _ _)

lemma contDiffOn_etaMaassForm : ContDiffOn ℝ ∞ (etaMaassForm k) {u | 0 < u.im} :=
  contDiffOn_im_rpow_mul _ (differentiableOn_etaPow _)

/-- **`y^(k/2) η^{2k}` transforms with the eta multiplier** under `SL(2, ℤ)`: for the unitary
slash action of weight `k`, `exp(-ik Arg(cz + d)) f(γz) = v_η^{2k}(γ) f(z)` for every real `k`. -/
lemma maassSlash_etaMaassForm :
    maassSlash k (etaMaassForm k) γ z = etaMultiplier k γ * etaMaassForm k z :=
  maassSlash_im_rpow_mul (etaPow_smul k γ z)

lemma maassLaplacian_etaMaassForm (hw : 0 < w.im) :
    maassLaplacian k (etaMaassForm k) w = k / 2 * (k / 2 - 1) * etaMaassForm k w :=
  maassLaplacian_im_rpow_mul k (differentiableOn_etaPow _) hw

lemma norm_etaMaassForm :
    ‖etaMaassForm k z‖ = (z.im ^ (6 : ℝ) * ‖CuspForm.discriminant z‖) ^ (k / 12) := by
  have h : ‖CuspForm.discriminant z‖ = ‖η z‖ ^ (24 : ℝ) := by
    rw [Real.rpow_ofNat, ← norm_pow]
    rfl
  rw [etaMaassForm, coe_im, norm_mul, norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg z.im_pos.le _), ← ofReal_ofNat, ← ofReal_mul,
    norm_etaPow_ofReal, h,
    Real.mul_rpow (Real.rpow_nonneg z.im_pos.le _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul z.im_pos.le, ← Real.rpow_mul (norm_nonneg _)]
  congr 2 <;> ring1

variable {k} in
lemma exists_norm_etaMaassForm_le (hk : 0 ≤ k) : ∃ C, ∀ z : ℍ, ‖etaMaassForm k z‖ ≤ C := by
  rcases CuspFormClass.exists_bound CuspForm.discriminant with ⟨C, hC⟩
  refine ⟨C ^ (k / 12), fun z ↦ ?_⟩
  have h : ‖CuspForm.discriminant z‖ * z.im ^ (((12 : ℤ) : ℝ) / 2) ≤ C :=
    (le_div_iff₀ <| Real.rpow_pos_of_pos z.im_pos _).mp (hC z)
  have h6 : ((12 : ℤ) : ℝ) / 2 = 6 := by norm_num
  rw [h6, mul_comm] at h
  rw [norm_etaMaassForm]
  exact Real.rpow_le_rpow (by positivity) h (by positivity)

lemma map_gamma0_one : (Gamma0 1).map (mapGL ℝ) = 𝒮ℒ := by
  rw [Gamma0_one_eq_top, MonoidHom.range_eq_map]

variable {k} in
/-- **`y^(k/2) η(z)^{2k}` is a Maass form of weight `k ≥ 0` with the eta multiplier** (LMFDB
`mf.maass.mwf.character`): it is a Maass form of weight `k` and multiplier system `v_η^{2k}` on
`SL(2, ℤ)`, with eigenvalue `λ = (k/2)(1 - k/2)`, in the sense of `IsMaassFormOfWeight`. It is
smooth, bounded and hence square-integrable on `SL(2, ℤ) \ ℍ`, transforms with `v_η^{2k}` under
the unitary slash action of weight `k`, and satisfies `(Δ_k + λ) f = 0`. It has no zero on `ℍ`
(`etaMaassForm_ne_zero`), so Maass forms of weight `k` "with the eta multiplier" exist; for
`k = 1/2` it is `y^(1/4) η(z)`, with eigenvalue `3/16`. -/
lemma isMaassFormOfWeight_etaMaassForm (hk : 0 ≤ k) : IsMaassFormOfWeight 𝒮ℒ k (etaMaassForm k)
    (fun γ ↦ etaMultiplier k γ) (k / 2 * (1 - k / 2)) := by
  refine ⟨contDiffOn_etaMaassForm k, ⟨gammaZeroDomain 1, ?_, ?_⟩, ?_, fun w hw ↦ ?_⟩
  · exact map_gamma0_one ▸ isFundamentalDomain_pgl_iff.mpr (isFundamentalDomain_gammaZeroDomain 1)
  · rcases exists_norm_etaMaassForm_le hk with ⟨C, hC⟩
    refine Measure.integrableOn_of_bounded (M := C ^ 2)
      (ModularGroup.volume_iUnion_out_inv_smul_fdo_lt_top _).ne
      ((continuous_comp_coe (contDiffOn_etaMaassForm k)).norm.pow 2).aestronglyMeasurable
      (ae_of_all _ fun z ↦ ?_)
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC z) 2
  · rintro ⟨_, γ, rfl⟩ z
    exact maassSlash_etaMaassForm k γ z
  · rw [maassLaplacian_etaMaassForm k hw]
    ring1

variable {k} in
/-- **A Maass form of weight `k ≤ 0` with the eta multiplier** (LMFDB `mf.maass.mwf.character`):
the complex conjugate of `y^(-k/2) η(z)^{-2k}` is a Maass form of weight `k` and multiplier system
`v_η^{2k}` on `SL(2, ℤ)`, with eigenvalue `(-k/2)(1 + k/2)`, in the sense of
`IsMaassFormOfWeight`. With `isMaassFormOfWeight_etaMaassForm`, there is a Maass form without
zeros that transforms according to the eta multiplier of weight `k`, for every real `k`. -/
lemma isMaassFormOfWeight_conj_etaMaassForm (hk : k ≤ 0) : IsMaassFormOfWeight 𝒮ℒ k
    (fun u ↦ conj (etaMaassForm (-k) u)) (fun γ ↦ etaMultiplier k γ) (-k / 2 * (1 + k / 2)) := by
  simpa [etaMultiplier_neg, RCLike.conj_ofNat, neg_div] using
    (isMaassFormOfWeight_etaMaassForm <| neg_nonneg.mpr hk).conj

end UpperHalfPlane
