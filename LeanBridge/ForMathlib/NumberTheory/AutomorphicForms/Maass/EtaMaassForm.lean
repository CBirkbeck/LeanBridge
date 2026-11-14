import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.NewformAtkinLehner
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.Weight
import LeanBridge.ForMathlib.NumberTheory.ModularForms.EtaMultiplier
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.PoincareSpanCuspForm
import Mathlib.NumberTheory.ModularForms.Bounds

/-!
# Maass forms of real weight with the eta multiplier

For a real number `k` and a holomorphic function `F` on the upper half-plane `ℍ`, the function
`f(z) = y^(k/2) F(z)`, `y = Im z`, is an eigenfunction of the weight `k` Laplacian
`Δ_k = y² (∂²/∂x² + ∂²/∂y²) - iky ∂/∂x`, with `Δ_k f = (k/2)(k/2 - 1) f`. If
`F(γz) = v (cz + d)^k F(z)` for some `γ = (a, b; c, d)` in `SL(2, ℤ)`, with the principal power,
then `exp(-ik Arg(cz + d)) f(γz) = v f(z)`: the unitary slash action of weight `k` of the LMFDB
(`mf.maass.mwf`) turns the automorphy factor `v (cz + d)^k` of `F` into the multiplier `v`.

For the powers `η^{2k} = exp(2k log η)` of the Dedekind eta function, whose multiplier is the eta
multiplier `v_η^{2k}` of weight `k` (`ModularForm.etaMultiplier`, LMFDB `mf.maass.mwf.character`),
this gives a Maass form of weight `k` that "transforms according to the eta multiplier", in the
sense of the LMFDB's character column, for every real `k`. For `k ≥ 0` it is `y^(k/2) η(z)^{2k}`,
with eigenvalue `(k/2)(1 - k/2)`: it is smooth and nowhere zero, and it is bounded, as
`y⁶ |Δ(z)|` is for the cusp form `Δ = η²⁴`, hence square-integrable on `SL(2, ℤ) \ ℍ`, which has
finite volume. For `k ≤ 0` it is the complex conjugate of `y^(-k/2) η(z)^{-2k}`, with eigenvalue
`(-k/2)(1 + k/2)`: conjugating a Maass form negates its weight and inverts its multiplier.

## Main definitions

* `UpperHalfPlane.etaMaassForm`: the function `y^(k/2) η(z)^{2k}`.

## Main results

* `UpperHalfPlane.maassLaplacian_im_rpow_mul`: `Δ_k (y^(k/2) F) = (k/2)(k/2 - 1) y^(k/2) F` for
  holomorphic `F`.
* `UpperHalfPlane.maassSlash_im_rpow_mul`: `y^(k/2) F` transforms with the multiplier `v` under
  `γ ∈ SL(2, ℤ)` when `F(γz) = v (cz + d)^k F(z)`.
* `UpperHalfPlane.etaMaassForm_ne_zero`: `y^(k/2) η^{2k}` has no zero on `ℍ`.
* `UpperHalfPlane.maassSlash_etaMaassForm`: `y^(k/2) η^{2k}` transforms with the eta multiplier
  `v_η^{2k}` under `SL(2, ℤ)`.
* `UpperHalfPlane.isMaassFormOfWeight_etaMaassForm` (LMFDB `mf.maass.mwf.character`): for `k ≥ 0`,
  `y^(k/2) η^{2k}` is a Maass form of weight `k` and multiplier system `v_η^{2k}` on `SL(2, ℤ)`.
* `UpperHalfPlane.IsMaassFormOfWeight.conj`: the complex conjugate of a Maass form of weight `k`
  and multiplier `v` is a Maass form of weight `-k` and multiplier `v⁻¹`.
* `UpperHalfPlane.isMaassFormOfWeight_conj_etaMaassForm` (LMFDB `mf.maass.mwf.character`): for
  `k ≤ 0`, the conjugate of `y^(-k/2) η^{-2k}` is a Maass form of weight `k` and multiplier system
  `v_η^{2k}` on `SL(2, ℤ)`.
-/

open Complex MeasureTheory ModularForm CongruenceSubgroup Matrix SpecialLinearGroup

open scoped ComplexConjugate ContDiff MatrixGroups

namespace UpperHalfPlane

variable (k t : ℝ) (γ : SL(2, ℤ)) (z : ℍ) {F G : ℂ → ℂ} {v w : ℂ}

lemma exp_neg_arg_mul_cpow (hw : w ≠ 0) :
    cexp (-(Complex.I * k * w.arg)) * w ^ (k : ℂ) = (‖w‖ ^ k : ℝ) := by
  rw [cpow_def_of_ne_zero hw, ← Complex.exp_add, Real.rpow_def_of_pos (norm_pos_iff.mpr hw),
    ofReal_exp, Complex.log]
  congr 1
  push_cast
  ring1

lemma hasFDerivAt_im_rpow_mul (hG : DifferentiableAt ℂ G w) (hw : 0 < w.im) : HasFDerivAt
    (fun u ↦ ((u.im ^ t : ℝ) : ℂ) * G u)
    (((w.im ^ t : ℝ) : ℂ) • (ContinuousLinearMap.toSpanSingleton ℂ (deriv G w)).restrictScalars ℝ +
      G w • ofRealCLM.comp ((t * w.im ^ (t - 1)) • imCLM)) w :=
  (ofRealCLM.hasFDerivAt.comp w <| imCLM.hasFDerivAt.rpow_const <| .inl hw.ne').mul <|
    hG.hasDerivAt.hasFDerivAt.restrictScalars ℝ

lemma fderiv_im_rpow_mul_one (hG : DifferentiableAt ℂ G w) (hw : 0 < w.im) :
    fderiv ℝ (fun u ↦ ((u.im ^ t : ℝ) : ℂ) * G u) w 1 = (w.im ^ t : ℝ) * deriv G w := by
  rw [(hasFDerivAt_im_rpow_mul t hG hw).fderiv]
  simp

lemma fderiv_im_rpow_mul_I (hG : DifferentiableAt ℂ G w) (hw : 0 < w.im) :
    fderiv ℝ (fun u ↦ ((u.im ^ t : ℝ) : ℂ) * G u) w Complex.I =
      (w.im ^ t : ℝ) * (Complex.I * deriv G w) + (w.im ^ (t - 1) : ℝ) * (t * G w) := by
  rw [(hasFDerivAt_im_rpow_mul t hG hw).fderiv]
  simp
  ring1

/-- **`y^(k/2) F` is an eigenfunction of the weight `k` Laplacian** for a holomorphic function `F`
on the upper half-plane: `Δ_k (y^(k/2) F) = (k/2)(k/2 - 1) y^(k/2) F`, where
`Δ_k = y² (∂²/∂x² + ∂²/∂y²) - iky ∂/∂x`. -/
lemma maassLaplacian_im_rpow_mul (hF : DifferentiableOn ℂ F {u | 0 < u.im}) (hw : 0 < w.im) :
    maassLaplacian k (fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * F u) w =
      k / 2 * (k / 2 - 1) * (((w.im ^ (k / 2) : ℝ) : ℂ) * F w) := by
  have ho : IsOpen {u : ℂ | 0 < u.im} := isOpen_upperHalfPlaneSet
  have hd {u : ℂ} (hu : 0 < u.im) : DifferentiableAt ℂ F u := hF.differentiableAt (ho.mem_nhds hu)
  have hd' {u : ℂ} (hu : 0 < u.im) : DifferentiableAt ℂ (deriv F) u :=
    (hF.deriv ho).differentiableAt (ho.mem_nhds hu)
  have h1 : (fun u ↦ fderiv ℝ (fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * F u) u 1) =ᶠ[nhds w]
      fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * deriv F u := by
    filter_upwards [ho.mem_nhds hw] with u hu using fderiv_im_rpow_mul_one _ (hd hu) hu
  have h2 : (fun u ↦ fderiv ℝ (fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * F u) u Complex.I) =ᶠ[nhds w]
      fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * (Complex.I * deriv F u) +
        ((u.im ^ (k / 2 - 1) : ℝ) : ℂ) * ((k / 2 : ℝ) * F u) := by
    filter_upwards [ho.mem_nhds hw] with u hu using fderiv_im_rpow_mul_I _ (hd hu) hu
  have hI : DifferentiableAt ℂ (fun u ↦ Complex.I * deriv F u) w := (hd' hw).const_mul _
  have hk : DifferentiableAt ℂ (fun u ↦ ((k / 2 : ℝ) : ℂ) * F u) w := (hd hw).const_mul _
  have h3 : fderiv ℝ (fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * (Complex.I * deriv F u) +
      ((u.im ^ (k / 2 - 1) : ℝ) : ℂ) * ((k / 2 : ℝ) * F u)) w Complex.I =
      fderiv ℝ (fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * (Complex.I * deriv F u)) w Complex.I +
        fderiv ℝ (fun u ↦ ((u.im ^ (k / 2 - 1) : ℝ) : ℂ) * ((k / 2 : ℝ) * F u)) w Complex.I := by
    rw [fderiv_fun_add (hasFDerivAt_im_rpow_mul _ hI hw).differentiableAt
      (hasFDerivAt_im_rpow_mul _ hk hw).differentiableAt]
    rfl
  have hy : (w.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw.ne'
  rw [maassLaplacian, hyperbolicLaplacian, h1.fderiv_eq, h2.fderiv_eq, h3,
    fderiv_im_rpow_mul_one _ (hd' hw) hw, fderiv_im_rpow_mul_one _ (hd hw) hw,
    fderiv_im_rpow_mul_I _ hI hw, fderiv_im_rpow_mul_I _ hk hw, deriv_const_mul _ (hd' hw),
    deriv_const_mul _ (hd hw), Real.rpow_sub_one hw.ne', Real.rpow_sub_one hw.ne',
    Real.rpow_sub_one hw.ne']
  push_cast
  field_simp
  linear_combination (4 * ((w.im ^ (k / 2) : ℝ) : ℂ) * (w.im : ℂ) ^ 2 * deriv (deriv F) w) * I_sq

lemma contDiffOn_im_rpow_mul (hF : DifferentiableOn ℂ F {u | 0 < u.im}) :
    ContDiffOn ℝ ∞ (fun u ↦ ((u.im ^ t : ℝ) : ℂ) * F u) {u | 0 < u.im} :=
  (ofRealCLM.contDiff.comp_contDiffOn <|
    imCLM.contDiff.contDiffOn.rpow_const_of_ne fun _ hu ↦ ne_of_gt hu).mul <|
      (hF.contDiffOn isOpen_upperHalfPlaneSet).restrict_scalars ℝ

variable {k γ z} in
/-- **The unitary slash action of `y^(k/2) F`**: if `F(γz) = v (cz + d)^k F(z)` for
`γ = (a, b; c, d)` in `SL(2, ℤ)`, with the principal power of `cz + d`, then `f = y^(k/2) F`
satisfies `exp(-ik Arg(cz + d)) f(γz) = v f(z)`. -/
lemma maassSlash_im_rpow_mul (hF : F ↑(γ • z) = v * denom γ z ^ (k : ℂ) * F z) :
    maassSlash k (fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * F u) γ z =
      v * (((z.im ^ (k / 2) : ℝ) : ℂ) * F z) := by
  have hd : denom γ z ≠ 0 := denom_ne_zero γ z
  have hn : 0 < ‖denom γ z‖ := norm_pos_iff.mpr hd
  have him : ((γ • z : ℍ) : ℂ).im = z.im / ‖denom γ z‖ ^ 2 := by
    rw [coe_im, ModularGroup.im_smul_eq_div_normSq, normSq_eq_norm_sq]
  have hpow : (z.im / ‖denom γ z‖ ^ 2) ^ (k / 2) = z.im ^ (k / 2) / ‖denom γ z‖ ^ k := by
    rw [Real.div_rpow z.im_pos.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hn.le,
      Nat.cast_ofNat, mul_div_cancel₀ k two_ne_zero]
  have hn' : ((‖denom γ z‖ ^ k : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hn k).ne'
  rw [maassSlash, ← ModularGroup.sl_moeb, him, hpow, hF]
  push_cast
  field_simp
  linear_combination (((z.im ^ (k / 2) : ℝ) : ℂ) * v * F z) * exp_neg_arg_mul_cpow k hd

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
  have h : Gamma0 1 = ⊤ := eq_top_iff.mpr fun γ _ ↦ Gamma0_mem.mpr (Subsingleton.elim _ _)
  rw [h, MonoidHom.range_eq_map]

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
/-- **The complex conjugate of a Maass form of weight `k`** and multiplier `v` on `Γ` is a Maass
form of weight `-k` on `Γ`, with the multiplier `v⁻¹ = conj v` and the conjugate eigenvalue. -/
lemma IsMaassFormOfWeight.conj {Γ : Subgroup (GL (Fin 2) ℝ)} {f : ℂ → ℂ} {μ : Γ → Circle}
    {eigenvalue : ℂ} (hf : IsMaassFormOfWeight Γ k f μ eigenvalue) :
    IsMaassFormOfWeight Γ (-k) (fun u ↦ conj (f u)) (fun γ ↦ (μ γ)⁻¹) (conj eigenvalue) := by
  refine ⟨conjCLE.contDiff.comp_contDiffOn hf.1, by simpa using hf.2.1, fun γ z ↦ ?_,
    fun u hu ↦ ?_⟩
  · simpa [maassSlash, ← exp_conj, ← Circle.coe_inv_eq_conj] using congrArg conj (hf.2.2.1 γ z)
  · simpa [maassLaplacian, hyperbolicLaplacian_conj, fderiv_conj_apply] using
      congrArg conj (hf.2.2.2 u hu)

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
