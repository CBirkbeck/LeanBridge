import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.UpperHalfPlane
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Maass forms of real weight with a multiplier system

A Maass form of weight `k ∈ ℝ` and multiplier system `v` on a subgroup `Γ` of `GL(2, ℝ)` is a
smooth function `f` on `ℍ` with `exp(-ik Arg(cz + d)) f(γz) = v(γ) f(z)` for every `γ ∈ Γ`, which
is square-integrable on `Γ \ ℍ` and an eigenfunction of the weight `k` Laplacian
`Δ_k = y² (∂²/∂x² + ∂²/∂y²) - iky ∂/∂x`.

For a holomorphic function `F` on `ℍ`, the function `f(z) = y^(k/2) F(z)`, `y = Im z`, is an
eigenfunction of the weight `k` Laplacian, with `Δ_k f = (k/2)(k/2 - 1) f`. If
`F(γz) = v (cz + d)^k F(z)` for some `γ = (a, b; c, d)` in `SL(2, ℤ)`, with the principal power,
then `exp(-ik Arg(cz + d)) f(γz) = v f(z)`: the unitary slash action of weight `k` turns the
automorphy factor `v (cz + d)^k` of `F` into the multiplier `v`. Conjugating a Maass form negates
its weight and inverts its multiplier.

## Main definitions

* `UpperHalfPlane.maassLaplacian` (LMFDB `mf.maass.mwf.weight`): the weight `k` Laplacian.
* `UpperHalfPlane.maassSlash` (LMFDB `mf.maass.mwf`): the unitary weight `k` slash action.
* `UpperHalfPlane.IsMaassFormOfWeight` (LMFDB `mf.maass.mwf`, `mf.maass.mwf.weight`): Maass forms
  of weight `k` and multiplier system `v`.

## Main results

* `UpperHalfPlane.isMaassFormOfWeight_zero_iff`: the Maass forms of weight `0` with trivial
  multiplier are the Maass forms of weight `0` of `UpperHalfPlane.IsMaassForm`.
* `UpperHalfPlane.IsMaassFormOfWeight.conj`: the complex conjugate of a Maass form of weight `k`
  and multiplier `v` is a Maass form of weight `-k` and multiplier `v⁻¹`.
* `UpperHalfPlane.maassLaplacian_im_rpow_mul`: `Δ_k (y^(k/2) F) = (k/2)(k/2 - 1) y^(k/2) F` for
  holomorphic `F`.
* `UpperHalfPlane.maassSlash_im_rpow_mul`: `y^(k/2) F` transforms with the multiplier `v` under
  `γ ∈ SL(2, ℤ)` when `F(γz) = v (cz + d)^k F(z)`.
-/

open Complex MeasureTheory Matrix

open scoped ComplexConjugate ContDiff MatrixGroups

lemma Complex.exp_neg_arg_mul_cpow (k : ℝ) {w : ℂ} (hw : w ≠ 0) :
    exp (-(I * k * w.arg)) * w ^ (k : ℂ) = (‖w‖ ^ k : ℝ) := by
  rw [cpow_def_of_ne_zero hw, ← Complex.exp_add, Real.rpow_def_of_pos (norm_pos_iff.mpr hw),
    ofReal_exp, Complex.log]
  congr 1
  push_cast
  ring1

namespace UpperHalfPlane

variable {Γ : Subgroup (GL (Fin 2) ℝ)} (k : ℝ) (f : ℂ → ℂ) {eigenvalue : ℂ}

variable (z : ℂ) in
/-- The **weight `k` Laplacian** (LMFDB `mf.maass.mwf.weight`)
`Δ_k = y² (∂²/∂x² + ∂²/∂y²) - iky ∂/∂x` at `z = x + iy`, for the unitary slash action
`maassSlash`. Its first part is `hyperbolicLaplacian`, with the sign convention of
`mf.maass.mwf.laplacian` explained there. -/
noncomputable def maassLaplacian : ℂ :=
  hyperbolicLaplacian f z - Complex.I * k * z.im * fderiv ℝ f z 1

variable (γ : GL (Fin 2) ℝ) (z : ℍ) in
/-- The **unitary weight `k` slash action** (LMFDB `mf.maass.mwf`)
`f|[γ, k](z) = exp(-ik Arg(cz + d)) f(γz)`, with `Arg` the principal argument in `(-π, π]`. -/
noncomputable def maassSlash : ℂ :=
  Complex.exp (-(Complex.I * k * (denom γ z).arg)) * f ↑(γ • z)

variable (Γ) in
/-- A function `f` on the upper half-plane, given on `ℂ`, is a **Maass form of weight `k`** (LMFDB
`mf.maass.mwf`, `mf.maass.mwf.weight`) with **multiplier system** `v` on a subgroup `Γ` of
`GL(2, ℝ)` and eigenvalue `λ` if it is smooth on `ℍ`, square-integrable on `Γ \ ℍ`, satisfies
`f|[γ, k] = v(γ) f` for every `γ ∈ Γ`, and `(Δ_k + λ) f = 0`.

The multiplier `v : Γ → S¹` is any unitary function: for non-integral weight, such as the eta
multipliers `v_η^{2k}` of the knowl (`ModularForm.etaMultiplier`), it is not a homomorphism.
Square-integrability is taken as in `IsMaassForm` (on a fundamental domain of the image of `Γ` in
`PGL(2, ℝ)`); the knowl lists it only for weight `0`, but `|f|` is `Γ`-invariant since `v` is
unitary, and it is part of the notion of a Maass form. The condition at `γ` determines `v(γ)` where
`f ≠ 0`; for instance `-1 ∈ Γ` acts trivially with `Arg(-1) = π`, forcing `v(-1) = exp(-ikπ)` for
`f ≠ 0`. For `k ≠ 0` the knowl's groups lie in `SL(2, ℝ)`: an element of negative determinant
exchanges `Δ_k` and `Δ_{-k}`, so it leaves only degenerate forms. -/
def IsMaassFormOfWeight (v : Γ → Circle) (eigenvalue : ℂ) : Prop :=
  ContDiffOn ℝ ∞ f {z | 0 < z.im} ∧
    (∃ D : Set ℍ, IsFundamentalDomain (Γ.map ProjGenLinGroup.mk) D ∧
      IntegrableOn (fun z : ℍ ↦ ‖f z‖ ^ 2) D) ∧
    (∀ (γ : Γ) (z : ℍ), maassSlash k f γ z = v γ * f z) ∧
    ∀ z : ℂ, 0 < z.im → maassLaplacian k f z + eigenvalue * f z = 0

/-- **Weight `0` with trivial multiplier**: these Maass forms are those of `IsMaassForm`. -/
lemma isMaassFormOfWeight_zero_iff :
    IsMaassFormOfWeight Γ 0 f 1 eigenvalue ↔ IsMaassForm Γ f eigenvalue := by
  simp [IsMaassFormOfWeight, IsMaassForm, maassSlash, maassLaplacian]

variable {k f} in
/-- **The complex conjugate of a Maass form of weight `k`** and multiplier `v` on `Γ` is a Maass
form of weight `-k` on `Γ`, with the multiplier `v⁻¹ = conj v` and the conjugate eigenvalue. -/
lemma IsMaassFormOfWeight.conj {μ : Γ → Circle} (hf : IsMaassFormOfWeight Γ k f μ eigenvalue) :
    IsMaassFormOfWeight Γ (-k) (fun u ↦ conj (f u)) (fun γ ↦ (μ γ)⁻¹) (conj eigenvalue) := by
  refine ⟨conjCLE.contDiff.comp_contDiffOn hf.1, by simpa using hf.2.1, fun γ z ↦ ?_,
    fun u hu ↦ ?_⟩
  · simpa [maassSlash, ← exp_conj, ← Circle.coe_inv_eq_conj] using congrArg conj (hf.2.2.1 γ z)
  · simpa [maassLaplacian, hyperbolicLaplacian_conj, fderiv_conj_apply] using
      congrArg conj (hf.2.2.2 u hu)

variable (t : ℝ) {F G : ℂ → ℂ} {v w : ℂ}

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

variable {k} in
/-- **The unitary slash action of `y^(k/2) F`**: if `F(γz) = v (cz + d)^k F(z)` for
`γ = (a, b; c, d)` in `SL(2, ℤ)`, with the principal power of `cz + d`, then `f = y^(k/2) F`
satisfies `exp(-ik Arg(cz + d)) f(γz) = v f(z)`. -/
lemma maassSlash_im_rpow_mul {γ : SL(2, ℤ)} {z : ℍ}
    (hF : F ↑(γ • z) = v * denom γ z ^ (k : ℂ) * F z) :
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

end UpperHalfPlane
