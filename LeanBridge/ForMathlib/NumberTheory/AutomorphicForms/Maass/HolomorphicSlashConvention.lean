import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.Weight

/-!
# Maass forms of real weight with the holomorphic slash action

The LMFDB's knowl on Maass forms (`mf.maass.mwf`) defines the Maass forms of weight `k` with the
unitary slash action `f|[γ, k](z) = exp(-ik Arg(cz + d)) f(γz)` and the weight `k` Laplacian
`Δ_k = y² (∂²/∂x² + ∂²/∂y²) - iky ∂/∂x`, and remarks: "One can also consider Maass forms
transforming with the usual "holomorphic" weight `k` slash-action. In this case the corresponding
weight `k` Laplacian will look slightly different:
`Δ_k = y² (∂²/∂x² + ∂²/∂y²) - iky (∂/∂x + i ∂/∂y)`."

The two conventions correspond under `f = y^{k/2} F`, `y = Im z`. For `γ = (a, b; c, d)` of
determinant `1`, `Im(γz) = y / |cz + d|²` and `(cz + d)^k = |cz + d|^k e^{ik Arg(cz + d)}` (the
principal power) give `f|[γ, k](z) = y^{k/2} (cz + d)^{-k} F(γz)`: the unitary slash action of `f`
is `y^{k/2}` times the holomorphic slash action `F|_k γ (z) = (cz + d)^{-k} F(γz)` of `F`. For `F`
of class `C²`, `Δ_k (y^{k/2} F) = y^{k/2} (Δ^hol_k F + (k/2)(k/2 - 1) F)`, where `Δ^hol_k` is the
Laplacian of the remark. So `f` transforms with a multiplier `v` under the unitary action
exactly when `F` transforms with `v` under the holomorphic one, and `(Δ_k + λ) f = 0` exactly when
`(Δ^hol_k + λ + (k/2)(k/2 - 1)) F = 0`: in the holomorphic convention the Maass forms are the
eigenfunctions of `Δ^hol_k`, the eigenvalue shifted by `(k/2)(k/2 - 1)`.

## Main definitions

* `UpperHalfPlane.holomorphicSlash`: the holomorphic slash action `(cz + d)^{-k} F(γz)` of real
  weight `k`.
* `UpperHalfPlane.holomorphicMaassLaplacian` (LMFDB `mf.maass.mwf`): the weight `k` Laplacian
  `y² (∂²/∂x² + ∂²/∂y²) - iky (∂/∂x + i ∂/∂y)` of the holomorphic slash action.

## Main results

* `UpperHalfPlane.maassSlash_im_rpow_mul_eq` (LMFDB `mf.maass.mwf`): the unitary slash action of
  `y^{k/2} F` is `y^{k/2}` times the holomorphic slash action of `F`.
* `UpperHalfPlane.maassSlash_im_rpow_mul`: `y^{k/2} F` transforms with the multiplier `μ` under
  `γ ∈ SL(2, ℤ)` when `F(γz) = μ (cz + d)^k F(z)`.
* `UpperHalfPlane.maassLaplacian_im_rpow_mul_eq` (LMFDB `mf.maass.mwf`):
  `Δ_k (y^{k/2} F) = y^{k/2} (Δ^hol_k F + (k/2)(k/2 - 1) F)`.
* `UpperHalfPlane.maassSlash_im_rpow_mul_eq_mul_iff`: the transformation laws correspond.
* `UpperHalfPlane.maassLaplacian_im_rpow_mul_add_mul_eq_zero_iff`: the Laplace equations
  correspond.

## References

* J. H. Bruinier, J. Funke, *On two geometric theta lifts*, Duke Math. J. 125 (2004), 45–90.
-/

open Complex Subgroup

open scoped MatrixGroups

namespace UpperHalfPlane

variable (k : ℝ) (F : ℂ → ℂ) {t : ℝ} {G : ℂ → ℂ} {w eigenvalue : ℂ} {Γ : Subgroup (GL (Fin 2) ℝ)}
    {v : Γ → Circle}

variable (γ : GL (Fin 2) ℝ) (z : ℍ) in
/-- The **holomorphic slash action of real weight `k`**, `F|_k γ (z) = (cz + d)^{-k} F(γz)` for
`γ = (a, b; c, d)`, with the principal power of `cz + d`: for an integral `k` it is the slash action
of holomorphic modular forms, and for real `k` the "holomorphic" weight `k` slash action of the
remark in `mf.maass.mwf`. -/
noncomputable def holomorphicSlash : ℂ :=
  denom γ z ^ (-(k : ℂ)) * F ↑(γ • z)

variable (z : ℂ) in
/-- The **weight `k` Laplacian of the holomorphic slash action** (LMFDB `mf.maass.mwf`, remark)
`Δ_k = y² (∂²/∂x² + ∂²/∂y²) - iky (∂/∂x + i ∂/∂y)` at `z = x + iy`. Up to the sign convention of
the LMFDB's Laplacians, this is the weight `k` Laplacian of harmonic weak Maass forms (Bruinier and
Funke). It corresponds to the weight `k` Laplacian `maassLaplacian` of the unitary slash action
under `f = y^{k/2} F` (`maassLaplacian_im_rpow_mul_eq`). -/
noncomputable def holomorphicMaassLaplacian : ℂ :=
  hyperbolicLaplacian F z -
    Complex.I * k * z.im * (fderiv ℝ F z 1 + Complex.I * fderiv ℝ F z Complex.I)

lemma fderiv_im_rpow_mul_one_of_differentiableAt (hG : DifferentiableAt ℝ G w) (hw : 0 < w.im) :
    fderiv ℝ (fun u ↦ ((u.im ^ t : ℝ) : ℂ) * G u) w 1 = (w.im ^ t : ℝ) * fderiv ℝ G w 1 := by
  rw [(hasFDerivAt_im_rpow_mul_of_hasFDerivAt hG.hasFDerivAt hw).fderiv]
  simp

lemma fderiv_im_rpow_mul_I_of_differentiableAt (hG : DifferentiableAt ℝ G w) (hw : 0 < w.im) :
    fderiv ℝ (fun u ↦ ((u.im ^ t : ℝ) : ℂ) * G u) w Complex.I =
      (w.im ^ t : ℝ) * fderiv ℝ G w Complex.I + (w.im ^ (t - 1) : ℝ) * (t * G w) := by
  rw [(hasFDerivAt_im_rpow_mul_of_hasFDerivAt hG.hasFDerivAt hw).fderiv]
  simp
  ring1

variable {k F} in
/-- **The unitary slash action of `y^{k/2} F` is `y^{k/2}` times the holomorphic slash action of
`F`** (LMFDB `mf.maass.mwf`, remark): for `γ = (a, b; c, d)` of determinant `1`,
`exp(-ik Arg(cz + d)) (y^{k/2} F)(γz) = y^{k/2} (cz + d)^{-k} F(γz)`. -/
lemma maassSlash_im_rpow_mul_eq {γ : GL (Fin 2) ℝ} (hγ : γ.det.val = 1) (z : ℍ) :
    maassSlash k (fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * F u) γ z =
      ((z.im ^ (k / 2) : ℝ) : ℂ) * holomorphicSlash k F γ z := by
  have hd : denom γ z ≠ 0 := denom_ne_zero γ z
  have hn : 0 < ‖denom γ z‖ := norm_pos_iff.mpr hd
  have him : ((γ • z : ℍ) : ℂ).im = z.im / ‖denom γ z‖ ^ 2 := by
    rw [coe_im, im_smul_eq_div_normSq, hγ, abs_one, one_mul, normSq_eq_norm_sq]
  have hpow : (z.im / ‖denom γ z‖ ^ 2) ^ (k / 2) = z.im ^ (k / 2) / ‖denom γ z‖ ^ k := by
    rw [Real.div_rpow z.im_pos.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hn.le,
      Nat.cast_ofNat, mul_div_cancel₀ k two_ne_zero]
  have hn' : ((‖denom γ z‖ ^ k : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hn k).ne'
  have hc : denom γ z ^ (k : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (.inl hd)
  rw [maassSlash, him, hpow, holomorphicSlash, cpow_neg]
  push_cast
  field_simp
  linear_combination (((z.im ^ (k / 2) : ℝ) : ℂ) * F ↑(γ • z)) * exp_neg_arg_mul_cpow k hd

variable {k F} in
/-- **The unitary slash action of `y^(k/2) F`**: if `F(γz) = μ (cz + d)^k F(z)` for
`γ = (a, b; c, d)` in `SL(2, ℤ)`, with the principal power of `cz + d`, then `f = y^(k/2) F`
satisfies `exp(-ik Arg(cz + d)) f(γz) = μ f(z)`. -/
lemma maassSlash_im_rpow_mul {γ : SL(2, ℤ)} {z : ℍ} {μ : ℂ}
    (hF : F ↑(γ • z) = μ * denom γ z ^ (k : ℂ) * F z) :
    maassSlash k (fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * F u) γ z =
      μ * (((z.im ^ (k / 2) : ℝ) : ℂ) * F z) := by
  have hc : denom γ z ^ (k : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (.inl (denom_ne_zero γ z))
  rw [maassSlash_im_rpow_mul_eq (by simp) z, holomorphicSlash, ← ModularGroup.sl_moeb, hF, cpow_neg]
  field_simp

variable {F} in
/-- **The weight `k` Laplacians of the two conventions correspond** (LMFDB `mf.maass.mwf`, remark):
for `F` of class `C²` on the upper half-plane,
`Δ_k (y^{k/2} F) = y^{k/2} (Δ^hol_k F + (k/2)(k/2 - 1) F)`, where
`Δ_k = y² (∂²/∂x² + ∂²/∂y²) - iky ∂/∂x` is the Laplacian of the unitary slash action and
`Δ^hol_k = y² (∂²/∂x² + ∂²/∂y²) - iky (∂/∂x + i ∂/∂y)` that of the holomorphic one. -/
lemma maassLaplacian_im_rpow_mul_eq (hF : ContDiffOn ℝ 2 F {u | 0 < u.im}) (hw : 0 < w.im) :
    maassLaplacian k (fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * F u) w = ((w.im ^ (k / 2) : ℝ) : ℂ) *
      (holomorphicMaassLaplacian k F w + k / 2 * (k / 2 - 1) * F w) := by
  have ho : IsOpen {u : ℂ | 0 < u.im} := isOpen_upperHalfPlaneSet
  have hd {u : ℂ} (hu : 0 < u.im) : DifferentiableAt ℝ F u :=
    (hF.differentiableOn (by norm_num)).differentiableAt (ho.mem_nhds hu)
  have hd' (a : ℂ) : DifferentiableAt ℝ (fun u ↦ fderiv ℝ F u a) w :=
    ((hF.fderiv_of_isOpen ho (m := 1) (by norm_num)).differentiableOn (by norm_num)
      |>.differentiableAt (ho.mem_nhds hw)).clm_apply (differentiableAt_const a)
  have hk : DifferentiableAt ℝ (fun u ↦ ((k / 2 : ℝ) : ℂ) * F u) w := (hd hw).const_mul _
  have h1 : (fun u ↦ fderiv ℝ (fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * F u) u 1) =ᶠ[nhds w]
      fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * fderiv ℝ F u 1 := by
    filter_upwards [ho.mem_nhds hw] with u hu using
      fderiv_im_rpow_mul_one_of_differentiableAt (hd hu) hu
  have h2 : (fun u ↦ fderiv ℝ (fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * F u) u Complex.I) =ᶠ[nhds w]
      fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * fderiv ℝ F u Complex.I +
        ((u.im ^ (k / 2 - 1) : ℝ) : ℂ) * ((k / 2 : ℝ) * F u) := by
    filter_upwards [ho.mem_nhds hw] with u hu using
      fderiv_im_rpow_mul_I_of_differentiableAt (hd hu) hu
  have h3 : fderiv ℝ (fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * fderiv ℝ F u Complex.I +
      ((u.im ^ (k / 2 - 1) : ℝ) : ℂ) * ((k / 2 : ℝ) * F u)) w Complex.I =
      fderiv ℝ (fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * fderiv ℝ F u Complex.I) w Complex.I +
        fderiv ℝ (fun u ↦ ((u.im ^ (k / 2 - 1) : ℝ) : ℂ) * ((k / 2 : ℝ) * F u)) w Complex.I := by
    rw [fderiv_fun_add
      (hasFDerivAt_im_rpow_mul_of_hasFDerivAt (hd' _).hasFDerivAt hw).differentiableAt
      (hasFDerivAt_im_rpow_mul_of_hasFDerivAt hk.hasFDerivAt hw).differentiableAt]
    rfl
  have hy : (w.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw.ne'
  rw [maassLaplacian, hyperbolicLaplacian, h1.fderiv_eq, h2.fderiv_eq, h3,
    fderiv_im_rpow_mul_one_of_differentiableAt (hd' 1) hw,
    fderiv_im_rpow_mul_one_of_differentiableAt (hd hw) hw,
    fderiv_im_rpow_mul_I_of_differentiableAt (hd' _) hw,
    fderiv_im_rpow_mul_I_of_differentiableAt hk hw, fderiv_const_mul (hd hw),
    smul_apply, smul_eq_mul, holomorphicMaassLaplacian, hyperbolicLaplacian,
    Real.rpow_sub_one hw.ne', Real.rpow_sub_one hw.ne', Real.rpow_sub_one hw.ne']
  push_cast
  field_simp
  linear_combination (4 * ((w.im ^ (k / 2) : ℝ) : ℂ) * k * w.im * fderiv ℝ F w Complex.I) * I_sq

variable {k F} [Γ.HasDetOne] in
/-- **The transformation laws of the two conventions correspond** (LMFDB `mf.maass.mwf`, remark):
on a subgroup `Γ` of `SL(2, ℝ)`, `f = y^{k/2} F` transforms with a multiplier `v` under the
unitary slash action of weight `k` exactly when `F` transforms with `v` under the holomorphic
slash action of weight `k`. -/
lemma maassSlash_im_rpow_mul_eq_mul_iff : (∀ (γ : Γ) (z : ℍ),
    maassSlash k (fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * F u) γ z =
      v γ * (((z : ℂ).im ^ (k / 2) : ℝ) * F z)) ↔
      ∀ (γ : Γ) (z : ℍ), holomorphicSlash k F γ z = v γ * F z := by
  refine forall₂_congr fun γ z ↦ ?_
  rw [maassSlash_im_rpow_mul_eq (congrArg Units.val (HasDetOne.det_eq γ.2)), coe_im,
    mul_left_comm, mul_right_inj' (ofReal_ne_zero.mpr (Real.rpow_pos_of_pos z.im_pos _).ne')]

variable {F} in
/-- **The Laplace equations of the two conventions correspond** (LMFDB `mf.maass.mwf`, remark):
for `F` of class `C²` on the upper half-plane, `(Δ_k + λ) (y^{k/2} F) = 0` at a point exactly
when `(Δ^hol_k + λ + (k/2)(k/2 - 1)) F = 0` there. -/
lemma maassLaplacian_im_rpow_mul_add_mul_eq_zero_iff (hF : ContDiffOn ℝ 2 F {u | 0 < u.im})
    (hw : 0 < w.im) : maassLaplacian k (fun u ↦ ((u.im ^ (k / 2) : ℝ) : ℂ) * F u) w +
      eigenvalue * (((w.im ^ (k / 2) : ℝ) : ℂ) * F w) = 0 ↔
      holomorphicMaassLaplacian k F w + (eigenvalue + k / 2 * (k / 2 - 1)) * F w = 0 := by
  rw [maassLaplacian_im_rpow_mul_eq k hF hw, mul_left_comm, ← mul_add,
    mul_eq_zero_iff_left (ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hw _).ne')]
  constructor <;> intro h <;> linear_combination h

end UpperHalfPlane
