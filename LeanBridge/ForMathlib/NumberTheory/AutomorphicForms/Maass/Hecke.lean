import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.UpperHalfPlane

/-!
# Hecke operators on Maass forms of weight zero

For a prime `p ∤ N`, the Hecke operator on functions on the upper half-plane is
`(T_p f)(z) = p^{-1/2} (f(pz) + ∑_{j < p} f((z + j)/p))`, normalised so that the Fourier
coefficient `a(p)` of a Hecke eigenform with `a(1) = 1` is its eigenvalue, as in the LMFDB knowls
`mf.maass.mwf.fourierexpansion` and `mf.maass.mwf.coefficients`. Each term is the composition of
`f` with a real affine map `z ↦ cz + b`, `c > 0`, an isometry of `ℍ`, so `T_p` commutes with the
hyperbolic Laplacian.

## Main definitions

* `UpperHalfPlane.maassHeckeOperator`: the Hecke operator `T_p`.
* `UpperHalfPlane.IsMaassHeckeEigenform` (LMFDB `mf.maass.mwf.fourierexpansion`,
  `mf.maass.mwf.coefficients`): Maass forms on `Γ₀(N)` that are eigenfunctions of every `T_p`,
  `p ∤ N`.

## Main results

* `UpperHalfPlane.hyperbolicLaplacian_comp_affine`: the hyperbolic Laplacian commutes with real
  affine maps.
* `UpperHalfPlane.hyperbolicLaplacian_maassHeckeOperator`: `Δ T_p f = T_p Δ f` on `ℍ`.
* `UpperHalfPlane.hyperbolicLaplacian_maassHeckeOperator_add_mul_eq_zero`: `T_p` preserves the
  eigenspaces of `Δ`.
* `UpperHalfPlane.IsMaassHeckeEigenform.heckeEigenvalue_eq`: the Hecke eigenvalues of a Maass Hecke
  eigenform are unique.
-/

open CongruenceSubgroup

open Matrix (SpecialLinearGroup.mapGL)

namespace UpperHalfPlane

variable {p : ℕ} {f g : ℂ → ℂ} {N : ℕ} {z : ℂ} {n : WithTop ℕ∞} {eigenvalue : ℂ}
  {heckeEigenvalue : ℕ → ℂ}

lemma fderiv_comp_affine_apply (c : ℝ) (b w v : ℂ) :
    fderiv ℝ (fun u ↦ g (c * u + b)) w v = c * fderiv ℝ g (c * w + b) v := by
  have h : fderiv ℝ (fun u ↦ g (c • u + b)) w = c • fderiv ℝ g (c • w + b) := by
    rw [fderiv_comp_smul (f := fun u ↦ g (u + b)), fderiv_comp_add_right]
  simpa [Complex.real_smul] using congrArg (· v) h

lemma fderiv_ofReal_mul (c : ℝ) (w : ℂ) :
    fderiv ℝ (fun u ↦ (c : ℂ) * g u) w = c • fderiv ℝ g w := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · let i : Invertible c := invertibleOfNonzero hc
    have h : (fun u ↦ (c : ℂ) * g u) = c • g := funext fun u ↦ (Complex.real_smul ..).symm
    rw [h]
    exact fderiv_const_smul_of_invertible c

/-- **The hyperbolic Laplacian commutes with real affine maps** `z ↦ cz + b`, which for `c > 0`
are isometries of `ℍ`. -/
lemma hyperbolicLaplacian_comp_affine (c b : ℝ) :
    hyperbolicLaplacian (fun u ↦ f (c * u + b)) z = hyperbolicLaplacian f (c * z + b) := by
  simp only [hyperbolicLaplacian, fderiv_comp_affine_apply]
  rw [fderiv_ofReal_mul, fderiv_ofReal_mul, smul_apply, smul_apply,
    fderiv_comp_affine_apply (g := fun w ↦ fderiv ℝ f w 1),
    fderiv_comp_affine_apply (g := fun w ↦ fderiv ℝ f w Complex.I)]
  simp [Complex.real_smul]
  ring1

lemma differentiableAt_fderiv_apply (hg : ContDiffAt ℝ 2 g z) (v : ℂ) :
    DifferentiableAt ℝ (fun w ↦ fderiv ℝ g w v) z :=
  ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
    (differentiableAt_const v)

lemma hyperbolicLaplacian_sum {ι : Type*} (s : Finset ι) {G : ι → ℂ → ℂ}
    (hG : ∀ i ∈ s, ContDiffAt ℝ 2 (G i) z) :
    hyperbolicLaplacian (fun w ↦ ∑ i ∈ s, G i w) z = ∑ i ∈ s, hyperbolicLaplacian (G i) z := by
  have hev (v : ℂ) : (fun w ↦ fderiv ℝ (fun u ↦ ∑ i ∈ s, G i u) w v) =ᶠ[nhds z]
      fun w ↦ ∑ i ∈ s, fderiv ℝ (G i) w v := by
    filter_upwards [s.eventually_all.mpr fun i hi ↦ (hG i hi).eventually (by simp)] with w hw
    rw [fderiv_fun_sum fun i hi ↦ (hw i hi).differentiableAt (by norm_num), sum_apply]
  simp only [hyperbolicLaplacian, (hev 1).fderiv_eq, (hev Complex.I).fderiv_eq,
    fderiv_fun_sum fun i hi ↦ differentiableAt_fderiv_apply (hG i hi) _, sum_apply]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]

lemma hyperbolicLaplacian_const_mul (c : ℂ) (hg : ContDiffAt ℝ 2 g z) :
    hyperbolicLaplacian (fun w ↦ c * g w) z = c * hyperbolicLaplacian g z := by
  have hev (v : ℂ) : (fun w ↦ fderiv ℝ (fun u ↦ c * g u) w v) =ᶠ[nhds z]
      fun w ↦ c * fderiv ℝ g w v := by
    filter_upwards [hg.eventually (by simp)] with w hw
    rw [fderiv_const_mul (hw.differentiableAt (by norm_num)), smul_apply, smul_eq_mul]
  simp only [hyperbolicLaplacian, (hev 1).fderiv_eq, (hev Complex.I).fderiv_eq,
    fderiv_const_mul (differentiableAt_fderiv_apply hg _), smul_apply, smul_eq_mul]
  ring1

lemma hyperbolicLaplacian_add (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    hyperbolicLaplacian (fun w ↦ f w + g w) z =
      hyperbolicLaplacian f z + hyperbolicLaplacian g z := by
  simpa using hyperbolicLaplacian_sum (G := ![f, g]) Finset.univ <| by
    simp [Fin.forall_fin_two, hf, hg]

lemma contDiffAt_comp_affine (hf : ContDiffOn ℝ n f {w | 0 < w.im}) {c : ℝ} (hc : 0 < c) (b : ℝ)
    (hz : 0 < z.im) : ContDiffAt ℝ n (fun u ↦ f (c * u + b)) z := by
  refine (hf.contDiffAt <| (isOpen_lt continuous_const Complex.continuous_im).mem_nhds ?_).comp z
    ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)
  simpa using mul_pos hc hz

variable (p f) in
/-- The **Hecke operator** `T_p` on functions on the upper half-plane, given on `ℂ`:
`(T_p f)(z) = p^{-1/2} (f(pz) + ∑_{j < p} f((z + j)/p))`, the sum of `f` composed with the `p + 1`
matrices `diag(p, 1)` and `!![1, j; 0, p]` acting on `ℍ`, scaled by `p^{-1/2}`. This is the
normalisation of the LMFDB (`mf.maass.mwf.fourierexpansion`, `mf.maass.mwf.coefficients`): the
`p`-th Fourier coefficient of an eigenform with `a(1) = 1` is its `T_p`-eigenvalue
(`HasMaassFourierExpansion.coeff_prime_eq`). It is meant for primes `p ∤ N` on `Γ₀(N)`, where it
preserves `Γ₀(N)`-invariance (`maassHeckeOperator_smul_eq`). -/
noncomputable def maassHeckeOperator (z : ℂ) : ℂ :=
  ((√p)⁻¹ : ℝ) * (f (p * z) + ∑ j ∈ Finset.range p, f ((z + j) / p))

lemma maassHeckeOperator_eq_affine (hp : p ≠ 0) :
    maassHeckeOperator p f = fun z ↦ ((√p)⁻¹ : ℝ) * ((fun u ↦ f ((p : ℝ) * u + (0 : ℝ))) z +
      ∑ j ∈ Finset.range p, (fun u ↦ f (((p : ℝ)⁻¹ : ℝ) * u + ((j : ℝ) / p : ℝ))) z) := by
  ext z
  simp only [maassHeckeOperator]
  congr 2
  · simp
  · refine Finset.sum_congr rfl fun j _ ↦ congrArg f ?_
    have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
    push_cast
    field_simp

lemma contDiffAt_maassHeckeOperator (hp : p ≠ 0) (hf : ContDiffOn ℝ n f {w | 0 < w.im})
    (hz : 0 < z.im) : ContDiffAt ℝ n (maassHeckeOperator p f) z := by
  have hp' : (0 : ℝ) < p := by positivity
  rw [maassHeckeOperator_eq_affine hp]
  exact contDiffAt_const.mul <| (contDiffAt_comp_affine hf hp' 0 hz).add <|
    ContDiffAt.sum fun j _ ↦ contDiffAt_comp_affine hf (inv_pos.mpr hp') _ hz

lemma contDiffOn_maassHeckeOperator (hp : p ≠ 0) (hf : ContDiffOn ℝ n f {w | 0 < w.im}) :
    ContDiffOn ℝ n (maassHeckeOperator p f) {w | 0 < w.im} :=
  fun _ hz ↦ (contDiffAt_maassHeckeOperator hp hf hz).contDiffWithinAt

/-- **`T_p` commutes with the hyperbolic Laplacian** on functions that are twice continuously
differentiable on `ℍ`: `T_p` is a combination of compositions with the isometries `z ↦ pz` and
`z ↦ (z + j)/p` of `ℍ`. -/
lemma hyperbolicLaplacian_maassHeckeOperator (hp : p ≠ 0) (hf : ContDiffOn ℝ 2 f {w | 0 < w.im})
    (hz : 0 < z.im) :
    hyperbolicLaplacian (maassHeckeOperator p f) z =
      maassHeckeOperator p (hyperbolicLaplacian f) z := by
  have hp' : (0 : ℝ) < p := by positivity
  rw [maassHeckeOperator_eq_affine hp, maassHeckeOperator_eq_affine hp,
    hyperbolicLaplacian_const_mul, hyperbolicLaplacian_add, hyperbolicLaplacian_sum,
    hyperbolicLaplacian_comp_affine]
  simp only [hyperbolicLaplacian_comp_affine]
  · exact fun j _ ↦ contDiffAt_comp_affine hf (inv_pos.mpr hp') _ hz
  · exact contDiffAt_comp_affine hf hp' 0 hz
  · exact ContDiffAt.sum fun j _ ↦ contDiffAt_comp_affine hf (inv_pos.mpr hp') _ hz
  · exact (contDiffAt_comp_affine hf hp' 0 hz).add <|
      ContDiffAt.sum fun j _ ↦ contDiffAt_comp_affine hf (inv_pos.mpr hp') _ hz

/-- **`T_p` preserves the eigenspaces of the hyperbolic Laplacian**: if `(Δ + λ) f = 0` on `ℍ`,
then `(Δ + λ) T_p f = 0` on `ℍ`. -/
lemma hyperbolicLaplacian_maassHeckeOperator_add_mul_eq_zero (hp : p ≠ 0)
    (hf : ContDiffOn ℝ 2 f {w | 0 < w.im})
    (h : ∀ w : ℂ, 0 < w.im → hyperbolicLaplacian f w + eigenvalue * f w = 0) (hz : 0 < z.im) :
    hyperbolicLaplacian (maassHeckeOperator p f) z + eigenvalue * maassHeckeOperator p f z = 0 := by
  have hp' : (0 : ℝ) < p := by positivity
  have h' (w : ℂ) (hw : 0 < w.im) : hyperbolicLaplacian f w = -eigenvalue * f w := by
    linear_combination h w hw
  rw [hyperbolicLaplacian_maassHeckeOperator hp hf hz]
  simp only [maassHeckeOperator]
  rw [h' _ (by simpa using mul_pos hp' hz),
    Finset.sum_congr rfl fun j _ ↦ h' _ (by simpa using div_pos hz hp'), ← Finset.mul_sum]
  ring1

variable (f N eigenvalue heckeEigenvalue) in
/-- A **Maass Hecke eigenform** of weight `0` on `Γ₀(N)`, with Laplace eigenvalue `λ` and Hecke
eigenvalues `λ_p` (LMFDB `mf.maass.mwf.fourierexpansion`, `mf.maass.mwf.coefficients`): a Maass
form of weight `0` on `Γ₀(N)` with eigenvalue `λ` (`IsMaassForm`) that does not vanish identically
on `ℍ` and satisfies `T_p f = λ_p f` on `ℍ` for every prime `p ∤ N`, with `T_p` the
`maassHeckeOperator`. Only the values `λ_p` at primes `p ∤ N` matter, and they are unique
(`IsMaassHeckeEigenform.heckeEigenvalue_eq`). -/
def IsMaassHeckeEigenform : Prop :=
  IsMaassForm ((Gamma0 N).map (SpecialLinearGroup.mapGL ℝ)) f eigenvalue ∧
    (∃ z : ℂ, 0 < z.im ∧ f z ≠ 0) ∧ ∀ p : ℕ, p.Prime → ¬p ∣ N → ∀ z : ℂ, 0 < z.im →
      maassHeckeOperator p f z = heckeEigenvalue p * f z

/-- **The Hecke eigenvalues of a Maass Hecke eigenform are unique** at the primes `p ∤ N`. -/
lemma IsMaassHeckeEigenform.heckeEigenvalue_eq {eigenvalue' : ℂ} {heckeEigenvalue' : ℕ → ℂ}
    (hf : IsMaassHeckeEigenform f N eigenvalue heckeEigenvalue)
    (hf' : IsMaassHeckeEigenform f N eigenvalue' heckeEigenvalue') (hp : p.Prime) (hpN : ¬p ∣ N) :
    heckeEigenvalue p = heckeEigenvalue' p := by
  rcases hf.2.1 with ⟨z, hz, hfz⟩
  exact mul_right_cancel₀ hfz <| (hf.2.2 p hp hpN z hz).symm.trans <| hf'.2.2 p hp hpN z hz

end UpperHalfPlane
