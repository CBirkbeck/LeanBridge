import LeanBridge.ForMathlib.Analysis.Fourier.PeriodicFourierSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# The Fourier series in `x` of a smooth periodic function on the upper half-plane

A smooth function `f` on the upper half-plane with `f(z + 1) = f(z)`, such as a Maass form on
`Γ₀(N)` (invariant under `!![1, 1; 0, 1]`), has at every height `y > 0` the absolutely convergent
Fourier expansion `f(x + iy) = ∑_{n ∈ ℤ} a_n(y) e^{2πinx}`, with
`a_n(y) = ∫_0^1 f(t + iy) e^{-2πint} dt`: the function `x ↦ f(x + iy)` is smooth and periodic. This
is the first step of the Fourier expansion of a Maass form (LMFDB `mf.maass.mwf.fourierexpansion`,
`mf.maass.mwf.coefficients`), whose coefficients `a_n(y)` are then multiples of
`√y K_{iR}(2π|n|y)` (`Complex.eq_div_mul_sqrt_mul_besselK_of_ode`) once they are known to satisfy
the differential equation coming from `Δf = -λf` and to grow at most polynomially; those two steps
are not proved here.

## Main results

* `UpperHalfPlane.hasSum_fourierCoeffOn_mul_exp`: the Fourier expansion in `x`.
-/

open Function Real Set

open scoped ContDiff

namespace UpperHalfPlane

variable {f : ℂ → ℂ} {y : ℝ} (v : ℂ) (x : ℝ)

lemma contDiffOn_fderiv_apply (hf : ContDiffOn ℝ ∞ f {z | 0 < z.im}) :
    ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ f w v) {z | 0 < z.im} :=
  (hf.fderiv_of_isOpen isOpen_upperHalfPlaneSet le_rfl).clm_apply contDiffOn_const

lemma hasDerivAt_comp_add_mul_I (hf : ContDiffOn ℝ ∞ f {z | 0 < z.im}) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ ↦ f (t + y * Complex.I)) (fderiv ℝ f (x + y * Complex.I) 1) x := by
  have hx : 0 < ((x : ℂ) + y * Complex.I).im := by
    simpa using hy
  have h1 : HasDerivAt (fun t : ℝ ↦ (t : ℂ) + y * Complex.I) 1 x :=
    (hasDerivAt_id x).ofReal_comp.add_const _
  exact ((hf.differentiableOn (by simp)).differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds hx)).hasFDerivAt.comp_hasDerivAt x h1

lemma periodic_fderiv_apply (hper : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z) {z : ℂ} (hz : 0 < z.im) :
    fderiv ℝ f (z + 1) v = fderiv ℝ f z v := by
  have h : (fun w ↦ f (w + 1)) =ᶠ[nhds z] f :=
    Filter.eventually_of_mem (isOpen_upperHalfPlaneSet.mem_nhds hz) fun w hw ↦ hper w hw
  rw [← fderiv_comp_add_right, h.fderiv_eq]

/-- **The Fourier expansion in `x`** of a smooth function `f` on the upper half-plane with
`f(z + 1) = f(z)`: at every height `y > 0`, `f(x + iy) = ∑_{n ∈ ℤ} a_n(y) e^{2πinx}` with
`a_n(y) = ∫_0^1 f(t + iy) e^{-2πint} dt`, the series converging absolutely
(`summable_fourierCoeffOn_of_periodic`). -/
lemma hasSum_fourierCoeffOn_mul_exp (hf : ContDiffOn ℝ ∞ f {z | 0 < z.im})
    (hper : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z) (hy : 0 < y) : HasSum (fun n : ℤ ↦
      fourierCoeffOn (lt_add_of_pos_right 0 one_pos) (fun t : ℝ ↦ f (t + y * Complex.I)) n *
        Complex.exp (2 * π * Complex.I * n * x)) (f (x + y * Complex.I)) := by
  have hT : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have ht (t : ℝ) : 0 < ((t : ℂ) + y * Complex.I).im := by
    simpa using hy
  have e (t : ℝ) : ((t + 1 : ℝ) : ℂ) + y * Complex.I = t + y * Complex.I + 1 := by
    push_cast
    ring1
  have hf1 : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ f w 1) {z | 0 < z.im} := contDiffOn_fderiv_apply 1 hf
  have h : HasSum (fun n : ℤ ↦ fourierCoeffOn (lt_add_of_pos_right 0 hT.out)
      (fun t : ℝ ↦ f (t + y * Complex.I)) n • fourier n (x : AddCircle (1 : ℝ)))
      (f (x + y * Complex.I)) :=
    hasSum_fourierCoeffOn_of_periodic (hasDerivAt_comp_add_mul_I · hf hy)
      (hasDerivAt_comp_add_mul_I · hf1 hy)
      ((contDiffOn_fderiv_apply 1 hf1).continuousOn.comp_continuous (by fun_prop) ht)
      (fun t ↦ (congrArg f (e t)).trans (hper _ (ht t))) x
  convert h using 1
  funext n
  rw [smul_eq_mul, fourier_coe_apply, Complex.ofReal_one, div_one]

end UpperHalfPlane
