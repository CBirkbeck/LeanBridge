import LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselK
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.MaassPicard

/-!
# Spectral parameters and Fourier expansions of Maass forms on the Picard group

A Maass form `f` on `PSL(2, ℤ[i])` satisfies `(Δ + λ) f = 0`; the LMFDB calls `λ` the true
eigenvalue and the spectral parameter `r`, with `λ = r² + 1`, the eigenvalue. Its Fourier expansion
is `f(x, y) = Σ_{n ∈ ℤ[i]} a(n) y K_{ir}(2π|n|y) e^{2πi Re(nx)}`.

## Main definitions

* `HyperbolicThreeSpace.picardTrueEigenvalue` (LMFDB `mf.maass.picard.eigenvalue`): the true
  eigenvalue `r² + 1` of the spectral parameter `r`.
* `HyperbolicThreeSpace.HasPicardSpectralParameter` (LMFDB `mf.maass.picard.eigenvalue`): a Maass
  form with spectral parameter `r`.
* `HyperbolicThreeSpace.picardFourierTerm` (LMFDB `mf.maass.picard.fourierexpansion`): the terms
  of the Fourier expansion.
* `HyperbolicThreeSpace.HasPicardFourierExpansion` (LMFDB `mf.maass.picard.fourierexpansion`):
  `f` has the Fourier expansion with coefficients `a`.

## Main results

* `HyperbolicThreeSpace.IsPicardMaassForm.eigenvalue_eq`: a nonzero Maass form has a unique true
  eigenvalue.
* `HyperbolicThreeSpace.HasPicardSpectralParameter.eq_or_eq_neg`: its spectral parameter is unique
  up to sign.
-/

open Complex Real

namespace HyperbolicThreeSpace

variable {f : ℂ × ℝ → ℂ} {p : ℂ × ℝ} {r s : ℂ}

/-- The **true eigenvalue** `λ = r² + 1` (LMFDB `mf.maass.picard.eigenvalue`) attached to the
**spectral parameter** `r` of a Maass form on hyperbolic 3-space, which the LMFDB calls the
**eigenvalue**. -/
def picardTrueEigenvalue (r : ℂ) : ℂ :=
  r ^ 2 + 1

/-- A Maass form `f` on `PSL(2, ℤ[i])` has **spectral parameter** `r` (LMFDB
`mf.maass.picard.eigenvalue`, where `r` is called the **eigenvalue**) if `(Δ + λ) f = 0` for the
**true eigenvalue** `λ = r² + 1`. The spectral parameter is only determined up to sign
(`HasPicardSpectralParameter.eq_or_eq_neg`); for the cusp forms in the LMFDB it is real, and the
LMFDB lists the positive one. -/
def HasPicardSpectralParameter (f : ℂ × ℝ → ℂ) (r : ℂ) : Prop :=
  IsPicardMaassForm f (picardTrueEigenvalue r)

/-- A **nonzero Maass form has a unique true eigenvalue**: if `f(p) ≠ 0` at some point `p` of
`ℋ₃`, the eigenvalue equation at `p` determines `λ`. -/
lemma IsPicardMaassForm.eigenvalue_eq {a b : ℂ} (ha : IsPicardMaassForm f a)
    (hb : IsPicardMaassForm f b) (hp : 0 < p.2) (hf : f p ≠ 0) : a = b := by
  have h : (a - b) * f p = 0 := by
    linear_combination ha.2.2.2 p hp - hb.2.2.2 p hp
  exact sub_eq_zero.mp <| (mul_eq_zero.mp h).resolve_right hf

lemma hasPicardSpectralParameter_neg_iff :
    HasPicardSpectralParameter f (-r) ↔ HasPicardSpectralParameter f r := by
  simp only [HasPicardSpectralParameter, picardTrueEigenvalue, neg_sq]

/-- The **spectral parameter** of a nonzero Maass form **is unique up to sign**. -/
lemma HasPicardSpectralParameter.eq_or_eq_neg (hr : HasPicardSpectralParameter f r)
    (hs : HasPicardSpectralParameter f s) (hp : 0 < p.2) (hf : f p ≠ 0) : s = r ∨ s = -r := by
  have h : s ^ 2 = r ^ 2 := by
    simpa only [picardTrueEigenvalue, add_left_inj] using hs.eigenvalue_eq hr hp hf
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h

/-- The `n`-th term `a(n) y K_{ir}(2π|n|y) e^{2πi Re(nx)}` at `(x, y)` of the **Fourier expansion**
(LMFDB `mf.maass.picard.fourierexpansion`) of a Maass form on `PSL(2, ℤ[i])` with spectral parameter
`r` and coefficients `a`. It is only meaningful for `n ≠ 0`: `K_{ir}(0)` diverges. -/
noncomputable def picardFourierTerm (r : ℂ) (a : GaussianInt → ℂ) (p : ℂ × ℝ) (n : GaussianInt) :
    ℂ :=
  a n * p.2 * besselK (I * r) (2 * π * ‖(n : ℂ)‖ * p.2) * exp (2 * π * I * ((n : ℂ) * p.1).re)

/-- A function `f` on `ℋ₃` has the **Fourier expansion** (LMFDB `mf.maass.picard.fourierexpansion`)
`f(x, y) = Σ_{n ∈ ℤ[i]} a(n) y K_{ir}(2π|n|y) e^{2πi Re(nx)}` with spectral parameter `r` and
coefficients `a`, the series converging (unconditionally) at every point of `ℋ₃`.

The term `n = 0` of the LMFDB's sum is undefined, as `K_{ir}(0)` diverges, so the sum runs over
`n ≠ 0` and `a(0)` plays no role: this is the expansion of a Maass cusp form, whose constant term
vanishes. The Maass forms on `PSL(2, ℤ[i])` that are not cusp forms are the constants, which have
no expansion of this shape. That every Maass cusp form with spectral parameter `r` has such an
expansion is a theorem, not proved here. -/
def HasPicardFourierExpansion (f : ℂ × ℝ → ℂ) (r : ℂ) (a : GaussianInt → ℂ) : Prop :=
  ∀ p : ℂ × ℝ, 0 < p.2 →
    HasSum (fun n : {n : GaussianInt // n ≠ 0} ↦ picardFourierTerm r a p n) (f p)

end HyperbolicThreeSpace
