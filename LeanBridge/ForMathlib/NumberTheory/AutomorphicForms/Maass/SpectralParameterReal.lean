import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.EigenvalueReal

/-!
# The spectral parameter of a Maass form is purely real or purely imaginary

The LMFDB (`mf.maass.exceptional_eigenvalue`) states that every eigenvalue `λ = 1/4 + R²` of a
Maass form is real and nonnegative, and that the spectral parameter `R` is either purely real or
purely imaginary. In the setting of the LMFDB, the Maass forms of weight `0` on `Γ₀(N)` with a
character, the reality of `λ` and its nonnegativity are proved in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.EigenvalueReal` and
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.KernelPair`. This file deduces the
statement on `R`: a complex number whose square is real is real or purely imaginary.

## Main results

* `UpperHalfPlane.re_eq_zero_or_im_eq_zero_of_maassEigenvalue_im_eq_zero`
  (LMFDB `mf.maass.exceptional_eigenvalue`): if `1/4 + R²` is real, `R` is purely imaginary or real.
* `UpperHalfPlane.re_eq_zero_or_im_eq_zero_of_mem_maassSpace`
  (LMFDB `mf.maass.exceptional_eigenvalue`): the spectral parameter of a nonzero Maass form of
  weight `0` on `Γ₀(N)` with a character is purely imaginary or real.
-/

open scoped ComplexConjugate

namespace UpperHalfPlane

variable {R : ℂ}

/-- **A spectral parameter with real eigenvalue is purely imaginary or real**
(LMFDB `mf.maass.exceptional_eigenvalue`). -/
lemma re_eq_zero_or_im_eq_zero_of_maassEigenvalue_im_eq_zero (h : (maassEigenvalue R).im = 0) :
    R.re = 0 ∨ R.im = 0 := by
  simp only [maassEigenvalue, sq, Complex.add_im, Complex.mul_im] at h
  norm_num at h
  rcases mul_eq_zero.mp (by linarith : (2 * R.re) * R.im = 0) with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr h

/-- **The spectral parameter of a nonzero Maass form of weight `0` on `Γ₀(N)` with a character is
purely imaginary or real** (LMFDB `mf.maass.exceptional_eigenvalue`). -/
lemma re_eq_zero_or_im_eq_zero_of_mem_maassSpace {N : ℕ} {χ : DirichletCharacter ℂ N} {F : ℍ → ℂ}
    (hF : F ∈ maassSpace N χ (maassEigenvalue R)) (hF0 : F ≠ 0) : R.re = 0 ∨ R.im = 0 :=
  re_eq_zero_or_im_eq_zero_of_maassEigenvalue_im_eq_zero <|
    Complex.conj_eq_iff_im.mp <| conj_eigenvalue_of_mem_maassSpace hF hF0

end UpperHalfPlane
