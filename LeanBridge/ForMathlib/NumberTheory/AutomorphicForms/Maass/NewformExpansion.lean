import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.FourierExpansionExists
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.TrivialCharacter

/-!
# The cosine and sine expansions of a Maass newform

A Maass newform `F` of weight `0` on `Γ₀(N)` with trivial character and spectral parameter `R`
(`UpperHalfPlane.IsMaassNewform`) is invariant under `z ↦ z + 1`. If its constant term vanishes
and `F` and `∂F/∂y` grow at most polynomially in `y`, uniformly in `x` (hypotheses that are
removed in `LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CuspNewformExpansion`, from
square-integrability alone, and in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.ConstantTerm` for real `R`), then, if
`F` is even, it has the cosine expansion
`F(x + iy) = ∑_{n ≥ 1} a(n) √y K_{iR}(2πny) cos(2πnx)` with `a = maassCoefficients R F` (LMFDB
`mf.maass.mwf.coefficients`), and if it is odd, the sine expansion with these coefficients. The
coefficients are unique (`UpperHalfPlane.HasMaassCosineExpansion.unique`,
`UpperHalfPlane.HasMaassSineExpansion.unique`), so they are a function of `F`. For cusp newforms
(`UpperHalfPlane.IsMaassCuspNewform`, which removes the constant-term hypothesis) the normalised
coefficients `a(n) / a(1)` are real for `n` prime to `N`, and `a(1) ≠ 0` at level `1`
(`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CuspNewform`); `a(1) ≠ 0` at higher
level and the reality of the other coefficients are not proved.

## Main results

* `UpperHalfPlane.IsMaassNewform.hasMaassCosineExpansion_maassCoefficients`: an even newform has the
  cosine expansion with coefficients `maassCoefficients R F`.
* `UpperHalfPlane.IsMaassNewform.hasMaassSineExpansion_maassCoefficients`: an odd newform has the
  sine expansion with coefficients `maassCoefficients R F`.
-/

open Filter CongruenceSubgroup Real

open scoped ContDiff MatrixGroups

namespace UpperHalfPlane

variable {N M : ℕ} {R : ℂ} {F : ℍ → ℂ} {C : ℝ}

lemma IsMaassNewform.comp_add_one (hF : IsMaassNewform N 1 (maassEigenvalue R) F) {z : ℂ}
    (hz : 0 < z.im) : (F ∘ ofComplex) (z + 1) = (F ∘ ofComplex) z := by
  have hT : ModularGroup.T ∈ Gamma0 N := Gamma0_mem.mpr (by simp)
  have h : (F ∘ ofComplex) ↑(ModularGroup.T • ofComplex z) =
      (1 : DirichletCharacter ℂ N) (ModularGroup.T 1 1 : ℤ) * (F ∘ ofComplex) ↑(ofComplex z) :=
    hF.1.1.2.2.1 ModularGroup.T hT (ofComplex z)
  rwa [dirichletCharacter_one_apply_of_mem_gamma0 hT, one_mul, modular_T_smul, coe_vadd,
    ofComplex_apply_of_im_pos hz, coe_mk, Complex.ofReal_one, add_comm] at h

/-- **The cosine expansion of an even Maass newform** (LMFDB `mf.maass.mwf.coefficients`): an even
Maass newform `F` of weight `0` on `Γ₀(N)` with trivial character and eigenvalue `1/4 + R²`, with
vanishing constant term and with `F` and `∂F/∂y` of polynomial growth in `y` uniformly in `x`, has
the cosine expansion `F(x + iy) = ∑_{n ≥ 1} a(n) √y K_{iR}(2πny) cos(2πnx)` with the coefficients
`a = maassCoefficients R F`. -/
lemma IsMaassNewform.hasMaassCosineExpansion_maassCoefficients
    (hF : IsMaassNewform N 1 (maassEigenvalue R) F)
    (h0 : ∀ y : ℝ, 0 < y → ∫ t in (0 : ℝ)..1, (F ∘ ofComplex) (t + y * Complex.I) = 0)
    (hb : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ, ‖(F ∘ ofComplex) (t + y * Complex.I)‖ ≤ C * y ^ M)
    (hb' : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ,
      ‖fderiv ℝ (F ∘ ofComplex) (t + y * Complex.I) Complex.I‖ ≤ C * y ^ M)
    (hs : IsEvenMaassForm (F ∘ ofComplex)) :
    HasMaassCosineExpansion (F ∘ ofComplex) R (maassCoefficients R (F ∘ ofComplex)) :=
  UpperHalfPlane.hasMaassCosineExpansion_maassCoefficients hF.1.1.1 (fun _ ↦ hF.comp_add_one)
    hF.1.1.2.2.2 h0 hb hb' hs

/-- **The sine expansion of an odd Maass newform** (LMFDB `mf.maass.mwf.coefficients`): an odd
Maass newform `F` of weight `0` on `Γ₀(N)` with trivial character and eigenvalue `1/4 + R²`, with
vanishing constant term and with `F` and `∂F/∂y` of polynomial growth in `y` uniformly in `x`, has
the sine expansion `F(x + iy) = ∑_{n ≥ 1} a(n) √y K_{iR}(2πny) sin(2πnx)` with the coefficients
`a = maassCoefficients R F`. -/
lemma IsMaassNewform.hasMaassSineExpansion_maassCoefficients
    (hF : IsMaassNewform N 1 (maassEigenvalue R) F)
    (h0 : ∀ y : ℝ, 0 < y → ∫ t in (0 : ℝ)..1, (F ∘ ofComplex) (t + y * Complex.I) = 0)
    (hb : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ, ‖(F ∘ ofComplex) (t + y * Complex.I)‖ ≤ C * y ^ M)
    (hb' : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ,
      ‖fderiv ℝ (F ∘ ofComplex) (t + y * Complex.I) Complex.I‖ ≤ C * y ^ M)
    (hs : IsOddMaassForm (F ∘ ofComplex)) :
    HasMaassSineExpansion (F ∘ ofComplex) R (maassCoefficients R (F ∘ ofComplex)) :=
  UpperHalfPlane.hasMaassSineExpansion_maassCoefficients hF.1.1.1 (fun _ ↦ hF.comp_add_one)
    hF.1.1.2.2.2 h0 hb hb' hs

end UpperHalfPlane
