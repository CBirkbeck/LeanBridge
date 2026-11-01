import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.NewformCoefficientsReal
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.NewformExpansion

/-!
# Maass cusp newforms

The LMFDB's Maass forms (`mf.maass.mwf`) are written as square-integrable eigenfunctions, a class
that contains the constant `1` of level `1` (`UpperHalfPlane.isMaassNewform_const_one`), which has
no cosine or sine expansion; the forms of the database, and those of the knowl
`mf.maass.mwf.coefficients`, are cusp forms. A Maass cusp newform of weight `0` on `Γ₀(N)` with
trivial character and spectral parameter `R` is a Maass newform (`UpperHalfPlane.IsMaassNewform`)
whose constant term vanishes at every cusp: `∫_0^N F(γ(t + iy)) dt = 0` for every
`γ ∈ SL(2, ℤ)` and `y > 0`. Here `N` is a common period: `F ∘ γ` is invariant under `z ↦ z + N`,
as `γ T^N γ⁻¹ ∈ Γ(N) ≤ Γ₀(N)`, so the integral is a multiple of the constant term at the cusp
`γ ∞`.

At the cusp `∞` this gives the vanishing constant term `∫_0^1 F(t + iy) dt = 0` of the existence
theorems of the cosine and sine expansions, which hold for Maass cusp newforms provided `F` and
`∂F/∂y` grow at most polynomially at `∞`. These growth bounds are hypotheses here: they hold for
Maass cusp forms (which decay exponentially at the cusps, with their derivatives), a consequence of
the cuspidality and of the eigenvalue equation that is not proved. With them, the coefficients
`a(n) / a(1)`, `a = maassCoefficients R F`, of the cusp newform normalised by `a(1) = 1` are real
at every index `n` prime to `N`, provided `a(1) ≠ 0`, which holds at level `1`
(`UpperHalfPlane.IsMaassNewform.coeff_one_ne_zero_of_hasMaassCosineExpansion`).

## Main definitions

* `UpperHalfPlane.IsMaassCuspNewform` (LMFDB `mf.maass.mwf.coefficients`): Maass cusp newforms of
  weight `0` on `Γ₀(N)` with trivial character.

## Main results

* `UpperHalfPlane.not_isMaassCuspNewform_const_one`: the constant `1` is not a cusp newform.
* `UpperHalfPlane.IsMaassCuspNewform.integral_eq_zero`: the constant term at `∞` vanishes.
* `UpperHalfPlane.IsMaassCuspNewform.hasMaassCosineExpansion_maassCoefficients`,
  `UpperHalfPlane.IsMaassCuspNewform.hasMaassSineExpansion_maassCoefficients`: an even (odd) Maass
  cusp newform of polynomial growth has the cosine (sine) expansion with the coefficients
  `maassCoefficients R F`.
* `UpperHalfPlane.IsMaassCuspNewform.conj_maassCoefficients_div_of_isEvenMaassForm`,
  `UpperHalfPlane.IsMaassCuspNewform.conj_maassCoefficients_div_of_isOddMaassForm`: the
  coefficients prime to `N` of the normalised Maass cusp newform of polynomial growth are real.
* `UpperHalfPlane.IsMaassCuspNewform.maassCoefficients_one_ne_zero_of_isEvenMaassForm`,
  `UpperHalfPlane.IsMaassCuspNewform.maassCoefficients_one_ne_zero_of_isOddMaassForm`: at level
  `1`, `a(1) ≠ 0`, so that all the coefficients of the normalised cusp newform are real.
-/

open Filter

open scoped ComplexConjugate MatrixGroups

namespace UpperHalfPlane

variable (N : ℕ) (R : ℂ) (F : ℍ → ℂ)

/-- A **Maass cusp newform** (LMFDB `mf.maass.mwf.coefficients`) of weight `0` on `Γ₀(N)` with
trivial character and spectral parameter `R`: a Maass newform (`IsMaassNewform`) with eigenvalue
`1/4 + R²` whose constant term vanishes at every cusp, `∫_0^N F(γ(t + iy)) dt = 0` for every
`γ ∈ SL(2, ℤ)` and `y > 0` (`N` is a period of `F ∘ γ`). This is the class of the LMFDB's data,
on which the cosine and sine expansions of the knowl hold; without the cuspidality the constant
`1` of level `1` is a newform without expansion (`isMaassNewform_const_one`). -/
def IsMaassCuspNewform : Prop :=
  IsMaassNewform N 1 (maassEigenvalue R) F ∧ ∀ γ : SL(2, ℤ), ∀ y : ℝ, 0 < y →
    ∫ t in (0 : ℝ)..N, F (γ • ofComplex (t + y * Complex.I)) = 0

variable {N R F} [NeZero N] {C : ℝ} {M : ℕ}

variable (N R) in
/-- **The constant function `1` is not a Maass cusp newform**, its constant term
`∫_0^N 1 dt = N` at `∞` being nonzero: the cuspidality excludes the newform
`isMaassNewform_const_one` that has no cosine or sine expansion. -/
lemma not_isMaassCuspNewform_const_one : ¬IsMaassCuspNewform N R fun _ ↦ 1 := fun h ↦
  NeZero.ne N <| by simpa using h.2 1 1 one_pos

/-- **The constant term at `∞` of a Maass cusp newform vanishes**: `∫_0^1 F(t + iy) dt = 0` for
every `y > 0`, the integral over `[0, N]` being `N` times this one by `1`-periodicity. -/
lemma IsMaassCuspNewform.integral_eq_zero (hF : IsMaassCuspNewform N R F) {y : ℝ} (hy : 0 < y) :
    ∫ t in (0 : ℝ)..1, (F ∘ ofComplex) (t + y * Complex.I) = 0 := by
  have hper : Function.Periodic (fun t : ℝ ↦ (F ∘ ofComplex) (t + y * Complex.I)) 1 := fun t ↦ by
    have h : (F ∘ ofComplex) (t + y * Complex.I + 1) = (F ∘ ofComplex) (t + y * Complex.I) :=
      hF.1.comp_add_one (by simpa using hy)
    simpa [add_right_comm] using h
  have hcont : Continuous fun t : ℝ ↦ (F ∘ ofComplex) (t + y * Complex.I) :=
    hF.1.1.1.1.continuousOn.comp_continuous (by fun_prop) fun t ↦ by simpa using hy
  have h : ∫ t in (0 : ℝ)..0 + (N : ℤ) • (1 : ℝ), (F ∘ ofComplex) (t + y * Complex.I) =
      (N : ℤ) • ∫ t in (0 : ℝ)..0 + 1, (F ∘ ofComplex) (t + y * Complex.I) :=
    hper.intervalIntegral_add_zsmul_eq N 0 fun _ _ ↦ hcont.intervalIntegrable _ _
  have h0 : ∫ t in (0 : ℝ)..N, F ((1 : SL(2, ℤ)) • ofComplex (t + y * Complex.I)) = 0 :=
    hF.2 1 y hy
  simp only [one_smul] at h0
  simp only [zero_add, zsmul_eq_mul, mul_one, Int.cast_natCast, Function.comp_apply] at h
  rw [h0, eq_comm, mul_eq_zero] at h
  exact h.resolve_left (Nat.cast_ne_zero.mpr (NeZero.ne N))

/-- **The cosine expansion of an even Maass cusp newform** (LMFDB `mf.maass.mwf.coefficients`): an
even Maass cusp newform `F` of weight `0` on `Γ₀(N)` with spectral parameter `R`, with `F` and
`∂F/∂y` of polynomial growth in `y` uniformly in `x`, has the cosine expansion
`F(x + iy) = ∑_{n ≥ 1} a(n) √y K_{iR}(2πny) cos(2πnx)` with the coefficients
`a = maassCoefficients R F`. -/
lemma IsMaassCuspNewform.hasMaassCosineExpansion_maassCoefficients (hF : IsMaassCuspNewform N R F)
    (hb : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ, ‖(F ∘ ofComplex) (t + y * Complex.I)‖ ≤ C * y ^ M)
    (hb' : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ,
      ‖fderiv ℝ (F ∘ ofComplex) (t + y * Complex.I) Complex.I‖ ≤ C * y ^ M)
    (hs : IsEvenMaassForm (F ∘ ofComplex)) :
    HasMaassCosineExpansion (F ∘ ofComplex) R (maassCoefficients R (F ∘ ofComplex)) :=
  hF.1.hasMaassCosineExpansion_maassCoefficients (fun _ hy ↦ hF.integral_eq_zero hy) hb hb' hs

/-- **The sine expansion of an odd Maass cusp newform** (LMFDB `mf.maass.mwf.coefficients`): an
odd Maass cusp newform `F` of weight `0` on `Γ₀(N)` with spectral parameter `R`, with `F` and
`∂F/∂y` of polynomial growth in `y` uniformly in `x`, has the sine expansion
`F(x + iy) = ∑_{n ≥ 1} a(n) √y K_{iR}(2πny) sin(2πnx)` with the coefficients
`a = maassCoefficients R F`. -/
lemma IsMaassCuspNewform.hasMaassSineExpansion_maassCoefficients (hF : IsMaassCuspNewform N R F)
    (hb : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ, ‖(F ∘ ofComplex) (t + y * Complex.I)‖ ≤ C * y ^ M)
    (hb' : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ,
      ‖fderiv ℝ (F ∘ ofComplex) (t + y * Complex.I) Complex.I‖ ≤ C * y ^ M)
    (hs : IsOddMaassForm (F ∘ ofComplex)) :
    HasMaassSineExpansion (F ∘ ofComplex) R (maassCoefficients R (F ∘ ofComplex)) :=
  hF.1.hasMaassSineExpansion_maassCoefficients (fun _ hy ↦ hF.integral_eq_zero hy) hb hb' hs

/-- **The coefficients of the normalised even Maass cusp newform are real** at the indices prime
to the level (LMFDB `mf.maass.mwf.coefficients`): for an even Maass cusp newform `F` on `Γ₀(N)`
with `F` and `∂F/∂y` of polynomial growth and coefficients `a = maassCoefficients R F` with
`a(1) ≠ 0` (which holds at level `1`), the coefficient `a(n) / a(1)` of the cusp newform
normalised by `a(1) = 1` is real for every `n` prime to `N`. -/
lemma IsMaassCuspNewform.conj_maassCoefficients_div_of_isEvenMaassForm
    (hF : IsMaassCuspNewform N R F)
    (hb : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ, ‖(F ∘ ofComplex) (t + y * Complex.I)‖ ≤ C * y ^ M)
    (hb' : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ,
      ‖fderiv ℝ (F ∘ ofComplex) (t + y * Complex.I) Complex.I‖ ≤ C * y ^ M)
    (hs : IsEvenMaassForm (F ∘ ofComplex)) (h1 : maassCoefficients R (F ∘ ofComplex) 1 ≠ 0) {n : ℕ+}
    (hn : (n : ℕ).Coprime N) :
    conj (maassCoefficients R (F ∘ ofComplex) n / maassCoefficients R (F ∘ ofComplex) 1) =
      maassCoefficients R (F ∘ ofComplex) n / maassCoefficients R (F ∘ ofComplex) 1 :=
  hF.1.conj_coeff_div_of_hasMaassCosineExpansion
    (hF.hasMaassCosineExpansion_maassCoefficients hb hb' hs) h1 hn

/-- **The coefficients of the normalised odd Maass cusp newform are real** at the indices prime
to the level (LMFDB `mf.maass.mwf.coefficients`): for an odd Maass cusp newform `F` on `Γ₀(N)`
with `F` and `∂F/∂y` of polynomial growth and coefficients `a = maassCoefficients R F` with
`a(1) ≠ 0` (which holds at level `1`), the coefficient `a(n) / a(1)` of the cusp newform
normalised by `a(1) = 1` is real for every `n` prime to `N`. -/
lemma IsMaassCuspNewform.conj_maassCoefficients_div_of_isOddMaassForm
    (hF : IsMaassCuspNewform N R F)
    (hb : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ, ‖(F ∘ ofComplex) (t + y * Complex.I)‖ ≤ C * y ^ M)
    (hb' : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ,
      ‖fderiv ℝ (F ∘ ofComplex) (t + y * Complex.I) Complex.I‖ ≤ C * y ^ M)
    (hs : IsOddMaassForm (F ∘ ofComplex)) (h1 : maassCoefficients R (F ∘ ofComplex) 1 ≠ 0) {n : ℕ+}
    (hn : (n : ℕ).Coprime N) :
    conj (maassCoefficients R (F ∘ ofComplex) n / maassCoefficients R (F ∘ ofComplex) 1) =
      maassCoefficients R (F ∘ ofComplex) n / maassCoefficients R (F ∘ ofComplex) 1 :=
  hF.1.conj_coeff_div_of_hasMaassSineExpansion
    (hF.hasMaassSineExpansion_maassCoefficients hb hb' hs) h1 hn

/-- **An even Maass cusp newform of level `1` has `a(1) ≠ 0`**: for an even Maass cusp newform `F`
on `SL(2, ℤ)` with `F` and `∂F/∂y` of polynomial growth, the first coefficient of
`a = maassCoefficients R F` does not vanish, so that the coefficients `a(n) / a(1)` of the
normalised cusp newform are real for every `n` (`conj_maassCoefficients_div_of_isEvenMaassForm`).
-/
lemma IsMaassCuspNewform.maassCoefficients_one_ne_zero_of_isEvenMaassForm
    (hF : IsMaassCuspNewform 1 R F)
    (hb : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ, ‖(F ∘ ofComplex) (t + y * Complex.I)‖ ≤ C * y ^ M)
    (hb' : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ,
      ‖fderiv ℝ (F ∘ ofComplex) (t + y * Complex.I) Complex.I‖ ≤ C * y ^ M)
    (hs : IsEvenMaassForm (F ∘ ofComplex)) : maassCoefficients R (F ∘ ofComplex) 1 ≠ 0 :=
  hF.1.coeff_one_ne_zero_of_hasMaassCosineExpansion
    (hF.hasMaassCosineExpansion_maassCoefficients hb hb' hs)

/-- **An odd Maass cusp newform of level `1` has `a(1) ≠ 0`**: for an odd Maass cusp newform `F`
on `SL(2, ℤ)` with `F` and `∂F/∂y` of polynomial growth, the first coefficient of
`a = maassCoefficients R F` does not vanish, so that the coefficients `a(n) / a(1)` of the
normalised cusp newform are real for every `n` (`conj_maassCoefficients_div_of_isOddMaassForm`).
-/
lemma IsMaassCuspNewform.maassCoefficients_one_ne_zero_of_isOddMaassForm
    (hF : IsMaassCuspNewform 1 R F)
    (hb : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ, ‖(F ∘ ofComplex) (t + y * Complex.I)‖ ≤ C * y ^ M)
    (hb' : ∀ᶠ y : ℝ in atTop, ∀ t : ℝ,
      ‖fderiv ℝ (F ∘ ofComplex) (t + y * Complex.I) Complex.I‖ ≤ C * y ^ M)
    (hs : IsOddMaassForm (F ∘ ofComplex)) : maassCoefficients R (F ∘ ofComplex) 1 ≠ 0 :=
  hF.1.coeff_one_ne_zero_of_hasMaassSineExpansion
    (hF.hasMaassSineExpansion_maassCoefficients hb hb' hs)

end UpperHalfPlane
