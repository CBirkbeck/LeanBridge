import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.HeckeFourier
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.Newform
import Mathlib.NumberTheory.LSeries.Basic

/-!
# The coefficients of a Maass newform

The LMFDB (`mf.maass.mwf.coefficients`) states that a Maass newform `f` of weight `0` on `Γ₀(N)`
(`UpperHalfPlane.IsMaassNewform` with the trivial character) with spectral parameter `R` has, if it
is even, a cosine expansion `f(x + iy) = ∑_{n ≥ 1} a(n) √y K_{iR}(2πny) cos(2πnx)` and, if it is
odd, a sine expansion `f(x + iy) = ∑_{n ≥ 1} a(n) √y K_{iR}(2πny) sin(2πnx)`; the `a(n)` are its
coefficients, real numbers, and define its `L`-function `L(f, s) = ∑ a(n) n^{-s}`.

The coefficients are defined here from the expansion, when there is one, and they are unique:
two cosine expansions of `f`, or two absolutely convergent sine expansions, have the same
coefficients, as soon as the `K`-Bessel function `K_{iR}` does not vanish identically on
`(0, ∞)`. They do not depend on the sign of `R`.

Proved elsewhere: the non-vanishing of `K_{iR}` somewhere on `(0, ∞)`
(`Complex.exists_besselK_ne_zero` in
`LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselKNonvanishing`), which with
`HasMaassCosineExpansion.unique` and `HasMaassSineExpansion.unique` (in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CoefficientsUnique`) makes the
coefficients of every expansion unique, sine expansions included without absolute convergence; the
existence of the expansions for every even or odd newform with vanishing constant term at `∞`, such
as a cusp newform of level `N ≠ 0` (`IsMaassNewform.hasMaassCosineExpansion_of_integral_eq_zero`,
`IsMaassCuspNewform.hasMaassCosineExpansion` and their sine analogues in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CuspNewformExpansion`) or a newform with
real `R` (`IsMaassNewform.hasMaassCosineExpansion_ofReal` and its sine analogue in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.ConstantTerm`); and, for a newform with
such an expansion at a level `N ≠ 0`, that `a(1) ≠ 0` and that the coefficient `a(n) / a(1)` of the
newform normalised by `a(1) = 1` is real for every `n`, `gcd(n, N) > 1` included
(`IsMaassNewform.coeff_one_ne_zero_of_cosine`, `IsMaassNewform.conj_coeff_div_of_cosine` and their
sine analogues in `LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.NewformAtkinLehner`,
from the Main Lemma of Atkin and Lehner and the self-adjointness of the Hecke operators in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.HeckeSelfAdjoint`). Not proved: that a
newform whose constant term at `∞` does not vanish is a constant of level `1`, which is classical
(the residual spectrum of `Γ₀(N)` consists of the constants). `IsMaassNewform` asks only for
square-integrability, and the constant `1` of level `1` satisfies it without having an expansion
(`not_hasMaassCosineExpansion_const_one`).

## Main definitions

* `UpperHalfPlane.maassCoefficients` (LMFDB `mf.maass.mwf.coefficients`): the coefficients `a(n)`.
* `UpperHalfPlane.maassLFunction` (LMFDB `mf.maass.mwf.coefficients`): the `L`-function
  `∑ a(n) n^{-s}`.

## Main results

* `UpperHalfPlane.HasMaassCosineExpansion.eq_of_besselK_ne_zero`,
  `UpperHalfPlane.HasMaassSineExpansion.eq_of_besselK_ne_zero`: uniqueness of the coefficients.
* `UpperHalfPlane.maassCoefficients_eq_of_hasMaassCosineExpansion`,
  `UpperHalfPlane.maassCoefficients_eq_of_hasMaassSineExpansion`: the coefficients of an expansion
  are `maassCoefficients`.
* `UpperHalfPlane.maassCoefficients_neg`: the coefficients do not depend on the sign of `R`.
-/

open Real

namespace UpperHalfPlane

variable (r : ℂ) (f : ℂ → ℂ) {c c' : ℕ+ → ℂ} {x : ℝ} (z : ℍ)

open scoped Classical in
/-- The **coefficients** `a(n)`, `n ≥ 1` (LMFDB `mf.maass.mwf.coefficients`), of a function `f` on
the upper half-plane, given on `ℂ`, with spectral parameter `R`: those of its cosine expansion
`f(x + iy) = ∑ a(n) √y K_{iR}(2πny) cos(2πnx)` (`HasMaassCosineExpansion`) if it has one, as an even
Maass cusp newform does, and otherwise those of its sine expansion
`f(x + iy) = ∑ a(n) √y K_{iR}(2πny) sin(2πnx)` (`HasMaassSineExpansion`) if it has one, as an odd
Maass cusp newform does; `0` if it has neither. A nonzero function cannot have both, being then even
and odd in `x`. The coefficients of an expansion are unique
(`maassCoefficients_eq_of_hasMaassCosineExpansion`, `maassCoefficients_eq_of_hasMaassSineExpansion`)
provided `K_{iR}` does not vanish identically on `(0, ∞)`, and do not depend on the sign of `R`
(`maassCoefficients_neg`). For a Maass newform `f` of weight `0` on `Γ₀(N)`, `N ≠ 0`, with
eigenvalue `1/4 + R²` (`IsMaassNewform`), the LMFDB's coefficients are those of the newform
normalised by `a(1) = 1` (`maassNormalisedNewform`), which are real. The expansion exists if `f` is
an even or odd cusp newform (`IsMaassCuspNewform.hasMaassCosineExpansion`,
`IsMaassCuspNewform.hasMaassSineExpansion`) or an even or odd newform with real `R`
(`IsMaassNewform.hasMaassCosineExpansion_ofReal`, `IsMaassNewform.hasMaassSineExpansion_ofReal`);
given an expansion, `a(1) ≠ 0` and `a(n) / a(1)` is real for every `n`
(`IsMaassNewform.coeff_one_ne_zero_of_cosine`, `IsMaassNewform.conj_coeff_div_of_cosine` and the
sine versions). The constant `1` of level `1` is a newform with no expansion
(`not_hasMaassCosineExpansion_const_one`, `not_hasMaassSineExpansion_const_one`). -/
noncomputable def maassCoefficients : ℕ+ → ℂ :=
  if h : ∃ c, HasMaassCosineExpansion f r c then h.choose
  else if h' : ∃ c, HasMaassSineExpansion f r c then h'.choose else 0

/-- The **`L`-function** `L(f, s) = ∑_{n ≥ 1} a(n) n^{-s}` (LMFDB `mf.maass.mwf.coefficients`) of a
function `f` on the upper half-plane with spectral parameter `R`, from its coefficients
`maassCoefficients`, as Mathlib's `L`-series (the sum where it converges absolutely, `0`
elsewhere). -/
noncomputable def maassLFunction (s : ℂ) : ℂ :=
  LSeries (fun n ↦ maassCoefficients r f n.toPNat') s

variable {r f}

lemma two_pi_mul_div (n : ℕ+) (hx : 0 < x) :
    2 * π * ((|((n : ℕ) : ℤ)| : ℤ) : ℝ) * (x / (2 * π * n)) = x := by
  have hn : (0 : ℝ) < n := by positivity
  rw [Nat.abs_cast, Int.cast_natCast]
  field_simp

lemma re_maassReflection_smul : (maassReflection • z).re = -z.re := by
  rw [← coe_re, coe_maassReflection_smul, Complex.neg_re, Complex.conj_re, coe_re]

lemma im_maassReflection_smul : (maassReflection • z).im = z.im := by
  rw [← coe_im, coe_maassReflection_smul, Complex.neg_im, Complex.conj_im, neg_neg, coe_im]

/-- **The coefficients of a cosine expansion are unique**: two cosine expansions of `f` with
spectral parameter `R` have the same coefficients if `K_{iR}(x) ≠ 0` for some `x > 0`. -/
lemma HasMaassCosineExpansion.eq_of_besselK_ne_zero (h : HasMaassCosineExpansion f r c)
    (h' : HasMaassCosineExpansion f r c') (hx : 0 < x) (hK : (Complex.I * r).besselK x ≠ 0) :
    c = c' := by
  funext n
  have hn : (0 : ℤ) < n := by positivity
  have key : c n / 2 * (Complex.I * r).besselK x = c' n / 2 * (Complex.I * r).besselK x := by
    simpa only [two_pi_mul_div n hx, hn, ite_true, Int.toNat_natCast, PNat.coe_toPNat'] using
      h.hasMaassFourierExpansion.mul_besselK_eq h'.hasMaassFourierExpansion n
        (div_pos hx <| by positivity : 0 < x / (2 * π * n))
  linear_combination 2 * mul_right_cancel₀ hK key

/-- **The coefficients of an absolutely convergent sine expansion are unique**: two absolutely
convergent sine expansions of `f` with spectral parameter `R` have the same coefficients if
`K_{iR}(x) ≠ 0` for some `x > 0`. -/
lemma HasMaassSineExpansion.eq_of_besselK_ne_zero (h : HasMaassSineExpansion f r c)
    (hs : ∀ z : ℍ, Summable fun k : ℕ+ ↦ ‖c k * √z.im * (Complex.I * r).besselK (2 * π * k * z.im)‖)
    (h' : HasMaassSineExpansion f r c')
    (hs' : ∀ z : ℍ,
      Summable fun k : ℕ+ ↦ ‖c' k * √z.im * (Complex.I * r).besselK (2 * π * k * z.im)‖)
    (hx : 0 < x) (hK : (Complex.I * r).besselK x ≠ 0) : c = c' := by
  funext n
  have hn : (0 : ℤ) < n := by positivity
  have key : c n / (2 * Complex.I) * (Complex.I * r).besselK x =
      c' n / (2 * Complex.I) * (Complex.I * r).besselK x := by
    simpa only [two_pi_mul_div n hx, hn, ite_true, Int.toNat_natCast, PNat.coe_toPNat'] using
      (h.hasMaassFourierExpansion hs).mul_besselK_eq (h'.hasMaassFourierExpansion hs') n
        (div_pos hx <| by positivity : 0 < x / (2 * π * n))
  exact (div_left_inj' <| by simp).mp <| mul_right_cancel₀ hK key

/-- **The coefficients of a cosine expansion are `maassCoefficients`**, provided `K_{iR}(x) ≠ 0`
for some `x > 0`. -/
lemma maassCoefficients_eq_of_hasMaassCosineExpansion (h : HasMaassCosineExpansion f r c)
    (hx : 0 < x) (hK : (Complex.I * r).besselK x ≠ 0) : maassCoefficients r f = c := by
  have hc : ∃ c, HasMaassCosineExpansion f r c := ⟨c, h⟩
  rw [maassCoefficients, dite_eq_left hc]
  exact hc.choose_spec.eq_of_besselK_ne_zero h hx hK

/-- **The coefficients of an absolutely convergent sine expansion are `maassCoefficients`**, for a
function `f` that does not vanish identically on `ℍ` (so that it has no cosine expansion) and whose
sine expansions all converge absolutely, provided `K_{iR}(x) ≠ 0` for some `x > 0`. -/
lemma maassCoefficients_eq_of_hasMaassSineExpansion (h : HasMaassSineExpansion f r c)
    (hs : ∀ c', HasMaassSineExpansion f r c' → ∀ z : ℍ,
      Summable fun k : ℕ+ ↦ ‖c' k * √z.im * (Complex.I * r).besselK (2 * π * k * z.im)‖)
    (hf : ∃ z : ℍ, f z ≠ 0) (hx : 0 < x) (hK : (Complex.I * r).besselK x ≠ 0) :
    maassCoefficients r f = c := by
  have hc : ¬∃ c, HasMaassCosineExpansion f r c := by
    rintro ⟨c', h'⟩
    rcases hf with ⟨z, hz⟩
    have h1 : f ↑(maassReflection • z) = f z := by
      refine (h' (maassReflection • z)).unique ?_
      convert h' z using 2 with n
      rw [re_maassReflection_smul, im_maassReflection_smul, mul_neg, Real.cos_neg]
    have h2 : f ↑(maassReflection • z) = -f z := by
      refine (h (maassReflection • z)).unique ?_
      convert (h z).neg using 2 with n
      rw [re_maassReflection_smul, im_maassReflection_smul, mul_neg, Real.sin_neg]
      push_cast
      ring1
    exact hz <| by linear_combination (h2 - h1) / 2
  have hc' : ∃ c, HasMaassSineExpansion f r c := ⟨c, h⟩
  rw [maassCoefficients, dite_eq_right hc, dite_eq_left hc']
  exact hc'.choose_spec.eq_of_besselK_ne_zero (hs _ hc'.choose_spec) h (hs c h) hx hK

/-- **The coefficients do not depend on the sign of the spectral parameter**, since
`K_{-ν} = K_ν`. -/
lemma maassCoefficients_neg : maassCoefficients (-r) f = maassCoefficients r f := by
  have hK (x : ℝ) : (Complex.I * -r).besselK x = (Complex.I * r).besselK x := by
    rw [mul_neg, Complex.besselK_neg]
  have hcos : HasMaassCosineExpansion f (-r) = HasMaassCosineExpansion f r := by
    funext c
    simp only [HasMaassCosineExpansion, hK]
  have hsin : HasMaassSineExpansion f (-r) = HasMaassSineExpansion f r := by
    funext c
    simp only [HasMaassSineExpansion, hK]
  rw [maassCoefficients, maassCoefficients, hcos, hsin]

end UpperHalfPlane
