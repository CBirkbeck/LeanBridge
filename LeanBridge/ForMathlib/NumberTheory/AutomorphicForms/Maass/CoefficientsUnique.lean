import LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselKNonvanishing
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.NewformCoefficients

/-!
# The coefficients of a Maass form are unique, and real for real forms

The coefficients `a(n)` of a cosine expansion `f(x + iy) = ∑_{n ≥ 1} a(n) √y K_{iR}(2πny) cos(2πnx)`
or of a sine expansion `f(x + iy) = ∑_{n ≥ 1} a(n) √y K_{iR}(2πny) sin(2πnx)` of a function `f` on
the upper half-plane (LMFDB `mf.maass.mwf.coefficients`) are determined by `f`, with no hypothesis:
`K_{iR}` does not vanish identically on `(0, ∞)` (`Complex.exists_besselK_ne_zero`), and a sine
expansion of `f` gives the cosine expansion
`f(z + t) - f(z - t) = ∑ 2 sin(2πnt) a(n) √y K_{iR}(2πny) cos(2πnx)`, which converges absolutely at
`x = 0`, so that no absolute convergence of the sine expansion is needed. Hence the coefficients
`maassCoefficients R f` are those of any cosine or sine expansion of `f`. For a real spectral
parameter `R`, the coefficients are real exactly when `f` is real-valued on `ℍ`.

## Main results

* `UpperHalfPlane.HasMaassCosineExpansion.unique`: two cosine expansions of `f` have the same
  coefficients.
* `UpperHalfPlane.HasMaassSineExpansion.unique`: two sine expansions of `f` have the same
  coefficients.
* `UpperHalfPlane.HasMaassCosineExpansion.isEvenMaassForm`,
  `UpperHalfPlane.HasMaassSineExpansion.isOddMaassForm`: a function with a cosine (sine) expansion
  is even (odd).
* `UpperHalfPlane.HasMaassCosineExpansion.maassCoefficients_eq`,
  `UpperHalfPlane.HasMaassSineExpansion.maassCoefficients_eq`: the coefficients of a cosine or sine
  expansion of `f` are `maassCoefficients R f`.
* `UpperHalfPlane.HasMaassCosineExpansion.forall_conj_eq_iff`,
  `UpperHalfPlane.HasMaassSineExpansion.forall_conj_eq_iff`: for real `R`, the coefficients are
  real if and only if `f` is real on `ℍ`.
-/

open Real

open scoped ComplexConjugate

namespace UpperHalfPlane

variable {f : ℂ → ℂ} {r : ℂ} {R : ℝ} {c c' : ℕ+ → ℂ}

/-- **The coefficients of a cosine expansion are unique**: two cosine expansions
`f(x + iy) = ∑ c(n) √y K_{iR}(2πny) cos(2πnx)` of `f` with spectral parameter `R` have the same
coefficients. -/
lemma HasMaassCosineExpansion.unique (h : HasMaassCosineExpansion f r c)
    (h' : HasMaassCosineExpansion f r c') : c = c' := by
  rcases (Complex.I * r).exists_besselK_ne_zero with ⟨x, hx, hK⟩
  exact h.eq_of_besselK_ne_zero h' hx hK

lemma HasMaassSineExpansion.hasMaassCosineExpansion_sub (h : HasMaassSineExpansion f r c) (t : ℝ) :
    HasMaassCosineExpansion (fun w ↦ f (w + t) - f (w - t)) r
      fun n ↦ 2 * sin (2 * π * n * t) * c n := by
  intro z
  have hp : 0 < (z + t : ℂ).im := by
    simpa using z.im_pos
  have hm : 0 < (z - t : ℂ).im := by
    simpa using z.im_pos
  convert (h (mk _ hp)).sub (h (mk _ hm)) using 1
  funext n
  have hs : sin (2 * π * n * (z.re + t)) - sin (2 * π * n * (z.re - t)) =
      2 * sin (2 * π * n * t) * cos (2 * π * n * z.re) := by
    rw [mul_add, mul_sub, sin_add, sin_sub]
    ring1
  simp only [mk_re, mk_im, Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im, coe_re,
    coe_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, sub_zero]
  rw [← mul_sub, ← Complex.ofReal_sub, hs]
  push_cast
  ring1

/-- **The coefficients of a sine expansion are unique**: two sine expansions
`f(x + iy) = ∑ c(n) √y K_{iR}(2πny) sin(2πnx)` of `f` with spectral parameter `R` have the same
coefficients. The cosine expansions of `f(z + t) - f(z - t)` with the coefficients
`2 sin(2πnt) c(n)` agree, and `t = 1/(4n)` gives `c(n)`. -/
lemma HasMaassSineExpansion.unique (h : HasMaassSineExpansion f r c)
    (h' : HasMaassSineExpansion f r c') : c = c' := by
  funext n
  have hn : (n : ℝ) ≠ 0 := by
    positivity
  have he : 2 * π * n * (1 / (4 * n)) = π / 2 := by
    field_simp
    ring1
  have key : 2 * (sin (2 * π * n * (1 / (4 * n))) : ℂ) * c n =
      2 * (sin (2 * π * n * (1 / (4 * n))) : ℂ) * c' n :=
    congrFun ((h.hasMaassCosineExpansion_sub _).unique (h'.hasMaassCosineExpansion_sub _)) n
  rw [he, sin_pi_div_two, Complex.ofReal_one] at key
  linear_combination key / 2

/-- **A function with a cosine expansion is even** (LMFDB `mf.maass.mwf.symmetry`):
`f(-z̄) = f(z)` on `ℍ`, as `cos` is even. -/
lemma HasMaassCosineExpansion.isEvenMaassForm (h : HasMaassCosineExpansion f r c) :
    IsEvenMaassForm f := by
  intro z
  refine (h (maassReflection • z)).unique ?_
  convert h z using 2 with n
  rw [re_maassReflection_smul, im_maassReflection_smul, mul_neg, cos_neg]

/-- **A function with a sine expansion is odd** (LMFDB `mf.maass.mwf.symmetry`):
`f(-z̄) = -f(z)` on `ℍ`, as `sin` is odd. -/
lemma HasMaassSineExpansion.isOddMaassForm (h : HasMaassSineExpansion f r c) :
    IsOddMaassForm f := by
  intro z
  refine (h (maassReflection • z)).unique ?_
  convert (h z).neg using 2 with n
  rw [re_maassReflection_smul, im_maassReflection_smul, mul_neg, sin_neg]
  push_cast
  ring1

lemma HasMaassCosineExpansion.eq_zero_of_hasMaassSineExpansion (h : HasMaassCosineExpansion f r c)
    (h' : HasMaassSineExpansion f r c') (z : ℍ) : f z = 0 := by
  linear_combination (h'.isOddMaassForm z - h.isEvenMaassForm z) / 2

/-- **The coefficients of a cosine expansion are `maassCoefficients`**: if `f` has the cosine
expansion `f(x + iy) = ∑ c(n) √y K_{iR}(2πny) cos(2πnx)`, then `maassCoefficients R f = c`. -/
lemma HasMaassCosineExpansion.maassCoefficients_eq (h : HasMaassCosineExpansion f r c) :
    maassCoefficients r f = c := by
  rcases (Complex.I * r).exists_besselK_ne_zero with ⟨x, hx, hK⟩
  exact maassCoefficients_eq_of_hasMaassCosineExpansion h hx hK

/-- **The coefficients of a sine expansion are `maassCoefficients`**: if `f` has the sine expansion
`f(x + iy) = ∑ c(n) √y K_{iR}(2πny) sin(2πnx)`, then `maassCoefficients R f = c`. If `f` also has
a cosine expansion, it vanishes on `ℍ`, being even and odd, and both coefficients are `0`. -/
lemma HasMaassSineExpansion.maassCoefficients_eq (h : HasMaassSineExpansion f r c) :
    maassCoefficients r f = c := by
  by_cases hc : ∃ c', HasMaassCosineExpansion f r c'
  · rcases hc with ⟨c', h'⟩
    have h0 : HasMaassCosineExpansion f r 0 := fun z ↦ by
      simp [h'.eq_zero_of_hasMaassSineExpansion h z]
    have h0' : HasMaassSineExpansion f r 0 := fun z ↦ by
      simp [h'.eq_zero_of_hasMaassSineExpansion h z]
    rw [h'.maassCoefficients_eq, h'.unique h0, h.unique h0']
  · have hs : ∃ c', HasMaassSineExpansion f r c' := ⟨c, h⟩
    rw [maassCoefficients, dite_eq_right hc, dite_eq_left hs]
    exact hs.choose_spec.unique h

lemma HasMaassCosineExpansion.conj (h : HasMaassCosineExpansion f R c) :
    HasMaassCosineExpansion (fun w ↦ conj (f w)) R fun n ↦ conj (c n) := by
  intro z
  refine (Complex.hasSum_conj'.mpr (h z)).congr_fun fun n ↦ ?_
  rw [map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
    Complex.conj_besselK_I_mul]

lemma HasMaassSineExpansion.conj (h : HasMaassSineExpansion f R c) :
    HasMaassSineExpansion (fun w ↦ conj (f w)) R fun n ↦ conj (c n) := by
  intro z
  refine (Complex.hasSum_conj'.mpr (h z)).congr_fun fun n ↦ ?_
  rw [map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
    Complex.conj_besselK_I_mul]

/-- **The coefficients of a cosine expansion are real exactly when the function is**: for a real
spectral parameter `R` (for which `K_{iR}` is real), the coefficients of a cosine expansion of `f`
are real if and only if `f` is real on `ℍ`, the conjugate coefficients being those of the
conjugate function. -/
lemma HasMaassCosineExpansion.forall_conj_eq_iff (h : HasMaassCosineExpansion f R c) :
    (∀ n, conj (c n) = c n) ↔ ∀ z : ℍ, conj (f z) = f z := by
  refine ⟨fun hc z ↦ ?_, fun hf ↦ ?_⟩
  · have h' : HasSum (fun n : ℕ+ ↦ conj (c n) * √z.im *
        (Complex.I * R).besselK (2 * π * n * z.im) * cos (2 * π * n * z.re)) (conj (f z)) :=
      h.conj z
    simp only [hc] at h'
    exact h'.unique (h z)
  · have h' : HasMaassCosineExpansion f R fun n ↦ conj (c n) := fun z ↦ hf z ▸ h.conj z
    exact congrFun (h'.unique h)

/-- **The coefficients of a sine expansion are real exactly when the function is**: for a real
spectral parameter `R`, the coefficients of a sine expansion of `f` are real if and only if `f` is
real on `ℍ`. -/
lemma HasMaassSineExpansion.forall_conj_eq_iff (h : HasMaassSineExpansion f R c) :
    (∀ n, conj (c n) = c n) ↔ ∀ z : ℍ, conj (f z) = f z := by
  refine ⟨fun hc z ↦ ?_, fun hf ↦ ?_⟩
  · have h' : HasSum (fun n : ℕ+ ↦ conj (c n) * √z.im *
        (Complex.I * R).besselK (2 * π * n * z.im) * sin (2 * π * n * z.re)) (conj (f z)) :=
      h.conj z
    simp only [hc] at h'
    exact h'.unique (h z)
  · have h' : HasMaassSineExpansion f R fun n ↦ conj (c n) := fun z ↦ hf z ▸ h.conj z
    exact congrFun (h'.unique h)

end UpperHalfPlane
