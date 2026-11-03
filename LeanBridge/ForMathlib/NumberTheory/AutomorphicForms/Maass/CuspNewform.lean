import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.Newform

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
theorems of the cosine and sine expansions
(`UpperHalfPlane.IsMaassCuspNewform.hasMaassCosineExpansion` and the sine version, in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CuspNewformExpansion`). At every level
`N ≠ 0`, for an even or odd cusp newform and `a = maassCoefficients R F`, `a(1) ≠ 0` and
`a(n) / a(1)` is real for every `n`, `gcd(n, N) > 1` included
(`UpperHalfPlane.IsMaassCuspNewform.maassCoefficients_one_ne_zero_of_even`,
`UpperHalfPlane.IsMaassCuspNewform.conj_maassCoefficients_div_of_even` and the odd versions, in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.NewformAtkinLehner`).

## Main definitions

* `UpperHalfPlane.IsMaassCuspNewform` (LMFDB `mf.maass.mwf.coefficients`): Maass cusp newforms of
  weight `0` on `Γ₀(N)` with trivial character.

## Main results

* `UpperHalfPlane.not_isMaassCuspNewform_const_one`: the constant `1` is not a cusp newform.
* `UpperHalfPlane.IsMaassCuspNewform.integral_eq_zero`: the constant term at `∞` vanishes.
-/

open scoped MatrixGroups

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

variable {N R F} [NeZero N]

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
      comp_add_one_of_mem_maassSpace hF.1.1.1 (by simpa using hy)
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

end UpperHalfPlane
