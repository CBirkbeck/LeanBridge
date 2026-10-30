import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.Newform
import LeanBridge.ForMathlib.NumberTheory.LFunction.AnalyticRank
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The analytic rank of a Bianchi newform

The L-function of a Bianchi newform `F` of weight `2` over an imaginary quadratic field `K` of class
number `1` is `L(F, s) = ∑_𝔫 c(𝔫) N(𝔫)^{-s}`, the sum over the nonzero ideals `𝔫 = (α)` of `𝒪_K` of
the Fourier–Bessel coefficients `c(α)` of `F`, which are its Hecke eigenvalues `a_𝔫`. As an
L-function over `ℚ`, of degree `4`, its Dirichlet coefficients in the analytic normalisation, with
central point `s = 1 / 2`, are `aₙ = n^{-1/2} ∑_{N(𝔫) = n} c(𝔫)`. Its analytic continuation and
functional equation are theorems, not proved here; the **analytic rank** (LMFDB `mf.bianchi.anr`)
is the order of vanishing at the central point of any analytic L-function
(`AnalyticLFunction`) with these Dirichlet coefficients, which does not depend on the choice
(`IsAnalyticRank.eq`). That its parity is given by the sign (LMFDB `mf.bianchi.sign`) is a
theorem, not proved here.

## Main definitions

* `HyperbolicThreeSpace.BianchiNewform.lCoeff`: the Dirichlet coefficients of `L(F, s)`.
* `HyperbolicThreeSpace.BianchiNewform.IsAnalyticRank` (LMFDB `mf.bianchi.anr`): `F` has analytic
  rank `r`.

## Main results

* `HyperbolicThreeSpace.BianchiNewform.IsAnalyticRank.eq`: the analytic rank is unique.
-/

open NumberField

open Submodule (IsPrincipal)

namespace HyperbolicThreeSpace.BianchiNewform

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)]
  {σ : K →+* ℂ} {𝔑 : Ideal (𝓞 K)} [NeZero 𝔑] (F : BianchiNewform σ 𝔑)

/-- The Dirichlet coefficients `aₙ = n^{-1/2} ∑_{N(𝔫) = n} c(𝔫)` of the L-function of a Bianchi
newform `F` of weight `2` in the analytic normalisation, where `c(𝔫)` is the Fourier–Bessel
coefficient of `F` at a generator of `𝔫`, which does not depend on the generator since
`diag(u, 1) ∈ Γ₀(𝔑)` for the units `u` (not proved here). -/
noncomputable def lCoeff (n : ℕ) : ℂ :=
  ∑ᶠ 𝔫 ∈ {𝔫 : Ideal (𝓞 K) | Ideal.absNorm 𝔫 = n}, F.coeff (IsPrincipal.generator 𝔫) / (√n : ℂ)

/-- A Bianchi newform `F` of weight `2` has **analytic rank** `r` (LMFDB `mf.bianchi.anr`): `r` is
the order of vanishing at the centre `s = 1 / 2` of its critical strip of the analytic continuation
of its L-function, that is the analytic rank of an analytic L-function whose Dirichlet coefficients
are those of `F`. The analytic rank is unique (`IsAnalyticRank.eq`); that it exists, the analytic
continuation of `L(F, s)`, is a theorem, not proved here. -/
def IsAnalyticRank (r : ℕ) : Prop :=
  ∃ L : AnalyticLFunction, (∀ n ≠ 0, L.coeff n = F.lCoeff n) ∧ L.analyticRank = r

variable {F} {r r' : ℕ}

/-- **The analytic rank of a Bianchi newform is unique**: the analytic rank of an analytic
L-function only depends on its Dirichlet coefficients. -/
lemma IsAnalyticRank.eq (h : F.IsAnalyticRank r) (h' : F.IsAnalyticRank r') : r = r' := by
  rcases h with ⟨L, hL, rfl⟩
  rcases h' with ⟨L', hL', rfl⟩
  exact L.analyticRank_congr fun n hn ↦ (hL n hn).trans (hL' n hn).symm

end HyperbolicThreeSpace.BianchiNewform
