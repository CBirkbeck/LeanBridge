import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.AnalyticRank
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.NewformOfWeight
import LeanBridge.ForMathlib.NumberTheory.LFunction.AnalyticRankParity

/-!
# The analytic rank of a Bianchi newform of any weight

Let `F` be a Bianchi newform of weight `k` (`BianchiNewformOfWeight`, in the convention of LMFDB
`mf.bianchi`, `F : ℋ₃ → ℂ^{k+1}`) over an imaginary quadratic field `K` of class number `1`. Its
coefficient system is `Sym^n ⊗ conj(Sym^n)`, `k = 2n + 2`, and its L-function is
`L(F, s) = ∑_𝔫 c(𝔫) N(𝔫)^{-s}`, the sum over the nonzero ideals `𝔫 = (α)` of `𝒪_K` of the
Fourier–Bessel coefficients `c(α)` of `F` (`HasBianchiWhittakerExpansion`), which are its Hecke
eigenvalues `a_𝔫` in the arithmetic normalisation; its good Euler factors are
`1 - a_𝔭 T + N(𝔭)^{k/2} T²`, of motivic weight `k / 2 = n + 1`. As an L-function over `ℚ`, of
degree `4`, its Dirichlet coefficients in the analytic normalisation, with central point
`s = 1 / 2`, are `aₙ = n^{-k/4} ∑_{N(𝔫) = n} c(𝔫)`, and in weight `2` these are the coefficients
`BianchiNewform.lCoeff` (`BianchiNewform.lCoeff_toBianchiNewformOfWeight`).

The **analytic rank** (LMFDB `mf.bianchi.anr`) is the order of vanishing at the central point of
any analytic L-function (`AnalyticLFunction`) with these Dirichlet coefficients, which does not
depend on the choice (`IsAnalyticRank.eq`). The analytic continuation and functional equation of
`L(F, s)`, which give such an L-function, are theorems not proved here. Its parity is given by the
sign `ε` of the functional equation, `ε = (-1)ʳ`, when the Dirichlet coefficients are real and the
gamma factor is real at the central point (`IsAnalyticRank.sign_eq_neg_one_pow`); that the
coefficients are real and that `ε` is the sign of `F` (LMFDB `mf.bianchi.sign`) are theorems not
proved here.

## Main definitions

* `HyperbolicThreeSpace.BianchiNewformOfWeight.lCoeff`: the Dirichlet coefficients of `L(F, s)`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.IsAnalyticRank` (LMFDB `mf.bianchi.anr`): `F` has
  analytic rank `r`.

## Main results

* `HyperbolicThreeSpace.BianchiNewformOfWeight.IsAnalyticRank.eq`: the analytic rank is unique.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.IsAnalyticRank.sign_eq_neg_one_pow`: the sign of
  the functional equation determines the parity of the analytic rank.
* `HyperbolicThreeSpace.BianchiNewform.lCoeff_toBianchiNewformOfWeight` and
  `HyperbolicThreeSpace.BianchiNewform.isAnalyticRank_toBianchiNewformOfWeight_iff`: in weight `2`,
  the Dirichlet coefficients and the analytic rank are those of `BianchiNewform`.
-/

open NumberField

open Submodule (IsPrincipal)

open scoped ComplexConjugate

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)]
  {σ : K →+* ℂ} {𝔑 : Ideal (𝓞 K)} [NeZero 𝔑]

namespace BianchiNewformOfWeight

variable {k : ℕ} (F : BianchiNewformOfWeight σ k 𝔑)

/-- The Dirichlet coefficients `aₙ = n^{-k/4} ∑_{N(𝔫) = n} c(𝔫)` of the L-function of a Bianchi
newform `F` of weight `k` in the analytic normalisation, where `c(𝔫)` is the Fourier–Bessel
coefficient of `F` at a generator of `𝔫`, its Hecke eigenvalue `a_𝔫` in the arithmetic
normalisation, and `k / 4` is half the motivic weight `k / 2`. The coefficient does not depend on
the generator since `diag(u, 1) ∈ Γ₀(𝔑)` for the units `u` (not proved here). -/
noncomputable def lCoeff (n : ℕ) : ℂ :=
  ∑ᶠ 𝔫 ∈ {𝔫 : Ideal (𝓞 K) | Ideal.absNorm 𝔫 = n},
    F.coeff (IsPrincipal.generator 𝔫) / ((n : ℝ) ^ ((k : ℝ) / 4) : ℝ)

/-- A Bianchi newform `F` of weight `k` has **analytic rank** `r` (LMFDB `mf.bianchi.anr`): `r` is
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

/-- **The sign of the functional equation determines the parity of the analytic rank** (LMFDB
`mf.bianchi.anr`): if `F` has analytic rank `r` and real Dirichlet coefficients, then every analytic
L-function `L` with the Dirichlet coefficients of `F` whose gamma factor is real at the central
point has sign `(-1)ʳ`. The coefficients are real as the Hecke eigenvalues are, and the gamma factor
of `L(F, s)` is `Γ_ℂ(s + k / 4)²`, theorems not proved here, as is the equality of the sign of `L`
with the sign of `F` (LMFDB `mf.bianchi.sign`). -/
lemma IsAnalyticRank.sign_eq_neg_one_pow (h : F.IsAnalyticRank r)
    (hF : ∀ n ≠ 0, conj (F.lCoeff n) = F.lCoeff n) {L : AnalyticLFunction}
    (hL : ∀ n ≠ 0, L.coeff n = F.lCoeff n)
    (hγ : conj (L.selbergData.gammaFactor (1 / 2)) = L.selbergData.gammaFactor (1 / 2)) :
    L.sign = (-1) ^ r := by
  rw [h.eq ⟨L, hL, rfl⟩]
  exact L.sign_eq_neg_one_pow_analyticRank (fun n hn ↦ (hL n hn).symm ▸ hF n hn) hγ

end BianchiNewformOfWeight

namespace BianchiNewform

variable (F : BianchiNewform σ 𝔑)

/-- **In weight `2`, the Dirichlet coefficients are those of `BianchiNewform.lCoeff`**, as
`n^{-2/4} = n^{-1/2}`. -/
lemma lCoeff_toBianchiNewformOfWeight : F.toBianchiNewformOfWeight.lCoeff = F.lCoeff := by
  ext n
  norm_num [BianchiNewformOfWeight.lCoeff, toBianchiNewformOfWeight, lCoeff, Real.sqrt_eq_rpow]

/-- **In weight `2`, the analytic rank is that of `BianchiNewform.IsAnalyticRank`.** -/
lemma isAnalyticRank_toBianchiNewformOfWeight_iff (r : ℕ) :
    F.toBianchiNewformOfWeight.IsAnalyticRank r ↔ F.IsAnalyticRank r := by
  rw [BianchiNewformOfWeight.IsAnalyticRank, lCoeff_toBianchiNewformOfWeight, IsAnalyticRank]

end BianchiNewform

end HyperbolicThreeSpace
