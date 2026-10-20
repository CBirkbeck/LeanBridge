import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import TauCeti.NumberTheory.ModularForms.Newforms.AnalyticInvariants

/-!
# The analytic conductor of a classical newform

The LMFDB attaches to a newform `f ∈ S_k^new(N, χ)` the positive real number
`N (exp (ψ (k / 2)) / (2π))²`, where `ψ = Γ' / Γ` is the digamma function. It depends on `f` only
through its level and weight. Mathlib's digamma function `Complex.digamma` is complex-valued, so
the definition takes the real part of `ψ (k / 2)`; `Complex.digamma_ofReal_im` shows that nothing
is lost.

## Main definitions

* `HeckeRing.GL2.Newform.analyticConductorLMFDB` (LMFDB `cmf.analytic_conductor`).

## Main results

* `Complex.digamma_ofReal_im`: the digamma function is real on the real line.
* `HeckeRing.GL2.Newform.ofReal_analyticConductorLMFDB`: the analytic conductor is the complex
  number `N (exp (ψ (k / 2)) / (2π))²`.
* `HeckeRing.GL2.Newform.analyticConductorLMFDB_pos`: it is positive.
* `HeckeRing.GL2.Newform.analyticConductorLMFDB_two_mul_add_two`: its value
  `N (exp (H_n - γ) / (2π))²` in even weight `2n + 2`, where `H_n` is the `n`-th harmonic number
  and `γ` the Euler–Mascheroni constant.
-/

open scoped ComplexConjugate Real

namespace Complex

lemma digamma_conj (s : ℂ) : digamma (conj s) = conj (digamma s) := by
  have hd : deriv Gamma (conj s) = conj (deriv Gamma s) := by
    simpa [Function.comp_def, Gamma_conj] using congrFun (deriv_conj_conj (f := Gamma)) (conj s)
  rw [digamma_def, logDeriv_apply, logDeriv_apply, hd, Gamma_conj, map_div₀]

/-- The digamma function is real on the real line. -/
lemma digamma_ofReal_im (x : ℝ) : (digamma x).im = 0 :=
  conj_eq_iff_im.mp <| by rw [← digamma_conj, conj_ofReal]

end Complex

namespace HeckeRing.GL2.Newform

variable (N : ℕ) (k : ℤ)

/-- The **analytic conductor** (LMFDB `cmf.analytic_conductor`) of a newform of level `N` and
weight `k`: the positive real number `N (exp (ψ (k / 2)) / (2π))²`, where `ψ = Γ' / Γ` is the
digamma function. It depends on the newform only through `N` and `k`, which are therefore its only
arguments.

Mathlib's digamma function is complex-valued, so the definition uses the real part of
`ψ (k / 2)`, which is `ψ (k / 2)` itself (`ofReal_analyticConductorLMFDB`). This is the LMFDB's
normalisation, not the Iwaniec–Kowalski conductor `N (|k / 2| + 3) (|k / 2 + 1| + 3)` of Tau Ceti's
`HeckeRing.GL2.Newform.analyticConductor`. -/
noncomputable def analyticConductorLMFDB : ℝ :=
  N * (Real.exp (Complex.digamma (k / 2)).re / (2 * π)) ^ 2

variable {N k}

/-- The analytic conductor is the complex number `N (exp (ψ (k / 2)) / (2π))²`. -/
lemma ofReal_analyticConductorLMFDB : (analyticConductorLMFDB N k : ℂ) = N *
    (Complex.exp (Complex.digamma (k / 2)) / (2 * π)) ^ 2 := by
  have hψ : ((Complex.digamma (k / 2)).re : ℂ) = Complex.digamma (k / 2) :=
    Complex.conj_eq_iff_re.mp <| by rw [← Complex.digamma_conj, map_div₀, map_intCast, map_ofNat]
  rw [analyticConductorLMFDB]
  push_cast
  rw [hψ]

/-- The analytic conductor of a newform is positive. -/
lemma analyticConductorLMFDB_pos [NeZero N] : 0 < analyticConductorLMFDB N k := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  unfold analyticConductorLMFDB
  positivity

/-- In even weight `2n + 2` the analytic conductor is `N (exp (H_n - γ) / (2π))²`, where `H_n` is
the `n`-th harmonic number and `γ` the Euler–Mascheroni constant. -/
lemma analyticConductorLMFDB_two_mul_add_two (n : ℕ) : analyticConductorLMFDB N (2 * n + 2) = N *
    (Real.exp (harmonic n - Real.eulerMascheroniConstant) / (2 * π)) ^ 2 := by
  have hk : ((2 * n + 2 : ℤ) : ℂ) / 2 = n + 1 := by
    push_cast
    ring1
  rw [analyticConductorLMFDB, hk, Complex.digamma_nat_add_one]
  norm_cast

end HeckeRing.GL2.Newform
