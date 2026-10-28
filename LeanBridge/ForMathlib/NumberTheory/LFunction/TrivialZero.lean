import LeanBridge.ForMathlib.NumberTheory.LFunction.RiemannHypothesis

/-!
# Trivial zeros of an analytic L-function

The gamma factor `∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ)` of an analytic L-function has its poles at the
points `s = -μⱼ - 2n` (poles of `Γ_ℝ(s + μⱼ) = π ^ (-(s + μⱼ) / 2) Γ((s + μⱼ) / 2)`) and
`s = -νₖ - n` (poles of `Γ_ℂ(s + νₖ) = 2 (2π) ^ (-(s + νₖ)) Γ(s + νₖ)`), for `n ∈ ℕ`. The zeros of
the L-function at these points are its trivial zeros.

## Main definitions

* `AnalyticLFunction.SelbergData.gammaPoles`: the poles of the gamma factors of a functional
  equation.
* `AnalyticLFunction.trivialZeros` (LMFDB `lfunction.trivial_zero`).
-/

namespace AnalyticLFunction

/-- The **poles of the gamma factors** (LMFDB `lfunction.gamma_factor`) `Γ_ℝ(s + μⱼ)` and
`Γ_ℂ(s + νₖ)` of a functional equation: the points `-μⱼ - 2n` and `-νₖ - n` for `n ∈ ℕ`, the poles
of `Γ((s + μⱼ) / 2)` and `Γ(s + νₖ)`. Since `Γ` has no zeros, these are also the poles of the
product `AnalyticLFunction.SelbergData.gammaFactor`. -/
def SelbergData.gammaPoles (D : SelbergData) : Set ℂ :=
  {s | ∃ μ ∈ D.μ, ∃ n : ℕ, s = -μ - 2 * n} ∪ {s | ∃ ν ∈ D.ν, ∃ n : ℕ, s = -ν - n}

variable (L : AnalyticLFunction)

/-- The **trivial zeros** (LMFDB `lfunction.trivial_zero`) of an analytic L-function: its zeros
(LMFDB `lfunction.zeros`) that occur at poles of its gamma factors (LMFDB `lfunction.gamma_factor`).
-/
noncomputable def trivialZeros : Set ℂ :=
  L.zeros ∩ L.selbergData.gammaPoles

lemma trivialZeros_subset_zeros : L.trivialZeros ⊆ L.zeros :=
  Set.inter_subset_left

end AnalyticLFunction
