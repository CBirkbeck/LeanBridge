import LeanBridge.ForMathlib.NumberTheory.NumberField.ClassNumberFormula
import Mathlib.Analysis.Meromorphic.Order

/-!
# The analytic class number formula on the whole complex plane

The LMFDB's analytic class number formula asserts that the Dedekind zeta function `ζ_K` of a
number field `K` continues meromorphically to the whole complex plane with a single pole, of order
`1`, at `s = 1`, and that its residue there is `2 ^ r₁ (2π) ^ r₂ R h / (w √|D|)`. The continuation
to `ℂ` is Hecke's theorem, which is not available; this file states the full assertion. The residue
formula for the continuation near `s = 1` is proved in
`NumberField.exists_tendsto_sub_one_mul_dedekindZeta`.

## Main definitions

* `NumberField.ClassNumberFormula` (LMFDB `nf.class_number_formula`).
-/

open Filter Topology

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The **analytic class number formula** (LMFDB `nf.class_number_formula`) for a number field `K`,
as a statement: the Dedekind zeta function `ζ_K(s)`, defined by its Dirichlet series for `re s > 1`,
continues to a function `F` holomorphic on `ℂ` minus `{1}` with a pole of order `1` at `s = 1`, and
`lim_{s → 1} (s - 1) F(s) = 2 ^ r₁ (2π) ^ r₂ R h / (w √|D|)` (`dedekindZeta_residue_def`). That
`F` is meromorphic on `ℂ` with no pole other than `s = 1` is the holomorphy on `{1}ᶜ`. -/
def ClassNumberFormula : Prop :=
  ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {1}ᶜ ∧ (∀ s : ℂ, 1 < s.re → F s = dedekindZeta K s) ∧
    meromorphicOrderAt F 1 = -1 ∧
    Tendsto (fun s ↦ (s - 1) * F s) (𝓝[≠] 1) (𝓝 (dedekindZeta_residue K))

end NumberField
