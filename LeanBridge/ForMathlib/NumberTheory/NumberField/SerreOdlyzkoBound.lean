import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The Serre–Odlyzko bound

Let `C_n` be the least root discriminant of a number field of degree `n`. Assuming the generalized
Riemann hypothesis, Odlyzko's analytic lower bounds for discriminants give `limsup C_n ≥ Ω`, for the
constant `Ω = 8 π e ^ γ` introduced by Serre. This file defines `Ω`; the conditional bound needs the
generalized Riemann hypothesis for Dedekind zeta functions, whose statement is not available, as
`NumberField.dedekindZeta` is not continued to the whole complex plane.

## Main definitions

* `NumberField.serreOdlyzkoBound` (LMFDB `nf.serre_odlyzko_bound`).
-/

open Real

namespace NumberField

/-- The **Serre–Odlyzko bound** (LMFDB `nf.serre_odlyzko_bound`): the constant
`Ω = 8 π e ^ γ ≈ 44.7632`, where `γ` is the Euler–Mascheroni constant. Under the generalized
Riemann hypothesis, the least root discriminant `C_n` of the number fields of degree `n` satisfies
`limsup C_n ≥ Ω`, so a number field whose root discriminant is below `Ω` has a small
discriminant. -/
noncomputable def serreOdlyzkoBound : ℝ :=
  8 * π * exp eulerMascheroniConstant

end NumberField
