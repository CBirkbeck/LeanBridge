import LeanBridge.ForMathlib.NumberTheory.LFunction.RiemannHypothesis
import LeanBridge.ForMathlib.NumberTheory.NumberField.SerreOdlyzkoBound
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# The Serre–Odlyzko inequality

Let `C_n` be the least root discriminant of a number field of degree `n`. Assuming the generalized
Riemann hypothesis, `limsup C_n ≥ Ω = 8 π e ^ γ`, the Serre–Odlyzko bound. This file defines `C_n`
and states this inequality, which is not proved.

## Main definitions

* `NumberField.minRootDiscr` (LMFDB `nf.serre_odlyzko_bound`): the least root discriminant `C_n`.
* `NumberField.SerreOdlyzkoInequality` (LMFDB `nf.serre_odlyzko_bound`): the statement
  `GRH → limsup C_n ≥ Ω`.
-/

open Filter Module

namespace NumberField

/-- The **least root discriminant** `C_n` (LMFDB `nf.serre_odlyzko_bound`) of the number fields of
degree `n`: the infimum of the root discriminants (LMFDB `nf.root_discriminant`) of the subfields of
`ℚ̄` of degree `n` over `ℚ`. Every number field of degree `n` is isomorphic to such a subfield, and
there are finitely many number fields of bounded discriminant, so the infimum is a minimum. -/
noncomputable def minRootDiscr (n : ℕ) : ℝ :=
  sInf {r | ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField K),
    finrank ℚ K = n ∧ rootDiscr K = r}

/-- The **Serre–Odlyzko inequality** (LMFDB `nf.serre_odlyzko_bound`), as a statement: assuming the
generalized Riemann hypothesis (LMFDB `lfunction.rh`), the least root discriminants `C_n` of the
number fields of degree `n` satisfy `limsup C_n ≥ Ω`, where `Ω = 8 π e ^ γ` is the Serre–Odlyzko
bound `NumberField.serreOdlyzkoBound`. The upper limit is taken in `EReal`, so that it makes sense
without knowing that `C_n` is bounded. -/
def SerreOdlyzkoInequality : Prop :=
  GeneralizedRiemannHypothesis →
    (serreOdlyzkoBound : EReal) ≤ limsup (fun n ↦ (minRootDiscr n : EReal)) atTop

end NumberField
