import TauCeti.NumberTheory.LocalField.Discriminant.Basic
import TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.Five.Basic

/-!
# The unramified quadratic extension `ℚ₂(√5)`

This file certifies the unramified test case of LeanBridge issue #63, on the ramification index
`e`, the residue degree `f` and the discriminant exponent `d` of a finite extension of `p`-adic
fields: an unramified extension of `ℚ_p` of degree `n` has `e = 1`, `f = n` and `d = 0`. The
extension is Tau Ceti's `TauCeti.DyadicSqrtFive`, the field `ℚ₂(√5)`, which is unramified over
`ℚ₂` (the instance `IsUnramified ℚ_[2] DyadicSqrtFive`) of degree `n = 2`
(`TauCeti.DyadicSqrtFive.finrank_eq_two`), and the invariants are Tau Ceti's
`TauCeti.ramificationIndex`, `TauCeti.inertiaDegree` and `TauCeti.discriminantExponent`. The
residue degree is `f = 2` (`TauCeti.DyadicSqrtFive.inertiaDegree_eq_two`).

## Main results

* `LeanBridge.DyadicSqrtFive.ramificationIndex_eq_one`: `e = 1`.
* `LeanBridge.DyadicSqrtFive.inertiaDegree_eq_finrank`: `f = n`.
* `LeanBridge.DyadicSqrtFive.discriminantExponent_eq_zero`: `d = 0`.
-/

open TauCeti

namespace LeanBridge.DyadicSqrtFive

/-- **`ℚ₂(√5)` has ramification index `e = 1`** over `ℚ₂`. -/
lemma ramificationIndex_eq_one : ramificationIndex ℚ_[2] DyadicSqrtFive = 1 :=
  IsUnramified.ramificationIndex_eq_one

/-- **`ℚ₂(√5)` has residue degree `f = n`** over `ℚ₂`, where `n = 2` is its degree. -/
lemma inertiaDegree_eq_finrank :
    inertiaDegree ℚ_[2] DyadicSqrtFive = Module.finrank ℚ_[2] DyadicSqrtFive :=
  IsUnramified.inertiaDegree_eq_finrank

/-- **`ℚ₂(√5)` has discriminant exponent `d = 0`** over `ℚ₂`. -/
lemma discriminantExponent_eq_zero : discriminantExponent ℚ_[2] DyadicSqrtFive = 0 :=
  (discriminantExponent_eq_zero_iff _ _).2 inferInstance

end LeanBridge.DyadicSqrtFive
