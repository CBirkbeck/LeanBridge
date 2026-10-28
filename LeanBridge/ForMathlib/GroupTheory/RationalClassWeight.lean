import Mathlib.Algebra.Group.Conj
import Mathlib.Basic.NNReal.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Weight functions on a finite group

## Main definitions

* `Group.IsWeightFunction` (LMFDB `group.weight_function`): a function `G → ℝ≥0` vanishing exactly
  at the identity and invariant under conjugation and under invertible powering.

## Main results

* `Group.IsWeightFunction.apply_conj_pow`: a weight function is constant on rational conjugacy
  classes.
-/

open scoped NNReal

namespace Group

variable {G : Type*} [Group G]

/-- A function `w : G → ℝ≥0` on a finite group `G` is a **weight function** (LMFDB
`group.weight_function`) if `w g = 0` exactly when `g = 1`, `w` is invariant under conjugation, and
`w (g ^ n) = w g` whenever `n` is coprime to `#G`.

The knowl states the last condition for `n ∤ #G`, which is not invariance under invertible powering
as it says (it would force `w (g ^ 4) = w g` in a group of order `6`); we use the intended condition
that `n` is coprime to `#G`, under which `g ↦ g ^ n` is a bijection. -/
structure IsWeightFunction (w : G → ℝ≥0) : Prop where
  eq_zero_iff (g : G) : w g = 0 ↔ g = 1
  apply_conj (g h : G) : w (h * g * h⁻¹) = w g
  apply_pow (g : G) {n : ℕ} : n.Coprime (Nat.card G) → w (g ^ n) = w g

/-- **A weight function is constant on rational conjugacy classes**: `w` takes the same value at
`g` and at every conjugate of every power `g ^ n` with `n` coprime to `#G`. -/
lemma IsWeightFunction.apply_conj_pow {w : G → ℝ≥0} (hw : IsWeightFunction w) (g h : G) {n : ℕ}
    (hn : n.Coprime (Nat.card G)) : w (h * g ^ n * h⁻¹) = w g :=
  (hw.apply_conj _ h).trans <| hw.apply_pow g hn

end Group
