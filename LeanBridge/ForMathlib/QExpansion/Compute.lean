import LeanBridge.ForMathlib.QExpansion.Generic
import LeanBridge.ForMathlib.QExpansion.IntEval

/-!
# `#qexp` command and `qexp_coeff` tactic

User-facing tooling for computing and certifying q-expansion coefficients of level-1 modular forms
expressed as polynomials in `E₄, E₆`.

* `#qexp P precision N` — print the first `N` q-coefficients of the polynomial `P : List (ℕ × ℕ × ℚ)`
  (a list of monomials `(a, b, c)` meaning `c · E₄^a · E₆^b`), e.g. `#qexp [(37, 0, 1)] precision 5`.
* `#qexp P coeff n` — print just the `n`-th coefficient.
* `qexp_coeff P N` — close a goal `(coeff n) (qExpansion 1 (f : ℍ → ℂ)) = v` where `f` is a sum of
  `(c : ℂ) • mkMonomForm a b k _` matching `P`; auto-derives the `evalEisPS` bridge and discharges
  the coefficient by `decide +kernel`.
-/

namespace LeanBridge.QExpansion

open Lean Elab Command Meta ModularForm EisensteinSeries PowerSeries UpperHalfPlane
open scoped MatrixGroups

/-! ## `#qexp` query command -/

/-- `#qexp P precision N` prints the first `N` rational q-coefficients of the `E₄/E₆` polynomial
`P : List (ℕ × ℕ × ℚ)`. `#qexp P coeff n` prints just the `n`-th coefficient. -/
syntax (name := qexpListCmd) "#qexp " term:max " precision " num : command
syntax (name := qexpCoeffCmd) "#qexp " term:max " coeff " num : command

macro_rules
  | `(command| #qexp $P:term precision $N:num) =>
    `(command| #eval (evalEisList $P $N))
  | `(command| #qexp $P:term coeff $n:num) =>
    `(command| #eval (evalEisList $P ($n + 1)).getD $n 0)

/-! ## `qexp_bridge` and `qexp_coeff` tactics -/

/-- Prove a goal `qExpansion 1 (↑f) = evalEisPS P` where `f` is a sum of `(c : ℂ) • mkMonomForm …`
matching `P`. The two `simp only` passes (reduce the `qExpansion` side, then unfold the `evalEisPS`
side) handle any number of monomials uniformly, mirroring the certified generator proof. -/
macro "qexp_bridge" : tactic =>
  `(tactic| (
    try simp only [ModularForm.coe_add]
    repeat rw [ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL]
    try simp only [ModularForm.IsGLPos.coe_smul]
    repeat rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
    simp only [qExpansion_mkMonomForm]
    unfold evalEisPS monomialEisPS
    simp only [List.foldr_cons, List.foldr_nil, add_zero]
    push_cast
    module))

/-- `qexp_coeff f P N n v` closes a goal
`(PowerSeries.coeff n) (qExpansion 1 (f : ℍ → ℂ)) = v`, where `f` is the *name* of a
`def f : ModularForm 𝒮ℒ k` built as a sum of `(c : ℂ) • mkMonomForm a b k _` matching the `E₄/E₆`
polynomial `P : List (ℕ × ℕ × ℚ)`, `N` is a precision `> n`, and `v` is the (numeral) value.

It auto-derives the `evalEisPS` bridge (no per-form bridge lemma needed), rewrites via
`qexp_coeff_via_E4E6`, and discharges the rational coefficient by `decide +kernel`. -/
syntax "qexp_coeff" ident term:max num num term:max : tactic

macro_rules
  | `(tactic| qexp_coeff $f:ident $P:term $N:num $n:num $v:term) =>
    `(tactic| (
      have hb : qExpansion 1 ($f : ℍ → ℂ) = evalEisPS $P := by
        unfold $f
        qexp_bridge
      rw [qexp_coeff_via_E4E6 $P ($f : ℍ → ℂ) hb $N $n (by decide),
        show (evalEisList $P $N).getD $n 0 = ($v : ℚ) from by decide +kernel]
      push_cast
      ring))

end LeanBridge.QExpansion
