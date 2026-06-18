import LeanBridge.ForMathlib.QExpansion.Generic
import LeanBridge.ForMathlib.QExpansion.Sturm
import Lean.Elab.Tactic

/-!
# `qexp_certify_pieces` tactic

A general-purpose tactic for the multi-piece q-coefficient certification pattern:
proves `(qExp ↑f).coeff n = some-algebraic-value` where `f = f_0 + α · f_1 + α² · f_2 + …`
by chaining the per-piece coefficient theorems and `decide +kernel` on the rational lists.

## Usage

```lean
qexp_certify_pieces decomp_lemma [thm_0, thm_1, …, thm_{d-1}]
                     [polyData_0, polyData_1, …, polyData_{d-1}]
                     sturm idx
                     [val_0, val_1, …, val_{d-1}]
```

Produces the rewrite chain + `push_cast; ring` to close the goal.
-/

namespace LeanBridge.QExpansion

open Lean Elab Tactic Meta

/-- Multi-piece q-coefficient certification.
For `f = f_0 + α · f_1 + ... + α^(d-1) · f_(d-1)` with each `f_i` having rational E₄/E₆
coefficients, this tactic proves `(qExp ↑f).coeff n = sum α^i · val_i`. -/
syntax "qexp_certify_pieces"
  term:max
  "[" term,* "]"
  "[" term,* "]"
  num num
  "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| qexp_certify_pieces $decomp:term
              [$coeffThms:term,*] [$polyDatas:term,*]
              $sturm:num $idx:num [$values:term,*]) => do
    let coeffThms := coeffThms.getElems
    let polyDatas := polyDatas.getElems
    let values := values.getElems
    unless coeffThms.size = polyDatas.size ∧ polyDatas.size = values.size do
      throwError "qexp_certify_pieces: lists must be the same length"
    -- Build the rewrite chain by sequencing individual rw calls
    -- Each `rw [t]` takes a `term` directly via the convenient overload.
    let mkRule (t : Term) : MetaM (TSyntax `Lean.Parser.Tactic.rwRule) := do
      `(Lean.Parser.Tactic.rwRule| $t:term)
    evalTactic (← `(tactic| rw [$(← mkRule decomp):rwRule]))
    for thm in coeffThms do
      let rule ← mkRule (← `($thm $sturm $idx (by decide)))
      evalTactic (← `(tactic| rw [$rule:rwRule]))
    for i in [0:polyDatas.size] do
      let polyData := polyDatas[i]!
      let value := values[i]!
      let rule ← mkRule (← `(show (evalEisList $polyData $sturm).getD $idx 0 = ($value : ℚ)
                              from by decide +kernel))
      evalTactic (← `(tactic| rw [$rule:rwRule]))
    evalTactic (← `(tactic| push_cast))
    evalTactic (← `(tactic| ring))

end LeanBridge.QExpansion
