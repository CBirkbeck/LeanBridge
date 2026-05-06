import LeanBridge.ForMathlib.QExpansion.DeltaBridge

/-!
# Examples: certifying coefficients of Δ's q-expansion

This file demonstrates two things:

1. The **manual usage pattern** for `qexp_coeff_via_E4E6`: a `rw` to push the abstract
   coefficient equality through to a list-side rational, then `decide +kernel` for the
   rational arithmetic, finishing with a cast.
2. A small **`qexp_certify` macro** that bundles this pattern, so a single coefficient check
   becomes a one-liner.

Both routes prove the same theorem: the `n`-th q-coefficient of the modular discriminant
matches the corresponding Ramanujan tau value.

The values used below are τ(n) for n = 0, 1, ..., 11. Reference (OEIS A000594):
0, 1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612.
-/

namespace LeanBridge.QExpansion

open ModularForm PowerSeries UpperHalfPlane

/-! ## Manual pattern: the form every certificate takes -/

/-- τ(0) = 0. -/
example : (PowerSeries.coeff (R := ℂ) 0)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = 0 := by
  rw [discriminant_qExpansion_coeff_via_generic 12 0 (by decide),
    show (evalEisList Delta_polyData 12).getD 0 0 = (0 : ℚ) from by decide +kernel]
  push_cast; rfl

/-- τ(1) = 1. -/
example : (PowerSeries.coeff (R := ℂ) 1)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = 1 := by
  rw [discriminant_qExpansion_coeff_via_generic 12 1 (by decide),
    show (evalEisList Delta_polyData 12).getD 1 0 = (1 : ℚ) from by decide +kernel]
  push_cast; rfl

/-! ## A `qexp_certify` macro

Bundles the manual pattern: given a precision `N` and an index `n`, the macro generates the
`rw + decide +kernel + push_cast + rfl` chain. The user only writes the target. -/

/-- Certifies a single q-expansion coefficient of `ModularForm.discriminant` against the
generic E₄/E₆ list-based computation. Usage:
`by qexp_certify_delta (precision := N) (idx := n) (value := q)` where `q : ℚ` is the
expected value (which must equal the goal's right-hand side after casting `ℚ → ℂ`). -/
syntax "qexp_certify_delta" "(" "precision" ":=" num ")" "(" "idx" ":=" num ")"
  "(" "value" ":=" term ")" : tactic

macro_rules
  | `(tactic| qexp_certify_delta (precision := $N:num) (idx := $n:num) (value := $v:term)) =>
    `(tactic|
        (rw [discriminant_qExpansion_coeff_via_generic $N $n (by decide),
             show (evalEisList Delta_polyData $N).getD $n 0 = ($v : ℚ) from by decide +kernel]
         push_cast; rfl))

/-! ## The same examples, via the macro -/

/-- τ(2) = -24. -/
example : (PowerSeries.coeff (R := ℂ) 2)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = -24 := by
  qexp_certify_delta (precision := 12) (idx := 2) (value := -24)

/-- τ(3) = 252. -/
example : (PowerSeries.coeff (R := ℂ) 3)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = 252 := by
  qexp_certify_delta (precision := 12) (idx := 3) (value := 252)

/-- τ(4) = -1472. -/
example : (PowerSeries.coeff (R := ℂ) 4)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = -1472 := by
  qexp_certify_delta (precision := 12) (idx := 4) (value := -1472)

/-- τ(5) = 4830. -/
example : (PowerSeries.coeff (R := ℂ) 5)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = 4830 := by
  qexp_certify_delta (precision := 12) (idx := 5) (value := 4830)

/-- τ(6) = -6048. -/
example : (PowerSeries.coeff (R := ℂ) 6)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = -6048 := by
  qexp_certify_delta (precision := 12) (idx := 6) (value := -6048)

/-- τ(7) = -16744. -/
example : (PowerSeries.coeff (R := ℂ) 7)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = -16744 := by
  qexp_certify_delta (precision := 12) (idx := 7) (value := -16744)

/-- τ(8) = 84480. -/
example : (PowerSeries.coeff (R := ℂ) 8)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = 84480 := by
  qexp_certify_delta (precision := 12) (idx := 8) (value := 84480)

/-- τ(9) = -113643. -/
example : (PowerSeries.coeff (R := ℂ) 9)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = -113643 := by
  qexp_certify_delta (precision := 12) (idx := 9) (value := -113643)

/-- τ(10) = -115920. -/
example : (PowerSeries.coeff (R := ℂ) 10)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = -115920 := by
  qexp_certify_delta (precision := 12) (idx := 10) (value := -115920)

/-- τ(11) = 534612. -/
example : (PowerSeries.coeff (R := ℂ) 11)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = 534612 := by
  qexp_certify_delta (precision := 12) (idx := 11) (value := 534612)

/-! ## Higher precision: τ at index 20

The same `precision := 12` macro fails the index-bound side condition for `idx := 20`; bump
the precision argument and the rest of the proof goes through unchanged. The increased work
is purely in the `decide +kernel` step (longer convolution). -/

/-- τ(20) = -7109760. -/
example : (PowerSeries.coeff (R := ℂ) 20)
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = -7109760 := by
  qexp_certify_delta (precision := 21) (idx := 20) (value := -7109760)

end LeanBridge.QExpansion
