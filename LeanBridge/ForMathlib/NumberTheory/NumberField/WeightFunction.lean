import Mathlib.Basic.NNReal.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Weight functions on finite groups

Inertial height functions, which order the Galois representations `Gal(ℚ̄/ℚ) → G` into a finite
group `G` (equivalently, number fields with Galois group `G`) for counting, are built from a weight
function on `G`: a function `G → ℝ≥0` vanishing exactly at the identity and invariant under
conjugation and under powering by integers prime to the order of `G`. The weight function equal
to `1` away from the identity gives the radical discriminant.

## Main definitions

* `NumberField.WeightFunction` (LMFDB `nf.inertial_height_function`).
* `NumberField.WeightFunction.indicator`: the weight function equal to `1` away from the identity.

The local heights `H_{w,p}(φ) = p ^ w(φ(τ_p))` at the primes `p ∤ #G`, where `τ_p` generates the
tame inertia of `Gal(ℚ̄_p/ℚ_p)`, and the inertial height function, their product with auxiliary
local heights at the primes dividing `#G`, are not defined here. (The LMFDB knowl writes
`H_{w,p}(φ) = w(φ(τ_p))`, which vanishes at every unramified `φ`; the power of `p` is what makes the
weight equal to `1` away from the identity give the radical discriminant.)
-/

open scoped NNReal

namespace NumberField

variable (G : Type*) [Group G]

/-- A **weight function** on a group `G` (LMFDB `nf.inertial_height_function`): a function
`w : G → ℝ≥0` such that `w g = 0` exactly when `g = 1`, `w (h g h⁻¹) = w g`, and `w (g ^ n) = w g`
for every natural number `n` prime to the order of `G`.

The LMFDB knowl asks for the last condition for the `n` with `n ∤ #G`, which no function vanishing
only at the identity satisfies for a nontrivial finite `G` (take `n` a multiple of `#G` not
dividing `#G`); its gloss "invariant under invertible powering" is the condition imposed here. -/
structure WeightFunction where
  /-- The function. -/
  toFun : G → ℝ≥0
  /-- It vanishes exactly at the identity. -/
  toFun_eq_zero_iff (g : G) : toFun g = 0 ↔ g = 1
  /-- It is invariant under conjugation. -/
  toFun_conj (g h : G) : toFun (h * g * h⁻¹) = toFun g
  /-- It is invariant under powering by integers prime to the order of the group. -/
  toFun_pow (g : G) (n : ℕ) : n.Coprime (Nat.card G) → toFun (g ^ n) = toFun g

namespace WeightFunction

variable {G} [DecidableEq G]

/-- The **weight function** equal to `1` away from the identity, for which an inertial height
function is the radical discriminant: the product of the primes ramified in the number field
corresponding to a Galois representation. -/
def indicator : WeightFunction G where
  toFun g := if g = 1 then 0 else 1
  toFun_eq_zero_iff _ := by simp
  toFun_conj _ _ := by simp
  toFun_pow _ _ hn := by
    simp only [(and_iff_left pow_card_eq_one').symm.trans (pow_eq_one_iff_of_coprime hn)]

end WeightFunction

end NumberField
