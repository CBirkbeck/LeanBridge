import LeanBridge.ForMathlib.NumberTheory.ModularCurve.CongruenceSubgroupOfOpen
import Mathlib.GroupTheory.DoubleCoset

/-!
# Cusps and cusp widths of an open subgroup of `GL₂(ℤ̂)`

For an open subgroup `H` of `GL₂(ℤ̂)` with `det(H) = ℤ̂ˣ`, the cusps of `H` are the double cosets
`±H \ GL₂(ℤ̂) / ⟨δ⟩` for `δ = [[1, 1], [0, 1]]`, and the width of a cusp is the number of right
cosets `±Hg` it contains, equivalently the least `h > 0` with `cδʰ = c`. As in
`LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level`, `GL₂(ℤ̂)` is the product `∏_ℓ GL₂(ℤ_ℓ)`.

That the cusps correspond to the cusps of the modular curve `X_H`, that the widths are finite for
open `H`, and that they sum to the `PSL₂`-index of `H` are not formalised.

## Main definitions

* `Matrix.GeneralLinearGroup.adelicCusps` (LMFDB `modcurve.cusp_widths`): the cusps of `H`.
* `Matrix.GeneralLinearGroup.adelicCuspWidth` (LMFDB `modcurve.cusp_widths`): the width of a cusp.
-/

open scoped MatrixGroups

namespace Matrix.GeneralLinearGroup

variable (H : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]))

/-- The **cusps** (LMFDB `modcurve.cusp_widths`) of a subgroup `H` of `GL₂(ℤ̂)`: the double cosets
`±H \ GL₂(ℤ̂) / ⟨δ⟩` for `δ = [[1, 1], [0, 1]]`. For open `H` with `det(H) = ℤ̂ˣ` they correspond
to the cusps of the modular curve `X_H`. -/
abbrev adelicCusps : Type :=
  DoubleCoset.Quotient (H.adjoinNegOne : Set (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]))
    (Subgroup.zpowers (sl2zToAdelic ModularGroup.T))

/-- The **width** (LMFDB `modcurve.cusp_widths`) of a cusp `c ∈ ±H \ GL₂(ℤ̂) / ⟨δ⟩` of a subgroup
`H` of `GL₂(ℤ̂)`: the number of right cosets `±Hg` contained in `c`, the size of the orbit of any
of them under the right action of `δ = [[1, 1], [0, 1]]`. -/
noncomputable def adelicCuspWidth (c : adelicCusps H) : ℕ :=
  Nat.card <| Quotient.mk (QuotientGroup.rightRel H.adjoinNegOne) '' {g | Quotient.mk _ g = c}

end Matrix.GeneralLinearGroup
