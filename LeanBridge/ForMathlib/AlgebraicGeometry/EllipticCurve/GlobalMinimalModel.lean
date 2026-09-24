import TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel

/-!
# Reduced minimal models over `ℚ`

Global and semi-global minimality (LMFDB `ec.global_minimal_model`,
`ec.semi_global_minimal_model`) are Tau Ceti's `WeierstrassCurve.IsGlobalMinimal` and
`WeierstrassCurve.IsSemiGlobalMinimal`. This file adds the normalization LMFDB uses over `ℚ`.

## Main definitions

* `WeierstrassCurve.IsReducedMinimal` (LMFDB `ec.q.minimal_weierstrass_equation`).
-/

namespace WeierstrassCurve

/-- A Weierstrass curve over `ℚ` is **reduced minimal** (LMFDB
`ec.q.minimal_weierstrass_equation`) if it is globally minimal over `ℤ` with `a₁, a₃ ∈ {0, 1}` and
`a₂ ∈ {-1, 0, 1}`. These normalizations single out a unique globally minimal model of an elliptic
curve over `ℚ`. -/
def IsReducedMinimal (W : WeierstrassCurve ℚ) [W.IsElliptic] : Prop :=
  IsGlobalMinimal ℤ W ∧
    (W.a₁ = 0 ∨ W.a₁ = 1) ∧ (W.a₂ = -1 ∨ W.a₂ = 0 ∨ W.a₂ = 1) ∧ (W.a₃ = 0 ∨ W.a₃ = 1)

end WeierstrassCurve
