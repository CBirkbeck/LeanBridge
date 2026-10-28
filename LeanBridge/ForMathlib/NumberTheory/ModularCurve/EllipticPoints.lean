import LeanBridge.ForMathlib.NumberTheory.ModularCurve.CongruenceSubgroupOfOpen
import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Finite
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Elliptic points of the modular curve `X_H`

An elliptic point of the modular curve `X_H` of an open subgroup `H` of `GL₂(ℤ̂)` is a point whose
stabiliser under the congruence subgroup `Γ_H = H ∩ SL₂(ℤ)` is finite and nontrivial. Since `-1`
acts trivially on the upper half-plane `ℍ`, stabilisers are taken in the image `Γ̄_H` of `Γ_H` in
`PSL₂(ℝ)`, which acts effectively. The stabiliser of a cusp is infinite, while the stabiliser of a
point of `ℍ` in the discrete group `Γ̄_H` is finite, so the elliptic points are the points of
`Γ̄_H \ ℍ` with nontrivial stabiliser: Tau Ceti's elliptic orbits `Subgroup.ellipticOrbits` of
`Γ̄_H`, whose finiteness results Tau Ceti proves for discrete subgroups of `PSL₂(ℝ)`. The
discreteness of `Γ̄_H`, hence the finiteness of the stabilisers of points of `ℍ`, is not formalised.

## Main definitions

* `Matrix.GeneralLinearGroup.modularGammaPSL`: the image `Γ̄_H` of `Γ_H` in `PSL₂(ℝ)`.
* `Matrix.GeneralLinearGroup.ellipticPoints` (LMFDB `modcurve.elliptic_points`): the elliptic
  points of `X_H`.

## Main results

* `Matrix.GeneralLinearGroup.ellipticPoints_eq_ellipticOrbits`: they are Tau Ceti's elliptic orbits
  of `Γ̄_H`.
-/

open scoped MatrixGroups

open UpperHalfPlane

namespace Matrix.GeneralLinearGroup

variable (H : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]))

/-- The image `Γ̄_H` in `PSL₂(ℝ)` of the congruence subgroup `Γ_H = H ∩ SL₂(ℤ)` of a subgroup `H` of
`GL₂(ℤ̂)`, the group acting effectively on the upper half-plane. -/
noncomputable def modularGammaPSL : Subgroup PSL(2, ℝ) :=
  (modularGamma H).map sl2zToPSL2R

/-- The **elliptic points** (LMFDB `modcurve.elliptic_points`) of the modular curve `X_H` of a
subgroup `H` of `GL₂(ℤ̂)`: the points of `Γ_H \ ℍ` whose stabiliser in the image `Γ̄_H` of
`Γ_H = H ∩ SL₂(ℤ)` in `PSL₂(ℝ)` is nontrivial. The cusps, whose stabilisers are infinite, are not
elliptic. -/
noncomputable def ellipticPoints : Set (MulAction.orbitRel.Quotient (modularGammaPSL H) ℍ) :=
  Quotient.mk _ '' (TauCeti.freeLocus (modularGammaPSL H) ℍ : Set ℍ)ᶜ

/-- **The elliptic points of `X_H` are Tau Ceti's elliptic orbits** of the image of `Γ_H` in
`PSL₂(ℝ)`. -/
lemma ellipticPoints_eq_ellipticOrbits : ellipticPoints H = (modularGammaPSL H).ellipticOrbits :=
  rfl

end Matrix.GeneralLinearGroup
