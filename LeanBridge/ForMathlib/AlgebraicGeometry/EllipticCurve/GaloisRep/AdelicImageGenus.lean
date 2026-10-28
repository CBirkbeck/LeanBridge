import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.AdelicImage
import LeanBridge.ForMathlib.NumberTheory.ModularCurve.GenusOfOpenSubgroup

/-!
# The genus of the adelic image of an elliptic curve

The image `H` of the adelic Galois representation of an elliptic curve, an open subgroup of
`GL₂(ℤ̂) = ∏_ℓ GL₂(ℤ_ℓ)` when the curve has no potential complex multiplication, has a genus, that of
the modular curve `X_H`. The LMFDB computes it (LMFDB `gl2.genus`) by the Riemann–Hurwitz formula
`g = 1 + i/12 - ν₂/4 - ν₃/3 - ν_∞/2` for `Γ_H = ±H_N ∩ SL₂(ℤ/Nℤ)`, where `N` is the level of `H`
and `H_N` its reduction modulo `N`: this is LeanBridge's `Matrix.GeneralLinearGroup.adelicGenus`.
The identification with the genus of the curve `X_H` itself is not formalised: Tau Ceti has no
modular curve `X_H`.

## Main definitions

* `WeierstrassCurve.adelicGaloisImageGenus` (LMFDB `ec.galois_rep_adelic_image`): the genus of the
  adelic image of an elliptic curve.
-/

open TauCeti

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K] (W : WeierstrassCurve F)
  (b : ∀ ℓ : Nat.Primes, Module.Basis (Fin 2) ℤ_[ℓ] (TateModule ℓ (W⁄K).toAffine.Point))

/-- The **genus** of the adelic image (LMFDB `ec.galois_rep_adelic_image`): the genus
`Matrix.GeneralLinearGroup.adelicGenus` of the image `H` of the adelic Galois representation in
`GL₂(ℤ̂)`, that of the modular curve `X_H`. It does not depend on the bases, which change `H` by a
conjugation (this invariance is not formalised). -/
noncomputable def adelicGaloisImageGenus : ℚ :=
  Matrix.GeneralLinearGroup.adelicGenus (W.adelicGaloisImage b)

end WeierstrassCurve
