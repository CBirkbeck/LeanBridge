import LeanBridge.ForMathlib.NumberTheory.ModularCurve.CongruenceSubgroupOfOpen
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# The canonical field of definition of a modular curve

Let `H` be an open subgroup of `GL₂(ℤ̂)` of level `N`, and let `H_N` be its reduction modulo `N`.
The canonical field of definition of the geometric components of the modular curve `X_H` is the
subfield of `ℚ(ζ_N)` fixed by `det(H_N) ≤ (ℤ/Nℤ)ˣ`, the automorphism of `ℚ(ζ_N)` attached to
`t ∈ (ℤ/Nℤ)ˣ` being `ζ_N ↦ ζ_N ^ t`. We take this description, given in the knowl, as the
definition. As in `LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level`, `GL₂(ℤ̂) = ∏_ℓ GL₂(ℤ_ℓ)`
and its reduction modulo `N` takes values in `∏_ℓ GL₂(ℤ / ℓ ^ v_ℓ(N) ℤ)`; accordingly `det(H_N)` is
the subgroup of the `t ∈ (ℤ/Nℤ)ˣ` whose reductions modulo the `ℓ ^ v_ℓ(N)` are the determinants of
the reduction of an element of `H`, which is `det(H_N)` by the Chinese remainder theorem. The field
`ℚ(ζ_N)` is any field `L` generated over `ℚ` by a primitive `N`-th root of unity
(`IsCyclotomicExtension {N} ℚ L`).

The geometric definition, as the field fixed by the stabiliser in `Gal(ℚ̄/ℚ)` of a geometric
component of `X_H`, and its agreement with this one, need the modular curve `X_H`, which is not
formalised.

## Main definitions

* `Matrix.GeneralLinearGroup.detReduction`: the subgroup `det(H_N)` of `(ℤ/Nℤ)ˣ`.
* `Matrix.GeneralLinearGroup.canonicalFieldOfLevel`: the subfield of `ℚ(ζ_N)` fixed by `det(H_N)`.
* `Matrix.GeneralLinearGroup.canonicalField` (LMFDB `modcurve.canonical_field`): the canonical field
  of definition of `X_H`, for `N` the level of `H`.
-/

open Polynomial

namespace Matrix.GeneralLinearGroup

variable (N : ℕ) (H : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ])) (L : Type*) [Field L]
  [Algebra ℚ L]

/-- The subgroup `det(H_N)` of `(ℤ/Nℤ)ˣ` for a subgroup `H` of `GL₂(ℤ̂) = ∏_ℓ GL₂(ℤ_ℓ)`: the units
`t` whose reduction modulo `ℓ ^ v_ℓ(N)` is the determinant of the reduction of `h_ℓ` modulo
`ℓ ^ v_ℓ(N)` for every prime `ℓ`, for some `h ∈ H`. -/
noncomputable def detReduction : Subgroup (ZMod N)ˣ :=
  (H.map <| (MonoidHom.pi fun ℓ : Nat.Primes ↦ det.comp (Pi.evalMonoidHom _ ℓ)).comp <|
    adelicReduction N).comap <| MonoidHom.pi fun ℓ : Nat.Primes ↦
      Units.map (ZMod.castHom (Nat.ordProj_dvd N ℓ) _).toMonoidHom

variable [NeZero N] [IsCyclotomicExtension {N} ℚ L] in
/-- The subfield of a cyclotomic field `L = ℚ(ζ_N)` fixed by `det(H_N) ≤ (ℤ/Nℤ)ˣ`, for a subgroup
`H` of `GL₂(ℤ̂)` and a positive integer `N`, where `t ∈ (ℤ/Nℤ)ˣ` acts by `ζ_N ↦ ζ_N ^ t`. -/
noncomputable def canonicalFieldOfLevel : IntermediateField ℚ L :=
  IntermediateField.fixedField <| (detReduction N H).comap <|
    (IsCyclotomicExtension.autEquivPow L <| cyclotomic.irreducible_rat <| NeZero.pos N).toMonoidHom

variable [NeZero (adelicLevel ⊤ H)] [IsCyclotomicExtension {adelicLevel ⊤ H} ℚ L] in
/-- The **canonical field of definition** (LMFDB `modcurve.canonical_field`) of the modular curve
`X_H` of an open subgroup `H` of `GL₂(ℤ̂)` of level `N`: the subfield of a cyclotomic field
`L = ℚ(ζ_N)` fixed by `det(H_N) ≤ (ℤ/Nℤ)ˣ`. The level is nonzero for open `H`. -/
noncomputable def canonicalField : IntermediateField ℚ L :=
  canonicalFieldOfLevel (adelicLevel ⊤ H) H L

end Matrix.GeneralLinearGroup
