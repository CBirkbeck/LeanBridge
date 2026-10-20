import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.Basic

/-!
# The image of the adelic Galois representation

The image of the adelic Galois representation of an elliptic curve without potential complex
multiplication over a number field is an open subgroup `H` of `GL₂(ℤ̂)`, here
`∏_ℓ GL₂(ℤ_ℓ)` (`WeierstrassCurve.adelicGaloisRepresentationGL`), and the LMFDB records its level,
its index and the genus of the modular curve `X_H`. The image depends on the bases of the Tate
modules only up to conjugacy, and conjugation changes neither the level nor the index (this
invariance is not formalised). The genus is not formalised: it needs the modular curve `X_H`, or the
reduction of `H` to `GL₂(ℤ/Nℤ)` together with the coset counts of the LMFDB's genus formula.

## Main definitions

* `WeierstrassCurve.adelicGaloisImage` (LMFDB `ec.galois_rep_adelic_image`): the adelic image.
* `WeierstrassCurve.adelicGaloisImageLevel` (LMFDB `ec.galois_rep_adelic_image`): its level.
* `WeierstrassCurve.adelicGaloisImageIndex` (LMFDB `ec.galois_rep_adelic_image`): its index.

## Main results

* `WeierstrassCurve.exists_adelicGaloisImage_eq_map_conj`: the adelic images in two families of
  bases are conjugate.
-/

open Matrix TauCeti
open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K] (W : WeierstrassCurve F)
  (b b' : ∀ ℓ : Nat.Primes, Module.Basis (Fin 2) ℤ_[ℓ] (TateModule ℓ (W⁄K).toAffine.Point))

/-- The **image of the adelic Galois representation** (LMFDB `ec.galois_rep_adelic_image`) of `W`,
in the bases `b ℓ` of the Tate modules: a subgroup of `∏_ℓ GL₂(ℤ_ℓ) = GL₂(ℤ̂)`, well defined up to
conjugacy (`exists_adelicGaloisImage_eq_map_conj`). For `K` a separable closure of a number field
`F` and `W` without potential complex multiplication it is open, by Serre's open image theorem. -/
noncomputable def adelicGaloisImage : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) :=
  (W.adelicGaloisRepresentationGL b).range

/-- The adelic images in two families of bases are **conjugate** in `∏_ℓ GL₂(ℤ_ℓ)`. -/
lemma exists_adelicGaloisImage_eq_map_conj : ∃ P : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ],
    W.adelicGaloisImage b' = (W.adelicGaloisImage b).map (MulAut.conj P).toMonoidHom :=
  (W.exists_adelicGaloisRepresentationGL_eq_conj b b').imp fun _ hP ↦
    (congr_arg MonoidHom.range (MonoidHom.ext hP)).trans (MonoidHom.range_comp _ _)

/-- The **level** of the adelic image (LMFDB `ec.galois_rep_adelic_image`): the least positive
integer `N` such that the image is the inverse image of its reduction to `GL₂(ℤ/Nℤ)`, its level
`GeneralLinearGroup.adelicLevel` as a subgroup of `GL₂(ℤ̂)` itself. It is positive when the image is
open (`GeneralLinearGroup.adelicLevel_pos`), and `0` when there is no such `N`, as for a curve with
potential complex multiplication. -/
noncomputable def adelicGaloisImageLevel : ℕ :=
  GeneralLinearGroup.adelicLevel ⊤ (W.adelicGaloisImage b)

/-- The **index** of the adelic image (LMFDB `ec.galois_rep_adelic_image`) in `GL₂(ℤ̂)`; for an open
image of level `N` it is the index `[GL₂(ℤ/Nℤ) : H]` of its reduction modulo `N`. It is `0` when
the index is infinite. -/
noncomputable def adelicGaloisImageIndex : ℕ :=
  (W.adelicGaloisImage b).index

end WeierstrassCurve
