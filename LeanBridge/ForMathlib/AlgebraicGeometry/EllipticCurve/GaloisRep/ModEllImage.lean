import Mathlib.LinearAlgebra.Determinant
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.Basic
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Exceptional
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.SutherlandLabel

/-!
# The image of the mod-`ℓ` Galois representation

The mod-`ℓ` image of an elliptic curve `W` over a field `F` is the image of the mod-`ℓ` Galois
representation, a subgroup of the automorphisms of `E[ℓ]`; in a basis of `E[ℓ]` it is a subgroup of
`GL₂(𝔽_ℓ)`, well defined up to conjugacy. The LMFDB identifies it by Sutherland's label
`ℓS.a.b.c`, decorated by `[d]` when the determinant is not surjective, `d` being the index of the
image of the determinant in `𝔽_ℓˣ`. A label `S.a.b.c` with `S` among `B`, `Cs`, `Ns`, `Cn`, `Nn`
names an explicit subgroup (`Matrix.GeneralLinearGroup.SutherlandLabel.subgroup`), and the image has
that label when it is that subgroup in some basis; for the exceptional labels only the type `A4`,
`S4`, `A5` of the projective image is recorded. The choice of the minimal `a`, `b`, `c` among
labels naming conjugate subgroups is a database convention and is not formalised.

## Main definitions

* `WeierstrassCurve.modGaloisImage` (LMFDB `ec.galois_rep_modell_image`): the mod-`ℓ` image, in
  `Aut(E[ℓ])`.
* `WeierstrassCurve.modGaloisImageGL` (LMFDB `ec.galois_rep_modell_image`): the mod-`ℓ` image in a
  basis of `E[ℓ]`, in `GL₂(𝔽_ℓ)`.
* `WeierstrassCurve.modGaloisImageDetIndex`: the index `d` of the image of the determinant.
* `WeierstrassCurve.HasModGaloisImageLabel` and `WeierstrassCurve.HasModGaloisImageExceptionalType`
  (LMFDB `ec.galois_rep_modell_image`): the mod-`ℓ` image has a given label.

## Main results

* `WeierstrassCurve.exists_modGaloisImageGL_eq_map_conj`: the mod-`ℓ` images in two bases are
  conjugate.
-/

open Matrix TauCeti
open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K] (W : WeierstrassCurve F)
  (ℓ : ℕ) [Fact ℓ.Prime]
  (b b' : Module.Basis (Fin 2) (ZMod ℓ) (AddSubgroup.torsionBy (W⁄K).toAffine.Point (ℓ : ℤ)))

/-- The **mod-`ℓ` image** (LMFDB `ec.galois_rep_modell_image`) of an elliptic curve `W` over `F`:
the image of the mod-`ℓ` Galois representation of `K ≃ₐ[F] K` (for `K` a separable closure, the
absolute Galois group), as a subgroup of the `𝔽_ℓ`-linear automorphisms of `E[ℓ]`. -/
noncomputable def modGaloisImage : Subgroup (LinearMap.GeneralLinearGroup (ZMod ℓ)
    (AddSubgroup.torsionBy (W⁄K).toAffine.Point (ℓ : ℤ))) :=
  (W.modGaloisRepresentation ℓ).range

/-- The **mod-`ℓ` image in a basis** `b` of `E[ℓ]` (LMFDB `ec.galois_rep_modell_image`): the image
of the mod-`ℓ` Galois representation as a subgroup of `GL₂(𝔽_ℓ)`, well defined up to conjugacy
(`exists_modGaloisImageGL_eq_map_conj`). -/
noncomputable def modGaloisImageGL : Subgroup (GL (Fin 2) (ZMod ℓ)) :=
  (W.modGaloisRepresentationGL ℓ b).range

/-- The mod-`ℓ` images in two bases are **conjugate** in `GL₂(𝔽_ℓ)`. -/
lemma exists_modGaloisImageGL_eq_map_conj : ∃ P : GL (Fin 2) (ZMod ℓ), W.modGaloisImageGL ℓ b' =
    (W.modGaloisImageGL ℓ b).map (MulAut.conj P).toMonoidHom :=
  (W.exists_modGaloisRepresentationGL_eq_conj ℓ b b').imp fun _ hP ↦
    (congr_arg MonoidHom.range (MonoidHom.ext hP)).trans (MonoidHom.range_comp _ _)

variable (K)

/-- The index `d` (LMFDB `ec.galois_rep_modell_image`) of the image under the determinant of the
mod-`ℓ` image in `𝔽_ℓˣ`; the label of the image carries `[d]` when `d > 1`. -/
noncomputable def modGaloisImageDetIndex : ℕ :=
  ((W.modGaloisImage (K := K) ℓ).map (Units.map LinearMap.det)).index

/-- The mod-`ℓ` image **has Sutherland's label** `ℓS.a.b.c` (LMFDB `ec.galois_rep_modell_image`),
for `S` among `B`, `Cs`, `Ns`, `Cn`, `Nn`: in some basis of `E[ℓ]` it is the subgroup of
`GL₂(𝔽_ℓ)` named by the label, that is, it is conjugate to that subgroup. -/
def HasModGaloisImageLabel (L : GeneralLinearGroup.SutherlandLabel) : Prop :=
  ∃ b : Module.Basis (Fin 2) (ZMod ℓ) (AddSubgroup.torsionBy (W⁄K).toAffine.Point (ℓ : ℤ)),
    W.modGaloisImageGL ℓ b = L.subgroup ℓ

/-- The mod-`ℓ` image **has exceptional type** `A4`, `S4` or `A5` (LMFDB
`ec.galois_rep_modell_image`): its image in `PGL₂(𝔽_ℓ)` is isomorphic to `A₄`, `S₄` or `A₅`. -/
def HasModGaloisImageExceptionalType (t : GeneralLinearGroup.ExceptionalType) : Prop :=
  ∃ b : Module.Basis (Fin 2) (ZMod ℓ) (AddSubgroup.torsionBy (W⁄K).toAffine.Point (ℓ : ℤ)),
    GeneralLinearGroup.HasExceptionalType (W.modGaloisImageGL ℓ b) t

end WeierstrassCurve
