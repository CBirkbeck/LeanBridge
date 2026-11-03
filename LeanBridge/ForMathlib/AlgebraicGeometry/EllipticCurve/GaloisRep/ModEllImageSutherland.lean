import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.ModEllDeterminant
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.SutherlandGroupLabel

/-!
# The mod-`ℓ` image of an elliptic curve and the relation `IsSutherlandLabel`

The LMFDB identifies the mod-`ℓ` image of an elliptic curve (LMFDB `ec.galois_rep_modell_image`)
by Sutherland's label `ℓS.a.b.c[d]` of its conjugacy class in `GL₂(𝔽_ℓ)` (after Sutherland,
arXiv:1504.07618, §6.4), which is `WeierstrassCurve.modGaloisImageLabel`. This file is about the
labels of the image for the relation `Matrix.GeneralLinearGroup.IsSutherlandLabel`, which is not
functional on `Ns` and differs from Sutherland's script on `Ns`, `Cn`, `Nn`. The images in two bases
of `E[ℓ]` are conjugate, so whether a label is a label of the image for this relation does not
depend on the basis. Over `ℚ` the determinant of the image is surjective, so such a label has
`d = 1` and is written `ℓS.a.b.c`, without `[d]`.

## Main definitions

* `WeierstrassCurve.HasModGaloisImageSutherlandLabel`: a label `ℓS.a.b.c[d]` of the mod-`ℓ` image
  for the relation `Matrix.GeneralLinearGroup.IsSutherlandLabel`.

## Main results

* `WeierstrassCurve.isSutherlandLabel_modGaloisImageGL_iff`: the labels of the mod-`ℓ` image in a
  basis of `E[ℓ]` do not depend on the basis.
* `WeierstrassCurve.d_eq_one_of_hasModGaloisImageSutherlandLabel`: over `ℚ` the label has `d = 1`.
* `WeierstrassCurve.cls_eq_S4_of_hasModGaloisImageSutherlandLabel`: over `ℚ` the classes `A4` and
  `A5` do not occur.
-/

open Matrix

open scoped WeierstrassCurve

namespace WeierstrassCurve

section Field

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K] (W : WeierstrassCurve F)
  (ℓ : ℕ) [Fact ℓ.Prime] (L : GeneralLinearGroup.SutherlandGroupLabel)

variable (K) in
/-- `L` is a **label** of the mod-`ℓ` image of `W` for the relation
`GeneralLinearGroup.IsSutherlandLabel`: a label of the image in a basis of `E[ℓ]`, equivalently in
every basis (`isSutherlandLabel_modGaloisImageGL_iff`). That relation is not functional on `Ns` and
differs from Sutherland's script on `Ns`, `Cn`, `Nn`; Sutherland's label of the image (LMFDB
`ec.galois_rep_modell_image`) is `modGaloisImageLabel`. -/
def HasModGaloisImageSutherlandLabel : Prop :=
  ∃ b : Module.Basis (Fin 2) (ZMod ℓ) (AddSubgroup.torsionBy (W⁄K).toAffine.Point (ℓ : ℤ)),
    GeneralLinearGroup.IsSutherlandLabel ℓ (W.modGaloisImageGL ℓ b) L

/-- **Whether `L` is a label of the mod-`ℓ` image does not depend on the basis** of `E[ℓ]`. -/
lemma isSutherlandLabel_modGaloisImageGL_iff
    (b b' : Module.Basis (Fin 2) (ZMod ℓ) (AddSubgroup.torsionBy (W⁄K).toAffine.Point (ℓ : ℤ))) :
    GeneralLinearGroup.IsSutherlandLabel ℓ (W.modGaloisImageGL ℓ b') L ↔
      GeneralLinearGroup.IsSutherlandLabel ℓ (W.modGaloisImageGL ℓ b) L := by
  rcases W.exists_modGaloisImageGL_eq_map_conj ℓ b b' with ⟨P, hP⟩
  rw [hP, GeneralLinearGroup.isSutherlandLabel_map_conj_iff]

end Field

variable {K : Type*} [Field K] [DecidableEq K] [Algebra ℚ K] [IsSepClosure ℚ K]
  (W : WeierstrassCurve ℚ) [W.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
  (L : GeneralLinearGroup.SutherlandGroupLabel)

/-- **Over `ℚ` the label of the mod-`ℓ` image has `d = 1`** (LMFDB `ec.galois_rep_modell_image`):
it is written `ℓS.a.b.c`, without `[d]`, for `K` a separable closure of `ℚ`. -/
lemma d_eq_one_of_hasModGaloisImageSutherlandLabel (h : W.HasModGaloisImageSutherlandLabel K ℓ L) :
    L.d = 1 := by
  rcases h with ⟨b, hb⟩
  rw [hb.2.1, map_det_modGaloisImageGL]
  exact W.modGaloisImageDetIndex_eq_one ℓ

/-- **Over `ℚ` the classes `A4` and `A5` do not occur** (LMFDB `ec.galois_rep_modell_image`): an
exceptional label of the mod-`ℓ` image has class `S4`, for `K` a separable closure of `ℚ`. -/
lemma cls_eq_S4_of_hasModGaloisImageSutherlandLabel (h : W.HasModGaloisImageSutherlandLabel K ℓ L)
    (hL : 6 ≤ L.cls.toNat) : L.cls = .S4 := by
  rcases h with ⟨b, hb⟩
  refine hb.cls_eq_S4 ?_ hL
  rw [map_det_modGaloisImageGL, ← Subgroup.index_eq_one]
  exact W.modGaloisImageDetIndex_eq_one ℓ

end WeierstrassCurve
