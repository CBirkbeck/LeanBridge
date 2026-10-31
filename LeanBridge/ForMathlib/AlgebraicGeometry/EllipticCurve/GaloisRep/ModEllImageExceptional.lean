import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.ModEllImage
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.ExceptionalDeterminant

/-!
# Mod-`ℓ` images of exceptional type `A4` and `A5`

The mod-`ℓ` image of an elliptic curve over a number field `K` that does not contain `SL₂(𝔽_ℓ)`
carries one of Sutherland's labels (LMFDB `ec.galois_rep_modell_image`), and the knowl states that
the exceptional types `A4` and `A5` cannot occur when `K = ℚ`. The reason is that the determinant
of the mod-`ℓ` image is then surjective (it is the mod-`ℓ` cyclotomic character, by the Weil
pairing), while for `ℓ` odd a subgroup of `GL₂(𝔽_ℓ)` whose image in `PGL₂(𝔽_ℓ)` is `A₄` or `A₅`
has square determinants, and for `ℓ = 2` the group `PGL₂(𝔽₂)` of order `6` is too small
(`Matrix.GeneralLinearGroup.eq_S4_of_hasExceptionalType`). Here this is proved for any
base field, with the surjectivity of the determinant (the index `d = 1` of the knowl) as the
hypothesis; that it holds over `ℚ` is `WeierstrassCurve.modGaloisImageDetIndex_eq_one`, in
`LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.ModEllDeterminant`.

## Main results

* `WeierstrassCurve.eq_S4_of_hasModGaloisImageExceptionalType` (LMFDB
  `ec.galois_rep_modell_image`): a mod-`ℓ` image with surjective determinant does not have
  exceptional type `A4` or `A5`.
-/

open Matrix TauCeti

open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K] (W : WeierstrassCurve F)
  (ℓ : ℕ) [Fact ℓ.Prime]

lemma map_det_modGaloisImageGL
    (b : Module.Basis (Fin 2) (ZMod ℓ) (AddSubgroup.torsionBy (W⁄K).toAffine.Point (ℓ : ℤ))) :
    (W.modGaloisImageGL ℓ b).map GeneralLinearGroup.det =
      (W.modGaloisImage (K := K) ℓ).map (Units.map LinearMap.det) := by
  rw [modGaloisImageGL, modGaloisImage, MonoidHom.map_range, MonoidHom.map_range,
    modGaloisRepresentationGL, ← MonoidHom.comp_assoc]
  congr 2
  refine MonoidHom.ext fun φ ↦ Units.ext ?_
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, GeneralLinearGroup.val_det_apply,
    GeneralLinearGroup.coe_toLin'_symm, LinearMap.det_toMatrix, Units.coe_map]

variable (K) in
/-- **The exceptional types `A4` and `A5` do not occur for a mod-`ℓ` image with surjective
determinant** (LMFDB `ec.galois_rep_modell_image`): if the image of the determinant on the mod-`ℓ`
image has index `d = 1` in `𝔽_ℓˣ` (as over `ℚ`) and the image has exceptional type `t`, then `t`
is `S4`. -/
lemma eq_S4_of_hasModGaloisImageExceptionalType (hd : W.modGaloisImageDetIndex K ℓ = 1)
    {t : GeneralLinearGroup.ExceptionalType} (ht : W.HasModGaloisImageExceptionalType K ℓ t) :
    t = .S4 := by
  rcases ht with ⟨b, hb⟩
  rw [modGaloisImageDetIndex, Subgroup.index_eq_one, ← W.map_det_modGaloisImageGL ℓ b] at hd
  exact GeneralLinearGroup.eq_S4_of_hasExceptionalType hd hb

end WeierstrassCurve
