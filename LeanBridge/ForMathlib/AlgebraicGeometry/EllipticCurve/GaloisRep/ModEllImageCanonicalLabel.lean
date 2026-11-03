import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.ModEllImageSutherland
import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.GL2LabelClassification

/-!
# The Sutherland label of the mod-`ℓ` image of an elliptic curve

Every subgroup of `GL₂(𝔽_ℓ)` has exactly one Sutherland label, and two subgroups have the same
label exactly when they are conjugate
(`Matrix.GeneralLinearGroup.sutherlandLabel_eq_sutherlandLabel_iff`). So the mod-`ℓ` image of an
elliptic curve is identified by a single label (LMFDB `ec.galois_rep_modell_image`), which does not
depend on the basis of `E[ℓ]`, and over `ℚ` this label has `d = 1` and class outside `A4`, `A5`.

## Main definitions

* `WeierstrassCurve.modGaloisImageLabel` (LMFDB `ec.galois_rep_modell_image`): the Sutherland label
  of the mod-`ℓ` image in a basis of `E[ℓ]`.

## Main results

* `WeierstrassCurve.modGaloisImageLabel_eq`: **the label of the mod-`ℓ` image does not depend on the
  basis** of `E[ℓ]`.
* `WeierstrassCurve.modGaloisImageLabel_eq_iff`: **the labels of two mod-`ℓ` images are equal
  exactly when the images are conjugate**, also for two different curves.
* `WeierstrassCurve.modGaloisImageLabel_cls_eq_G_iff`: the label has class `G` exactly when the
  image contains `SL₂(𝔽_ℓ)`.
* `WeierstrassCurve.modGaloisImageLabel_d`: `d` is the index of the determinant of the image.
* `WeierstrassCurve.modGaloisImageLabel_d_eq_one`: over `ℚ` the label has `d = 1`.
* `WeierstrassCurve.modGaloisImageLabel_cls_eq_S4`: over `ℚ` the classes `A4` and `A5` do not occur.
-/

open Matrix

open scoped Pointwise WeierstrassCurve

namespace WeierstrassCurve

section Field

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K] (W : WeierstrassCurve F)
  (ℓ : ℕ) [Fact ℓ.Prime]
  (b : Module.Basis (Fin 2) (ZMod ℓ) (AddSubgroup.torsionBy (W⁄K).toAffine.Point (ℓ : ℤ)))

/-- **Sutherland's label** `ℓS.a.b.c[d]` of the mod-`ℓ` image of `W` (LMFDB
`ec.galois_rep_modell_image`), in a basis of `E[ℓ]`, on which it does not depend
(`modGaloisImageLabel_eq`). A basis exists for an elliptic curve over a separably closed field `K`
in which `ℓ` is invertible (`WeierstrassCurve.nonempty_basis_torsionBy`). -/
noncomputable def modGaloisImageLabel : GeneralLinearGroup.SutherlandGroupLabel :=
  GeneralLinearGroup.sutherlandLabel ℓ (W.modGaloisImageGL ℓ b)

/-- **The label of the mod-`ℓ` image does not depend on the basis** of `E[ℓ]`. -/
lemma modGaloisImageLabel_eq
    (b' : Module.Basis (Fin 2) (ZMod ℓ) (AddSubgroup.torsionBy (W⁄K).toAffine.Point (ℓ : ℤ))) :
    W.modGaloisImageLabel ℓ b = W.modGaloisImageLabel ℓ b' := by
  rcases W.exists_modGaloisImageGL_eq_map_conj ℓ b b' with ⟨P, hP⟩
  rw [modGaloisImageLabel, modGaloisImageLabel,
    GeneralLinearGroup.sutherlandLabel_eq_sutherlandLabel_iff, hP,
    GeneralLinearGroup.map_conj_eq_smul]
  exact MulAction.mem_orbit _ _

/-- **The labels of two mod-`ℓ` images are equal exactly when the images are conjugate**. -/
lemma modGaloisImageLabel_eq_iff {F' K' : Type*} [Field F'] [Field K'] [DecidableEq K']
    [Algebra F' K'] (W' : WeierstrassCurve F')
    (b' : Module.Basis (Fin 2) (ZMod ℓ) (AddSubgroup.torsionBy (W'⁄K').toAffine.Point (ℓ : ℤ))) :
    W.modGaloisImageLabel ℓ b = W'.modGaloisImageLabel ℓ b' ↔ W'.modGaloisImageGL ℓ b' ∈
      GeneralLinearGroup.subgroupConjClass ℓ (W.modGaloisImageGL ℓ b) :=
  GeneralLinearGroup.sutherlandLabel_eq_sutherlandLabel_iff

/-- **The label has class `G` exactly when the image contains `SL₂(𝔽_ℓ)`**: the classes of the
other images are `B`, `Cs`, `Cn`, `Ns`, `Nn`, `A4`, `S4`, `A5` (LMFDB
`ec.galois_rep_modell_image`). -/
lemma modGaloisImageLabel_cls_eq_G_iff :
    (W.modGaloisImageLabel ℓ b).cls = .G ↔ GeneralLinearGroup.det.ker ≤ W.modGaloisImageGL ℓ b :=
  GeneralLinearGroup.cls_sutherlandLabel_eq_G_iff

/-- **`d` is the index of the determinant of the image** (LMFDB `ec.galois_rep_modell_image`). -/
lemma modGaloisImageLabel_d : (W.modGaloisImageLabel ℓ b).d = W.modGaloisImageDetIndex K ℓ := by
  rw [modGaloisImageLabel, GeneralLinearGroup.d_sutherlandLabel, map_det_modGaloisImageGL]
  rfl

end Field

variable {K : Type*} [Field K] [DecidableEq K] [Algebra ℚ K] [IsSepClosure ℚ K]
  (W : WeierstrassCurve ℚ) [W.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
  (b : Module.Basis (Fin 2) (ZMod ℓ) (AddSubgroup.torsionBy (W⁄K).toAffine.Point (ℓ : ℤ)))

/-- **Over `ℚ` the label of the mod-`ℓ` image has `d = 1`** (LMFDB `ec.galois_rep_modell_image`),
for `K` a separable closure of `ℚ`. -/
lemma modGaloisImageLabel_d_eq_one : (W.modGaloisImageLabel ℓ b).d = 1 := by
  rw [modGaloisImageLabel_d]
  exact W.modGaloisImageDetIndex_eq_one ℓ

/-- **Over `ℚ` the classes `A4` and `A5` do not occur** (LMFDB `ec.galois_rep_modell_image`): an
exceptional label of the mod-`ℓ` image has class `S4`, for `K` a separable closure of `ℚ`. -/
lemma modGaloisImageLabel_cls_eq_S4 (hL : 6 ≤ (W.modGaloisImageLabel ℓ b).cls.toNat) :
    (W.modGaloisImageLabel ℓ b).cls = .S4 := by
  refine GeneralLinearGroup.cls_sutherlandLabel_eq_S4 ?_ hL
  rw [map_det_modGaloisImageGL, ← Subgroup.index_eq_one]
  exact W.modGaloisImageDetIndex_eq_one ℓ

end WeierstrassCurve
