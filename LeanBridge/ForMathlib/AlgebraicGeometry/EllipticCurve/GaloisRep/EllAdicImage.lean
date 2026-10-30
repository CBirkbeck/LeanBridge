import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.Basic

/-!
# The image of the `ℓ`-adic Galois representation

The image of the `ℓ`-adic Galois representation of an elliptic curve `W` over a field `F` is a
subgroup `H` of `GL₂(ℤ_ℓ)`, in a basis of the Tate module `T_ℓ E`
(`WeierstrassCurve.tateModuleGaloisRepresentationGL`); another basis conjugates it. The LMFDB
records its level and index (LMFDB `ec.galois_rep_elladic_image`), and for `ℓ = 2` its Rouse label
(LMFDB `ec.rouse_label`): the label `Xk`, `1 ≤ k ≤ 727` (LMFDB `modcurve.other_labels`), that Rouse
and Zureick-Brown give to the modular curve `X_H` parametrising the elliptic curves whose `2`-adic
image is contained in a conjugate of `H`, for a subgroup `H` that the knowl does not specify
further. The numbering `k` is an enumeration of their database that the knowl does not define, and
it is not formalised. Rouse and Zureick-Brown let matrices act on the right, so their subgroups are
the transposes of those here. What is formalised for the Rouse label is its mathematical content:
the `2`-adic image up to conjugacy, and the condition that it be contained in a conjugate of a given
subgroup `H`. The level and the index of the image, which do not depend on the basis, are not part
of the Rouse label.

## Main definitions

* `WeierstrassCurve.tateModuleGaloisImage` (LMFDB `ec.galois_rep_elladic_image`, and
  `ec.rouse_label` for `ℓ = 2`): the `ℓ`-adic image.
* `WeierstrassCurve.tateModuleGaloisImageLevel` (LMFDB `ec.galois_rep_elladic_image`, `gl2.level`):
  its level.
* `WeierstrassCurve.tateModuleGaloisImageIndex` (LMFDB `gl2.index`): its index.
* `WeierstrassCurve.HasTateModuleGaloisImageIn` (LMFDB `ec.rouse_label` for `ℓ = 2`): the image is
  contained in a given subgroup up to conjugacy.

## Main results

* `WeierstrassCurve.exists_tateModuleGaloisImage_eq_map_conj`: the `ℓ`-adic images in two bases
  are conjugate.
* `Matrix.GeneralLinearGroup.padicLevel_map_conj`: conjugate subgroups of `GL_n(ℤ_ℓ)` have the same
  level.
* `WeierstrassCurve.tateModuleGaloisImageLevel_eq` and
  `WeierstrassCurve.tateModuleGaloisImageIndex_eq`: the level and the index of the `ℓ`-adic image do
  not depend on the basis.
-/

open Matrix TauCeti

lemma Subgroup.comap_map_map_conj {G Q : Type*} [Group G] [Group Q] (π : G →* Q) (P : G)
    (H : Subgroup G) : ((H.map (MulAut.conj P).toMonoidHom).map π).comap π =
    ((H.map π).comap π).map (MulAut.conj P).toMonoidHom := by
  rw [comap_map_eq, comap_map_eq, map_sup, MulEquiv.toMonoidHom_eq_coe, π.normal_ker.map_conj_eq]

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Conjugate subgroups of `GL_n(ℤ_ℓ)` have the same level** (LMFDB `gl2.level`). -/
lemma padicLevel_map_conj (P : GL n ℤ_[ℓ]) (H : Subgroup (GL n ℤ_[ℓ])) :
    padicLevel ℓ ⊤ (H.map (MulAut.conj P).toMonoidHom) = padicLevel ℓ ⊤ H := by
  simp only [padicLevel, top_inf_eq, Subgroup.comap_map_map_conj,
    (Subgroup.map_injective (f := (MulAut.conj P).toMonoidHom) (MulAut.conj P).injective).eq_iff]

end Matrix.GeneralLinearGroup

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K] (W : WeierstrassCurve F)
  (ℓ : ℕ) [Fact ℓ.Prime] (b b' : Module.Basis (Fin 2) ℤ_[ℓ] (TateModule ℓ (W⁄K).toAffine.Point))

/-- The **image of the `ℓ`-adic Galois representation** (LMFDB `ec.galois_rep_elladic_image`, and
LMFDB `ec.rouse_label` for `ℓ = 2`) of `W`, in the basis `b` of the Tate module `T_ℓ E`: a subgroup
of `GL₂(ℤ_ℓ)`, well defined up to conjugacy (`exists_tateModuleGaloisImage_eq_map_conj`). For
`ℓ = 2` the Rouse label of `W` is the label of the modular curve `X_H` of a subgroup `H` of
`GL₂(ℤ₂)` containing a conjugate of this image (`HasTateModuleGaloisImageIn`), which the knowl does
not specify further; the numbering `Xk` of these curves is an enumeration of the database of Rouse
and Zureick-Brown, which is not formalised. -/
noncomputable def tateModuleGaloisImage : Subgroup (GL (Fin 2) ℤ_[ℓ]) :=
  (W.tateModuleGaloisRepresentationGL ℓ b).range

/-- The `ℓ`-adic images in two bases are **conjugate** in `GL₂(ℤ_ℓ)`. -/
lemma exists_tateModuleGaloisImage_eq_map_conj : ∃ P : GL (Fin 2) ℤ_[ℓ],
    W.tateModuleGaloisImage ℓ b' = (W.tateModuleGaloisImage ℓ b).map (MulAut.conj P).toMonoidHom :=
  (W.exists_tateModuleGaloisRepresentationGL_eq_conj ℓ b b').imp fun _ hP ↦
    (congr_arg MonoidHom.range (MonoidHom.ext hP)).trans (MonoidHom.range_comp _ _)

/-- The **level** of the `ℓ`-adic image (LMFDB `ec.galois_rep_elladic_image`, `gl2.level`): the
least positive integer `N` such that the image is the inverse image of its reduction modulo `N`,
its level `GeneralLinearGroup.padicLevel` as a subgroup of `GL₂(ℤ_ℓ)`, a power of `ℓ` when the image
is open. It is `0` when there is no such `N`, as when the image is not open. -/
noncomputable def tateModuleGaloisImageLevel : ℕ :=
  GeneralLinearGroup.padicLevel ℓ ⊤ (W.tateModuleGaloisImage ℓ b)

/-- The **index** of the `ℓ`-adic image (LMFDB `gl2.index`) in `GL₂(ℤ_ℓ)`. It is `0` when the index
is infinite. -/
noncomputable def tateModuleGaloisImageIndex : ℕ :=
  (W.tateModuleGaloisImage ℓ b).index

/-- **The level of the `ℓ`-adic image does not depend on the basis.** -/
lemma tateModuleGaloisImageLevel_eq :
    W.tateModuleGaloisImageLevel ℓ b' = W.tateModuleGaloisImageLevel ℓ b := by
  rcases W.exists_tateModuleGaloisImage_eq_map_conj ℓ b b' with ⟨P, hP⟩
  rw [tateModuleGaloisImageLevel, hP, GeneralLinearGroup.padicLevel_map_conj,
    tateModuleGaloisImageLevel]

/-- **The index of the `ℓ`-adic image does not depend on the basis.** -/
lemma tateModuleGaloisImageIndex_eq :
    W.tateModuleGaloisImageIndex ℓ b' = W.tateModuleGaloisImageIndex ℓ b := by
  rcases W.exists_tateModuleGaloisImage_eq_map_conj ℓ b b' with ⟨P, hP⟩
  rw [tateModuleGaloisImageIndex, hP, Subgroup.index_map_of_bijective (MulAut.conj P).bijective,
    tateModuleGaloisImageIndex]

variable (K) in
/-- The `ℓ`-adic image of `W` **is contained in** a subgroup `H` of `GL₂(ℤ_ℓ)` up to conjugacy
(LMFDB `ec.rouse_label` for `ℓ = 2`): in some basis of the Tate module `T_ℓ E` over `K`, the image
of the `ℓ`-adic Galois representation lies in `H`. These are the elliptic curves that the modular
curve `X_H` parametrises, in the description of the knowl. -/
def HasTateModuleGaloisImageIn (H : Subgroup (GL (Fin 2) ℤ_[ℓ])) : Prop :=
  ∃ c : Module.Basis (Fin 2) ℤ_[ℓ] (TateModule ℓ (W⁄K).toAffine.Point),
    W.tateModuleGaloisImage ℓ c ≤ H

end WeierstrassCurve
