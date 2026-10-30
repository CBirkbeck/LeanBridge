import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.ModEllImage
import LeanBridge.ForMathlib.NumberTheory.ModularCurve.AdelicPreimage
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ProjGenLinGroup

/-!
# The modular curve `X_{S₄}(ℓ)`

For an odd prime `ℓ`, the modular curve `X_{S₄}(ℓ)` is the modular curve `X_H` for `H ≤ GL₂(ℤ̂)` the
inverse image of the subgroup of `PGL₂(𝔽_ℓ)` isomorphic to `S₄`, which is unique up to conjugacy
(not formalised): `H` is the inverse image in `GL₂(ℤ̂)` of `H_ℓ ≤ GL₂(𝔽_ℓ)`, the inverse image of
that subgroup under `GL₂(𝔽_ℓ) → PGL₂(𝔽_ℓ)`. The subgroups `H_ℓ` of this form are those whose image
in `PGL₂(𝔽_ℓ)` is isomorphic to `S₄` and which contain the scalar matrices, in particular `-I`.

The knowl says that `X_{S₄}(ℓ)` parametrizes the elliptic curves whose mod-`ℓ` Galois representation
has projective image `S₄`, which is `WeierstrassCurve.HasModGaloisImageExceptionalType` for the type
`S4`. More precisely, as `-I ∈ H_ℓ`, the elliptic curves `E` over `F` that give non-cuspidal
`F`-points of `X_{S₄}(ℓ)` are those whose mod-`ℓ` image lies, in some basis of `E[ℓ]`, in such a
subgroup `H_ℓ`, that is, whose projective mod-`ℓ` image lies in a subgroup of `PGL₂(𝔽_ℓ)` isomorphic
to `S₄`, possibly a proper one; for the curves whose projective mod-`ℓ` image is isomorphic to `S₄`
it is that subgroup. The modular curve itself is not formalised.

## Main definitions

* `Matrix.GeneralLinearGroup.IsS4Preimage` (LMFDB `modcurve.xs4`): the inverse image in
  `GL₂(𝔽_ℓ)` of a subgroup of `PGL₂(𝔽_ℓ)` isomorphic to `S₄`.
* `Matrix.GeneralLinearGroup.IsAdelicS4` (LMFDB `modcurve.xs4`): its inverse image in `GL₂(ℤ̂)`,
  the group of `X_{S₄}(ℓ)`.
* `WeierstrassCurve.HasProjectiveModGaloisImageInS4` (LMFDB `modcurve.xs4`): the projective mod-`ℓ`
  image of an elliptic curve lies in a subgroup of `PGL₂(𝔽_ℓ)` isomorphic to `S₄`.

## Main results

* `Matrix.GeneralLinearGroup.isS4Preimage_iff`: the inverse images in `GL₂(𝔽_ℓ)` of the subgroups
  of `PGL₂(𝔽_ℓ)` isomorphic to `S₄` are the subgroups with projective image isomorphic to `S₄` that
  contain the scalar matrices.
* `Matrix.GeneralLinearGroup.IsS4Preimage.neg_one_mem`: they contain `-I`.
* `Matrix.GeneralLinearGroup.IsS4Preimage.twenty_four_mul_index` and
  `Matrix.GeneralLinearGroup.IsAdelicS4.twenty_four_mul_index`: they, and the group of
  `X_{S₄}(ℓ)` in `GL₂(ℤ̂)`, have index `(ℓ³ - ℓ) / 24`.
* `WeierstrassCurve.hasProjectiveModGaloisImageInS4_iff`: the projective mod-`ℓ` image of `E` lies
  in a subgroup isomorphic to `S₄` if and only if, in some basis, the mod-`ℓ` image of `E` lies in
  the inverse image of such a subgroup.
* `WeierstrassCurve.HasModGaloisImageExceptionalType.hasProjectiveModGaloisImageInS4`: a curve whose
  projective mod-`ℓ` image is isomorphic to `S₄` satisfies the latter condition.
-/

open Matrix GeneralLinearGroup

namespace Matrix.GeneralLinearGroup

variable {ℓ : ℕ} [Fact ℓ.Prime] {H : Subgroup (GL (Fin 2) (ZMod ℓ))}
  {G : Subgroup (∀ p : Nat.Primes, GL (Fin 2) ℤ_[p])}

variable (H) in
/-- A subgroup `H` of `GL₂(𝔽_ℓ)` is the **inverse image of a subgroup of `PGL₂(𝔽_ℓ)` isomorphic to
`S₄`** (LMFDB `modcurve.xs4`) under the projection `GL₂(𝔽_ℓ) → PGL₂(𝔽_ℓ)`. For an odd prime `ℓ` the
modular curve `X_{S₄}(ℓ)` is `X_G` for `G` the inverse image of such an `H` in `GL₂(ℤ̂)`
(`IsAdelicS4`); for `ℓ = 2`, `PGL₂(𝔽₂)` has order `6` and there is no such `H`. -/
def IsS4Preimage : Prop :=
  ∃ S : Subgroup (ProjGenLinGroup (Fin 2) (ZMod ℓ)), Nonempty (S ≃* Equiv.Perm (Fin 4)) ∧
    H = S.comap ProjGenLinGroup.mk

/-- **The inverse images of the subgroups of `PGL₂(𝔽_ℓ)` isomorphic to `S₄`** are the subgroups of
`GL₂(𝔽_ℓ)` with projective image isomorphic to `S₄` (exceptional type `S4`) that contain the scalar
matrices, the center of `GL₂(𝔽_ℓ)`. -/
lemma isS4Preimage_iff :
    IsS4Preimage H ↔ HasExceptionalType H .S4 ∧ Subgroup.center (GL (Fin 2) (ZMod ℓ)) ≤ H := by
  refine ⟨?_, fun ⟨hS, hc⟩ ↦ ⟨projectiveImage H, hS, ?_⟩⟩
  · rintro ⟨S, hS, rfl⟩
    refine ⟨?_, fun g hg ↦ Subgroup.mem_comap.mpr (ProjGenLinGroup.mk_eq_one.mpr hg ▸ one_mem S)⟩
    rwa [HasExceptionalType, projectiveImage,
      Subgroup.map_comap_eq_self_of_surjective ProjGenLinGroup.mk_surjective]
  · have hker : (ProjGenLinGroup.mk : GL (Fin 2) (ZMod ℓ) →* _).ker ≤ H := by
      rwa [ProjGenLinGroup.ker_mk]
    rw [projectiveImage, Subgroup.comap_map_eq_self hker]

/-- **The inverse image of a subgroup of `PGL₂(𝔽_ℓ)` contains `-I`**, a scalar matrix. -/
lemma IsS4Preimage.neg_one_mem (hH : IsS4Preimage H) : -1 ∈ H :=
  (isS4Preimage_iff.mp hH).2 <| Subgroup.mem_center_iff.mpr fun g ↦ (Commute.neg_one_right g).eq

/-- **The inverse image of a subgroup of `PGL₂(𝔽_ℓ)` isomorphic to `S₄` has index `(ℓ³ - ℓ) / 24`**
in `GL₂(𝔽_ℓ)`, as `PGL₂(𝔽_ℓ)` has `ℓ³ - ℓ` elements. -/
lemma IsS4Preimage.twenty_four_mul_index (hH : IsS4Preimage H) : 24 * H.index = ℓ ^ 3 - ℓ := by
  rcases hH with ⟨S, ⟨e⟩, rfl⟩
  have h : Nat.card S * S.index = Nat.card (ProjGenLinGroup (Fin 2) (ZMod ℓ)) := S.card_mul_index
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin, TauCeti.natCard_PGL_fin_two,
    ZMod.card] at h
  rwa [S.index_comap_of_surjective ProjGenLinGroup.mk_surjective]

variable (ℓ G) in
/-- A subgroup `G` of `GL₂(ℤ̂) = ∏_p GL₂(ℤ_p)` is **the group of `X_{S₄}(ℓ)`** (LMFDB
`modcurve.xs4`): the inverse image under reduction modulo `ℓ` of the inverse image in `GL₂(𝔽_ℓ)` of
a subgroup of `PGL₂(𝔽_ℓ)` isomorphic to `S₄`, so that `X_{S₄}(ℓ) = X_G` for an odd prime `ℓ`. -/
def IsAdelicS4 : Prop :=
  ∃ H : Subgroup (GL (Fin 2) (ZMod ℓ)), IsS4Preimage H ∧ G = adelicPreimage ℓ H

/-- **The group of `X_{S₄}(ℓ)` has index `(ℓ³ - ℓ) / 24`** in `GL₂(ℤ̂)`. -/
lemma IsAdelicS4.twenty_four_mul_index (hG : IsAdelicS4 ℓ G) : 24 * G.index = ℓ ^ 3 - ℓ := by
  rcases hG with ⟨H, hH, rfl⟩
  rw [index_adelicPreimage]
  exact hH.twenty_four_mul_index

end Matrix.GeneralLinearGroup

namespace WeierstrassCurve

variable {F : Type*} (K : Type*) [Field F] [Field K] [DecidableEq K] [Algebra F K]
  (W : WeierstrassCurve F) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The **projective mod-`ℓ` image of `W` lies in a subgroup of `PGL₂(𝔽_ℓ)` isomorphic to `S₄`**
(LMFDB `modcurve.xs4`): in a basis of `E[ℓ]`, the image in `PGL₂(𝔽_ℓ)` of the mod-`ℓ` image of `W`
is contained in such a subgroup. Equivalently, the mod-`ℓ` image lies, in some basis, in the
reduction modulo `ℓ` of the group of `X_{S₄}(ℓ)` (`hasProjectiveModGaloisImageInS4_iff`); for `K` a
separable closure of `F` and `ℓ` odd and invertible in `F`, these are the elliptic curves over `F`
giving non-cuspidal `F`-points of `X_{S₄}(ℓ)`. One basis suffices: another one conjugates the image,
and conjugation permutes the subgroups isomorphic to `S₄` (not formalised). -/
def HasProjectiveModGaloisImageInS4 : Prop :=
  ∃ (b : Module.Basis (Fin 2) (ZMod ℓ) (AddSubgroup.torsionBy (W⁄K).toAffine.Point (ℓ : ℤ)))
    (S : Subgroup (ProjGenLinGroup (Fin 2) (ZMod ℓ))), Nonempty (S ≃* Equiv.Perm (Fin 4)) ∧
    projectiveImage (W.modGaloisImageGL ℓ b) ≤ S

/-- **The projective mod-`ℓ` image of `W` lies in a subgroup isomorphic to `S₄` if and only if, in
some basis of `E[ℓ]`, the mod-`ℓ` image lies in the inverse image of such a subgroup**: that is, in
the reduction modulo `ℓ` of the group of `X_{S₄}(ℓ)`. -/
lemma hasProjectiveModGaloisImageInS4_iff : W.HasProjectiveModGaloisImageInS4 K ℓ ↔
    ∃ (b : Module.Basis (Fin 2) (ZMod ℓ) (AddSubgroup.torsionBy (W⁄K).toAffine.Point (ℓ : ℤ)))
    (H : Subgroup (GL (Fin 2) (ZMod ℓ))), IsS4Preimage H ∧ W.modGaloisImageGL ℓ b ≤ H :=
  ⟨fun ⟨b, S, hS, hle⟩ ↦ ⟨b, _, ⟨S, hS, rfl⟩, Subgroup.map_le_iff_le_comap.mp hle⟩,
    fun ⟨b, _, ⟨S, hS, rfl⟩, hle⟩ ↦ ⟨b, S, hS, Subgroup.map_le_iff_le_comap.mpr hle⟩⟩

/-- **A curve whose projective mod-`ℓ` image is isomorphic to `S₄` has projective mod-`ℓ` image in a
subgroup isomorphic to `S₄`**: its own projective image. -/
lemma HasModGaloisImageExceptionalType.hasProjectiveModGaloisImageInS4
    (h : W.HasModGaloisImageExceptionalType K ℓ .S4) : W.HasProjectiveModGaloisImageInS4 K ℓ :=
  h.imp fun _ hb ↦ ⟨_, hb, le_rfl⟩

end WeierstrassCurve
