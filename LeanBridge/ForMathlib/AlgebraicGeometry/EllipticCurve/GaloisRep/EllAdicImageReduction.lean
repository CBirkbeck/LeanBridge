import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.EllAdicImage
import LeanBridge.ForMathlib.NumberTheory.ModularCurve.AdelicPreimage

/-!
# The `ℓ`-adic image and its reductions

The LMFDB identifies the image `H ≤ GL₂(ℤ_ℓ)` of the `ℓ`-adic Galois representation of an elliptic
curve, up to conjugacy, by the label (LMFDB `gl2.label`) of its projection to `GL₂(ℤ/ℓⁿℤ)`, where
`ℓⁿ` is the level of `H` (LMFDB `ec.galois_rep_elladic_image`). This rests on two facts, proved
here: an open `H` is the inverse image of its projection to `GL₂(ℤ/ℓⁿℤ)`, so the projection
determines `H`; and two subgroups that are the inverse images of their reductions modulo `ℓⁿ` are
conjugate as soon as their reductions are, invertible matrices modulo `ℓⁿ` lifting to `GL₂(ℤ_ℓ)`.
The projections in two bases of the Tate module are conjugate, so the conjugacy class of the
projection depends only on the curve. The label itself, whose last component is a numbering of the
subgroups of `GL₂(ℤ/ℓⁿℤ)` of given level, index and genus, is not formalised; its level and index
are `WeierstrassCurve.tateModuleGaloisImageLevel` and `WeierstrassCurve.tateModuleGaloisImageIndex`.
That the image is open when the curve has no complex multiplication (Serre's open image theorem),
and the description of the image for curves with complex multiplication, are not proved.

## Main definitions

* `WeierstrassCurve.tateModuleGaloisImageMod` (LMFDB `ec.galois_rep_elladic_image`): the reduction
  of the `ℓ`-adic image modulo `N`, a subgroup of `GL₂(ℤ/ℓ^{v_ℓ(N)}ℤ)`; for `N` the level, its
  projection to `GL₂(ℤ/ℓⁿℤ)`.

## Main results

* `Matrix.GeneralLinearGroup.exists_eq_map_conj_of_map_padicReduction_eq`: two subgroups of
  `GL_n(ℤ_ℓ)` that are the inverse images of their reductions modulo `N` are conjugate when their
  reductions are.
* `WeierstrassCurve.exists_tateModuleGaloisImageMod_eq_map_conj`: the reductions of the `ℓ`-adic
  images in two bases are conjugate.
* `WeierstrassCurve.comap_tateModuleGaloisImageMod_level`: an open `ℓ`-adic image is the inverse
  image of its projection to `GL₂(ℤ/ℓⁿℤ)`, `ℓⁿ` being its level.
* `WeierstrassCurve.index_tateModuleGaloisImageMod_level`: an open `ℓ`-adic image has the index of
  its projection to `GL₂(ℤ/ℓⁿℤ)`.
-/

open Matrix TauCeti

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] (ℓ : ℕ) [Fact ℓ.Prime] (N : ℕ)
  {H H' : Subgroup (GL n ℤ_[ℓ])}

variable (H) in
lemma map_padicReduction_map_conj (Q : GL n ℤ_[ℓ]) :
    (H.map (MulAut.conj Q).toMonoidHom).map (padicReduction ℓ N) =
      (H.map (padicReduction ℓ N)).map (MulAut.conj (padicReduction ℓ N Q)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun g ↦ ?_
  simp

/-- **Subgroups of `GL_n(ℤ_ℓ)` that are the inverse images of their reductions modulo `N` are
conjugate when their reductions are** (LMFDB `ec.galois_rep_elladic_image`): the conjugating matrix
modulo `N` lifts to `GL_n(ℤ_ℓ)`. -/
lemma exists_eq_map_conj_of_map_padicReduction_eq
    (hH : (H.map (padicReduction ℓ N)).comap (padicReduction ℓ N) = H)
    (hH' : (H'.map (padicReduction ℓ N)).comap (padicReduction ℓ N) = H')
    {P : GL n (ZMod (ℓ ^ N.factorization ℓ))} (hP : H'.map (padicReduction ℓ N) =
    (H.map (padicReduction ℓ N)).map (MulAut.conj P).toMonoidHom) :
    ∃ Q : GL n ℤ_[ℓ], H' = H.map (MulAut.conj Q).toMonoidHom := by
  rcases padicReduction_surjective N ℓ P with ⟨Q, rfl⟩
  refine ⟨Q, ?_⟩
  rw [← hH', hP, ← map_padicReduction_map_conj, Subgroup.comap_map_map_conj, hH]

end Matrix.GeneralLinearGroup

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K] (W : WeierstrassCurve F)
  (ℓ : ℕ) [Fact ℓ.Prime] (b b' : Module.Basis (Fin 2) ℤ_[ℓ] (TateModule ℓ (W⁄K).toAffine.Point))
  (N : ℕ)

/-- The **reduction modulo `N` of the `ℓ`-adic image** (LMFDB `ec.galois_rep_elladic_image`) of `W`
in the basis `b` of the Tate module: its image in `GL₂(ℤ_ℓ / N ℤ_ℓ) = GL₂(ℤ/ℓ^{v_ℓ(N)}ℤ)`, which is
the image of the mod-`ℓ^{v_ℓ(N)}` Galois representation. For `N = ℓⁿ` the level of the `ℓ`-adic
image (`tateModuleGaloisImageLevel`), it is the projection to `GL₂(ℤ/ℓⁿℤ)` by whose label (LMFDB
`gl2.label`) the LMFDB identifies the image: it determines the image when the image is open
(`comap_tateModuleGaloisImageMod_level`), and its conjugacy class determines the conjugacy class of
the image (`Matrix.GeneralLinearGroup.exists_eq_map_conj_of_map_padicReduction_eq`). -/
noncomputable def tateModuleGaloisImageMod : Subgroup (GL (Fin 2) (ZMod (ℓ ^ N.factorization ℓ))) :=
  (W.tateModuleGaloisImage ℓ b).map (GeneralLinearGroup.padicReduction ℓ N)

/-- The reductions modulo `N` of the `ℓ`-adic images in two bases are **conjugate**. -/
lemma exists_tateModuleGaloisImageMod_eq_map_conj : ∃ P : GL (Fin 2) (ZMod (ℓ ^ N.factorization ℓ)),
    W.tateModuleGaloisImageMod ℓ b' N =
      (W.tateModuleGaloisImageMod ℓ b N).map (MulAut.conj P).toMonoidHom := by
  rcases W.exists_tateModuleGaloisImage_eq_map_conj ℓ b b' with ⟨Q, hQ⟩
  exact ⟨GeneralLinearGroup.padicReduction ℓ N Q, by
    rw [tateModuleGaloisImageMod, hQ, GeneralLinearGroup.map_padicReduction_map_conj,
      tateModuleGaloisImageMod]⟩

/-- **An open `ℓ`-adic image is the inverse image of its projection to `GL₂(ℤ/ℓⁿℤ)`** (LMFDB
`ec.galois_rep_elladic_image`), where `ℓⁿ` is its level: the projection determines the image. -/
lemma comap_tateModuleGaloisImageMod_level
    (hH : IsOpen (W.tateModuleGaloisImage ℓ b : Set (GL (Fin 2) ℤ_[ℓ]))) :
    (W.tateModuleGaloisImageMod ℓ b (W.tateModuleGaloisImageLevel ℓ b)).comap
      (GeneralLinearGroup.padicReduction ℓ (W.tateModuleGaloisImageLevel ℓ b)) =
        W.tateModuleGaloisImage ℓ b :=
  (top_inf_eq _).symm.trans <| GeneralLinearGroup.inf_comap_map_padicReduction_padicLevel ℓ ⊤ le_top
    (hH.preimage continuous_subtype_val)

/-- **An open `ℓ`-adic image has the index of its projection to `GL₂(ℤ/ℓⁿℤ)`** (LMFDB
`ec.galois_rep_elladic_image`, `gl2.index`), where `ℓⁿ` is its level, reduction modulo `ℓⁿ` being
surjective: the index component of the label of the projection is the index of the image. -/
lemma index_tateModuleGaloisImageMod_level
    (hH : IsOpen (W.tateModuleGaloisImage ℓ b : Set (GL (Fin 2) ℤ_[ℓ]))) :
    (W.tateModuleGaloisImageMod ℓ b (W.tateModuleGaloisImageLevel ℓ b)).index =
      W.tateModuleGaloisImageIndex ℓ b := by
  rw [tateModuleGaloisImageIndex, ← W.comap_tateModuleGaloisImageMod_level ℓ b hH,
    Subgroup.index_comap_of_surjective _ (GeneralLinearGroup.padicReduction_surjective _ ℓ)]

end WeierstrassCurve
