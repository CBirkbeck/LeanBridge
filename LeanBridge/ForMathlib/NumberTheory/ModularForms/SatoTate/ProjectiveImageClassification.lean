import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.FiniteProjectiveSubgroup
import LeanBridge.ForMathlib.NumberTheory.ModularForms.SatoTate.ProjectiveImageType

/-!
# The type of the projective image of a newform of weight one

The projective image of a newform of weight one (LMFDB `cmf.projective_image`) is a finite subgroup
of `PGL₂(ℂ)`. By the classification of the finite subgroups of `PGL₂(ℂ)`
(`Matrix.ProjGenLinGroup.classification`) it is cyclic, dihedral, or isomorphic to `A₄`, `S₄` or
`A₅`, and it is not cyclic exactly when the Galois representation `ρ` is irreducible, which the
Deligne–Serre theorem asserts: an eigenvector of a lift of a generator of a cyclic projective image
spans a stable line, and conversely a stable line is a point of the projective line fixed by the
projective image, whose stabiliser is cyclic. So the projective image has exactly one of the four
types `D_n` (`n ≥ 2`), `A₄`, `S₄`, `A₅` of `HeckeRing.GL2.Newform.GaloisRep.ProjectiveImageType`
if and only if `ρ` is irreducible, and the type is then a function of `ρ`.

The structure `HeckeRing.GL2.Newform.GaloisRep` does not record that `ρ` is irreducible, which is
part of the Deligne–Serre theorem: it enters as the hypothesis `[ρ.toRepresentation.IsIrreducible]`,
as in `HeckeRing.GL2.Newform.GaloisRep.exists_isTypeOf_projectiveImage`. Nothing else is assumed.

## Main definitions

* `HeckeRing.GL2.Newform.GaloisRep.typeOfProjectiveImage` (LMFDB `cmf.projective_image`): the type
  of the projective image of an irreducible Galois representation of a weight-one newform.

## Main results

* `HeckeRing.GL2.Newform.GaloisRep.isCyclic_or_exists_isTypeOf`: a finite subgroup of `PGL₂(ℂ)` is
  cyclic or has a type.
* `HeckeRing.GL2.Newform.GaloisRep.isIrreducible_iff_not_isCyclic_projectiveImage`: a Galois
  representation of a weight-one newform is irreducible if and only if its projective image is not
  cyclic.
* `HeckeRing.GL2.Newform.GaloisRep.exists_isTypeOf_projectiveImage_iff`: the projective image has a
  type if and only if the Galois representation is irreducible.
* `HeckeRing.GL2.Newform.GaloisRep.isTypeOf_typeOfProjectiveImage`: the projective image has the
  type `typeOfProjectiveImage`, and no other type.
-/

open Matrix MulAction Projectivization

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace HeckeRing.GL2.Newform.GaloisRep

variable {N : ℕ} [NeZero N] {f : Newform N 1} (ρ : GaloisRep f) {t : ProjectiveImageType}
  {H : Subgroup (GL (Fin 2) ℂ ⧸ Subgroup.center (GL (Fin 2) ℂ))}

namespace ProjectiveImageType

lemma IsTypeOf.not_isCyclic (ht : t.IsTypeOf H) : ¬IsCyclic H := by
  intro hH
  cases t with
  | dihedral n =>
    rcases ht with ⟨hn, ⟨e⟩⟩
    exact DihedralGroup.not_isCyclic (by omega) (isCyclic_of_surjective e.toMonoidHom e.surjective)
  | tetrahedral =>
    rcases ht with ⟨e⟩
    have h : IsCyclic (alternatingGroup (Fin 4)) :=
      isCyclic_of_surjective e.toMonoidHom e.surjective
    simpa using alternatingGroup.isCyclic_iff_card_le_three.mp h
  | octahedral =>
    rcases ht with ⟨e⟩
    have : IsCyclic (Equiv.Perm (Fin 4)) := isCyclic_of_surjective e.toMonoidHom e.surjective
    simpa using alternatingGroup.isCyclic_iff_card_le_three.mp
      (inferInstance : IsCyclic (alternatingGroup (Fin 4)))
  | icosahedral =>
    rcases ht with ⟨e⟩
    have h : IsCyclic (alternatingGroup (Fin 5)) :=
      isCyclic_of_surjective e.toMonoidHom e.surjective
    simpa using alternatingGroup.isCyclic_iff_card_le_three.mp h

end ProjectiveImageType

variable (H) in
/-- **A finite subgroup of `PGL₂(ℂ)` is cyclic or has a type**: it is cyclic, isomorphic to the
dihedral group `D_n` of order `2n` for some `n ≥ 2`, or isomorphic to `A₄`, `S₄` or `A₅`
(`Matrix.ProjGenLinGroup.classification`). -/
lemma isCyclic_or_exists_isTypeOf [hH : Finite H] :
    IsCyclic H ∨ ∃ t : ProjectiveImageType, t.IsTypeOf H := by
  rcases @ProjGenLinGroup.classification H hH with h | ⟨n, hn, e⟩ | e | e | e
  · exact Or.inl h
  · exact Or.inr ⟨.dihedral n, hn, e⟩
  · exact Or.inr ⟨.tetrahedral, e⟩
  · exact Or.inr ⟨.octahedral, e⟩
  · exact Or.inr ⟨.icosahedral, e⟩

lemma isCyclic_projectiveImage_of_mulVec_eq_smul {v : Fin 2 → ℂ} (hv : v ≠ 0)
    (h : ∀ σ : Gal(AlgebraicClosure ℚ/ℚ), ∃ c : ℂ,
      (ρ.toMonoidHom σ : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = c • v) : IsCyclic ρ.projectiveImage := by
  let H : Subgroup PGL(Fin 2, ℂ) := ρ.projectiveImage
  have hH : Finite H := inferInstanceAs (Finite ρ.projectiveImage)
  have hcyc : IsCyclic (stabilizer H (Projectivization.mk ℂ v hv)) :=
    ProjGenLinGroup.isCyclic_stabilizer H _
  have hfix : ∀ k : H, k • Projectivization.mk ℂ v hv = Projectivization.mk ℂ v hv := by
    rintro ⟨_, σ, rfl⟩
    rcases h σ with ⟨c, hc⟩
    have hσ : ProjGenLinGroup.mk (ρ.toMonoidHom σ) • Projectivization.mk ℂ v hv =
        Projectivization.mk ℂ v hv := by
      rw [PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff']
      exact ⟨c, hc.symm⟩
    exact hσ
  exact isCyclic_of_surjective (stabilizer H (Projectivization.mk ℂ v hv)).subtype fun k ↦
    ⟨⟨k, hfix k⟩, rfl⟩

lemma isIrreducible_of_not_isCyclic (h : ¬IsCyclic ρ.projectiveImage) :
    ρ.toRepresentation.IsIrreducible := by
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h' ↦ ?_⟩, eq_bot_or_eq_top := fun W ↦ ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h' : (⊥ : Submodule ℂ (Fin 2 → ℂ)) = ⊤)
  · by_cases hW : W.toSubmodule = ⊥
    · exact Or.inl (Subrepresentation.toSubmodule_injective hW)
    by_cases hW' : W.toSubmodule = ⊤
    · exact Or.inr (Subrepresentation.toSubmodule_injective hW')
    rcases Submodule.exists_mem_ne_zero_of_ne_bot hW with ⟨v, hvW, hv⟩
    have h1 : Module.finrank ℂ W.toSubmodule = 1 := by
      have hlt : Module.finrank ℂ W.toSubmodule < 2 :=
        (Submodule.finrank_lt hW').trans_eq (Module.finrank_fin_fun ℂ)
      have hne : Module.finrank ℂ W.toSubmodule ≠ 0 := Submodule.finrank_eq_zero.not.mpr hW
      omega
    refine (h (ρ.isCyclic_projectiveImage_of_mulVec_eq_smul hv fun σ ↦ ?_)).elim
    rcases (finrank_eq_one_iff_of_nonzero' (⟨v, hvW⟩ : W.toSubmodule) fun h0 ↦ hv
      (congrArg Subtype.val h0)).mp h1 ⟨ρ.toRepresentation σ v, W.apply_mem_toSubmodule σ hvW⟩ with
      ⟨c, hc⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩

/-- **A Galois representation of a weight-one newform is irreducible if and only if its projective
image is not cyclic**: an eigenvector of a lift of a generator of a cyclic projective image spans a
stable line, and a stable line is a point of the projective line fixed by the projective image,
which then lies in a point stabiliser, a cyclic group. -/
lemma isIrreducible_iff_not_isCyclic_projectiveImage :
    ρ.toRepresentation.IsIrreducible ↔ ¬IsCyclic ρ.projectiveImage :=
  ⟨fun _ ↦ ρ.not_isCyclic_projectiveImage, ρ.isIrreducible_of_not_isCyclic⟩

/-- **The projective image of a Galois representation of a weight-one newform has a type if and only
if the representation is irreducible**: a group with a type is not cyclic, and a finite subgroup of
`PGL₂(ℂ)` that is not cyclic has a type. -/
lemma exists_isTypeOf_projectiveImage_iff :
    (∃ t : ProjectiveImageType, t.IsTypeOf ρ.projectiveImage) ↔ ρ.toRepresentation.IsIrreducible :=
  ⟨fun ⟨_, ht⟩ ↦ ρ.isIrreducible_of_not_isCyclic ht.not_isCyclic, fun _ ↦
    (isCyclic_or_exists_isTypeOf ρ.projectiveImage).resolve_left ρ.not_isCyclic_projectiveImage⟩

variable [ρ.toRepresentation.IsIrreducible]

/-- The **type** of the projective image of a weight-one newform (LMFDB `cmf.projective_image`),
for an irreducible Galois representation `ρ`, as the Deligne–Serre representation is: the type `t`
such that the projective image is isomorphic to the dihedral group `D_n` of order `2n` for some
`n ≥ 2` (with `D₂ = C₂ × C₂`), to `A₄`, to `S₄` or to `A₅`, as `t` says. It exists by the
classification of the finite subgroups of `PGL₂(ℂ)` and is unique
(`ProjectiveImageType.IsTypeOf.eq`). -/
noncomputable def typeOfProjectiveImage : ProjectiveImageType :=
  ρ.projectiveImageType <| ρ.exists_isTypeOf_projectiveImage_iff.mpr inferInstance

/-- **The projective image has the type `typeOfProjectiveImage`.** -/
lemma isTypeOf_typeOfProjectiveImage : ρ.typeOfProjectiveImage.IsTypeOf ρ.projectiveImage :=
  ρ.isTypeOf_projectiveImageType _

lemma typeOfProjectiveImage_eq (ht : t.IsTypeOf ρ.projectiveImage) : ρ.typeOfProjectiveImage = t :=
  ρ.projectiveImageType_eq _ ht

end HeckeRing.GL2.Newform.GaloisRep
