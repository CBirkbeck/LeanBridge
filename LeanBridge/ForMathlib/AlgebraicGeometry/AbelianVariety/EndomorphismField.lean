import TauCeti.AlgebraicGeometry.AbelianVariety.End.BaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The endomorphism field and the endomorphism lattice of an abelian variety

Let `A` be an abelian variety over a field `K`. For field extensions `K ⊆ L ⊆ M`, the base change
`(A_L)_M` of `A_L` to `M` is canonically isomorphic to `A_M`, by the transitivity of pullbacks, so
base change from `L` to `M` gives the natural inclusion `End(A_L) ⊆ End(A_M)` of endomorphism
rings, compatible with the inclusions `End(A) ⊆ End(A_L)`. For a field `L` between `K` and an
algebraic closure `K̄` of `K`, the image of `End(A_L)` in `End(A_K̄)` is the ring of endomorphisms
of `A_K̄` defined over `L`.

The endomorphism field of `A` is the smallest field `L` between `K` and `K̄` with
`End(A_L) = End(A_K̄)`, over which all the endomorphisms of `A_K̄` are defined, and the endomorphism
lattice of `A` is the set of the rings `End(A_L)` for `L` between `K` and the endomorphism field,
ordered by inclusion.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.baseChangeFunctorCompIso` and
  `TauCeti.AlgebraicGeometry.AbelianVariety.baseChangeBaseChangeIso`: the natural isomorphism
  `(A_L)_M ≅ A_M`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.End.baseChangeTower`: the natural inclusion
  `End(A_L) → End(A_M)`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.endRange`: the image of `End(A_L)` in `End(A_K̄)`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.endomorphismField` (LMFDB `av.endomorphism_field`).
* `TauCeti.AlgebraicGeometry.AbelianVariety.endomorphismLattice` (LMFDB `g2c.jac_end_lattice`).

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.End.baseChangeTower_baseChange`: the natural inclusions
  `End(A) ⊆ End(A_L) ⊆ End(A_M)` compose to the natural inclusion `End(A) ⊆ End(A_M)`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.range_baseChange_le_endRange`: the endomorphisms of `A`
  are defined over every `L`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.endomorphismField_le`: the endomorphism field lies in
  every field `L` between `K` and `K̄` with `End(A_L) = End(A_K̄)`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.endomorphismField_eq_bot`: the endomorphism field is `K`
  if all the endomorphisms of `A_K̄` are defined over `K`.

That the endomorphism field is itself such a field and is a finite Galois extension of `K`, and that
the endomorphism lattice is a lattice, are not formalised: they rest on Galois descent for the
endomorphisms of `A_K̄`, which are defined over a finite separable extension of `K`.
-/

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K] (A : AbelianVariety K) (L M : Type u) [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

lemma baseChangeFunctor_comp_inducedFunctor : baseChangeFunctor L ⋙
    inducedFunctor (fun A : AbelianVariety L ↦ CommGrp.mk A.toOver) =
    inducedFunctor (fun A : AbelianVariety K ↦ CommGrp.mk A.toOver) ⋙
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp :=
  Functor.hext (fun B ↦ commGrpMk_baseChange_toOver B L) fun B C _ ↦ (conj_eqToHom_iff_heq _ _
    (commGrpMk_baseChange_toOver B L) (commGrpMk_baseChange_toOver C L)).mp rfl

/-- The natural isomorphism `(A_L)_M ≅ A_M` between the base change to `M` of the base change of an
abelian variety `A` over `K` to `L` and its base change to `M`, for a tower of fields
`K ⊆ L ⊆ M`: the transitivity of pullbacks (`CategoryTheory.Over.pullbackComp`), on the commutative
group schemes underlying the abelian varieties. -/
noncomputable def baseChangeFunctorCompIso :
    baseChangeFunctor L ⋙ baseChangeFunctor M ≅ (baseChangeFunctor M : AbelianVariety K ⥤ _) :=
  ((fullyFaithfulInducedFunctor _).whiskeringRight _).preimageIso <| Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (baseChangeFunctor_comp_inducedFunctor M)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (baseChangeFunctor_comp_inducedFunctor L)) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.mapCommGrpCompIso.symm ≪≫
      Functor.mapCommGrpNatIso (Over.pullbackComp _ _).symm ≪≫
      Functor.mapCommGrpNatIso (eqToIso (by
        congr 1
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]))) ≪≫
    eqToIso (baseChangeFunctor_comp_inducedFunctor M).symm

/-- The isomorphism `(A_L)_M ≅ A_M`, the component at `A` of
`TauCeti.AlgebraicGeometry.AbelianVariety.baseChangeFunctorCompIso`. -/
noncomputable def baseChangeBaseChangeIso : (A.baseChange L).baseChange M ≅ A.baseChange M :=
  (baseChangeFunctorCompIso L M).app A

variable {A} in
lemma baseChangeBaseChangeIso_hom_naturality {B : AbelianVariety K} (φ : A ⟶ B) :
    Hom.baseChange (Hom.baseChange φ L) M ≫ (B.baseChangeBaseChangeIso L M).hom =
      (A.baseChangeBaseChangeIso L M).hom ≫ Hom.baseChange φ M :=
  (baseChangeFunctorCompIso L M).hom.naturality φ

namespace End

/-- The **natural inclusion** `End(A_L) → End(A_M)` of endomorphism rings, for an abelian variety
`A` over `K` and a tower of fields `K ⊆ L ⊆ M`: base change from `L` to `M`, followed by the
identification of `(A_L)_M` with `A_M`
(`TauCeti.AlgebraicGeometry.AbelianVariety.baseChangeBaseChangeIso`). -/
noncomputable def baseChangeTower : End (A.baseChange L) →+* End (A.baseChange M) :=
  (congr (A.baseChangeBaseChangeIso L M)).toRingHom.comp (baseChange (A.baseChange L) M)

/-- The natural inclusions `End(A) ⊆ End(A_L) ⊆ End(A_M)` compose to the natural inclusion
`End(A) ⊆ End(A_M)`. -/
lemma baseChangeTower_baseChange (x : End A) :
    baseChangeTower A L M (baseChange A L x) = baseChange A M x := by
  ext1
  rw [baseChangeTower, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    toHom_congr, toHom_baseChange, toHom_baseChange, toHom_baseChange,
    baseChangeBaseChangeIso_hom_naturality, Iso.inv_hom_id_assoc]

end End

variable (F : IntermediateField K (AlgebraicClosure K))

/-- The **ring of endomorphisms of `A_K̄` defined over `F`**, for an abelian variety `A` over `K`,
an algebraic closure `K̄` of `K` and a field `F` between `K` and `K̄`: the image of the natural
inclusion `End(A_F) → End(A_K̄)` (`TauCeti.AlgebraicGeometry.AbelianVariety.End.baseChangeTower`).
It is isomorphic to `End(A_F)`, the natural inclusion being injective (not formalised here). -/
noncomputable def endRange : Subring (End (A.baseChange (AlgebraicClosure K))) :=
  (End.baseChangeTower A F (AlgebraicClosure K)).range

/-- The **endomorphism field** (LMFDB `av.endomorphism_field`) of an abelian variety `A` over a
field `K`: the smallest field `L` between `K` and an algebraic closure `K̄` of `K` such that
`End(A_L) = End(A_K̄)`, that is such that the natural inclusion `End(A_L) → End(A_K̄)` is onto
(`TauCeti.AlgebraicGeometry.AbelianVariety.endRange`). It is defined as the intersection of these
fields, which is the smallest of them: the endomorphisms of `A_K̄` are defined over a finite Galois
extension of `K` in `K̄`, and by Galois descent the fields `L` with `End(A_L) = End(A_K̄)` are those
that contain the smallest such extension (not formalised here). -/
noncomputable def endomorphismField : IntermediateField K (AlgebraicClosure K) :=
  sInf {L | A.endRange L = ⊤}

/-- The **endomorphism lattice** (LMFDB `g2c.jac_end_lattice`) of an abelian variety `A` over a
field `K`: the set of the rings `End(A_F)` (`TauCeti.AlgebraicGeometry.AbelianVariety.endRange`),
for the fields `F` between `K` and the endomorphism field `L` of `A`
(`TauCeti.AlgebraicGeometry.AbelianVariety.endomorphismField`), ordered by inclusion as subrings
of `End(A_L) = End(A_K̄)`, for an algebraic closure `K̄` of `K`. By Galois descent,
`End(A_F) = End(A_L)^{Gal(L / F)}`, so these rings form a lattice (not formalised here). The LMFDB
considers the Jacobians of genus `2` curves. -/
noncomputable def endomorphismLattice : Set (Subring (End (A.baseChange (AlgebraicClosure K)))) :=
  A.endRange '' Set.Iic A.endomorphismField

/-- The endomorphisms of `A` are defined over every field `F` between `K` and `K̄`: the image of
`End(A)` in `End(A_K̄)` lies in that of `End(A_F)`. -/
lemma range_baseChange_le_endRange : (End.baseChange A (AlgebraicClosure K)).range ≤ A.endRange F :=
  fun _ ⟨x, hx⟩ ↦ ⟨End.baseChange A F x, (End.baseChangeTower_baseChange A F _ x).trans hx⟩

variable {A F}

/-- The endomorphism field of `A` lies in every field `F` between `K` and `K̄` with
`End(A_F) = End(A_K̄)`. -/
lemma endomorphismField_le (hF : A.endRange F = ⊤) : A.endomorphismField ≤ F :=
  sInf_le hF

/-- If all the endomorphisms of `A_K̄` are defined over `K`, the endomorphism field of `A` is
`K`. -/
lemma endomorphismField_eq_bot (hA : (End.baseChange A (AlgebraicClosure K)).range = ⊤) :
    A.endomorphismField = ⊥ :=
  le_bot_iff.mp <| endomorphismField_le <| top_le_iff.mp <| hA ▸ A.range_baseChange_le_endRange ⊥

lemma endRange_mem_endomorphismLattice (hF : F ≤ A.endomorphismField) :
    A.endRange F ∈ A.endomorphismLattice :=
  Set.mem_image_of_mem _ hF

end TauCeti.AlgebraicGeometry.AbelianVariety
