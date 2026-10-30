import Mathlib.AlgebraicGeometry.Group.Affine
import TauCeti.AlgebraicGeometry.AbelianVariety.Basic
import TauCeti.AlgebraicGeometry.GroupScheme.Kernel
import TauCeti.Algebra.AlgebraicGroup.Torus.Basic

/-!
# Semiabelian varieties

A semiabelian variety over a field `K` (LMFDB `av.semiabelian_variety`) is a commutative group
variety `G` over `K` which is an extension of an abelian variety by a torus: there is an exact
sequence `1 → T → G → A → 1` of commutative group schemes with `A` an abelian variety and `T` a
torus. Group schemes over `K` are the group objects of `Over (Spec K)`, as for Tau Ceti's abelian
varieties (`TauCeti.AlgebraicGeometry.AbelianVariety`); a group variety is one that is of finite
type and geometrically integral over `K` (hence smooth, being a group scheme); the exactness is
that `G → A` is a faithfully flat homomorphism whose scheme-theoretic kernel (Tau Ceti's kernel in
`Grp (Over (Spec K))`, the fibre over the identity) is `T`. A torus is an affine group scheme
`Spec H` whose coordinate Hopf algebra `H` is a torus in Tau Ceti's sense
(`TauCeti.torusCommHopfAlgProperty`): of finite type, and a split torus `K̄[ℤⁿ]` over an algebraic
closure `K̄`; group schemes are compared with Hopf algebras through Mathlib's `Spec` functor
`AlgebraicGeometry.hopfSpec`.

Every abelian variety is a semiabelian variety, with the trivial torus (the split torus of rank
`0`) as kernel of the identity.

## Main definitions

* `TauCeti.AlgebraicGeometry.IsTorusGroupScheme`: a group scheme over `K` is a torus.
* `TauCeti.AlgebraicGeometry.SemiabelianVariety` (LMFDB `av.semiabelian_variety`): semiabelian
  varieties over `K`, with their presentation as extensions.
* `TauCeti.AlgebraicGeometry.AbelianVariety.toSemiabelianVariety`: an abelian variety as a
  semiabelian variety.

## Main results

* `TauCeti.AlgebraicGeometry.IsTorusGroupScheme.of_iso`: being a torus is invariant under
  isomorphism.
* `TauCeti.AlgebraicGeometry.isZero_hopfSpec_self`: the spectrum of the trivial Hopf algebra `K` is
  the trivial group scheme.
* `TauCeti.AlgebraicGeometry.isTorusGroupScheme_of_isZero`: the trivial group scheme is a torus.
* The instance `Smooth G.toGrp.X.hom`: a semiabelian variety is smooth over `K`, as a
  geometrically reduced group scheme locally of finite type over a field.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite CartesianMonoidalCategory

universe u

namespace TauCeti.AlgebraicGeometry

variable (K : Type u) [Field K] {T T' : Grp (Over (Spec (.of K)))}

variable (T) in
/-- A group scheme `T` over a field `K` is a **torus** (LMFDB `av.semiabelian_variety`) if it is
isomorphic to the spectrum `Spec H` of the coordinate Hopf algebra `H` of a torus, a finite type
commutative Hopf algebra over `K` which becomes the group algebra `K̄[ℤⁿ]` of a split torus over an
algebraic closure `K̄` (Tau Ceti's `torusCommHopfAlgProperty`), as group schemes over `K`. -/
def IsTorusGroupScheme : Prop :=
  ∃ H : FiniteTypeCommHopfAlgCat.{u, u} K, torusCommHopfAlgProperty K H ∧
    Nonempty (T ≅ (hopfSpec (.of K)).obj (op ((forget₂ _ (CommHopfAlgCat K)).obj H)))

variable {K} in
/-- **Being a torus is invariant under isomorphism of group schemes.** -/
lemma IsTorusGroupScheme.of_iso (e : T ≅ T') (hT : IsTorusGroupScheme K T) :
    IsTorusGroupScheme K T' :=
  hT.imp fun _ ↦ And.imp_right fun ⟨i⟩ ↦ ⟨e.symm ≪≫ i⟩

lemma isZero_grp_of_isIso_hom {S : Scheme.{u}} {G : Grp (Over S)} (h : IsIso G.X.hom) :
    IsZero G := by
  have hT : IsTerminal G.X := Over.mkIdTerminal.ofIso (Over.isoMk (asIso G.X.hom).symm (by simp))
  exact (Grp.isZero_trivial _).of_iso <| Grp.mkIso (hT.uniqueUpToIso isTerminalTensorUnit)
    (toUnit_unique ..) (toUnit_unique ..)

/-- **The spectrum of the trivial Hopf algebra `K` is the trivial group scheme** `Spec K` over `K`,
a zero object of the category of group schemes over `K`. -/
lemma isZero_hopfSpec_self : IsZero ((hopfSpec (.of K)).obj (op ((forget₂ _ (CommHopfAlgCat K)).obj
    (FiniteTypeCommHopfAlgCat.of K K)))) := by
  have h : IsIso (Spec.map (CommRingCat.ofHom (algebraMap K K))) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    exact IsIso.id _
  exact isZero_grp_of_isIso_hom h

variable {K} in
/-- **The trivial group scheme is a torus**, the split torus of rank `0`. -/
lemma isTorusGroupScheme_of_isZero (hT : IsZero T) : IsTorusGroupScheme K T :=
  ⟨FiniteTypeCommHopfAlgCat.of K K, (splitTorusCommHopfAlgProperty_trivial K).torus,
    ⟨hT.iso (isZero_hopfSpec_self K)⟩⟩

/-- A **semiabelian variety** (LMFDB `av.semiabelian_variety`) over a field `K`: a commutative group
variety `G` over `K`, i.e. a commutative group scheme over `Spec K` of finite type and
geometrically integral, together with its presentation as an extension `1 → T → G → A → 1` of an
abelian variety `A` by a torus `T`: a homomorphism `G → A` of group schemes that is flat and
surjective, hence faithfully flat, whose kernel `T` is a torus (`IsTorusGroupScheme`). -/
structure SemiabelianVariety where
  /-- The underlying group scheme `G` over `Spec K`. -/
  toGrp : Grp (Over (Spec (.of K)))
  isCommMonObj : IsCommMonObj toGrp.X
  locallyOfFiniteType : LocallyOfFiniteType toGrp.X.hom
  quasiCompact : QuasiCompact toGrp.X.hom
  geometricallyIntegral : GeometricallyIntegral toGrp.X.hom
  /-- The abelian variety `A` of which `G` is an extension by a torus. -/
  abelianVariety : AbelianVariety K
  /-- The homomorphism `G → A` of group schemes. -/
  toAbelianVariety : toGrp ⟶ Grp.mk abelianVariety.toOver
  flat : Flat toAbelianVariety.hom.hom.left
  surjective : Surjective toAbelianVariety.hom.hom.left
  isTorusGroupScheme_kernel : IsTorusGroupScheme K (kernel toAbelianVariety)

namespace SemiabelianVariety

attribute [instance] isCommMonObj locallyOfFiniteType quasiCompact geometricallyIntegral flat
  surjective

variable {K}

instance (G : SemiabelianVariety K) : Smooth G.toGrp.X.hom := by
  let i : GrpObj (Over.mk G.toGrp.X.hom) := inferInstanceAs (GrpObj G.toGrp.X)
  exact smooth_of_grpObj G.toGrp.X.hom

end SemiabelianVariety

namespace AbelianVariety

variable {K}

/-- An **abelian variety as a semiabelian variety** (LMFDB `av.semiabelian_variety`): the
extension of `A` by the trivial torus, through the identity of `A`, whose kernel is the trivial
group scheme. -/
noncomputable def toSemiabelianVariety (A : AbelianVariety K) : SemiabelianVariety K where
  toGrp := Grp.mk A.toOver
  isCommMonObj := A.isCommMonObj
  locallyOfFiniteType := inferInstanceAs (LocallyOfFiniteType A.toOver.hom)
  quasiCompact := inferInstanceAs (QuasiCompact A.toOver.hom)
  geometricallyIntegral := A.geometricallyIntegral
  abelianVariety := A
  toAbelianVariety := 𝟙 _
  flat := inferInstanceAs (Flat (𝟙 A.toScheme))
  surjective := inferInstanceAs (Surjective (𝟙 A.toScheme))
  isTorusGroupScheme_kernel := isTorusGroupScheme_of_isZero <| isZero_kernel_of_mono _

end AbelianVariety

end TauCeti.AlgebraicGeometry
