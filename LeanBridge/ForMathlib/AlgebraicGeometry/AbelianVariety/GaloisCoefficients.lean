import Mathlib.Algebra.Module.Torsion.Basic
import TauCeti.AlgebraicGeometry.AbelianVariety.Basic
import TauCeti.AlgebraicGeometry.Scheme.SpecOver
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
import TauCeti.Topology.Algebra.GroupAction.ForcedDiscrete
import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup

/-!
# The Galois modules of points of an abelian variety

Let `A` be an abelian variety over a field `K`, and `L` a field extension of `K`, with separable
closure `Lˢ`. The points `A(Lˢ)` of `A` over `Lˢ`, the morphisms `Spec Lˢ ⟶ A` over `Spec K`, form
a commutative group under the group law of `A`, on which the absolute Galois group
`G_L = Gal(Lˢ / L)` acts through its action on `Spec Lˢ`. With the discrete topology, this is a
discrete `G_L`-module: a point of `A(Lˢ)` is fixed by an open subgroup of `G_L`, as it is defined
over a finite extension of `L`, since `A` is locally of finite type over `K`. So is its `m`-torsion
`A(Lˢ)[m]`. These are the coefficient modules of the Galois cohomology of `A` over `K` and over the
extensions `L` of `K`, such as the completions of a number field `K`. A `K`-embedding `Kˢ → Lˢ`
gives maps `A(Kˢ) → A(Lˢ)` and `A(Kˢ)[m] → A(Lˢ)[m]`, equivariant along the corresponding map
`G_L → G_K`, which are the coefficient maps of the restriction from `K` to `L` in Galois cohomology.

## Main definitions

* `AlgHom.specOverHom`: the morphism `Spec Ω' ⟶ Spec Ω` over `Spec K` of a `K`-algebra
  homomorphism `Ω → Ω'`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.PointCoeff`: the discrete `G_L`-module `A(Lˢ)`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.TorsionCoeff`: the discrete `G_L`-module `A(Lˢ)[m]`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.torsionCoeffIncl`: the inclusion
  `A(Lˢ)[m] → A(Lˢ)`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.pointCoeffMap` and
  `TauCeti.AlgebraicGeometry.AbelianVariety.torsionCoeffMap`: the maps `A(Kˢ) → A(Lˢ)` and
  `A(Kˢ)[m] → A(Lˢ)[m]` along a `K`-embedding `Kˢ → Lˢ`.

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.PointCoeff.isOpen_stabilizer`: every point of `A(Lˢ)`
  has an open stabiliser in `G_L`, so that `A(Lˢ)` and `A(Lˢ)[m]` are discrete `G_L`-modules (the
  instances `ContinuousSMul (AbsoluteGaloisGroup L) (A.PointCoeff L)` and
  `ContinuousSMul (AbsoluteGaloisGroup L) (A.TorsionCoeff L m)`).
* `TauCeti.AlgebraicGeometry.AbelianVariety.pointCoeffMap_smul` and
  `TauCeti.AlgebraicGeometry.AbelianVariety.torsionCoeffMap_smul`: the maps `A(Kˢ) → A(Lˢ)` and
  `A(Kˢ)[m] → A(Lˢ)[m]` along an embedding `τ : Kˢ → Lˢ` are equivariant along `G_L → G_K`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.pointCoeffMap_comp` and
  `TauCeti.AlgebraicGeometry.AbelianVariety.torsionCoeffMap_comp`: precomposing `τ` with an element
  of `G_K` precomposes these maps with its action.
-/

open AddSubgroup CategoryTheory AlgebraicGeometry MonObj TopologicalSpace

universe u

namespace AlgHom

variable {K Ω Ω' Ω'' : Type u} [CommRing K] [CommRing Ω] [CommRing Ω'] [CommRing Ω''] [Algebra K Ω]
  [Algebra K Ω'] [Algebra K Ω''] (f : Ω →ₐ[K] Ω') (g : Ω' →ₐ[K] Ω'')

/-- The morphism `Spec Ω' ⟶ Spec Ω` over `Spec K` of a `K`-algebra homomorphism `f : Ω → Ω'`. -/
noncomputable def specOverHom : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω'))) ⟶
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) <| (Spec.map_comp _ _).symm.trans <|
    congrArg (fun φ : K →+* Ω' ↦ Spec.map (CommRingCat.ofHom φ)) f.comp_algebraMap

lemma specOverHom_id : (AlgHom.id K Ω).specOverHom = 𝟙 _ := by
  ext1
  exact (congrArg Spec.map CommRingCat.ofHom_id).trans (Spec.map_id _)

lemma specOverHom_comp : (g.comp f).specOverHom = g.specOverHom ≫ f.specOverHom := by
  ext1
  exact Spec.map_comp (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom)

end AlgHom

namespace TauCeti.AlgebraicGeometry.AbelianVariety

variable {K : Type u} [Field K] (A : AbelianVariety K) (L : Type u) [Field L] [Algebra K L]
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L) (m : ℕ) (g : AbsoluteGaloisGroup L)
  (σ : AbsoluteGaloisGroup K)

/-- The **points `A(Lˢ)`** of an abelian variety `A` over `K` over the separable closure `Lˢ` of a
field extension `L` of `K`: the morphisms `Spec Lˢ ⟶ A` over `Spec K`, a commutative group under the
group law of `A`, with the discrete topology. It is a discrete module over the absolute Galois group
`G_L = Gal(Lˢ / L)` (`TauCeti.AlgebraicGeometry.AbelianVariety.PointCoeff.isOpen_stabilizer`),
which acts through its action on `Spec Lˢ`. -/
def PointCoeff : Type u :=
  ForcedDiscrete (Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K
    (SeparableClosure L)))) ⟶ A.toOver))

noncomputable instance : AddCommGroup (A.PointCoeff L) :=
  inferInstanceAs (AddCommGroup (ForcedDiscrete _))

instance : TopologicalSpace (A.PointCoeff L) :=
  inferInstanceAs (TopologicalSpace (ForcedDiscrete _))

instance : DiscreteTopology (A.PointCoeff L) :=
  inferInstanceAs (DiscreteTopology (ForcedDiscrete _))

noncomputable instance : SMul (AbsoluteGaloisGroup L) (A.PointCoeff L) where
  smul g P := Additive.ofMul <|
    ((g : SeparableClosure L →ₐ[L] SeparableClosure L).restrictScalars K).specOverHom ≫
      Additive.toMul P

variable {A L} (P : A.PointCoeff L) (Q : A.PointCoeff K)

lemma PointCoeff.smul_def : g • P = Additive.ofMul
    (((g : SeparableClosure L →ₐ[L] SeparableClosure L).restrictScalars K).specOverHom ≫
      Additive.toMul P) :=
  rfl

noncomputable instance : DistribMulAction (AbsoluteGaloisGroup L) (A.PointCoeff L) where
  one_smul P := by
    rw [PointCoeff.smul_def]
    exact congrArg Additive.ofMul <| (congrArg (· ≫ Additive.toMul P) AlgHom.specOverHom_id).trans
      (Category.id_comp _)
  mul_smul g g' P := by
    rw [PointCoeff.smul_def, PointCoeff.smul_def, PointCoeff.smul_def]
    exact congrArg Additive.ofMul <| (congrArg (· ≫ Additive.toMul P)
      (((g' : SeparableClosure L →ₐ[L] SeparableClosure L).restrictScalars K).specOverHom_comp
        ((g : SeparableClosure L →ₐ[L] SeparableClosure L).restrictScalars K))).trans
        (Category.assoc _ _ _)
  smul_zero g := by
    rw [PointCoeff.smul_def]
    exact congrArg Additive.ofMul (comp_one _)
  smul_add g P P' := by
    rw [PointCoeff.smul_def, PointCoeff.smul_def, PointCoeff.smul_def]
    exact congrArg Additive.ofMul (comp_mul _ _ _)

/-- **Every point of `A(Lˢ)` has an open stabiliser in `G_L`**: it is defined over a finite
extension of `L`. A point `Spec Lˢ ⟶ A` lands in an affine open `Spec R` of `A`, where it is given
by a `K`-algebra homomorphism `φ : R → Lˢ`; as `A` is locally of finite type over `K`, the
`K`-algebra `R` is generated by finitely many elements, and the point is fixed by the open subgroup
of `G_L` fixing their images under `φ`. -/
lemma PointCoeff.isOpen_stabilizer :
    IsOpen (MulAction.stabilizer (AbsoluteGaloisGroup L) P : Set (AbsoluteGaloisGroup L)) := by
  let p : Spec (.of (SeparableClosure L)) ⟶ A.toScheme := (Additive.toMul P).left
  let _ : A.toScheme.Over (Spec (.of K)) := ⟨A.toOver.hom⟩
  have hp : p.IsOver (Spec (.of K)) := ⟨(Additive.toMul P).w⟩
  rcases exists_isAffineOpen_mem_and_subset (Opens.mem_top (p (IsLocalRing.closedPoint
    (SeparableClosure L)))) with ⟨U, hU, hxU, -⟩
  let ψ : CommRingCat.of K ⟶ Γ(A.toScheme, U) :=
    (Scheme.ΓSpecIso (.of K)).inv ≫ A.toOver.hom.appLE ⊤ U le_top
  let _ : Algebra K Γ(A.toScheme, U) := ψ.hom.toAlgebra
  have hf : hU.fromSpec.IsOver (Spec (.of K)) :=
    ⟨((isAffineOpen_top _).SpecMap_appLE_fromSpec A.toOver.hom hU le_top).symm.trans <| by
      rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
      exact (Spec.map_comp _ _).symm⟩
  have hrange : Set.range p ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro - ⟨y, rfl⟩
    rwa [Subsingleton.elim y (IsLocalRing.closedPoint (SeparableClosure L))]
  rcases exists_spec_map_comp_eq_of_range_subset (R := K) hU.fromSpec p hrange with ⟨φ, hφ⟩
  have hft : Algebra.FiniteType K Γ(A.toScheme, U) :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType A.toOver.hom inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp <| .of_surjective _
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective
  rcases hft.out with ⟨s, hs⟩
  have hle : (⨅ a ∈ s, MulAction.stabilizer (AbsoluteGaloisGroup L) (φ a)) ≤
      MulAction.stabilizer (AbsoluteGaloisGroup L) P := by
    intro g hg
    have hφg : ((g : SeparableClosure L →ₐ[L] SeparableClosure L).restrictScalars K).comp φ = φ :=
      AlgHom.ext_of_adjoin_eq_top hs fun a ha ↦ Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hg a) ha
    have h : CommRingCat.ofHom φ.toRingHom ≫
        CommRingCat.ofHom (g : SeparableClosure L →+* SeparableClosure L) =
          CommRingCat.ofHom φ.toRingHom :=
      congrArg (fun f : Γ(A.toScheme, U) →ₐ[K] SeparableClosure L ↦ CommRingCat.ofHom f.toRingHom)
        hφg
    rw [MulAction.mem_stabilizer_iff, PointCoeff.smul_def]
    refine congrArg Additive.ofMul ?_
    ext1
    exact (whisker_eq _ hφ.symm).trans <| (Spec.map_comp_assoc _ _ _).symm.trans <|
      (eq_whisker (congrArg Spec.map h) _).trans hφ
  refine Subgroup.isOpen_mono hle ?_
  simp only [Subgroup.coe_iInf]
  exact isOpen_biInter_finset fun a _ ↦ stabilizer_isOpen_of_isIntegral (φ a)

instance : ContinuousSMul (AbsoluteGaloisGroup L) (A.PointCoeff L) :=
  continuousSMul_iff_stabilizer_isOpen.mpr PointCoeff.isOpen_stabilizer

variable (A L) in
/-- The **`m`-torsion `A(Lˢ)[m]`** of the points `A(Lˢ)` of an abelian variety `A` over `K` over the
separable closure `Lˢ` of a field extension `L` of `K`
(`TauCeti.AlgebraicGeometry.AbelianVariety.PointCoeff`), a discrete module over the absolute Galois
group `G_L = Gal(Lˢ / L)`. -/
abbrev TorsionCoeff : Type u :=
  (A.PointCoeff L)[m]

variable {m} in
lemma PointCoeff.smul_mem_torsionBy (hP : P ∈ (A.PointCoeff L)[m]) :
    g • P ∈ (A.PointCoeff L)[m] := by
  rw [torsionBy.nsmul_iff] at hP ⊢
  rw [← smul_comm, hP, smul_zero]

noncomputable instance : DistribMulAction (AbsoluteGaloisGroup L) (A.TorsionCoeff L m) :=
  (A.PointCoeff L)[m].restrictDistribMulAction PointCoeff.smul_mem_torsionBy

variable {m} in
lemma coe_smul_torsionCoeff (x : A.TorsionCoeff L m) :
    ((g • x : A.TorsionCoeff L m) : A.PointCoeff L) = g • (x : A.PointCoeff L) :=
  rfl

instance : ContinuousSMul (AbsoluteGaloisGroup L) (A.TorsionCoeff L m) :=
  (A.PointCoeff L)[m].restrictDistribMulAction_continuousSMul PointCoeff.smul_mem_torsionBy

variable (A L) in
/-- The inclusion `A(Lˢ)[m] → A(Lˢ)`, a homomorphism of `G_L`-modules. -/
def torsionCoeffIncl : A.TorsionCoeff L m →+[AbsoluteGaloisGroup L] A.PointCoeff L where
  toFun := Subtype.val
  map_smul' := coe_smul_torsionCoeff
  map_zero' := rfl
  map_add' _ _ := rfl

variable (A) (y : A.TorsionCoeff K m)

/-- The map `A(Kˢ) → A(Lˢ)` along a `K`-embedding `τ : Kˢ → Lˢ` of separable closures: a point
`Spec Kˢ ⟶ A` is sent to its composite with `Spec τ : Spec Lˢ ⟶ Spec Kˢ`. -/
noncomputable def pointCoeffMap : A.PointCoeff K →+ A.PointCoeff L where
  toFun Q := Additive.ofMul (τ.specOverHom ≫ Additive.toMul Q)
  map_zero' := congrArg Additive.ofMul (comp_one _)
  map_add' _ _ := congrArg Additive.ofMul (comp_mul _ _ _)

lemma pointCoeffMap_apply :
    A.pointCoeffMap τ Q = Additive.ofMul (τ.specOverHom ≫ Additive.toMul Q) :=
  rfl

/-- The map `A(Kˢ) → A(Lˢ)` along `τ : Kˢ → Lˢ` is equivariant along the map `G_L → G_K` given by
`τ`. -/
lemma pointCoeffMap_smul :
    A.pointCoeffMap τ (absoluteGaloisGroupMap τ g • Q) = g • A.pointCoeffMap τ Q := by
  have h : τ.specOverHom ≫
      (absoluteGaloisGroupMap τ g : SeparableClosure K →ₐ[K] SeparableClosure K).specOverHom =
      ((g : SeparableClosure L →ₐ[L] SeparableClosure L).restrictScalars K).specOverHom ≫
      τ.specOverHom := by
    rw [← AlgHom.specOverHom_comp, ← AlgHom.specOverHom_comp]
    exact congrArg AlgHom.specOverHom (AlgHom.ext (absoluteGaloisGroupMap_commutes τ g))
  exact congrArg Additive.ofMul <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ Additive.toMul Q) h).trans (Category.assoc _ _ _)

/-- Precomposing the embedding `τ : Kˢ → Lˢ` with an element `σ` of `G_K` precomposes the map
`A(Kˢ) → A(Lˢ)` with the action of `σ`. -/
lemma pointCoeffMap_comp :
    A.pointCoeffMap (τ.comp (σ : SeparableClosure K →ₐ[K] SeparableClosure K)) Q =
      A.pointCoeffMap τ (σ • Q) := by
  rw [pointCoeffMap_apply, pointCoeffMap_apply, PointCoeff.smul_def, AlgHom.specOverHom_comp]
  exact congrArg Additive.ofMul (Category.assoc _ _ _)

/-- The map `A(Kˢ)[m] → A(Lˢ)[m]` along a `K`-embedding `τ : Kˢ → Lˢ` of separable closures, the
restriction of `TauCeti.AlgebraicGeometry.AbelianVariety.pointCoeffMap`. -/
noncomputable def torsionCoeffMap : A.TorsionCoeff K m →+ A.TorsionCoeff L m :=
  ((A.pointCoeffMap τ).comp (A.PointCoeff K)[m].subtype).codRestrict _ fun x ↦ by
    rw [torsionBy.nsmul_iff, AddMonoidHom.comp_apply, ← map_nsmul, AddSubgroup.coe_subtype,
      torsionBy.nsmul_iff.mp x.2, map_zero]

variable {m} in
lemma coe_torsionCoeffMap : (A.torsionCoeffMap τ m y : A.PointCoeff L) = A.pointCoeffMap τ y :=
  rfl

/-- The map `A(Kˢ)[m] → A(Lˢ)[m]` along `τ : Kˢ → Lˢ` is equivariant along the map `G_L → G_K`
given by `τ`. -/
lemma torsionCoeffMap_smul :
    A.torsionCoeffMap τ m (absoluteGaloisGroupMap τ g • y) = g • A.torsionCoeffMap τ m y :=
  Subtype.ext <| A.pointCoeffMap_smul τ g y

/-- Precomposing the embedding `τ : Kˢ → Lˢ` with an element `σ` of `G_K` precomposes the map
`A(Kˢ)[m] → A(Lˢ)[m]` with the action of `σ`. -/
lemma torsionCoeffMap_comp :
    A.torsionCoeffMap (τ.comp (σ : SeparableClosure K →ₐ[K] SeparableClosure K)) m y =
      A.torsionCoeffMap τ m (σ • y) :=
  Subtype.ext <| A.pointCoeffMap_comp τ σ y

end TauCeti.AlgebraicGeometry.AbelianVariety
