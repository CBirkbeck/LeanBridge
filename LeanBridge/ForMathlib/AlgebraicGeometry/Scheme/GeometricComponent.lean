import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Hyperelliptic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Irreducible
import TauCeti.Topology.NoetherianSpace.ConnectedComponents

/-!
# Geometric components

A geometric component (LMFDB `ag.geom_component`) of a smooth scheme `X` of finite type over a field
`K` is an irreducible component of its base change `X_K̄ = X ×_K K̄` to an algebraic closure `K̄`
of `K` (`AlgebraicGeometry.Scheme.geometricBaseChangeScheme`, the scheme underlying LeanBridge's
`AlgebraicGeometry.Scheme.geometricBaseChange`).

A scheme `Y` smooth over a field has regular local rings, so a connected open subscheme of `Y` is
irreducible (Tau Ceti's `TauCeti.AlgebraicGeometry.Smooth.irreducibleSpace_of_connectedSpace`).
When `Y` is Noetherian its connected components are open, so they are irreducible, and they are
then exactly its irreducible components. As `X_K̄` is smooth and of finite type over `K̄`, hence
Noetherian, its irreducible components are its connected components, and they are finitely many.

An element `σ` of the absolute Galois group `Gal(K̄/K)` (Mathlib's `Field.absoluteGaloisGroup K`,
by definition `K̄ ≃ₐ[K] K̄`) acts on `X_K̄ = X ×_K K̄` through the second factor, by the
automorphism `id × Spec(σ)` of the fibre product. Pulling back irreducible components along these
homeomorphisms gives an action of `Gal(K̄/K)` on the set of geometric components.

## Main definitions

* `AlgebraicGeometry.Scheme.geometricBaseChangeScheme`: the base change `X_K̄` as a scheme.
* `AlgebraicGeometry.Scheme.geometricComponents` (LMFDB `ag.geom_component`): the geometric
  components of a scheme over a field.
* `AlgebraicGeometry.Scheme.geometricGaloisMap`: the automorphism `id × Spec(σ)` of `X_K̄`.
* `AlgebraicGeometry.Scheme.geometricGaloisHomeomorph`: the same automorphism, as a homeomorphism.
* `AlgebraicGeometry.Scheme.geometricGaloisPerm` (LMFDB `ag.geom_component`): the action of
  `Gal(K̄/K)` on the geometric components, also the instance
  `MulAction (K̄ ≃ₐ[K] K̄) (X.geometricComponents K)`.

## Main results

* `AlgebraicGeometry.Scheme.irreducibleComponents_eq_range_connectedComponent`: the irreducible
  components of a Noetherian scheme smooth over a field are its connected components.
* `AlgebraicGeometry.Scheme.geometricComponents_eq_range_connectedComponent` (LMFDB
  `ag.geom_component`): the geometric components of a smooth scheme of finite type over a field
  are the connected components of `X_K̄`.
* `AlgebraicGeometry.Scheme.finite_geometricComponents` (LMFDB `ag.geom_component`): there are
  finitely many geometric components.
-/

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable {K : Type u} [Field K] {Y : Scheme.{u}} [NoetherianSpace Y]

open TauCeti AlgebraicGeometry in
lemma isIrreducible_connectedComponent (f : Y ⟶ Spec (.of K)) [Smooth f] (y : Y) :
    IsIrreducible (connectedComponent y) := by
  let U : Y.Opens := ⟨connectedComponent y, isOpen_connectedComponent⟩
  have : ConnectedSpace U := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have : IrreducibleSpace U := Smooth.irreducibleSpace_of_connectedSpace (U.ι ≫ f)
  exact isIrreducible_iff_irreducibleSpace.mpr this

/-- **The irreducible components of a Noetherian scheme smooth over a field are its connected
components**: a connected component is open, and a connected open subscheme of a scheme smooth over
a field is irreducible. -/
lemma irreducibleComponents_eq_range_connectedComponent (f : Y ⟶ Spec (.of K)) [Smooth f] :
    irreducibleComponents Y = Set.range (connectedComponent : Y → Set Y) := by
  ext Z
  constructor
  · intro hZ
    rcases hZ.1.nonempty with ⟨y, hy⟩
    have h : Z ⊆ connectedComponent y :=
      hZ.1.isPreirreducible.isPreconnected.subset_connectedComponent hy
    exact ⟨y, (hZ.2 (isIrreducible_connectedComponent f y) h).antisymm h⟩
  · rintro ⟨y, rfl⟩
    exact ⟨isIrreducible_connectedComponent f y, fun t ht hle ↦
      ht.isPreirreducible.isPreconnected.subset_connectedComponent (hle mem_connectedComponent)⟩

variable (X : Scheme.{u}) [X.Over (Spec (.of K))]
  (σ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)

variable (K) in
/-- The base change `X_K̄ = X ×_K K̄` of a scheme `X` over a field `K` to the algebraic closure `K̄`
of `K`, as a scheme: the fibre product of `X ⟶ Spec K` and `Spec K̄ ⟶ Spec K`, the scheme
underlying LeanBridge's `AlgebraicGeometry.Scheme.geometricBaseChange`. -/
noncomputable abbrev geometricBaseChangeScheme : Scheme.{u} :=
  pullback (X ↘ Spec (.of K)) (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))

variable (y : X.geometricBaseChangeScheme K)

variable (K) in
/-- The **geometric components** (LMFDB `ag.geom_component`) of a scheme `X` over a field `K`: the
irreducible components of its base change `X_K̄` to an algebraic closure of `K`. -/
noncomputable def geometricComponents : Set (Set (X.geometricBaseChangeScheme K)) :=
  irreducibleComponents _

lemma spec_map_algebraMap_comp_id :
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫ 𝟙 (Spec (.of K)) =
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) := by
  rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact (σ.commutes x).symm

/-- The automorphism `id × Spec(σ)` of the base change `X_K̄ = X ×_K K̄` induced by an element `σ`
of the absolute Galois group `Gal(K̄/K)`, acting on the second factor. -/
noncomputable def geometricGaloisMap :
    X.geometricBaseChangeScheme K ⟶ X.geometricBaseChangeScheme K :=
  pullback.map (X ↘ Spec (.of K)) (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
    (X ↘ Spec (.of K)) (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (𝟙 X)
    (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K))) (𝟙 _)
    (by simp) (spec_map_algebraMap_comp_id σ)

lemma geometricGaloisMap_one : X.geometricGaloisMap (1 : AlgebraicClosure K ≃ₐ[K] _) = 𝟙 _ := by
  rw [geometricGaloisMap]
  convert pullback.map_id
  rw [← Spec.map_id]
  rfl

lemma geometricGaloisMap_comp :
    X.geometricGaloisMap σ ≫ X.geometricGaloisMap τ = X.geometricGaloisMap (σ * τ) := by
  rw [geometricGaloisMap, geometricGaloisMap, geometricGaloisMap, pullback.map_comp]
  congr 1
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

lemma geometricGaloisMap_apply_geometricGaloisMap :
    X.geometricGaloisMap τ (X.geometricGaloisMap σ y) = X.geometricGaloisMap (σ * τ) y := by
  rw [← geometricGaloisMap_comp]
  rfl

lemma geometricGaloisMap_one_apply : X.geometricGaloisMap 1 y = y := by
  rw [geometricGaloisMap_one]
  rfl

/-- The automorphism `id × Spec(σ)` of `X_K̄` induced by `σ ∈ Gal(K̄/K)`, as a homeomorphism, with
inverse that of `σ⁻¹`. -/
noncomputable def geometricGaloisHomeomorph :
    X.geometricBaseChangeScheme K ≃ₜ X.geometricBaseChangeScheme K where
  toFun := X.geometricGaloisMap σ
  invFun := X.geometricGaloisMap σ⁻¹
  left_inv y := by
    rw [geometricGaloisMap_apply_geometricGaloisMap, mul_inv_cancel, geometricGaloisMap_one_apply]
  right_inv y := by
    rw [geometricGaloisMap_apply_geometricGaloisMap, inv_mul_cancel, geometricGaloisMap_one_apply]
  continuous_toFun := (X.geometricGaloisMap σ).continuous
  continuous_invFun := (X.geometricGaloisMap σ⁻¹).continuous

lemma preimage_geometricGaloisMap_mem_geometricComponents {Z : Set (X.geometricBaseChangeScheme K)}
    (hZ : Z ∈ X.geometricComponents K) : X.geometricGaloisMap σ ⁻¹' Z ∈ X.geometricComponents K :=
  preimage_mem_irreducibleComponents hZ (X.geometricGaloisHomeomorph σ).isOpenEmbedding
    (hZ.1.nonempty.mono fun y hy ↦ ⟨hy, (X.geometricGaloisHomeomorph σ).surjective y⟩)

/-- The **action of the absolute Galois group `Gal(K̄/K)` on the geometric components** (LMFDB
`ag.geom_component`) of a scheme `X` over `K`: `σ` sends a component `Z` of `X_K̄` to its preimage
under the automorphism `id × Spec(σ)` of `X_K̄ = X ×_K K̄`, a homeomorphism. -/
noncomputable def geometricGaloisPerm :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* Equiv.Perm (X.geometricComponents K) where
  toFun σ :=
    { toFun Z := ⟨X.geometricGaloisMap σ ⁻¹' Z,
        X.preimage_geometricGaloisMap_mem_geometricComponents σ Z.2⟩
      invFun Z := ⟨X.geometricGaloisMap σ⁻¹ ⁻¹' Z,
        X.preimage_geometricGaloisMap_mem_geometricComponents σ⁻¹ Z.2⟩
      left_inv Z := Subtype.ext <| Set.ext fun y ↦ by
        rw [Set.mem_preimage, Set.mem_preimage, geometricGaloisMap_apply_geometricGaloisMap,
          inv_mul_cancel, geometricGaloisMap_one_apply]
      right_inv Z := Subtype.ext <| Set.ext fun y ↦ by
        rw [Set.mem_preimage, Set.mem_preimage, geometricGaloisMap_apply_geometricGaloisMap,
          mul_inv_cancel, geometricGaloisMap_one_apply] }
  map_one' := Equiv.ext fun Z ↦ Subtype.ext <| Set.ext fun y ↦ by
    simp [geometricGaloisMap_one_apply]
  map_mul' σ τ := Equiv.ext fun Z ↦ Subtype.ext <| Set.ext fun y ↦ by
    simp [geometricGaloisMap_apply_geometricGaloisMap]

noncomputable instance :
    MulAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (X.geometricComponents K) :=
  MulAction.compHom _ X.geometricGaloisPerm

variable [Smooth (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]

instance : NoetherianSpace (X.geometricBaseChangeScheme K) := by
  have : IsLocallyNoetherian (X.geometricBaseChangeScheme K) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (X ↘ Spec (.of K)) _)
  have : CompactSpace (X.geometricBaseChangeScheme K) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (X ↘ Spec (.of K)) _)
  have : IsNoetherian (X.geometricBaseChangeScheme K) := ⟨⟩
  infer_instance

/-- **The geometric components of a smooth scheme `X` of finite type over a field `K` are the
connected components of `X_K̄`** (LMFDB `ag.geom_component`): `X_K̄` is smooth over `K̄` and
Noetherian. -/
lemma geometricComponents_eq_range_connectedComponent :
    X.geometricComponents K = Set.range connectedComponent :=
  irreducibleComponents_eq_range_connectedComponent (pullback.snd (X ↘ Spec (.of K)) _)

/-- **A smooth scheme of finite type over a field has finitely many geometric components** (LMFDB
`ag.geom_component`): `X_K̄` is Noetherian. -/
lemma finite_geometricComponents : (X.geometricComponents K).Finite :=
  NoetherianSpace.finite_irreducibleComponents

end AlgebraicGeometry.Scheme
