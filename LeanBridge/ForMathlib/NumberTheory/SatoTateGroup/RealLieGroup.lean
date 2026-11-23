import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.Embedding
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.LieGroup
import TauCeti.Geometry.Lie.AutomaticSmoothness
import TauCeti.Geometry.Manifold.Instances.Comap

/-!
# Sato–Tate groups as real Lie groups

A Sato–Tate group `G` of degree `d` (LMFDB `st_group.definition`) is a closed subgroup of the
unitary group `U(d)`, so its image `K` in `GL_d(ℂ)` is a closed subgroup of a Lie group, an
embedded Lie subgroup modelled on its Lie algebra by Cartan's closed-subgroup theorem (Tau Ceti's
`TauCeti.Lie.nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed`). The inclusion
`G → K` is a homeomorphism and a group isomorphism, so the charts of `K` pull back to `G`
(`IsLocalHomeomorph.chartedSpaceComap`, as Tau Ceti does for universal covers): this makes `G`
itself a real Lie group, modelled on the Lie algebra `SatoTateGroup.LieModel` of `G`, of dimension
the real dimension of `G` (LMFDB `st_group.real_dimension`). These are the instances
`ChartedSpace G.LieModel G.toSubgroup` and `LieGroup 𝓘(ℝ, G.LieModel) ∞ G.toSubgroup`.

A continuous homomorphism of Lie groups is smooth (Tau Ceti's
`TauCeti.Lie.contMDiff_of_continuous_monoidHom`), so an isomorphism of topological groups between
two Sato–Tate groups is an isomorphism of real Lie groups, a diffeomorphism
(`SatoTateGroup.diffeomorphOfContinuousMulEquiv`). In particular the Sato–Tate groups
`{(u, uζ, uζ²)}` and `{(u, u, uζ)}` of weight `1` and degree `6`, which have different
distributions of characteristic polynomials
(`SatoTateGroup.charpolyDistribution_regularCubeRoots_ne`), are isomorphic as real Lie groups
(`SatoTateGroup.regularCubeRootsDiffeomorph`, LMFDB `st_group.embedding`).

The Lie group `GL_d(ℂ)` is the group of units of the matrix algebra with the `L∞` operator norm,
whose topology is the entrywise topology of the matrices but not the same instance; it is selected
only to build the charts, as in `SatoTateGroup.isEmbeddedLieSubgroup`, and the instances above are
for the topology of `G` as a subspace of `U(d)`.

## Main definitions

* `SatoTateGroup.LieModel`: the Lie algebra of a Sato–Tate group, the model space of its charts.
* `SatoTateGroup.diffeomorphOfContinuousMulEquiv`: an isomorphism of topological groups between
  Sato–Tate groups, as a diffeomorphism of real Lie groups.
* `SatoTateGroup.regularCubeRootsDiffeomorph` (LMFDB `st_group.embedding`): the isomorphism of real
  Lie groups between the Sato–Tate groups `{(u, uζ, uζ²)}` and `{(u, u, uζ)}`.

## Main results

* The instance `LieGroup 𝓘(ℝ, G.LieModel) ∞ G.toSubgroup`: a Sato–Tate group is a real Lie group.
* `SatoTateGroup.finrank_lieModel` (LMFDB `st_group.real_dimension`): its dimension is the real
  dimension of `G`.
* `SatoTateGroup.coe_diffeomorphOfContinuousMulEquiv`: the diffeomorphism is the given group
  isomorphism.
* `SatoTateGroup.coe_regularCubeRootsDiffeomorph` (LMFDB `st_group.embedding`): the diffeomorphism
  between `{(u, uζ, uζ²)}` and `{(u, u, uζ)}` is the group isomorphism
  `SatoTateGroup.regularCubeRootsEquiv`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
-/

open TauCeti Lie

open scoped ContDiff Manifold

namespace SatoTateGroup

variable (G : SatoTateGroup)

open scoped Matrix.Norms.Operator in
attribute [local instance] Matrix.linftyOpTopologicalSpace in
/-- The **Lie algebra** of a Sato–Tate group `G` of degree `d`: Tau Ceti's
`TauCeti.Lie.lieSubalgebraOfSubgroup` of its image in `GL_d(ℂ)`, the left-invariant vector fields
whose one-parameter subgroups stay in `G`, as a real normed space. It is the model space of the
charts of `G`, of dimension the real dimension of `G` (`SatoTateGroup.finrank_lieModel`). -/
def LieModel : Type :=
  (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (Fin G.degree) (Fin G.degree) ℂ))
    (G.toSubgroup.map Unitary.toUnits)).toSubmodule

open scoped Matrix.Norms.Operator in
attribute [local instance] Matrix.linftyOpTopologicalSpace in
noncomputable instance : NormedAddCommGroup G.LieModel := by
  unfold LieModel
  infer_instance

open scoped Matrix.Norms.Operator in
attribute [local instance] Matrix.linftyOpTopologicalSpace in
noncomputable instance : NormedSpace ℝ G.LieModel := by
  unfold LieModel
  infer_instance

open scoped Matrix.Norms.Operator in
attribute [local instance] Matrix.linftyOpTopologicalSpace in
instance : FiniteDimensional ℝ G.LieModel := by
  have _ : T2Space (GL (Fin G.degree) ℂ) :=
    t2Space_of_lieGroup (I := 𝓘(ℝ, Matrix (Fin G.degree) (Fin G.degree) ℂ)) (n := ∞)
  have _ : FiniteDimensional ℝ (LeftInvariantDerivation 𝓘(ℝ, Matrix (Fin G.degree) (Fin G.degree) ℂ)
      (GL (Fin G.degree) ℂ)) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  unfold LieModel
  infer_instance

/-- **The dimension of a Sato–Tate group as a real Lie group is its real dimension** (LMFDB
`st_group.real_dimension`): the dimension of its Lie algebra, the model space of its charts. -/
lemma finrank_lieModel : Module.finrank ℝ G.LieModel = G.realDimension :=
  rfl

open scoped Matrix.Norms.Operator in
attribute [local instance] Matrix.linftyOpTopologicalSpace in
/-- The structure of embedded Lie subgroup of `GL_d(ℂ)` of the image of a Sato–Tate group `G` of
degree `d`, modelled on the Lie algebra of `G`, given by Cartan's closed-subgroup theorem. -/
noncomputable def embeddedLieSubgroupData :
    EmbeddedLieSubgroupData 𝓘(ℝ, Matrix (Fin G.degree) (Fin G.degree) ℂ)
      (G.toSubgroup.map Unitary.toUnits) G.LieModel :=
  Classical.choice (nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed
    G.isClosed_map_toUnits)

open scoped Matrix.Norms.Operator in
attribute [local instance] Matrix.linftyOpTopologicalSpace in
lemma isLocalHomeomorph_toUnits : IsLocalHomeomorph
    (G.toSubgroup.equivMapOfInjective Unitary.toUnits Unitary.toUnits_injective) := by
  have _ : ContinuousStar (Matrix (Fin G.degree) (Fin G.degree) ℂ) :=
    Matrix.linftyOpContinuousStar _ _
  have _ : CompactSpace G.toSubgroup := isCompact_iff_compactSpace.mp G.isClosed.isCompact
  let e : G.toSubgroup ≃* G.toSubgroup.map Unitary.toUnits :=
    G.toSubgroup.equivMapOfInjective Unitary.toUnits Unitary.toUnits_injective
  have he : Continuous e :=
    (Unitary.continuous_toUnits.comp continuous_subtype_val).subtype_mk _
  exact (he.homeoOfEquivCompactToT2 (f := e.toEquiv)).isLocalHomeomorph

open scoped Matrix.Norms.Operator in
attribute [local instance] Matrix.linftyOpTopologicalSpace in
/-- The charts of a Sato–Tate group `G`: those of its image in `GL_d(ℂ)`, an embedded Lie subgroup
(`SatoTateGroup.embeddedLieSubgroupData`), pulled back along the homeomorphism from `G`. -/
@[instance_reducible]
noncomputable def chartedSpaceAux : ChartedSpace G.LieModel G.toSubgroup :=
  letI : ChartedSpace G.LieModel (G.toSubgroup.map Unitary.toUnits) :=
    G.embeddedLieSubgroupData.chartedSpace
  G.isLocalHomeomorph_toUnits.chartedSpaceComap

open scoped Matrix.Norms.Operator in
attribute [local instance] Matrix.linftyOpTopologicalSpace in
lemma lieGroupAux :
    letI : ChartedSpace G.LieModel G.toSubgroup := G.chartedSpaceAux
    LieGroup 𝓘(ℝ, G.LieModel) ∞ G.toSubgroup := by
  have _ : ContinuousStar (Matrix (Fin G.degree) (Fin G.degree) ℂ) :=
    Matrix.linftyOpContinuousStar _ _
  let _ : ChartedSpace G.LieModel (G.toSubgroup.map Unitary.toUnits) :=
    G.embeddedLieSubgroupData.chartedSpace
  have _ : LieGroup 𝓘(ℝ, G.LieModel) ∞ (G.toSubgroup.map Unitary.toUnits) :=
    G.embeddedLieSubgroupData.lieGroup
  let e : G.toSubgroup ≃* G.toSubgroup.map Unitary.toUnits :=
    G.toSubgroup.equivMapOfInjective Unitary.toUnits Unitary.toUnits_injective
  have hp : IsLocalHomeomorph e := G.isLocalHomeomorph_toUnits
  let _ : ChartedSpace G.LieModel G.toSubgroup := hp.chartedSpaceComap
  have hsmooth : ContMDiff 𝓘(ℝ, G.LieModel) 𝓘(ℝ, G.LieModel) ∞ e := hp.contMDiff_chartedSpaceComap
  have _ : IsManifold 𝓘(ℝ, G.LieModel) ∞ G.toSubgroup := hp.isManifold_chartedSpaceComap
  have hmul : (e ∘ fun q : G.toSubgroup × G.toSubgroup ↦ q.1 * q.2) = fun q ↦ e q.1 * e q.2 :=
    funext fun q ↦ map_mul e q.1 q.2
  have hinv : (e ∘ fun a : G.toSubgroup ↦ a⁻¹) = fun a ↦ (e a)⁻¹ :=
    funext fun a ↦ map_inv e a
  refine
    { contMDiff_mul := hp.contMDiff_chartedSpaceComap_iff.2 ⟨continuous_mul, ?_⟩
      contMDiff_inv := hp.contMDiff_chartedSpaceComap_iff.2 ⟨continuous_inv, ?_⟩ }
  · rw [hmul]
    exact (hsmooth.comp contMDiff_fst).mul (hsmooth.comp contMDiff_snd)
  · rw [hinv]
    exact hsmooth.inv

noncomputable instance : ChartedSpace G.LieModel G.toSubgroup :=
  G.chartedSpaceAux

instance : LieGroup 𝓘(ℝ, G.LieModel) ∞ G.toSubgroup :=
  G.lieGroupAux

variable {G₁ G₂ : SatoTateGroup} (φ : G₁.toSubgroup ≃ₜ* G₂.toSubgroup)

/-- An isomorphism of topological groups between two Sato–Tate groups, as an **isomorphism of
real Lie groups**: a diffeomorphism, as a continuous homomorphism of Lie groups is smooth (Tau
Ceti's `TauCeti.Lie.contMDiff_of_continuous_monoidHom`). It is the group isomorphism `φ`
(`SatoTateGroup.coe_diffeomorphOfContinuousMulEquiv`). -/
noncomputable def diffeomorphOfContinuousMulEquiv :
    G₁.toSubgroup ≃ₘ^∞⟮𝓘(ℝ, G₁.LieModel), 𝓘(ℝ, G₂.LieModel)⟯ G₂.toSubgroup where
  toEquiv := φ.toEquiv
  contMDiff_toFun := contMDiff_of_continuous_monoidHom φ φ.continuous
  contMDiff_invFun := contMDiff_of_continuous_monoidHom φ.symm φ.symm.continuous

/-- **The diffeomorphism `SatoTateGroup.diffeomorphOfContinuousMulEquiv φ` is the group isomorphism
`φ`**, so it is an isomorphism of real Lie groups. -/
lemma coe_diffeomorphOfContinuousMulEquiv : ⇑(diffeomorphOfContinuousMulEquiv φ) = ⇑φ :=
  rfl

/-- The **isomorphism of real Lie groups** (LMFDB `st_group.embedding`) between the Sato–Tate
groups `{(u, uζ, uζ²)}` and `{(u, u, uζ)}` of weight `1` and degree `6`: the group isomorphism
`SatoTateGroup.regularCubeRootsEquiv`, `(x₀, x₁, x₂) ↦ (x₀, x₀, x₁)`, as a diffeomorphism. The
two groups have different distributions of characteristic polynomials
(`SatoTateGroup.charpolyDistribution_regularCubeRoots_ne`). -/
noncomputable def regularCubeRootsDiffeomorph :
    regularCubeRoots.toSubgroup ≃ₘ^∞⟮𝓘(ℝ, regularCubeRoots.LieModel),
      𝓘(ℝ, reflectionCubeRoots.LieModel)⟯ reflectionCubeRoots.toSubgroup :=
  diffeomorphOfContinuousMulEquiv regularCubeRootsEquiv

/-- **The Sato–Tate groups `{(u, uζ, uζ²)}` and `{(u, u, uζ)}` are isomorphic as real Lie groups**
(LMFDB `st_group.embedding`): the diffeomorphism `SatoTateGroup.regularCubeRootsDiffeomorph` is the
group isomorphism `SatoTateGroup.regularCubeRootsEquiv`. -/
lemma coe_regularCubeRootsDiffeomorph : ⇑regularCubeRootsDiffeomorph = ⇑regularCubeRootsEquiv :=
  rfl

end SatoTateGroup
