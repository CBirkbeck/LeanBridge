import LeanBridge.ForMathlib.NumberTheory.ModEllGaloisRep.Determinant
import LeanBridge.ForMathlib.NumberTheory.ModEllGaloisRep.GeneralLinearPoints
import LeanBridge.ForMathlib.NumberTheory.ModEllGaloisRep.ProjectiveRepresentation

/-!
# Mod-`ℓ` Galois representations into an algebraic group with an embedding into `GL_n`

A mod-`ℓ` Galois representation `ρ : Gal(K̄/K) → G(𝔽_ℓ)` takes values in the `𝔽_ℓ`-points of an
algebraic group `G` over `𝔽_ℓ` (LMFDB `modlgal`, `MonoidHom.IsModEllGaloisRepIn`). The determinant
character, the surjectivity of the determinant, the determinant index, the Frobenius trace,
determinant and characteristic polynomial, and the projective representation of the LMFDB use the
determinant, trace, characteristic polynomial and scalars of `G(𝔽_ℓ)`, which exist through an
embedding `ι : G ⟶ GL_n` over `𝔽_ℓ`, a morphism of group schemes that is a closed immersion: the
knowls presuppose that `G` comes with such an embedding, through which these notions are defined.
On `𝔽_ℓ`-points, `ι` induces a homomorphism `G(𝔽_ℓ) → GL_n(𝔽_ℓ)`
(`AlgebraicGeometry.rationalPointsToGL`), injective for an embedding, and `ρ` gives the
representation `ι ∘ ρ : Gal(K̄/K) → GL_n(𝔽_ℓ)` (`MonoidHom.mapGL`), a mod-`ℓ` Galois representation
into `GL_n(𝔽_ℓ)`. Each notion is defined for every morphism `ι`, and the statements of the knowls
hold for every `G` with an embedding:

* the determinant character of `ρ` is that of `ι ∘ ρ`; it is a `1`-dimensional mod-`ℓ` Galois
  representation, with values in the `𝔽_ℓ`-points of the algebraic group `GL_1`, and when `ρ` has
  dimension `1` it is `ρ` itself, followed by `ι` on `𝔽_ℓ`-points;
* the determinant index of `ρ` is the index in `𝔽_ℓˣ` of `det(ρ(Gal(K̄/K)))`, the determinant
  `G(𝔽_ℓ) → 𝔽_ℓˣ` being that of `ι`, and it is `1` exactly when the determinant of `ρ` is
  surjective, that is, when the image of its determinant map is `GL_1(𝔽_ℓ)`;
* at a prime `𝔭` at which `ρ` is unramified, the characteristic polynomial, the trace and the
  determinant of `ρ(Frob_𝔭)` are those of `ι(A)` for any `A` in the conjugacy class `ρ(Frob_𝔭)` of
  `G(𝔽_ℓ)` (`MonoidHom.frobeniusConjClass`). For an embedding, `ρ` and `ι ∘ ρ` have the same
  splitting field, `ι` carries the Frobenius class of `ρ` onto the class of the Frobenius matrices
  of `ι ∘ ρ`, and these invariants are those of the Frobenius matrices; the Frobenius determinant is
  the value of the determinant character at a Frobenius element;
* the projective representation takes values in the quotient of `G(𝔽_ℓ)` by its scalars, the
  points that `ι` maps to scalar matrices (`AlgebraicGeometry.scalarPoints`). They form the group
  `𝔽_ℓˣ` when `ι` is an embedding and `G` contains the scalars of `GL_n`: this hypothesis gives the
  quotient `G(𝔽_ℓ)/𝔽_ℓ^*` of the LMFDB, which the definition extends to every `G`. The quotient
  embeds into `PGL_n(𝔽_ℓ)`, carrying the projective representation of `ρ` to that of `ι ∘ ρ`, and
  for `ℓ = 2` it is `G(𝔽₂)`, carrying the projective representation of `ρ` to `ρ`.

The examples are `GL_n` itself, with the identity, for which these are the notions of
`GL_n(𝔽_ℓ)`; Tau Ceti's special linear group scheme `SL_n`, a proper closed subgroup whose
determinant characters are trivial, so that its determinant index is `ℓ - 1`; and Tau Ceti's
diagonal split torus of `GL_n`, a proper closed subgroup that contains the scalars. The trivial
representation into the `𝔽_ℓ`-points of any algebraic group is a mod-`ℓ` Galois representation.

## Main definitions

* `AlgebraicGeometry.scalarPoints`: the scalars of `G(R)` for a morphism `ι : G ⟶ GL_n`.
* `AlgebraicGeometry.scalarPointsMulEquivUnits`: they form the group `Rˣ` when `ι` is an embedding
  and `G` contains the scalars.
* `AlgebraicGeometry.projectivePointsToPGL`: the embedding of `G(R)` modulo its scalars into
  `PGL_n(R)`.
* `AlgebraicGeometry.quotientScalarPointsMulEquiv`: over a ring with only one unit, such as `𝔽₂`,
  `G(R)` modulo its scalars is `G(R)` for an embedding.
* `MonoidHom.mapGL`: the representation `ι ∘ ρ : Gal(K̄/K) → GL_n(𝔽_ℓ)`.
* `MonoidHom.IsDetSurjective` (LMFDB `modlgal.det_surjective`): the determinant is surjective.
* `MonoidHom.detIndex` (LMFDB `modlgal.determinant_index`): the determinant index.
* `MonoidHom.frobeniusCharpolyIn` (LMFDB `modlgal.frobenius_charpoly`): the characteristic
  polynomial of Frobenius.
* `MonoidHom.frobeniusTraceIn` (LMFDB `modlgal.frobenius_trace`): the Frobenius trace.
* `MonoidHom.frobeniusDetIn` (LMFDB `modlgal.frobenius_determinant`): the Frobenius determinant.
* `MonoidHom.projectiveRepresentationIn` (LMFDB `modlgal.projective_representation`): the
  projective representation.

## Main results

* `AlgebraicGeometry.projectivePointsToPGL_injective`: `G(R)` modulo its scalars embeds into
  `PGL_n(R)`.
* `MonoidHom.IsModEllGaloisRepIn.isModEllGaloisRep_mapGL`: through `ι`, a mod-`ℓ` Galois
  representation into `G(𝔽_ℓ)` gives one into `GL_n(𝔽_ℓ)`.
* `MonoidHom.IsModEllGaloisRep.isModEllGaloisRepIn`: a mod-`ℓ` Galois representation into
  `GL_n(𝔽_ℓ)` is one into the `𝔽_ℓ`-points of the algebraic group `GL_n`.
* `MonoidHom.mapGL_id`: for `GL_n` with the identity, `ι ∘ ρ` is the representation into
  `GL_n(𝔽_ℓ)`.
* `MonoidHom.IsModEllGaloisRepIn.isModEllGaloisRepIn_detCharacterGL` (LMFDB `modlgal.determinant`):
  the determinant character is a `1`-dimensional mod-`ℓ` Galois representation.
* `MonoidHom.symm_comp_detCharacterGL_mapGL` (LMFDB `modlgal.determinant`): the determinant
  character of a `1`-dimensional representation is the representation itself.
* `MonoidHom.isDetSurjective_iff` (LMFDB `modlgal.det_surjective`): the determinant is surjective
  exactly when the determinant character is.
* `MonoidHom.isDetSurjective_iff_detIndex_eq_one`: the determinant is surjective exactly when the
  determinant index is `1`.
* `MonoidHom.detIndex_mapGL` (LMFDB `modlgal.determinant_index`): the determinant index of `ρ` is
  the index of `det(ρ(Gal(K̄/K)))` in `𝔽_ℓˣ`.
* `MonoidHom.frobeniusCharpolyIn_eq`, `MonoidHom.frobeniusTraceIn_eq` and
  `MonoidHom.frobeniusDetIn_eq`: the Frobenius invariants are those of `ι(A)` for any `A` in the
  Frobenius class of `ρ`.
* `MonoidHom.frobeniusDetIn_eq_detCharacter` (LMFDB `modlgal.frobenius_determinant`): the Frobenius
  determinant is the value of the determinant character at a Frobenius element.
* `MonoidHom.splittingField_mapGL`: for an embedding, `ρ` and `ι ∘ ρ` have the same splitting field.
* `MonoidHom.frobeniusClass_mapGL`: for an embedding, `ι` carries the Frobenius class of `ρ` onto
  the class of the Frobenius matrices of `ι ∘ ρ`.
* `MonoidHom.frobeniusCharpolyIn_eq_frobeniusCharpoly`,
  `MonoidHom.frobeniusTraceIn_eq_frobeniusTrace` and `MonoidHom.frobeniusDetIn_eq_frobeniusDet`:
  for an embedding, the Frobenius invariants of `ρ` are those of `ι ∘ ρ`.
* `MonoidHom.projectivePointsToPGL_comp_projectiveRepresentationIn`: the projective representation
  of `ρ` is carried to that of `ι ∘ ρ`.
* `MonoidHom.quotientScalarPointsMulEquiv_comp_projectiveRepresentationIn_two`
  (LMFDB `modlgal.projective_representation`): for `ℓ = 2` the projective representation is the
  representation itself.
* `MonoidHom.isModEllGaloisRepIn_one_of_locallyOfFiniteType`: the trivial representation into the
  `𝔽_ℓ`-points of an algebraic group is a mod-`ℓ` Galois representation.
* `MonoidHom.detCharacter_mapGL_specialLinear` and `MonoidHom.detIndex_mapGL_specialLinear`: the
  determinant character of a representation into `SL_n(𝔽_ℓ)` is trivial, and its determinant index
  is `ℓ - 1`.
-/

open CategoryTheory AlgebraicGeometry Matrix GeneralLinearGroup NumberField TauCeti

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {n : ℕ} {G : Grp (Over (Spec (.of R)))}
  (ι : G ⟶ GeneralLinear.groupScheme R n)

/-- The subgroup of **scalars** of the group `G(R)` of `R`-points of a group scheme `G` over `R`,
for a morphism `ι : G ⟶ GL_n`: the points that `ι` maps to scalar matrices, the centre of
`GL_n(R)` (Mathlib's `Matrix.GeneralLinearGroup.center_eq_range_scalar`). It is a normal subgroup,
the group `Rˣ` when `ι` is an embedding and `G` contains the scalars
(`AlgebraicGeometry.scalarPointsMulEquivUnits`). -/
noncomputable def scalarPoints : Subgroup (rationalPoints G) :=
  (Subgroup.center (GL (Fin n) R)).comap (rationalPointsToGL ι)

instance : (scalarPoints ι).Normal :=
  Subgroup.normal_comap _

/-- The homomorphism from `G(R)` modulo its scalars to `PGL_n(R)` induced by `ι : G ⟶ GL_n`, an
embedding (`AlgebraicGeometry.projectivePointsToPGL_injective`). -/
noncomputable def projectivePointsToPGL :
    rationalPoints G ⧸ scalarPoints ι →* ProjGenLinGroup (Fin n) R :=
  QuotientGroup.map _ _ (rationalPointsToGL ι) le_rfl

/-- **`G(R)` modulo its scalars embeds into `PGL_n(R)`**: the scalars of `G(R)` are exactly the
points that `ι` maps into the centre of `GL_n(R)`. -/
lemma projectivePointsToPGL_injective : Function.Injective (projectivePointsToPGL ι) :=
  (MonoidHom.ker_eq_bot_iff _).mp <| (QuotientGroup.ker_map _ _ _ _).trans <|
    QuotientGroup.map_mk'_self _

variable {ι}

/-- **The scalars of `G(R)` form the group `Rˣ` when `G` contains the scalars**: if `ι` is injective
on `R`-points, as an embedding is (`AlgebraicGeometry.rationalPointsToGL_injective`), and every
scalar matrix of `GL_n(R)`, `n ≥ 1`, is the image of an `R`-point of `G`, then the scalars of `G(R)`
are isomorphic to `Rˣ`, through `ι` and the scalar matrices. Both hypotheses hold for `GL_n` with
the identity (`AlgebraicGeometry.range_rationalPointsToGL_id`) and for the diagonal torus of `GL_n`
(`AlgebraicGeometry.center_le_range_rationalPointsToGL_diagonalTorus`). -/
noncomputable def scalarPointsMulEquivUnits [NeZero n]
    (hι : Function.Injective (rationalPointsToGL ι))
    (hG : Subgroup.center (GL (Fin n) R) ≤ (rationalPointsToGL ι).range) : scalarPoints ι ≃* Rˣ :=
  ((Subgroup.equivMapOfInjective _ _ hι).trans <| MulEquiv.subgroupCongr <| by
    rw [scalarPoints, Subgroup.map_comap_eq, inf_eq_right.mpr hG, center_eq_range_scalar]).trans
    (MonoidHom.ofInjective (f := scalar (Fin n)) <| Units.map_injective fun _ _ ↦
      scalar_inj.mp).symm

lemma scalarPoints_eq_bot [Subsingleton Rˣ] (hι : Function.Injective (rationalPointsToGL ι)) :
    scalarPoints ι = ⊥ := by
  rw [scalarPoints, ← ProjGenLinGroup.ker_mk,
    (MonoidHom.ker_eq_bot_iff _).mpr ProjGenLinGroup.mk_injective_of_subsingleton_units,
    MonoidHom.comap_bot, MonoidHom.ker_eq_bot_iff]
  exact hι

/-- Over a ring `R` with only one unit, such as `𝔽₂`, an embedding `ι : G ⟶ GL_n` has no
non-trivial scalars, and `G(R)` modulo its scalars is `G(R)`. -/
noncomputable def quotientScalarPointsMulEquiv [Subsingleton Rˣ]
    (hι : Function.Injective (rationalPointsToGL ι)) :
    rationalPoints G ⧸ scalarPoints ι ≃* rationalPoints G :=
  (QuotientGroup.quotientMulEquivOfEq (scalarPoints_eq_bot hι)).trans QuotientGroup.quotientBot

end AlgebraicGeometry

namespace MonoidHom

variable {K : Type*} [Field K] {ℓ n : ℕ} {G : Grp (Over (Spec (.of (ZMod ℓ))))}
  (ι : G ⟶ GeneralLinear.groupScheme (ZMod ℓ) n) (ρ : Gal(AlgebraicClosure K/K) →* rationalPoints G)

/-- The representation `ι ∘ ρ : Gal(K̄/K) → GL_n(𝔽_ℓ)` of a representation `ρ` of the absolute
Galois group of a field `K`, such as a number field, with values in the `𝔽_ℓ`-points of a group
scheme `G` over `𝔽_ℓ`, through a morphism of group schemes `ι : G ⟶ GL_n`, such as an embedding: the
composite of `ρ` with the homomorphism `G(𝔽_ℓ) → GL_n(𝔽_ℓ)` induced by `ι`. The determinant
character, the determinant index and the surjectivity of the determinant of `ρ` are those of
`ι ∘ ρ`. -/
noncomputable def mapGL : Gal(AlgebraicClosure K/K) →* GL (Fin n) (ZMod ℓ) :=
  (rationalPointsToGL ι).comp ρ

/-- The **projective representation** (LMFDB `modlgal.projective_representation`)
`ℙρ : Gal(K̄/K) → G(𝔽_ℓ)/𝔽_ℓ^*` of a mod-`ℓ` Galois representation `ρ : Gal(K̄/K) → G(𝔽_ℓ)`, for an
algebraic group `G` with an embedding `ι : G ⟶ GL_n` over `𝔽_ℓ`: the composite of `ρ` with the
projection of `G(𝔽_ℓ)` onto its quotient by its scalars, the points that `ι` maps to scalar
matrices (`AlgebraicGeometry.scalarPoints`). The scalars of `G(𝔽_ℓ)` are `𝔽_ℓ^*` when `G` contains
the scalars of `GL_n` (`AlgebraicGeometry.scalarPointsMulEquivUnits`), which the LMFDB's quotient
`G(𝔽_ℓ)/𝔽_ℓ^*` presupposes; for every `G` the quotient is the image of `G(𝔽_ℓ)` in `PGL_n(𝔽_ℓ)`
(`AlgebraicGeometry.projectivePointsToPGL_injective`). -/
noncomputable def projectiveRepresentationIn :
    Gal(AlgebraicClosure K/K) →* rationalPoints G ⧸ scalarPoints ι :=
  (QuotientGroup.mk' _).comp ρ

/-- **The projective representation of `ρ` is carried to that of `ι ∘ ρ`** by the embedding of
`G(𝔽_ℓ)` modulo its scalars into `PGL_n(𝔽_ℓ)`. -/
lemma projectivePointsToPGL_comp_projectiveRepresentationIn : (projectivePointsToPGL ι).comp
    (ρ.projectiveRepresentationIn ι) = (ρ.mapGL ι).projectiveRepresentation :=
  ext fun _ ↦ rfl

/-- **For `ℓ = 2` the projective representation is the representation itself**
(LMFDB `modlgal.projective_representation`): for an algebraic group `G₂` over `𝔽₂` with an
embedding `ι₂ : G₂ ⟶ GL_n`, injective on `𝔽₂`-points, the scalars of `G₂(𝔽₂)` are trivial, and the
projective representation transported back along the isomorphism `G₂(𝔽₂)/𝔽₂^* ≃* G₂(𝔽₂)` is `ρ₂`. -/
lemma quotientScalarPointsMulEquiv_comp_projectiveRepresentationIn_two
    {G₂ : Grp (Over (Spec (.of (ZMod 2))))} {ι₂ : G₂ ⟶ GeneralLinear.groupScheme (ZMod 2) n}
    (hι₂ : Function.Injective (rationalPointsToGL ι₂))
    (ρ₂ : Gal(AlgebraicClosure K/K) →* rationalPoints G₂) :
    (quotientScalarPointsMulEquiv hι₂).toMonoidHom.comp (ρ₂.projectiveRepresentationIn ι₂) = ρ₂ :=
  ext fun _ ↦ rfl

/-- **The determinant character of a `1`-dimensional representation is the representation itself**
(LMFDB `modlgal.determinant`): for an embedding `ι₁ : G ⟶ GL_1`, the determinant character of `ρ`,
as a representation into the `𝔽_ℓ`-points of `GL_1`, is `ρ` followed by `ι₁` on `𝔽_ℓ`-points. -/
lemma symm_comp_detCharacterGL_mapGL (ι₁ : G ⟶ GeneralLinear.groupScheme (ZMod ℓ) 1) :
    (rationalPointsGLMulEquiv (ZMod ℓ) 1).symm.toMonoidHom.comp (ρ.mapGL ι₁).detCharacterGL =
      (IsMonHom.monoidHom ι₁.hom.hom _).comp ρ := by
  ext1 σ
  simp only [detCharacterGL_eq_self, comp_apply, MulEquiv.coe_toMonoidHom, mapGL,
    rationalPointsToGL, MulEquiv.symm_apply_apply]

variable {ι ρ} (ρ' : Gal(AlgebraicClosure K/K) →* GL (Fin n) (ZMod ℓ))

/-- **Through `ι`, a mod-`ℓ` Galois representation into `G(𝔽_ℓ)` gives one into `GL_n(𝔽_ℓ)`**: the
representation `ι ∘ ρ` is continuous, as its kernel contains the open kernel of `ρ`. -/
lemma IsModEllGaloisRepIn.isModEllGaloisRep_mapGL (hρ : ρ.IsModEllGaloisRepIn) :
    (ρ.mapGL ι).IsModEllGaloisRep where
  prime := hρ.prime
  isOpen_ker := Subgroup.isOpen_mono (fun σ hσ ↦ by
    rw [mem_ker, mapGL, comp_apply, mem_ker.mp hσ, map_one]) hρ.isOpen_ker

variable {ρ'} in
/-- **A mod-`ℓ` Galois representation into `GL_n(𝔽_ℓ)` is one into the `𝔽_ℓ`-points of the
algebraic group `GL_n`**, through the identification of these points with `GL_n(𝔽_ℓ)`. -/
lemma IsModEllGaloisRep.isModEllGaloisRepIn (hρ' : ρ'.IsModEllGaloisRep) :
    ((rationalPointsGLMulEquiv (ZMod ℓ) n).symm.toMonoidHom.comp ρ').IsModEllGaloisRepIn where
  prime := hρ'.prime
  locallyOfFiniteType := inferInstance
  quasiCompact := inferInstance
  isOpen_ker := by
    rw [ker_comp_of_injective _ _ (rationalPointsGLMulEquiv (ZMod ℓ) n).symm.injective]
    exact hρ'.isOpen_ker

/-- **For `GL_n` with the identity, `ι ∘ ρ` is the representation into `GL_n(𝔽_ℓ)`**: the notions
defined through `ι` are those of `GL_n(𝔽_ℓ)`. -/
lemma mapGL_id :
    ((rationalPointsGLMulEquiv (ZMod ℓ) n).symm.toMonoidHom.comp ρ').mapGL (𝟙 _) = ρ' := by
  ext1 σ
  rw [mapGL, rationalPointsToGL_id]
  exact (rationalPointsGLMulEquiv (ZMod ℓ) n).apply_symm_apply (ρ' σ)

/-- **The determinant character of a mod-`ℓ` Galois representation `ρ : Gal(K̄/K) → G(𝔽_ℓ)` is a
`1`-dimensional mod-`ℓ` Galois representation** (LMFDB `modlgal.determinant`): the determinant
character `det ρ : Gal(K̄/K) → 𝔽_ℓˣ` is that of `ι ∘ ρ`, the composite of `ρ` with the determinant
`G(𝔽_ℓ) → 𝔽_ℓˣ` of `ι`, and as a representation into `GL_1(𝔽_ℓ)` it takes values in the
`𝔽_ℓ`-points of the algebraic group `GL_1`, continuously. -/
lemma IsModEllGaloisRepIn.isModEllGaloisRepIn_detCharacterGL (hρ : ρ.IsModEllGaloisRepIn) :
    ((rationalPointsGLMulEquiv (ZMod ℓ) 1).symm.toMonoidHom.comp
      (ρ.mapGL ι).detCharacterGL).IsModEllGaloisRepIn :=
  ((ρ.mapGL ι).isModEllGaloisRep_detCharacterGL hρ.isModEllGaloisRep_mapGL).isModEllGaloisRepIn

/-- The **determinant** of a mod-`ℓ` Galois representation `ρ' : Gal(K̄/K) → GL_n(𝔽_ℓ)` **is
surjective** (LMFDB `modlgal.det_surjective`) if the image of its determinant map, the determinant
character as a `1`-dimensional representation `Gal(K̄/K) → GL_1(𝔽_ℓ)`, is all of `GL_1(𝔽_ℓ)`. For
a representation `ρ : Gal(K̄/K) → G(𝔽_ℓ)` and an embedding `ι : G ⟶ GL_n`, it is that of `ι ∘ ρ`. -/
def IsDetSurjective : Prop :=
  ρ'.detCharacterGL.range = ⊤

/-- The **determinant index** (LMFDB `modlgal.determinant_index`) of a mod-`ℓ` Galois
representation `ρ' : Gal(K̄/K) → GL_n(𝔽_ℓ)`: the index of `det(ρ'(Gal(K̄/K)))`, the image of the
determinant character, in `𝔽_ℓˣ`. For a representation `ρ : Gal(K̄/K) → G(𝔽_ℓ)` and an embedding
`ι : G ⟶ GL_n`, it is that of `ι ∘ ρ`, the index of `det(ρ(Gal(K̄/K)))` for the determinant
`G(𝔽_ℓ) → 𝔽_ℓˣ` of `ι` (`MonoidHom.detIndex_mapGL`). -/
noncomputable def detIndex : ℕ :=
  ρ'.detCharacter.range.index

/-- **The determinant is surjective exactly when the determinant character is**, as a map onto
`𝔽_ℓˣ`. -/
lemma isDetSurjective_iff : ρ'.IsDetSurjective ↔ Function.Surjective ρ'.detCharacter := by
  rw [IsDetSurjective, range_eq_top, detCharacterGL, coe_comp, MulEquiv.coe_toMonoidHom,
    EquivLike.comp_surjective]

/-- **The determinant is surjective exactly when the determinant index is `1`.** -/
lemma isDetSurjective_iff_detIndex_eq_one : ρ'.IsDetSurjective ↔ ρ'.detIndex = 1 := by
  rw [isDetSurjective_iff, detIndex, Subgroup.index_eq_one, range_eq_top]

/-- **The determinant index of `ρ : Gal(K̄/K) → G(𝔽_ℓ)` is the index of `det(ρ(Gal(K̄/K)))` in
`𝔽_ℓˣ`**, for the determinant `G(𝔽_ℓ) → 𝔽_ℓˣ` of the embedding `ι`. -/
lemma detIndex_mapGL :
    (ρ.mapGL ι).detIndex = (ρ.range.map (det.comp (rationalPointsToGL ι))).index := by
  rw [detIndex, detCharacter, mapGL, ← comp_assoc, range_comp]

/-- **The trivial representation into the `𝔽_ℓ`-points of an algebraic group is a mod-`ℓ` Galois
representation**, for `ℓ` prime and `G` of finite type over `𝔽_ℓ`, such as Tau Ceti's `GL_n`,
`SL_n` and diagonal torus of `GL_n`: the hypotheses of `MonoidHom.IsModEllGaloisRepIn` hold for
every algebraic group. -/
lemma isModEllGaloisRepIn_one_of_locallyOfFiniteType (hℓ : ℓ.Prime) [LocallyOfFiniteType G.X.hom]
    [QuasiCompact G.X.hom] :
    (1 : Gal(AlgebraicClosure K/K) →* rationalPoints G).IsModEllGaloisRepIn where
  prime := hℓ
  locallyOfFiniteType := ‹_›
  quasiCompact := ‹_›
  isOpen_ker := by
    rw [ker_one, Subgroup.coe_top]
    exact isOpen_univ

variable (ρₛ : Gal(AlgebraicClosure K/K) →* rationalPoints (SpecialLinear.groupScheme (ZMod ℓ) n))

/-- **The determinant character of a representation into `SL_n(𝔽_ℓ)` is trivial**, for Tau Ceti's
closed immersion `SL_n ⟶ GL_n`. -/
lemma detCharacter_mapGL_specialLinear :
    (ρₛ.mapGL (SpecialLinear.groupSchemeι (ZMod ℓ) n)).detCharacter = 1 :=
  ext fun σ ↦ det_rationalPointsToGL_specialLinear (ρₛ σ)

/-- **The determinant index of a representation into `SL_n(𝔽_ℓ)` is `ℓ - 1`**, for `ℓ` prime: its
determinant is not surjective unless `ℓ = 2`. -/
lemma detIndex_mapGL_specialLinear [Fact ℓ.Prime] :
    (ρₛ.mapGL (SpecialLinear.groupSchemeι (ZMod ℓ) n)).detIndex = ℓ - 1 := by
  rw [detIndex, detCharacter_mapGL_specialLinear, range_one, Subgroup.index_bot,
    Nat.card_eq_fintype_card, ZMod.card_units]

variable [NumberField K] (hρ : IsOpen (ρ.ker : Set Gal(AlgebraicClosure K/K))) (𝔭 : Ideal (𝓞 K))
  [𝔭.IsMaximal] (hur : ∀ (Q : Ideal (𝓞 (kerSplittingField ρ hρ))) [Q.IsPrime] [Q.LiesOver 𝔭],
    Algebra.IsUnramifiedAt (𝓞 K) Q)

variable (ι) in
/-- The **characteristic polynomial of Frobenius** (LMFDB `modlgal.frobenius_charpoly`) of a
mod-`ℓ` Galois representation `ρ : Gal(K̄/K) → G(𝔽_ℓ)`, for an algebraic group `G` with an embedding
`ι : G ⟶ GL_n`, at a prime `𝔭` at which `ρ` is unramified, that is, which is unramified in the
splitting field `L` of `ρ`: the characteristic polynomial of `ρ(Frob_𝔭)` through `ι`, for
`ρ(Frob_𝔭)` in the image under `ρ` of the conjugacy class of the Frobenius elements of `Gal(L/K)`
at the primes above `𝔭` (`MonoidHom.frobeniusConjClass`), which does not depend on the element of
that class (`MonoidHom.frobeniusCharpolyIn_eq`). -/
noncomputable def frobeniusCharpolyIn : Polynomial (ZMod ℓ) :=
  Quotient.lift (s := IsConj.setoid _)
    (fun A : rationalPoints G ↦ (rationalPointsToGL ι A).val.charpoly)
    (fun _ _ h ↦ by
      rcases isConj_iff.mp h with ⟨c, rfl⟩
      simp) (frobeniusConjClass hρ 𝔭 hur)

variable (ι) in
/-- The **Frobenius trace** (LMFDB `modlgal.frobenius_trace`) of a mod-`ℓ` Galois representation
`ρ : Gal(K̄/K) → G(𝔽_ℓ)`, for an algebraic group `G` with an embedding `ι : G ⟶ GL_n`, at a prime
`𝔭` at which `ρ` is unramified: the trace of `ρ(Frob_𝔭)` through `ι`, which does not depend on the
element `ρ(Frob_𝔭)` of the Frobenius class of `ρ` in `G(𝔽_ℓ)` (`MonoidHom.frobeniusTraceIn_eq`). -/
noncomputable def frobeniusTraceIn : ZMod ℓ :=
  Quotient.lift (s := IsConj.setoid _)
    (fun A : rationalPoints G ↦ (rationalPointsToGL ι A).val.trace)
    (fun _ _ h ↦ by
      rcases isConj_iff.mp h with ⟨c, rfl⟩
      rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, trace_units_conj])
    (frobeniusConjClass hρ 𝔭 hur)

variable (ι) in
/-- The **Frobenius determinant** (LMFDB `modlgal.frobenius_determinant`) of a mod-`ℓ` Galois
representation `ρ : Gal(K̄/K) → G(𝔽_ℓ)`, for an algebraic group `G` with an embedding
`ι : G ⟶ GL_n`, at a prime `𝔭` at which `ρ` is unramified: the determinant of `ρ(Frob_𝔭)` through
`ι`, which does not depend on the element `ρ(Frob_𝔭)` of the Frobenius class of `ρ` in `G(𝔽_ℓ)`
(`MonoidHom.frobeniusDetIn_eq`), and is the value of the determinant character at a Frobenius
element (`MonoidHom.frobeniusDetIn_eq_detCharacter`). -/
noncomputable def frobeniusDetIn : (ZMod ℓ)ˣ :=
  Quotient.lift (s := IsConj.setoid _) (det.comp (rationalPointsToGL ι))
    (fun _ _ h ↦ isConj_iff_eq.mp ((det.comp (rationalPointsToGL ι)).map_isConj h))
    (frobeniusConjClass hρ 𝔭 hur)

variable {hρ 𝔭 hur} {A : rationalPoints G}

/-- **The characteristic polynomial of Frobenius is that of `ι(A)` for any `A` in the Frobenius
class of `ρ`.** -/
lemma frobeniusCharpolyIn_eq (hA : ConjClasses.mk A = frobeniusConjClass hρ 𝔭 hur) :
    frobeniusCharpolyIn ι hρ 𝔭 hur = (rationalPointsToGL ι A).val.charpoly := by
  rw [frobeniusCharpolyIn, ← hA]
  rfl

/-- **The Frobenius trace is that of `ι(A)` for any `A` in the Frobenius class of `ρ`.** -/
lemma frobeniusTraceIn_eq (hA : ConjClasses.mk A = frobeniusConjClass hρ 𝔭 hur) :
    frobeniusTraceIn ι hρ 𝔭 hur = (rationalPointsToGL ι A).val.trace := by
  rw [frobeniusTraceIn, ← hA]
  rfl

/-- **The Frobenius determinant is that of `ι(A)` for any `A` in the Frobenius class of `ρ`.** -/
lemma frobeniusDetIn_eq (hA : ConjClasses.mk A = frobeniusConjClass hρ 𝔭 hur) :
    frobeniusDetIn ι hρ 𝔭 hur = det (rationalPointsToGL ι A) := by
  rw [frobeniusDetIn, ← hA]
  rfl

lemma kerGaloisFactor_restrictNormalHom {H : Type*} [Group H] {φ : Gal(AlgebraicClosure K/K) →* H}
    (hφ : IsOpen (φ.ker : Set Gal(AlgebraicClosure K/K))) (σ : Gal(AlgebraicClosure K/K)) :
    kerGaloisFactor hφ (AlgEquiv.restrictNormalHom (kerSplittingField φ hφ) σ) = φ σ :=
  (congrArg (QuotientGroup.kerLift φ) <| (MulEquiv.symm_apply_eq _).mpr
    (InfiniteGalois.normalAutEquivQuotient_apply ⟨φ.ker, φ.ker.isClosed_of_isOpen hφ⟩ σ).symm).trans
    (QuotientGroup.kerLift_mk φ σ)

/-- **The Frobenius determinant is the value of the determinant character at a Frobenius element**
(LMFDB `modlgal.frobenius_determinant`): at any `σ ∈ Gal(K̄/K)` whose restriction to the splitting
field of `ρ` lies in the conjugacy class of the Frobenius elements at the primes above `𝔭`, Tau
Ceti's `NumberField.artinSymbol`. -/
lemma frobeniusDetIn_eq_detCharacter {σ : Gal(AlgebraicClosure K/K)}
    (hσ : ConjClasses.mk (AlgEquiv.restrictNormalHom _ σ) = artinSymbol 𝔭 hur) :
    frobeniusDetIn ι hρ 𝔭 hur = (ρ.mapGL ι).detCharacter σ :=
  frobeniusDetIn_eq <| (congrArg ConjClasses.mk (kerGaloisFactor_restrictNormalHom hρ σ).symm).trans
    (congrArg (ConjClasses.map (kerGaloisFactor hρ)) hσ)

variable {hρ' : IsOpen ((ρ.mapGL ι).ker : Set Gal(AlgebraicClosure K/K))}
  {hur' : ∀ (Q : Ideal (𝓞 (splittingField (ρ.mapGL ι) hρ'))) [Q.IsPrime] [Q.LiesOver 𝔭],
    Algebra.IsUnramifiedAt (𝓞 K) Q}

/-- **For an embedding, `ρ` and `ι ∘ ρ` have the same splitting field**, as `ι` is injective on
`𝔽_ℓ`-points and their kernels agree: so `ρ` and `ι ∘ ρ` are unramified at the same primes. -/
lemma splittingField_mapGL (hι : Function.Injective (rationalPointsToGL ι)) :
    splittingField (ρ.mapGL ι) hρ' = kerSplittingField ρ hρ :=
  FiniteGaloisIntermediateField.val_injective <|
    congrArg IntermediateField.fixedField (ker_comp_of_injective ρ _ hι)

/-- **For an embedding, `ι` carries the Frobenius class of `ρ` onto the class of the Frobenius
matrices of `ι ∘ ρ`**: `ρ` and `ι ∘ ρ` have the same splitting field `L`, and `ι` carries the image
under `ρ` of the Frobenius elements of `Gal(L/K)` at the primes above `𝔭` to their image under
`ι ∘ ρ`. -/
lemma frobeniusClass_mapGL (hι : Function.Injective (rationalPointsToGL ι)) :
    frobeniusClass hρ' 𝔭 hur' = (frobeniusConjClass hρ 𝔭 hur).map (rationalPointsToGL ι) := by
  have hL : (kerSplittingField ρ hρ).toIntermediateField =
      (splittingField (ρ.mapGL ι) hρ').toIntermediateField :=
    congrArg FiniteGaloisIntermediateField.toIntermediateField (splittingField_mapGL hι).symm
  have he (σ : Gal(AlgebraicClosure K/K)) : (IntermediateField.equivOfEq hL).autCongr
      (AlgEquiv.restrictNormalHom _ σ) = AlgEquiv.restrictNormalHom _ σ :=
    AlgEquiv.ext fun _ ↦ Subtype.ext <| by
      simp [AlgEquiv.restrictNormalHom_apply]
  rcases ConjClasses.exists_rep (artinSymbol 𝔭 hur) with ⟨τ, hτ⟩
  rcases AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) τ with ⟨σ, rfl⟩
  rw [frobeniusClass, frobeniusConjClass,
    artinSymbol_eq_map_autCongr 𝔭 (IntermediateField.equivOfEq hL) hur hur', ← hτ]
  exact congrArg ConjClasses.mk <| (congrArg (galoisFactor hρ') (he σ)).trans <|
    (galoisFactor_restrictNormalHom hρ' σ).trans <|
      congrArg (rationalPointsToGL ι) (kerGaloisFactor_restrictNormalHom hρ σ).symm

lemma isFrobeniusMatrix_rationalPointsToGL (hι : Function.Injective (rationalPointsToGL ι))
    (hA : ConjClasses.mk A = frobeniusConjClass hρ 𝔭 hur) :
    IsFrobeniusMatrix hρ' 𝔭 hur' (rationalPointsToGL ι A) :=
  (congrArg (ConjClasses.map (rationalPointsToGL ι)) hA).trans (frobeniusClass_mapGL hι).symm

/-- **For an embedding, the characteristic polynomial of Frobenius of `ρ` is that of `ι ∘ ρ`**, the
characteristic polynomial of its Frobenius matrices. -/
lemma frobeniusCharpolyIn_eq_frobeniusCharpoly (hι : Function.Injective (rationalPointsToGL ι)) :
    frobeniusCharpolyIn ι hρ 𝔭 hur = frobeniusCharpoly hρ' 𝔭 hur' := by
  rcases ConjClasses.exists_rep (frobeniusConjClass hρ 𝔭 hur) with ⟨A, hA⟩
  rw [frobeniusCharpolyIn_eq hA, frobeniusCharpoly_eq (isFrobeniusMatrix_rationalPointsToGL hι hA)]

/-- **For an embedding, the Frobenius trace of `ρ` is that of `ι ∘ ρ`**, the trace of its Frobenius
matrices. -/
lemma frobeniusTraceIn_eq_frobeniusTrace (hι : Function.Injective (rationalPointsToGL ι)) :
    frobeniusTraceIn ι hρ 𝔭 hur = frobeniusTrace hρ' 𝔭 hur' := by
  rcases ConjClasses.exists_rep (frobeniusConjClass hρ 𝔭 hur) with ⟨A, hA⟩
  rw [frobeniusTraceIn_eq hA, frobeniusTrace_eq (isFrobeniusMatrix_rationalPointsToGL hι hA)]

/-- **For an embedding, the Frobenius determinant of `ρ` is that of `ι ∘ ρ`**, the determinant of
its Frobenius matrices. -/
lemma frobeniusDetIn_eq_frobeniusDet (hι : Function.Injective (rationalPointsToGL ι)) :
    frobeniusDetIn ι hρ 𝔭 hur = frobeniusDet hρ' 𝔭 hur' := by
  rcases ConjClasses.exists_rep (frobeniusConjClass hρ 𝔭 hur) with ⟨A, hA⟩
  rw [frobeniusDetIn_eq hA, frobeniusDet_eq (isFrobeniusMatrix_rationalPointsToGL hι hA)]

end MonoidHom
