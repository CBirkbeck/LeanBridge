import LeanBridge.ForMathlib.NumberTheory.Artin.Basic
import LeanBridge.ForMathlib.NumberTheory.ModularForms.SatoTate.ProjectiveImageClassification

/-!
# The projective image of an Artin representation and its type

A representation `ρ` of a group `G` on a vector space `V` with a basis `b` indexed by `ι` gives a
homomorphism `G → GL_ι(k)`, the matrices of `ρ` in `b`, and its composite with the projection
`GL_ι(k) → PGL_ι(k)` is the projective representation of `ρ`, whose image is the projective image of
`ρ` (LMFDB `artin.projective_image`, where `ρ` is an Artin representation of `G = Gal(ℚ̄/ℚ)`).
Another basis conjugates the matrices, so the projective image does not depend on the basis up to
isomorphism. The projective image of an Artin representation is finite, as the kernel of its
projective representation is open.

A two-dimensional complex representation with finite projective image, such as an Artin
representation or a representation of a finite group, is irreducible if and only if its projective
image is not cyclic: an eigenvector of a lift of a generator of a cyclic projective image spans a
stable line, and conversely a stable line is a point of the projective line fixed by the projective
image, whose stabilisers in a finite subgroup of `PGL₂(ℂ)` are cyclic
(`Matrix.ProjGenLinGroup.isCyclic_stabilizer`). By the classification of the finite subgroups of
`PGL₂(ℂ)` (`Matrix.ProjGenLinGroup.classification`), the projective image of such a representation
is then isomorphic to the dihedral group `D_m` of order `2m` for some `m ≥ 2` (`D₂` being the Klein
four-group), to `A₄`, to `S₄` or to `A₅` if and only if the representation is irreducible: these
are the types of `HeckeRing.GL2.Newform.GaloisRep.ProjectiveImageType` (LMFDB
`artin.projective_image_type`), and the type is unique
(`HeckeRing.GL2.Newform.GaloisRep.ProjectiveImageType.IsTypeOf.eq`). The LMFDB states the
classification for every two-dimensional Artin representation, but the projective image of a
reducible one, such as `χ₁ ⊕ χ₂`, is cyclic: the statement needs `ρ` irreducible.

The instance `Finite (ρ.projectiveImage b)` covers the representations of a finite group.

## Main definitions

* `Representation.toGL`: the matrices `G → GL_ι(k)` of a representation in a basis.
* `Representation.toPGL` (LMFDB `artin.projective_image`): the projective representation
  `G → PGL_ι(k)`.
* `Representation.projectiveImage` (LMFDB `artin.projective_image`): the projective image.

## Main results

* `Representation.nonempty_mulEquiv_projectiveImage`: the projective images of a representation in
  two bases are isomorphic.
* `Representation.isIrreducible_iff_not_isCyclic_projectiveImage`: a two-dimensional complex
  representation with finite projective image is irreducible if and only if its projective image is
  not cyclic.
* `Representation.exists_isTypeOf_projectiveImage_iff`: the projective image of a two-dimensional
  complex representation with finite projective image has a type if and only if the representation
  is irreducible.
* `Representation.IsArtin.finite_projectiveImage` (LMFDB `artin.projective_image_type`): the
  projective image of an Artin representation is finite.
* `Representation.IsArtin.exists_isTypeOf_projectiveImage_iff` (LMFDB
  `artin.projective_image_type`): the projective image of a two-dimensional Artin representation is
  isomorphic to `D_m` for some `m ≥ 2`, to `A₄`, to `S₄` or to `A₅` if and only if the
  representation is irreducible.
-/

open Matrix Module MulAction Projectivization HeckeRing GL2 Newform GaloisRep

open scoped LinearAlgebra.Projectivization MatrixGroups

namespace Representation

section Field

variable {k G V ι : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] [Fintype ι]
  [DecidableEq ι] (ρ : Representation k G V) (b : Basis ι k V)

/-- The **matrices** of a representation `ρ` of a group `G` in a basis `b` indexed by `ι`: the
homomorphism `G → GL_ι(k)` sending `g` to the matrix of `ρ g` in `b`. -/
noncomputable def toGL : G →* GL ι k :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp ρ.asGroupHom

lemma coe_toGL (g : G) : (ρ.toGL b g : Matrix ι ι k) = LinearMap.toMatrix b b (ρ g) :=
  rfl

/-- The **projective representation** (LMFDB `artin.projective_image`) `G → PGL_ι(k)` of a
representation `ρ` in a basis `b`: the composite of its matrices `Representation.toGL` with the
projection of `GL_ι(k)` onto `PGL_ι(k)`, Mathlib's quotient of `GL_ι(k)` by its centre, the scalar
matrices. -/
noncomputable def toPGL : G →* PGL(ι, k) :=
  ProjGenLinGroup.mk.comp (ρ.toGL b)

/-- The **projective image** (LMFDB `artin.projective_image`) of a representation `ρ` in a basis
`b`: the image of its projective representation, a subgroup of `PGL_ι(k)`. It does not depend on
`b` up to isomorphism (`Representation.nonempty_mulEquiv_projectiveImage`). -/
noncomputable def projectiveImage : Subgroup PGL(ι, k) :=
  (ρ.toPGL b).range

instance [Finite G] : Finite (ρ.projectiveImage b) :=
  Finite.of_surjective _ (ρ.toPGL b).rangeRestrict_surjective

/-- **The projective image does not depend on the basis**, up to isomorphism: the matrices of `ρ`
in two bases are conjugate by the change of basis matrix, so the two projective images are
conjugate in `PGL_ι(k)`. -/
lemma nonempty_mulEquiv_projectiveImage (b' : Basis ι k V) :
    Nonempty (ρ.projectiveImage b ≃* ρ.projectiveImage b') := by
  let P : GL ι k := ⟨b'.toMatrix b, b.toMatrix b', b'.toMatrix_mul_toMatrix_flip b,
    b.toMatrix_mul_toMatrix_flip b'⟩
  have h : ρ.toPGL b' = (MulAut.conj (ProjGenLinGroup.mk P)).toMonoidHom.comp (ρ.toPGL b) := by
    ext1 g
    have hg : ρ.toGL b' g = P * ρ.toGL b g * P⁻¹ :=
      Units.ext (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b' b b' b (ρ g)).symm
    simp only [toPGL, MonoidHom.comp_apply, hg, map_mul, map_inv, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
  exact ⟨((ρ.toPGL b).range.equivMapOfInjective (MulAut.conj (ProjGenLinGroup.mk P)).toMonoidHom
    (MulAut.conj _).injective).trans <|
      MulEquiv.subgroupCongr (by rw [projectiveImage, h, MonoidHom.range_comp])⟩

end Field

section Complex

variable {G V ι : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
  (ρ : Representation ℂ G V)

lemma exists_eigenvector_of_isCyclic_projectiveImage [Nonempty ι] (b : Basis ι ℂ V)
    [Finite (ρ.projectiveImage b)] [IsCyclic (ρ.projectiveImage b)] :
    ∃ v : V, v ≠ 0 ∧ ∀ g, ∃ c : ℂ, ρ g v = c • v := by
  rcases IsCyclic.exists_generator (α := ρ.projectiveImage b) with ⟨x, hx⟩
  rcases ProjGenLinGroup.mk_surjective (x : PGL(ι, ℂ)) with ⟨A, hA⟩
  rcases End.exists_eigenvalue (toLin' (A : Matrix ι ι ℂ)) with ⟨μ, hμ⟩
  rcases hμ.exists_hasEigenvector with ⟨w, hw⟩
  refine ⟨b.equivFun.symm w, b.equivFun.symm.map_ne_zero_iff.mpr hw.2, fun g ↦ ?_⟩
  rcases mem_powers_iff_mem_zpowers.mpr (hx ⟨ρ.toPGL b g, g, rfl⟩) with ⟨m, hm⟩
  have h : ProjGenLinGroup.mk (A ^ m) = ProjGenLinGroup.mk (ρ.toGL b g) := by
    rw [map_pow, hA]
    exact congrArg Subtype.val hm
  rcases GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp (QuotientGroup.eq.mp h) with
    ⟨c, hc⟩
  have hρ : LinearMap.toMatrix b b (ρ g) = c • (A : Matrix ι ι ℂ) ^ m := by
    rw [← coe_toGL, ← mul_inv_cancel_left (A ^ m) (ρ.toGL b g), Units.val_mul, ← hc, scalar_apply,
      ← smul_one_eq_diagonal, Matrix.mul_smul, mul_one, Units.val_pow_eq_pow_val]
  refine ⟨c * μ ^ m, b.equivFun.injective ?_⟩
  rw [map_smul, LinearEquiv.apply_symm_apply, Basis.equivFun_apply,
    ← LinearMap.toMatrix_mulVec_repr b b, hρ, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply,
    smul_mulVec, ← toLin'_apply, toLin'_pow, hw.pow_apply, smul_smul]

variable (b : Basis (Fin 2) ℂ V) [Finite (ρ.projectiveImage b)]

lemma not_isCyclic_projectiveImage [ρ.IsIrreducible] : ¬IsCyclic (ρ.projectiveImage b) := by
  intro hcyc
  rcases ρ.exists_eigenvector_of_isCyclic_projectiveImage b with ⟨v, hv, hρ⟩
  have hW : ∀ (g : G) ⦃w : V⦄, w ∈ ℂ ∙ v → ρ g w ∈ ℂ ∙ v := by
    intro g w hw
    rcases Submodule.mem_span_singleton.mp hw with ⟨a, rfl⟩
    rcases hρ g with ⟨c, hc⟩
    exact Submodule.mem_span_singleton.mpr ⟨a * c, by rw [map_smul, hc, smul_smul]⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top (⟨ℂ ∙ v, hW⟩ : Subrepresentation ρ) with h | h
  · have h' : ℂ ∙ v = ⊥ := congrArg Subrepresentation.toSubmodule h
    exact hv <| (Submodule.mem_bot ℂ).mp <| h' ▸ Submodule.mem_span_singleton_self v
  · have h' : ℂ ∙ v = ⊤ := congrArg Subrepresentation.toSubmodule h
    have h₁ : finrank ℂ (ℂ ∙ v) = 1 := finrank_span_singleton hv
    rw [h', finrank_top, finrank_eq_card_basis b, Fintype.card_fin] at h₁
    exact absurd h₁ (by decide)

lemma isCyclic_projectiveImage_of_eigenvector {v : V} (hv : v ≠ 0)
    (hρ : ∀ g, ∃ c : ℂ, ρ g v = c • v) : IsCyclic (ρ.projectiveImage b) := by
  have hv' : b.equivFun v ≠ 0 := b.equivFun.map_ne_zero_iff.mpr hv
  have : IsCyclic (stabilizer (ρ.projectiveImage b) (Projectivization.mk ℂ _ hv')) :=
    ProjGenLinGroup.isCyclic_stabilizer _ _
  refine isCyclic_of_surjective (stabilizer _ (Projectivization.mk ℂ _ hv')).subtype fun k ↦
    ⟨⟨k, ?_⟩, rfl⟩
  rcases k with ⟨_, g, rfl⟩
  rcases hρ g with ⟨c, hc⟩
  refine (PGL.mk_smul_mk (ρ.toGL b g) hv').trans <| (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    ⟨c, ?_⟩
  rw [← map_smul, ← hc, Basis.equivFun_apply, Basis.equivFun_apply,
    ← LinearMap.toMatrix_mulVec_repr b b]
  rfl

lemma isIrreducible_of_not_isCyclic_projectiveImage (h : ¬IsCyclic (ρ.projectiveImage b)) :
    ρ.IsIrreducible := by
  have hV : finrank ℂ V = 2 := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  have : FiniteDimensional ℂ V := b.finiteDimensional_of_finite
  have : Nontrivial V := nontrivial_of_finrank_eq_succ hV
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h' ↦ ?_⟩, eq_bot_or_eq_top := fun W ↦ ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h' : (⊥ : Submodule ℂ V) = ⊤)
  · by_cases hW : W.toSubmodule = ⊥
    · exact Or.inl (Subrepresentation.toSubmodule_injective hW)
    by_cases hW' : W.toSubmodule = ⊤
    · exact Or.inr (Subrepresentation.toSubmodule_injective hW')
    rcases Submodule.exists_mem_ne_zero_of_ne_bot hW with ⟨v, hvW, hv⟩
    have h1 : finrank ℂ W.toSubmodule = 1 := by
      have hlt : finrank ℂ W.toSubmodule < 2 := hV ▸ Submodule.finrank_lt hW'
      have hne : finrank ℂ W.toSubmodule ≠ 0 := Submodule.finrank_eq_zero.not.mpr hW
      omega
    refine (h (ρ.isCyclic_projectiveImage_of_eigenvector b hv fun g ↦ ?_)).elim
    rcases (finrank_eq_one_iff_of_nonzero' (⟨v, hvW⟩ : W.toSubmodule) fun h0 ↦ hv
      (congrArg Subtype.val h0)).mp h1 ⟨ρ g v, W.apply_mem_toSubmodule g hvW⟩ with ⟨c, hc⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩

/-- **A two-dimensional representation with finite projective image is irreducible if and only if
its projective image is not cyclic**: an eigenvector of a lift of a generator of a cyclic projective
image spans a stable line, and a stable line is a point of the projective line fixed by the
projective image, which then lies in a point stabiliser, a cyclic group. -/
lemma isIrreducible_iff_not_isCyclic_projectiveImage :
    ρ.IsIrreducible ↔ ¬IsCyclic (ρ.projectiveImage b) :=
  ⟨fun _ ↦ ρ.not_isCyclic_projectiveImage b, ρ.isIrreducible_of_not_isCyclic_projectiveImage b⟩

/-- **The projective image of a two-dimensional representation with finite projective image has a
type if and only if the representation is irreducible**: it is isomorphic to the dihedral group
`D_m` of order `2m` for some `m ≥ 2`, to `A₄`, to `S₄` or to `A₅` exactly when it is not cyclic, by
the classification of the finite subgroups of `PGL₂(ℂ)`. -/
lemma exists_isTypeOf_projectiveImage_iff :
    (∃ t : ProjectiveImageType, t.IsTypeOf (ρ.projectiveImage b)) ↔ ρ.IsIrreducible :=
  ⟨fun ⟨_, ht⟩ ↦ ρ.isIrreducible_of_not_isCyclic_projectiveImage b ht.not_isCyclic, fun _ ↦
    (isCyclic_or_exists_isTypeOf _ (hH := ‹_›)).resolve_left (ρ.not_isCyclic_projectiveImage b)⟩

end Complex

section Artin

variable {K V ι : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module ℂ V] [Fintype ι]
  [DecidableEq ι] {ρ : Representation ℂ Gal(AlgebraicClosure K/K) V}

/-- **The projective image of an Artin representation is finite** (LMFDB
`artin.projective_image_type`): the kernel of its projective representation contains the kernel of
the representation, so it is open, and its fixed field is a finite extension whose degree is the
order of the projective image. -/
lemma IsArtin.finite_projectiveImage (h : ρ.IsArtin) (b : Basis ι ℂ V) :
    Finite (ρ.projectiveImage b) := by
  have hker : ρ.ker ≤ (ρ.toPGL b).ker := fun g hg ↦ by
    have h1 : ρ.toGL b g = 1 := Units.ext <| by
      rw [coe_toGL, MonoidHom.mem_ker.mp hg, LinearMap.toMatrix_one, Units.val_one]
    rw [MonoidHom.mem_ker, toPGL, MonoidHom.comp_apply, h1, map_one]
  have hopen : IsOpen ((ρ.toPGL b).ker : Set Gal(AlgebraicClosure K/K)) :=
    Subgroup.isOpen_mono hker h.isOpen_ker
  have : FiniteDimensional K (IntermediateField.fixedField (ρ.toPGL b).ker) :=
    (ρ.toPGL b).finiteDimensional_fixedField_ker hopen
  exact Nat.finite_of_card_ne_zero ((ρ.toPGL b).finrank_fixedField_ker hopen ▸ finrank_pos.ne')

/-- **The projective image type of a two-dimensional Artin representation** (LMFDB
`artin.projective_image_type`): the projective image of a two-dimensional Artin representation `ρ`
is isomorphic to the dihedral group `D_m` of order `2m` for some `m ≥ 2` (`D₂` being the Klein
four-group), to `A₄`, to `S₄` or to `A₅` if and only if `ρ` is irreducible; the projective image of
a reducible one is cyclic. -/
lemma IsArtin.exists_isTypeOf_projectiveImage_iff (h : ρ.IsArtin) (b : Basis (Fin 2) ℂ V) :
    (∃ t : ProjectiveImageType, t.IsTypeOf (ρ.projectiveImage b)) ↔ ρ.IsIrreducible :=
  have : Finite (ρ.projectiveImage b) := h.finite_projectiveImage b
  ρ.exists_isTypeOf_projectiveImage_iff b

end Artin

end Representation
