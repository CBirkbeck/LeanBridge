import LeanBridge.ForMathlib.LinearAlgebra.QuadraticForm.FiniteFieldClassification

/-!
# The orthogonal groups over a finite field are well defined

Similar quadratic forms have isomorphic orthogonal groups. If `c • Q` is isometric to `Q'` by `e`,
then `O(Q) = O(c • Q)`, and conjugation by `e` carries it onto `O(Q')` and `SO(Q)` onto `SO(Q')`;
it carries the scalars onto the scalars, so that `PGO(Q) ≅ PGO(Q')` and `PSO(Q) ≅ PSO(Q')` as well.

With the classification of the nondegenerate quadratic forms over `𝔽_q`
(`QuadraticForm.exists_equivalent_smul_parabolicForm`,
`QuadraticForm.equivalent_hyperbolicForm_or_equivalent_ellipticForm`), this shows that the groups
of LMFDB `group.orthogonal` do not depend on the chosen forms up to isomorphism. In odd dimension
`2 m + 1` the groups `O`, `SO`, `PGO`, `PSO` of every nondegenerate form are isomorphic to those of
the parabolic form, `GO(2m + 1, q)`, `SO(2m + 1, q)`, `PGO(2m + 1, q)` and `PSO(2m + 1, q)`. In even
dimension `2 m + 2` they are isomorphic to those of the hyperbolic form, `GO⁺(2m + 2, q)` and its
relatives, or to those of the elliptic form, `GO⁻(2m + 2, q)` and its relatives, and the two forms
are not similar (`QuadraticForm.not_equivalent_smul_hyperbolicForm_ellipticForm`).

## Main definitions

* `QuadraticForm.quotientScalarSubgroupEquiv`: an isomorphism of subgroups of `GL(V)` and `GL(W)`
  given by conjugation induces an isomorphism of their quotients by the scalars.
* `QuadraticForm.orthogonalGroupEquivOfSMul`, `QuadraticForm.specialOrthogonalGroupEquivOfSMul`,
  `QuadraticForm.projectiveOrthogonalGroupEquivOfSMul`,
  `QuadraticForm.projectiveSpecialOrthogonalGroupEquivOfSMul`: the isomorphisms of the groups `O`,
  `SO`, `PGO`, `PSO` of similar quadratic forms.

## Main results

* `QuadraticForm.nonempty_orthogonalGroup_mulEquiv_parabolicForm`,
  `QuadraticForm.nonempty_specialOrthogonalGroup_mulEquiv_parabolicForm`,
  `QuadraticForm.nonempty_projectiveOrthogonalGroup_mulEquiv_parabolicForm`,
  `QuadraticForm.nonempty_projectiveSpecialOrthogonalGroup_mulEquiv_parabolicForm` (LMFDB
  `group.orthogonal`): `GO(n, q)`, `SO(n, q)`, `PGO(n, q)` and `PSO(n, q)`, `n` odd, are unique
  up to isomorphism.
* `QuadraticForm.nonempty_orthogonalGroup_mulEquiv_hyperbolicForm_or_ellipticForm`,
  `QuadraticForm.nonempty_specialOrthogonalGroup_mulEquiv_hyperbolicForm_or_ellipticForm`,
  `QuadraticForm.nonempty_projectiveOrthogonalGroup_mulEquiv_hyperbolicForm_or_ellipticForm`,
  `QuadraticForm.nonempty_projectiveSpecialOrthogonalGroup_mulEquiv_hyperbolicForm_or_ellipticForm`
  (LMFDB `group.orthogonal`): for `n` even the groups of every nondegenerate form are those of the
  `+` or of the `-` form.
-/

open Module TauCeti QuadraticMap

namespace QuadraticForm

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  {Q : QuadraticForm F V} {Q' : QuadraticForm F W} (c : Fˣ) (e : (c • Q).IsometryEquiv Q')
  (ψ : V ≃ₗ[F] W)

private lemma mem_scalarSubgroup_iff_of_conj {f : V ≃ₗ[F] V} {g : W ≃ₗ[F] W}
    (h : ∀ v, g (ψ v) = ψ (f v)) :
    f ∈ LinearEquiv.scalarSubgroup F V ↔ g ∈ LinearEquiv.scalarSubgroup F W := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, LinearEquiv.ext fun w ↦ ?_⟩
    rw [← ψ.apply_symm_apply w, h]
    simp [Units.smul_def]
  · rintro ⟨a, ha⟩
    refine ⟨a, LinearEquiv.ext fun v ↦ ψ.injective ?_⟩
    rw [← h, ← ha]
    simp [Units.smul_def]

/-- An isomorphism of subgroups `H₁ ≤ GL(V)` and `H₂ ≤ GL(W)` given by conjugation by a linear
equivalence `ψ : V ≃ W` induces an isomorphism of their quotients by the scalar automorphisms. -/
noncomputable def quotientScalarSubgroupEquiv {H₁ : Subgroup (V ≃ₗ[F] V)}
    {H₂ : Subgroup (W ≃ₗ[F] W)} (φ : H₁ ≃* H₂)
    (hφ : ∀ s v, (φ s : W ≃ₗ[F] W) (ψ v) = ψ ((s : V ≃ₗ[F] V) v)) :
    H₁ ⧸ (LinearEquiv.scalarSubgroup F V).subgroupOf H₁ ≃*
      H₂ ⧸ (LinearEquiv.scalarSubgroup F W).subgroupOf H₂ :=
  QuotientGroup.congr _ _ φ <| Subgroup.ext fun t ↦ by
    rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    exact mem_scalarSubgroup_iff_of_conj ψ fun v ↦ by rw [← hφ, MulEquiv.apply_symm_apply]

lemma orthogonalGroup_smul : orthogonalGroup (c • Q) = orthogonalGroup Q := by
  ext f
  simp

lemma specialOrthogonalGroup_smul : specialOrthogonalGroup (c • Q) = specialOrthogonalGroup Q := by
  rw [specialOrthogonalGroup, specialOrthogonalGroup, orthogonalGroup_smul]

/-- **Similar quadratic forms have isomorphic orthogonal groups**: if `c • Q` is isometric to `Q'`
by `e`, conjugation by `e` carries `O(Q) = O(c • Q)` onto `O(Q')`. -/
noncomputable def orthogonalGroupEquivOfSMul : orthogonalGroup Q ≃* orthogonalGroup Q' :=
  (MulEquiv.subgroupCongr (orthogonalGroup_smul c).symm).trans e.orthogonalGroupCongr

lemma orthogonalGroupEquivOfSMul_apply (s : orthogonalGroup Q) (v : V) :
    (orthogonalGroupEquivOfSMul c e s : W ≃ₗ[F] W) (e v) = e ((s : V ≃ₗ[F] V) v) := by
  simp [orthogonalGroupEquivOfSMul]

/-- **Similar quadratic forms have isomorphic special orthogonal groups**: conjugation by an
isometry `e` from `c • Q` to `Q'` carries `SO(Q) = SO(c • Q)` onto `SO(Q')`. -/
noncomputable def specialOrthogonalGroupEquivOfSMul :
    specialOrthogonalGroup Q ≃* specialOrthogonalGroup Q' :=
  (MulEquiv.subgroupCongr (specialOrthogonalGroup_smul c).symm).trans
    e.specialOrthogonalGroupCongr

lemma specialOrthogonalGroupEquivOfSMul_apply (s : specialOrthogonalGroup Q) (v : V) :
    (specialOrthogonalGroupEquivOfSMul c e s : W ≃ₗ[F] W) (e v) = e ((s : V ≃ₗ[F] V) v) := by
  simp [specialOrthogonalGroupEquivOfSMul]

/-- **Similar quadratic forms have isomorphic projective orthogonal groups**: conjugation by an
isometry from `c • Q` to `Q'` carries the scalars of `O(Q)` onto those of `O(Q')`. -/
noncomputable def projectiveOrthogonalGroupEquivOfSMul :
    projectiveOrthogonalGroup Q ≃* projectiveOrthogonalGroup Q' :=
  quotientScalarSubgroupEquiv e.toLinearEquiv (orthogonalGroupEquivOfSMul c e)
    (orthogonalGroupEquivOfSMul_apply c e)

/-- **Similar quadratic forms have isomorphic projective special orthogonal groups**: conjugation
by an isometry from `c • Q` to `Q'` carries the scalars of `SO(Q)` onto those of `SO(Q')`. -/
noncomputable def projectiveSpecialOrthogonalGroupEquivOfSMul :
    projectiveSpecialOrthogonalGroup Q ≃* projectiveSpecialOrthogonalGroup Q' :=
  quotientScalarSubgroupEquiv e.toLinearEquiv (specialOrthogonalGroupEquivOfSMul c e)
    (specialOrthogonalGroupEquivOfSMul_apply c e)

variable [Finite F] [FiniteDimensional F V] {m : ℕ}

/-- **`GO(2m + 1, q)` is unique up to isomorphism** (LMFDB `group.orthogonal`): the orthogonal
group of every nondegenerate quadratic form of dimension `2 m + 1` over `𝔽_q` is isomorphic to that
of the parabolic form. -/
lemma nonempty_orthogonalGroup_mulEquiv_parabolicForm (hQ : Q.Nondegenerate)
    (hV : finrank F V = 2 * m + 1) :
    Nonempty (orthogonalGroup Q ≃* orthogonalGroup (parabolicForm F m)) := by
  rcases exists_equivalent_smul_parabolicForm hQ hV with ⟨c, ⟨e⟩⟩
  exact ⟨orthogonalGroupEquivOfSMul c e⟩

/-- **`SO(2m + 1, q)` is unique up to isomorphism** (LMFDB `group.orthogonal`). -/
lemma nonempty_specialOrthogonalGroup_mulEquiv_parabolicForm (hQ : Q.Nondegenerate)
    (hV : finrank F V = 2 * m + 1) :
    Nonempty (specialOrthogonalGroup Q ≃* specialOrthogonalGroup (parabolicForm F m)) := by
  rcases exists_equivalent_smul_parabolicForm hQ hV with ⟨c, ⟨e⟩⟩
  exact ⟨specialOrthogonalGroupEquivOfSMul c e⟩

/-- **`PGO(2m + 1, q)` is unique up to isomorphism** (LMFDB `group.orthogonal`). -/
lemma nonempty_projectiveOrthogonalGroup_mulEquiv_parabolicForm (hQ : Q.Nondegenerate)
    (hV : finrank F V = 2 * m + 1) :
    Nonempty (projectiveOrthogonalGroup Q ≃* projectiveOrthogonalGroup (parabolicForm F m)) := by
  rcases exists_equivalent_smul_parabolicForm hQ hV with ⟨c, ⟨e⟩⟩
  exact ⟨projectiveOrthogonalGroupEquivOfSMul c e⟩

/-- **`PSO(2m + 1, q)` is unique up to isomorphism** (LMFDB `group.orthogonal`). -/
lemma nonempty_projectiveSpecialOrthogonalGroup_mulEquiv_parabolicForm (hQ : Q.Nondegenerate)
    (hV : finrank F V = 2 * m + 1) : Nonempty (projectiveSpecialOrthogonalGroup Q ≃*
      projectiveSpecialOrthogonalGroup (parabolicForm F m)) := by
  rcases exists_equivalent_smul_parabolicForm hQ hV with ⟨c, ⟨e⟩⟩
  exact ⟨projectiveSpecialOrthogonalGroupEquivOfSMul c e⟩

/-- **`GO^±(2m + 2, q)` are the orthogonal groups in even dimension** (LMFDB `group.orthogonal`):
the orthogonal group of every nondegenerate quadratic form of dimension `2 m + 2` over `𝔽_q` is
isomorphic to that of the hyperbolic (`+`) or of the elliptic (`-`) form. -/
lemma nonempty_orthogonalGroup_mulEquiv_hyperbolicForm_or_ellipticForm (hQ : Q.Nondegenerate)
    (hV : finrank F V = 2 * m + 2) :
    Nonempty (orthogonalGroup Q ≃* orthogonalGroup (hyperbolicForm F (m + 1))) ∨
      Nonempty (orthogonalGroup Q ≃* orthogonalGroup (ellipticForm F m)) :=
  (equivalent_hyperbolicForm_or_equivalent_ellipticForm hQ hV).imp
    (fun ⟨e⟩ ↦ ⟨e.orthogonalGroupCongr⟩) fun ⟨e⟩ ↦ ⟨e.orthogonalGroupCongr⟩

/-- **`SO^±(2m + 2, q)` are the special orthogonal groups in even dimension** (LMFDB
`group.orthogonal`). -/
lemma nonempty_specialOrthogonalGroup_mulEquiv_hyperbolicForm_or_ellipticForm (hQ : Q.Nondegenerate)
    (hV : finrank F V = 2 * m + 2) :
    Nonempty (specialOrthogonalGroup Q ≃* specialOrthogonalGroup (hyperbolicForm F (m + 1))) ∨
      Nonempty (specialOrthogonalGroup Q ≃* specialOrthogonalGroup (ellipticForm F m)) :=
  (equivalent_hyperbolicForm_or_equivalent_ellipticForm hQ hV).imp
    (fun ⟨e⟩ ↦ ⟨e.specialOrthogonalGroupCongr⟩) fun ⟨e⟩ ↦ ⟨e.specialOrthogonalGroupCongr⟩

/-- **`PGO^±(2m + 2, q)` are the projective orthogonal groups in even dimension** (LMFDB
`group.orthogonal`). -/
lemma nonempty_projectiveOrthogonalGroup_mulEquiv_hyperbolicForm_or_ellipticForm
    (hQ : Q.Nondegenerate) (hV : finrank F V = 2 * m + 2) :
    Nonempty (projectiveOrthogonalGroup Q ≃*
      projectiveOrthogonalGroup (hyperbolicForm F (m + 1))) ∨
      Nonempty (projectiveOrthogonalGroup Q ≃* projectiveOrthogonalGroup (ellipticForm F m)) :=
  (equivalent_hyperbolicForm_or_equivalent_ellipticForm hQ hV).imp
    (fun ⟨e⟩ ↦ ⟨quotientScalarSubgroupEquiv e.toLinearEquiv e.orthogonalGroupCongr
      fun s v ↦ by simp⟩)
    fun ⟨e⟩ ↦ ⟨quotientScalarSubgroupEquiv e.toLinearEquiv e.orthogonalGroupCongr
      fun s v ↦ by simp⟩

/-- **`PSO^±(2m + 2, q)` are the projective special orthogonal groups in even dimension** (LMFDB
`group.orthogonal`). -/
lemma nonempty_projectiveSpecialOrthogonalGroup_mulEquiv_hyperbolicForm_or_ellipticForm
    (hQ : Q.Nondegenerate) (hV : finrank F V = 2 * m + 2) :
    Nonempty (projectiveSpecialOrthogonalGroup Q ≃*
      projectiveSpecialOrthogonalGroup (hyperbolicForm F (m + 1))) ∨
      Nonempty (projectiveSpecialOrthogonalGroup Q ≃*
        projectiveSpecialOrthogonalGroup (ellipticForm F m)) :=
  (equivalent_hyperbolicForm_or_equivalent_ellipticForm hQ hV).imp
    (fun ⟨e⟩ ↦ ⟨quotientScalarSubgroupEquiv e.toLinearEquiv e.specialOrthogonalGroupCongr
      fun s v ↦ by simp⟩)
    fun ⟨e⟩ ↦ ⟨quotientScalarSubgroupEquiv e.toLinearEquiv e.specialOrthogonalGroupCongr
      fun s v ↦ by simp⟩

end QuadraticForm
