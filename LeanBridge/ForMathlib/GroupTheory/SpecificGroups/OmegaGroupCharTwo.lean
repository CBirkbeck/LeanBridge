import LeanBridge.ForMathlib.LinearAlgebra.QuadraticForm.DicksonInvariant

/-!
# The groups `Ω^±(2m, q)`, `PΩ^±(2m, q)` and `D(n, q)` for even `q`

For a quadratic form `Q` with nondegenerate polar form on a finite-dimensional vector space over a
field of characteristic `2` (necessarily of even dimension), the group `Ω(Q)` of LMFDB
`group.omega` is the kernel of the knowl's *quasideterminant* `g ↦ (-1) ^ dim ker (g - 1)` on
`SO(Q)`: the elements whose fixed space has even dimension. It is the kernel of the Dickson
invariant (`QuadraticForm.dicksonInvariant`), which is a homomorphism, so `Ω(Q)` is a subgroup,
of index `2` when `Q` is not the zero space. Over `𝔽_q` with `q` even:

* `Ω⁺(2m, q)` is `Ω` of the hyperbolic form `x₁ y₁ + ⋯ + x_m y_m`;
* `Ω⁻(2m + 2, q)` is `Ω` of the elliptic form `x₁ y₁ + ⋯ + x_m y_m + (z² + z w + ζ w²)`;
* `PΩ^±` is the quotient of `Ω^±` by its scalar automorphisms, a trivial subgroup in
  characteristic `2`, so that `PΩ(Q) ≅ Ω(Q)`;
* the Chevalley group `D(n, q)` of LMFDB `group.chevalley` is `Ω⁺(2n, q)`.

In odd dimension the LMFDB takes `Ω(2m + 1, q) = SO(2m + 1, q)` for even `q`: Tau Ceti's
`TauCeti.QuadraticMap.specialOrthogonalGroup` of the parabolic form, which is nondegenerate
(`QuadraticForm.nondegenerate_parabolicForm'`), and `PΩ(2m + 1, q)` is
`QuadraticForm.projectiveSpecialOrthogonalGroup` of that form. For odd `q`, `Ω` is the kernel of
the spinor norm (`QuadraticForm.omegaGroup`).

## Main definitions

* `QuadraticForm.dicksonOmegaGroup` (LMFDB `group.omega`): `Ω(Q)` in characteristic `2`.
* `QuadraticForm.dicksonOmegaPlusGroup`, `QuadraticForm.dicksonOmegaMinusGroup`
  (LMFDB `group.omega`): `Ω⁺(2m, q)` and `Ω⁻(2m + 2, q)` for even `q`.
* `QuadraticForm.projectiveDicksonOmegaGroup` (LMFDB `group.omega`): `PΩ(Q)` in characteristic `2`.
* `QuadraticForm.projectiveDicksonOmegaGroupEquiv`: `PΩ(Q) ≃* Ω(Q)`.
* `QuadraticForm.chevalleyDOfCharTwo` (LMFDB `group.chevalley`): `D(n, q) = Ω⁺(2n, q)` for even `q`.

## Main results

* `QuadraticForm.dicksonOmegaGroup_eq_comap_ker_quasideterminant`: `Ω(Q)` is the kernel of the
  quasideterminant on `SO(Q)`.
* `QuadraticForm.mem_dicksonOmegaGroup_iff`: `g ∈ Ω(Q)` exactly when the fixed space of `g` has
  even dimension.
* `QuadraticForm.index_dicksonOmegaGroup`: `Ω(Q)` has index `2` in `SO(Q)` on a nonzero space, and
  `QuadraticForm.index_dicksonOmegaPlusGroup`, `QuadraticForm.index_dicksonOmegaMinusGroup` for
  `Ω⁺(2m + 2, q)` and `Ω⁻(2m + 2, q)`.
* `QuadraticForm.scalarSubgroup_subgroupOf_dicksonOmegaGroup_eq_bot`: `Ω(Q)` has no scalar
  automorphism other than `1`.
-/

open Module TauCeti QuadraticMap

namespace QuadraticForm

variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V) (hQ : (polarBilin Q).ker = ⊥)

/-- The group **`Ω(Q)`** (LMFDB `group.omega`) of a quadratic form `Q` with nondegenerate polar
form on a finite-dimensional vector space over a field of characteristic `2`: the kernel on
`SO(Q)` of the Dickson invariant, or equivalently of the knowl's quasideterminant
`g ↦ (-1) ^ dim ker (g - 1)` (`QuadraticForm.dicksonOmegaGroup_eq_comap_ker_quasideterminant`,
`QuadraticForm.mem_dicksonOmegaGroup_iff`). Here `SO(Q) = O(Q)`
(`QuadraticForm.specialOrthogonalGroup_eq_orthogonalGroup`). For odd `q`, `Ω` is the kernel of the
spinor norm instead (`QuadraticForm.omegaGroup`): there the knowl's quasideterminant is the
determinant in even dimension, trivial on `SO`. -/
noncomputable def dicksonOmegaGroup : Subgroup (specialOrthogonalGroup Q) :=
  (dicksonInvariant Q hQ).ker.comap (specialOrthogonalToOrthogonal Q)

/-- **`Ω(Q)` is the kernel of the quasideterminant** `g ↦ (-1) ^ dim ker (g - 1)` on `SO(Q)`, as in
LMFDB `group.omega`. -/
lemma dicksonOmegaGroup_eq_comap_ker_quasideterminant :
    dicksonOmegaGroup Q hQ = (quasideterminant Q hQ).ker.comap (specialOrthogonalToOrthogonal Q) :=
  congrArg (Subgroup.comap (specialOrthogonalToOrthogonal Q)) (ker_quasideterminant hQ).symm

variable {Q hQ} in
/-- **`Ω(Q)` is the kernel of the quasideterminant**: an element of `SO(Q)` lies in `Ω(Q)` exactly
when its fixed space has even dimension. -/
lemma mem_dicksonOmegaGroup_iff {g : specialOrthogonalGroup Q} :
    g ∈ dicksonOmegaGroup Q hQ ↔ Even (finrank K ((g : V →ₗ[K] V) - 1).ker) :=
  dicksonInvariant_eq_one_iff hQ (specialOrthogonalGroup_le_orthogonalGroup Q g.2)

/-- **`Ω(Q)` has index `2` in `SO(Q)`** on a nonzero space. -/
lemma index_dicksonOmegaGroup [Nontrivial V] : (dicksonOmegaGroup Q hQ).index = 2 := by
  rw [dicksonOmegaGroup, Subgroup.index_comap_of_surjective _ fun g ↦
    ⟨⟨g, (specialOrthogonalGroup_eq_orthogonalGroup hQ).ge g.2⟩, rfl⟩]
  exact index_ker_dicksonInvariant hQ

/-- The **projective group `PΩ(Q)`** (LMFDB `group.omega`) of a quadratic form `Q` with
nondegenerate polar form over a field of characteristic `2`: the quotient of `Ω(Q)`
(`QuadraticForm.dicksonOmegaGroup`) by its subgroup of scalar automorphisms, which is trivial
(`QuadraticForm.scalarSubgroup_subgroupOf_dicksonOmegaGroup_eq_bot`), so that `PΩ(Q) ≅ Ω(Q)`
(`QuadraticForm.projectiveDicksonOmegaGroupEquiv`). For the hyperbolic and elliptic forms over
`𝔽_q`, `q` even, these are `PΩ⁺(2m, q)` and `PΩ⁻(2m + 2, q)`. -/
abbrev projectiveDicksonOmegaGroup : Type _ :=
  dicksonOmegaGroup Q hQ ⧸ ((LinearEquiv.scalarSubgroup K V).subgroupOf
    (specialOrthogonalGroup Q)).subgroupOf (dicksonOmegaGroup Q hQ)

/-- **`Ω(Q)` has no scalar automorphism other than `1`** in characteristic `2`, since `a² = 1`
forces `a = 1` there. -/
lemma scalarSubgroup_subgroupOf_dicksonOmegaGroup_eq_bot :
    ((LinearEquiv.scalarSubgroup K V).subgroupOf (specialOrthogonalGroup Q)).subgroupOf
      (dicksonOmegaGroup Q hQ) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦ ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hg
  rcases hg with ⟨a, ha⟩
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact Subsingleton.elim _ _
  have hO : DistribMulAction.toModuleAut K V a ∈ orthogonalGroup Q :=
    ha ▸ specialOrthogonalGroup_le_orthogonalGroup Q (g : specialOrthogonalGroup Q).2
  rcases exists_apply_ne_zero hQ with ⟨v, hv⟩
  have ha₂ : (a : K) ^ 2 = 1 :=
    (toModuleAut_mem_orthogonalGroup_iff (fun h : Q = 0 ↦ hv (h ▸ rfl)) a).mp hO
  have ha₁ : ((a : K) - 1) ^ 2 = 0 := by
    linear_combination ha₂ - ((a : K) - 1) * (CharTwo.two_eq_zero : (2 : K) = 0)
  have ha₀ : a = 1 := Units.ext <| sub_eq_zero.mp <| pow_eq_zero_iff two_ne_zero |>.mp ha₁
  rw [ha₀, map_one] at ha
  exact Subtype.ext <| Subtype.ext ha.symm

/-- The isomorphism **`PΩ(Q) ≃* Ω(Q)`** in characteristic `2`, the scalar subgroup of `Ω(Q)` being
trivial. -/
noncomputable def projectiveDicksonOmegaGroupEquiv :
    projectiveDicksonOmegaGroup Q hQ ≃* dicksonOmegaGroup Q hQ :=
  (QuotientGroup.quotientMulEquivOfEq
    (scalarSubgroup_subgroupOf_dicksonOmegaGroup_eq_bot Q hQ)).trans QuotientGroup.quotientBot

variable (K) (m : ℕ)

/-- The group **`Ω⁺(2m, q)`** (LMFDB `group.omega`), for `K = 𝔽_q` with `q` even: `Ω`, the kernel
of the Dickson invariant on `SO`, of the hyperbolic form `x₁ y₁ + ⋯ + x_m y_m`, whose polar form is
nondegenerate. -/
noncomputable abbrev dicksonOmegaPlusGroup :
    Subgroup (specialOrthogonalGroup (hyperbolicForm K m)) :=
  dicksonOmegaGroup (hyperbolicForm K m) (ker_polarBilin_hyperbolicForm K m)

/-- The Chevalley group **`D(m, q) = Ω⁺(2m, q)`** (LMFDB `group.chevalley`), for `K = 𝔽_q` with
`q` even: the kernel of the Dickson invariant on the special orthogonal group of the hyperbolic
form `x₁ y₁ + ⋯ + x_m y_m`. -/
noncomputable abbrev chevalleyDOfCharTwo : Subgroup (specialOrthogonalGroup (hyperbolicForm K m)) :=
  dicksonOmegaPlusGroup K m

/-- **`Ω⁺(2m + 2, q)` has index `2` in `SO⁺(2m + 2, q)`** for even `q`. -/
lemma index_dicksonOmegaPlusGroup : (dicksonOmegaPlusGroup K (m + 1)).index = 2 :=
  index_dicksonOmegaGroup _ _

variable [Finite K]

/-- The group **`Ω⁻(2m + 2, q)`** (LMFDB `group.omega`), for `K = 𝔽_q` with `q` even: `Ω`, the
kernel of the Dickson invariant on `SO`, of the elliptic form
`x₁ y₁ + ⋯ + x_m y_m + (z² + z w + ζ w²)`, whose polar form is nondegenerate. -/
noncomputable abbrev dicksonOmegaMinusGroup :
    Subgroup (specialOrthogonalGroup (ellipticForm K m)) :=
  dicksonOmegaGroup (ellipticForm K m)
    (ker_polarBilin_prod (ker_polarBilin_hyperbolicForm K m) (ker_polarBilin_anisotropicPlane K))

/-- **`Ω⁻(2m + 2, q)` has index `2` in `SO⁻(2m + 2, q)`** for even `q`. -/
lemma index_dicksonOmegaMinusGroup : (dicksonOmegaMinusGroup K m).index = 2 :=
  index_dicksonOmegaGroup _ _

end QuadraticForm
