import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# Orthogonal groups

The orthogonal group `O(Q)` of a quadratic form `Q` on a vector space `V` over a field `F` is the
group of linear automorphisms of `V` preserving `Q`, and its special orthogonal group `SO(Q)` is its
subgroup of automorphisms of determinant `1`; they are Tau Ceti's
`TauCeti.QuadraticMap.orthogonalGroup` and `TauCeti.QuadraticMap.specialOrthogonalGroup`, which a
basis of `V` turns into subgroups of `GL_n(F)` (`TauCeti.QuadraticMap.orthogonalToGeneralLinear`).
This file adds the projective versions, the quotients by the scalar automorphisms. A scalar `a`
lies in `O(Q)` exactly when `a² = 1`, if `Q ≠ 0`, and in `SO(Q)` when moreover `aⁿ = 1`, `n` the
dimension: so `PGO(Q) = O(Q) / {±1}`, while `PSO(Q) = SO(Q) / {±1}` in even dimension and
`PSO(Q) = SO(Q)` in odd dimension; in characteristic `2`, where `-1 = 1`, `PGO(Q) = O(Q)` and
`PSO(Q) = SO(Q)`. This is the table of the LMFDB knowl.

Over a finite field `F = 𝔽_q`, the LMFDB names the orthogonal groups of the standard forms:

* `GO(2m + 1, q)`, `SO(2m + 1, q)`, `PGO(2m + 1, q)`, `PSO(2m + 1, q)` are the groups `O`, `SO`,
  `PGO` and `PSO` of `QuadraticForm.parabolicForm F m`;
* `GO⁺(2m, q)` and its relatives are those of `QuadraticForm.hyperbolicForm F m`;
* `GO⁻(2m + 2, q)` and its relatives are those of `QuadraticForm.ellipticForm F m`.

Here the elliptic form uses a chosen `ζ ∈ F` for which `t² + t + ζ` has no root in `F`
(`QuadraticForm.anisotropicCoeff`), so that its last plane is anisotropic
(`QuadraticForm.anisotropic_anisotropicPlane`). That these forms represent the classes of
nondegenerate quadratic forms over `𝔽_q` up to similarity (one class in odd dimension, two in even
dimension), so that the groups do not depend on these choices up to isomorphism, is not proved
here. In odd dimension and odd characteristic there are two isometry classes, which are similar:
the knowl's "one equivalence class" holds for similarity, which is what makes `GO(n, q)` unique.

## Main definitions

* `LinearEquiv.scalarSubgroup`: the scalar automorphisms of a vector space.
* `QuadraticForm.projectiveOrthogonalGroup` (LMFDB `group.orthogonal`): `PGO(Q)`.
* `QuadraticForm.projectiveSpecialOrthogonalGroup` (LMFDB `group.orthogonal`): `PSO(Q)`.
* `QuadraticForm.hyperbolicForm`, `QuadraticForm.ellipticForm`, `QuadraticForm.parabolicForm`
  (LMFDB `group.orthogonal`): the `+`, `-` and odd-dimensional forms over a finite field.
* `QuadraticForm.anisotropicCoeff`, `QuadraticForm.anisotropicPlane`: the anisotropic plane
  `x² + x y + ζ y²` completing the elliptic form.

## Main results

* `QuadraticForm.toModuleAut_mem_orthogonalGroup_iff`: the scalar `a` lies in `O(Q)` exactly when
  `a² = 1`, for `Q ≠ 0`.
* `QuadraticForm.toModuleAut_mem_specialOrthogonalGroup_iff`: it lies in `SO(Q)` exactly when
  moreover `aⁿ = 1`, `n` the dimension.
* `QuadraticForm.anisotropic_anisotropicPlane`: the plane completing the elliptic form is
  anisotropic.
-/

open TauCeti.QuadraticMap

namespace LinearEquiv

variable (F V : Type*) [Field F] [AddCommGroup V] [Module F V]

/-- The **scalar automorphisms** `v ↦ a • v`, `a ∈ Fˣ`, of a vector space `V` over `F`: the scalar
matrices of `GL(V)`. -/
abbrev scalarSubgroup : Subgroup (V ≃ₗ[F] V) :=
  (DistribMulAction.toModuleAut F V : Fˣ →* V ≃ₗ[F] V).range

variable {F V}

lemma commute_of_mem_scalarSubgroup {s : V ≃ₗ[F] V} (hs : s ∈ scalarSubgroup F V) (f : V ≃ₗ[F] V) :
    Commute s f := by
  rcases hs with ⟨a, rfl⟩
  exact LinearEquiv.ext fun v ↦ (f.map_smul_of_tower (a : F) v).symm

instance (H : Subgroup (V ≃ₗ[F] V)) : ((scalarSubgroup F V).subgroupOf H).Normal where
  conj_mem s hs g := by
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, ← (commute_of_mem_scalarSubgroup hs g).eq,
      Subgroup.coe_inv, mul_inv_cancel_right]

end LinearEquiv

namespace QuadraticForm

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] (Q : QuadraticForm F V) (m : ℕ)

/-- The **projective orthogonal group** `PGO(Q)` (LMFDB `group.orthogonal`): the quotient of the
orthogonal group `O(Q)` (Tau Ceti's `TauCeti.QuadraticMap.orthogonalGroup`) by its subgroup of
scalar automorphisms, which is `{±1}` when `Q ≠ 0`
(`QuadraticForm.toModuleAut_mem_orthogonalGroup_iff`). -/
abbrev projectiveOrthogonalGroup : Type _ :=
  orthogonalGroup Q ⧸ (LinearEquiv.scalarSubgroup F V).subgroupOf (orthogonalGroup Q)

/-- The **projective special orthogonal group** `PSO(Q)` (LMFDB `group.orthogonal`): the quotient
of the special orthogonal group `SO(Q)` (Tau Ceti's `TauCeti.QuadraticMap.specialOrthogonalGroup`)
by its subgroup of scalar automorphisms. -/
abbrev projectiveSpecialOrthogonalGroup : Type _ :=
  specialOrthogonalGroup Q ⧸ (LinearEquiv.scalarSubgroup F V).subgroupOf (specialOrthogonalGroup Q)

variable {Q} (hQ : Q ≠ 0) (a : Fˣ)

include hQ in
/-- **The scalar automorphisms of a nonzero quadratic form are `±1`**: the scalar `a` preserves
`Q ≠ 0` exactly when `a² = 1`. -/
lemma toModuleAut_mem_orthogonalGroup_iff :
    DistribMulAction.toModuleAut F V a ∈ orthogonalGroup Q ↔ (a : F) ^ 2 = 1 := by
  simp only [mem_orthogonalGroup_iff, DistribMulAction.toModuleAut_apply,
    DistribMulAction.toLinearEquiv_apply, Units.smul_def, QuadraticMap.map_smul, smul_eq_mul]
  refine ⟨fun h ↦ ?_, fun h v ↦ by rw [← sq, h, one_mul]⟩
  rcases DFunLike.ne_iff.mp hQ with ⟨v, hv⟩
  rw [sq]
  exact mul_right_cancel₀ hv ((h v).trans (one_mul _).symm)

include hQ in
/-- **The scalar special orthogonal automorphisms**: the scalar `a` lies in `SO(Q)`, for `Q ≠ 0`,
exactly when `a² = 1` and `aⁿ = 1`, `n` the dimension. -/
lemma toModuleAut_mem_specialOrthogonalGroup_iff :
    DistribMulAction.toModuleAut F V a ∈ specialOrthogonalGroup Q ↔ (a : F) ^ 2 = 1 ∧
      (a : F) ^ Module.finrank F V = 1 := by
  have ha : (DistribMulAction.toModuleAut F V a : V →ₗ[F] V) = (a : F) • LinearMap.id := by
    ext
    simp [Units.smul_def]
  rw [mem_specialOrthogonalGroup_iff, toModuleAut_mem_orthogonalGroup_iff hQ, Units.ext_iff,
    LinearEquiv.coe_det, ha, LinearMap.det_smul, LinearMap.det_id, mul_one, Units.val_one]

variable (F)

/-- The **hyperbolic form** `x₁ y₁ + ⋯ + x_m y_m` on `(F × F) ^ m`, of dimension `2 m` and Witt
index `m`: the quadratic form of `+` type. -/
def hyperbolicForm : QuadraticForm F (Fin m → F × F) :=
  QuadraticMap.pi fun _ ↦ QuadraticMap.linMulLin (LinearMap.fst F F F) (LinearMap.snd F F F)

/-- The **parabolic form** `z² + x₁ y₁ + ⋯ + x_m y_m` on `F × (F × F) ^ m`, of dimension
`2 m + 1`. -/
def parabolicForm : QuadraticForm F (F × (Fin m → F × F)) :=
  QuadraticMap.sq.prod (hyperbolicForm F m)

variable [Finite F]

variable {F} in
lemma exists_forall_sq_add_add_ne_zero : ∃ ζ : F, ∀ t : F, t ^ 2 + t + ζ ≠ 0 := by
  have h : ¬Function.Surjective fun t : F ↦ t ^ 2 + t := by
    rw [← Finite.injective_iff_surjective]
    intro h
    exact one_ne_zero <| neg_eq_zero.mp (h (by ring1 : (0 : F) ^ 2 + 0 = (-1) ^ 2 + -1)).symm
  rcases not_forall.mp h with ⟨c, hc⟩
  exact ⟨-c, fun t ht ↦ hc ⟨t, by linear_combination ht⟩⟩

/-- An element `ζ` of the finite field `F` such that `t² + t + ζ` has no root in `F`, chosen once
and for all: the coefficient of the anisotropic plane `x² + x y + ζ y²`. -/
noncomputable def anisotropicCoeff : F :=
  exists_forall_sq_add_add_ne_zero.choose

lemma sq_add_add_anisotropicCoeff_ne_zero (t : F) : t ^ 2 + t + anisotropicCoeff F ≠ 0 :=
  exists_forall_sq_add_add_ne_zero.choose_spec t

/-- The **anisotropic plane** `x² + x y + ζ y²` on `F × F`, for the element
`ζ = QuadraticForm.anisotropicCoeff F` of the finite field `F`, chosen so that `t² + t + ζ` has no
root in `F`. -/
noncomputable def anisotropicPlane : QuadraticForm F (F × F) :=
  QuadraticMap.sq.comp (LinearMap.fst F F F) +
    QuadraticMap.linMulLin (LinearMap.fst F F F) (LinearMap.snd F F F) +
      anisotropicCoeff F • QuadraticMap.sq.comp (LinearMap.snd F F F)

lemma anisotropicPlane_apply (x : F × F) :
    anisotropicPlane F x = x.1 ^ 2 + x.1 * x.2 + anisotropicCoeff F * x.2 ^ 2 := by
  simp [anisotropicPlane, sq]

/-- **The plane `x² + x y + ζ y²` is anisotropic**: it represents `0` only at `0`, since
`t² + t + ζ` has no root in `F`. -/
lemma anisotropic_anisotropicPlane : (anisotropicPlane F).Anisotropic := by
  rintro ⟨a, b⟩ h
  rw [anisotropicPlane_apply] at h
  by_cases hb : b = 0
  · subst hb
    simpa using h
  · refine absurd ?_ (sq_add_add_anisotropicCoeff_ne_zero F (a / b))
    field_simp
    linear_combination h

/-- The **elliptic form** `x₁ y₁ + ⋯ + x_m y_m + (z² + z w + ζ w²)` on `(F × F) ^ m × (F × F)`, of
dimension `2 m + 2` and Witt index `m`: the quadratic form of `-` type. -/
noncomputable def ellipticForm : QuadraticForm F ((Fin m → F × F) × (F × F)) :=
  (hyperbolicForm F m).prod (anisotropicPlane F)

end QuadraticForm
