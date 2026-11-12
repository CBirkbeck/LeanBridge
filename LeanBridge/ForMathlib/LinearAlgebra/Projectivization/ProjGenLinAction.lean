import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# `PGL(n, K)` as the group of linear automorphisms of projective space

The projective general linear group `PGL(n, K) = GL(n, K) / {scalars}`, Mathlib's
`Matrix.ProjGenLinGroup`, acts on the projective space `ℙ(Kⁿ)` of lines in `Kⁿ`, which has
dimension `n - 1` (LMFDB `group.linear`). The action is faithful: an invertible matrix fixing every
line has every nonzero vector as an eigenvector, so it is a scalar matrix. Hence `PGL(n, K)` is
isomorphic to the group of the permutations of `ℙ(Kⁿ) = ℙ^{n-1}(K)` induced by the invertible
linear maps of `Kⁿ`, the linear automorphisms of `ℙ^{n-1}(K)`; the LMFDB's "projective `n`-space"
is off by one.

## Main definitions

* `Matrix.ProjGenLinGroup.mulEquivRangeToPermHom` (LMFDB `group.linear`): the isomorphism of
  `PGL(n, K)` with the group of linear automorphisms of `ℙ(Kⁿ)`.

## Main results

* `Matrix.ProjGenLinGroup.toPermHom_injective` (LMFDB `group.linear`): `PGL(n, K)` acts faithfully
  on `ℙ(Kⁿ)`.
* `Matrix.ProjGenLinGroup.range_toPermHom` (LMFDB `group.linear`): the permutations of `ℙ(Kⁿ)`
  given by `PGL(n, K)` are those given by `GL(n, K)`.
-/

open MulAction Projectivization

open scoped LinearAlgebra.Projectivization MatrixGroups

namespace Matrix.ProjGenLinGroup

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

lemma mem_center_of_forall_mk_smul_eq {A : GL ι K}
    (hA : ∀ x : ℙ K (ι → K), (mk A : PGL(ι, K)) • x = x) : A ∈ Subgroup.center (GL ι K) := by
  rcases (toLin' (A : Matrix ι ι K)).exists_eq_smul_id_of_forall_notLinearIndependent fun v ↦ by
      by_cases hv : v = 0
      · simp [hv, linearIndependent_fin2]
      · simpa [LinearIndependent.pair_iff' hv, Projectivization.mk_eq_mk_iff'] using!
          hA (.mk K v hv) with ⟨a, ha⟩
  have hscalar : (A : Matrix ι ι K) = a • (1 : Matrix ι ι K) := by
    rw [← LinearMap.toMatrix'_toLin' (A : Matrix ι ι K), ha, map_smul, LinearMap.toMatrix'_one]
  refine Subgroup.mem_center_iff.mpr fun B ↦ Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hscalar, Matrix.mul_smul, mul_one, smul_mul, one_mul]

/-- **`PGL(n, K)` acts faithfully on the projective space `ℙ(Kⁿ)`** (LMFDB `group.linear`): an
invertible matrix fixing every line of `Kⁿ` is scalar, so it is trivial in `PGL(n, K)`. -/
lemma toPermHom_injective : Function.Injective (toPermHom PGL(ι, K) (ℙ K (ι → K))) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  induction g using ProjGenLinGroup.induction_on with | mk A => ?_
  exact mk_eq_one.mpr <| mem_center_of_forall_mk_smul_eq fun x ↦ congrArg (· x) hg

instance : FaithfulSMul PGL(ι, K) (ℙ K (ι → K)) :=
  ⟨fun h ↦ toPermHom_injective (Equiv.ext h)⟩

/-- **The permutations of `ℙ(Kⁿ)` given by `PGL(n, K)` are the linear automorphisms**, those given
by `GL(n, K)` (LMFDB `group.linear`). -/
lemma range_toPermHom :
    (toPermHom PGL(ι, K) (ℙ K (ι → K))).range = (toPermHom (GL ι K) (ℙ K (ι → K))).range := by
  ext σ
  refine ⟨?_, ?_⟩
  · rintro ⟨g, rfl⟩
    induction g using ProjGenLinGroup.induction_on with | mk A => exact ⟨A, rfl⟩
  · rintro ⟨A, rfl⟩
    exact ⟨mk A, rfl⟩

variable (ι K) in
/-- **`PGL(n, K)` is the group of linear automorphisms of `ℙ^{n-1}(K) = ℙ(Kⁿ)`** (LMFDB
`group.linear`): the isomorphism with the group of the permutations of `ℙ(Kⁿ)` induced by
invertible linear maps of `Kⁿ`, through the faithful action of `PGL(n, K)`. -/
noncomputable def mulEquivRangeToPermHom : PGL(ι, K) ≃* (toPermHom (GL ι K) (ℙ K (ι → K))).range :=
  (MonoidHom.ofInjective toPermHom_injective).trans (MulEquiv.subgroupCongr range_toPermHom)

end Matrix.ProjGenLinGroup
