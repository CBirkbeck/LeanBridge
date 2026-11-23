import TauCeti.Geometry.Lie.Exponential.Units.Compatibility
import TauCeti.Geometry.Lie.Subgroup.CartanChart
import TauCeti.Geometry.Lie.Subgroup.Units

/-!
# Closed subgroups of the units of a normed algebra near the identity

Let `R` be a finite-dimensional real normed algebra and `K` a closed subgroup of the Lie group `Rˣ`.
Near the identity, `K` is the image of its Lie algebra under the exponential map, by the local form
of Cartan's closed-subgroup theorem (Tau Ceti's
`TauCeti.Lie.exists_mem_nhds_one_iff_exists_mem_lieSubalgebraOfSubgroup_and_lieExp_eq_of_isClosed`).
Read through the identification of the Lie algebra of `Rˣ` with `R`, the exponential map is the
Banach-algebra exponential `TauCeti.expUnit`, and the Lie algebra of `K` is the set of the `x : R`
whose exponential line `t ↦ exp (t • x)` stays in `K`. So every element of `K` close enough to `1`
is the exponential of such an `x` (`Subgroup.exists_mem_nhds_one_forall_exists_expUnit_eq`).

## Main results

* `Subgroup.exists_mem_nhds_one_forall_exists_expUnit_eq`: near `1`, every element of a closed
  subgroup `K` of `Rˣ` is `exp x` for an `x : R` whose exponential line lies in `K`.
-/

open scoped Manifold Topology

open TauCeti Lie

attribute [local instance] TauCeti.normedAlgebraRatOfReal

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R]

local instance : CompleteSpace R :=
  FiniteDimensional.complete ℝ R

namespace Subgroup

/-- **Near the identity, every element of a closed subgroup `K` of `Rˣ` is the exponential of an
element of its Lie algebra**: of an `x : R` whose exponential line `t ↦ exp (t • x)` lies in `K`.
This is the local form of Cartan's closed-subgroup theorem, read in the algebra `R`. -/
lemma exists_mem_nhds_one_forall_exists_expUnit_eq {K : Subgroup Rˣ} (hK : IsClosed (K : Set Rˣ)) :
    ∃ U ∈ 𝓝 (1 : Rˣ), ∀ k ∈ K, k ∈ U → ∃ x : R, (∀ t : ℝ, expUnit (t • x) ∈ K) ∧ expUnit x = k := by
  rcases exists_mem_nhds_one_iff_exists_mem_lieSubalgebraOfSubgroup_and_lieExp_eq_of_isClosed
    (I := 𝓘(ℝ, R)) hK with ⟨U, hU, hUK⟩
  refine ⟨U, hU, fun k hk hkU ↦ ?_⟩
  rcases (hUK k hkU).mp hk with ⟨X, hX, rfl⟩
  refine ⟨unitsLieAlgebraEquiv X, ?_, (lieExp_eq_expUnit X).symm⟩
  rw [← unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff hK,
    unitsLieAlgebraLieEquiv_symm_apply, LinearEquiv.symm_apply_apply]
  exact hX

end Subgroup
