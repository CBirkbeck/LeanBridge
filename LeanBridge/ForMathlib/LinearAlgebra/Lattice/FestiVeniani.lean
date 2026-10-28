import Mathlib.GroupTheory.Index
import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Group
import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group

/-!
# The Festi–Veniani index of an integral lattice

Every isometry of an integral lattice `L` induces an automorphism of its discriminant group
`L^∨ / L`. The Festi–Veniani index of `L` is the index of the image of the automorphism group
`O(L)` of `L` in the automorphism group of `L^∨ / L`.

## Main definitions

* `TauCeti.IntegralLattice.discriminantGroupAction`: the action of `O(L)` on `L^∨ / L`.
* `TauCeti.IntegralLattice.festiVenianiIndex` (LMFDB `lattice.festi_veniani_index`).

## Main results

* `TauCeti.IntegralLattice.festiVenianiIndex_ne_zero`: the Festi–Veniani index of a nondegenerate
  lattice is finite.
-/

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- The **action** of the automorphism group `O(L)` of an integral lattice `L` (LMFDB
`lattice.automorphism_group`) on its discriminant group `L^∨ / L` (LMFDB
`lattice.discriminant_group`): an isometry `e` of `L` acts by
`TauCeti.IntegralLattice.Isometry.discriminantGroupEquiv`, `u + L ↦ e(u) + L`. The automorphisms
of the abelian group `L^∨ / L` are its `ℤ`-linear automorphisms. -/
def discriminantGroupAction : Isometry L L →* (L.DiscriminantGroup ≃ₗ[ℤ] L.DiscriminantGroup) where
  toFun e := e.discriminantGroupEquiv
  map_one' := by
    rw [Isometry.one_def, Isometry.discriminantGroupEquiv_refl]
    rfl
  map_mul' f g := by
    rw [Isometry.mul_def, Isometry.discriminantGroupEquiv_trans]
    rfl

/-- The **Festi–Veniani index** (LMFDB `lattice.festi_veniani_index`) of an integral lattice `L`:
the index of the image of its automorphism group `O(L)` in the automorphism group of its
discriminant group `L^∨ / L`, or `0` if the index is infinite. The LMFDB takes all group
automorphisms of `L^∨ / L`; Festi and Veniani take the isometries of the discriminant form instead. -/
noncomputable def festiVenianiIndex : ℕ :=
  L.discriminantGroupAction.range.index

/-- **The Festi–Veniani index of a nondegenerate lattice is finite.** -/
lemma festiVenianiIndex_ne_zero [L.IsNondegenerate] : L.festiVenianiIndex ≠ 0 :=
  have : Finite (L.DiscriminantGroup ≃ₗ[ℤ] L.DiscriminantGroup) :=
    .of_injective _ DFunLike.coe_injective
  Subgroup.index_ne_zero_of_finite

end TauCeti.IntegralLattice
