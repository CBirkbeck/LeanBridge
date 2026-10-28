import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level
import Mathlib.GroupTheory.Index

/-!
# The entanglement index of a subgroup of `GL₂(ℤ̂)`

As in `LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level`, `GL₂(ℤ̂)` is the product
`∏_ℓ GL₂(ℤ_ℓ)`, so the projections of a subgroup `H` to the factors `GL₂(ℤ_ℓ)` are its images
under the coordinate projections. The entanglement index of `H` is its index in the direct product
`G = ∏_ℓ H_ℓ` of these projections, and the entanglement quotient is `G / H` when `H` is normal
in `G`.

## Main definitions

* `Matrix.GeneralLinearGroup.productOfProjections`: the product `∏_ℓ H_ℓ` of the projections of a
  subgroup `H` of `GL₂(ℤ̂)`.
* `Matrix.GeneralLinearGroup.entanglementIndex` (LMFDB `modcurve.entanglement_index`): the
  entanglement index.
* `Matrix.GeneralLinearGroup.EntanglementQuotient` (LMFDB `modcurve.entanglement_index`): the
  entanglement quotient.

## Main results

* `Matrix.GeneralLinearGroup.le_productOfProjections`: a subgroup is contained in the product of its
  projections.
-/

namespace Matrix.GeneralLinearGroup

variable (H : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]))

/-- The **direct product of the projections** `∏_ℓ H_ℓ` of a subgroup `H` of
`GL₂(ℤ̂) = ∏_ℓ GL₂(ℤ_ℓ)`, where `H_ℓ ≤ GL₂(ℤ_ℓ)` is the image of `H` under the `ℓ`-th projection. -/
noncomputable def productOfProjections : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) :=
  Subgroup.pi Set.univ fun ℓ ↦ H.map (Pi.evalMonoidHom _ ℓ)

/-- The **entanglement index** (LMFDB `modcurve.entanglement_index`) of a subgroup `H` of
`GL₂(ℤ̂) = ∏_ℓ GL₂(ℤ_ℓ)`: the index of `H` in the direct product of its projections to the factors
`GL₂(ℤ_ℓ)`. -/
noncomputable def entanglementIndex : ℕ :=
  H.relIndex (productOfProjections H)

/-- The **entanglement quotient** (LMFDB `modcurve.entanglement_index`) of a subgroup `H` of
`GL₂(ℤ̂)`: the quotient `G / H` of the direct product `G` of the projections of `H` to the factors
`GL₂(ℤ_ℓ)`, a group when `H` is normal in `G`. -/
abbrev EntanglementQuotient : Type :=
  productOfProjections H ⧸ H.subgroupOf (productOfProjections H)

/-- **A subgroup of `GL₂(ℤ̂)` is contained in the direct product of its projections.** -/
lemma le_productOfProjections : H ≤ productOfProjections H :=
  fun _ hg _ _ ↦ Subgroup.mem_map_of_mem _ hg

end Matrix.GeneralLinearGroup
