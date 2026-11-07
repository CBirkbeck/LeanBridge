import LeanBridge.ForMathlib.LinearAlgebra.Lattice.Sublattice

/-!
# The even sublattice of an integral lattice

The even sublattice `L₀` of an integral lattice `L` (LMFDB `lattice.even_sublattice`) is generated
by the vectors of even norm (`TauCeti.IntegralLattice.span_setOf_even_integralNorm`), which form
Tau Ceti's submodule `TauCeti.IntegralLattice.evenSubmodule` of the carrier of `L`, and Tau Ceti's
`TauCeti.IntegralLattice.evenSublattice` is the corresponding integral lattice. The knowl says
"vectors of even length", where the norm is meant: the root lattice `A₂` is even but has no
nonzero vector of even Euclidean length, its nonzero norms `2(a² - ab + b²)` never being of the
form `4k²`.

`L` is even exactly when it is its own even sublattice, and `L₀` has index at most `2` in `L`:
index `1` for an even lattice and index `2` for an odd one
(`TauCeti.IntegralLattice.natCard_quotient_evenSubmodule`). The index bound is Tau Ceti main's
`relIndex_evenSublattice_le_two`, not at the pin; it is a few lines from the pin, proved here, to
be replaced after the bump.

## Main results

* `TauCeti.IntegralLattice.isEven_iff_evenSubmodule_eq_top`: `L` is even exactly when all its
  vectors have even norm.
* `TauCeti.IntegralLattice.isEven_iff_evenSublattice_eq` (LMFDB `lattice.even_sublattice`): `L`
  is even exactly when it is equal to its even sublattice.
* `TauCeti.IntegralLattice.natCard_quotient_evenSubmodule_le_two` (LMFDB
  `lattice.even_sublattice`): the even sublattice has index at most `2`.
-/

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- **An integral lattice is even exactly when all its vectors have even norm**, that is, when Tau
Ceti's `TauCeti.IntegralLattice.evenSubmodule` is the whole carrier. -/
lemma isEven_iff_evenSubmodule_eq_top : L.IsEven ↔ L.evenSubmodule = ⊤ :=
  (Submodule.eq_top_iff'.trans <| forall_congr' L.mem_evenSubmodule_iff).symm

/-- **An integral lattice is even exactly when it is equal to its even sublattice** (LMFDB
`lattice.even_sublattice`), Tau Ceti's `TauCeti.IntegralLattice.evenSublattice`. -/
lemma isEven_iff_evenSublattice_eq : L.IsEven ↔ L.evenSublattice = L := by
  rw [isEven_iff_evenSubmodule_eq_top]
  refine ⟨fun h ↦ ext ?_ L.evenSublattice_form, fun h ↦ ?_⟩
  · rw [evenSublattice_carrier, h, Submodule.map_top, Submodule.range_subtype]
  · rw [← evenSublattice_carrier_submoduleOf, h, Submodule.submoduleOf_self]

/-- **The even sublattice of an integral lattice `L` has index at most `2` in `L`** (LMFDB
`lattice.even_sublattice`): index `1` if `L` is even, `2` otherwise. This is Tau Ceti main's
`relIndex_evenSublattice_le_two`, not at the pin. -/
lemma natCard_quotient_evenSubmodule_le_two : Nat.card (L ⧸ L.evenSubmodule) ≤ 2 := by
  by_cases hL : L.IsEven
  · rw [(isEven_iff_evenSubmodule_eq_top L).mp hL]
    simp
  · exact (L.natCard_quotient_evenSubmodule hL).le

end TauCeti.IntegralLattice
