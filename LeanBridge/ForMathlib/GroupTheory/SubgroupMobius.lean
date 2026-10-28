import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Data.Fintype.Powerset

/-!
# Möbius functions of the subgroup lattice and of the normal subgroup lattice

## Main definitions

* `Subgroup.mobius` and `Subgroup.normalMobius` (LMFDB `group.mobius_function`).

## Main results

* `Subgroup.mobius_eq_neg_finsum`: `μ_G(H) = -∑_{H' > H} μ_G(H')` for `H ≠ G`.
* `Subgroup.normalMobius_eq_neg_finsum`: `ν_G(N) = -∑_{N' < N} ν_G(N')` for `N ≠ 1`.
-/

open IncidenceAlgebra

variable {G : Type*} [Group G] [Finite G]

namespace Subgroup

lemma finite_subgroup : Finite (Subgroup G) :=
  .of_injective _ SetLike.coe_injective

/-- The **Möbius subgroup function** (LMFDB `group.mobius_function`) `μ_G(H)` of a finite group,
the Möbius function `μ(H, G)` of the lattice of subgroups of `G`. It is determined by
`μ_G(G) = 1` and `μ_G(H) = -∑_{H' > H} μ_G(H')`. -/
noncomputable def mobius (H : Subgroup G) : ℤ :=
  haveI : Finite (Subgroup G) := finite_subgroup
  letI : LocallyFiniteOrder (Subgroup G) := .ofFiniteIcc fun _ _ ↦ Set.toFinite _
  letI : DecidableEq (Subgroup G) := Classical.decEq _
  mu ℤ H ⊤

/-- The **Möbius quotient function** (LMFDB `group.mobius_function`) `ν_G(N)` of a finite group,
the Möbius function `μ(1, N)` of the lattice of normal subgroups of `G`. It is determined by
`ν_G(1) = 1` and `ν_G(N) = -∑_{N' < N} ν_G(N')`. -/
noncomputable def normalMobius (N : {N : Subgroup G // N.Normal}) : ℤ :=
  haveI : Finite (Subgroup G) := finite_subgroup
  letI : LocallyFiniteOrder {N : Subgroup G // N.Normal} := .ofFiniteIcc fun _ _ ↦ Set.toFinite _
  letI : DecidableEq {N : Subgroup G // N.Normal} := Classical.decEq _
  mu ℤ ⟨⊥, normal_bot⟩ N

lemma mobius_top : mobius (⊤ : Subgroup G) = 1 := by
  have hf : Finite (Subgroup G) := finite_subgroup
  let hl : LocallyFiniteOrder (Subgroup G) := .ofFiniteIcc fun _ _ ↦ Set.toFinite _
  let hd : DecidableEq (Subgroup G) := Classical.decEq _
  exact mu_self _

/-- The recursion of LMFDB `group.mobius_function` for the Möbius subgroup function. -/
lemma mobius_eq_neg_finsum {H : Subgroup G} (hH : H ≠ ⊤) :
    mobius H = -∑ᶠ K ∈ Set.Ioi H, mobius K := by
  have hf : Finite (Subgroup G) := finite_subgroup
  let hl : LocallyFiniteOrder (Subgroup G) := .ofFiniteIcc fun _ _ ↦ Set.toFinite _
  let hd : DecidableEq (Subgroup G) := Classical.decEq _
  rw [mobius, mu_eq_neg_sum_Ioc_of_ne hH, ← finsum_mem_coe_finset, Finset.coe_Ioc, Set.Ioc_top]
  rfl

lemma normalMobius_bot : normalMobius (⟨⊥, normal_bot⟩ : {N : Subgroup G // N.Normal}) = 1 := by
  have hf : Finite (Subgroup G) := finite_subgroup
  let hl : LocallyFiniteOrder {N : Subgroup G // N.Normal} :=
    .ofFiniteIcc fun _ _ ↦ Set.toFinite _
  let hd : DecidableEq {N : Subgroup G // N.Normal} := Classical.decEq _
  exact mu_self _

/-- The recursion of LMFDB `group.mobius_function` for the Möbius quotient function. -/
lemma normalMobius_eq_neg_finsum {N : {N : Subgroup G // N.Normal}} (hN : N ≠ ⟨⊥, normal_bot⟩) :
    normalMobius N = -∑ᶠ K ∈ Set.Iio N, normalMobius K := by
  have hf : Finite (Subgroup G) := finite_subgroup
  let hl : LocallyFiniteOrder {N : Subgroup G // N.Normal} :=
    .ofFiniteIcc fun _ _ ↦ Set.toFinite _
  let hd : DecidableEq {N : Subgroup G // N.Normal} := Classical.decEq _
  have hI : Set.Ico (⟨⊥, normal_bot⟩ : {N : Subgroup G // N.Normal}) N = Set.Iio N :=
    Set.ext fun K ↦ and_iff_right (bot_le (a := K.1))
  rw [normalMobius, mu_eq_neg_sum_Ico_of_ne hN.symm, ← finsum_mem_coe_finset, Finset.coe_Ico, hI]
  rfl

end Subgroup
