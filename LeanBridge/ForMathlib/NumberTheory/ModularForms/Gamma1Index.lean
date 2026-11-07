import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Totient
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The index of `Γ₁(N)` in `SL₂(ℤ)`

The group `Γ₁(N)` is the kernel of the surjective homomorphism `Γ₀(N) → (ℤ/Nℤ)ˣ` to the lower
right entry, so `[Γ₀(N) : Γ₁(N)] = φ(N)` and `[SL₂(ℤ) : Γ₁(N)] = [SL₂(ℤ) : Γ₀(N)] φ(N)` for
`N ≥ 1`. With Tau Ceti's `[SL₂(ℤ) : Γ₀(pᵏ)] = p ^ (k - 1) (p + 1)`, this gives the index
`[SL₂(ℤ) : Γ₁(N)] = N ^ 2 ∏_{p ∣ N} (1 - 1 / p ^ 2)` in the LMFDB's Sturm bound
`⌊k [SL₂(ℤ) : Γ₁(N)] / 12⌋` (LMFDB `cmf.sturm_bound_gamma1`) at prime power levels `N = pᵏ`. At
the other levels it follows in the same way from Dedekind's formula
`[SL₂(ℤ) : Γ₀(N)] = N ∏_{p ∣ N} (1 + 1 / p)`, which is on Tau Ceti's main
(`CongruenceSubgroup.Gamma0_index_mul_prod_primeFactors`) but not at LeanBridge's pin of Tau Ceti.

## Main results

* `CongruenceSubgroup.relIndex_Gamma1_Gamma0`: `[Γ₀(N) : Γ₁(N)] = φ(N)` for `N ≥ 1`.
* `CongruenceSubgroup.index_Gamma1`: `[SL₂(ℤ) : Γ₁(N)] = [SL₂(ℤ) : Γ₀(N)] φ(N)` for `N ≥ 1`.
* `CongruenceSubgroup.index_Gamma1_of_isPrimePow` (LMFDB `cmf.sturm_bound_gamma1`):
  `[SL₂(ℤ) : Γ₁(N)] = N ^ 2 ∏_{p ∣ N} (1 - 1 / p ^ 2)` for a prime power `N`.
-/

namespace CongruenceSubgroup

variable {N : ℕ}

lemma Gamma1_subgroupOf_Gamma0 :
    (Gamma1 N).subgroupOf (Gamma0 N) = (Gamma0Map N).toHomUnits.ker := by
  ext g
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, mem_Gamma1_iff_toHomUnits_eq_one]

/-- **`[Γ₀(N) : Γ₁(N)] = φ(N)`** for `N ≥ 1`: `Γ₁(N)` is the kernel of the surjective homomorphism
`Γ₀(N) → (ℤ/Nℤ)ˣ` to the lower right entry. -/
lemma relIndex_Gamma1_Gamma0 [NeZero N] : (Gamma1 N).relIndex (Gamma0 N) = N.totient := by
  rw [Subgroup.relIndex, Gamma1_subgroupOf_Gamma0, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr Gamma0Map_toHomUnits_surjective, Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- **`[SL₂(ℤ) : Γ₁(N)] = [SL₂(ℤ) : Γ₀(N)] φ(N)`** for `N ≥ 1`. -/
lemma index_Gamma1 [NeZero N] : (Gamma1 N).index = (Gamma0 N).index * N.totient := by
  rw [← Subgroup.relIndex_mul_index (Gamma1_in_Gamma0 N), relIndex_Gamma1_Gamma0, mul_comm]

/-- **The index of `Γ₁(N)` at a prime power level** (LMFDB `cmf.sturm_bound_gamma1`):
`[SL₂(ℤ) : Γ₁(N)] = N ^ 2 ∏_{p ∣ N} (1 - 1 / p ^ 2)` when `N` is a prime power. -/
lemma index_Gamma1_of_isPrimePow (hN : IsPrimePow N) :
    ((Gamma1 N).index : ℚ) = (N : ℚ) ^ 2 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  rcases (isPrimePow_nat_iff N).mp hN with ⟨p, k, hp, hk, rfl⟩
  have : NeZero (p ^ k) :=
    ⟨pow_ne_zero k hp.ne_zero⟩
  rw [index_Gamma1, Gamma0_prime_power_index p hp k hk, Nat.totient_prime_pow hp hk,
    Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton]
  rcases Nat.exists_eq_add_one_of_ne_zero hk.ne' with ⟨j, rfl⟩
  have hp₀ : (p : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hp.ne_zero
  push_cast [hp.one_le]
  field_simp
  ring1

end CongruenceSubgroup
