import TauCeti.LinearAlgebra.IntegralLattice.Level

/-!
# The level of an integral lattice and the exponent of its discriminant group

The level `N` of a nondegenerate integral lattice `L` is the least positive integer such that
`N · B(v, v)` is even for every `v` in the dual lattice `Lᵛ` (Tau Ceti's
`TauCeti.IntegralLattice.level`), and Tau Ceti proves that the exponent `e` of the discriminant
group `Lᵛ/L` divides `N`. This file proves that `N` divides `2e`, so that either `N = e` or `N = 2e`
(LMFDB `lattice.level`): for `v ∈ Lᵛ` the vector `e v` lies in `L`, so `e B(v, v) = B(e v, v)` is
an integer.

## Main results

* `TauCeti.IntegralLattice.level_dvd_two_mul_exponent`: the level divides twice the exponent of the
  discriminant group.
* `TauCeti.IntegralLattice.level_eq_exponent_or_eq_two_mul_exponent`: the level is the exponent of
  the discriminant group or twice it (LMFDB `lattice.level`).
-/

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- **The level divides twice the exponent of the discriminant group.** -/
lemma level_dvd_two_mul_exponent :
    (L.level : ℤ) ∣ 2 * (AddMonoid.exponent L.DiscriminantGroup : ℤ) := by
  refine (L.level_dvd_iff _).mpr fun x hx ↦ ?_
  have hmem : AddMonoid.exponent L.DiscriminantGroup • x ∈ L.carrier := by
    have h := AddMonoid.exponent_nsmul_eq_zero
      (Submodule.Quotient.mk (⟨x, hx⟩ : L.dualCarrier) : L.DiscriminantGroup)
    rw [← Submodule.Quotient.mk_smul, discriminantGroup_mk_eq_zero_iff] at h
    exact h
  rw [LinearMap.BilinForm.mem_dualSubmodule] at hx
  rcases Submodule.mem_one.mp (hx _ hmem) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [eq_intCast, map_nsmul, nsmul_eq_mul] at hk
  rw [norm_apply, hk]
  push_cast
  ring1

variable [L.IsNondegenerate] in
/-- **The level is the exponent `e` of the discriminant group or `2e`** (LMFDB `lattice.level`). -/
lemma level_eq_exponent_or_eq_two_mul_exponent :
    L.level = AddMonoid.exponent L.DiscriminantGroup ∨
      L.level = 2 * AddMonoid.exponent L.DiscriminantGroup := by
  rcases L.exponent_discriminantGroup_dvd_level with ⟨m, hm⟩
  have h2 : L.level ∣ 2 * AddMonoid.exponent L.DiscriminantGroup := by
    exact_mod_cast L.level_dvd_two_mul_exponent
  have he : 0 < AddMonoid.exponent L.DiscriminantGroup :=
    Nat.pos_of_ne_zero fun h ↦ by simp [h] at hm; exact L.level_pos.ne' hm
  rw [hm, mul_comm 2] at h2 ⊢
  have hm2 : m ∣ 2 := (Nat.mul_dvd_mul_iff_left he).mp h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with rfl | rfl
  · exact Or.inl (mul_one _)
  · exact Or.inr rfl

end TauCeti.IntegralLattice
