import Mathlib.RepresentationTheory.Invariants
import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup

/-!
# The conductor of an Artin representation

Let `K/ℚ` be a finite Galois extension, `ρ` a representation of `Gal(K/ℚ)` on a finite-dimensional
complex vector space `V`, and `Q` a prime of `𝓞 K` above a prime number `p`. The ramification groups
`G_i = {σ | σ x ≡ x mod Q^(i + 1)}` of `Q`, for `i ≥ 0`, are Tau Ceti's `Ideal.ramificationGroup`;
they lie in the decomposition group of `Q`, which is the Galois group of the completion `K_Q/ℚ_p`,
and they are the ramification groups of `K_Q/ℚ_p` in the lower numbering. The exponent of the
conductor at `p` is `f(ρ, p) = ∑_{i ≥ 0} (g_i / g_0) (dim V - dim V^{G_i})`, with `g_i = |G_i|`; it
does not depend on the choice of `Q`, and the conductor of `ρ` is `∏_p p^f(ρ, p)`.

Artin's theorem that the exponents are integers is not proved here, so the exponents are rational
numbers and the conductor is a real number. Neither is the independence of the conductor from the
Galois extension `K` through which an Artin representation of `Gal(ℚ̄/ℚ)` factors.

## Main definitions

* `Representation.finrankInvariants`: the dimension of the vectors fixed by a subgroup.
* `Representation.artinConductorExponentAt`: the exponent `f(ρ, Q)` at a prime `Q` of `𝓞 K`.
* `Representation.artinConductorExponent` (LMFDB `artin.conductor`): the exponent `f(ρ, p)` at a
  prime number `p`.
* `Representation.artinConductor` (LMFDB `artin.conductor`): the conductor `∏_p p^f(ρ, p)`.

## Main results

* `Representation.artinConductorExponentAt_smul` and `Representation.artinConductorExponent_eq`:
  the exponent does not depend on the prime above `p`.
* `Representation.artinConductorExponentAt_eq_zero` and
  `Representation.artinConductorExponent_eq_zero`: the exponent vanishes at unramified primes.
* `Representation.artinConductorExponentAt_pos` and `Representation.artinConductorExponent_pos`: the
  exponent of a faithful representation is positive at ramified primes.
-/

open Module NumberField
open scoped Pointwise

namespace Representation

section Invariants

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
  (H : Subgroup G)

/-- The dimension of the subspace `V^H` of vectors fixed by a subgroup `H`. -/
noncomputable def finrankInvariants : ℕ :=
  finrank ℂ (invariants (ρ.comp H.subtype))

lemma finrankInvariants_bot : ρ.finrankInvariants ⊥ = finrank ℂ V := by
  have h : invariants (ρ.comp (⊥ : Subgroup G).subtype) = ⊤ := eq_top_iff.mpr fun v _ g ↦ by
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.mem_bot.mp g.2, map_one, End.one_apply]
  rw [finrankInvariants, h, finrank_top]

lemma finrankInvariants_map_conj (g : G) :
    ρ.finrankInvariants (H.map (MulAut.conj g)) = ρ.finrankInvariants H := by
  let e : V ≃ₗ[ℂ] V := LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹)
    (LinearMap.ext fun x ↦ ρ.self_inv_apply g x) (LinearMap.ext fun x ↦ ρ.inv_self_apply g x)
  have hρ (h : G) (v : V) : ρ (g * h * g⁻¹) v = ρ g (ρ h (ρ g⁻¹ v)) := by
    rw [map_mul, map_mul, End.mul_apply, End.mul_apply]
  have h : invariants (ρ.comp (H.map (MulAut.conj g)).subtype) = (invariants (ρ.comp H.subtype)).map
      (e : V →ₗ[ℂ] V) := by
    ext v
    rw [Submodule.mem_map_equiv, mem_invariants, mem_invariants]
    refine ⟨fun hv h ↦ ?_, fun hv k ↦ ?_⟩
    · have hk : ρ g (ρ h (ρ g⁻¹ v)) = v := by
        rw [← hρ]
        exact hv ⟨g * h * g⁻¹, Subgroup.mem_map_of_mem _ h.2⟩
      have hk' : ρ g⁻¹ (ρ g (ρ h (ρ g⁻¹ v))) = ρ g⁻¹ v := congrArg (ρ g⁻¹) hk
      rwa [ρ.inv_self_apply] at hk'
    · rcases k with ⟨_, h, hh, rfl⟩
      have hv' : ρ h (ρ g⁻¹ v) = ρ g⁻¹ v := hv ⟨h, hh⟩
      simp [hv']
  rw [finrankInvariants, finrankInvariants, h, LinearEquiv.finrank_map_eq]

variable [FiniteDimensional ℂ V]

lemma finrankInvariants_le : ρ.finrankInvariants H ≤ finrank ℂ V :=
  Submodule.finrank_le _

variable {H} in
lemma finrankInvariants_lt (hρ : Function.Injective ρ) (hH : H ≠ ⊥) :
    ρ.finrankInvariants H < finrank ℂ V := by
  refine Submodule.finrank_lt fun htop ↦ ?_
  rcases (Subgroup.ne_bot_iff_exists_ne_one).mp hH with ⟨h, hh⟩
  refine hh (Subtype.ext (hρ (LinearMap.ext fun v ↦ ?_)))
  have hv : v ∈ invariants (ρ.comp H.subtype) := htop ▸ Submodule.mem_top
  rw [Subgroup.coe_one, map_one, End.one_apply]
  exact hv h

end Invariants

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ Gal(K/ℚ) V) (Q : Ideal (𝓞 K)) (p : Nat.Primes)

/-- The **exponent of the Artin conductor** of a representation `ρ` of `Gal(K/ℚ)` at a prime `Q` of
`𝓞 K`: `f(ρ, Q) = ∑_{i ≥ 0} (g_i / g_0) (dim V - dim V^{G_i})`, where `G_i` is the `i`-th
ramification group of `Q` and `g_i` its order. -/
noncomputable def artinConductorExponentAt : ℚ :=
  ∑ᶠ i : ℕ, (Nat.card (Q.ramificationGroup Gal(K/ℚ) i) : ℚ) /
    Nat.card (Q.ramificationGroup Gal(K/ℚ) 0) *
      (finrank ℂ V - ρ.finrankInvariants (Q.ramificationGroup Gal(K/ℚ) i))

/-- **The exponent of the Artin conductor does not change when the prime is moved by the Galois
group**: the ramification groups are conjugated. -/
lemma artinConductorExponentAt_smul (σ : Gal(K/ℚ)) :
    ρ.artinConductorExponentAt (σ • Q) = ρ.artinConductorExponentAt Q := by
  simp only [artinConductorExponentAt, Ideal.ramificationGroup_smul,
    Subgroup.card_map_of_injective (f := (MulAut.conj σ : Gal(K/ℚ) →* Gal(K/ℚ)))
      (MulAut.conj σ).injective, finrankInvariants_map_conj]

lemma isPrime_span_natCast : (Ideal.span {(p : ℤ)}).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime <| Nat.prime_iff_prime_int.mp p.prop

/-- The **exponent `f(ρ, p)` of the Artin conductor** (LMFDB `artin.conductor`) of a representation
`ρ` of `Gal(K/ℚ)` at a prime number `p`: the exponent `f(ρ, Q)` at a prime `Q` of `𝓞 K` above `p`,
which does not depend on `Q` when `K/ℚ` is Galois (`Representation.artinConductorExponent_eq`). -/
noncomputable def artinConductorExponent : ℚ :=
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := isPrime_span_natCast p
  ρ.artinConductorExponentAt (Classical.arbitrary (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K))).1

/-- The **conductor** of a representation `ρ` of `Gal(K/ℚ)` on a finite-dimensional complex vector
space (LMFDB `artin.conductor`): the product `∏_p p^f(ρ, p)` over the prime numbers. Artin's
theorem that the exponents `f(ρ, p)` are integers, so that the conductor is a positive integer, is
not proved here: the exponents are rational numbers, and the conductor is a real number. -/
noncomputable def artinConductor : ℝ :=
  ∏ᶠ p : Nat.Primes, (p : ℝ) ^ (ρ.artinConductorExponent p : ℝ)

section FiniteDimensional

variable [FiniteDimensional ℂ V]

lemma artinConductorExponentAt_nonneg : 0 ≤ ρ.artinConductorExponentAt Q :=
  finsum_nonneg fun _ ↦ mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (sub_nonneg.mpr (Nat.cast_le.mpr (ρ.finrankInvariants_le _)))

lemma artinConductorExponent_nonneg : 0 ≤ ρ.artinConductorExponent p :=
  ρ.artinConductorExponentAt_nonneg _

lemma one_le_artinConductor : 1 ≤ ρ.artinConductor :=
  one_le_finprod fun p ↦ Real.one_le_rpow (by exact_mod_cast p.prop.one_lt.le)
    (by exact_mod_cast ρ.artinConductorExponent_nonneg p)

end FiniteDimensional

variable [IsGalois ℚ K] [Q.IsPrime]

/-- **The exponent of the Artin conductor vanishes at an unramified prime.** -/
lemma artinConductorExponentAt_eq_zero [Algebra.IsUnramifiedAt (𝓞 ℚ) Q] :
    ρ.artinConductorExponentAt Q = 0 := by
  simp [artinConductorExponentAt, finrankInvariants_bot]

lemma exists_artinConductorExponentAt_eq_sum : ∃ N : ℕ, ρ.artinConductorExponentAt Q = ∑ i ∈
    Finset.range (N + 1), (Nat.card (Q.ramificationGroup Gal(K/ℚ) i) : ℚ) / Nat.card
    (Q.ramificationGroup Gal(K/ℚ) 0) * (finrank ℂ V - ρ.finrankInvariants (Q.ramificationGroup
    Gal(K/ℚ) i)) := by
  have : FaithfulSMul Gal(K/ℚ) (𝓞 K) := IsGaloisGroup.faithful (A := 𝓞 ℚ)
  rcases Ideal.exists_forall_ramificationGroup_eq_bot (G := Gal(K/ℚ)) ‹Q.IsPrime›.ne_top
    with ⟨N, hN⟩
  refine ⟨N, finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_⟩
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra h
  refine Function.mem_support.mp hi ?_
  rw [hN i (by omega), finrankInvariants_bot, sub_self, mul_zero]

variable [Q.LiesOver (Ideal.span {(p : ℤ)})]

/-- **The exponent of the Artin conductor at `p` is its exponent at any prime above `p`**, since
the Galois group acts transitively on the primes above `p`. -/
lemma artinConductorExponent_eq : ρ.artinConductorExponent p = ρ.artinConductorExponentAt Q := by
  have : (Ideal.span {(p : ℤ)}).IsPrime := isPrime_span_natCast p
  rcases Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)})
    (Classical.arbitrary (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K))).1 Q Gal(K/ℚ) with ⟨σ, hσ⟩
  rw [artinConductorExponent, ← hσ, artinConductorExponentAt_smul]

/-- **The exponent of the Artin conductor vanishes at a prime unramified in `K`.** -/
lemma artinConductorExponent_eq_zero [Algebra.IsUnramifiedAt (𝓞 ℚ) Q] :
    ρ.artinConductorExponent p = 0 :=
  (ρ.artinConductorExponent_eq Q p).trans (ρ.artinConductorExponentAt_eq_zero Q)

variable [FiniteDimensional ℂ V] (hρ : Function.Injective ρ)
  (hQ : ¬Algebra.IsUnramifiedAt (𝓞 ℚ) Q)

include hρ hQ

/-- **The exponent of the Artin conductor of a faithful representation is positive at a ramified
prime.** -/
lemma artinConductorExponentAt_pos : 0 < ρ.artinConductorExponentAt Q := by
  rcases ρ.exists_artinConductorExponentAt_eq_sum Q with ⟨N, hN⟩
  have hG : Q.ramificationGroup Gal(K/ℚ) 0 ≠ ⊥ :=
    fun h ↦ hQ ((Ideal.ramificationGroup_zero_eq_bot_iff_isUnramifiedAt Q).mp h)
  rw [hN]
  refine Finset.sum_pos' (fun i _ ↦ mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (sub_nonneg.mpr (Nat.cast_le.mpr (ρ.finrankInvariants_le _)))) ⟨0, Finset.mem_range.mpr
    N.succ_pos, ?_⟩
  rw [div_self (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul, sub_pos, Nat.cast_lt]
  exact ρ.finrankInvariants_lt hρ hG

/-- **The exponent of the Artin conductor of a faithful representation is positive at a prime
ramified in `K`.** -/
lemma artinConductorExponent_pos : 0 < ρ.artinConductorExponent p :=
  (ρ.artinConductorExponent_eq Q p).symm ▸ ρ.artinConductorExponentAt_pos Q hρ hQ

end Representation
