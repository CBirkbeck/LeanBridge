import Mathlib.Basic.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Duality
import TauCeti.Data.ZMod.ExactDivisor

/-!
# Minimal Dirichlet characters

The LMFDB chooses, among the characters of a twist class, minimal ones, to define the twist-minimal
spaces of newforms. A character of prime power modulus is minimal when its conductor avoids the
interval `(√N, N)` (with a further condition when `N` is a square divisible by `16`) and its order
and conductor are minimal among the characters `χψ²` with `cond(ψ) cond(χψ) ∣ N`. A character of
any modulus is minimal when the characters of prime power modulus into which it factors are.

## Main definitions

* `DirichletCharacter.primePowerPart`: the factor of a character at an exact prime power divisor
  of its modulus.
* `DirichletCharacter.IsMinimalOfPrimePowerModulus` (LMFDB `character.dirichlet.minimal`):
  minimal characters of prime power modulus.
* `DirichletCharacter.IsMinimal` (LMFDB `character.dirichlet.minimal`): minimal characters.

## Main results

* `DirichletCharacter.IsPrimitive.isMinimalOfPrimePowerModulus`: a primitive character of prime
  power modulus is minimal.
* `DirichletCharacter.isMinimalOfPrimePowerModulus_one_iff`: the trivial character modulo `N`
  satisfies the prime power conditions exactly when `N` is not a square divisible by `16`.
* `DirichletCharacter.isMinimal_one`: the trivial character modulo `N` is minimal if `16 ∤ N`.
-/

open TauCeti.Nat (isExactDivisor_primePow)

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R] {N : ℕ} (p : ℕ) (χ : DirichletCharacter ℂ N)

/-- The **`p`-part** of a Dirichlet character `ψ` modulo `N`: the character modulo the exact prime
power divisor `p ^ v_p(N)` of `N` that sends `u` to `ψ û`, where `û ≡ u` modulo `p ^ v_p(N)` and
`û ≡ 1` modulo `N / p ^ v_p(N)`. The `p`-parts of `ψ`, for `p` dividing `N`, are the characters of
prime power modulus into which `ψ` factors uniquely
(`TauCeti.Nat.IsExactDivisor.eq_mul_comp_unitsMap`). -/
noncomputable def primePowerPart (ψ : DirichletCharacter R N) :
    DirichletCharacter R (p ^ N.factorization p) :=
  MulChar.ofUnitHom <| (ψ.toUnitHom.comp
    isExactDivisor_primePow.unitsEquivProd.symm.toMonoidHom).comp (MonoidHom.inl _ _)

lemma primePowerPart_one : primePowerPart p (1 : DirichletCharacter R N) = 1 := by
  ext u
  simp [primePowerPart]

/-- A complex Dirichlet character `χ` of prime power modulus `N` is **minimal** (LMFDB
`character.dirichlet.minimal`) if
1. its conductor does not lie in the open interval `(√N, N)`, and if `N` is a square divisible by
   `16` then its conductor is `√N` or `N`;
2. both its order and its conductor are minimal among the characters `χψ²`, for `ψ` running over
   the characters modulo `N` with `cond(ψ) cond(χψ) ∣ N`.

We read the second condition as saying that neither the order nor the conductor of `χ` exceeds
that of such a `χψ²` (`χ` itself is one of them, for `ψ = 1`). The conditions are stated for every
modulus `N`; the LMFDB uses them for prime powers. -/
def IsMinimalOfPrimePowerModulus : Prop :=
  ¬(N < χ.conductor ^ 2 ∧ χ.conductor < N) ∧
    (IsSquare N → 16 ∣ N → χ.conductor ^ 2 = N ∨ χ.conductor = N) ∧ ∀ ψ : DirichletCharacter ℂ N,
    ψ.conductor * (χ * ψ).conductor ∣ N → orderOf χ ≤ orderOf (χ * ψ ^ 2) ∧
    χ.conductor ≤ (χ * ψ ^ 2).conductor

/-- A complex Dirichlet character `χ` modulo `N` is **minimal** (LMFDB
`character.dirichlet.minimal`) if every character in its factorization into characters of prime
power moduli `p ^ v_p(N)`, its `p`-parts for the primes `p ∣ N`, is minimal. -/
def IsMinimal : Prop :=
  ∀ p ∈ N.primeFactors, (χ.primePowerPart p).IsMinimalOfPrimePowerModulus

variable {χ} in
/-- A primitive Dirichlet character of prime power modulus is minimal. -/
lemma IsPrimitive.isMinimalOfPrimePowerModulus (hN : IsPrimePow N) (hχ : χ.IsPrimitive) :
    χ.IsMinimalOfPrimePowerModulus := by
  rcases (isPrimePow_nat_iff N).mp hN with ⟨p, e, hp, -, rfl⟩
  have : NeZero (p ^ e) := ⟨(pow_pos hp.pos e).ne'⟩
  refine ⟨fun h ↦ (hχ ▸ h.2).false, fun _ _ ↦ .inr hχ, fun ψ hψ ↦ ?_⟩
  rcases (Nat.dvd_prime_pow hp).mp ((Nat.dvd_mul_right _ _).trans hψ) with ⟨i, -, hai⟩
  rcases (Nat.dvd_prime_pow hp).mp ((Nat.dvd_mul_left _ _).trans hψ) with ⟨j, -, hbj⟩
  have hdvd : (χ * ψ * ψ⁻¹).conductor ∣ (χ * ψ).conductor.lcm ψ⁻¹.conductor :=
    conductor_mul_dvd_lcm_conductor (χ * ψ) ψ⁻¹
  rw [mul_inv_cancel_right, hχ, conductor_inv, hai, hbj] at hdvd
  have he : e ≤ max i j := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp <| hdvd.trans <|
    Nat.lcm_dvd (pow_dvd_pow p (le_max_right i j)) (pow_dvd_pow p (le_max_left i j))
  have hij : i + j ≤ e := by
    rw [hai, hbj, ← pow_add] at hψ
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hψ
  rcases i.eq_zero_or_pos with rfl | hi0
  · rw [pow_zero, ← eq_one_iff_conductor_eq_one] at hai
    subst hai
    simp
  · have hj0 : j = 0 := by omega
    rw [hj0, pow_zero, ← eq_one_iff_conductor_eq_one, mul_eq_one_iff_eq_inv'] at hbj
    subst hbj
    rw [sq, ← mul_assoc, mul_inv_cancel, one_mul, orderOf_inv, conductor_inv]
    exact ⟨le_rfl, le_rfl⟩

/-- The trivial character modulo `N` satisfies the conditions for minimality of a character of prime
power modulus exactly when `N` is not a square divisible by `16`: the LMFDB's claim that the
trivial character is minimal fails for the moduli `2 ^ e` with `e ≥ 4` even. -/
lemma isMinimalOfPrimePowerModulus_one_iff [NeZero N] :
    IsMinimalOfPrimePowerModulus (1 : DirichletCharacter ℂ N) ↔ ¬(IsSquare N ∧ 16 ∣ N) := by
  refine ⟨fun h ⟨hN, h16⟩ ↦ ?_, fun h ↦ ⟨fun h' ↦ ?_, fun hN h16 ↦ (h ⟨hN, h16⟩).elim,
    fun ψ _ ↦ ?_⟩⟩
  · rcases h.2.1 hN h16 with h1 | h1 <;> simp only [conductor_one] at h1 <;> omega
  · rw [conductor_one, one_pow] at h'
    omega
  · rw [one_mul, orderOf_one, conductor_one]
    exact ⟨orderOf_pos _, Nat.pos_of_ne_zero (conductor_ne_zero _)⟩

/-- The trivial character modulo `N` is minimal if `16 ∤ N`.

The LMFDB asserts that the trivial character is minimal; under the first condition of
`IsMinimalOfPrimePowerModulus`, this fails for the moduli whose `2`-part is `2 ^ e` with `e ≥ 4`
even, whose trivial character has conductor `1`, neither `2 ^ (e / 2)` nor `2 ^ e`. -/
lemma isMinimal_one (h : ¬16 ∣ N) : IsMinimal (1 : DirichletCharacter ℂ N) := by
  intro p hp
  have : NeZero (p ^ N.factorization p) :=
    ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero⟩
  rw [primePowerPart_one]
  exact isMinimalOfPrimePowerModulus_one_iff.mpr fun h16 ↦ h (h16.2.trans (N.ordProj_dvd p))

end DirichletCharacter
