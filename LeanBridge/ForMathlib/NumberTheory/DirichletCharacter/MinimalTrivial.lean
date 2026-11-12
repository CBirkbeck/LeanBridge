import LeanBridge.ForMathlib.NumberTheory.DirichletCharacter.Minimal

/-!
# Minimality of the trivial Dirichlet character

The LMFDB knowl `character.dirichlet.minimal` says that the minimal Dirichlet characters of prime
power modulus include the primitive ones but not only those, and that the trivial character is
minimal. The trivial character modulo `3` is minimal, `3` not being a square divisible by `16`, but
not primitive, its conductor being `1`. The trivial character modulo `N` is minimal exactly when the
largest power `2 ^ e` of `2` dividing `N` does not have `e ≥ 4` even: when `2 ^ e` is a square
divisible by `16`, the first condition for its factor at `2` asks for its conductor `1` to be
`2 ^ (e / 2)` or `2 ^ e`. So the knowl's claim that the trivial character is minimal fails for
these `N`, such as `N = 16`.

## Main results

* `DirichletCharacter.not_forall_isPrimitive_of_isMinimalOfPrimePowerModulus`: not every minimal
  character of prime power modulus is primitive.
* `DirichletCharacter.isMinimal_one_iff`: the trivial character modulo `N` is minimal exactly when
  `2 ^ e ∥ N` with `e` odd or `e < 4`.
-/

namespace DirichletCharacter

variable {N : ℕ}

/-- **Not every minimal Dirichlet character of prime power modulus is primitive** (LMFDB
`character.dirichlet.minimal`): the trivial character modulo `3` is minimal, `3` not being a square
divisible by `16` (`DirichletCharacter.isMinimalOfPrimePowerModulus_one_iff`), but its conductor is
`1`, not `3`. -/
lemma not_forall_isPrimitive_of_isMinimalOfPrimePowerModulus : ¬∀ N, IsPrimePow N →
    ∀ χ : DirichletCharacter ℂ N, χ.IsMinimalOfPrimePowerModulus → χ.IsPrimitive :=
  fun h ↦ absurd ((h 3 Nat.prime_three.isPrimePow 1 <| isMinimalOfPrimePowerModulus_one_iff.mpr
    fun h3 ↦ absurd h3.2 (by norm_num)).symm.trans conductor_one) (by norm_num)

/-- **The trivial character modulo `N` is minimal exactly when `2 ^ e ∥ N` with `e` odd or
`e < 4`** (LMFDB `character.dirichlet.minimal`). The knowl's claim that the trivial character is
minimal fails for the `N` whose largest power of `2` dividing it is `2 ^ e` with `e ≥ 4` even, such
as `N = 16`. -/
lemma isMinimal_one_iff :
    IsMinimal (1 : DirichletCharacter ℂ N) ↔ ¬(2 ∣ N.factorization 2 ∧ 4 ≤ N.factorization 2) := by
  refine ⟨fun h ⟨he, h4⟩ ↦ ?_, fun h p hp ↦ ?_⟩
  · have h2 : 2 ∈ N.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      omega
    have : NeZero (2 ^ N.factorization 2) := ⟨by positivity⟩
    have h1 : (primePowerPart 2 (1 : DirichletCharacter ℂ N)).IsMinimalOfPrimePowerModulus := h 2 h2
    rw [primePowerPart_one] at h1
    exact isMinimalOfPrimePowerModulus_one_iff.mp h1
      ⟨(even_iff_two_dvd.mpr he).isSquare_pow 2, pow_dvd_pow 2 h4⟩
  · have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    have : NeZero (p ^ N.factorization p) := ⟨pow_ne_zero _ hp'.ne_zero⟩
    rw [primePowerPart_one, isMinimalOfPrimePowerModulus_one_iff]
    rintro ⟨hsq, h16⟩
    have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp').mp <|
      Nat.prime_two.dvd_of_dvd_pow <| dvd_trans (by norm_num) h16).symm
    subst hp2
    refine h ⟨?_, (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (h16 : 2 ^ 4 ∣ _)⟩
    simpa [Nat.prime_two.factorization_self, even_iff_two_dvd] using
      Nat.isSquare_iff_even_factorization.mp hsq 2 Nat.prime_two

end DirichletCharacter
