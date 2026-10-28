import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.FrobeniusOrder

/-!
# Singular primes and singular support

The singular primes of an order `R` in an étale `ℚ`-algebra `K` are its maximal ideals that contain
the conductor `(R : 𝒪_K) = {x ∈ R | x 𝒪_K ⊆ R}` of `R`, the primes at which `R` is not maximal.
The singular support of an overorder `S` of the Frobenius order `ℤ[F, V]` of a Weil polynomial is
the set of singular primes of `ℤ[F, V]` that contain the relative conductor `(ℤ[F, V] : S)`.

## Main definitions

* `Subalgebra.relativeConductor`: the conductor `(R : S) = {x ∈ R | x S ⊆ R}`, an ideal of `R`
  (LMFDB `av.fq.conductor`).
* `Subalgebra.singularPrimes` (LMFDB `av.fq.singular_primes`).
* `Polynomial.singularSupport` (LMFDB `av.fq.singular_primes`).

## Main results

* `Subalgebra.relativeConductor_eq_top_iff`: the conductor `(R : S)` is `R` if and only if
  `S ⊆ R`.
* `Subalgebra.singularPrimes_eq_empty_iff`: an order has no singular primes if and only if it is
  maximal.
-/

namespace Subalgebra

variable {K : Type*} [CommRing K] (R S : Subalgebra ℤ K)

/-- The **conductor** `(R : S) = {x ∈ R | x S ⊆ R}` of a subring `S` of `K` into a subring `R`, an
ideal of `R` (LMFDB `av.fq.conductor`). For an order `R` of an étale `ℚ`-algebra `K` and `S` the
maximal order `𝒪_K` it is the conductor `𝔣_R` of `R`, and for an overorder `S` of `R` it is the
relative conductor. -/
def relativeConductor : Ideal R where
  carrier := {x | ∀ s ∈ S, (x : K) * s ∈ R}
  add_mem' hx hy s hs := by
    rw [AddMemClass.coe_add, add_mul]
    exact add_mem (hx s hs) (hy s hs)
  zero_mem' s _ := by
    rw [ZeroMemClass.coe_zero, zero_mul]
    exact zero_mem R
  smul_mem' c x hx s hs := by
    rw [smul_eq_mul, MulMemClass.coe_mul, mul_assoc]
    exact mul_mem c.2 (hx s hs)

/-- The **singular primes** (LMFDB `av.fq.singular_primes`) of an order `R` of an étale `ℚ`-algebra
`K`: the maximal ideals of `R` that contain (that is, divide) its conductor `(R : 𝒪_K)`, for the
maximal order `𝒪_K` of `K`, the integral closure of `ℤ` in `K`. -/
def singularPrimes : Set (Ideal R) :=
  {𝔓 | 𝔓.IsMaximal ∧ R.relativeConductor (integralClosure ℤ K) ≤ 𝔓}

variable {R S}

/-- The conductor `(R : S)` is `R` if and only if `S ⊆ R`. -/
lemma relativeConductor_eq_top_iff : R.relativeConductor S = ⊤ ↔ S ≤ R := by
  refine ⟨fun h s hs ↦ ?_, fun h ↦ (Ideal.eq_top_iff_one _).mpr fun s hs ↦ ?_⟩
  · simpa using ((Ideal.eq_top_iff_one _).mp h) s hs
  · simpa using h hs

/-- An order `R` has no singular primes if and only if it is maximal, that is it contains the
integral closure of `ℤ` in `K`. -/
lemma singularPrimes_eq_empty_iff : R.singularPrimes = ∅ ↔ integralClosure ℤ K ≤ R := by
  rw [← relativeConductor_eq_top_iff, Set.eq_empty_iff_forall_notMem]
  refine ⟨fun h ↦ by_contra fun hne ↦ ?_, fun h 𝔓 h𝔓 ↦ h𝔓.1.ne_top <| top_le_iff.mp <| h ▸ h𝔓.2⟩
  rcases Ideal.exists_le_maximal _ hne with ⟨𝔓, h𝔓, hle⟩
  exact h 𝔓 ⟨h𝔓, hle⟩

end Subalgebra

namespace Polynomial

variable (q : ℕ) (h : ℤ[X])

/-- The **singular support** (LMFDB `av.fq.singular_primes`) of an overorder `S` of the Frobenius
order `ℤ[F, V]` of a polynomial `h ∈ ℤ[x]` (`Polynomial.frobeniusOrder`): the singular primes of
`ℤ[F, V]` that contain the relative conductor `(ℤ[F, V] : S)`. The LMFDB's `h` is the Weil
polynomial of an isogeny class of abelian varieties over `𝔽_q`; here `h` is any polynomial and `S`
any subring of the étale algebra of `h`. -/
def singularSupport (S : Subalgebra ℤ h.EtaleAlgebra) : Set (Ideal (h.frobeniusOrder q)) :=
  {𝔓 ∈ (h.frobeniusOrder q).singularPrimes | (h.frobeniusOrder q).relativeConductor S ≤ 𝔓}

end Polynomial
