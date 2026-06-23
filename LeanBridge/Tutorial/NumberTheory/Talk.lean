/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

import Mathlib
import LeanBridge.Tutorial.NumberTheory.Instances --ignore this

/-
If your computer is fast enough, always start with `import Mathlib`. You can clean up later.
-/

/-!

# Algebraic Number Theory in Lean

We will give an overview of what is in mathlib concerning algebraic number theory. Even if one
wants to use AI, it's a good idea to know what is in the library and what is missing, so one can
guide the LLM in choosing the most idiomatic proof: this can speed up the process a lot.

It's also a very interesting experience: even if you are a number theorist, you will most likely be
surprised by the mathlib approach from time to time.

We go through various examples taken from Marcus' book *Number Fields* and see how to state them in
Lean, using the library and then we will move to elliptic curves and modular forms.

Most (but not all!) of the `sorry` are provable. It's a good idea to try to do so to familiarize
yourself with the library (the one in line 202 is probably quite hard, but it's fun).

-/

open Algebra Ideal Module Nat NumberField InfinitePlace Polynomial Real
--to use standard notation, almost always a good idea

/-- Theorem 1, page 10
Let `α` be an algebraic integer, and let `f` be a monic polynomial over `ℤ` of least degree having
`α` as a root. Then `f` is irreducible over `ℚ`. -/
example (a : ℂ) (ha : IsIntegral ℤ a) :
    Irreducible (map (algebraMap ℤ ℚ) (minpoly ℤ a)) := by
  sorry

/-- ... Equivalently, the monic irreducible polynomial over `ℚ` having `α` as a root has
    coefficients in `ℤ`. -/
example (K : Type) [Field K] [CharZero K] (a : K) (ha : IsIntegral ℤ a) :
    (minpoly ℚ a) ∈ lifts (algebraMap ℤ ℚ) := by
  sorry

/- `minpoly.isIntegrallyClosed_eq_field_fractions` and
 `minpoly.isIntegrallyClosed_eq_field_fractions'` are the mathlib way of stating this.
  Can you understand the difference between the two statements? -/

#check minpoly.isIntegrallyClosed_eq_field_fractions

#check minpoly.isIntegrallyClosed_eq_field_fractions'

--How do we check that Lean knows `ℤ` is integrally closed?
#synth IsIntegrallyClosed ℤ

/- Corollary, page 22
Let `K` be a number field of degree `n` over ℚ, and let `R` be the ring of integers of `K`.
Then `R` is a free abelian group of rank `n`. -/

variable (K : Type*) [Field K] [NumberField K] -- note that `[Field K]` is needed

#synth AddCommGroup (𝓞 K)

#synth Free ℤ (𝓞 K)

#synth Module.Finite ℤ (𝓞 K)

example : finrank ℤ (𝓞 K) = finrank ℚ K := by
  sorry

/- Theorem 14, page 40
Every number ring is a Dedekind domain -/

#synth (IsDedekindDomain (𝓞 K))

/- Theorem 16, page 40
Every ideal in a Dedekind domain `R` is uniquely representable as a product of prime ideals. -/

variable (R : Type*) [CommRing R] [IsDedekindDomain R]

#synth (CommSemiring (Ideal R))

#synth (UniqueFactorizationMonoid (Ideal R))

/- Theorem 21, page 46
∑ eᵢ fᵢ = n -/

example (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (p : Ideal (𝓞 K)) [p.IsMaximal] :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 L), p.ramificationIdx P * p.inertiaDeg P =
    Module.finrank K L := by
  sorry

/- We even have a generalization to any finite flat extension! -/

#check sum_ramification_inertia_eq_finrank

/- Corollary 1, page 95
Every nonzero ideal `I` in `𝓞 K` contains a nonzero element `α` with
`|Norm(α)| ≤ n! / n ^ n * (4 / π)^r₂ √|disc(𝓞 K)| * Norm(I)`.
-/
example (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    letI n := finrank ℚ K
    ∃ a, a ∈ I ∧ a ≠ 0 ∧ |norm ℚ (a : K)| ≤
    absNorm I * (4 / π) ^ nrComplexPlaces K * n ! / n ^ n * √|discr K| := by
  sorry

/- Theorem 38, page 100, Dirichlet's units theorem
-/

#synth Module.Finite ℤ (Additive (𝓞 K)ˣ)

example : finrank ℤ (Additive (𝓞 K)ˣ) = nrRealPlaces K + nrComplexPlaces K - 1 := by
  sorry

/- The class number formula -/
open Filter Topology Units in
example :
    letI r₁ := nrRealPlaces K
    letI r₂ := nrComplexPlaces K
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[>] 1)
    (𝓝 (2 ^ r₁ * (2 * π) ^ r₂ * regulator K * classNumber K / (torsionOrder K * √|discr K|))) := by
  sorry

open Ideal in
/-- A weak form of Chebotarev's density theorem. -/
example (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] (C : ConjClasses Gal(K/ℚ)) :
    {p : Primes | ∃ Q ∈ (span {(p : ℤ)}).primesOver (𝓞 K),
      ∃ σ, ConjClasses.mk σ = C ∧ IsArithFrobAt ℤ σ Q}.Infinite := by
  sorry

/-!
## Explicit number fields
-/

/- We realize `ℚ(i)` as `QuadraticAlgebra ℚ (-1) 0`, the quadratic algebra in which `i ^ 2 = -1`
(in general `QuadraticAlgebra R a b` is the algebra where `i ^ 2 = a + b * i`, so here `a = -1`,
`b = 0`). Similarly `ℤ[i]` is `QuadraticAlgebra ℤ (-1) 0`.

To see `QuadraticAlgebra ℚ (-1) 0` as a field, mathlib needs to know that `X ^ 2 + 1` has no
rational root, which is encoded as the following `Fact`. -/
instance : Fact (∀ r : ℚ, r ^ 2 ≠ -1 + 0 * r) := ⟨by grind [sq_nonneg]⟩

instance : NumberField (QuadraticAlgebra ℚ (-1) 0) where

/-- The ring of integers of `ℚ(i)` is `ℤ[i]`. -/
example : 𝓞 (QuadraticAlgebra ℚ (-1) 0) ≃ₐ[ℤ] QuadraticAlgebra ℤ (-1) 0 := by
  sorry

/-- A more idiomatic way of saying the same is the following, but it needs
`import Norwich.Instances`. An interesting exercise is to remove it and fill in the missing instance
by hand: you will discover that the instance
`instance (a : ℤ) : Algebra (QuadraticAlgebra ℤ a 0) (QuadraticAlgebra S a 0) :=`
is not enough here. Can you spot why?
-/
example : IsIntegralClosure (QuadraticAlgebra ℤ (-1) 0) ℤ ((QuadraticAlgebra ℚ (-1) 0)) := by
  sorry

/-- The discriminant of `ℚ(i)` is `-4`. -/
example : discr (QuadraticAlgebra ℚ (-1) 0) = -4 := by
  sorry

/- We now state the same two facts for the `n`-th cyclotomic field. -/

/-- The ring of integers of `ℚ(ζₙ)` is `ℤ[ζₙ]`. -/
example (n : ℕ) [NeZero n] (K : Type*) [Field K] [CharZero K] [IsCyclotomicExtension {n} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    IsIntegralClosure (ℤ[ζ]) ℤ K := by
  sorry

/-- The discriminant of `ℚ(ζₙ)`. -/
example (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] :
    discr K = (-1) ^ (φ n / 2) * (n ^ φ n / ∏ p ∈ n.primeFactors, p ^ (φ n / (p - 1))) := by
  sorry

/-- The Kronecker–Weber theorem: every finite abelian extension of `ℚ` is contained in a
cyclotomic field, i.e. it embeds into `ℚ(ζₙ)` for some `n`. (This is not yet in mathlib.) -/
example (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K] :
    ∃ n : ℕ, Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) := by
  sorry


/-!
## Elliptic curves and modular forms
-/

/-- For a prime `p` of good reduction, the `p`-th coefficient of the L-function of an elliptic
curve `E / ℚ` is `aₚ = p + 1 - #E(𝔽_p)`, where `E(𝔽_p)` is the group of points of the reduction
of `E` modulo `p` (here the reduction is taken over the residue field of `ℤ_[p]`). -/
example (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hp : ((E.baseChange ℚ_[p]).minimal ℤ_[p]).HasGoodReduction ℤ_[p]) :
    E.LFunction p = p + 1 -
      Nat.card (((E.baseChange ℚ_[p]).minimal ℤ_[p]).reduction ℤ_[p]).toAffine.Point := by
  sorry

open IsDedekindDomain IsLocalRing in
/-- Here is another version. -/
example (E : WeierstrassCurve ℚ) (p : HeightOneSpectrum (𝓞 ℚ))
    (hp : ((E.baseChange (p.adicCompletion ℚ)).minimal
      (p.adicCompletionIntegers ℚ)).HasGoodReduction (p.adicCompletionIntegers ℚ)) :
    letI R := p.adicCompletionIntegers ℚ
    E.LFunction (Nat.card (ResidueField R)) = Nat.card (ResidueField R) + 1 -
      Nat.card (((E.baseChange (p.adicCompletion ℚ)).minimal R).reduction R).toAffine.Point := by
  sorry

/-- Let's state a particular case of a weaker version of the modularity theorem, for the elliptic
curve `E : y² + y = x³ - x²`. -/
noncomputable def E : WeierstrassCurve ℚ := ⟨0, -1, 1, 0, 0⟩

open CongruenceSubgroup UpperHalfPlane in
/-- There is a unique normalized weight `2` cusp form of level `Γ₀(11)` whose coefficients agree
with the curve's L-function at every prime. -/
example : ∃! f : CuspForm (Gamma0 11) 2, (qExpansion 1 f).coeff 1 = 1 ∧
    ∀ (p : Primes), (qExpansion 1 f).coeff p = E.LFunction p := by
  sorry
