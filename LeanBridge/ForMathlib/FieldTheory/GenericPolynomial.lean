import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Generic polynomials

A polynomial `f(t₁, …, tₙ, x)` over the rational function field `K(t) = K(t₁, …, tₙ)` is generic
for a finite group `G` if its splitting field `L` is Galois and regular over `K(t)` (every element
of `L` algebraic over `K` lies in `K`), with Galois group isomorphic to `G`, and every Galois
extension with group `G` of every field `M ⊇ K` is the splitting field of a specialisation
`f(a₁, …, aₙ, x)`, `aᵢ ∈ M`.

## Main definitions

* `Polynomial.IsGenericPolynomial` (LMFDB `gg.generic_polynomial`).
-/

open Polynomial

namespace Polynomial

universe u

variable (K : Type u) [Field K] (G : Type*) [Group G] {n : ℕ}

/-- A monic polynomial `f ∈ K[t₁, …, tₙ][x]` is a **generic polynomial** (LMFDB
`gg.generic_polynomial`) for the group `G` over `K` if, with `F = K(t₁, …, tₙ)` the field of
fractions of `K[t₁, …, tₙ]` and `L` the splitting field of `f` over `F`:

1. `L` is Galois over `F` and regular over `F` (LMFDB `gg.regular_extension`): every element of
   `L` algebraic over `K` lies in (the image of) `K`;
2. `Gal(L/F) ≅ G`;
3. and 4. for every field `M ⊇ K` (of the universe of `K`) and every Galois extension `E/M` with
   `Gal(E/M) ≅ G`, `E` is the splitting field over `M` of `f(a₁, …, aₙ, x)` for some `aᵢ ∈ M`.

The LMFDB allows `f ∈ K(t₁, …, tₙ)[x]`; coefficients are taken in `K[t₁, …, tₙ]` here, so that
every specialisation `f(a₁, …, aₙ, x)` is defined, and `f` monic, so that it keeps its degree. -/
def IsGenericPolynomial (f : (MvPolynomial (Fin n) K)[X]) : Prop :=
  f.Monic ∧
    IsGalois (FractionRing (MvPolynomial (Fin n) K))
      (f.map (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)))).SplittingField ∧
    algebraicClosure K
      (f.map (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)))).SplittingField = ⊥ ∧
    Nonempty ((f.map (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)))).Gal ≃* G) ∧
    ∀ (M : Type u) [Field M] [Algebra K M] (E : Type u) [Field E] [Algebra M E] [IsGalois M E]
      [FiniteDimensional M E], Nonempty ((E ≃ₐ[M] E) ≃* G) →
        ∃ a : Fin n → M, (f.map (MvPolynomial.aeval a).toRingHom).IsSplittingField M E

end Polynomial
