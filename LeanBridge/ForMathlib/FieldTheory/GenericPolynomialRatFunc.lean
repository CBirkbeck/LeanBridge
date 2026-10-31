import LeanBridge.ForMathlib.FieldTheory.GenericPolynomial

/-!
# Generic polynomials with coefficients in a rational function field

A generic polynomial for a finite group `G` over a field `K` (LMFDB `gg.generic_polynomial`) is a
polynomial `f(t₁, …, tₙ, x)` with coefficients in the rational function field
`K(t) = K(t₁, …, tₙ)`. Its specialisation `f(a₁, …, aₙ, x)` at a point `a ∈ Mⁿ` of a field
`M ⊇ K` is only defined when the denominators of the coefficients of `f` do not vanish at `a`: it
is then `F(a, x) / q(a)` for any denominator `q ∈ K[t]` of `f` with `q(a) ≠ 0`, `F = q f ∈ K[t][x]`,
and this does not depend on `q`. The earlier `Polynomial.IsGenericPolynomial` treats monic
polynomials with coefficients in `K[t]`, whose specialisations are always defined; it is the case
of a monic polynomial of `IsGeneric`.

## Main definitions

* `Polynomial.IsSpecialisationAt` (LMFDB `gg.generic_polynomial`): `g` is the specialisation
  `f(a, x)` of `f ∈ K(t)[x]` at `a`.
* `Polynomial.IsGeneric` (LMFDB `gg.generic_polynomial`): generic polynomials in `K(t)[x]`.

## Main results

* `Polynomial.IsSpecialisationAt.eq`: the specialisation of `f` at `a`, when it is defined, does
  not depend on the choice of the denominator.
* `Polynomial.isGenericPolynomial_iff`: a polynomial `f ∈ K[t][x]` is generic in the sense of
  `Polynomial.IsGenericPolynomial` exactly when it is monic and its image in `K(t)[x]` is generic.
-/

open Polynomial

namespace Polynomial

universe u

variable {K : Type u} [Field K] (G : Type*) [Group G] {n : ℕ} {M : Type*} [Field M] [Algebra K M]
  {f : (FractionRing (MvPolynomial (Fin n) K))[X]} {a : Fin n → M} {g g' : M[X]}
  (F : (MvPolynomial (Fin n) K)[X])

variable (f a g) in
/-- The polynomial `g ∈ M[x]` is the **specialisation** `f(a₁, …, aₙ, x)` (LMFDB
`gg.generic_polynomial`) of `f ∈ K(t₁, …, tₙ)[x]` at the point `a ∈ Mⁿ` of a field `M ⊇ K` if, for
some denominator `q ∈ K[t]` of `f` with `q(a) ≠ 0`, so that `F = q f` lies in `K[t][x]`,
`q(a) g = F(a, x)`. Such a `q` exists exactly when the coefficients of `f` are regular at `a`, and
`g` then does not depend on it (`Polynomial.IsSpecialisationAt.eq`): at a point where denominators
vanish the specialisation is undefined. -/
def IsSpecialisationAt : Prop :=
  ∃ (F : (MvPolynomial (Fin n) K)[X]) (q : MvPolynomial (Fin n) K), MvPolynomial.aeval a q ≠ 0 ∧
    F.map (algebraMap _ _) = C (algebraMap _ _ q) * f ∧
    C (MvPolynomial.aeval a q) * g = F.map (MvPolynomial.aeval a).toRingHom

/-- **The specialisation of a polynomial over `K(t)` is well defined**: two specialisations of
`f` at the same point, computed with two denominators of `f` that do not vanish there, agree. -/
lemma IsSpecialisationAt.eq (h : f.IsSpecialisationAt a g) (h' : f.IsSpecialisationAt a g') :
    g = g' := by
  rcases h with ⟨F, q, hq, hF, hg⟩
  rcases h' with ⟨F', q', hq', hF', hg'⟩
  have hFF : C q' * F = C q * F' := by
    refine map_injective _
      (IsFractionRing.injective (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))) ?_
    rw [Polynomial.map_mul, Polynomial.map_mul, map_C, map_C, hF, hF']
    ring1
  have hFF' : (C q' * F).map (MvPolynomial.aeval a).toRingHom =
      (C q * F').map (MvPolynomial.aeval a).toRingHom :=
    congrArg _ hFF
  rw [Polynomial.map_mul, Polynomial.map_mul, map_C, map_C, ← hg, ← hg'] at hFF'
  refine mul_left_cancel₀ (mul_ne_zero (C_ne_zero.mpr hq) (C_ne_zero.mpr hq')) ?_
  linear_combination hFF'

lemma isSpecialisationAt_map :
    (F.map (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)))).IsSpecialisationAt a
    (F.map (MvPolynomial.aeval a).toRingHom) :=
  ⟨F, 1, by simp, by simp, by simp⟩

lemma isSpecialisationAt_map_iff :
    (F.map (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)))).IsSpecialisationAt a g ↔
    g = F.map (MvPolynomial.aeval a).toRingHom :=
  ⟨fun h ↦ h.eq <| isSpecialisationAt_map F, fun h ↦ h ▸ isSpecialisationAt_map F⟩

variable (K f) in
/-- A polynomial `f ∈ K(t₁, …, tₙ)[x]` is **generic** (LMFDB `gg.generic_polynomial`) for the
group `G` over `K` if, with `L` the splitting field of `f` over `K(t)`, the field of fractions of
`K[t₁, …, tₙ]`:

1. `L` is Galois over `K(t)` and regular over `K(t)` (LMFDB `gg.regular_extension`): every element
   of `L` algebraic over `K` lies in (the image of) `K`;
2. `Gal(L/K(t)) ≅ G`;
3. and 4. for every field `M ⊇ K` (of the universe of `K`) and every Galois extension `E/M` with
   `Gal(E/M) ≅ G`, there is a point `a ∈ Mⁿ` at which the specialisation `f(a, x)` is defined
   (`Polynomial.IsSpecialisationAt`: no denominator of the coefficients of `f` vanishes at `a`)
   and `E` is the splitting field of `f(a, x)` over `M`. -/
def IsGeneric : Prop :=
  IsGalois (FractionRing (MvPolynomial (Fin n) K)) f.SplittingField ∧
    algebraicClosure K f.SplittingField = ⊥ ∧ Nonempty (f.Gal ≃* G) ∧
      ∀ (M : Type u) [Field M] [Algebra K M] (E : Type u) [Field E] [Algebra M E] [IsGalois M E]
        [FiniteDimensional M E], Nonempty ((E ≃ₐ[M] E) ≃* G) →
          ∃ (a : Fin n → M) (g : M[X]), f.IsSpecialisationAt a g ∧ g.IsSplittingField M E

/-- **Generic polynomials over `K[t]` are generic polynomials over `K(t)`**: a polynomial
`f ∈ K[t][x]` satisfies `Polynomial.IsGenericPolynomial` exactly when it is monic and its image in
`K(t)[x]` is generic, its specialisations being the polynomials `f(a, x)`. -/
lemma isGenericPolynomial_iff : IsGenericPolynomial K G F ↔ F.Monic ∧
    IsGeneric K G (F.map (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)))) := by
  simp only [IsGenericPolynomial, IsGeneric, isSpecialisationAt_map_iff, exists_eq_left]

end Polynomial
