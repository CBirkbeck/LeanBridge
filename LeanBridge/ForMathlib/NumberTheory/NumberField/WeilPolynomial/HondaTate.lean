import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# The Honda–Tate condition on Weil polynomials

The Honda–Tate theorem (LMFDB `av.fq.honda_tate`) says that two abelian varieties over `𝔽_q` are
isogenous if and only if they have the same Weil polynomial (LMFDB `av.fq.weil_polynomial`), and
characterises the Weil `q`-polynomials (LMFDB `nf.weil_polynomial`) that are Weil polynomials of
abelian varieties over `𝔽_q` by a condition on the multiplicities of their irreducible factors
(Tate, *Classes d'isogénie des variétés abéliennes sur un corps fini (d'après T. Honda)*, Séminaire
Bourbaki 352; Waterhouse, *Abelian varieties over finite fields*). Let `q = p ^ r`, with `p` prime
and `r ≥ 1`, and let `m` be a monic irreducible factor over `ℚ`, of multiplicity `k`, of a Weil
`q`-polynomial `h`. A root `π` of `m` is a Weil `q`-number, and the simple abelian variety over
`𝔽_q` attached to `π` has as endomorphism algebra the central division algebra over `ℚ(π)` with
local invariants `1/2` at the real places of `ℚ(π)`, `(v(π) / v(q)) [ℚ(π)_v : ℚ_p]` at its places
`v` above `p`, and `0` elsewhere; its Weil polynomial is `m ^ e`, where `e` is the order of this
algebra in the Brauer group of `ℚ(π)`, the least common multiple of the orders of the local
invariants in `ℚ / ℤ`. Since every abelian variety is isogenous to a product of simple ones, `h` is
the Weil polynomial of an abelian variety over `𝔽_q` if and only if, for each such factor `m`, `e`
divides `k`, that is `k` times every local invariant is an integer.

This condition is formalised here as a predicate on polynomials. The places of `ℚ(π) = ℚ[x] / (m)`
above `p` correspond to the monic irreducible factors `f` of `m` over `ℚ_p`, with completion
`ℚ_p[x] / (f)`; the norm of `π` from this completion to `ℚ_p` is `±f(0)`, so that the local
invariant at the place of `f` is `v_p(f(0)) / r`, for the `p`-adic valuation `v_p` normalised by
`v_p(p) = 1`. The real places of `ℚ(π)` correspond to the real roots of `m`. So the condition on
`m` and `k` is that `k` is even if `m` has a real root, and that `r` divides `k v_p(f(0))` for every
monic irreducible factor `f` of `m` over `ℚ_p`. The theorem itself, and its complement that `A` is
isogenous to an abelian subvariety of `B` if and only if the Weil polynomial of `A` divides that of
`B`, are not formalised: the Weil polynomial of an abelian variety is only available relative to
its Tate modules (`TauCeti.AlgebraicGeometry.AbelianVariety.HasWeilPolynomial`), and Tate's isogeny
theorem and Honda's construction are out of reach.

## Main definitions

* `Polynomial.IsHondaTateMultiplicity` (LMFDB `av.fq.honda_tate`): the condition on a monic
  irreducible factor `m ∈ ℚ[x]` of multiplicity `k`.
* `Polynomial.IsHondaTate` (LMFDB `av.fq.honda_tate`): `h` is a Weil `p ^ r`-polynomial all of whose
  irreducible factors over `ℚ` satisfy the condition.

## Main results

* `Polynomial.IsWeilPolynomial.mul`: a product of Weil `q`-polynomials is a Weil `q`-polynomial.
* `Polynomial.IsHondaTate.mul`: the condition is stable under products, as Weil polynomials of
  abelian varieties are, being multiplicative in products of abelian varieties.
* `Polynomial.isHondaTate_X_sub_C_sq` and `Polynomial.not_isHondaTate_X_sub_C`: for `q = p ^ (2s)`,
  the Weil polynomial `(x - √q)²` of a supersingular elliptic curve satisfies the condition, but
  `x - √q` does not.
-/

namespace Polynomial

open UniqueFactorizationMonoid

variable (p r : ℕ) [Fact p.Prime] {m : ℚ[X]} {k k' q : ℕ} {h h' : ℤ[X]}

variable (m k) in
/-- The **Honda–Tate multiplicity condition** (LMFDB `av.fq.honda_tate`) on a monic irreducible
polynomial `m ∈ ℚ[x]` and a multiplicity `k`, for `q = p ^ r`: `k` is even if `m` has a real root,
and `r` divides `k v_p(f(0))` for every monic irreducible factor `f` of `m` over `ℚ_p`. For a root
`π` of `m`, these say that `k` times every local invariant of the central division algebra over
`ℚ(π)` attached to `π` by Tate is an integer: the invariant is `1/2` at the real places of `ℚ(π)`,
which correspond to the real roots of `m`, and `v_p(f(0)) / r` at the place above `p` that
corresponds to `f`. -/
def IsHondaTateMultiplicity : Prop :=
  ((∃ x : ℝ, aeval x m = 0) → Even k) ∧ ∀ f : ℚ_[p][X], f.Monic → Irreducible f →
    f ∣ m.map (algebraMap ℚ ℚ_[p]) → (r : ℤ) ∣ k * (f.coeff 0).valuation

variable (h) in
/-- A polynomial `h ∈ ℤ[x]` satisfies the **Honda–Tate condition** (LMFDB `av.fq.honda_tate`) for
`q = p ^ r` if it is a Weil `q`-polynomial (LMFDB `nf.weil_polynomial`) and each of its monic
irreducible factors `m` over `ℚ`, of multiplicity `k` in `h`, satisfies the Honda–Tate multiplicity
condition `IsHondaTateMultiplicity p r m k`. By the Honda–Tate theorem, these are exactly the Weil
polynomials of abelian varieties over `𝔽_q` (LMFDB `av.fq.weil_polynomial`), for `r ≥ 1`; this is
not formalised. -/
def IsHondaTate : Prop :=
  h.IsWeilPolynomial (p ^ r) ∧ ∀ m ∈ normalizedFactors (h.map (Int.castRingHom ℚ)),
    IsHondaTateMultiplicity p r m ((normalizedFactors (h.map (Int.castRingHom ℚ))).count m)

lemma isHondaTateMultiplicity_zero : IsHondaTateMultiplicity p r m 0 :=
  ⟨fun _ ↦ Even.zero, fun _ _ _ _ ↦ by simp⟩

variable {p r}

lemma IsHondaTateMultiplicity.add (hk : IsHondaTateMultiplicity p r m k)
    (hk' : IsHondaTateMultiplicity p r m k') : IsHondaTateMultiplicity p r m (k + k') := by
  refine ⟨fun hx ↦ (hk.1 hx).add (hk'.1 hx), fun f hf hi hd ↦ ?_⟩
  rw [Nat.cast_add, add_mul]
  exact dvd_add (hk.2 f hf hi hd) (hk'.2 f hf hi hd)

/-- **A product of Weil `q`-polynomials is a Weil `q`-polynomial**: it is monic, and its complex
roots are those of its factors. -/
lemma IsWeilPolynomial.mul (hh : h.IsWeilPolynomial q) (hh' : h'.IsWeilPolynomial q) :
    (h * h').IsWeilPolynomial q := by
  refine ⟨hh.1.mul hh'.1, fun z hz ↦ ?_⟩
  rw [Polynomial.map_mul, roots_mul ((hh.1.map _).mul (hh'.1.map _)).ne_zero,
    Multiset.mem_add] at hz
  exact hz.elim (hh.2 z) (hh'.2 z)

variable (m) in
lemma IsHondaTate.isHondaTateMultiplicity (hh : h.IsHondaTate p r) :
    IsHondaTateMultiplicity p r m ((normalizedFactors (h.map (Int.castRingHom ℚ))).count m) := by
  by_cases hm : m ∈ normalizedFactors (h.map (Int.castRingHom ℚ))
  · exact hh.2 m hm
  · rw [Multiset.count_eq_zero.mpr hm]
    exact isHondaTateMultiplicity_zero p r

/-- **The Honda–Tate condition is stable under products**: the multiplicities of an irreducible
factor in two polynomials add up in their product. This is the condition for the Weil polynomial
`P_A P_B` of a product `A × B` of abelian varieties over `𝔽_q`. -/
lemma IsHondaTate.mul (hh : h.IsHondaTate p r) (hh' : h'.IsHondaTate p r) :
    (h * h').IsHondaTate p r := by
  refine ⟨hh.1.mul hh'.1, fun m _ ↦ ?_⟩
  rw [Polynomial.map_mul, normalizedFactors_mul (hh.1.1.map _).ne_zero (hh'.1.1.map _).ne_zero,
    Multiset.count_add]
  exact (hh.isHondaTateMultiplicity m).add (hh'.isHondaTateMultiplicity m)

lemma isWeilPolynomial_X_sub_C_natCast (n : ℕ) : (X - C (n : ℤ)).IsWeilPolynomial (n ^ 2) := by
  refine ⟨monic_X_sub_C _, fun z hz ↦ ?_⟩
  rw [Polynomial.map_sub, map_X, map_C, roots_X_sub_C, Multiset.mem_singleton] at hz
  rw [hz, eq_intCast, Int.cast_natCast, Complex.norm_natCast, Nat.cast_pow,
    Real.sqrt_sq (Nat.cast_nonneg _)]

lemma normalizedFactors_X_sub_C_natCast (n : ℕ) :
    normalizedFactors ((X - C (n : ℤ)).map (Int.castRingHom ℚ)) = {X - C (n : ℚ)} := by
  rw [Polynomial.map_sub, map_X, map_C, normalizedFactors_irreducible (irreducible_X_sub_C _),
    (monic_X_sub_C _).normalize_eq_self, eq_intCast, Int.cast_natCast]

variable (p)

/-- **The Weil polynomial `(x - √q)²` satisfies the Honda–Tate condition** for `q = p ^ (2s)`: it
is the Weil polynomial of a supersingular elliptic curve over `𝔽_q` all of whose endomorphisms are
defined over `𝔽_q`, whose endomorphism algebra is the quaternion algebra over `ℚ` ramified at `p`
and `∞`, of local invariants `1/2`. -/
lemma isHondaTate_X_sub_C_sq (s : ℕ) : ((X - C ((p ^ s : ℕ) : ℤ)) ^ 2).IsHondaTate p (2 * s) := by
  have hw : (X - C ((p ^ s : ℕ) : ℤ)).IsWeilPolynomial (p ^ (2 * s)) :=
    pow_mul' p 2 s ▸ isWeilPolynomial_X_sub_C_natCast (p ^ s)
  refine ⟨sq (X - C ((p ^ s : ℕ) : ℤ)) ▸ hw.mul hw, fun m hm ↦ ?_⟩
  rw [Polynomial.map_pow, normalizedFactors_pow, normalizedFactors_X_sub_C_natCast] at hm ⊢
  rw [Multiset.count_nsmul, Multiset.mem_singleton.mp (Multiset.mem_of_mem_nsmul hm),
    Multiset.count_singleton_self, mul_one]
  refine ⟨fun _ ↦ even_two, fun f hf hi hd ↦ ?_⟩
  rw [Polynomial.map_sub, map_X, map_C, map_natCast] at hd
  rw [eq_of_monic_of_associated hf (monic_X_sub_C _)
    ((hi.dvd_irreducible_iff_associated (irreducible_X_sub_C _)).mp hd), coeff_sub, coeff_X_zero,
    coeff_C_zero, zero_sub, ← Rat.cast_natCast, ← Rat.cast_neg, Padic.valuation_ratCast,
    padicValRat.neg, padicValRat.of_nat, padicValNat.prime_pow]
  exact (Nat.cast_mul 2 s).dvd

/-- **The Weil polynomial `x - √q` does not satisfy the Honda–Tate condition** for `q = p ^ (2s)`:
its real root `√q` asks for an even multiplicity. Indeed the Weil polynomial of an abelian variety
has even degree. -/
lemma not_isHondaTate_X_sub_C (s : ℕ) : ¬(X - C ((p ^ s : ℕ) : ℤ)).IsHondaTate p (2 * s) := by
  rintro ⟨-, hh⟩
  rw [normalizedFactors_X_sub_C_natCast] at hh
  simpa using (hh _ (Multiset.mem_singleton_self _)).1 ⟨(p ^ s : ℕ), by simp⟩

end Polynomial
