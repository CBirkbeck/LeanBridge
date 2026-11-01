import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Polynomial.GaussLemma
import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
import TauCeti.NumberTheory.NumberField.ResidueDegree
import TauCeti.RingTheory.DedekindDomain.AdicValuation.LocalDegree

/-!
# The Cremona–Page–Sutherland order on the prime ideals of a number field

Cremona, Page and Sutherland (*Sorting and labelling integral ideals in a number field*,
arXiv:2005.09491, §2) order the prime ideals of a number field `K = ℚ(α)`, `α` a fixed integral
primitive element (for the LMFDB the root of the reduced defining polynomial of `nf.polredabs`),
first by norm, then by ramification index, and finally, among the primes above the same `p`, by
their `p`-adic factors: a prime `𝔭 ∣ p` corresponds to the irreducible factor `h` of the minimal
polynomial `g` of `α` over `ℚ_p` with `h(α) = 0` in the completion `K_𝔭`, the minimal polynomial of
`α` over `ℚ_p` in `K_𝔭`, and these factors, all in `ℤ_p[X]`, are ordered lexicographically by
their vectors of `p`-adic digits `(a_{0,0}, a_{1,0}, …, a_{d,0}, a_{0,1}, …)`, where
`h = ∑ᵢ (∑ⱼ a_{i,j} pʲ) Xⁱ` with `0 ≤ a_{i,j} < p`; these conventions (the digit level varying
slowest, the constant term first) are also those of the authors' code (`psort.py` in
github.com/JohnCremona/Sorting). This file defines that order and proves that it is total:
distinct primes above `p` have distinct `p`-adic factors, by the semi-local decomposition
`ℚ_p ⊗ K ≅ ∏_{𝔭 ∣ p} K_𝔭` of Tau Ceti, and a `p`-adic integer is determined by its digits.

## Main definitions

* `PadicInt.digit`: the digits of the `p`-adic expansion of a `p`-adic integer.
* `Padic.intDigit`: the digits of an element of `ℚ_[p]` that is a `p`-adic integer.
* `Polynomial.padicDigits` (LMFDB `nf.ideal_labels`): the digit vector of a polynomial over
  `ℚ_[p]` with `p`-adic integer coefficients.
* `NumberField.padicFactor` (LMFDB `nf.ideal_labels`): the `p`-adic factor of a prime above `p`,
  over the completion `ℚ_v`, and `NumberField.padicFactorPadic`, the same over `ℚ_[p]`.
* `NumberField.primeDigits` (LMFDB `nf.ideal_labels`): the digit vector of the `p`-adic factor of
  a prime.
* `NumberField.primeKey` (LMFDB `nf.ideal_labels`): the key `(N(𝔭), e(𝔭), digits)` ordering the
  primes.
* `NumberField.primeLinearOrder` (LMFDB `nf.ideal_labels`): the Cremona–Page–Sutherland order on
  the primes of `K`.

## Main results

* `PadicInt.eq_of_forall_digit_eq`: a `p`-adic integer is determined by its digits.
* `Polynomial.eq_of_padicDigits_eq`: a polynomial with `p`-adic integer coefficients is determined
  by its digit vector.
* `NumberField.irreducible_padicFactor`, `NumberField.padicFactor_dvd`: the `p`-adic factor of a
  prime is an irreducible factor over `ℚ_p` of the minimal polynomial of `α`.
* `NumberField.natDegree_padicFactor`: the `p`-adic factor of `𝔭` has degree `e(𝔭/p) f(𝔭/p)`.
* `NumberField.padicFactor_injective`: distinct primes above `p` have distinct `p`-adic factors.
* `NumberField.norm_coeff_padicFactorPadic_le_one`: the `p`-adic factors have `p`-adic integer
  coefficients.
* `NumberField.padicDigits_padicFactorPadic_injective`: distinct primes above `p` have distinct
  digit vectors.
* `NumberField.under_eq_of_absNorm_eq`: primes of equal norm lie above the same prime of `ℚ`.
* `NumberField.primeKey_injective`: the key determines the prime, so the order is total.
-/

open IsDedekindDomain Module NumberField Polynomial Rat HeightOneSpectrum

open scoped TensorProduct AdicCompletionExtension IntermediateField

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) {y : ℤ_[p]}

/-- The **`n`-th digit** `aₙ ∈ [0, p - 1]` of the `p`-adic expansion `x = ∑ aₙ pⁿ` of a `p`-adic
integer (Cremona–Page–Sutherland, arXiv:2005.09491, §2.2): `appr x (n + 1) = a₀ + ⋯ + aₙ pⁿ` is the
residue of `x` modulo `pⁿ⁺¹` in `[0, pⁿ⁺¹)`, and `aₙ` its quotient by `pⁿ`. -/
noncomputable def digit (n : ℕ) : ℕ :=
  x.appr (n + 1) / p ^ n

lemma appr_succ_eq_add_digit (n : ℕ) : x.appr (n + 1) = x.appr n + p ^ n * x.digit n := by
  rcases x.dvd_appr_sub_appr n (n + 1) n.le_succ with ⟨c, hc⟩
  rw [digit, Nat.eq_add_of_sub_eq (x.appr_mono n.le_succ) hc,
    Nat.mul_add_div (pow_pos (Fact.out : p.Prime).pos n), Nat.div_eq_of_lt (x.appr_lt n), add_zero,
    add_comm]

variable {x} in
lemma appr_eq_of_forall_digit_eq (h : ∀ n, x.digit n = y.digit n) (n : ℕ) :
    x.appr n = y.appr n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [appr_succ_eq_add_digit, appr_succ_eq_add_digit, ih, h]

variable {x} in
/-- **A `p`-adic integer is determined by its digits.** -/
lemma eq_of_forall_digit_eq (h : ∀ n, x.digit n = y.digit n) : x = y :=
  ext_of_toZModPow.mp fun n ↦
    congrArg (Nat.cast : ℕ → ZMod (p ^ n)) (appr_eq_of_forall_digit_eq h n)

end PadicInt

namespace Padic

variable {p : ℕ} [Fact p.Prime]

/-- The **`n`-th digit** `aₙ ∈ [0, p - 1]` of the `p`-adic expansion of an element `x` of `ℚ_[p]`
that is a `p`-adic integer (`PadicInt.digit`), and `0` if `x` is not one. -/
noncomputable def intDigit (x : ℚ_[p]) (n : ℕ) : ℕ :=
  if hx : ‖x‖ ≤ 1 then PadicInt.digit ⟨x, hx⟩ n else 0

end Padic

namespace Polynomial

variable {p : ℕ} [Fact p.Prime] {P Q : ℚ_[p][X]}

variable (P) in
/-- The **digit vector** (LMFDB `nf.ideal_labels`) of a polynomial `P = ∑ᵢ (∑ⱼ a_{i,j} pʲ) Xⁱ` over
`ℚ_[p]` with `p`-adic integer coefficients, `0 ≤ a_{i,j} < p` (Cremona–Page–Sutherland,
arXiv:2005.09491, §2.2): the vector `(a_{0,0}, a_{1,0}, …, a_{d,0}, a_{0,1}, a_{1,1}, …)` by which
the `p`-adic factors of a polynomial are sorted, lexicographically. It is given as the sequence over
the digit level `j` of the sequences over the degree `i` of the digits `a_{i,j}`, each ordered
lexicographically; for monic polynomials of degree `d`, the only ones the order compares, the
coefficients of degree above `d` vanish and this is the lexicographic order of the paper's vectors
in `[0, p - 1]^∞`. -/
noncomputable def padicDigits : Lex (ℕ → Lex (ℕ → ℕ)) :=
  toLex fun j ↦ toLex fun i ↦ (P.coeff i).intDigit j

/-- **A polynomial with `p`-adic integer coefficients is determined by its digit vector.** -/
lemma eq_of_padicDigits_eq (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (hQ : ∀ i, ‖Q.coeff i‖ ≤ 1)
    (h : P.padicDigits = Q.padicDigits) : P = Q := by
  ext i
  have hPQ : (⟨P.coeff i, hP i⟩ : ℤ_[p]) = ⟨Q.coeff i, hQ i⟩ :=
    PadicInt.eq_of_forall_digit_eq fun j ↦ by
      have hji : ofLex (ofLex P.padicDigits j) i = ofLex (ofLex Q.padicDigits j) i := by
        rw [h]
      simpa only [padicDigits, ofLex_toLex, Padic.intDigit, hP i, hQ i, ↓reduceDIte] using hji
  exact congrArg Subtype.val hPQ

end Polynomial

namespace NumberField

local instance (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

variable {K : Type*} [Field K] [NumberField K] (α : 𝓞 K) (v : HeightOneSpectrum (𝓞 ℚ))
  (w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal}) {F : Type*} [Field F]
  [NumberField F] [Algebra F K] (v₀ : HeightOneSpectrum (𝓞 F))
  (w₀ : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v₀.asIdeal}) (pb : PowerBasis F K)
  (𝔭 : HeightOneSpectrum (𝓞 K)) {𝔮 : HeightOneSpectrum (𝓞 K)}

/-- The **`p`-adic factor** (LMFDB `nf.ideal_labels`) of a prime `𝔭` of `K` above the prime `p` of
`ℚ` given by `v` (Cremona–Page–Sutherland, arXiv:2005.09491, §2.2): the irreducible factor over
`ℚ_p = ℚ_v` of the minimal polynomial of `α` that corresponds to `𝔭`, the one with `h(α) = 0` in
the completion `K_𝔭`. It is the minimal polynomial over `ℚ_v` of the image of `α` in `K_𝔭`. -/
noncomputable def padicFactor : (v.adicCompletion ℚ)[X] :=
  minpoly (v.adicCompletion ℚ) (algebraMap K (w.1.adicCompletion K) α)

/-- The **`p`-adic factor** (LMFDB `nf.ideal_labels`) of a prime above `p` (`padicFactor`), as a
polynomial over `ℚ_[p]`. -/
noncomputable def padicFactorPadic : ℚ_[primesEquiv v][X] :=
  (padicFactor α v w).map (adicCompletion.padicEquiv v : v.adicCompletion ℚ →+* ℚ_[primesEquiv v])

/-- The power basis `1 ⊗ x` of `F_v ⊗[F] K` over the completion `F_v`, for a power basis `x` of `K`
over a number field `F`. -/
private noncomputable def tensorPowerBasis :
    PowerBasis (v₀.adicCompletion F) (v₀.adicCompletion F ⊗[F] K) where
  gen := 1 ⊗ₜ pb.gen
  dim := pb.dim
  basis := pb.basis.baseChange (v₀.adicCompletion F)
  basis_eq_pow i := by
    simp

/-- The power basis `(x)_w` of `∏_{w ∣ v} K_w` over `F_v`, for a power basis `x` of `K` over a
number field `F`: the image of `1 ⊗ x` under the semi-local decomposition `F_v ⊗[F] K ≅ ∏ K_w`. -/
private noncomputable def piPowerBasis :
    PowerBasis (v₀.adicCompletion F)
      ((w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v₀.asIdeal}) →
        w.1.adicCompletion K) :=
  (tensorPowerBasis v₀ pb).map (TauCeti.semilocalEquiv K v₀)

private lemma piPowerBasis_gen :
    (piPowerBasis v₀ pb).gen w₀ = algebraMap K (w₀.1.adicCompletion K) pb.gen := by
  simp only [piPowerBasis, PowerBasis.map_gen, tensorPowerBasis, TauCeti.semilocalEquiv_tmul,
    map_one, one_mul]

private lemma minpoly_dvd_map (x : K) :
    minpoly (v₀.adicCompletion F) (algebraMap K (w₀.1.adicCompletion K) x) ∣
      (minpoly F x).map (algebraMap F (v₀.adicCompletion F)) :=
  minpoly.dvd _ _ <| by rw [aeval_map_algebraMap, aeval_algebraMap_apply, minpoly.aeval, map_zero]

private lemma exists_forall_aeval_eq (hα : ℚ⟮(α : K)⟯ = ⊤)
    (y : (w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal}) →
      w.1.adicCompletion K) :
    ∃ f : (v.adicCompletion ℚ)[X], ∀ w, aeval (algebraMap K (w.1.adicCompletion K) α) f = y w := by
  have hint : IsIntegral ℚ (α : K) := .of_finite ℚ _
  rcases (piPowerBasis v (.ofAdjoinSimpleEqTop hint hα)).exists_eq_aeval' y with ⟨f, hf⟩
  exact ⟨f, fun w ↦ by rw [← PowerBasis.ofAdjoinSimpleEqTop_gen hint hα, ← piPowerBasis_gen,
    ← aeval_pi_apply₂, ← hf]⟩

/-- **The `p`-adic factor of a prime is irreducible** over `ℚ_v`. -/
lemma irreducible_padicFactor : Irreducible (padicFactor α v w) :=
  minpoly.irreducible (IsIntegral.of_finite _ _)

/-- **The `p`-adic factor of a prime divides the minimal polynomial of `α`** over `ℚ_v`. -/
lemma padicFactor_dvd :
    padicFactor α v w ∣ (minpoly ℤ (α : K)).map (algebraMap ℤ (v.adicCompletion ℚ)) := by
  convert minpoly_dvd_map v w (α : K) using 1
  · rfl
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ α.isIntegral_coe, Polynomial.map_map]
  congr 1

lemma adjoin_completion_algebraMap_eq_top (hα : ℚ⟮(α : K)⟯ = ⊤) :
    (v.adicCompletion ℚ)⟮algebraMap K (w.1.adicCompletion K) α⟯ = ⊤ := by
  classical
  have hsurj : Function.Surjective (aeval (algebraMap K (w.1.adicCompletion K) α) :
      (v.adicCompletion ℚ)[X] →ₐ[v.adicCompletion ℚ] w.1.adicCompletion K) := fun y ↦ by
    rcases exists_forall_aeval_eq α v hα (Pi.single w y) with ⟨f, hf⟩
    exact ⟨f, by rw [hf, Pi.single_eq_same]⟩
  refine IntermediateField.toSubalgebra_injective ?_
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (IsIntegral.of_finite _ _).isAlgebraic, IntermediateField.top_toSubalgebra]
  exact (Algebra.adjoin_singleton_eq_range_aeval _ _).trans ((AlgHom.range_eq_top _).2 hsurj)

/-- **The degree of the `p`-adic factor of `𝔭` is `e(𝔭/p) f(𝔭/p)`** (Cremona–Page–Sutherland,
arXiv:2005.09491, §2.2): the image of `α` generates the completion `K_𝔭` over `ℚ_p`, whose degree
is `e f`. -/
lemma natDegree_padicFactor (hα : ℚ⟮(α : K)⟯ = ⊤) : (padicFactor α v w).natDegree =
    w.1.asIdeal.ramificationIdx (𝓞 ℚ) * w.1.asIdeal.inertiaDeg (𝓞 ℚ) := by
  rw [← finrank_adicCompletion v w.1 (K := ℚ) (L := K)]
  exact (Field.primitive_element_iff_minpoly_natDegree_eq _ _).mp
    (adjoin_completion_algebraMap_eq_top α v w hα)

/-- **Distinct primes above `p` have distinct `p`-adic factors** (Cremona–Page–Sutherland,
arXiv:2005.09491, §2.2, after Janusz, Theorem 3.8): the images of `α` in the completions `K_𝔭`,
`𝔭 ∣ p`, generate `∏_{𝔭 ∣ p} K_𝔭 ≅ ℚ_p ⊗ K` over `ℚ_p`, so a polynomial vanishing at one of
them and not at another exists. -/
lemma padicFactor_injective (hα : ℚ⟮(α : K)⟯ = ⊤) : Function.Injective (padicFactor α v) := by
  classical
  intro w u hwu
  by_contra hne
  rcases exists_forall_aeval_eq α v hα (Pi.single u 1) with ⟨f, hf⟩
  have hdvd : padicFactor α v u ∣ f := by
    rw [← hwu]
    exact minpoly.dvd _ _ <| by rw [hf, Pi.single_eq_of_ne hne]
  have hu : aeval (algebraMap K (u.1.adicCompletion K) α) f = 1 := by
    rw [hf, Pi.single_eq_same]
  exact zero_ne_one <| (aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (minpoly.aeval _ _)).symm.trans hu

/-- **The `p`-adic factors have `p`-adic integer coefficients**, by Gauss's lemma: they are monic
factors over `ℚ_p` of the minimal polynomial of `α`, which has integer coefficients. -/
lemma norm_coeff_padicFactorPadic_le_one (i : ℕ) : ‖(padicFactorPadic α v w).coeff i‖ ≤ 1 := by
  have hint : IsIntegral ℤ (α : K) := α.isIntegral_coe
  have hdvd : padicFactorPadic α v w ∣
      ((minpoly ℤ (α : K)).map (algebraMap ℤ ℤ_[primesEquiv v])).map
        (algebraMap ℤ_[primesEquiv v] ℚ_[primesEquiv v]) := by
    convert Polynomial.map_dvd
      (adicCompletion.padicEquiv v : v.adicCompletion ℚ →+* ℚ_[primesEquiv v])
      (padicFactor_dvd α v w) using 1
    · rfl
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact RingHom.ext_int _ _
  have hmonic : (padicFactorPadic α v w).Monic :=
    (minpoly.monic (IsIntegral.of_finite _ _)).map _
  rcases IsIntegrallyClosed.eq_map_mul_C_of_dvd _ ((minpoly.monic hint).map _) hdvd with ⟨g, hg⟩
  rw [← hg, hmonic.leadingCoeff, C_1, mul_one, coeff_map]
  exact (g.coeff i).norm_le_one

/-- **Distinct primes above `p` have distinct digit vectors** (`Polynomial.padicDigits`) of their
`p`-adic factors, which are distinct polynomials with `p`-adic integer coefficients. -/
lemma padicDigits_padicFactorPadic_injective (hα : ℚ⟮(α : K)⟯ = ⊤) :
    Function.Injective fun w ↦ (padicFactorPadic α v w).padicDigits := fun w u h ↦
  padicFactor_injective α v hα <| map_injective _ (RingHom.injective _) <|
    eq_of_padicDigits_eq (norm_coeff_padicFactorPadic_le_one α v w)
      (norm_coeff_padicFactorPadic_le_one α v u) h

variable {w} in
lemma padicDigits_padicFactorPadic_congr {v' : HeightOneSpectrum (𝓞 ℚ)} (hv : v = v')
    {w' : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v'.asIdeal}} (hw : w.1 = w'.1) :
    (padicFactorPadic α v w).padicDigits = (padicFactorPadic α v' w').padicDigits := by
  subst hv
  rw [Subtype.ext hw]

lemma natGenerator_under : natGenerator (𝔭.under (𝓞 ℚ)) = TauCeti.rationalPrimeBelow 𝔭 := by
  refine (Nat.prime_dvd_prime_iff_eq (prime_natGenerator _)
    (TauCeti.prime_rationalPrimeBelow 𝔭)).mp ?_
  rw [natGenerator_dvd_iff, ← Ideal.comap_symm, Ideal.mem_comap, map_natCast, under_asIdeal,
    Ideal.under_def, Ideal.mem_comap, map_natCast]
  exact_mod_cast (𝔭.intCast_mem_asIdeal_iff _).mpr dvd_rfl

variable {𝔭} in
lemma rationalPrimeBelow_eq_of_absNorm_dvd (h : Ideal.absNorm 𝔮.asIdeal ∣ Ideal.absNorm 𝔭.asIdeal) :
    TauCeti.rationalPrimeBelow 𝔮 = TauCeti.rationalPrimeBelow 𝔭 := by
  rw [TauCeti.absNorm_eq_rationalPrimeBelow_pow, TauCeti.absNorm_eq_rationalPrimeBelow_pow] at h
  exact (Nat.prime_dvd_prime_iff_eq (TauCeti.prime_rationalPrimeBelow 𝔮)
    (TauCeti.prime_rationalPrimeBelow 𝔭)).mp <|
      (TauCeti.prime_rationalPrimeBelow 𝔮).dvd_of_dvd_pow <|
        (dvd_pow_self _ (Ideal.inertiaDeg_pos 𝔮.asIdeal ℤ).ne').trans h

variable {𝔭} in
/-- **Primes of equal norm lie above the same prime of `ℚ`**: the norm of `𝔭` is `p ^ f(𝔭)`. -/
lemma under_eq_of_absNorm_eq (h : Ideal.absNorm 𝔭.asIdeal = Ideal.absNorm 𝔮.asIdeal) :
    𝔭.under (𝓞 ℚ) = 𝔮.under (𝓞 ℚ) := by
  have hp : TauCeti.rationalPrimeBelow 𝔭 = TauCeti.rationalPrimeBelow 𝔮 :=
    rationalPrimeBelow_eq_of_absNorm_dvd (h ▸ dvd_rfl)
  exact primesEquiv.injective <| Subtype.ext <|
    (natGenerator_under 𝔭).trans <| hp.trans (natGenerator_under 𝔮).symm

/-- The **digit vector of a prime** `𝔭` of `K` (LMFDB `nf.ideal_labels`): that of its `p`-adic
factor, `p` the prime of `ℚ` below `𝔭` (Cremona–Page–Sutherland, arXiv:2005.09491, §2.2). -/
noncomputable def primeDigits : Lex (ℕ → Lex (ℕ → ℕ)) :=
  (padicFactorPadic α (𝔭.under (𝓞 ℚ)) ⟨𝔭, ⟨rfl⟩⟩).padicDigits

/-- The **Cremona–Page–Sutherland key** (LMFDB `nf.ideal_labels`) of a prime `𝔭` of `K`, for the
integral primitive element `α` (arXiv:2005.09491, §2): its norm `N(𝔭) = p ^ f`, its ramification
index `e(𝔭/p)` and the digit vector of its `p`-adic factor, ordered lexicographically. The primes
are ordered first by norm, then by ramification index, and the primes above the same `p` of the same
norm and ramification index by the lexicographic order of the digit vectors of their `p`-adic
factors. -/
noncomputable def primeKey : ℕ ×ₗ ℕ ×ₗ Lex (ℕ → Lex (ℕ → ℕ)) :=
  toLex (Ideal.absNorm 𝔭.asIdeal, toLex (𝔭.asIdeal.ramificationIdx ℤ, primeDigits α 𝔭))

/-- **The Cremona–Page–Sutherland key determines the prime**: primes of equal norm lie above the
same `p`, and distinct primes above `p` have distinct digit vectors. -/
lemma primeKey_injective (hα : ℚ⟮(α : K)⟯ = ⊤) : Function.Injective (primeKey α) := by
  intro 𝔭 𝔮 h
  have hv : 𝔭.under (𝓞 ℚ) = 𝔮.under (𝓞 ℚ) :=
    under_eq_of_absNorm_eq <| congrArg (fun k ↦ (ofLex k).1) h
  have hd : primeDigits α 𝔭 = primeDigits α 𝔮 := congrArg (fun k ↦ (ofLex (ofLex k).2).2) h
  have hw : (⟨𝔭, ⟨rfl⟩⟩ :
      {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver (𝔭.under (𝓞 ℚ)).asIdeal}) =
        ⟨𝔮, ⟨congrArg asIdeal hv⟩⟩ :=
    padicDigits_padicFactorPadic_injective α _ hα <| hd.trans <|
      padicDigits_padicFactorPadic_congr α (𝔮.under (𝓞 ℚ)) hv.symm rfl
  exact congrArg Subtype.val hw

/-- The **Cremona–Page–Sutherland order** (LMFDB `nf.ideal_labels`) on the primes of a number field
`K`, for an integral primitive element `α` of `K` (arXiv:2005.09491, §2): the order of the keys
`primeKey α`, a total order since the key determines the prime. The LMFDB takes `K = ℚ[X]/(g)` and
`α` the class of `X`, `g` the reduced defining polynomial of `K` (`NumberField.polredabs`). -/
@[instance_reducible]
noncomputable def primeLinearOrder (hα : ℚ⟮(α : K)⟯ = ⊤) : LinearOrder (HeightOneSpectrum (𝓞 K)) :=
  LinearOrder.lift' (primeKey α) (primeKey_injective α hα)

end NumberField
