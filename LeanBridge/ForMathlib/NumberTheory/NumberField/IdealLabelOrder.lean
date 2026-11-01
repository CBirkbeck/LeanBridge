import LeanBridge.ForMathlib.NumberTheory.NumberField.IdealNormLabel
import LeanBridge.ForMathlib.NumberTheory.NumberField.Polredabs
import LeanBridge.ForMathlib.NumberTheory.NumberField.PrimeIdealOrder
import Mathlib.Data.Finsupp.Lex
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

/-!
# Cremona–Page–Sutherland labels of the ideals of a number field

Cremona, Page and Sutherland (*Sorting and labelling integral ideals in a number field*,
arXiv:2005.09491, §3) extend their order on the primes of a number field `K = ℚ(α)`
(`NumberField.primeKey`) to all nonzero ideals of `𝓞 K`, first by norm and then, among the
ideals of norm `N = p₁^{a₁} ⋯ p_k^{a_k}`, `p₁ < ⋯ < p_k`, lexicographically on the factorisation
`𝔞 = 𝔞₁ ⋯ 𝔞_k` into ideals `𝔞ᵢ` of norm `pᵢ^{aᵢ}`; two ideals `𝔞 = ∏ 𝔭ᵢ^{vᵢ}` and `𝔟 = ∏ 𝔭ᵢ^{wᵢ}` of
the same `p`-power norm, `𝔭₁ < ⋯ < 𝔭_r` the primes above `p`, are compared by their weights
`∑ vᵢ` and `∑ wᵢ` and then by the reverse lexicographic order of `(v₁, …, v_r)` and
`(w₁, …, w_r)`. The ideal label `N.i` of `𝔞` (LMFDB `nf.ideal_labels`) is its norm `N` and its
position `i` among the ideals of norm `N`.

Here the comparison of two ideals of the same norm is the lexicographic order of a finitely
supported function, indexed by the pairs `(p, ⊥)` and `(p, 𝔭)`, `𝔭` a prime above `p`, ordered by
`p`, then `⊥` before the primes, then the primes in their order: its value at `(p, ⊥)` is the
weight `∑_{𝔭 ∣ p} v_𝔭(𝔞)` of the `p`-part of `𝔞` and at `(p, 𝔭)` it is `-v_𝔭(𝔞)`, the sign making
the order on the exponents the reverse lexicographic one (the authors' code, `psort.py` in
github.com/JohnCremona/Sorting, likewise sorts the exponent vectors `v` by `(∑ vᵢ, -v)`). Two
ideals of the same norm first differ at the least `p` at which their `p`-parts differ, and there
the comparison is that of the paper.

The LMFDB represents a number field as `ℚ[X]/(g)`, `g` its reduced defining polynomial
(`NumberField.polredabs`, LMFDB `nf.polredabs`), and takes for `α` the class of `X`, an integral
primitive element; `NumberField.lmfdbIdealLabel` is the label for that choice.

## Main definitions

* `NumberField.weightSlot`, `NumberField.primeSlot`: the indices of the key of an ideal.
* `NumberField.idealKey` (LMFDB `nf.ideal_labels`): the key ordering the ideals of a given norm.
* `NumberField.IdealLT` (LMFDB `nf.ideal_labels`): the Cremona–Page–Sutherland order on ideals.
* `NumberField.idealLabel` (LMFDB `nf.ideal_labels`): the ideal label `N.i`.
* `NumberField.lmfdbIdealLabel` (LMFDB `nf.ideal_labels`): the ideal label for the class of `X` in
  `ℚ[X]/(g)`, `g` the reduced defining polynomial.

## Main results

* `NumberField.idealKey_injOn`: the key determines a nonzero ideal.
* `NumberField.isStrictTotalOrder_idealLT`: the order is a strict total order.
* `NumberField.idealLabel_injective`: an ideal is determined by its label.
* `NumberField.exists_idealLabel_eq`: the labels of the ideals of norm `N` are `N.1, …, N.m`.
* `NumberField.idealLT_of_absNorm_eq`: the prime ideals come first among the ideals of their norm.
* `NumberField.idealLT_asIdeal_iff`: the primes of a given norm are ordered by their keys.
* `NumberField.isIntegral_algEquiv_root`, `NumberField.adjoin_algEquiv_root_eq_top`: the class of
  `X` in `ℚ[X]/(g)`, `g ∈ ℤ[X]` monic, is an integral primitive element.
* `NumberField.lmfdbIdealLabel_injective`: an ideal is determined by its LMFDB label.
-/

open IsDedekindDomain HeightOneSpectrum NumberField Polynomial UniqueFactorizationMonoid

open scoped IntermediateField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] (α : 𝓞 K) {P Q I J : Ideal (𝓞 K)} {g : ℤ[X]}
  (e : AdjoinRoot (g.map (Int.castRingHom ℚ)) ≃ₐ[ℚ] K) (𝔭 : HeightOneSpectrum (𝓞 K))
  {𝔮 : HeightOneSpectrum (𝓞 K)} (e₀ : AdjoinRoot ((polredabs K).map (Int.castRingHom ℚ)) ≃ₐ[ℚ] K)

variable (P) in
/-- The slot `(p, ⊥)` of the weight of the `p`-part of an ideal, for an ideal `P` above `p`, in the
key of an ideal (`idealKey`). -/
noncomputable def weightSlot : ℕ ×ₗ WithBot (ℕ ×ₗ ℕ ×ₗ Lex (ℕ → Lex (ℕ → ℕ))) :=
  toLex (Ideal.absNorm (P.under ℤ), ⊥)

open scoped Classical in
variable (P) in
/-- The slot `(p, 𝔭)` of the exponent of a nonzero prime `𝔭` above `p` in the key of an ideal
(`idealKey`), with `𝔭` given by its key `primeKey α 𝔭`; `(p, ⊥)` for the other ideals. -/
noncomputable def primeSlot : ℕ ×ₗ WithBot (ℕ ×ₗ ℕ ×ₗ Lex (ℕ → Lex (ℕ → ℕ))) :=
  toLex (Ideal.absNorm (P.under ℤ),
    if h : P.IsPrime ∧ P ≠ ⊥ then (primeKey α ⟨P, h.1, h.2⟩ : WithBot _) else ⊥)

open scoped Classical in
variable (I) in
/-- The **Cremona–Page–Sutherland key** (LMFDB `nf.ideal_labels`) of an ideal `𝔞` of `𝓞 K`, for
the integral primitive element `α` (arXiv:2005.09491, §3): the finitely supported function with
value `∑_{𝔭 ∣ p} v_𝔭(𝔞)` at `(p, ⊥)` and `-v_𝔭(𝔞)` at `(p, 𝔭)` for a prime `𝔭` above `p`, ordered
lexicographically. Among the ideals of a given norm, its order is that of the paper: the
lexicographic order on the `p`-parts, `p` increasing, each compared by weight and then by the
reverse lexicographic order of the exponents, the primes above `p` being in their order
(`NumberField.primeKey`). -/
noncomputable def idealKey : Lex (ℕ ×ₗ WithBot (ℕ ×ₗ ℕ ×ₗ Lex (ℕ → Lex (ℕ → ℕ))) →₀ ℤ) :=
  toLex (((factorization I).mapDomain weightSlot).mapRange ((↑) : ℕ → ℤ) Nat.cast_zero -
    ((factorization I).mapDomain (primeSlot α)).mapRange ((↑) : ℕ → ℤ) Nat.cast_zero)

variable (I J) in
/-- The **Cremona–Page–Sutherland order** (LMFDB `nf.ideal_labels`) on the ideals of `𝓞 K`, for
the integral primitive element `α` (arXiv:2005.09491, §3): by norm, and then by the key
`idealKey α`. -/
def IdealLT : Prop :=
  toLex (Ideal.absNorm I, idealKey α I) < toLex (Ideal.absNorm J, idealKey α J)

open scoped Classical in
variable (I) in
lemma support_factorization_subset :
    ((factorization I).support : Set (Ideal (𝓞 K))) ⊆ {P | P.IsPrime ∧ P ≠ ⊥} := fun P hP ↦ by
  rw [Finset.mem_coe, support_factorization, Multiset.mem_toFinset] at hP
  have hprime : Prime P := prime_of_normalized_factor P hP
  exact ⟨Ideal.isPrime_of_prime hprime, hprime.ne_zero⟩

lemma primeSlot_of_isPrime (hP : P.IsPrime ∧ P ≠ ⊥) : primeSlot α P =
    toLex (Ideal.absNorm (P.under ℤ), (primeKey α ⟨P, hP.1, hP.2⟩ : WithBot _)) := by
  rw [primeSlot, dite_eq_left hP]

lemma primeSlot_injOn (hα : ℚ⟮(α : K)⟯ = ⊤) :
    Set.InjOn (primeSlot α) {P : Ideal (𝓞 K) | P.IsPrime ∧ P ≠ ⊥} := fun P hP Q hQ h ↦ by
  have hk : primeKey α ⟨P, hP.1, hP.2⟩ = primeKey α ⟨Q, hQ.1, hQ.2⟩ := by
    have h' : (ofLex (primeSlot α P)).2 = (ofLex (primeSlot α Q)).2 :=
      congrArg (fun s ↦ (ofLex s).2) h
    simpa only [primeSlot_of_isPrime α hP, primeSlot_of_isPrime α hQ, ofLex_toLex,
      WithBot.coe_inj] using h'
  exact congrArg asIdeal (primeKey_injective α hα hk)

variable (Q) in
lemma weightSlot_ne_primeSlot (hP : P.IsPrime ∧ P ≠ ⊥) : weightSlot Q ≠ primeSlot α P := fun h ↦ by
  rw [primeSlot_of_isPrime α hP] at h
  exact WithBot.bot_ne_coe (congrArg (fun s ↦ (ofLex s).2) h)

open scoped Classical in
lemma idealKey_apply_primeSlot (hα : ℚ⟮(α : K)⟯ = ⊤) (𝔞 : Ideal (𝓞 K)) (hP : P.IsPrime ∧ P ≠ ⊥) :
    ofLex (idealKey α 𝔞) (primeSlot α P) = -(factorization 𝔞 P : ℤ) := by
  rw [idealKey, ofLex_toLex, Finsupp.sub_apply, Finsupp.mapRange_apply, Finsupp.mapRange_apply,
    Finsupp.mapDomain_of_notMem_range _ _ fun ⟨Q, hQ⟩ ↦ weightSlot_ne_primeSlot α Q hP hQ,
    Finsupp.mapDomain_apply' _ _ (support_factorization_subset 𝔞) (primeSlot_injOn α hα) hP,
    Nat.cast_zero, zero_sub]

/-- **The Cremona–Page–Sutherland key determines a nonzero ideal**: its values at the slots of the
primes are the exponents of its factorisation. -/
lemma idealKey_injOn (hα : ℚ⟮(α : K)⟯ = ⊤) :
    Set.InjOn (idealKey α) {I : Ideal (𝓞 K) | I ≠ ⊥} := fun I hI J hJ h ↦ by
  classical
  refine associated_iff_eq.mp (associated_of_factorization_eq I J hI hJ (Finsupp.ext fun P ↦ ?_))
  by_cases hP : P.IsPrime ∧ P ≠ ⊥
  · have h' : ofLex (idealKey α I) (primeSlot α P) = ofLex (idealKey α J) (primeSlot α P) :=
      DFunLike.congr_fun (congrArg ofLex h) (primeSlot α P)
    simpa only [idealKey_apply_primeSlot α hα _ hP, neg_inj, Nat.cast_inj] using h'
  · rw [Finsupp.notMem_support_iff.mp fun hm ↦ hP (support_factorization_subset I hm),
      Finsupp.notMem_support_iff.mp fun hm ↦ hP (support_factorization_subset J hm)]

lemma eq_of_absNorm_eq_of_idealKey_eq (hα : ℚ⟮(α : K)⟯ = ⊤)
    (hN : Ideal.absNorm I = Ideal.absNorm J) (h : idealKey α I = idealKey α J) : I = J := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · exact (Ideal.absNorm_eq_zero_iff.mp (hN.symm.trans Ideal.absNorm_bot)).symm
  · exact idealKey_injOn α hα hI
      (fun hJ ↦ hI (Ideal.absNorm_eq_zero_iff.mp (hN.trans (hJ ▸ Ideal.absNorm_bot)))) h

lemma idealLT_iff_idealKey_lt (hN : Ideal.absNorm I = Ideal.absNorm J) :
    IdealLT α I J ↔ idealKey α I < idealKey α J :=
  ⟨fun h ↦ ((Prod.lex_def.mp h).resolve_left hN.not_lt).2,
    fun h ↦ Prod.lex_def.mpr (.inr ⟨hN, h⟩)⟩

/-- **The Cremona–Page–Sutherland order is a strict total order** on the ideals of `𝓞 K`. -/
lemma isStrictTotalOrder_idealLT (hα : ℚ⟮(α : K)⟯ = ⊤) :
    IsStrictTotalOrder (Ideal (𝓞 K)) (IdealLT α) where
  trichotomous I J hIJ hJI := by
    have h : toLex (Ideal.absNorm I, idealKey α I) = toLex (Ideal.absNorm J, idealKey α J) :=
      le_antisymm (not_lt.mp hJI) (not_lt.mp hIJ)
    exact eq_of_absNorm_eq_of_idealKey_eq α hα (congrArg (fun k ↦ (ofLex k).1) h)
      (congrArg (fun k ↦ (ofLex k).2) h)
  irrefl _ := lt_irrefl _
  trans _ _ _ := lt_trans

variable (I) in
/-- The **ideal label** `N.i` (LMFDB `nf.ideal_labels`) of an ideal `I` of `𝓞 K`, for the integral
primitive element `α` of `K` (Cremona–Page–Sutherland, arXiv:2005.09491, §3), as the pair
`(N, i)`: its norm `N = [𝓞 K : I]` and its index `i` in the list of the ideals of norm `N` sorted by
the Cremona–Page–Sutherland order `IdealLT α`. The LMFDB takes `K = ℚ[X]/(g)` and `α` the class of
`X`, `g` the reduced defining polynomial of `K` (`NumberField.polredabs`), and labels the nonzero
ideals. The order is total when `α` generates `K` (`isStrictTotalOrder_idealLT`), and then the label
determines the ideal (`idealLabel_injective`). -/
noncomputable def idealLabel : ℕ × ℕ :=
  Ideal.normLabel (IdealLT α) I

/-- **An ideal is determined by its label.** -/
lemma idealLabel_injective (hα : ℚ⟮(α : K)⟯ = ⊤) : Function.Injective (idealLabel α) := by
  have : IsStrictTotalOrder (Ideal (𝓞 K)) (IdealLT α) := isStrictTotalOrder_idealLT α hα
  exact Ideal.normLabel_injective (IdealLT α)

/-- **The labels of the ideals of norm `N` are `N.1, …, N.m`**, `m` the number of ideals of norm
`N`. -/
lemma exists_idealLabel_eq (hα : ℚ⟮(α : K)⟯ = ⊤) {N i : ℕ} (hi : 1 ≤ i)
    (hiN : i ≤ {J : Ideal (𝓞 K) | Ideal.absNorm J = N}.ncard) :
    ∃ I : Ideal (𝓞 K), idealLabel α I = (N, i) := by
  have : IsStrictTotalOrder (Ideal (𝓞 K)) (IdealLT α) := isStrictTotalOrder_idealLT α hα
  exact Ideal.exists_normLabel_eq (IdealLT α) hi hiN

open scoped Classical in
lemma idealKey_asIdeal : ofLex (idealKey α 𝔭.asIdeal) = Finsupp.single (weightSlot 𝔭.asIdeal) 1 -
    Finsupp.single (primeSlot α 𝔭.asIdeal) 1 := by
  rw [idealKey, ofLex_toLex, factorization,
    normalizedFactors_irreducible (Ideal.prime_of_isPrime 𝔭.ne_bot 𝔭.isPrime).irreducible,
    normalize_eq, Multiset.toFinsupp_singleton, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
    Finsupp.mapRange_single, Finsupp.mapRange_single, Nat.cast_one]

variable {𝔭} in
lemma weightSlot_eq_of_absNorm_dvd (h : Ideal.absNorm 𝔮.asIdeal ∣ Ideal.absNorm 𝔭.asIdeal) :
    weightSlot 𝔮.asIdeal = weightSlot 𝔭.asIdeal :=
  congrArg (fun n : ℕ ↦ (toLex (n, ⊥) : ℕ ×ₗ WithBot (ℕ ×ₗ ℕ ×ₗ Lex (ℕ → Lex (ℕ → ℕ)))))
    (rationalPrimeBelow_eq_of_absNorm_dvd h)

open scoped Classical in
lemma weightSlot_eq_of_mem_support (hN : Ideal.absNorm J = Ideal.absNorm 𝔭.asIdeal)
    (hQ : Q ∈ (factorization J).support) : weightSlot Q = weightSlot 𝔭.asIdeal := by
  have hQp : Q.IsPrime ∧ Q ≠ ⊥ := support_factorization_subset J hQ
  rw [support_factorization, Multiset.mem_toFinset] at hQ
  have hdvd : Ideal.absNorm Q ∣ Ideal.absNorm 𝔭.asIdeal :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ))
  exact weightSlot_eq_of_absNorm_dvd (𝔮 := ⟨Q, hQp.1, hQp.2⟩) hdvd

lemma weightSlot_lt_primeSlot (hP : P.IsPrime ∧ P ≠ ⊥) : weightSlot P < primeSlot α P := by
  rw [weightSlot, primeSlot_of_isPrime α hP]
  exact Prod.lex_def.mpr (.inr ⟨rfl, WithBot.bot_lt_coe _⟩)

lemma two_le_card_normalizedFactors (hJ : J ≠ ⊥) (hJp : ¬J.IsPrime) (hJt : J ≠ ⊤) :
    2 ≤ Multiset.card (normalizedFactors J) := by
  have h0 : Multiset.card (normalizedFactors J) ≠ 0 := fun h ↦
    hJt (Ideal.isUnit_iff.mp ((normalizedFactors_eq_zero_iff hJ).mp (Multiset.card_eq_zero.mp h)))
  have h1 : Multiset.card (normalizedFactors J) ≠ 1 := fun h ↦ by
    rcases Multiset.card_eq_one.mp h with ⟨Q, hQ⟩
    have hQJ : Associated (normalizedFactors J).prod J := prod_normalizedFactors hJ
    rw [hQ, Multiset.prod_singleton] at hQJ
    exact hJp (associated_iff_eq.mp hQJ ▸
      Ideal.isPrime_of_prime (prime_of_normalized_factor Q (hQ ▸ Multiset.mem_singleton_self Q)))
  omega

open scoped Classical in
/-- **Prime ideals come first** among the ideals of their norm (Cremona–Page–Sutherland,
arXiv:2005.09491, §3): a nonzero prime `𝔭` is smaller than every nonzero ideal of the same norm
that is not prime. Such an ideal has weight at least `2` at the prime `p` below `𝔭`, and `𝔭` has
weight `1`. -/
lemma idealLT_of_absNorm_eq (hJ : J ≠ ⊥) (hJp : ¬J.IsPrime)
    (hN : Ideal.absNorm J = Ideal.absNorm 𝔭.asIdeal) : IdealLT α 𝔭.asIdeal J := by
  have hJt : J ≠ ⊤ := by
    rintro rfl
    exact 𝔭.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp (hN.symm.trans Ideal.absNorm_top))
  have hw : ∀ Q ∈ (factorization J).support, weightSlot Q = weightSlot 𝔭.asIdeal :=
    fun Q hQ ↦ weightSlot_eq_of_mem_support 𝔭 hN hQ
  have hpJ : ∀ j ≤ weightSlot 𝔭.asIdeal, (factorization J).mapDomain (primeSlot α) j = 0 :=
    fun j hj ↦ Finsupp.mapDomain_of_notMem_image_support fun ⟨Q, hQ, hQj⟩ ↦
      (hw Q hQ ▸ weightSlot_lt_primeSlot α (support_factorization_subset J hQ)).not_ge (hQj ▸ hj)
  have hwJ : ∀ j ≠ weightSlot 𝔭.asIdeal, (factorization J).mapDomain weightSlot j = 0 :=
    fun j hj ↦ Finsupp.mapDomain_of_notMem_image_support fun ⟨Q, hQ, hQj⟩ ↦ hj (hQj ▸ hw Q hQ)
  have hcard : (factorization J).mapDomain weightSlot (weightSlot 𝔭.asIdeal) =
      Multiset.card (normalizedFactors J) := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply, ← Multiset.toFinsupp_sum_eq]
    exact Finsupp.sum_congr fun Q hQ ↦ by rw [hw Q hQ, Finsupp.single_eq_same, id]
  have h𝔭 : weightSlot 𝔭.asIdeal < primeSlot α 𝔭.asIdeal :=
    weightSlot_lt_primeSlot α ⟨𝔭.isPrime, 𝔭.ne_bot⟩
  refine (idealLT_iff_idealKey_lt α hN.symm).mpr <|
    Finsupp.lex_def.mpr ⟨weightSlot 𝔭.asIdeal, fun j hj ↦ ?_, ?_⟩
  · rw [idealKey_asIdeal, idealKey, ofLex_toLex, Finsupp.sub_apply, Finsupp.sub_apply,
      Finsupp.single_eq_of_ne hj.ne, Finsupp.single_eq_of_ne (hj.trans h𝔭).ne,
      Finsupp.mapRange_apply, Finsupp.mapRange_apply, hwJ j hj.ne, hpJ j hj.le, Nat.cast_zero]
  · rw [idealKey_asIdeal, idealKey, ofLex_toLex, Finsupp.sub_apply, Finsupp.sub_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne h𝔭.ne, Finsupp.mapRange_apply,
      Finsupp.mapRange_apply, hcard, hpJ _ le_rfl]
    have h2 : 2 ≤ Multiset.card (normalizedFactors J) := two_le_card_normalizedFactors hJ hJp hJt
    omega

variable {𝔭} in
open scoped Classical in
lemma idealKey_lt_of_primeKey_lt (hN : Ideal.absNorm 𝔭.asIdeal = Ideal.absNorm 𝔮.asIdeal)
    (h : primeKey α 𝔭 < primeKey α 𝔮) : idealKey α 𝔭.asIdeal < idealKey α 𝔮.asIdeal := by
  have hp : TauCeti.rationalPrimeBelow 𝔭 = TauCeti.rationalPrimeBelow 𝔮 :=
    rationalPrimeBelow_eq_of_absNorm_dvd (hN ▸ dvd_rfl)
  have hs : weightSlot 𝔮.asIdeal = weightSlot 𝔭.asIdeal :=
    weightSlot_eq_of_absNorm_dvd (hN ▸ dvd_rfl)
  have htt : primeSlot α 𝔭.asIdeal < primeSlot α 𝔮.asIdeal := by
    rw [primeSlot_of_isPrime α ⟨𝔭.isPrime, 𝔭.ne_bot⟩, primeSlot_of_isPrime α ⟨𝔮.isPrime, 𝔮.ne_bot⟩]
    exact Prod.lex_def.mpr (.inr ⟨hp, WithBot.coe_lt_coe.mpr h⟩)
  have h𝔭 : weightSlot 𝔭.asIdeal < primeSlot α 𝔭.asIdeal :=
    weightSlot_lt_primeSlot α ⟨𝔭.isPrime, 𝔭.ne_bot⟩
  refine Finsupp.lex_def.mpr ⟨primeSlot α 𝔭.asIdeal, fun j hj ↦ ?_, ?_⟩
  · rw [idealKey_asIdeal, idealKey_asIdeal, hs, Finsupp.sub_apply, Finsupp.sub_apply,
      Finsupp.single_eq_of_ne hj.ne, Finsupp.single_eq_of_ne (hj.trans htt).ne]
  · rw [idealKey_asIdeal, idealKey_asIdeal, hs, Finsupp.sub_apply, Finsupp.sub_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne h𝔭.ne', Finsupp.single_eq_of_ne htt.ne]
    norm_num

variable {𝔭} in
/-- **The primes of a given norm are ordered as in the order on primes** (Cremona–Page–Sutherland,
arXiv:2005.09491, §3): on the primes of norm `N`, the order of the ideals is that of their keys
`primeKey α`. -/
lemma idealLT_asIdeal_iff (hα : ℚ⟮(α : K)⟯ = ⊤)
    (hN : Ideal.absNorm 𝔭.asIdeal = Ideal.absNorm 𝔮.asIdeal) :
    IdealLT α 𝔭.asIdeal 𝔮.asIdeal ↔ primeKey α 𝔭 < primeKey α 𝔮 := by
  rw [idealLT_iff_idealKey_lt α hN]
  refine ⟨fun h ↦ ?_, idealKey_lt_of_primeKey_lt α hN⟩
  rcases lt_trichotomy (primeKey α 𝔭) (primeKey α 𝔮) with h' | h' | h'
  · exact h'
  · rw [primeKey_injective α hα h'] at h
    exact absurd h (lt_irrefl _)
  · exact absurd h (idealKey_lt_of_primeKey_lt α hN.symm h').not_gt

/-- **The class of `X` is integral** (LMFDB `nf.ideal_labels`): for a monic `g ∈ ℤ[X]` and an
isomorphism `e : ℚ[X]/(g) ≃ K`, the image of the class of `X` is an algebraic integer. -/
lemma isIntegral_algEquiv_root (hg : g.Monic) : IsIntegral ℤ (e (AdjoinRoot.root _)) := by
  refine IsIntegral.map e ⟨g, hg, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap ℚ, AdjoinRoot.aeval_eq]
  exact AdjoinRoot.mk_self

/-- **The class of `X` is a primitive element** (LMFDB `nf.ideal_labels`): for an isomorphism
`e : ℚ[X]/(g) ≃ K`, the image of the class of `X` generates `K`. -/
lemma adjoin_algEquiv_root_eq_top : ℚ⟮e (AdjoinRoot.root _)⟯ = ⊤ := by
  refine IntermediateField.adjoin_eq_top_of_algebra _ _ ?_
  rw [← Set.image_singleton, ← AlgEquiv.coe_toAlgHom, Algebra.adjoin_image,
    AdjoinRoot.adjoinRoot_eq_top, Algebra.map_top, AlgHom.range_eq_top, AlgEquiv.coe_toAlgHom]
  exact e.surjective

/-- The **LMFDB ideal label** `N.i` (LMFDB `nf.ideal_labels`) of an ideal of `𝓞 K`, for `K`
represented as `ℚ[X]/(g)` through an isomorphism `e₀`, `g = polredabs K` the reduced defining
polynomial of `K` (LMFDB `nf.polredabs`): the label `idealLabel α` for the canonical integral
primitive element `α`, the image of the class of `X`. The LMFDB's fields are `ℚ[X]/(g)` itself,
with `e₀` the identity (up to `polredabs K = g`, `IsPolredabs.eq`). For an abstract `K` the labels
depend on `e₀`: two such isomorphisms `e₀` and `σ ∘ e₀` differ by an automorphism `σ` of `K`, and
by transport of structure (not formalised here) the label of `𝔞` for `σ ∘ e₀` is that of `σ⁻¹(𝔞)`
for `e₀`. For instance, complex conjugation exchanges the ideals `5.1 = (i + 2)` and `5.2 = (i - 2)`
of `ℚ(i)`, so these labels are only defined up to `Aut(K)` on an abstract `K`. -/
noncomputable def lmfdbIdealLabel (𝔞 : Ideal (𝓞 K)) : ℕ × ℕ :=
  idealLabel ⟨e₀ (AdjoinRoot.root _), isIntegral_algEquiv_root e₀ (isPolredabs_polredabs K).1.1⟩ 𝔞

/-- **An ideal is determined by its LMFDB label.** -/
lemma lmfdbIdealLabel_injective : Function.Injective (lmfdbIdealLabel e₀) :=
  idealLabel_injective _ (adjoin_algEquiv_root_eq_top e₀)

end NumberField
