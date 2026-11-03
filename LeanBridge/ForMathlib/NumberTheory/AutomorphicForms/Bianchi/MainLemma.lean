import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.LevelOperators

/-!
# The Main Lemma of Atkin and Lehner for Bianchi forms

Let `K` be an imaginary quadratic field of class number `1`, embedded in `ℂ` by `σ`. The Main Lemma
of Atkin and Lehner (*Hecke operators on `Γ₀(m)`*, Math. Ann. 185 (1970), Theorem 1; Miyake,
*Modular forms*, 4.6.8; in the shape of the Main Lemma for Maass forms) says that a cusp form of
level `Γ₀(𝔑)` whose Fourier–Bessel coefficients vanish at every `α` prime to `𝔑` is old. The proof
involves no holomorphy, and carries over to Bianchi forms over the principal ideal domain `𝒪_K`,
with `n = N(q)` in place of a rational prime.

The vanishing of the coefficients is written without coefficients: for primes `q_1, …, q_r`, the
function `(1 - E_{q_r}) ⋯ (1 - E_{q_1}) F` (`HyperbolicThreeSpace.bianchiCoprimeFilter`), with
`E_q F = n⁻¹ ∑_{j mod q} F(x + j/q, y)`, keeps exactly the terms of the expansion of `F` whose index
is divisible by no `q_i`. If it vanishes, then `F` lies in the span of the `G ∣ (q_i, 0; 0, 1)`, `G`
of level `N / q_i`. The induction removes the prime `q = q_1`: `H = F - E_q F` has level `Nq`, so by
induction `H` is a sum of `G_p ∣ (p, 0; 0, 1)` with `G_p` of level `Nq / p`, `p ≠ q`. Applying the
trace from `Γ₀(Nq)` to `Γ₀(N)`, which fixes `F`, commutes with the level raising, and sends `E_q F`
to `(1 - c) F + c Z ∣ (q, 0; 0, 1)` with `c ≠ 0` and `Z` of level `N / q`
(`HyperbolicThreeSpace.sub_bianchiLevelTrace_bianchiPeriodAverage`), gives
`c (F - Z ∣ (q, 0; 0, 1)) = ∑_p (Tr G_p) ∣ (p, 0; 0, 1)`.

## Main definitions

* `HyperbolicThreeSpace.bianchiPrimeFilter`: the function `F - E_q F`.
* `HyperbolicThreeSpace.bianchiCoprimeFilter`: the function `(1 - E_{q_r}) ⋯ (1 - E_{q_1}) F`.
* `HyperbolicThreeSpace.bianchiOldPart`: the part of the old space coming from a list of primes.

## Main results

* `HyperbolicThreeSpace.mem_bianchiOldPart_of_bianchiCoprimeFilter_eq_zero`: the Main Lemma for a
  list of primes.
* `HyperbolicThreeSpace.bianchiOldPart_le_bianchiOldforms`: that part lies in the oldforms.
* `HyperbolicThreeSpace.sum_cexp_eq`: the sum of an additive character of `𝒪_K / (q)`.
* `HyperbolicThreeSpace.HasBianchiWhittakerExpansion.primeFilter`: the filter on expansions.
* `HyperbolicThreeSpace.mem_bianchiOldforms_of_coeff_eq_zero`: the Main Lemma, a form whose
  Fourier–Bessel coefficients vanish at every index prime to the level is old.
-/

open Complex Ideal Matrix Module NumberField HilbertModularGroup

open Ideal renaming Quotient.mk → quotientMk, Quotient.mk_out → quotientMk_out

open scoped ComplexConjugate MatrixGroups nonZeroDivisors Real

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] {σ : K →+* ℂ} {δ : ℂ} {x : K} {k : ℕ} {c : 𝓞 K → ℂ} {N q : (𝓞 K)⁰}
  {S S' : List (𝓞 K)⁰} {F G H : HyperbolicThreeSpace → Fin (k + 1) → ℂ}

variable (σ k N S) in
/-- The part of the old space of level `N` coming from a list `S` of primes: the span of the
functions `G ∣ (p, 0; 0, 1)` with `p` in `S` and `G` in `S_k(M)`, for `N = pM`. -/
noncomputable def bianchiOldPart : Submodule ℂ (HyperbolicThreeSpace → Fin (k + 1) → ℂ) :=
  Submodule.span ℂ {F | ∃ p ∈ S, ∃ M : (𝓞 K)⁰, N = p * M ∧
    ∃ G ∈ bianchiCuspForms σ (Ideal.span {(M : 𝓞 K)}).gamma0GL k, bianchiLevelRaise σ k p G = F}

lemma bianchiOldPart_mono (h : S ⊆ S') : bianchiOldPart σ k N S ≤ bianchiOldPart σ k N S' :=
  Submodule.span_mono fun _ ⟨p, hp, hG⟩ ↦ ⟨p, h hp, hG⟩

lemma exists_eq_mul_of_dvd (h : (q : 𝓞 K) ∣ N) : ∃ M : (𝓞 K)⁰, N = q * M := by
  rcases h with ⟨M, hM⟩
  exact ⟨⟨M, mem_nonZeroDivisors_of_ne_zero <| right_ne_zero_of_mul <|
    hM ▸ nonZeroDivisors.ne_zero N.2⟩, Subtype.ext hM⟩

lemma rowScale_eq_heckeLower (u : Kˣ) :
    GeneralLinearGroup.rowScale (0 : Fin 2) u = heckeLower u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeLower]

/-- **The old part lies in the oldforms.** -/
lemma bianchiOldPart_le_bianchiOldforms (hS : ∀ p ∈ S, Prime (p : 𝓞 K)) :
    bianchiOldPart σ k N S ≤ bianchiOldforms σ k (Ideal.span {(N : 𝓞 K)}) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨p, hp, M, rfl, G, hG, rfl⟩
  refine Submodule.subset_span ⟨Ideal.span {(M : 𝓞 K)}, ?_, p, nonZeroDivisors.ne_zero p.2, ?_, G,
    hG, ?_⟩
  · refine Ideal.span_singleton_lt_span_singleton.mpr
      ⟨nonZeroDivisors.ne_zero M.2, p, (hS p hp).not_isUnit, ?_⟩
    rw [Submonoid.coe_mul, mul_comm]
  · rw [Ideal.span_singleton_mul_span_singleton, Submonoid.coe_mul]
  · rw [bianchiLevelRaise, bianchiGLSlash, rowScale_eq_heckeLower]
    rfl

lemma extend_sub : extend (F - G) = extend F - extend G := by
  ext p : 1
  by_cases hp : 0 < p.2 <;> simp [extend, hp]

lemma extend_sum {ι : Type*} (s : Finset ι) (Φ : ι → HyperbolicThreeSpace → Fin (k + 1) → ℂ) :
    extend (∑ i ∈ s, Φ i) = ∑ i ∈ s, extend (Φ i) := by
  ext p : 1
  by_cases hp : 0 < p.2 <;> simp [extend]

lemma extend_bianchiGLSlash_heckeUpper_one (b : K) {p : ℂ × ℝ} (hp : 0 < p.2) :
    extend (bianchiGLSlash σ k (heckeUpper 1 b) F) p = extend F (p.1 + σ b, p.2) := by
  rw [extend_bianchiGLSlash_heckeUpper σ 1 b hp]
  simp [← one_fin_two, symPowMatrix_one]

open scoped Classical in
lemma ite_exists_mem_cons_dvd (α : 𝓞 K) (a : ℂ) : (if ∃ p ∈ q :: S, (p : 𝓞 K) ∣ α then 0 else a) =
    if ∃ p ∈ S, (p : 𝓞 K) ∣ α then 0 else if (q : 𝓞 K) ∣ α then 0 else a := by
  by_cases hq : (q : 𝓞 K) ∣ α <;> simp [hq]

variable [IsPrincipalIdealRing (𝓞 K)] (N) in
lemma exists_list_prime_factors : ∃ S : List (𝓞 K)⁰,
    (S.Pairwise fun p p' : (𝓞 K)⁰ ↦ ¬Associated (p : 𝓞 K) p') ∧
      (∀ p ∈ S, Prime (p : 𝓞 K) ∧ (p : 𝓞 K) ∣ N) ∧ ∀ α : 𝓞 K, (∀ p ∈ S, ¬(p : 𝓞 K) ∣ α) →
        IsCoprime α N := by
  suffices h : ∀ a : 𝓞 K, a ≠ 0 → ∃ S : List (𝓞 K)⁰,
      (S.Pairwise fun p p' : (𝓞 K)⁰ ↦ ¬Associated (p : 𝓞 K) p') ∧
        (∀ p ∈ S, Prime (p : 𝓞 K) ∧ (p : 𝓞 K) ∣ a) ∧
          ∀ α : 𝓞 K, (∀ p ∈ S, ¬(p : 𝓞 K) ∣ α) → IsCoprime α a from
    h N (nonZeroDivisors.ne_zero N.2)
  intro a
  induction a using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h ↦ absurd rfl h
  | h₂ a ha =>
    exact fun _ ↦ ⟨[], .nil, by simp, fun α _ ↦
      isCoprime_one_right.of_isCoprime_of_dvd_right ha.dvd⟩
  | h₃ a p ha hp ih =>
    rintro -
    rcases ih ha with ⟨S, hS₀, hS₁, hS₂⟩
    have hp₀ : p ∈ (𝓞 K)⁰ := mem_nonZeroDivisors_of_ne_zero hp.ne_zero
    have hcop (α : 𝓞 K) (hα : ¬p ∣ α) : IsCoprime α p :=
      (hp.coprime_iff_not_dvd.mpr hα).symm
    by_cases hmem : ∃ p' ∈ S, Associated p (p' : 𝓞 K)
    · rcases hmem with ⟨p', hp', hpp'⟩
      refine ⟨S, hS₀, fun r hr ↦ ⟨(hS₁ r hr).1, (hS₁ r hr).2.mul_left p⟩, fun α hα ↦ ?_⟩
      exact (hcop α fun h ↦ hα p' hp' (hpp'.symm.dvd.trans h)).mul_right (hS₂ α hα)
    · refine ⟨⟨p, hp₀⟩ :: S, List.pairwise_cons.mpr ⟨?_, hS₀⟩, ?_, fun α hα ↦ ?_⟩
      · exact fun p' hp' hass ↦ hmem ⟨p', hp', hass⟩
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨hp, dvd_mul_right _ _⟩
        · exact ⟨(hS₁ r hr).1, (hS₁ r hr).2.mul_left p⟩
      · exact (hcop α (hα ⟨p, hp₀⟩ List.mem_cons_self)).mul_right
          (hS₂ α fun r hr ↦ hα r (List.mem_cons_of_mem _ hr))

variable [NumberField K]

variable (σ k q F) in
/-- The function `F - E_q F`, with `E_q` of `bianchiPeriodAverage`: for `F` with a Fourier–Bessel
expansion, it keeps exactly the terms whose index is not divisible by `q`
(`HasBianchiWhittakerExpansion.primeFilter`). -/
noncomputable def bianchiPrimeFilter : HyperbolicThreeSpace → Fin (k + 1) → ℂ :=
  F - bianchiPeriodAverage σ k q F

variable (σ k) in
/-- The function `(1 - E_{q_r}) ⋯ (1 - E_{q_1}) F` for a list `q_1, …, q_r` of elements of `𝒪_K`:
for `F` with a Fourier–Bessel expansion, it keeps exactly the terms whose index is divisible by no
`q_i`. -/
noncomputable def bianchiCoprimeFilter :
    List (𝓞 K)⁰ → (HyperbolicThreeSpace → Fin (k + 1) → ℂ) → HyperbolicThreeSpace → Fin (k + 1) → ℂ
  | [], F => F
  | q :: S, F => bianchiCoprimeFilter S (bianchiPrimeFilter σ k q F)

lemma bianchiLevelTrace_add : bianchiLevelTrace σ k N q (G + H) = bianchiLevelTrace σ k N q G +
    bianchiLevelTrace σ k N q H := by
  simp only [bianchiLevelTrace, glSlash_add, Finset.sum_add_distrib, smul_add]

lemma bianchiLevelTrace_smul (a : ℂ) :
    bianchiLevelTrace σ k N q (a • H) = a • bianchiLevelTrace σ k N q H := by
  simp only [bianchiLevelTrace, glSlash_smul, ← Finset.smul_sum, smul_comm a]

lemma bianchiLevelTrace_zero : bianchiLevelTrace σ k N q 0 = 0 := by
  simpa using bianchiLevelTrace_smul (H := 0) 0

lemma bianchiLevelTrace_sub : bianchiLevelTrace σ k N q (G - H) = bianchiLevelTrace σ k N q G -
    bianchiLevelTrace σ k N q H := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ H, bianchiLevelTrace_add, bianchiLevelTrace_smul,
    neg_one_smul,
    sub_eq_add_neg]

lemma sum_out_eq_zero_of_ne_one {ψ : 𝓞 K → ℂ} (hadd : ∀ a b, ψ (a + b) = ψ a * ψ b)
    (hq : ∀ t, ψ ((q : 𝓞 K) * t) = 1) {z₀ : 𝓞 K} (hz₀ : ψ z₀ ≠ 1) :
    ∑ j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}, ψ (Quotient.out j) = 0 := by
  have h (j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) :
      ψ (Quotient.out (j + quotientMk _ z₀)) = ψ (Quotient.out j) * ψ z₀ := by
    have h₁ :
        Quotient.out (j + quotientMk _ z₀) - (Quotient.out j + z₀) ∈ Ideal.span {(q : 𝓞 K)} := by
      rw [← Quotient.mk_eq_mk_iff_sub_mem, map_add, quotientMk_out, quotientMk_out]
    rcases Ideal.mem_span_singleton.mp h₁ with ⟨t, ht⟩
    rw [← sub_add_cancel (Quotient.out (j + quotientMk _ z₀)) (Quotient.out j + z₀), ht,
      hadd,
      hq, one_mul, hadd]
  have h₂ : ∑ j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}, ψ (Quotient.out j) * ψ z₀ =
      ∑ j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}, ψ (Quotient.out j) := by
    simpa only [Equiv.coe_addRight, h] using
      Equiv.sum_comp (Equiv.addRight (quotientMk (Ideal.span {(q : 𝓞 K)}) z₀))
        fun j ↦ ψ (Quotient.out j)
  rw [← Finset.sum_mul] at h₂
  have h₃ : (∑ j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}, ψ (Quotient.out j)) * (ψ z₀ - 1) = 0 := by
    linear_combination h₂
  exact (mul_eq_zero.mp h₃).resolve_right (sub_ne_zero.mpr hz₀)

lemma cexp_two_pi_mul_eq_one (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) (hδ : δ ^ 2 = discr K)
    (z : 𝓞 K) : cexp (2 * π * I * (σ z / δ + conj (σ z / δ))) = 1 := by
  rcases exists_intCast_eq_of_sq_eq_discr σ hK hx hδ z with ⟨n, hn⟩
  rw [hn]
  exact Complex.exp_eq_one_iff.mpr ⟨n, by ring1⟩

open scoped Classical in
/-- **The sum of an additive character of `𝒪_K / (q)`**: for a quadratic field `K` embedded in `ℂ`
by `σ` with `σ(K) ⊄ ℝ` and `δ² = Δ`, the sum `∑_{j mod q} ψ(αj / (qδ))`, for
`ψ(z) = e^{2πi(z + z̄)}`, is `|𝒪_K / (q)|` if `q ∣ α`, and `0` otherwise, as `𝒪_K / √Δ` is the dual
lattice of `𝒪_K`. -/
lemma sum_cexp_eq (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) (hδ : δ ^ 2 = discr K) (α : 𝓞 K) :
    ∑ j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)},
      cexp (2 * π * I * (σ α * (σ (Quotient.out j : 𝓞 K) / σ (q : 𝓞 K)) / δ +
        conj (σ α * (σ (Quotient.out j : 𝓞 K) / σ (q : 𝓞 K)) / δ))) =
      if (q : 𝓞 K) ∣ α then (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ) else 0 := by
  have hδ₀ : δ ≠ 0 := ne_zero_of_sq_eq_discr K hδ
  have hq₀ : σ ((q : 𝓞 K) : K) ≠ 0 := (map_ne_zero σ).mpr <| RingOfIntegers.coe_ne_zero_iff.mpr <|
    nonZeroDivisors.ne_zero q.2
  split_ifs with hα
  · rcases hα with ⟨β, rfl⟩
    have h (j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : cexp (2 * π * I * (σ (((q : 𝓞 K) * β : 𝓞 K) : K) *
          (σ (Quotient.out j : 𝓞 K) / σ (q : 𝓞 K)) / δ + conj (σ (((q : 𝓞 K) * β : 𝓞 K) : K) *
            (σ (Quotient.out j : 𝓞 K) / σ (q : 𝓞 K)) / δ))) = 1 := by
      have e : σ (((q : 𝓞 K) * β : 𝓞 K) : K) * (σ (Quotient.out j : 𝓞 K) / σ (q : 𝓞 K)) / δ =
          σ ((β * Quotient.out j : 𝓞 K) : K) / δ := by
        simp only [map_mul]
        simp only [RingOfIntegers.coe_eq_algebraMap] at hq₀
        field_simp
      rw [e]
      exact cexp_two_pi_mul_eq_one hK hx hδ _
    simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · let ψ : 𝓞 K → ℂ := fun z ↦ cexp (2 * π * I * (σ α * (σ z / σ (q : 𝓞 K)) / δ +
      conj (σ α * (σ z / σ (q : 𝓞 K)) / δ)))
    have hadd (a b : 𝓞 K) : ψ (a + b) = ψ a * ψ b := by
      simp only [ψ, ← Complex.exp_add]
      congr 1
      simp only [add_div, mul_add, map_add]
      ring1
    have hmul (t : 𝓞 K) : ψ ((q : 𝓞 K) * t) = 1 := by
      have e :
          σ α * (σ (((q : 𝓞 K) * t : 𝓞 K) : K) / σ (q : 𝓞 K)) / δ = σ ((α * t : 𝓞 K) : K) / δ := by
        simp only [map_mul]
        simp only [RingOfIntegers.coe_eq_algebraMap] at hq₀
        field_simp
      simp only [ψ]
      rw [e]
      exact cexp_two_pi_mul_eq_one hK hx hδ _
    have hne : ∃ z₀ : 𝓞 K, ψ z₀ ≠ 1 := by
      by_contra hne
      push Not at hne
      have hdual (z : 𝓞 K) :
          ∃ n : ℤ, σ α / (δ * σ (q : 𝓞 K)) * σ z + conj (σ α / (δ * σ (q : 𝓞 K)) * σ z) = n := by
        rcases Complex.exp_eq_one_iff.mp (hne z) with ⟨n, hn⟩
        have h2π : (2 * π * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
        have e : σ α * (σ z / σ (q : 𝓞 K)) / δ = σ α / (δ * σ (q : 𝓞 K)) * σ z := by
          field_simp
        rw [e] at hn
        exact ⟨n, mul_left_cancel₀ h2π (by rw [hn]; ring1)⟩
      rcases exists_div_eq_of_dual σ hK hx hδ hdual with ⟨β, hβ⟩
      refine hα ⟨β, RingOfIntegers.coe_injective ?_⟩
      refine (RingHom.injective σ) ?_
      simp only [map_mul] at hβ hq₀ ⊢
      field_simp at hβ
      linear_combination -hβ
    rcases hne with ⟨z₀, hz₀⟩
    exact sum_out_eq_zero_of_ne_one hadd hmul hz₀

lemma bianchiWhittakerTerm_add (p : ℂ × ℝ) (α : 𝓞 K) (b : ℂ) :
    bianchiWhittakerTerm σ δ k c (p.1 + b, p.2) α =
      cexp (2 * π * I * (σ α * b / δ + conj (σ α * b / δ))) • bianchiWhittakerTerm σ δ k c p α := by
  simp only [bianchiWhittakerTerm, smul_smul]
  congr 1
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [mul_add, add_div, map_add]
  ring1

open scoped Classical in
/-- **The filter on Fourier–Bessel expansions**: if `F` has the expansion with coefficients `c(α)`,
then `F - E_q F` has the expansion with coefficients `c(α)` for `q ∤ α` and `0` for `q ∣ α`. -/
lemma HasBianchiWhittakerExpansion.primeFilter (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hδ : δ ^ 2 = discr K) (h : HasBianchiWhittakerExpansion σ δ k (extend F) c) :
    HasBianchiWhittakerExpansion σ δ k (extend (bianchiPrimeFilter σ k q F))
      fun α ↦ if (q : 𝓞 K) ∣ α then 0 else c α := by
  intro p hp
  have hn : (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ) ≠ 0 := card_residue_ne_zero q
  have he (j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) :
      σ (algebraMap (𝓞 K) K (Quotient.out j) / bianchiUnit q) =
        σ (Quotient.out j : 𝓞 K) / σ (q : 𝓞 K) := by
    rw [map_div₀, coe_bianchiUnit]
  have hj (j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦
      cexp (2 * π * I * (σ α.1 * (σ (Quotient.out j : 𝓞 K) / σ (q : 𝓞 K)) / δ +
        conj (σ α.1 * (σ (Quotient.out j : 𝓞 K) / σ (q : 𝓞 K)) / δ))) •
          bianchiWhittakerTerm σ δ k c p α)
      (extend (bianchiGLSlash σ k (heckeUpper 1 (algebraMap (𝓞 K) K (Quotient.out j) /
        bianchiUnit q)) F) p) := by
    rw [extend_bianchiGLSlash_heckeUpper_one _ hp, he]
    simpa only [bianchiWhittakerTerm_add] using
      h (p.1 + σ (Quotient.out j : 𝓞 K) / σ (q : 𝓞 K), p.2) hp
  have e : extend (bianchiPrimeFilter σ k q F) p = extend F p -
      (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ)⁻¹ • ∑ j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)},
        extend (bianchiGLSlash σ k (heckeUpper 1 (algebraMap (𝓞 K) K (Quotient.out j) /
          bianchiUnit q)) F) p := by
    rw [bianchiPrimeFilter, extend_sub, bianchiPeriodAverage, extend_smul, extend_sum]
    simp
  rw [e]
  refine ((h p hp).sub ((hasSum_sum (s := Finset.univ) fun j _ ↦ hj j).const_smul _)).congr_fun
    fun α ↦ ?_
  rw [← Finset.sum_smul, sum_cexp_eq hK hx hδ α.1]
  by_cases hα : (q : 𝓞 K) ∣ α.1
  · simp [bianchiWhittakerTerm, hα]
  · simp [bianchiWhittakerTerm, hα]

open scoped Classical in
lemma HasBianchiWhittakerExpansion.coprimeFilter (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hδ : δ ^ 2 = discr K) (h : HasBianchiWhittakerExpansion σ δ k (extend F) c) :
    HasBianchiWhittakerExpansion σ δ k (extend (bianchiCoprimeFilter σ k S F))
      fun α ↦ if ∃ p ∈ S, (p : 𝓞 K) ∣ α then 0 else c α := by
  induction S generalizing F c with
  | nil => simpa [bianchiCoprimeFilter] using h
  | cons q S ih =>
    simpa only [ite_exists_mem_cons_dvd, bianchiCoprimeFilter] using
      ih (h.primeFilter (q := q) hK hx hδ)

variable [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)]

lemma bianchiLevelTrace_mem_bianchiOldPart (hK : finrank ℚ K = 2) (hk : Even k)
    (hq : Prime (q : 𝓞 K)) (hqS : ∀ p ∈ S, ¬Associated (q : 𝓞 K) p)
    (hS : ∀ p ∈ S, Prime (p : 𝓞 K) ∧ (p : 𝓞 K) ∣ N) (hqN : (q : 𝓞 K) ∣ N)
    (hH : H ∈ bianchiOldPart σ k (N * q) S) :
    bianchiLevelTrace σ k N q H ∈ bianchiOldPart σ k N S := by
  induction hH using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨p, hp, M, hM, G, hG, rfl⟩
    rcases hS p hp with ⟨hpp, hpN⟩
    rcases exists_eq_mul_of_dvd hpN with ⟨N'', rfl⟩
    have hM' : M = N'' * q := Subtype.ext <| mul_left_cancel₀ hpp.ne_zero <| by
      rw [← Submonoid.coe_mul, ← hM, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul,
        mul_assoc]
    subst hM'
    have h₁ : (q : 𝓞 K) ∣ (p : 𝓞 K) * N'' := hqN
    have hqN'' : (q : 𝓞 K) ∣ N'' := (hq.dvd_mul.mp h₁).resolve_left fun h ↦
      hqS p hp (hq.associated_of_dvd hpp h)
    rw [bianchiLevelTrace_bianchiLevelRaise hk]
    exact Submodule.subset_span ⟨p, hp, N'', rfl, _,
      bianchiLevelTrace_mem_bianchiCuspForms hK hk hq hqN'' hG, rfl⟩
  | zero =>
    rw [bianchiLevelTrace_zero]
    exact zero_mem _
  | add y z _ _ hy hz =>
    rw [bianchiLevelTrace_add]
    exact add_mem hy hz
  | smul a y _ hy =>
    rw [bianchiLevelTrace_smul]
    exact Submodule.smul_mem _ a hy

/-- **The Main Lemma of Atkin and Lehner, for a list of primes**: for a list `S` of pairwise
non-associated primes dividing `N`, in even weight, and `F` in `S_k(N)`, if
`(1 - E_{q_r}) ⋯ (1 - E_{q_1}) F = 0`, then `F` lies in the span of the functions
`G ∣ (p, 0; 0, 1)` with `p` in `S` and `G` in `S_k(N / p)`. The induction on `S` goes through the
level `Nq`: `H = F - E_q F` lies in `S_k(Nq)`, so `H` is a sum of `G_p ∣ (p, 0; 0, 1)` with `G_p` of
level `Nq / p`, and the trace from `Γ₀(Nq)` to `Γ₀(N)` gives `Tr H = c (F - Z ∣ (q, 0; 0, 1))`
on one side and a sum of `(Tr G_p) ∣ (p, 0; 0, 1)` on the other, with `Tr G_p` of level `N / p`. -/
lemma mem_bianchiOldPart_of_bianchiCoprimeFilter_eq_zero (hK : finrank ℚ K = 2) (hk : Even k)
    (hS₀ : S.Pairwise fun p p' : (𝓞 K)⁰ ↦ ¬Associated (p : 𝓞 K) p')
    (hS : ∀ p ∈ S, Prime (p : 𝓞 K) ∧ (p : 𝓞 K) ∣ N)
    (hF : F ∈ bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k)
    (h : bianchiCoprimeFilter σ k S F = 0) : F ∈ bianchiOldPart σ k N S := by
  induction S generalizing N F with
  | nil =>
    have h₀ : F = 0 := h
    rw [h₀]
    exact zero_mem _
  | cons q S ih =>
    rcases List.pairwise_cons.mp hS₀ with ⟨hqS, hS₁⟩
    rcases hS q List.mem_cons_self with ⟨hqp, hqN⟩
    have hS₂ : ∀ p ∈ S, Prime (p : 𝓞 K) ∧ (p : 𝓞 K) ∣ N :=
      fun p hp ↦ hS p (List.mem_cons_of_mem q hp)
    have hH : bianchiPrimeFilter σ k q F ∈
        bianchiCuspForms σ (Ideal.span {((N * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL k :=
      sub_mem (bianchiCuspForms_mono hK (dvd_mul_right _ _) hF)
        (bianchiPeriodAverage_mem_bianchiCuspForms hK hk hqp hqN hF)
    have hold : bianchiPrimeFilter σ k q F ∈ bianchiOldPart σ k (N * q) S :=
      ih hS₁ (fun p hp ↦ (hS₂ p hp).imp_right (·.mul_right q)) hH h
    have htr : bianchiLevelTrace σ k N q (bianchiPrimeFilter σ k q F) ∈ bianchiOldPart σ k N S :=
      bianchiLevelTrace_mem_bianchiOldPart hK hk hqp hqS hS₂ hqN hold
    rcases exists_eq_mul_of_dvd hqN with ⟨M, rfl⟩
    have hc : bianchiTraceConstant M q ≠ 0 := bianchiTraceConstant_ne_zero hqp
    have hinv : IsBianchiSlashInvariant σ (Ideal.span {((q * M : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL k F :=
      ((mem_bianchiCuspForms_iff hK (ne_bot_span _)).mp hF).2
    have hsub : bianchiLevelTrace σ k (q * M) q (bianchiPrimeFilter σ k q F) =
        bianchiTraceConstant M q •
          (F - bianchiLevelRaise σ k q (bianchiTraceRemainder σ k M q F)) := by
      rw [bianchiPrimeFilter, bianchiLevelTrace_sub, bianchiLevelTrace_eq_self hinv,
        sub_bianchiLevelTrace_bianchiPeriodAverage hK hk hqp hF]
    have hFeq : F = (bianchiTraceConstant M q)⁻¹ •
        bianchiLevelTrace σ k (q * M) q (bianchiPrimeFilter σ k q F) +
          bianchiLevelRaise σ k q (bianchiTraceRemainder σ k M q F) := by
      rw [hsub, smul_smul, inv_mul_cancel₀ hc, one_smul, sub_add_cancel]
    rw [hFeq]
    refine add_mem (Submodule.smul_mem _ _ (bianchiOldPart_mono (List.subset_cons_self q S) htr)) ?_
    exact Submodule.subset_span ⟨q, List.mem_cons_self, M, rfl, _,
      bianchiTraceRemainder_mem_bianchiCuspForms hK hk hqp hF, rfl⟩

/-- **The Main Lemma of Atkin and Lehner for Bianchi forms** (the analogue of Atkin and Lehner,
*Hecke operators on `Γ₀(m)`*, Theorem 1; Miyake, *Modular forms*, 4.6.8): for `K` imaginary
quadratic of class number `1` and `F` in `S_k(𝔑)`, `𝔑 ≠ 0`, if the Fourier–Bessel coefficients
`c(α)` of `F` vanish at every `α` prime to `𝔑`, then `F` is old. The weight is any `k`, forms of
odd weight vanishing. -/
lemma mem_bianchiOldforms_of_coeff_eq_zero (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hδ : δ ^ 2 = discr K) {𝔑 : Ideal (𝓞 K)} (h𝔑 : 𝔑 ≠ ⊥) (hF : F ∈ bianchiCuspForms σ 𝔑.gamma0GL k)
    (hc : HasBianchiWhittakerExpansion σ δ k (extend F) c)
    (h : ∀ α, α ≠ 0 → Ideal.span {α} ⊔ 𝔑 = ⊤ → c α = 0) : F ∈ bianchiOldforms σ k 𝔑 := by
  rcases Nat.even_or_odd k with hk | hk
  · rcases (IsPrincipalIdealRing.principal 𝔑).principal with ⟨N₀, rfl⟩
    have hN₀ : N₀ ∈ (𝓞 K)⁰ := mem_nonZeroDivisors_of_ne_zero fun h₀ ↦ h𝔑 (by simp [h₀])
    rcases exists_list_prime_factors (⟨N₀, hN₀⟩ : (𝓞 K)⁰) with ⟨S, hS₀, hS₁, hS₂⟩
    refine bianchiOldPart_le_bianchiOldforms (N := ⟨N₀, hN₀⟩) (fun p hp ↦ (hS₁ p hp).1) <|
      mem_bianchiOldPart_of_bianchiCoprimeFilter_eq_zero hK hk hS₀ hS₁ hF ?_
    have hzero : extend (bianchiCoprimeFilter σ k S F) = 0 := by
      ext p : 1
      by_cases hp : 0 < p.2
      · refine (hc.coprimeFilter (S := S) hK hx hδ p hp).unique ?_
        convert hasSum_zero with α
        by_cases hα : ∃ q ∈ S, (q : 𝓞 K) ∣ α.1
        · simp [bianchiWhittakerTerm, hα]
        · have hcop : IsCoprime α.1 N₀ := hS₂ α.1 fun q hq hqα ↦ hα ⟨q, hq, hqα⟩
          have htop : Ideal.span {α.1} ⊔ Ideal.span {N₀} = ⊤ :=
            Ideal.isCoprime_iff_sup_eq.mp ((Ideal.isCoprime_span_singleton_iff _ _).mpr hcop)
          simp [bianchiWhittakerTerm, h α.1 α.2 htop]
      · simp [extend, hp]
    ext z j
    have h₂ : extend (bianchiCoprimeFilter σ k S F) z.coords = 0 := by
      rw [hzero]
      rfl
    rw [extend_coords] at h₂
    exact congrFun h₂ j
  · rw [hF.1.invariant.eq_zero_of_odd hk]
    exact zero_mem _

end HyperbolicThreeSpace
