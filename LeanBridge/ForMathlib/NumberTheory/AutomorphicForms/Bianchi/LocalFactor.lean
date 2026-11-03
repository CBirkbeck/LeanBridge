import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.AnalyticRankOfWeight
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.CoeffMultiplicative
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Basic

/-!
# The local factors over `ℚ` of the L-function of a Bianchi newform

Let `K` be an imaginary quadratic field of class number `1`, and `F` a Bianchi newform of weight
`k ≥ 1` and level `𝔑`, with coefficients `c(𝔞)` at the nonzero ideals of `𝒪_K`. Its L-function over
`ℚ`, of degree `4`, has the Dirichlet coefficients `aₙ = n^{-k/4} ∑_{N(𝔞) = n} c(𝔞)`
(`BianchiNewformOfWeight.lCoeff`). They are multiplicative
(`HyperbolicThreeSpace.BianchiNewformOfWeight.lCoeff_mul`), as an ideal of norm `mn`, for coprime
`m` and `n`, is uniquely the product of an ideal of norm `m` and of an ideal of norm `n`. A rational
prime `p` is inert, ramified or split in `𝒪_K`, which determines the ideals of norm a power of `p`,
and so, by the recursion of the coefficients at the powers of a prime, their local factor: a
polynomial `F_p` of degree at most `4`, of degree `4` exactly for `p ∤ N(𝔑) Δ²`, with
`F_p(T) ∑_j a_{p^j} T^j = 1` (`HyperbolicThreeSpace.BianchiNewformOfWeight.exists_eulerFactor`).

## Main definitions

* `HyperbolicThreeSpace.eulerPoly`: the polynomial `1 - A X + E X²`.

## Main results

* `HyperbolicThreeSpace.BianchiNewformOfWeight.lCoeff_mul`: the Dirichlet coefficients are
  multiplicative.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.exists_eulerFactor`: the local factors.
-/

open Module NumberField Polynomial TauCeti

open Submodule (IsPrincipal)

open scoped nonZeroDivisors

namespace HyperbolicThreeSpace

/-- The polynomial `1 - A X + E X²`. -/
noncomputable def eulerPoly (A E : ℂ) : ℂ[X] :=
  1 - C A * X + C E * X ^ 2

variable {A E : ℂ}

lemma eulerPoly_mul_mk {h : ℕ → ℂ} (h₀ : h 0 = 1) (h₁ : h 1 = A)
    (h₂ : ∀ j, h (j + 2) = A * h (j + 1) - E * h j) :
    (eulerPoly A E : PowerSeries ℂ) * PowerSeries.mk h = 1 := by
  ext n
  rcases n with _ | _ | n
  · simp [eulerPoly, h₀]
  · simp [eulerPoly, sub_mul, add_mul, mul_assoc, PowerSeries.coeff_X_pow_mul', h₀, h₁]
  · simp [eulerPoly, sub_mul, add_mul, mul_assoc, PowerSeries.coeff_X_pow_mul', h₂]

lemma eulerPoly_comp_mul_mk {x : ℕ → ℂ} (h₀ : x 0 = 1) (h₁ : x 1 = 0) (h₂ : x 2 = A) (h₃ : x 3 = 0)
    (h₄ : ∀ n, x (n + 4) = A * x (n + 2) - E * x n) :
    (((eulerPoly A E).comp (X ^ 2) : ℂ[X]) : PowerSeries ℂ) * PowerSeries.mk x = 1 := by
  have e : (eulerPoly A E).comp (X ^ 2) = 1 - C A * X ^ 2 + C E * X ^ 4 := by
    simp only [eulerPoly, add_comp, sub_comp, one_comp, mul_comp, C_comp, X_comp, pow_comp]
    ring1
  rw [e]
  ext n
  rcases n with _ | _ | _ | _ | n
  · simp [h₀]
  · simp [sub_mul, add_mul, mul_assoc, PowerSeries.coeff_X_pow_mul', h₁]
  · simp [sub_mul, add_mul, mul_assoc, PowerSeries.coeff_X_pow_mul', h₀, h₂]
  · simp [sub_mul, add_mul, mul_assoc, PowerSeries.coeff_X_pow_mul', h₁, h₃]
  · simp [sub_mul, add_mul, mul_assoc, PowerSeries.coeff_X_pow_mul', h₄]

lemma eulerPoly_ne_zero : eulerPoly A E ≠ 0 := by
  intro h
  have h₁ : (eulerPoly A E).coeff 0 = (0 : ℂ[X]).coeff 0 := congrArg (fun q ↦ coeff q 0) h
  simp [eulerPoly] at h₁

lemma natDegree_eulerPoly_of_ne_zero (hE : E ≠ 0) : (eulerPoly A E).natDegree = 2 := by
  have e : eulerPoly A E = C E * X ^ 2 + C (-A) * X + C 1 := by
    simp only [eulerPoly, C_neg, C_1]
    ring1
  rw [e]
  exact natDegree_quadratic hE

lemma natDegree_eulerPoly_zero : (eulerPoly A 0).natDegree ≤ 1 := by
  have e : eulerPoly A 0 = C (-A) * X + C 1 := by
    simp only [eulerPoly, C_neg, C_1, C_0]
    ring1
  rw [e]
  exact natDegree_linear_le

lemma natDegree_eulerPoly_eq_two_iff : (eulerPoly A E).natDegree = 2 ↔ E ≠ 0 := by
  refine ⟨fun h hE ↦ ?_, natDegree_eulerPoly_of_ne_zero⟩
  have h₁ : (eulerPoly A 0).natDegree ≤ 1 := natDegree_eulerPoly_zero
  rw [hE] at h
  omega

lemma natDegree_eulerPoly_le_two : (eulerPoly A E).natDegree ≤ 2 := by
  by_cases hE : E = 0
  · rw [hE]
    exact natDegree_eulerPoly_zero.trans one_le_two
  · exact (natDegree_eulerPoly_of_ne_zero hE).le

variable {K : Type*} [Field K] [NumberField K] {𝔞 𝔮 𝔮' : Ideal (𝓞 K)} {m n p j : ℕ}

variable (p) in
lemma absNorm_span_natCast_eq_sq (hK : finrank ℚ K = 2) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK]

lemma span_natCast_ne_bot (hp : p.Prime) : Ideal.span {(p : 𝓞 K)} ≠ ⊥ :=
  Ideal.span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)

lemma ne_bot_of_absNorm_eq (hp : p.Prime) (h : Ideal.absNorm 𝔞 = p) : 𝔞 ≠ ⊥ :=
  fun h₁ ↦ hp.ne_zero <| by rw [← h, h₁, Ideal.absNorm_bot]

lemma natCast_mem_of_absNorm_eq_pow (h : Ideal.absNorm 𝔞 = p ^ j) {𝔯 : Ideal (𝓞 K)} (h𝔯 : 𝔯.IsPrime)
    (h𝔞𝔯 : 𝔞 ≤ 𝔯) : (p : 𝓞 K) ∈ 𝔯 := by
  have h₁ : ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 K) ∈ 𝔯 := h𝔞𝔯 (Ideal.absNorm_mem 𝔞)
  rw [h, Nat.cast_pow] at h₁
  exact h𝔯.mem_of_pow_mem _ h₁

lemma exists_factorization (hK : finrank ℚ K = 2) (hp : p.Prime) :
    (Ideal.span {(p : 𝓞 K)}).IsPrime ∨ ∃ 𝔮 𝔮' : Ideal (𝓞 K), 𝔮.IsPrime ∧ 𝔮'.IsPrime ∧
      Ideal.absNorm 𝔮 = p ∧ Ideal.absNorm 𝔮' = p ∧ Ideal.span {(p : 𝓞 K)} = 𝔮 * 𝔮' := by
  have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := absNorm_span_natCast_eq_sq p hK
  have htop : Ideal.span {(p : 𝓞 K)} ≠ ⊤ := fun h ↦ by
    rw [h, Ideal.absNorm_top] at hN
    exact (Nat.one_lt_pow two_ne_zero hp.one_lt).ne hN
  rcases Ideal.exists_le_maximal _ htop with ⟨𝔮, h𝔮, hle⟩
  rcases Ideal.dvd_iff_le.mpr hle with ⟨𝔮', he⟩
  have hprod : Ideal.absNorm 𝔮 * Ideal.absNorm 𝔮' = p ^ 2 := by
    rw [← map_mul, ← he, hN]
  rcases (Nat.dvd_prime_pow hp).mp (Dvd.intro _ hprod) with ⟨i, hi, hNq⟩
  have hi₂ : i = 0 ∨ i = 1 ∨ i = 2 := by
    omega
  rcases hi₂ with rfl | rfl | rfl
  · rw [pow_zero] at hNq
    exact absurd (Ideal.absNorm_eq_one_iff.mp hNq) h𝔮.ne_top
  · rw [pow_one] at hNq
    have hNq' : Ideal.absNorm 𝔮' = p := by
      rw [hNq, sq] at hprod
      exact Nat.eq_of_mul_eq_mul_left hp.pos hprod
    exact Or.inr ⟨𝔮, 𝔮', h𝔮.isPrime, Ideal.isPrime_of_irreducible_absNorm (hNq' ▸ hp), hNq, hNq',
      he⟩
  · have hNq' : Ideal.absNorm 𝔮' = 1 := by
      rw [hNq] at hprod
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (hprod.trans (mul_one _).symm)
    rw [Ideal.absNorm_eq_one_iff.mp hNq', Ideal.mul_top] at he
    exact Or.inl (he ▸ h𝔮.isPrime)

lemma exists_eq_pow_mul_pow (hp : p.Prime) (h𝔮 : 𝔮.IsPrime) (h𝔮' : 𝔮'.IsPrime)
    (hN : Ideal.absNorm 𝔮 = p) (hN' : Ideal.absNorm 𝔮' = p) (hP : Ideal.span {(p : 𝓞 K)} = 𝔮 * 𝔮')
    (h : Ideal.absNorm 𝔞 = p ^ j) : ∃ a b : ℕ, a + b = j ∧ 𝔞 = 𝔮 ^ a * 𝔮' ^ b := by
  have h₀ {𝔯 : Ideal (𝓞 K)} (h𝔯 : Ideal.absNorm 𝔯 = p) : 𝔯 ≠ ⊥ := ne_bot_of_absNorm_eq hp h𝔯
  induction j generalizing 𝔞 with
  | zero =>
    rw [pow_zero] at h
    exact ⟨0, 0, rfl, by rw [Ideal.absNorm_eq_one_iff.mp h, pow_zero, pow_zero, Ideal.one_eq_top,
      Ideal.top_mul]⟩
  | succ j ih =>
    have htop : 𝔞 ≠ ⊤ := fun h₁ ↦ by
      rw [h₁, Ideal.absNorm_top] at h
      exact (Nat.one_lt_pow j.succ_ne_zero hp.one_lt).ne h
    rcases Ideal.exists_le_maximal 𝔞 htop with ⟨𝔯, h𝔯, h𝔞𝔯⟩
    have hmem : (p : 𝓞 K) ∈ 𝔯 := natCast_mem_of_absNorm_eq_pow h h𝔯.isPrime h𝔞𝔯
    have hle : 𝔮 * 𝔮' ≤ 𝔯 := hP ▸ (Ideal.span_singleton_le_iff_mem _).mpr hmem
    rcases h𝔯.isPrime.mul_le.mp hle with h₂ | h₂
    · have he : 𝔮 = 𝔯 := (h𝔮.isMaximal (h₀ hN)).eq_of_le h𝔯.ne_top h₂
      subst he
      rcases Ideal.dvd_iff_le.mpr h𝔞𝔯 with ⟨𝔞', rfl⟩
      have h₃ : Ideal.absNorm 𝔞' = p ^ j := by
        rw [map_mul, hN, pow_succ'] at h
        exact Nat.eq_of_mul_eq_mul_left hp.pos h
      rcases ih h₃ with ⟨a, b, hab, rfl⟩
      exact ⟨a + 1, b, by omega, by ring1⟩
    · have he : 𝔮' = 𝔯 := (h𝔮'.isMaximal (h₀ hN')).eq_of_le h𝔯.ne_top h₂
      subst he
      rcases Ideal.dvd_iff_le.mpr h𝔞𝔯 with ⟨𝔞', rfl⟩
      have h₃ : Ideal.absNorm 𝔞' = p ^ j := by
        rw [map_mul, hN', pow_succ'] at h
        exact Nat.eq_of_mul_eq_mul_left hp.pos h
      rcases ih h₃ with ⟨a, b, hab, rfl⟩
      exact ⟨a, b + 1, by omega, by ring1⟩

lemma exists_eq_pow_of_isPrime (hK : finrank ℚ K = 2) (hp : p.Prime)
    (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) (h : Ideal.absNorm 𝔞 = p ^ j) :
    ∃ i : ℕ, 2 * i = j ∧ 𝔞 = Ideal.span {(p : 𝓞 K)} ^ i := by
  have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := absNorm_span_natCast_eq_sq p hK
  have hP₀ : Ideal.span {(p : 𝓞 K)} ≠ ⊥ := span_natCast_ne_bot hp
  induction j using Nat.strong_induction_on generalizing 𝔞 with
  | _ j ih =>
    by_cases hj : j = 0
    · subst hj
      rw [pow_zero] at h
      exact ⟨0, rfl, by rw [Ideal.absNorm_eq_one_iff.mp h, pow_zero, Ideal.one_eq_top]⟩
    have htop : 𝔞 ≠ ⊤ := fun h₁ ↦ by
      rw [h₁, Ideal.absNorm_top] at h
      exact (Nat.one_lt_pow hj hp.one_lt).ne h
    rcases Ideal.exists_le_maximal 𝔞 htop with ⟨𝔯, h𝔯, h𝔞𝔯⟩
    have hmem : (p : 𝓞 K) ∈ 𝔯 := natCast_mem_of_absNorm_eq_pow h h𝔯.isPrime h𝔞𝔯
    have he : Ideal.span {(p : 𝓞 K)} = 𝔯 := (hP.isMaximal hP₀).eq_of_le h𝔯.ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
    subst he
    rcases Ideal.dvd_iff_le.mpr h𝔞𝔯 with ⟨𝔞', rfl⟩
    rw [map_mul, hN] at h
    have hj₂ : 2 ≤ j := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (Dvd.intro _ h)
    have h₃ : Ideal.absNorm 𝔞' = p ^ (j - 2) := by
      have e : p ^ j = p ^ 2 * p ^ (j - 2) := by
        rw [← pow_add]
        congr 1
        omega
      rw [e] at h
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h
    rcases ih (j - 2) (by omega) h₃ with ⟨i, hi, rfl⟩
    exact ⟨i + 1, by omega, by ring1⟩

lemma isUnramifiedAt_iff (hp : p.Prime) {𝔯 : Ideal (𝓞 K)} (h𝔯 : 𝔯.IsPrime) (hmem : (p : 𝓞 K) ∈ 𝔯) :
    Algebra.IsUnramifiedAt ℤ 𝔯 ↔ ¬Ideal.span {(p : 𝓞 K)} ≤ 𝔯 ^ 2 := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hl : 𝔯.LiesOver (Ideal.span {(p : ℤ)}) :=
    (Ideal.liesOver_span_iff h𝔯.ne_top hp').mpr (by simpa using hmem)
  have hmap : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) = Ideal.span {(p : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have hle : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≤ 𝔯 := by
    rw [hmap]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hmem
  have hbot : Ideal.span {(p : ℤ)} ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hp'.ne_zero
  have h₁ : (Ideal.span {(p : ℤ)}).ramificationIdx' 𝔯 = 𝔯.ramificationIdx ℤ :=
    Ideal.ramificationIdx'_eq_ramificationIdx _ 𝔯 hbot
  have hfin : Ring.HasFiniteQuotients ℤ := .of_module_finite ℤ _
  rw [← Ideal.ramificationIdx_eq_one_iff, ← h₁, ← not_ne_iff, Ideal.ramificationIdx'_ne_one_iff hle,
    hmap]

lemma not_dvd_discr_iff_forall (hp : p.Prime) : ¬(p : ℤ) ∣ discr K ↔ ∀ 𝔯 : Ideal (𝓞 K), 𝔯.IsPrime →
    (p : 𝓞 K) ∈ 𝔯 → ¬Ideal.span {(p : 𝓞 K)} ≤ 𝔯 ^ 2 := by
  rw [NumberField.not_dvd_discr_iff_forall_mem K (𝓞 K) (Nat.prime_iff_prime_int.mp hp)]
  refine forall_congr' fun 𝔯 ↦ forall_congr' fun h𝔯 ↦ ?_
  rw [Int.cast_natCast]
  exact forall_congr' fun hmem ↦ isUnramifiedAt_iff hp h𝔯 hmem

lemma dvd_absNorm_iff {𝔑 : Ideal (𝓞 K)} (hK : finrank ℚ K = 2) (hp : p.Prime) :
    p ∣ Ideal.absNorm 𝔑 ↔ ∃ 𝔯 : Ideal (𝓞 K), 𝔯.IsMaximal ∧ (p : 𝓞 K) ∈ 𝔯 ∧ 𝔑 ≤ 𝔯 := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  refine ⟨fun h ↦ ?_, fun ⟨𝔯, h𝔯, hmem, hle⟩ ↦ ?_⟩
  · rcases Ideal.exists_isMaximal_dvd_of_dvd_absNorm hp' 𝔑 (Int.natCast_dvd_natCast.mpr h) with
      ⟨𝔯, h𝔯, hu, hd⟩
    refine ⟨𝔯, h𝔯, ?_, Ideal.le_of_dvd hd⟩
    have h₁ : (p : ℤ) ∈ 𝔯.under ℤ := hu ▸ Ideal.mem_span_singleton_self _
    simpa using Ideal.mem_comap.mp h₁
  · have h₁ : Ideal.absNorm 𝔯 ∣ p ^ 2 := by
      rw [← absNorm_span_natCast_eq_sq p hK]
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
    rcases (Nat.dvd_prime_pow hp).mp h₁ with ⟨i, -, hi⟩
    have hi₀ : i ≠ 0 := fun h₀ ↦ h𝔯.ne_top (Ideal.absNorm_eq_one_iff.mp (by rw [hi, h₀, pow_zero]))
    exact (dvd_pow_self p hi₀).trans (hi ▸ Ideal.absNorm_dvd_absNorm_of_le hle)

namespace BianchiNewformOfWeight

variable {k : ℕ} {𝔑 : Ideal (𝓞 K)}

lemma natCast_pow_mul_sq (hk' : Even k) (hp : p ≠ 0) :
    (p : ℂ) ^ (k / 2) * (((p : ℝ) ^ ((k : ℝ) / 4) : ℝ) : ℂ)⁻¹ ^ 2 = 1 := by
  have hp₀ : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp)
  have e : ((p : ℝ) ^ ((k : ℝ) / 4)) ^ 2 = (p : ℝ) ^ (k / 2) := by
    rcases hk' with ⟨m, rfl⟩
    have e₁ : (m + m) / 2 = m := by
      omega
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hp₀.le, e₁, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring1
  have e₂ : (((p : ℝ) ^ ((k : ℝ) / 4) : ℝ) : ℂ) ^ 2 = (p : ℂ) ^ (k / 2) := by
    exact_mod_cast e
  have hne : (p : ℂ) ^ (k / 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp)
  rw [inv_pow, e₂, mul_inv_cancel₀ hne]

variable [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)] {σ : K →+* ℂ} [NeZero 𝔑]
  (N : BianchiNewformOfWeight σ k 𝔑)

variable (n) in
/-- The sum `∑_{N(𝔞) = n} c(𝔞)` of the coefficients of a Bianchi newform over the ideals of norm
`n`: the coefficient of `n^{-s}` in its L-function, in the arithmetic normalisation. -/
noncomputable def normCoeff : ℂ :=
  ∑ᶠ 𝔫 ∈ {𝔫 : Ideal (𝓞 K) | Ideal.absNorm 𝔫 = n}, N.idealCoeff 𝔫

variable (n) in
lemma lCoeff_eq : N.lCoeff n = N.normCoeff n / ((n : ℝ) ^ ((k : ℝ) / 4) : ℝ) := by
  simp only [div_eq_mul_inv]
  exact (finsum_mem_mul _ _).symm

lemma normCoeff_one (hK : finrank ℚ K = 2) : N.normCoeff 1 = 1 := by
  have e : {𝔫 : Ideal (𝓞 K) | Ideal.absNorm 𝔫 = 1} = {⊤} :=
    Set.ext fun 𝔫 ↦ Ideal.absNorm_eq_one_iff
  rw [normCoeff, e, finsum_mem_singleton, N.idealCoeff_top hK]

lemma lCoeff_one (hK : finrank ℚ K = 2) : N.lCoeff 1 = 1 := by
  rw [lCoeff_eq, N.normCoeff_one hK]
  simp

lemma isMultiplicative_restrict_idealCoeff (hK : finrank ℚ K = 2) (hk : k ≠ 0) :
    (IdealArithmeticFunction.restrict N.idealCoeff).IsMultiplicative where
  map_one := by
    rw [IdealArithmeticFunction.restrict_apply, Submonoid.coe_one, Ideal.one_eq_top,
      N.idealCoeff_top hK]
  map_mul_of_isRelPrime {I J} h := N.idealCoeff_mul hK hk (nonZeroDivisors.coe_ne_zero I)
    (nonZeroDivisors.coe_ne_zero J) <| Ideal.isCoprime_iff_sup_eq.mpr <| by_contra fun hne ↦ by
      rcases Ideal.exists_le_maximal _ hne with ⟨𝔪, h𝔪, hle⟩
      exact h𝔪.ne_top (Ideal.isUnit_iff.mp (h (Ideal.dvd_iff_le.mpr (le_sup_left.trans hle))
        (Ideal.dvd_iff_le.mpr (le_sup_right.trans hle))))

lemma normCoeff_eq (hn : n ≠ 0) :
    N.normCoeff n = TauCeti.normCoeff K (IdealArithmeticFunction.restrict N.idealCoeff) n := by
  have e : {𝔫 : Ideal (𝓞 K) | Ideal.absNorm 𝔫 = n} =
      (↑) '' {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n} := by
    ext 𝔫
    refine ⟨fun h ↦ ⟨⟨𝔫, mem_nonZeroDivisors_of_ne_zero fun h₀ ↦ hn ?_⟩, h, rfl⟩, ?_⟩
    · rw [← Set.mem_ofPred_eq.mp h, h₀, map_zero]
    · rintro ⟨I, hI, rfl⟩
      exact hI
  rw [normCoeff, e, finsum_mem_image Subtype.val_injective.injOn, TauCeti.normCoeff_apply]
  rfl

lemma normCoeff_mul (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hc : m.Coprime n) : N.normCoeff (m * n) = N.normCoeff m * N.normCoeff n := by
  have hf : (IdealArithmeticFunction.restrict N.idealCoeff).IsMultiplicative :=
    N.isMultiplicative_restrict_idealCoeff hK hk
  have hM :
      (TauCeti.normCoeff K (IdealArithmeticFunction.restrict N.idealCoeff)).IsMultiplicative := by
    rw [IdealArithmeticFunction.normCoeff_eq_eulerProduct hf]
    exact IdealArithmeticFunction.isMultiplicative_eulerProduct hf.map_one
  rw [N.normCoeff_eq (mul_ne_zero hm hn), N.normCoeff_eq hm, N.normCoeff_eq hn,
    hM.map_mul_of_coprime hc]

/-- **The Dirichlet coefficients of the L-function of a Bianchi newform are multiplicative**
(LMFDB `mf.bianchi.anr`): `a_{mn} = a_m a_n` for coprime `m` and `n`, for `K` imaginary quadratic
of class number `1` and `k ≥ 1`. -/
lemma lCoeff_mul (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hc : m.Coprime n) :
    N.lCoeff (m * n) = N.lCoeff m * N.lCoeff n := by
  rcases eq_or_ne m 0 with rfl | hm
  · have hn : n = 1 := by
      simpa using hc
    rw [hn, mul_one, N.lCoeff_one hK, mul_one]
  rcases eq_or_ne n 0 with rfl | hn
  · have hm' : m = 1 := by
      simpa using hc
    rw [hm', one_mul, N.lCoeff_one hK, one_mul]
  rw [lCoeff_eq, lCoeff_eq, lCoeff_eq, N.normCoeff_mul hK hk hm hn hc, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), Complex.ofReal_mul, mul_div_mul_comm]

variable (p j) in
lemma lCoeff_pow :
    N.lCoeff (p ^ j) = N.normCoeff (p ^ j) * (((p : ℝ) ^ ((k : ℝ) / 4) : ℝ) : ℂ)⁻¹ ^ j := by
  have e : (((p ^ j : ℕ) : ℝ) ^ ((k : ℝ) / 4)) = ((p : ℝ) ^ ((k : ℝ) / 4)) ^ j := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) j, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm,
      Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]
  rw [lCoeff_eq, e, Complex.ofReal_pow, inv_pow, div_eq_mul_inv]

lemma eulerPoly_mul_mk_idealCoeff (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (u : ℂ) :
    (eulerPoly (N.eigenvalue 𝔭 * u) (heckeWeight k 𝔑 𝔭.1 * u ^ 2) : PowerSeries ℂ) *
      PowerSeries.mk (fun j ↦ N.idealCoeff (𝔭.1 ^ j) * u ^ j) = 1 := by
  refine eulerPoly_mul_mk ?_ ?_ fun j ↦ ?_
  · rw [pow_zero, pow_zero, Ideal.one_eq_top, N.idealCoeff_top hK, mul_one]
  · rw [pow_one, pow_one, N.idealCoeff_self hK hk]
  · rw [N.idealCoeff_pow_add_two hK hk 𝔭 j]
    ring1

variable (j) in
lemma normCoeff_pow_of_eq_mul_self (hp : p.Prime) (h𝔮 : 𝔮.IsPrime) (hN : Ideal.absNorm 𝔮 = p)
    (hP : Ideal.span {(p : 𝓞 K)} = 𝔮 * 𝔮) : N.normCoeff (p ^ j) = N.idealCoeff (𝔮 ^ j) := by
  have e : {𝔫 : Ideal (𝓞 K) | Ideal.absNorm 𝔫 = p ^ j} = {𝔮 ^ j} := by
    refine Set.ext fun 𝔞 ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rcases exists_eq_pow_mul_pow hp h𝔮 h𝔮 hN hN hP h with ⟨a, b, hab, rfl⟩
      rw [← pow_add, hab]
      exact Set.mem_singleton _
    · rw [Set.mem_singleton_iff.mp h, Set.mem_ofPred_eq, map_pow, hN]
  rw [normCoeff, e, finsum_mem_singleton]

variable (j) in
lemma normCoeff_pow_of_ne (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hp : p.Prime) (h𝔮 : 𝔮.IsPrime)
    (h𝔮' : 𝔮'.IsPrime) (hN : Ideal.absNorm 𝔮 = p) (hN' : Ideal.absNorm 𝔮' = p)
    (hP : Ideal.span {(p : 𝓞 K)} = 𝔮 * 𝔮') (hne : 𝔮 ≠ 𝔮') : N.normCoeff (p ^ j) =
    ∑ x ∈ Finset.antidiagonal j, N.idealCoeff (𝔮 ^ x.1) * N.idealCoeff (𝔮' ^ x.2) := by
  classical
  have h₀ {𝔯 : Ideal (𝓞 K)} (h𝔯 : Ideal.absNorm 𝔯 = p) : 𝔯 ≠ ⊥ := ne_bot_of_absNorm_eq hp h𝔯
  have hπ : Prime 𝔮 := Ideal.prime_of_isPrime (h₀ hN) h𝔮
  have hnd : ¬𝔮 ∣ 𝔮' := fun h ↦ hne ((h𝔮'.isMaximal (h₀ hN')).eq_of_le h𝔮.ne_top
    (Ideal.le_of_dvd h)).symm
  have hmult (a b : ℕ) : emultiplicity 𝔮 (𝔮 ^ a * 𝔮' ^ b) = a := by
    rw [emultiplicity_mul hπ, emultiplicity_pow_self_of_prime hπ,
      emultiplicity_eq_zero.mpr fun h ↦ hnd (hπ.dvd_of_dvd_pow h), add_zero]
  have hinj : Set.InjOn (fun x : ℕ × ℕ ↦ 𝔮 ^ x.1 * 𝔮' ^ x.2)
      (Finset.antidiagonal j : Set (ℕ × ℕ)) := fun x hx y hy he ↦ by
    have he' : 𝔮 ^ x.1 * 𝔮' ^ x.2 = 𝔮 ^ y.1 * 𝔮' ^ y.2 := he
    have h₁ : (x.1 : ℕ∞) = y.1 := by
      rw [← hmult x.1 x.2, he', hmult y.1 y.2]
    have h₂ : x.1 = y.1 := by
      exact_mod_cast h₁
    have hx' : x.1 + x.2 = j := Finset.mem_antidiagonal.mp hx
    have hy' : y.1 + y.2 = j := Finset.mem_antidiagonal.mp hy
    exact Prod.ext h₂ (by omega)
  have e : {𝔫 : Ideal (𝓞 K) | Ideal.absNorm 𝔫 = p ^ j} =
      ((Finset.antidiagonal j).image fun x : ℕ × ℕ ↦ 𝔮 ^ x.1 * 𝔮' ^ x.2 :
        Finset (Ideal (𝓞 K))) := by
    refine Set.ext fun 𝔞 ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have h' : Ideal.absNorm 𝔞 = p ^ j := h
      rcases exists_eq_pow_mul_pow hp h𝔮 h𝔮' hN hN' hP h' with ⟨a, b, hab, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(a, b), Finset.mem_antidiagonal.mpr hab, rfl⟩)
    · rcases Finset.mem_image.mp (Finset.mem_coe.mp h) with ⟨x, hx, rfl⟩
      rw [Set.mem_ofPred_eq, map_mul, map_pow, map_pow, hN, hN', ← pow_add,
        Finset.mem_antidiagonal.mp hx]
  have hcop : IsCoprime 𝔮 𝔮' := Ideal.isCoprime_iff_sup_eq.mpr
    ((h𝔮.isMaximal (h₀ hN)).coprime_of_ne (h𝔮'.isMaximal (h₀ hN')) hne)
  rw [normCoeff, e, finsum_mem_coe_finset, Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun x _ ↦ N.idealCoeff_mul hK hk (pow_ne_zero _ (h₀ hN))
    (pow_ne_zero _ (h₀ hN')) (hcop.pow)

lemma normCoeff_pow_two_mul (hK : finrank ℚ K = 2) (hp : p.Prime)
    (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) (i : ℕ) :
    N.normCoeff (p ^ (2 * i)) = N.idealCoeff (Ideal.span {(p : 𝓞 K)} ^ i) := by
  have e : {𝔫 : Ideal (𝓞 K) | Ideal.absNorm 𝔫 = p ^ (2 * i)} = {Ideal.span {(p : 𝓞 K)} ^ i} := by
    refine Set.ext fun 𝔞 ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rcases exists_eq_pow_of_isPrime hK hp hP h with ⟨i', hi', rfl⟩
      have hi : i' = i := by
        omega
      rw [hi]
      exact Set.mem_singleton _
    · rw [Set.mem_singleton_iff.mp h, Set.mem_ofPred_eq, map_pow, absNorm_span_natCast_eq_sq p hK,
        ← pow_mul]
  rw [normCoeff, e, finsum_mem_singleton]

lemma normCoeff_pow_two_mul_add_one (hK : finrank ℚ K = 2) (hp : p.Prime)
    (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) (i : ℕ) : N.normCoeff (p ^ (2 * i + 1)) = 0 := by
  have e : {𝔫 : Ideal (𝓞 K) | Ideal.absNorm 𝔫 = p ^ (2 * i + 1)} = ∅ :=
    Set.eq_empty_of_forall_notMem fun 𝔞 h ↦ by
      rcases exists_eq_pow_of_isPrime hK hp hP h with ⟨i', hi', -⟩
      omega
  rw [normCoeff, e, finsum_mem_empty]

lemma exists_eulerFactor_of_isPrime (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hp : p.Prime)
    (hdvd : p ∣ Ideal.absNorm 𝔑 * (discr K).natAbs ^ 2 ↔ p ∣ Ideal.absNorm 𝔑 ∨ (p : ℤ) ∣ discr K)
    {u : ℂ} (hu₂ : (p : ℂ) ^ (k / 2) * u ^ 2 = 1)
    (hl : ∀ j : ℕ, N.lCoeff (p ^ j) = N.normCoeff (p ^ j) * u ^ j)
    (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) : ∃ F : ℂ[X], F.natDegree ≤ 4 ∧
    (F.natDegree = 4 ↔ ¬p ∣ Ideal.absNorm 𝔑 * (discr K).natAbs ^ 2) ∧
    (F : PowerSeries ℂ) * PowerSeries.mk (fun j ↦ N.lCoeff (p ^ j)) = 1 := by
  have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := absNorm_span_natCast_eq_sq p hK
  have hP₀ : Ideal.span {(p : 𝓞 K)} ≠ ⊥ := span_natCast_ne_bot hp
  have hmem : (p : 𝓞 K) ∈ Ideal.span {(p : 𝓞 K)} := Ideal.mem_span_singleton_self _
  have hdisc : ¬(p : ℤ) ∣ discr K := by
    refine (not_dvd_discr_iff_forall hp).mpr fun 𝔯 h𝔯 hp𝔯 hle ↦ ?_
    have he : Ideal.span {(p : 𝓞 K)} = 𝔯 := (hP.isMaximal hP₀).eq_of_le h𝔯.ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hp𝔯)
    subst he
    have h₁ : Ideal.absNorm (Ideal.span {(p : 𝓞 K)} ^ 2) ∣
        Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [map_pow, hN, ← pow_mul] at h₁
    have h₂ : 2 * 2 ≤ 2 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h₁
    omega
  have hlevel : p ∣ Ideal.absNorm 𝔑 ↔ 𝔑 ≤ Ideal.span {(p : 𝓞 K)} := by
    rw [dvd_absNorm_iff hK hp]
    refine ⟨fun ⟨𝔯, h𝔯, hp𝔯, hle⟩ ↦ ?_, fun h ↦ ⟨_, hP.isMaximal hP₀, hmem, h⟩⟩
    have he : Ideal.span {(p : 𝓞 K)} = 𝔯 := (hP.isMaximal hP₀).eq_of_le h𝔯.ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hp𝔯)
    exact he ▸ hle
  have hE : heckeWeight k 𝔑 (Ideal.span {(p : 𝓞 K)}) * u ^ 4 ≠ 0 ↔ ¬𝔑 ≤ Ideal.span {(p : 𝓞 K)} := by
    refine ⟨fun h h₁ ↦ h (by rw [heckeWeight_of_le h₁, zero_mul]), fun h ↦ ?_⟩
    have e :
        heckeWeight k 𝔑 (Ideal.span {(p : 𝓞 K)}) * u ^ 4 = ((p : ℂ) ^ (k / 2) * u ^ 2) ^ 2 := by
      rw [heckeWeight_of_not_le h, hN]
      push_cast
      ring1
    rw [e, hu₂, one_pow]
    exact one_ne_zero
  have hdeg (A E : ℂ) :
      ((eulerPoly A E).comp (X ^ 2)).natDegree = (eulerPoly A E).natDegree * 2 := by
    rw [natDegree_comp, natDegree_X_pow]
  refine ⟨(eulerPoly (N.eigenvalue ⟨_, hP, hP₀⟩ * u ^ 2)
    (heckeWeight k 𝔑 (Ideal.span {(p : 𝓞 K)}) * u ^ 4)).comp (X ^ 2), ?_, ?_, ?_⟩
  · have h₁ : (eulerPoly (N.eigenvalue ⟨_, hP, hP₀⟩ * u ^ 2)
        (heckeWeight k 𝔑 (Ideal.span {(p : 𝓞 K)}) * u ^ 4)).natDegree ≤ 2 :=
      natDegree_eulerPoly_le_two
    rw [hdeg]
    omega
  · rw [hdeg, hdvd, hlevel, not_or, and_iff_left hdisc, ← hE,
      ← natDegree_eulerPoly_eq_two_iff (A := N.eigenvalue ⟨_, hP, hP₀⟩ * u ^ 2)]
    omega
  · have hx₀ (i : ℕ) :
        N.lCoeff (p ^ (2 * i)) = N.idealCoeff (Ideal.span {(p : 𝓞 K)} ^ i) * u ^ (2 * i) := by
      rw [hl, N.normCoeff_pow_two_mul hK hp hP]
    have hx₁ (i : ℕ) : N.lCoeff (p ^ (2 * i + 1)) = 0 := by
      rw [hl, N.normCoeff_pow_two_mul_add_one hK hp hP, zero_mul]
    refine eulerPoly_comp_mul_mk ?_ ?_ ?_ ?_ fun n ↦ ?_
    · rw [pow_zero]
      exact N.lCoeff_one hK
    · exact hx₁ 0
    · have h₁ :
          N.lCoeff (p ^ (2 * 1)) = N.idealCoeff (Ideal.span {(p : 𝓞 K)} ^ 1) * u ^ (2 * 1) := hx₀ 1
      rw [pow_one, mul_one] at h₁
      rw [h₁]
      exact congrArg (· * u ^ 2) (N.idealCoeff_self hK hk ⟨_, hP, hP₀⟩)
    · exact hx₁ 1
    · rcases Nat.even_or_odd' n with ⟨i, rfl | rfl⟩
      · have e₁ : 2 * i + 4 = 2 * (i + 2) := by
          ring1
        have e₂ : 2 * i + 2 = 2 * (i + 1) := by
          ring1
        rw [e₁, e₂, hx₀, hx₀, hx₀, N.idealCoeff_pow_add_two hK hk ⟨_, hP, hP₀⟩ i]
        ring1
      · have e₁ : 2 * i + 1 + 4 = 2 * (i + 2) + 1 := by
          ring1
        have e₂ : 2 * i + 1 + 2 = 2 * (i + 1) + 1 := by
          ring1
        rw [e₁, e₂, hx₁, hx₁, hx₁, mul_zero, mul_zero, sub_zero]

/-- **The local factors of the L-function of a Bianchi newform** (LMFDB `lfunction.euler_product`,
`mf.bianchi.anr`): for `K` imaginary quadratic of class number `1` and a rational prime `p`, there
is a polynomial `F_p` of degree at most `4`, of degree `4` exactly for `p ∤ N(𝔑) Δ²`, with
`F_p(T) ∑_j a_{p^j} T^j = 1`. -/
lemma exists_eulerFactor (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hp : p.Prime) : ∃ F : ℂ[X],
    F.natDegree ≤ 4 ∧ (F.natDegree = 4 ↔ ¬p ∣ Ideal.absNorm 𝔑 * (discr K).natAbs ^ 2) ∧
    (F : PowerSeries ℂ) * PowerSeries.mk (fun j ↦ N.lCoeff (p ^ j)) = 1 := by
  have hk' : Even k := N.even hK
  have hdvd :
      p ∣ Ideal.absNorm 𝔑 * (discr K).natAbs ^ 2 ↔ p ∣ Ideal.absNorm 𝔑 ∨ (p : ℤ) ∣ discr K := by
    rw [hp.dvd_mul, Int.natCast_dvd]
    exact or_congr_right ⟨fun h ↦ hp.dvd_of_dvd_pow h, fun h ↦ dvd_pow h two_ne_zero⟩
  rcases (⟨_, rfl⟩ : ∃ u : ℂ, u = (((p : ℝ) ^ ((k : ℝ) / 4) : ℝ) : ℂ)⁻¹) with ⟨u, hu⟩
  have hu₂ : (p : ℂ) ^ (k / 2) * u ^ 2 = 1 := hu ▸ natCast_pow_mul_sq hk' hp.ne_zero
  have hl (j : ℕ) : N.lCoeff (p ^ j) = N.normCoeff (p ^ j) * u ^ j := hu ▸ N.lCoeff_pow p j
  have hE {𝔮 : Ideal (𝓞 K)} (hN : Ideal.absNorm 𝔮 = p) :
      heckeWeight k 𝔑 𝔮 * u ^ 2 ≠ 0 ↔ ¬𝔑 ≤ 𝔮 := by
    refine ⟨fun h h₁ ↦ h (by rw [heckeWeight_of_le h₁, zero_mul]), fun h ↦ ?_⟩
    rw [heckeWeight_of_not_le h, hN, hu₂]
    exact one_ne_zero
  rcases exists_factorization hK hp with hP | ⟨𝔮, 𝔮', h𝔮, h𝔮', hN, hN', hP⟩
  · exact N.exists_eulerFactor_of_isPrime hK hk hp hdvd hu₂ hl hP
  · have h₀ {𝔯 : Ideal (𝓞 K)} (h𝔯 : Ideal.absNorm 𝔯 = p) : 𝔯 ≠ ⊥ := ne_bot_of_absNorm_eq hp h𝔯
    have hmem : (p : 𝓞 K) ∈ 𝔮 * 𝔮' := by
      rw [← hP]
      exact Ideal.mem_span_singleton_self _
    have hmem₁ : (p : 𝓞 K) ∈ 𝔮 := Ideal.mul_le_left hmem
    have hmem₂ : (p : 𝓞 K) ∈ 𝔮' := Ideal.mul_le_right hmem
    by_cases hne : 𝔮 = 𝔮'
    · subst hne
      refine ⟨eulerPoly (N.eigenvalue ⟨𝔮, h𝔮, h₀ hN⟩ * u) (heckeWeight k 𝔑 𝔮 * u ^ 2),
        natDegree_eulerPoly_le_two.trans (by norm_num), ⟨fun h ↦ ?_, fun h ↦ ?_⟩, ?_⟩
      · have h₁ : (eulerPoly (N.eigenvalue ⟨𝔮, h𝔮, h₀ hN⟩ * u)
            (heckeWeight k 𝔑 𝔮 * u ^ 2)).natDegree ≤ 2 := natDegree_eulerPoly_le_two
        omega
      · exfalso
        refine h (hdvd.mpr (Or.inr (by_contra fun hd ↦ ?_)))
        refine (not_dvd_discr_iff_forall hp).mp hd 𝔮 h𝔮 hmem₁ ?_
        rw [hP, sq]
      · have e : (fun j ↦ N.lCoeff (p ^ j)) = fun j ↦ N.idealCoeff (𝔮 ^ j) * u ^ j := by
          funext j
          rw [hl, N.normCoeff_pow_of_eq_mul_self _ hp h𝔮 hN hP]
        rw [e]
        exact N.eulerPoly_mul_mk_idealCoeff hK hk ⟨𝔮, h𝔮, h₀ hN⟩ u
    · have hnd : ¬𝔮 ∣ 𝔮' := fun h ↦ hne ((h𝔮'.isMaximal (h₀ hN')).eq_of_le h𝔮.ne_top
        (Ideal.le_of_dvd h)).symm
      have hnd' : ¬𝔮' ∣ 𝔮 := fun h ↦ hne ((h𝔮.isMaximal (h₀ hN)).eq_of_le h𝔮'.ne_top
        (Ideal.le_of_dvd h))
      have hdisc : ¬(p : ℤ) ∣ discr K := by
        refine (not_dvd_discr_iff_forall hp).mpr fun 𝔯 h𝔯 hp𝔯 hle ↦ ?_
        have h𝔯₀ : 𝔯 ≠ ⊥ := fun h₁ ↦ hp.ne_zero <| by
          rw [h₁, Ideal.mem_bot] at hp𝔯
          exact_mod_cast hp𝔯
        rcases h𝔯.mul_le.mp (hP ▸ (Ideal.span_singleton_le_iff_mem _).mpr hp𝔯 :
          𝔮 * 𝔮' ≤ 𝔯) with h₁ | h₁
        · have he : 𝔮 = 𝔯 := (h𝔮.isMaximal (h₀ hN)).eq_of_le h𝔯.ne_top h₁
          subst he
          rw [hP, sq] at hle
          exact hnd ((mul_dvd_mul_iff_left (h₀ hN)).mp (Ideal.dvd_iff_le.mpr hle))
        · have he : 𝔮' = 𝔯 := (h𝔮'.isMaximal (h₀ hN')).eq_of_le h𝔯.ne_top h₁
          subst he
          rw [hP, sq, mul_comm] at hle
          exact hnd' ((mul_dvd_mul_iff_left (h₀ hN')).mp (Ideal.dvd_iff_le.mpr hle))
      have hlevel : p ∣ Ideal.absNorm 𝔑 ↔ 𝔑 ≤ 𝔮 ∨ 𝔑 ≤ 𝔮' := by
        rw [dvd_absNorm_iff hK hp]
        refine ⟨fun ⟨𝔯, h𝔯, hp𝔯, hle⟩ ↦ ?_, fun h ↦ ?_⟩
        · rcases h𝔯.isPrime.mul_le.mp (hP ▸ (Ideal.span_singleton_le_iff_mem _).mpr hp𝔯 :
            𝔮 * 𝔮' ≤ 𝔯) with h₁ | h₁
          · exact Or.inl (((h𝔮.isMaximal (h₀ hN)).eq_of_le h𝔯.ne_top h₁) ▸ hle)
          · exact Or.inr (((h𝔮'.isMaximal (h₀ hN')).eq_of_le h𝔯.ne_top h₁) ▸ hle)
        · rcases h with h | h
          · exact ⟨𝔮, h𝔮.isMaximal (h₀ hN), hmem₁, h⟩
          · exact ⟨𝔮', h𝔮'.isMaximal (h₀ hN'), hmem₂, h⟩
      have hne₀ : eulerPoly (N.eigenvalue ⟨𝔮, h𝔮, h₀ hN⟩ * u) (heckeWeight k 𝔑 𝔮 * u ^ 2) ≠ 0 :=
        eulerPoly_ne_zero
      have hne₁ : eulerPoly (N.eigenvalue ⟨𝔮', h𝔮', h₀ hN'⟩ * u) (heckeWeight k 𝔑 𝔮' * u ^ 2) ≠ 0 :=
        eulerPoly_ne_zero
      have hd₁ : (eulerPoly (N.eigenvalue ⟨𝔮, h𝔮, h₀ hN⟩ * u)
          (heckeWeight k 𝔑 𝔮 * u ^ 2)).natDegree ≤ 2 := natDegree_eulerPoly_le_two
      have hd₂ : (eulerPoly (N.eigenvalue ⟨𝔮', h𝔮', h₀ hN'⟩ * u)
          (heckeWeight k 𝔑 𝔮' * u ^ 2)).natDegree ≤ 2 := natDegree_eulerPoly_le_two
      refine ⟨eulerPoly (N.eigenvalue ⟨𝔮, h𝔮, h₀ hN⟩ * u) (heckeWeight k 𝔑 𝔮 * u ^ 2) *
        eulerPoly (N.eigenvalue ⟨𝔮', h𝔮', h₀ hN'⟩ * u) (heckeWeight k 𝔑 𝔮' * u ^ 2), ?_, ?_, ?_⟩
      · rw [natDegree_mul hne₀ hne₁]
        omega
      · rw [natDegree_mul hne₀ hne₁, hdvd, hlevel, not_or, not_or, and_iff_left hdisc, ← hE hN,
          ← hE hN', ← natDegree_eulerPoly_eq_two_iff (A := N.eigenvalue ⟨𝔮, h𝔮, h₀ hN⟩ * u),
          ← natDegree_eulerPoly_eq_two_iff (A := N.eigenvalue ⟨𝔮', h𝔮', h₀ hN'⟩ * u)]
        omega
      · have e : PowerSeries.mk (fun j ↦ N.lCoeff (p ^ j)) =
            PowerSeries.mk (fun j ↦ N.idealCoeff (𝔮 ^ j) * u ^ j) *
              PowerSeries.mk (fun j ↦ N.idealCoeff (𝔮' ^ j) * u ^ j) := by
          ext j
          rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, hl,
            N.normCoeff_pow_of_ne _ hK hk hp h𝔮 h𝔮' hN hN' hP hne, Finset.sum_mul]
          refine Finset.sum_congr rfl fun x hx ↦ ?_
          rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, ← Finset.mem_antidiagonal.mp hx, pow_add]
          ring1
        rw [e, Polynomial.coe_mul, mul_mul_mul_comm,
          N.eulerPoly_mul_mk_idealCoeff hK hk ⟨𝔮, h𝔮, h₀ hN⟩ u,
          N.eulerPoly_mul_mk_idealCoeff hK hk ⟨𝔮', h𝔮', h₀ hN'⟩ u, one_mul]

end BianchiNewformOfWeight

end HyperbolicThreeSpace
