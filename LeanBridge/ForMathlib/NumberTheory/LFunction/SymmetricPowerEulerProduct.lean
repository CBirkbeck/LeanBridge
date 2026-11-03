import LeanBridge.ForMathlib.NumberTheory.LFunction.CriticalStrip
import LeanBridge.ForMathlib.NumberTheory.LFunction.Primitive
import LeanBridge.ForMathlib.NumberTheory.LFunction.SymmetricPower

/-!
# The Euler product of a symmetric power of an L-function

The symmetric `n`-th power (LMFDB `lfunction.symm`) of an analytic L-function `L` of conductor `N`
is written in the knowl as an explicit Euler product

`L(s, symⁿ) = ∏_{p ∤ N} ∏_m (1 - m(α₁(p), …, α_r(p)) p ^ (-s))⁻¹ × ∏_{p ∣ N} L_p(s, symⁿ)`.

This file defines that product as a formal Dirichlet series, the way Mathlib defines the L-function
of a Weierstrass curve: the reciprocal of each local polynomial is a power series, which
`ArithmeticFunction.ofPowerSeries` turns into a local factor, and these are multiplied by
`ArithmeticFunction.eulerProduct`. The knowl leaves the factors at the primes `p ∣ N` to a recipe
that it does not state, so they are a parameter `B : ℕ → ℂ[X]`, of which only the values at the
primes `p ∣ N` matter: two choices of `B` give the same coefficients at every `m` coprime to `N`.
The series exists for every `L`, `n` and `B`. It converges absolutely on a right half plane, with no
appeal to the Ramanujan bounds, and there, for bad factors with constant coefficient `1`, its
L-series is the product above.

That function is not shown to be an analytic L-function: its continuation and functional equation
are symmetric-power functoriality, open in general and known only in special cases, so for a general
`L` an analytic L-function `M` with `L.IsSymmetricPower n M` is available in Lean only for `n = 0`
and `n = 1`. What is proved is that `IsSymmetricPower` says exactly that the coefficients of `M` are
those of the series for the bad factors of `M`.

## Main definitions

* `AnalyticLFunction.symmetricPowerLocalFactor` (LMFDB `lfunction.symm`): the Euler factor at `p` of
  the symmetric `n`-th power, given the bad factors.
* `AnalyticLFunction.symmetricPowerDirichletSeries` (LMFDB `lfunction.symm`): the Euler product of
  the symmetric `n`-th power as a formal Dirichlet series, given the bad factors.

## Main results

* `AnalyticLFunction.isMultiplicative_symmetricPowerDirichletSeries`: the series is multiplicative.
* `AnalyticLFunction.symmetricPowerDirichletSeries_prime_pow`: its coefficient at `p ^ k` is the
  coefficient of `T ^ k` in the reciprocal of the local factor at `p`.
* `AnalyticLFunction.coe_symmetricPowerLocalFactor_mul_mk`: the local factor at `p` times
  `∑ₖ a_{pᵏ} Tᵏ` is `1`, with no condition on the bad factors at `p ∤ N`.
* `AnalyticLFunction.symmetricPowerDirichletSeries_eq_of_coprime`: the coefficients at `m` coprime
  to `N` do not depend on the bad factors.
* `AnalyticLFunction.isSymmetricPower_iff`: `M` is the symmetric `n`-th power of `L` exactly when
  its coefficients are those of the series for the bad factors of `M`.
* `AnalyticLFunction.symmetricPowerDirichletSeries_one`: for the bad factors of `L`, the series of
  the symmetric first power has the coefficients of `L`.
* `AnalyticLFunction.symmetricPowerDirichletSeries_zero`: for the bad factors of `ζ`, the series of
  the symmetric zeroth power has the coefficients of `ζ`.
* `AnalyticLFunction.abscissaOfAbsConv_symmetricPowerDirichletSeries_lt_top`: the series converges
  absolutely on a right half plane, for all bad factors.
* `AnalyticLFunction.hasProd_eval_symmetricPowerLocalFactor_inv`: on that half plane, its L-series
  is the Euler product of the knowl.
-/

open ArithmeticFunction Finset Polynomial TauCeti LSeries

open scoped NNReal PowerSeries

namespace AnalyticLFunction

variable {ι : Type*} (L : AnalyticLFunction) (n : ℕ) (B : ℕ → ℂ[X]) {M : AnalyticLFunction}
  {p m : ℕ}

lemma mk_prod_prime_pow (hp : p.Prime) (s : Finset ι) (f : ι → ArithmeticFunction ℂ) :
    PowerSeries.mk (fun k ↦ (∏ i ∈ s, f i) (p ^ k)) =
      ∏ i ∈ s, PowerSeries.mk (fun k ↦ f i (p ^ k)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext k
    simp [one_apply, hp.ne_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, ← ih, ← mk_convolution_prime_pow hp,
      ArithmeticFunction.coe_mul]

lemma eulerProduct_ofPowerSeries_prime_pow {g : Nat.Primes → ℂ⟦X⟧}
    (hg : ∀ q, (g q).constantCoeff = 1) (q : Nat.Primes) (k : ℕ) :
    eulerProduct (fun r : Nat.Primes ↦ ofPowerSeries r (g r)) ((q : ℕ) ^ k) = (g q).coeff k := by
  have hN : Northcott fun r : Nat.Primes ↦ (r : ℕ) :=
    ⟨fun b ↦ (Set.finite_Iic b).preimage Subtype.coe_injective.injOn⟩
  rcases ((tendsTo_eulerProduct_ofPowerSeries (fun r : Nat.Primes ↦ (r : ℕ)) g hg ((q : ℕ) ^ k)).and
    (Filter.eventually_ge_atTop {q})).exists with ⟨s, hs, hqs⟩
  have h : PowerSeries.mk (fun k ↦ (∏ r ∈ s, ofPowerSeries (r : ℕ) (g r)) ((q : ℕ) ^ k)) = g q := by
    rw [mk_prod_prime_pow q.2, Finset.prod_eq_single_of_mem q (hqs (Finset.mem_singleton_self q))]
    · ext j
      rw [PowerSeries.coeff_mk, ofPowerSeries_apply_pow q.2.one_lt]
    · rintro r - hrq
      ext j
      rcases j with _ | j
      · simpa using hg r
      · rw [PowerSeries.coeff_mk, ofPowerSeries_apply r.2.one_lt, Function.extend_apply',
          Pi.zero_apply, PowerSeries.coeff_one, ite_eq_right j.succ_ne_zero]
        rintro ⟨a, ha⟩
        exact hrq <| Subtype.ext <| .symm <| (Nat.prime_dvd_prime_iff_eq q.2 r.2).mp <|
          q.2.dvd_of_dvd_pow <| ha ▸ dvd_pow_self (q : ℕ) j.succ_ne_zero
  rw [← hs, ← h, PowerSeries.coeff_mk]

variable (p) in
/-- The **Euler factor at `p` of the symmetric `n`-th power** (LMFDB `lfunction.symm`) of an
analytic L-function `L` of conductor `N`, with bad factors `B`: the polynomial `∏_m (1 - m T)` of
`symmetricPowerEulerFactor` at `p ∤ N`, and `B p` at `p ∣ N`, where the knowl gives no recipe. -/
noncomputable def symmetricPowerLocalFactor : ℂ[X] :=
  if p ∣ L.conductor then B p else L.symmetricPowerEulerFactor n p

/-- The **symmetric `n`-th power** `L(s, symⁿ)` (LMFDB `lfunction.symm`) of an analytic L-function
`L`, with bad factors `B`, as a formal Dirichlet series: the Euler product over the primes `p` of
the reciprocals of `symmetricPowerLocalFactor`, built as Mathlib's `WeierstrassCurve.LFunction`.
A reciprocal is a true inverse when the local factor has constant coefficient `1`, as
`M.eulerPolynomial` has for every analytic L-function `M`; otherwise `PowerSeries.invOfUnit` gives a
junk value. -/
noncomputable def symmetricPowerDirichletSeries : ArithmeticFunction ℂ :=
  eulerProduct fun q : Nat.Primes ↦ ofPowerSeries q <|
    PowerSeries.invOfUnit (L.symmetricPowerLocalFactor n B q) 1

/-- **The series of a symmetric power is multiplicative**, for all bad factors. -/
lemma isMultiplicative_symmetricPowerDirichletSeries :
    (L.symmetricPowerDirichletSeries n B).IsMultiplicative :=
  isMultiplicative_eulerProduct _ fun q ↦
    isMultiplicative_ofPowerSeries_of_isPrimePow _ q.2.isPrimePow _ <| by simp

/-- **The coefficient of the series of a symmetric power at `p ^ k`** is the coefficient of `T ^ k`
in the reciprocal of the local factor at `p`. -/
lemma symmetricPowerDirichletSeries_prime_pow (hp : p.Prime) (k : ℕ) :
    L.symmetricPowerDirichletSeries n B (p ^ k) =
      (PowerSeries.invOfUnit (L.symmetricPowerLocalFactor n B p) 1).coeff k :=
  eulerProduct_ofPowerSeries_prime_pow (fun _ ↦ by simp) ⟨p, hp⟩ k

lemma coeff_zero_symmetricPowerEulerFactor : (L.symmetricPowerEulerFactor n p).coeff 0 = 1 := by
  simp [symmetricPowerEulerFactor, coeff_zero_eq_eval_zero, eval_multiset_prod]

/-- **The local factor of a symmetric power at `p` times `∑ₖ a_{pᵏ} Tᵏ` is `1`**, where `aₙ` are the
coefficients of the series. So at `p ∤ N` the series has the Euler factor `∏_m (1 - m T)` of the
knowl, whatever `B` is, and at `p ∣ N` the factor `B p`, if that has constant coefficient `1`. -/
lemma coe_symmetricPowerLocalFactor_mul_mk (hp : p.Prime)
    (hB : p ∣ L.conductor → (B p).coeff 0 = 1) :
    (L.symmetricPowerLocalFactor n B p : ℂ⟦X⟧) *
      PowerSeries.mk (fun k ↦ L.symmetricPowerDirichletSeries n B (p ^ k)) = 1 := by
  have hF : (L.symmetricPowerLocalFactor n B p).coeff 0 = 1 := by
    rw [symmetricPowerLocalFactor]
    split_ifs with hpN
    · exact hB hpN
    · exact L.coeff_zero_symmetricPowerEulerFactor n
  have h : PowerSeries.mk (fun k ↦ L.symmetricPowerDirichletSeries n B (p ^ k)) =
      PowerSeries.invOfUnit (L.symmetricPowerLocalFactor n B p) 1 := by
    ext k
    rw [PowerSeries.coeff_mk, L.symmetricPowerDirichletSeries_prime_pow n B hp]
  rw [h]
  exact PowerSeries.mul_invOfUnit _ _ <| by simp [hF]

/-- **The coefficients at `m` coprime to the conductor do not depend on the bad factors**: so the
series for the various `B` are one Dirichlet series away from the bad primes, multiplied by the
factors at the bad primes, which is all that the knowl determines. -/
lemma symmetricPowerDirichletSeries_eq_of_coprime (B' : ℕ → ℂ[X]) (hm : m.Coprime L.conductor) :
    L.symmetricPowerDirichletSeries n B m = L.symmetricPowerDirichletSeries n B' m := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    have hpN : ¬p ∣ L.conductor :=
      hp.coprime_iff_not_dvd.mp <| hm.coprime_dvd_left <| dvd_pow_self p hk.ne'
    rw [symmetricPowerDirichletSeries_prime_pow _ _ _ hp,
      symmetricPowerDirichletSeries_prime_pow _ _ _ hp, symmetricPowerLocalFactor,
      symmetricPowerLocalFactor, ite_eq_right hpN, ite_eq_right hpN]
  | zero =>
    simp
  | one =>
    rw [(L.isMultiplicative_symmetricPowerDirichletSeries n B).map_one,
      (L.isMultiplicative_symmetricPowerDirichletSeries n B').map_one]
  | coprime a b _ _ hab iha ihb =>
    rw [(L.isMultiplicative_symmetricPowerDirichletSeries n B).map_mul_of_coprime hab,
      (L.isMultiplicative_symmetricPowerDirichletSeries n B').map_mul_of_coprime hab,
      iha hm.coprime_mul_right, ihb hm.coprime_mul_left]

variable {L n}

lemma coe_eulerPolynomial_mul_mk (hp : p.Prime) :
    (M.eulerPolynomial p : ℂ⟦X⟧) * PowerSeries.mk (fun k ↦ M.coeff (p ^ k)) = 1 := by
  rcases M.exists_eulerFactor p hp with ⟨F, -, -, hF⟩
  rwa [eulerPolynomial_eq hp hF]

lemma IsSymmetricPower.mk_symmetricPowerDirichletSeries_eq (h : L.IsSymmetricPower n M)
    (hp : p.Prime) :
    PowerSeries.mk (fun k ↦ L.symmetricPowerDirichletSeries n M.eulerPolynomial (p ^ k)) =
      PowerSeries.mk (fun k ↦ M.coeff (p ^ k)) := by
  have hF : L.symmetricPowerLocalFactor n M.eulerPolynomial p = M.eulerPolynomial p := by
    by_cases hpN : p ∣ L.conductor
    · exact ite_eq_left hpN
    · exact (ite_eq_right hpN).trans <| coe_inj.mp <|
        (h p hp hpN).symm.trans (coe_eulerPolynomial hp).symm
  refine left_inv_eq_right_inv ?_ <| coe_eulerPolynomial_mul_mk hp
  rw [mul_comm, ← hF]
  exact L.coe_symmetricPowerLocalFactor_mul_mk n _ hp fun _ ↦ coeff_zero_eulerPolynomial

variable {B} in
lemma isSymmetricPower_of_forall_coeff_eq
    (h : ∀ m ≠ 0, L.symmetricPowerDirichletSeries n B m = M.coeff m) : L.IsSymmetricPower n M :=
  fun p hp hpN ↦ M.eulerFactor_eq <| by
    have hk : PowerSeries.mk (fun k ↦ M.coeff (p ^ k)) =
        PowerSeries.mk (fun k ↦ L.symmetricPowerDirichletSeries n B (p ^ k)) :=
      PowerSeries.ext fun k ↦ by simp [h _ (pow_ne_zero k hp.ne_zero)]
    have hF : L.symmetricPowerLocalFactor n B p = L.symmetricPowerEulerFactor n p :=
      ite_eq_right hpN
    rw [hk, ← hF]
    exact L.coe_symmetricPowerLocalFactor_mul_mk n B hp fun h ↦ absurd h hpN

/-- **`M` is the symmetric `n`-th power of `L` exactly when its coefficients are those of the series
of the symmetric `n`-th power of `L` for the bad factors of `M`**. So `IsSymmetricPower` adds to the
series only that it comes from an analytic L-function. In the converse any bad factors will do. -/
lemma isSymmetricPower_iff : L.IsSymmetricPower n M ↔
    ∀ m ≠ 0, L.symmetricPowerDirichletSeries n M.eulerPolynomial m = M.coeff m := by
  refine ⟨fun h m hm ↦ ?_, isSymmetricPower_of_forall_coeff_eq⟩
  have hs :
      L.symmetricPowerDirichletSeries n M.eulerPolynomial = toArithmeticFunction M.coeff := by
    refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
      (L.isMultiplicative_symmetricPowerDirichletSeries n _) _
      M.isMultiplicative_toArithmeticFunction_coeff).mpr fun p k hp ↦ ?_
    simpa [toArithmeticFunction, hp.ne_zero] using
      congrArg (PowerSeries.coeff k) (h.mk_symmetricPowerDirichletSeries_eq hp)
  simp [hs, toArithmeticFunction, hm]

variable (L)

/-- **The series of the symmetric first power is `L`**, for the bad factors of `L`. -/
lemma symmetricPowerDirichletSeries_one (hm : m ≠ 0) :
    L.symmetricPowerDirichletSeries 1 L.eulerPolynomial m = L.coeff m :=
  isSymmetricPower_iff.mp L.isSymmetricPower_one m hm

/-- **The series of the symmetric zeroth power is `ζ`**, for the bad factors of `ζ`. -/
lemma symmetricPowerDirichletSeries_zero (hm : m ≠ 0) :
    L.symmetricPowerDirichletSeries 0 zeta.eulerPolynomial m = zeta.coeff m :=
  isSymmetricPower_iff.mp L.isSymmetricPower_zero_zeta m hm

variable (n)

lemma norm_le_of_mem_satakeParameters (hp : p.Prime) {α : ℂ} (hα : α ∈ L.satakeParameters p) :
    ‖α‖ ≤ (p : ℝ) ^ 2 := by
  rcases Multiset.mem_map.mp hα with ⟨r, hr, rfl⟩
  refine not_lt.mp fun h ↦ (one_ne_zero : (1 : ℂ) ≠ 0) ?_
  have hsum : Summable fun k ↦ ‖L.coeff (p ^ k) * r ^ k‖ := by
    refine .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ ?_)
      ((L.LSeriesSummable_coeff (s := 2) (by simp)).norm.comp_injective
        (Nat.pow_right_injective hp.two_le))
    rw [Function.comp_apply, term_pow _ hp.ne_zero, norm_mul, norm_mul, norm_pow, norm_pow]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ k) (norm_nonneg _)
    rw [Complex.cpow_neg, Complex.cpow_ofNat, norm_inv, norm_pow, Complex.norm_natCast]
    rw [norm_inv] at h
    exact (le_inv_comm₀ (norm_pos_iff.mpr <| ne_zero_of_mem_roots_eulerPolynomial hr)
      (pow_pos (Nat.cast_pos.mpr hp.pos) 2)).mpr h.le
  have h₁ : (L.eulerPolynomial p).eval r * ∑' k, L.coeff (p ^ k) * r ^ k = 1 :=
    eval_mul_tsum_eq_one (coe_eulerPolynomial_mul_mk hp) hsum
  rwa [(mem_roots'.mp hr).2, zero_mul, eq_comm] at h₁

lemma norm_le_of_mem_symmetricPowerSatakeParameters (hp : p.Prime) {x : ℂ}
    (hx : x ∈ L.symmetricPowerSatakeParameters n p) : ‖x‖ ≤ ((p : ℝ) ^ 2) ^ n := by
  rcases List.mem_map.mp (Multiset.mem_coe.mp hx) with ⟨s, hs, rfl⟩
  have h : ‖(s : Multiset ℂ).prod‖₊ ≤ ((p : ℝ≥0) ^ 2) ^ n := by
    rw [Multiset.nnnorm_prod]
    refine (Multiset.prod_le_pow_card _ ((p : ℝ≥0) ^ 2) fun y hy ↦ ?_).trans_eq (by simp)
    rcases Multiset.mem_map.mp hy with ⟨α, hα, rfl⟩
    rw [← NNReal.coe_le_coe]
    simpa using L.norm_le_of_mem_satakeParameters hp
      (Multiset.mem_toList.mp <| List.mem_of_mem_of_mem_sym hα hs)
  exact_mod_cast h

lemma norm_coeff_le_of_prod_mul_eq_one {ρ : ℝ} (hρ : 0 ≤ ρ) {S : Multiset ℂ} (hS : ∀ x ∈ S, ‖x‖ ≤ ρ)
    {G : ℂ⟦X⟧} (hG : (((S.map fun x ↦ 1 - C x * X).prod : ℂ[X]) : ℂ⟦X⟧) * G = 1) (k : ℕ) :
    ‖PowerSeries.coeff k G‖ ≤ (S.card * ρ) ^ k := by
  induction S using Multiset.induction_on generalizing G k with
  | empty =>
    have h : G = 1 := by
      simpa using hG
    rcases k with _ | k <;> simp [h]
  | cons x S ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.coe_mul,
      mul_comm ((1 - C x * X : ℂ[X]) : ℂ⟦X⟧), mul_assoc] at hG
    have hx : ‖x‖ ≤ ρ :=
      hS x (Multiset.mem_cons_self x S)
    have hS' : ∀ y ∈ S, ‖y‖ ≤ ρ :=
      fun y hy ↦ hS y (Multiset.mem_cons_of_mem hy)
    rw [Multiset.card_cons, Nat.cast_succ]
    induction k with
    | zero =>
      simpa using ih hS' hG 0
    | succ j ihj =>
      have h : PowerSeries.coeff (j + 1) G =
          PowerSeries.coeff (j + 1) (((1 - C x * X : ℂ[X]) : ℂ⟦X⟧) * G) +
            x * PowerSeries.coeff j G := by
        simp [sub_mul, mul_assoc]
      have hc : 0 ≤ (S.card : ℝ) * ρ :=
        mul_nonneg (Nat.cast_nonneg _) hρ
      have h₂ : ((S.card : ℝ) * ρ) ^ (j + 1) ≤ (((S.card : ℝ) + 1) * ρ) ^ j * (S.card * ρ) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc (by linarith) j) hc
      have h₃ : (((S.card : ℝ) + 1) * ρ) ^ j * (((S.card : ℝ) + 1) * ρ) =
          (((S.card : ℝ) + 1) * ρ) ^ j * (S.card * ρ) + (((S.card : ℝ) + 1) * ρ) ^ j * ρ := by
        ring1
      rw [h, pow_succ, h₃]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      linarith [ih hS' hG (j + 1), mul_le_mul hx ihj (norm_nonneg _) hρ]

lemma norm_coeff_invOfUnit_le (F : ℂ[X]) (k : ℕ) :
    ‖PowerSeries.coeff k (PowerSeries.invOfUnit (F : ℂ⟦X⟧) 1)‖ ≤
      ((⌈∑' i, ‖F.coeff i‖⌉₊ + 1 : ℕ) : ℝ) ^ k := by
  have hF : Summable fun i ↦ ‖F.coeff i‖ :=
    summable_of_ne_finset_zero (s := F.support) fun i hi ↦ by simpa using hi
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · simp
    · rw [PowerSeries.coeff_invOfUnit, ite_eq_right k.succ_ne_zero, inv_one, Units.val_one,
        neg_one_mul, norm_neg]
      refine (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun x _ ↦ (?_ :
        _ ≤ ‖F.coeff x.1‖ * ((⌈∑' i, ‖F.coeff i‖⌉₊ + 1 : ℕ) : ℝ) ^ k)).trans ?_
      · split_ifs with hx₂
        · rw [norm_mul, coeff_coe]
          refine mul_le_mul_of_nonneg_left ((ih _ hx₂).trans ?_) (norm_nonneg _)
          exact pow_le_pow_right₀ (by simp) (Nat.lt_succ_iff.mp hx₂)
        · rw [norm_zero]
          positivity
      · rw [← Finset.sum_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, pow_succ']
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine (hF.sum_le_tsum _ fun _ _ ↦ norm_nonneg _).trans <| (Nat.le_ceil _).trans ?_
        simp

/-- An exponent `A` with `‖aₘ‖ ≤ m ^ A` for the coefficients `aₘ` of the series of the symmetric
`n`-th power of `L` with bad factors `B` (`norm_symmetricPowerDirichletSeries_le`), from the bound
`‖α‖ ≤ p ^ 2` on the Satake parameters of `L` that holds since `L` converges at `s = 2`. It is far
from sharp: the Ramanujan bounds would give `‖aₘ‖ ≤ m ^ ε` away from the bad primes. -/
noncomputable def symmetricPowerGrowthExponent : ℕ :=
  L.degree.multichoose n + 2 * n + ∑ q ∈ L.conductor.primeFactors, (⌈∑' i, ‖(B q).coeff i‖⌉₊ + 1)

lemma norm_symmetricPowerDirichletSeries_prime_pow_le (hp : p.Prime) (k : ℕ) :
    ‖L.symmetricPowerDirichletSeries n B (p ^ k)‖ ≤
      ((p ^ k : ℕ) : ℝ) ^ L.symmetricPowerGrowthExponent n B := by
  have hle (a : ℕ) : (a : ℝ) ≤ (p : ℝ) ^ a := by
    exact_mod_cast (Nat.lt_two_pow_self (n := a)).le.trans (Nat.pow_le_pow_left hp.two_le a)
  have key {a : ℕ} {r : ℝ} (hr₀ : 0 ≤ r) (hr : r ≤ (p : ℝ) ^ a)
      (ha : a ≤ L.symmetricPowerGrowthExponent n B) :
      r ^ k ≤ ((p ^ k : ℕ) : ℝ) ^ L.symmetricPowerGrowthExponent n B := by
    refine (pow_le_pow_left₀ hr₀ hr k).trans <| le_trans (le_of_eq ?_) <|
      pow_le_pow_right₀ (Nat.one_le_cast.mpr <| Nat.pow_pos hp.pos) ha
    rw [Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm]
  by_cases hpN : p ∣ L.conductor
  · rw [L.symmetricPowerDirichletSeries_prime_pow n B hp, symmetricPowerLocalFactor,
      ite_eq_left hpN]
    refine (norm_coeff_invOfUnit_le (B p) k).trans <| key (Nat.cast_nonneg _) (hle _) ?_
    exact (Finset.single_le_sum (f := fun q ↦ ⌈∑' i, ‖(B q).coeff i‖⌉₊ + 1)
      (fun _ _ ↦ Nat.zero_le _)
      (Nat.mem_primeFactors.mpr ⟨hp, hpN, L.selbergData.conductor_pos.ne'⟩)).trans
        (Nat.le_add_left _ _)
  · have hF : L.symmetricPowerLocalFactor n B p = L.symmetricPowerEulerFactor n p :=
      ite_eq_right hpN
    have hG : (L.symmetricPowerEulerFactor n p : ℂ⟦X⟧) *
        PowerSeries.mk (fun k ↦ L.symmetricPowerDirichletSeries n B (p ^ k)) = 1 :=
      hF ▸ L.coe_symmetricPowerLocalFactor_mul_mk n B hp fun h ↦ absurd h hpN
    have h : ‖L.symmetricPowerDirichletSeries n B (p ^ k)‖ ≤
        ((L.symmetricPowerSatakeParameters n p).card * ((p : ℝ) ^ 2) ^ n) ^ k := by
      simpa using norm_coeff_le_of_prod_mul_eq_one (by positivity)
        (fun _ hx ↦ L.norm_le_of_mem_symmetricPowerSatakeParameters n hp hx) hG k
    refine h.trans <| key (a := L.degree.multichoose n + 2 * n) (by positivity) ?_
      (Nat.le_add_right _ _)
    rw [card_symmetricPowerSatakeParameters, card_satakeParameters hp hpN, pow_add, pow_mul]
    exact mul_le_mul_of_nonneg_right (hle _) (by positivity)

lemma norm_symmetricPowerDirichletSeries_le (hm : m ≠ 0) :
    ‖L.symmetricPowerDirichletSeries n B m‖ ≤ (m : ℝ) ^ L.symmetricPowerGrowthExponent n B := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp _ =>
    exact L.norm_symmetricPowerDirichletSeries_prime_pow_le n B hp k
  | zero =>
    exact absurd rfl hm
  | one =>
    simpa using L.norm_symmetricPowerDirichletSeries_prime_pow_le n B Nat.prime_two 0
  | coprime a b ha hb hab iha ihb =>
    rw [(L.isMultiplicative_symmetricPowerDirichletSeries n B).map_mul_of_coprime hab, norm_mul,
      Nat.cast_mul, mul_pow]
    exact mul_le_mul (iha (by omega)) (ihb (by omega)) (norm_nonneg _) (by positivity)

/-- **The series of a symmetric power converges absolutely on a right half plane**, for all bad
factors and with no appeal to the Ramanujan bounds. -/
lemma abscissaOfAbsConv_symmetricPowerDirichletSeries_lt_top :
    abscissaOfAbsConv (L.symmetricPowerDirichletSeries n B) < ⊤ := by
  refine (abscissaOfAbsConv_le_of_le_const_mul_rpow (x := L.symmetricPowerGrowthExponent n B)
    ⟨1, fun m hm ↦ ?_⟩).trans_lt (EReal.coe_lt_top _)
  simpa using L.norm_symmetricPowerDirichletSeries_le n B hm

/-- **On a right half plane the L-series of a symmetric power is the Euler product of the knowl**:
`L(s, symⁿ) = ∏_p F_p(p ^ (-s))⁻¹`, where `F_p = ∏_m (1 - m T)` at `p ∤ N` and `F_p = B p` at
`p ∣ N`, for bad factors with constant coefficient `1`, such as `fun _ ↦ 1` or `M.eulerPolynomial`.
The half plane is not empty (`abscissaOfAbsConv_symmetricPowerDirichletSeries_lt_top`), and each
inverse is a true one: `F_p(p ^ (-s))` times the sum of the terms at the powers of `p` is `1`. -/
lemma hasProd_eval_symmetricPowerLocalFactor_inv
    (hB : ∀ p : ℕ, p.Prime → p ∣ L.conductor → (B p).coeff 0 = 1) {s : ℂ}
    (hs : abscissaOfAbsConv (L.symmetricPowerDirichletSeries n B) < s.re) :
    HasProd (fun q : Nat.Primes ↦ ((L.symmetricPowerLocalFactor n B q).eval ((q : ℂ) ^ (-s)))⁻¹)
      (LSeries (L.symmetricPowerDirichletSeries n B) s) := by
  have hsum : LSeriesSummable (L.symmetricPowerDirichletSeries n B) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re hs
  have hmul : (L.symmetricPowerDirichletSeries n B).IsMultiplicative :=
    L.isMultiplicative_symmetricPowerDirichletSeries n B
  have h : HasProd (fun q : Nat.Primes ↦
      ∑' e, term (L.symmetricPowerDirichletSeries n B) s ((q : ℕ) ^ e))
      (LSeries (L.symmetricPowerDirichletSeries n B) s) :=
    EulerProduct.eulerProduct_hasProd (by simp [hmul.map_one])
      (term_mul_of_coprime fun _ _ h ↦ hmul.map_mul_of_coprime h) hsum.norm (term_zero ..)
  convert h with q
  have hq : Summable fun e : ℕ ↦ ‖term (L.symmetricPowerDirichletSeries n B) s ((q : ℕ) ^ e)‖ :=
    hsum.norm.comp_injective (Nat.pow_right_injective q.prop.two_le)
  simp_rw [term_pow _ q.prop.ne_zero] at hq ⊢
  exact (eq_inv_of_mul_eq_one_right (eval_mul_tsum_eq_one
    (L.coe_symmetricPowerLocalFactor_mul_mk n B q.prop (hB q q.prop)) hq)).symm

end AnalyticLFunction
