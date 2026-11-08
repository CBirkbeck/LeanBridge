import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The `p`-adic expansion

Every `x ∈ ℤ_p` is the sum `x = ∑_{n ≥ 0} d_n p ^ n` of a convergent series with digits
`d_n ∈ {0, …, p - 1}`, and the digits are unique: for any such series the partial sum
`∑_{n < N} d_n p ^ n` is the natural number `x.appr N`, the representative of `x` modulo `p ^ N` in
`[0, p ^ N)`. A nonzero `x ∈ ℚ_p` with `|x|_p = p ^ (-n₀)` is `p ^ n₀` times a unit of `ℤ_p`, so
`x = ∑_{n ≥ n₀} a_n p ^ n` with digits `a_n ∈ {0, …, p - 1}` and `a_{n₀} ≠ 0`, and `n₀` and the
digits are unique (LMFDB `lf.qp`).

The knowl's absolute value on `ℚ` is Mathlib's `padicNorm`: a nonzero rational is `p ^ j a / b` with
`gcd(p, ab) = 1`, and then `padicNorm p r = p ^ (-j)`. Mathlib's `ℚ_p` (`Padic`) is by definition
the completion of `ℚ` for this absolute value.

The knowl's example is the square root of `2` in `ℚ_7` congruent to `3` modulo `7`: its expansion
begins `3 + 7 + 2 · 7 ^ 2 + 6 · 7 ^ 3 + 7 ^ 4 + 2 · 7 ^ 5`, and a `7`-adic integer squares to `2`
exactly when all its truncations square to `2` modulo the matching power of `7`.

## Main definitions

* `PadicInt.digit` (LMFDB `lf.qp`): the digits of a `p`-adic integer.
* `Padic.unitPart`: the unit `x p ^ (-v_p(x))` of `ℤ_p` attached to a nonzero `p`-adic number `x`.
* `Padic.digit` (LMFDB `lf.qp`): the digits of a nonzero `p`-adic number, from its leading digit.
* `PadicInt.sqrtTwo` (LMFDB `lf.qp`): the square root of `2` in `ℤ_7` congruent to `3` modulo `7`.

## Main theorems

* `padicNorm.exists_eq_zpow_mul_div` (LMFDB `lf.qp`): a nonzero rational is `p ^ j a / b` with
  `gcd(p, ab) = 1`.
* `padicNorm.eq_zpow_neg_of_eq_zpow_mul_div` (LMFDB `lf.qp`): then `|r|_p = p ^ (-j)`.
* `PadicInt.hasSum_iff_eq_digit` (LMFDB `lf.qp`): `x = ∑ a_n p ^ n` with digits `a_n < p` exactly
  for the digits of `x`.
* `Padic.expansion_iff` (LMFDB `lf.qp`): existence and uniqueness of the expansion
  `x = ∑_{n ≥ n₀} a_n p ^ n` of a nonzero `x ∈ ℚ_p`, with `|x|_p = p ^ (-n₀)` and `a_{n₀} ≠ 0`.
* `PadicInt.sq_eq_intCast_iff` (LMFDB `lf.qp`): `x ^ 2 = c` exactly when every truncation of the
  expansion of `x` squares to `c` modulo the matching power of `p`.
* `PadicInt.sqrtTwo_sq`, `PadicInt.eq_sqrtTwo`, `PadicInt.map_digit_sqrtTwo` and
  `PadicInt.dvd_sq_sum_digit_sqrtTwo_sub_two` (LMFDB `lf.qp`): the square root of `2` in `ℤ_7`
  congruent to `3` modulo `7`, its uniqueness, its first six digits `3, 1, 2, 6, 1, 2`, and the
  congruences of its truncations.
-/

open Finset Filter Polynomial Topology

namespace padicNorm

variable {p : ℕ} [hp : Fact p.Prime] {r : ℚ}

/-- **Rationals as `p ^ j a / b`** (LMFDB `lf.qp`): a nonzero rational number `r` is `p ^ j a / b`
for an integer `j` and integers `a, b` with `gcd(p, ab) = 1`. -/
lemma exists_eq_zpow_mul_div (hr : r ≠ 0) :
    ∃ j : ℤ, ∃ a b : ℤ, Int.gcd p (a * b) = 1 ∧ r = p ^ j * a / b := by
  rcases Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hr)) p
    hp.out.ne_one with ⟨α, a, ha, hnum⟩
  rcases Nat.exists_eq_pow_mul_and_not_dvd r.den_nz p hp.out.ne_one with ⟨β, b, hb, hden⟩
  refine ⟨α - β, r.num.sign * a, b, ?_, ?_⟩
  · rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_mul,
      Int.natAbs_sign_of_ne_zero (Rat.num_ne_zero.2 hr), one_mul, Int.natAbs_natCast,
      Int.natAbs_natCast]
    exact (hp.out.coprime_iff_not_dvd.2 ha).mul_right (hp.out.coprime_iff_not_dvd.2 hb)
  · have hp₀ : (p : ℚ) ≠ 0 := by
      exact_mod_cast hp.out.ne_zero
    have hnum' : (r.num : ℚ) = r.num.sign * (p ^ α * a) := by
      exact_mod_cast hnum ▸ (Int.sign_mul_natAbs r.num).symm
    nth_rw 1 [← Rat.num_div_den r]
    rw [hnum', hden, zpow_sub₀ hp₀, zpow_natCast, zpow_natCast]
    push_cast
    field_simp

/-- **The `p`-adic absolute value** (LMFDB `lf.qp`): for a rational number `r = p ^ j a / b` with
`gcd(p, ab) = 1`, Mathlib's `padicNorm p r` is `p ^ (-j)`. In particular `j` does not depend on the
way `r` is written. -/
lemma eq_zpow_neg_of_eq_zpow_mul_div {j : ℤ} {a b : ℤ} (hab : Int.gcd p (a * b) = 1)
    (hr : r = p ^ j * a / b) : padicNorm p r = (p : ℚ) ^ (-j) := by
  have hp₀ : (p : ℚ) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  have hdvd (c : ℤ) (hc : c ∣ a * b) : ¬(p : ℤ) ∣ c := fun h ↦ by
    have hdvd : p ∣ Int.gcd p (a * b) :=
      Int.dvd_gcd (Int.natCast_dvd_natCast.2 (dvd_refl p)) (h.trans hc)
    rw [hab] at hdvd
    exact hp.out.not_dvd_one hdvd
  rw [hr, padicNorm.div, padicNorm.mul, (int_eq_one_iff a).2 (hdvd a (dvd_mul_right a b)),
    (int_eq_one_iff b).2 (hdvd b (dvd_mul_left b a)), mul_one, div_one,
    padicNorm.eq_zpow_of_nonzero (zpow_ne_zero j hp₀), padicValRat.zpow,
    padicValRat.self hp.out.one_lt, mul_one]

end padicNorm

namespace PadicInt

variable {p : ℕ} [hp : Fact p.Prime] (x : ℤ_[p])

variable (p) in
private lemma inv_natCast_lt_one : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ <| mod_cast hp.out.one_lt

variable (p) in
private lemma tendsto_inv_natCast_pow : Tendsto (fun n : ℕ ↦ (p : ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_natCast_lt_one p)

/-- The **`p`-adic digits** (LMFDB `lf.qp`) of a `p`-adic integer `x`: the `d_n ∈ {0, …, p - 1}`
with `x = ∑_{n ≥ 0} d_n p ^ n`. The partial sum `∑_{n < N} d_n p ^ n` is `x.appr N`, the
representative of `x` modulo `p ^ N` in `[0, p ^ N)`, so `d_n = ⌊x.appr (n + 1) / p ^ n⌋`. -/
noncomputable def digit (n : ℕ) : ℕ :=
  x.appr (n + 1) / p ^ n

lemma appr_succ (n : ℕ) : x.appr (n + 1) = x.appr n + x.digit n * p ^ n := by
  rcases x.dvd_appr_sub_appr n (n + 1) n.le_succ with ⟨d, hd⟩
  have hle : x.appr n ≤ x.appr (n + 1) := x.appr_mono n.le_succ
  have happr : x.appr (n + 1) = x.appr n + p ^ n * d := by
    omega
  rw [digit, happr, Nat.add_mul_div_left _ _ (pow_pos hp.out.pos n),
    Nat.div_eq_of_lt (x.appr_lt n), zero_add, mul_comm]

lemma digit_lt (n : ℕ) : x.digit n < p :=
  Nat.div_lt_of_lt_mul <| (x.appr_lt (n + 1)).trans_eq <| pow_succ p n

lemma sum_digit_mul_pow (N : ℕ) : ∑ n ∈ range N, x.digit n * p ^ n = x.appr N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [sum_range_succ, ih, appr_succ]

lemma norm_sub_appr_le (N : ℕ) : ‖x - x.appr N‖ ≤ (p : ℝ)⁻¹ ^ N := by
  rw [inv_pow, ← zpow_natCast, ← zpow_neg]
  exact (norm_le_pow_iff_mem_span_pow _ N).2 (appr_spec N x)

lemma tendsto_appr : Tendsto (fun N ↦ (x.appr N : ℤ_[p])) atTop (𝓝 x) :=
  tendsto_iff_norm_sub_tendsto_zero.2 <| squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun N ↦ (norm_sub_rev _ _).trans_le (x.norm_sub_appr_le N)) (tendsto_inv_natCast_pow p)

lemma summable_norm_natCast_mul_pow (a : ℕ → ℕ) : Summable fun n ↦ ‖(a n : ℤ_[p]) * p ^ n‖ := by
  refine (summable_geometric_of_lt_one (by positivity) (inv_natCast_lt_one p)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  rw [norm_mul, norm_pow, norm_p]
  exact mul_le_of_le_one_left (by positivity) (norm_le_one _)

lemma hasSum_digit : HasSum (fun n ↦ (x.digit n : ℤ_[p]) * p ^ n) x := by
  rw [hasSum_iff_tendsto_nat_of_summable_norm (summable_norm_natCast_mul_pow _)]
  simpa only [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_sum, sum_digit_mul_pow] using
    x.tendsto_appr

lemma sum_mul_pow_lt {a : ℕ → ℕ} (ha : ∀ n, a n < p) (N : ℕ) :
    ∑ n ∈ range N, a n * p ^ n < p ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, pow_succ]
    nlinarith [ha N, pow_pos hp.out.pos N]

lemma sum_mul_pow_eq_appr {a : ℕ → ℕ} (ha : ∀ n, a n < p)
    (h : HasSum (fun n ↦ (a n : ℤ_[p]) * p ^ n) x) (N : ℕ) :
    ∑ n ∈ range N, a n * p ^ n = x.appr N := by
  have htail : HasSum (fun n ↦ (a (n + N) : ℤ_[p]) * p ^ (n + N))
      (x - ∑ n ∈ range N, (a n : ℤ_[p]) * p ^ n) :=
    (hasSum_nat_add_iff' N).2 h
  have hy : HasSum (fun n ↦ (p : ℤ_[p]) ^ N * ((a (n + N) : ℤ_[p]) * p ^ n))
      ((p : ℤ_[p]) ^ N * ∑' n, (a (n + N) : ℤ_[p]) * p ^ n) :=
    (Summable.of_norm (summable_norm_natCast_mul_pow _)).hasSum.mul_left _
  simp_rw [← mul_assoc, mul_comm ((p : ℤ_[p]) ^ N), mul_assoc, ← pow_add, add_comm N] at hy
  have hmem : x - ∑ n ∈ range N, (a n : ℤ_[p]) * p ^ n ∈ Ideal.span {(p : ℤ_[p]) ^ N} := by
    rw [htail.unique hy]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hdvd : ((p ^ N : ℕ) : ℤ) ∣ (x.appr N : ℤ) - (∑ n ∈ range N, a n * p ^ n : ℕ) := by
    rw [Nat.cast_pow, ← norm_int_le_pow_iff_dvd, norm_le_pow_iff_mem_span_pow]
    have hsub : x - ∑ n ∈ range N, (a n : ℤ_[p]) * p ^ n - (x - x.appr N) ∈
        Ideal.span {(p : ℤ_[p]) ^ N} :=
      Ideal.sub_mem _ hmem (appr_spec N x)
    push_cast at hsub ⊢
    rwa [sub_sub_sub_cancel_left] at hsub
  exact (Nat.modEq_iff_dvd.2 hdvd).eq_of_lt_of_lt (sum_mul_pow_lt ha N) (x.appr_lt N)

/-- **The `p`-adic expansion of a `p`-adic integer** (LMFDB `lf.qp`): `x = ∑_{n ≥ 0} a_n p ^ n`
with digits `a_n ∈ {0, …, p - 1}` exactly when `a` is the sequence of digits of `x`. -/
lemma hasSum_iff_eq_digit {a : ℕ → ℕ} (ha : ∀ n, a n < p) :
    HasSum (fun n ↦ (a n : ℤ_[p]) * p ^ n) x ↔ a = x.digit := by
  refine ⟨fun h ↦ funext fun n ↦ ?_, fun h ↦ h ▸ x.hasSum_digit⟩
  have hn : ∑ i ∈ range (n + 1), a i * p ^ i = x.appr (n + 1) :=
    x.sum_mul_pow_eq_appr ha h (n + 1)
  rw [sum_range_succ, x.sum_mul_pow_eq_appr ha h n, appr_succ, Nat.add_left_cancel_iff] at hn
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos n) hn

lemma appr_one_ne_zero (hx : ‖x‖ = 1) : x.appr 1 ≠ 0 := by
  intro h
  have hle : ‖x - x.appr 1‖ ≤ (p : ℝ)⁻¹ ^ 1 := x.norm_sub_appr_le 1
  rw [h, Nat.cast_zero, sub_zero, hx, pow_one] at hle
  exact (inv_natCast_lt_one p).not_ge hle

/-- **Truncations of a square root** (LMFDB `lf.qp`): a `p`-adic integer `x` satisfies
`x ^ 2 = c` for an integer `c` exactly when, for every `n`, the truncation
`x.appr n = ∑_{k < n} d_k p ^ k` of its expansion squares to `c` modulo `p ^ n`. -/
lemma sq_eq_intCast_iff (c : ℤ) : x ^ 2 = c ↔ ∀ n, (p : ℤ) ^ n ∣ (x.appr n : ℤ) ^ 2 - c := by
  have hmem (n : ℕ) : (x.appr n : ℤ_[p]) - x ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
    rw [← neg_sub]
    exact neg_mem (appr_spec n x)
  constructor
  · intro h n
    rw [← norm_int_le_pow_iff_dvd, Int.cast_sub, Int.cast_pow, Int.cast_natCast, ← h, sq_sub_sq,
      norm_le_pow_iff_mem_span_pow]
    exact Ideal.mul_mem_left _ _ (hmem n)
  · intro h
    rw [← sub_eq_zero, ← norm_eq_zero]
    refine le_antisymm (ge_of_tendsto' (tendsto_inv_natCast_pow p) fun n ↦ ?_) (norm_nonneg _)
    have hsq :
        x ^ 2 - c = ((x.appr n : ℤ) ^ 2 - c : ℤ) - ((x.appr n : ℤ_[p]) - x) * (x.appr n + x) := by
      push_cast
      ring1
    rw [inv_pow, ← zpow_natCast, ← zpow_neg, norm_le_pow_iff_mem_span_pow, hsq]
    refine Ideal.sub_mem _ ?_ (Ideal.mul_mem_right _ _ (hmem n))
    rw [← norm_le_pow_iff_mem_span_pow, norm_int_le_pow_iff_dvd]
    exact h n

local instance : Fact (Nat.Prime 7) :=
  ⟨Nat.prime_seven⟩

lemma norm_aeval_derivative_X_sq_sub_two_three :
    ‖(derivative (X ^ 2 - 2 : ℤ_[7][X])).aeval (3 : ℤ_[7])‖ = 1 := by
  have h6 : algebraMap ℤ_[7] ℤ_[7] ((2 : ℕ) : ℤ_[7]) * 3 ^ (2 - 1) = ((6 : ℕ) : ℤ_[7]) := by
    norm_num
  rw [derivative_sub, derivative_X_pow, derivative_ofNat, sub_zero, map_mul, aeval_C, aeval_X_pow,
    h6, norm_natCast_eq_one_iff]
  exact Nat.coprime_of_lt_prime (by norm_num) (by norm_num) Nat.prime_seven

lemma norm_aeval_X_sq_sub_two_three_lt : ‖(X ^ 2 - 2 : ℤ_[7][X]).aeval (3 : ℤ_[7])‖ <
    ‖(derivative (X ^ 2 - 2 : ℤ_[7][X])).aeval (3 : ℤ_[7])‖ ^ 2 := by
  have h7 : (3 : ℤ_[7]) ^ 2 - 2 = ((7 : ℕ) : ℤ_[7]) := by
    norm_num
  rw [norm_aeval_derivative_X_sq_sub_two_three, one_pow, map_sub, aeval_X_pow, map_ofNat, h7,
    norm_natCast_lt_one_iff]

/-- The **square root of `2` in `ℤ_7`** congruent to `3` modulo `7` (LMFDB `lf.qp`): the root of
`X ^ 2 - 2` that Hensel's lemma lifts from its simple root `3` modulo `7`. Its expansion is
`3 + 7 + 2 · 7 ^ 2 + 6 · 7 ^ 3 + 7 ^ 4 + 2 · 7 ^ 5 + ⋯` (`PadicInt.map_digit_sqrtTwo`). -/
noncomputable def sqrtTwo : ℤ_[7] :=
  Classical.choose (hensels_lemma norm_aeval_X_sq_sub_two_three_lt)

/-- **The square root of `2`** (LMFDB `lf.qp`): `sqrtTwo ^ 2 = 2` in `ℤ_7`. -/
lemma sqrtTwo_sq : sqrtTwo ^ 2 = 2 := by
  have h : (X ^ 2 - 2 : ℤ_[7][X]).aeval sqrtTwo = 0 :=
    (Classical.choose_spec (hensels_lemma norm_aeval_X_sq_sub_two_three_lt)).1
  rwa [map_sub, aeval_X_pow, map_ofNat, sub_eq_zero] at h

lemma norm_sqrtTwo_sub_three_lt_one : ‖sqrtTwo - 3‖ < 1 :=
  (Classical.choose_spec (hensels_lemma norm_aeval_X_sq_sub_two_three_lt)).2.1.trans_eq
    norm_aeval_derivative_X_sq_sub_two_three

/-- **The square root of `2` congruent to `3` modulo `7` is unique** (LMFDB `lf.qp`): a `z ∈ ℤ_7`
with `z ^ 2 = 2` and `|z - 3|_7 < 1` is `sqrtTwo`. -/
lemma eq_sqrtTwo {z : ℤ_[7]} (hz : z ^ 2 = 2) (hz₃ : ‖z - 3‖ < 1) : z = sqrtTwo :=
  (Classical.choose_spec (hensels_lemma norm_aeval_X_sq_sub_two_three_lt)).2.2.2 z
    (by rw [map_sub, aeval_X_pow, map_ofNat, hz, sub_self])
    (by rwa [norm_aeval_derivative_X_sq_sub_two_three])

lemma appr_sqrtTwo_six : sqrtTwo.appr 6 = 38181 := by
  have h₂ : (7 : ℤ) ^ 6 ∣ (sqrtTwo.appr 6 : ℤ) ^ 2 - 2 := by
    exact_mod_cast (sqrtTwo.sq_eq_intCast_iff 2).1 (by rw [sqrtTwo_sq, Int.cast_ofNat]) 6
  have h₃ : (7 : ℤ) ∣ (sqrtTwo.appr 6 : ℤ) - 3 := by
    rw [← Nat.cast_ofNat, ← norm_int_lt_one_iff_dvd, Int.cast_sub, Int.cast_natCast,
      Int.cast_ofNat, ← sub_add_sub_cancel _ sqrtTwo]
    refine (nonarchimedean _ _).trans_lt (max_lt ?_ norm_sqrtTwo_sub_three_lt_one)
    rw [norm_sub_rev]
    exact (sqrtTwo.norm_sub_appr_le 6).trans_lt <|
      pow_lt_one₀ (by positivity) (inv_natCast_lt_one 7) (by norm_num)
  have h7 : Prime (7 : ℤ) := by
    exact_mod_cast Nat.prime_iff_prime_int.1 Nat.prime_seven
  have hcop : IsCoprime ((7 : ℤ) ^ 6) ((sqrtTwo.appr 6 : ℤ) + 38181) :=
    (h7.irreducible.coprime_iff_not_dvd.2 (by omega)).pow_left
  have hdvd : (7 : ℤ) ^ 6 ∣ ((sqrtTwo.appr 6 : ℤ) - 38181) * ((sqrtTwo.appr 6 : ℤ) + 38181) := by
    have hw : (7 : ℤ) ^ 6 ∣ 38181 ^ 2 - 2 := by
      norm_num
    convert dvd_sub h₂ hw using 1
    ring1
  have hlt : (sqrtTwo.appr 6 : ℤ) < 7 ^ 6 := by
    exact_mod_cast sqrtTwo.appr_lt 6
  have h : (7 : ℤ) ^ 6 ∣ (sqrtTwo.appr 6 : ℤ) - 38181 :=
    hcop.dvd_of_dvd_mul_right hdvd
  norm_num at h hlt
  omega

lemma appr_sqrtTwo {k : ℕ} (hk : k ≤ 6) : sqrtTwo.appr k = 38181 % 7 ^ k := by
  rw [← appr_sqrtTwo_six, ← Nat.mod_eq_of_lt (sqrtTwo.appr_lt k)]
  exact (Nat.modEq_iff_dvd' (sqrtTwo.appr_mono hk)).2 (sqrtTwo.dvd_appr_sub_appr k 6 hk)

/-- **The `7`-adic expansion of the square root of `2`** (LMFDB `lf.qp`): the digits of
`sqrtTwo` begin `3, 1, 2, 6, 1, 2`, that is
`sqrtTwo = 3 + 7 + 2 · 7 ^ 2 + 6 · 7 ^ 3 + 7 ^ 4 + 2 · 7 ^ 5 + ⋯`. -/
lemma map_digit_sqrtTwo : (List.range 6).map sqrtTwo.digit = [3, 1, 2, 6, 1, 2] := by
  have h (k : ℕ) (hk : k < 6) : sqrtTwo.digit k = 38181 % 7 ^ (k + 1) / 7 ^ k := by
    rw [digit, appr_sqrtTwo hk]
  simp [List.range_succ, h]

/-- **Truncations of the expansion of the square root of `2`** (LMFDB `lf.qp`): truncating the
expansion of `sqrtTwo` after `n` terms and squaring gives a number congruent to `2` modulo
`7 ^ n`. By `PadicInt.sq_eq_intCast_iff`, this property of all truncations is equivalent to
`sqrtTwo ^ 2 = 2`. -/
lemma dvd_sq_sum_digit_sqrtTwo_sub_two (n : ℕ) :
    (7 : ℤ) ^ n ∣ ((∑ k ∈ range n, sqrtTwo.digit k * 7 ^ k : ℕ) : ℤ) ^ 2 - 2 := by
  rw [sum_digit_mul_pow]
  exact_mod_cast (sqrtTwo.sq_eq_intCast_iff 2).1 (by rw [sqrtTwo_sq, Int.cast_ofNat]) n

end PadicInt

namespace Padic

variable {p : ℕ} [hp : Fact p.Prime] {x : ℚ_[p]}

lemma norm_mul_zpow_neg_valuation (hx : x ≠ 0) : ‖x * (p : ℚ_[p]) ^ (-x.valuation)‖ = 1 := by
  rw [norm_mul, norm_eq_zpow_neg_valuation hx, norm_p_zpow, neg_neg,
    ← zpow_add₀ (by exact_mod_cast hp.out.ne_zero), neg_add_cancel, zpow_zero]

lemma norm_mul_zpow_neg_valuation_le_one (x : ℚ_[p]) :
    ‖x * (p : ℚ_[p]) ^ (-x.valuation)‖ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (norm_mul_zpow_neg_valuation hx).le

/-- The **unit part** `x p ^ (-v_p(x))` of a `p`-adic number `x`, as a `p`-adic integer: a unit of
`ℤ_p` when `x ≠ 0` (of norm `1`), and `0` when `x = 0`. -/
noncomputable def unitPart (x : ℚ_[p]) : ℤ_[p] :=
  ⟨x * (p : ℚ_[p]) ^ (-x.valuation), norm_mul_zpow_neg_valuation_le_one x⟩

lemma coe_unitPart (x : ℚ_[p]) : (x.unitPart : ℚ_[p]) = x * (p : ℚ_[p]) ^ (-x.valuation) :=
  rfl

/-- The **`p`-adic digits** (LMFDB `lf.qp`) of a nonzero `p`-adic number `x`: `x.digit k` is the
digit `a_{n₀ + k}` of the expansion `x = ∑_{n ≥ n₀} a_n p ^ n`, where `n₀ = v_p(x)`, so that
`|x|_p = p ^ (-n₀)`. It is the `k`-th digit of the unit `x p ^ (-n₀)` of `ℤ_p`. -/
noncomputable def digit (x : ℚ_[p]) (k : ℕ) : ℕ :=
  x.unitPart.digit k

/-- **The `p`-adic expansion** (LMFDB `lf.qp`): a nonzero `x ∈ ℚ_p` is the sum of the convergent
series `∑_{k ≥ 0} a_k p ^ (n₀ + k)` with digits `a_k ∈ {0, …, p - 1}`, `|x|_p = p ^ (-n₀)` and
`a_0 ≠ 0` exactly for `n₀ = v_p(x)` and `a = x.digit`. So the expansion
`x = ∑_{n ≥ n₀} a_n p ^ n` exists and is unique. -/
lemma expansion_iff (hx : x ≠ 0) {n₀ : ℤ} {a : ℕ → ℕ} : (n₀, a) = (x.valuation, x.digit) ↔
    (∀ k, a k < p) ∧ a 0 ≠ 0 ∧ ‖x‖ = (p : ℝ) ^ (-n₀) ∧
    HasSum (fun k ↦ (a k : ℚ_[p]) * (p : ℚ_[p]) ^ (n₀ + k)) x := by
  have hp₀ : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  have hpv : (p : ℚ_[p]) ^ (-x.valuation) * (p : ℚ_[p]) ^ x.valuation = 1 := by
    rw [← zpow_add₀ hp₀, neg_add_cancel, zpow_zero]
  have hterm (k : ℕ) : (p : ℚ_[p]) ^ x.valuation * ((x.digit k : ℚ_[p]) * (p : ℚ_[p]) ^ k) =
      (x.digit k : ℚ_[p]) * (p : ℚ_[p]) ^ (x.valuation + k) := by
    rw [zpow_add₀ hp₀, zpow_natCast]
    ring1
  constructor
  · rintro ⟨⟩
    refine ⟨x.unitPart.digit_lt, ?_, norm_eq_zpow_neg_valuation hx, ?_⟩
    · rw [digit, PadicInt.digit, pow_zero, Nat.div_one]
      exact x.unitPart.appr_one_ne_zero (norm_mul_zpow_neg_valuation hx)
    · convert (x.unitPart.hasSum_digit.map (algebraMap ℤ_[p] ℚ_[p])
        continuous_subtype_val).mul_left ((p : ℚ_[p]) ^ x.valuation) using 1
      · funext k
        rw [← hterm, Function.comp_apply, map_mul, map_natCast, map_pow, map_natCast, digit]
      · rw [PadicInt.algebraMap_apply, coe_unitPart, mul_left_comm, ← zpow_add₀ hp₀,
          add_neg_cancel, zpow_zero, mul_one]
  · rintro ⟨ha, -, hnorm, hsum⟩
    have hn₀ : n₀ = x.valuation := by
      rw [norm_eq_zpow_neg_valuation hx, zpow_right_inj₀ (by exact_mod_cast hp.out.pos)
        (by exact_mod_cast hp.out.ne_one), neg_inj] at hnorm
      exact hnorm.symm
    subst hn₀
    have hsum' : HasSum (algebraMap ℤ_[p] ℚ_[p] ∘ fun k ↦ (a k : ℤ_[p]) * (p : ℤ_[p]) ^ k)
        (algebraMap ℤ_[p] ℚ_[p] x.unitPart) := by
      convert hsum.mul_left ((p : ℚ_[p]) ^ (-x.valuation)) using 1
      · funext k
        rw [Function.comp_apply, map_mul, map_natCast, map_pow, map_natCast, zpow_add₀ hp₀,
          zpow_natCast]
        linear_combination -((a k : ℚ_[p]) * (p : ℚ_[p]) ^ k) * hpv
      · exact mul_comm _ _
    exact Prod.ext rfl <| (x.unitPart.hasSum_iff_eq_digit ha).1 <|
      (IsInducing.subtypeVal.hasSum_iff (g := algebraMap ℤ_[p] ℚ_[p]) _ _).1 hsum'

end Padic
