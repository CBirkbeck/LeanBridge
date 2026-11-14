import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The Jacobi triple product identity

Let `q` and `z ≠ 0` be elements of a complete normed field with `‖q‖ < 1`. The theta series
`∑_{n ∈ ℤ} zⁿ q^(n²)` converges, and the Jacobi triple product identity writes it as an infinite
product:

`∑_{n ∈ ℤ} zⁿ q^(n²) = ∏_{n ≥ 1} (1 - q^(2n)) (1 + z q^(2n-1)) (1 + z⁻¹ q^(2n-1))`.

The proof is the classical one through a finite form of the identity. The `q`-binomial theorem
`∏_{i < n} (1 + t xⁱ) = ∑_{k ≤ n} x^(k(k-1)/2) [n; k]_x tᵏ` for the Gaussian binomial coefficients
`[n; k]_x`, taken at `x = q²`, `n = 2N` and `t = z q^(1-2N)`, is the finite identity

`∏_{j < N} (1 + z q^(2j+1)) (1 + z⁻¹ q^(2j+1)) = ∑_{|n| ≤ N} [2N; N + n]_{q²} zⁿ q^(n²)`.

By the product formula `[a + b; a]_x (x; x)_a (x; x)_b = (x; x)_{a+b}`, where
`(x; x)_n = ∏_{i < n} (1 - x^(i+1))`, the coefficient `[2N; N + n]_{q²}` tends to
`1 / ∏_{n ≥ 1} (1 - q^(2n))` as `N → ∞`, and it is bounded uniformly in `N` and `n`. So the sums on
the right converge to `∑_{n ∈ ℤ} zⁿ q^(n²) / ∏_{n ≥ 1} (1 - q^(2n))` by dominated convergence for
series (Tannery's theorem), while the products on the left converge to
`∏_{n ≥ 1} (1 + z q^(2n-1)) (1 + z⁻¹ q^(2n-1))`.

Neither the triple product nor its limit argument is in Mathlib or Tau Ceti, but some general
facts used here are. Mathlib's `ModularForm.multipliable_one_sub_pow` is the complex case of the
convergence of `∏_{n ≥ 1} (1 - qⁿ)`. Tau Ceti's main, not at LeanBridge's pin, has that
convergence and the nonvanishing of the product in any complete normed field
(`TauCeti.multipliable_one_sub_pow_mul`, `TauCeti.tprod_one_sub_pow_ne_zero`), the absolute
convergence of the theta series of the Tate curve (`TauCeti.summable_norm_tateTheta`), and the
`q`-binomial theorem and the product formula in the symmetric normalisation of quantum binomial
coefficients (`TauCeti.coeff_prod_range_one_add_C_mul_X`,
`TauCeti.laurentQuantumBinomial_mul_laurentQuantumFactorial_mul_laurentQuantumFactorial`). The
lemmas here that state these facts can be derived from those after the bump.

## Main definitions

* `JacobiTripleProduct.gaussBinom`: the Gaussian binomial coefficient `[n; k]_x` over a commutative
  ring, by its Pascal recursion.

## Main results

* `JacobiTripleProduct.prod_range_one_add_mul_pow`: the `q`-binomial theorem.
* `JacobiTripleProduct.gaussBinom_mul_prod_mul_prod`: the product formula
  `[a + b; a]_x (x; x)_a (x; x)_b = (x; x)_{a+b}`.
* `JacobiTripleProduct.prod_range_eq_sum_gaussBinom`: the finite form of the triple product.
* `summable_zpow_mul_zpow_sq`: the theta series `∑_{n ∈ ℤ} zⁿ q^(n²)` converges for `‖q‖ < 1`.
* `hasProd_tsum_zpow_mul_zpow_sq`, `tsum_zpow_mul_zpow_sq`: **the Jacobi triple product identity**.
* `tsum_zpow_mul_zpow_sq_eq_mul`: the same identity, with the three infinite products taken
  separately.

## References

* G. E. Andrews, *The Theory of Partitions*, Encyclopedia of Mathematics and its Applications 2,
  Addison-Wesley, 1976, Theorems 2.8 and 3.3.
* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, Encyclopedia of Mathematics and its
  Applications 71, Cambridge University Press, 1999, §10.4.
* G. H. Hardy, E. M. Wright, *An Introduction to the Theory of Numbers*, Theorem 352.
-/

open Filter Finset

open scoped Topology

namespace JacobiTripleProduct

section GaussBinom

variable {R : Type*} [CommRing R] (x t : R) (n k a b : ℕ)

/-- The **Gaussian binomial coefficient** `[n; k]_x` over a commutative ring, defined by
`[n; 0]_x = 1`, `[0; k + 1]_x = 0` and the Pascal recursion
`[n + 1; k + 1]_x = [n; k]_x + x ^ (k + 1) * [n; k + 1]_x`. -/
def gaussBinom : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gaussBinom n k + x ^ (k + 1) * gaussBinom n (k + 1)

lemma gaussBinom_zero_right : gaussBinom x n 0 = 1 := by
  rw [gaussBinom]

lemma gaussBinom_succ_succ :
    gaussBinom x (n + 1) (k + 1) = gaussBinom x n k + x ^ (k + 1) * gaussBinom x n (k + 1) := by
  rw [gaussBinom]

variable {n k} in
lemma gaussBinom_eq_zero_of_lt (h : n < k) : gaussBinom x n k = 0 := by
  induction n generalizing k with
  | zero =>
    rcases k with _ | k
    · exact absurd h (lt_irrefl 0)
    · rw [gaussBinom]
  | succ n ih =>
    rcases k with _ | k
    · exact absurd h (Nat.not_lt_zero _)
    · rw [gaussBinom_succ_succ, ih (by omega), ih (by omega), mul_zero, add_zero]

lemma gaussBinom_self : gaussBinom x n n = 1 := by
  induction n with
  | zero => rw [gaussBinom]
  | succ n ih =>
    rw [gaussBinom_succ_succ, ih, gaussBinom_eq_zero_of_lt x n.lt_succ_self, mul_zero, add_zero]

private lemma sum_range_succ_mul_one_add (f : ℕ → R) (hf : f (n + 1) = 0) :
    (∑ k ∈ range (n + 1), f k) * (1 + t) = ∑ k ∈ range (n + 1), (f k * t + f (k + 1)) + f 0 := by
  rw [sum_add_distrib, ← sum_mul, sum_range_succ fun k ↦ f (k + 1), hf, add_zero, sum_range_succ' f]
  ring1

/-- The **`q`-binomial theorem**: `∏_{i < n} (1 + t xⁱ) = ∑_{k ≤ n} x^(k(k-1)/2) [n; k]_x tᵏ`. -/
lemma prod_range_one_add_mul_pow : ∏ i ∈ range n, (1 + t * x ^ i) =
    ∑ k ∈ range (n + 1), x ^ k.choose 2 * gaussBinom x n k * t ^ k := by
  induction n generalizing t with
  | zero => simp [gaussBinom_zero_right]
  | succ n ih =>
    rw [prod_range_succ', prod_congr rfl fun i _ ↦ by rw [pow_succ', ← mul_assoc], ih, pow_zero,
      mul_one, sum_range_succ_mul_one_add _ _ _ <| by
        rw [gaussBinom_eq_zero_of_lt x n.lt_succ_self, mul_zero, zero_mul],
      sum_range_succ' _ (n + 1)]
    refine congrArg₂ _ (sum_congr rfl fun k _ ↦ ?_) (by simp [gaussBinom_zero_right])
    rw [gaussBinom_succ_succ, Nat.choose_succ_succ', Nat.choose_one_right]
    ring1

/-- The **product formula** for the Gaussian binomial coefficients:
`[a + b; a]_x (x; x)_a (x; x)_b = (x; x)_{a+b}`, where `(x; x)_n = ∏_{i < n} (1 - x^(i+1))`. -/
lemma gaussBinom_mul_prod_mul_prod : gaussBinom x (a + b) a * (∏ i ∈ range a, (1 - x ^ (i + 1))) *
    ∏ i ∈ range b, (1 - x ^ (i + 1)) = ∏ i ∈ range (a + b), (1 - x ^ (i + 1)) := by
  induction a generalizing b with
  | zero => simp [gaussBinom_zero_right]
  | succ a iha =>
    induction b with
    | zero => simp [gaussBinom_self]
    | succ b ihb =>
      specialize iha (b + 1)
      rw [← add_assoc, prod_range_succ _ b] at iha
      rw [add_right_comm, prod_range_succ _ a] at ihb
      rw [← add_assoc, add_right_comm a 1 b, gaussBinom_succ_succ, prod_range_succ _ a,
        prod_range_succ _ b, prod_range_succ _ (a + b + 1)]
      linear_combination (1 - x ^ (a + 1)) * iha + x ^ (a + 1) * (1 - x ^ (b + 1)) * ihb

private lemma two_mul_choose_two_add : 2 * k.choose 2 + k = k ^ 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    linarith

end GaussBinom

section Field

variable {K : Type*} [Field K] {q z : K} (N : ℕ)

private lemma zpow_sub_sq_mul (hq : q ≠ 0) (k : ℕ) :
    q ^ ((k : ℤ) - N) ^ 2 * (q ^ (2 * N)) ^ k = q ^ N ^ 2 * (q ^ 2) ^ k.choose 2 * q ^ k := by
  have h : (2 * k.choose 2 + k : ℤ) = k ^ 2 := mod_cast two_mul_choose_two_add k
  simp only [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hq]
  congr 1
  push_cast
  linear_combination -h

private lemma pow_sq_mul_prod_range (hq : q ≠ 0) (hz : z ≠ 0) :
    q ^ N ^ 2 * ∏ i ∈ range (2 * N), (1 + z * q / q ^ (2 * N) * (q ^ 2) ^ i) =
      z ^ N * ∏ j ∈ range N, (1 + z * q ^ (2 * j + 1)) * (1 + z⁻¹ * q ^ (2 * j + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h (i : ℕ) : 1 + z * q / q ^ (2 * N + 2) * (q ^ 2) ^ (i + 1) =
        1 + z * q / q ^ (2 * N) * (q ^ 2) ^ i := by
      field_simp
      ring1
    have h₁ : 1 + z * q / q ^ (2 * N + 2) * (q ^ 2) ^ (2 * N + 1) = 1 + z * q ^ (2 * N + 1) := by
      field_simp
      ring1
    have h₂ : q ^ (2 * N + 1) * (1 + z * q / q ^ (2 * N + 2) * (q ^ 2) ^ 0) =
        z * (1 + z⁻¹ * q ^ (2 * N + 1)) := by
      field_simp
      ring1
    rw [mul_add_one 2 N, prod_range_succ', prod_range_succ, prod_congr rfl fun i _ ↦ h i, h₁,
      prod_range_succ]
    generalize ∏ i ∈ range (2 * N), (1 + z * q / q ^ (2 * N) * (q ^ 2) ^ i) = A at ih ⊢
    generalize ∏ j ∈ range N, (1 + z * q ^ (2 * j + 1)) * (1 + z⁻¹ * q ^ (2 * j + 1)) = B at ih ⊢
    linear_combination (1 + z * q ^ (2 * N + 1)) * (z * (1 + z⁻¹ * q ^ (2 * N + 1))) * ih +
      q ^ N ^ 2 * A * (1 + z * q ^ (2 * N + 1)) * h₂

/-- The **finite form of the Jacobi triple product**:
`∏_{j < N} (1 + z q^(2j+1)) (1 + z⁻¹ q^(2j+1)) = ∑_{k ≤ 2N} [2N; k]_{q²} z^(k-N) q^((k-N)²)`. -/
lemma prod_range_eq_sum_gaussBinom (hq : q ≠ 0) (hz : z ≠ 0) :
    ∏ j ∈ range N, (1 + z * q ^ (2 * j + 1)) * (1 + z⁻¹ * q ^ (2 * j + 1)) =
      ∑ k ∈ range (2 * N + 1), gaussBinom (q ^ 2) (2 * N) k *
          (z ^ ((k : ℤ) - N) * q ^ ((k : ℤ) - N) ^ 2) := by
  rw [← mul_right_inj' (pow_ne_zero N hz), ← pow_sq_mul_prod_range N hq hz,
    prod_range_one_add_mul_pow, mul_sum, mul_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← (div_eq_iff (pow_ne_zero _ (pow_ne_zero _ hq))).mpr (zpow_sub_sq_mul N hq k).symm,
    zpow_sub₀ hz, zpow_natCast, zpow_natCast, div_pow, mul_pow]
  field_simp

end Field

section Normed

variable {𝕜 : Type*} [NormedField 𝕜] {q z : 𝕜} (N : ℕ)

lemma norm_sq_lt_one (hq : ‖q‖ < 1) : ‖q ^ 2‖ < 1 :=
  (norm_pow q 2).trans_lt <| pow_lt_one₀ (norm_nonneg q) hq two_ne_zero

lemma one_sub_pow_ne_zero (hq : ‖q‖ < 1) (n : ℕ) : 1 - q ^ (n + 1) ≠ 0 := by
  refine sub_ne_zero.mpr fun h ↦ (pow_lt_one₀ (norm_nonneg q) hq n.succ_ne_zero).ne ?_
  rw [← norm_pow, ← h, norm_one]

lemma summable_norm_pow_succ (hq : ‖q‖ < 1) : Summable fun n : ℕ ↦ ‖q ^ (n + 1)‖ := by
  simpa only [norm_pow] using
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg q) hq)

lemma gaussBinom_eq_div (hq : ‖q‖ < 1) (a b : ℕ) : gaussBinom q (a + b) a =
    (∏ i ∈ range (a + b), (1 - q ^ (i + 1))) /
        ((∏ i ∈ range a, (1 - q ^ (i + 1))) * ∏ i ∈ range b, (1 - q ^ (i + 1))) := by
  rw [eq_div_iff (mul_ne_zero (prod_ne_zero_iff.mpr fun i _ ↦ one_sub_pow_ne_zero hq i)
    (prod_ne_zero_iff.mpr fun i _ ↦ one_sub_pow_ne_zero hq i)), ← mul_assoc]
  exact gaussBinom_mul_prod_mul_prod q a b

variable (q) in
/-- The coefficient of `z ^ n * q ^ n ^ 2` in the product
`∏_{j < N} (1 + z q^(2j+1)) (1 + z⁻¹ q^(2j+1))`: it is `[2N; N + n]_{q²}` for `|n| ≤ N` and `0`
otherwise. -/
private def coeff (n : ℤ) : 𝕜 :=
  if -(N : ℤ) ≤ n then gaussBinom (q ^ 2) (2 * N) (n + N).toNat else 0

private lemma tsum_coeff_mul (hq : q ≠ 0) (hz : z ≠ 0) :
    ∑' n : ℤ, coeff q N n * (z ^ n * q ^ n ^ 2) =
      ∏ j ∈ range N, (1 + z * q ^ (2 * j + 1)) * (1 + z⁻¹ * q ^ (2 * j + 1)) := by
  have hinj : Function.Injective fun k : ℕ ↦ (k : ℤ) - N := fun a b h ↦ by simpa using h
  rw [prod_range_eq_sum_gaussBinom N hq hz, ← hinj.tsum_eq]
  · refine (tsum_eq_sum fun k hk ↦ ?_).trans <| sum_congr rfl fun k _ ↦ ?_
    · have h : 2 * N < k := by simpa using hk
      simp [coeff, gaussBinom_eq_zero_of_lt _ h]
    · simp [coeff]
  · intro n hn
    have h : -(N : ℤ) ≤ n := by
      by_contra h
      simp [coeff, h] at hn
    exact ⟨(n + N).toNat, by simp [Int.toNat_of_nonneg (by omega : 0 ≤ n + N)]⟩

variable [CompleteSpace 𝕜]

lemma multipliable_one_sub_pow (hq : ‖q‖ < 1) : Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) :=
  multipliable_one_sub_of_summable (summable_norm_pow_succ hq)

lemma tendsto_prod_range_one_sub_pow (hq : ‖q‖ < 1) :
    Tendsto (fun n ↦ ∏ i ∈ range n, (1 - q ^ (i + 1))) atTop (𝓝 (∏' n : ℕ, (1 - q ^ (n + 1)))) :=
  (multipliable_one_sub_pow hq).tendsto_prod_tprod_nat

lemma tprod_one_sub_pow_ne_zero (hq : ‖q‖ < 1) : ∏' n : ℕ, (1 - q ^ (n + 1)) ≠ 0 := by
  simp_rw [sub_eq_add_neg]
  refine tprod_one_add_ne_zero_of_summable (fun n ↦ ?_) ?_
  · simpa only [← sub_eq_add_neg] using one_sub_pow_ne_zero hq n
  · simpa only [norm_neg] using summable_norm_pow_succ hq

variable (z) in
lemma multipliable_one_add_mul_pow (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 + z * q ^ (2 * n + 1) := by
  refine multipliable_one_add_of_summable <| ((summable_geometric_of_lt_one (sq_nonneg ‖q‖) <|
    pow_lt_one₀ (norm_nonneg q) hq two_ne_zero).mul_left (‖z‖ * ‖q‖)).congr fun n ↦ ?_
  rw [norm_mul, norm_pow]
  ring1

lemma tendsto_gaussBinom (hq : ‖q‖ < 1) {a b : ℕ → ℕ} (ha : Tendsto a atTop atTop)
    (hb : Tendsto b atTop atTop) :
    Tendsto (fun N ↦ gaussBinom q (a N + b N) (a N)) atTop (𝓝 (∏' n : ℕ, (1 - q ^ (n + 1)))⁻¹) := by
  have h0 : ∏' n : ℕ, (1 - q ^ (n + 1)) ≠ 0 := tprod_one_sub_pow_ne_zero hq
  rw [← div_mul_cancel_left₀ h0 (∏' n : ℕ, (1 - q ^ (n + 1)))]
  exact (((tendsto_prod_range_one_sub_pow hq).comp <|
    tendsto_atTop_mono (fun N ↦ Nat.le_add_right (a N) (b N)) ha).div
      (((tendsto_prod_range_one_sub_pow hq).comp ha).mul <|
        (tendsto_prod_range_one_sub_pow hq).comp hb) <| mul_ne_zero h0 h0).congr fun N ↦
          (gaussBinom_eq_div hq (a N) (b N)).symm

lemma exists_norm_gaussBinom_le (hq : ‖q‖ < 1) : ∃ C, ∀ n k, ‖gaussBinom q n k‖ ≤ C := by
  rcases (tendsto_prod_range_one_sub_pow hq).norm.bddAbove_range with ⟨C₁, hC₁⟩
  rcases ((tendsto_prod_range_one_sub_pow hq).inv₀ <|
    tprod_one_sub_pow_ne_zero hq).norm.bddAbove_range with ⟨C₂, hC₂⟩
  have h₁ (n : ℕ) : ‖∏ i ∈ range n, (1 - q ^ (i + 1))‖ ≤ C₁ := hC₁ ⟨n, rfl⟩
  have h₂ (n : ℕ) : ‖(∏ i ∈ range n, (1 - q ^ (i + 1)))⁻¹‖ ≤ C₂ := hC₂ ⟨n, rfl⟩
  have hC₂0 : 0 ≤ C₂ := (norm_nonneg _).trans (h₂ 0)
  refine ⟨C₁ * (C₂ * C₂), fun n k ↦ ?_⟩
  rcases lt_or_ge n k with h | h
  · rw [gaussBinom_eq_zero_of_lt q h, norm_zero]
    exact mul_nonneg ((norm_nonneg _).trans (h₁ 0)) (mul_nonneg hC₂0 hC₂0)
  · rcases Nat.exists_eq_add_of_le h with ⟨m, rfl⟩
    rw [gaussBinom_eq_div hq, div_eq_mul_inv, mul_inv, norm_mul, norm_mul]
    exact mul_le_mul (h₁ _) (mul_le_mul (h₂ _) (h₂ _) (norm_nonneg _) hC₂0)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ((norm_nonneg _).trans (h₁ 0))

variable (z) in
private lemma summable_pow_mul_pow_sq (hq : ‖q‖ < 1) : Summable fun n : ℕ ↦ z ^ n * q ^ n ^ 2 := by
  have ht : Tendsto (fun n : ℕ ↦ ‖z‖ * ‖q‖ ^ (2 * n + 1)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).comp
      (tendsto_atTop_mono (fun n ↦ by omega : ∀ n : ℕ, n ≤ 2 * n + 1) tendsto_id)).const_mul ‖z‖
  refine summable_of_ratio_norm_eventually_le one_half_lt_one ?_
  filter_upwards [ht.eventually_le_const one_half_pos] with n hn
  have h : z ^ (n + 1) * q ^ (n + 1) ^ 2 = z * q ^ (2 * n + 1) * (z ^ n * q ^ n ^ 2) := by
    ring1
  rw [h, norm_mul, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)

end Normed

end JacobiTripleProduct

open JacobiTripleProduct

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {q z : 𝕜}

variable (z) in
/-- **The theta series converges**: for `‖q‖ < 1` in a complete normed field, the series
`∑_{n ∈ ℤ} zⁿ q^(n²)` is summable for every `z`. -/
lemma summable_zpow_mul_zpow_sq (hq : ‖q‖ < 1) : Summable fun n : ℤ ↦ z ^ n * q ^ n ^ 2 := by
  refine .of_nat_of_neg ?_ ?_
  · simpa only [← Nat.cast_pow, zpow_natCast] using summable_pow_mul_pow_sq z hq
  · simpa only [neg_sq, zpow_neg, ← Nat.cast_pow, zpow_natCast, ← inv_pow] using
      summable_pow_mul_pow_sq z⁻¹ hq

private lemma tendsto_coeff (hq : ‖q‖ < 1) (n : ℤ) :
    Tendsto (fun N ↦ coeff q N n) atTop (𝓝 (∏' i : ℕ, (1 - (q ^ 2) ^ (i + 1)))⁻¹) := by
  have ha : Tendsto (fun N : ℕ ↦ (n + N).toNat) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b ↦ ⟨b + n.natAbs, fun N hN ↦ by omega⟩
  have hb : Tendsto (fun N : ℕ ↦ (N - n).toNat) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b ↦ ⟨b + n.natAbs, fun N hN ↦ by omega⟩
  refine (tendsto_gaussBinom (norm_sq_lt_one hq) ha hb).congr' ?_
  filter_upwards [eventually_ge_atTop n.natAbs] with N hN
  have h : (n + N).toNat + (N - n).toNat = 2 * N := by omega
  rw [coeff, ite_eq_left (by omega), h]

private lemma tsum_zpow_mul_zpow_sq_of_ne_zero (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hz : z ≠ 0) :
    ∑' n : ℤ, z ^ n * q ^ n ^ 2 = (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) *
        ∏' n : ℕ, (1 + z * q ^ (2 * n + 1)) * (1 + z⁻¹ * q ^ (2 * n + 1)) := by
  rcases exists_norm_gaussBinom_le (norm_sq_lt_one hq) with ⟨C, hC⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 0)
  have hlim : Tendsto (fun N ↦ ∑' n : ℤ, coeff q N n * (z ^ n * q ^ n ^ 2)) atTop
      (𝓝 (∑' n : ℤ, (∏' i : ℕ, (1 - (q ^ 2) ^ (i + 1)))⁻¹ * (z ^ n * q ^ n ^ 2))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n ↦ C * (‖z‖ ^ n * ‖q‖ ^ n ^ 2))
      ?_ (fun n ↦ (tendsto_coeff hq n).mul_const _) (.of_forall fun N n ↦ ?_)
    · exact (summable_zpow_mul_zpow_sq ‖z‖ (by simpa using hq)).mul_left C
    · rw [norm_mul, norm_mul, norm_zpow, norm_zpow]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [coeff]
      split_ifs
      · exact hC _ _
      · rwa [norm_zero]
  have hm : Multipliable fun j : ℕ ↦ (1 + z * q ^ (2 * j + 1)) * (1 + z⁻¹ * q ^ (2 * j + 1)) :=
    (multipliable_one_add_mul_pow z hq).mul (multipliable_one_add_mul_pow z⁻¹ hq)
  rw [tendsto_nhds_unique (hm.tendsto_prod_tprod_nat.congr fun N ↦ (tsum_coeff_mul N hq0 hz).symm)
    hlim, tsum_mul_left, mul_inv_cancel_left₀ (tprod_one_sub_pow_ne_zero (norm_sq_lt_one hq))]

/-- **The Jacobi triple product identity**, with the three infinite products taken separately: for
`‖q‖ < 1` and `z ≠ 0` in a complete normed field, the theta series `∑_{n ∈ ℤ} zⁿ q^(n²)` is the
product of `∏_{n ≥ 1} (1 - q^(2n))`, `∏_{n ≥ 1} (1 + z q^(2n-1))` and
`∏_{n ≥ 1} (1 + z⁻¹ q^(2n-1))`. -/
lemma tsum_zpow_mul_zpow_sq_eq_mul (hq : ‖q‖ < 1) (hz : z ≠ 0) : ∑' n : ℤ, z ^ n * q ^ n ^ 2 =
    (∏' n : ℕ, (1 - q ^ (2 * (n + 1)))) * (∏' n : ℕ, (1 + z * q ^ (2 * n + 1))) *
        ∏' n : ℕ, (1 + z⁻¹ * q ^ (2 * n + 1)) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [tsum_eq_single 0 fun n hn ↦ by rw [zero_zpow _ (pow_ne_zero 2 hn), mul_zero]]
    simp
  · rw [tsum_zpow_mul_zpow_sq_of_ne_zero hq hq0 hz, mul_assoc,
      (multipliable_one_add_mul_pow z hq).tprod_mul (multipliable_one_add_mul_pow z⁻¹ hq)]
    simp_rw [pow_mul]

/-- **The Jacobi triple product identity**: for `‖q‖ < 1` and `z ≠ 0` in a complete normed field,
the product `∏_{n ≥ 1} (1 - q^(2n)) (1 + z q^(2n-1)) (1 + z⁻¹ q^(2n-1))` converges to the theta
series `∑_{n ∈ ℤ} zⁿ q^(n²)`. -/
lemma hasProd_tsum_zpow_mul_zpow_sq (hq : ‖q‖ < 1) (hz : z ≠ 0) : HasProd
    (fun n : ℕ ↦ (1 - q ^ (2 * (n + 1))) * (1 + z * q ^ (2 * n + 1)) * (1 + z⁻¹ * q ^ (2 * n + 1)))
    (∑' n : ℤ, z ^ n * q ^ n ^ 2) := by
  have h₁ : Multipliable fun n : ℕ ↦ 1 - q ^ (2 * (n + 1)) := by
    simpa only [pow_mul] using multipliable_one_sub_pow (norm_sq_lt_one hq)
  have h₂ : Multipliable fun n : ℕ ↦ 1 + z * q ^ (2 * n + 1) := multipliable_one_add_mul_pow z hq
  have h₃ : Multipliable fun n : ℕ ↦ 1 + z⁻¹ * q ^ (2 * n + 1) :=
    multipliable_one_add_mul_pow z⁻¹ hq
  rw [((h₁.mul h₂).mul h₃).hasProd_iff, (h₁.mul h₂).tprod_mul h₃, h₁.tprod_mul h₂,
    tsum_zpow_mul_zpow_sq_eq_mul hq hz]

/-- **The Jacobi triple product identity**: for `‖q‖ < 1` and `z ≠ 0` in a complete normed field,
`∑_{n ∈ ℤ} zⁿ q^(n²) = ∏_{n ≥ 1} (1 - q^(2n)) (1 + z q^(2n-1)) (1 + z⁻¹ q^(2n-1))`. -/
lemma tsum_zpow_mul_zpow_sq (hq : ‖q‖ < 1) (hz : z ≠ 0) : ∑' n : ℤ, z ^ n * q ^ n ^ 2 =
    ∏' n : ℕ, (1 - q ^ (2 * (n + 1))) * (1 + z * q ^ (2 * n + 1)) * (1 + z⁻¹ * q ^ (2 * n + 1)) :=
  (hasProd_tsum_zpow_mul_zpow_sq hq hz).tprod_eq.symm
